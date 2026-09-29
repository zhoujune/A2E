"""Four Redis scenarios x two broker variants, with real SIGKILL and retained evidence.

Linux/WSL only. Uses a private Unix socket (Redis TCP disabled), no Python packages.
The mutant is built in a temporary source copy; production sources stay unchanged.
"""
import argparse
from datetime import datetime, timezone
import difflib
import hashlib
import json
import os
from pathlib import Path
import platform
import queue
import shutil
import signal
import socket
import subprocess
import tempfile
import threading
import time
import traceback


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def encode(args):
    parts = [str(a).encode() for a in args]
    return b'*%d\r\n' % len(parts) + b''.join(
        b'$%d\r\n' % len(p) + p + b'\r\n' for p in parts)


def read_resp(f):
    line = f.readline()
    if not line or not line.endswith(b'\r\n'):
        raise EOFError('incomplete RESP line')
    kind, value = line[:1], line[1:-2]
    if kind in (b'+', b'-'):
        return line, value.decode()
    if kind == b':':
        return line, int(value)
    if kind == b'$':
        n = int(value)
        if n == -1:
            return line, None
        payload = f.read(n + 2)
        if len(payload) != n + 2 or not payload.endswith(b'\r\n'):
            raise EOFError('incomplete RESP payload')
        return line + payload, payload[:-2].decode()
    if kind == b'*':
        parts = [read_resp(f) for _ in range(int(value))]
        return line + b''.join(p[0] for p in parts), [p[1] for p in parts]
    raise ValueError('unsupported RESP type')


def query(path, *args):
    with socket.socket(socket.AF_UNIX) as sock:
        sock.settimeout(15)
        sock.connect(str(path))
        sock.sendall(encode(args))
        with sock.makefile('rb') as f:
            wire, value = read_resp(f)
        if wire.startswith(b'-'):
            raise RuntimeError(value)
        return value


class ReplyBarrier:
    """Forward commands unchanged; withhold the first SADD reply after Redis executes."""
    def __init__(self, path, upstream):
        self.path, self.upstream = path, upstream
        self.ready, self.release = threading.Event(), threading.Event()
        self.transcript, self.error = [], None
        self.listener = socket.socket(socket.AF_UNIX)
        self.listener.bind(str(path))
        self.listener.listen(1)
        self.listener.settimeout(20)
        self.thread = threading.Thread(target=self.run, daemon=True)
        self.thread.start()

    def run(self):
        try:
            client, _ = self.listener.accept()
            with client, socket.socket(socket.AF_UNIX) as upstream:
                client.settimeout(20)
                upstream.settimeout(20)
                upstream.connect(str(self.upstream))
                with client.makefile('rb') as cf, upstream.makefile('rb') as uf:
                    while True:
                        wire, args = read_resp(cf)
                        upstream.sendall(wire)
                        reply, decoded = read_resp(uf)
                        self.transcript.append({'command': args[0], 'reply': decoded})
                        if args[0] == 'SADD':
                            assert reply == b':1\r\n', reply
                            self.ready.set()
                            if not self.release.wait(20):
                                raise TimeoutError('reply barrier not released')
                            # Parent has reaped the SIGKILLed client. Drop the withheld reply.
                            return
                        client.sendall(reply)
        except Exception:
            self.error = traceback.format_exc()
            self.ready.set()
        finally:
            self.listener.close()

    def close(self):
        self.release.set()
        self.thread.join(21)
        assert not self.thread.is_alive(), 'proxy failed to finish'
        if self.error:
            raise AssertionError(self.error)


class Worker:
    def __init__(self, binary, case_dir, socket_path, mode, label):
        self.events, self.lines = queue.Queue(), []
        self.stderr_path = case_dir / (label + '.stderr')
        self.stderr_file = self.stderr_path.open('w')
        self.stdout_path = case_dir / (label + '.stdout')
        self.proc = subprocess.Popen(
            [str(binary), str(case_dir), str(socket_path), mode],
            stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=self.stderr_file,
            text=True, bufsize=1)
        self.thread = threading.Thread(target=self.read, daemon=True)
        self.thread.start()

    def read(self):
        for line in self.proc.stdout:
            self.lines.append(line.rstrip())
            self.events.put(line.rstrip())
        self.events.put(None)

    def until(self, prefix):
        end = time.monotonic() + 20
        while True:
            line = self.events.get(timeout=max(0.01, end - time.monotonic()))
            if line is None:
                raise AssertionError('worker ended early: ' + self.stderr_path.read_text())
            if line.startswith(prefix):
                return line
            if time.monotonic() >= end:
                raise TimeoutError(prefix)

    def proceed(self):
        self.proc.stdin.write('continue\n')
        self.proc.stdin.flush()

    def finish(self, kill=False):
        if kill:
            assert self.proc.poll() is None
            self.proc.kill()
        code = self.proc.wait(timeout=20)
        self.thread.join(2)
        self.stderr_file.close()
        self.stdout_path.write_text('\n'.join(self.lines) + '\n')
        assert code == (-signal.SIGKILL if kill else 0), (code, self.stderr_path.read_text())
        return code

    def cleanup(self):
        if self.proc.poll() is None:
            self.proc.kill()
            self.proc.wait(timeout=10)
        self.thread.join(2)
        self.stderr_file.close()
        self.stdout_path.write_text('\n'.join(self.lines) + '\n')


def run_case(binary, variant, scenario, case_dir, redis_server, socket_root):
    case_dir.mkdir()
    service_dir = case_dir / 'service'
    service_dir.mkdir()
    server_socket = socket_root / 'redis.sock'
    server_socket.unlink(missing_ok=True)
    proxy_socket = socket_root / 'proxy.sock'
    proxy_socket.unlink(missing_ok=True)
    config = [str(redis_server), '--port', '0', '--unixsocket', str(server_socket),
              '--unixsocketperm', '700', '--dir', str(service_dir),
              '--appendonly', 'yes', '--appendfsync', 'always', '--save', '',
              '--logfile', str(service_dir / 'redis.log')]
    server = subprocess.Popen(config, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE)
    workers, proxy = [], None
    result = {'variant': variant, 'scenario': scenario, 'redis_command': config,
              'broker_exit_codes': [], 'service_pid': server.pid, 'oracle': {}}
    try:
        end = time.monotonic() + 20
        while True:
            assert server.poll() is None, server.stderr.read().decode()
            try:
                if query(server_socket, 'PING') == 'PONG':
                    break
            except (FileNotFoundError, ConnectionRefusedError):
                pass
            assert time.monotonic() < end, 'Redis did not start'
            time.sleep(0.02)
        assert query(server_socket, 'ACL', 'SETUSER', 'study', 'reset', 'on',
                     '>experiment-only', '~study:members', '+sadd') == 'OK'
        result['oracle']['initial'] = query(server_socket, 'SISMEMBER', 'study:members', 'member')
        assert result['oracle']['initial'] == 0
        paired = scenario in ('uninvoked_then_rejected', 'effect_then_rejected')
        effect = int(scenario in ('effect_then_rejected', 'success'))
        if scenario == 'conclusive_failure':
            query(server_socket, 'ACL', 'SETUSER', 'study', '-sadd')
        if paired:
            mode, endpoint = 'before_send', server_socket
            if effect:
                proxy = ReplyBarrier(proxy_socket, server_socket)
                mode, endpoint = 'fresh', proxy_socket
            first = Worker(binary, case_dir, endpoint, mode, 'initial')
            workers.append(first)
            if effect:
                assert proxy.ready.wait(20), 'service did not reach reply barrier'
                assert proxy.error is None, proxy.error
                assert all(not line.startswith('REPLY|') for line in first.lines)
            else:
                first.until('BEFORE_SEND')
            result['oracle']['before_kill'] = query(server_socket, 'SISMEMBER', 'study:members', 'member')
            assert result['oracle']['before_kill'] == effect
            result['broker_exit_codes'].append(first.finish(kill=True))
            assert server.poll() is None
            if proxy:
                proxy.close()
                result['withheld_reply'] = proxy.transcript
                proxy = None
            shutil.copyfile(case_dir / 'broker.wal', case_dir / 'initial.wal')
            result['oracle']['after_kill'] = query(server_socket, 'SISMEMBER', 'study:members', 'member')
            assert result['oracle']['after_kill'] == effect
            # Change only ACL state; never change the protected member between observations.
            query(server_socket, 'ACL', 'SETUSER', 'study', '-sadd')
        worker = Worker(binary, case_dir, server_socket, 'resume' if paired else 'fresh', 'decision')
        workers.append(worker)
        decision = worker.until('PRE_TERMINAL|').split('|')[1]
        assert ('REPLY|-NOPERM ' in '\n'.join(worker.lines)) == (scenario != 'success')
        shutil.copyfile(case_dir / 'broker.wal', case_dir / 'preterminal.wal')
        result['oracle']['decision_boundary'] = query(server_socket, 'SISMEMBER', 'study:members', 'member')
        assert result['oracle']['decision_boundary'] == effect
        expected = ('Fail' if variant == 'without_failure_coverage' else 'Unknown') if paired else ('Commit' if effect else 'Fail')
        assert decision == expected, (decision, expected)
        worker.proceed()
        assert worker.until('TERMINAL|') == 'TERMINAL|' + expected + '|1'
        result['broker_exit_codes'].append(worker.finish())
        reopen = Worker(binary, case_dir, server_socket, 'resume', 'reopen')
        workers.append(reopen)
        assert reopen.until('TERMINAL|') == 'TERMINAL|' + expected + '|0'
        result['broker_exit_codes'].append(reopen.finish())
        result['oracle']['after_reopen'] = query(server_socket, 'SISMEMBER', 'study:members', 'member')
        assert result['oracle']['after_reopen'] == effect
        assert server.poll() is None
        result.update(terminal=decision, effect=effect, reopened_calls=0,
                      service_survived=True, observed_effect_violation=(decision == 'Fail' and effect == 1),
                      preterminal_wal_sha256=sha(case_dir / 'preterminal.wal'),
                      preterminal_records=(case_dir / 'preterminal.txt').read_text(),
                      preterminal_records_sha256=sha(case_dir / 'preterminal.txt'),
                      initial_wal_sha256=sha(case_dir / 'initial.wal') if paired else None)
        (case_dir / 'case.json').write_text(json.dumps(result, indent=2) + '\n')
        return result
    finally:
        for worker in workers:
            worker.cleanup()
        if proxy:
            proxy.release.set()
            proxy.thread.join(21)
        if server.poll() is None:
            server.terminate()
        server.wait(timeout=20)
        (service_dir / 'stderr.txt').write_bytes(server.stderr.read())


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cargo', type=Path, required=True)
    parser.add_argument('--redis-server', type=Path, required=True)
    parser.add_argument('--redis-source-archive', type=Path)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    assert os.name == 'posix', 'requires Linux/WSL SIGKILL and Unix sockets'
    crate = Path(__file__).resolve().parents[1]
    repo = crate.parent
    output = args.output.resolve()
    output.parent.mkdir(parents=True, exist_ok=True)
    run_dir = output.parent / (output.stem + '-runs') / datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
    run_dir.mkdir(parents=True)
    env = os.environ.copy()
    env['PATH'] = str(args.cargo.resolve().parent) + os.pathsep + env.get('PATH', '')
    env['RUSTC'] = str(args.cargo.resolve().with_name('rustc'))
    paths = sorted(list((crate / 'src').rglob('*.rs')) +
                   [crate / 'Cargo.toml', crate / 'Cargo.lock',
                    crate / 'examples/redis_crash_worker.rs', Path(__file__).resolve()])
    report = {'schema_version': 1, 'status': 'running', 'cases': [],
              'started_at_utc': datetime.now(timezone.utc).isoformat(),
              'platform': platform.platform(), 'artifacts': str(run_dir),
              'source_sha256': {p.relative_to(repo).as_posix(): sha(p) for p in paths},
              'rustc': subprocess.check_output([env['RUSTC'], '--version'], text=True).strip(),
              'redis': subprocess.check_output([str(args.redis_server), '--version'], text=True).strip(),
              'redis_binary_sha256': sha(args.redis_server),
              'redis_archive_sha256': sha(args.redis_source_archive) if args.redis_source_archive else None,
              'scope': 'Four controlled scenarios, two variants; serialized reference broker, observer gate only; Redis process survives broker SIGKILL; no power loss or machine-checked Redis refinement.'}
    try:
        with tempfile.TemporaryDirectory(prefix='a2e-redis-') as temp:
            temp = Path(temp)
            binaries = {}
            for variant in ('full', 'without_failure_coverage'):
                build = temp / variant
                build.mkdir()
                shutil.copytree(crate / 'src', build / 'src')
                (build / 'examples').mkdir()
                shutil.copyfile(crate / 'examples/redis_crash_worker.rs', build / 'examples/redis_crash_worker.rs')
                for name in ('Cargo.toml', 'Cargo.lock'):
                    shutil.copyfile(crate / name, build / name)
                if variant != 'full':
                    source = build / 'src/broker.rs'
                    original = source.read_text()
                    start = original.index('                Observation::Failure\n                    if state.class == Some(RetryClass::Idempotent)')
                    end = original.index('                Observation::Failure => RecoveryDecision::Fail', start)
                    removed = original[start:end]
                    assert 'UnknownReason::NonConclusiveFailure' in removed and '!state.all_attempts_failed' in removed
                    mutated = original[:start] + original[end:]
                    source.write_text(mutated)
                    diff = ''.join(difflib.unified_diff(original.splitlines(True), mutated.splitlines(True),
                                                       fromfile='full/src/broker.rs', tofile='without_failure_coverage/src/broker.rs'))
                    (run_dir / 'ablation.patch').write_text(diff)
                    report['ablation'] = {'removed_branch': removed, 'mutant_broker_sha256': sha(source),
                                          'description': 'Delete only the classifier branch that maps incomplete idempotent failure coverage to Unknown.'}
                command = [str(args.cargo), 'build', '--offline', '--manifest-path', str(build / 'Cargo.toml'),
                           '--example', 'redis_crash_worker']
                built = subprocess.run(command, env=env, capture_output=True, text=True, timeout=120)
                (run_dir / (variant + '-build.log')).write_text(built.stdout + built.stderr)
                assert built.returncode == 0, built.stderr
                binaries[variant] = build / 'target/debug/examples/redis_crash_worker'
            for variant, binary in binaries.items():
                for scenario in ('uninvoked_then_rejected', 'effect_then_rejected', 'conclusive_failure', 'success'):
                    case = run_case(binary, variant, scenario, run_dir / (variant + '-' + scenario),
                                    args.redis_server.resolve(), temp)
                    report['cases'].append(case)
                    print(variant, scenario, case['terminal'], case['effect'], flush=True)
            checks = []
            for variant in binaries:
                cases = [c for c in report['cases'] if c['variant'] == variant]
                a, b = cases[:2]
                for field in ('initial_wal_sha256', 'preterminal_wal_sha256', 'preterminal_records_sha256'):
                    assert a[field] == b[field], (variant, field)
                checks.append({'variant': variant, 'identical_initial_wal': True,
                               'identical_preterminal_wal': True, 'identical_preterminal_records': True})
            for scenario in ('uninvoked_then_rejected', 'effect_then_rejected', 'conclusive_failure', 'success'):
                a, b = [c for c in report['cases'] if c['scenario'] == scenario]
                assert a['preterminal_wal_sha256'] == b['preterminal_wal_sha256'], scenario
            report['pair_checks'] = checks
            report['summary'] = {variant: {
                'executions': 4,
                'observed_effect_violations': sum(c['observed_effect_violation'] for c in report['cases'] if c['variant'] == variant),
                'paired_unknown_decisions': sum(c['terminal'] == 'Unknown' for c in report['cases'] if c['variant'] == variant),
                'conclusive_controls_correct': 2,
                'reopen_without_invocation': 4,
            } for variant in binaries}
            report['status'] = 'passed'
    except Exception:
        report['status'] = 'failed'
        report['error'] = traceback.format_exc()
        raise
    finally:
        report['finished_at_utc'] = datetime.now(timezone.utc).isoformat()
        output.write_text(json.dumps(report, indent=2) + '\n')
        print('report:', output, flush=True)


if __name__ == '__main__':
    main()
