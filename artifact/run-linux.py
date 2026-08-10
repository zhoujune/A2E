#!/usr/bin/env python3
"""Linux TLA+ artifact runner with isolated, hash-checked model snapshots."""

import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time
from pathlib import Path


SAFE_NAME = re.compile(r"^[A-Za-z0-9][A-Za-z0-9._-]*$")
JAVA_VERSION = re.compile(r'"21\.0\.11')
SHA256 = re.compile(r"^[0-9a-fA-F]{64}$")
GIT_REVISION = re.compile(r"^[0-9a-f]{40}$")


def fail(message):
    raise RuntimeError(message)


def sha256(path):
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def source_revision(root):
    configured = os.environ.get("PROVEAI_SOURCE_REVISION")
    if configured:
        return configured
    if (root / ".git").exists():
        try:
            return subprocess.check_output(
                ["git", "rev-parse", "HEAD"],
                cwd=root,
                text=True,
                stderr=subprocess.DEVNULL,
            ).strip()
        except (OSError, subprocess.CalledProcessError):
            pass
    revision_file = root / "artifact" / "source-revision.txt"
    if revision_file.is_file():
        revision = revision_file.read_text(encoding="utf-8").strip()
        if GIT_REVISION.fullmatch(revision):
            return revision
    return "unknown"


def require_file(path, description):
    if not path.is_file():
        fail(f"missing {description}: {path}")


def safe_name(value, description):
    if not isinstance(value, str) or not SAFE_NAME.fullmatch(value):
        fail(f"unsafe {description}: {value!r}")
    return value


def load_suite(root):
    suite_path = root / "formal" / "model-suite.json"
    with suite_path.open(encoding="utf-8") as stream:
        suite = json.load(stream)
    if not isinstance(suite.get("scenarios"), list) or not suite["scenarios"]:
        fail("model-suite.json has no scenarios")
    names = set()
    scenarios = []
    for entry in suite["scenarios"]:
        if set(entry) != {"name", "tier", "module", "config"}:
            fail(f"scenario keys are not exact: {entry}")
        name = safe_name(entry["name"], "scenario name")
        if name in names:
            fail(f"duplicate scenario: {name}")
        names.add(name)
        if entry["tier"] not in {"smoke", "full"}:
            fail(f"invalid scenario tier: {entry['tier']}")
        module = safe_name(entry["module"], "module name")
        config = safe_name(entry["config"], "configuration name")
        if not module.endswith(".tla") or not config.endswith(".cfg"):
            fail(f"invalid module/config suffix for {name}")
        if not (root / "formal" / module).is_file() or not (root / "formal" / config).is_file():
            fail(f"scenario input missing for {name}")
        scenarios.append({"name": name, "tier": entry["tier"], "module": module, "config": config})
    registered_cfg = {path.name for path in (root / "formal").glob("*.cfg")}
    selected_cfg = {entry["config"] for entry in scenarios}
    if registered_cfg != selected_cfg:
        fail(f"configuration registry mismatch: unregistered={registered_cfg - selected_cfg}, missing={selected_cfg - registered_cfg}")
    return scenarios


def resolve_java(argument, expected_sha256):
    candidate = Path(argument) if argument else None
    if candidate and candidate.is_dir():
        candidate = candidate / "bin" / "java"
    if candidate is None:
        java_home = os.environ.get("JAVA_HOME")
        if java_home:
            candidate = Path(java_home) / "bin" / "java"
        else:
            candidate = shutil.which("java")
            candidate = Path(candidate) if candidate else None
    if candidate is None or not candidate.is_file() or not os.access(candidate, os.X_OK):
        fail("Java 21.0.11 is required; set JAVA_HOME or --java to a hash-pinned Linux JRE")
    if not expected_sha256 or not SHA256.fullmatch(expected_sha256):
        fail("the toolchain lock, --java-sha256, or PROVEAI_JAVA_SHA256 must provide a Java executable SHA-256")
    actual_sha256 = sha256(candidate)
    if actual_sha256.lower() != expected_sha256.lower():
        fail(f"Java executable SHA-256 mismatch: expected {expected_sha256}, observed {actual_sha256}")
    try:
        result = subprocess.run(
            [str(candidate), "-version"], capture_output=True, text=True, timeout=10
        )
    except subprocess.TimeoutExpired:
        fail("Java version probe exceeded 10 seconds")
    version_text = result.stderr + result.stdout
    if result.returncode != 0 or not JAVA_VERSION.search(version_text):
        fail(f"Java 21.0.11 is required, observed: {version_text.strip()}")
    return candidate, version_text.strip(), actual_sha256


def resolve_tla(argument, lock):
    expected = lock["tla_tools"]["sha256"]
    candidate = Path(argument) if argument else None
    if candidate is None:
        environment = os.environ.get("PROVEAI_TLA_TOOLS")
        candidate = Path(environment) if environment else None
    if candidate is None:
        fail("TLA+ Tools v1.7.4 is required; set PROVEAI_TLA_TOOLS to the pinned JAR")
    require_file(candidate, "TLA+ Tools JAR")
    actual = sha256(candidate)
    if actual != expected:
        fail(f"TLA+ Tools SHA-256 mismatch: expected {expected}, observed {actual}")
    return candidate, actual


def snapshot_inputs(root, scenarios, destination):
    formal = root / "formal"
    inputs = sorted(
        {path.name for path in formal.glob("*.tla")}
        | {entry["config"] for entry in scenarios}
    )
    for path in inputs:
        source = formal / path
        target = destination / path
        shutil.copy2(source, target)
        target.chmod(0o444)
    hashes = {path: sha256(destination / path) for path in inputs}
    return inputs, hashes


def verify_snapshot(destination, inputs, hashes):
    observed = sorted(path.name for path in destination.iterdir())
    if observed != inputs:
        fail(f"isolated snapshot membership changed: expected {inputs}, observed {observed}")
    for path in inputs:
        actual = sha256(destination / path)
        if actual != hashes[path]:
            fail(f"isolated snapshot hash changed for {path}: expected {hashes[path]}, observed {actual}")


def run(args):
    root = Path(args.repository).resolve()
    toolchain_lock_path = root / "artifact" / "toolchain.lock.json"
    require_file(toolchain_lock_path, "toolchain lock")
    toolchain_lock_bytes = toolchain_lock_path.read_bytes()
    toolchain_lock_hash = hashlib.sha256(toolchain_lock_bytes).hexdigest()
    toolchain_lock = json.loads(toolchain_lock_bytes)
    runner_hash = sha256(Path(__file__))
    manifest_hash = sha256(root / "formal" / "model-suite.json")
    revision = source_revision(root)
    scenarios = load_suite(root)
    selected = [entry for entry in scenarios if args.suite == "full" or entry["tier"] == "smoke"]
    java = None
    java_version = None
    java_hash = None
    tla_tools = None
    tla_hash = None
    lock = None
    if not args.dry_run:
        lock = toolchain_lock
        java, java_version, java_hash = resolve_java(
            args.java,
            args.java_sha256
            or os.environ.get("PROVEAI_JAVA_SHA256")
            or lock["java"].get("sha256"),
        )
        tla_tools, tla_hash = resolve_tla(args.tla_tools, lock)
    report_path = Path(args.report).resolve()
    if report_path.exists():
        fail(f"refusing to overwrite existing report: {report_path}")
    started = time.time()
    with tempfile.TemporaryDirectory(prefix="proveai-tla-linux-") as temporary:
        temporary_root = Path(temporary)
        snapshot = temporary_root / "snapshot"
        states = temporary_root / "states"
        snapshot.mkdir()
        states.mkdir()
        java_temp = temporary_root / "java-temp"
        java_temp.mkdir()
        inputs, hashes = snapshot_inputs(root, selected, snapshot)
        verify_snapshot(snapshot, inputs, hashes)
        scenario_reports = []
        for entry in selected:
            state_dir = states / entry["name"]
            state_dir.mkdir()
            scenario_started = time.time()
            if args.dry_run:
                status = "dry_run"
                exit_code = None
                output_length = 0
                output_sha256 = hashlib.sha256(b"").hexdigest()
            else:
                command = [
                    str(java),
                    "-XX:+UseParallelGC",
                    "-Djava.io.tmpdir=" + str(temporary_root / "java-temp"),
                    "-cp",
                    str(tla_tools),
                    "tlc2.TLC",
                    "-workers",
                    str(args.workers),
                    "-metadir",
                    str(state_dir),
                    "-config",
                    entry["config"],
                    entry["module"],
                ]
                try:
                    result = subprocess.run(
                        command,
                        cwd=snapshot,
                        capture_output=True,
                        timeout=args.timeout_seconds,
                    )
                    status = "passed" if result.returncode == 0 else "failed"
                    exit_code = result.returncode
                    output = result.stdout + result.stderr
                except subprocess.TimeoutExpired as error:
                    status = "timeout"
                    exit_code = None
                    output = (error.stdout or b"") + (error.stderr or b"")
                output_bytes = bytes(output)
                output_sha256 = hashlib.sha256(output_bytes).hexdigest()
                output_length = len(output_bytes)
            verify_snapshot(snapshot, inputs, hashes)
            scenario_reports.append(
                {
                    **entry,
                    "status": status,
                    "exit_code": exit_code,
                    "duration_ms": round((time.time() - scenario_started) * 1000),
                    "module_sha256": hashes[entry["module"]],
                    "config_sha256": hashes[entry["config"]],
                    "output_bytes": output_length,
                    "output_sha256": output_sha256,
                }
            )
        verify_snapshot(snapshot, inputs, hashes)
    report = {
        "schema_version": 1,
        "status": "dry_run" if args.dry_run else ("passed" if all(item["status"] == "passed" for item in scenario_reports) else "failed"),
        "generated_unix_seconds": int(time.time()),
        "source_revision": revision,
        "repository": ".",
        "runner": {"path": "artifact/run-linux.py", "sha256": runner_hash},
        "manifest": {"path": "formal/model-suite.json", "sha256": manifest_hash},
        "toolchain_lock": {
            "path": "artifact/toolchain.lock.json",
            "sha256": toolchain_lock_hash,
        },
        "suite": args.suite,
        "workers": args.workers,
        "timeout_seconds": args.timeout_seconds,
        "java": {"provided": java is not None, "version": java_version, "sha256": java_hash},
        "tla_tools": {
            "provided": tla_tools is not None,
            "version": lock["tla_tools"]["version"] if lock else None,
            "sha256": tla_hash,
        },
        "snapshot": {
            "inputs": inputs,
            "hashes": hashes,
            "isolated_read_only": True,
            "verified_before_and_after": True,
        },
        "scenarios": scenario_reports,
        "limitations": [
            "dry-run does not execute TLC",
            "Java provisioning is an explicit hash-pinned artifact prerequisite",
        ],
        "duration_ms": round((time.time() - started) * 1000),
    }
    report_path.parent.mkdir(parents=True, exist_ok=True)
    report_path.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(f"artifact {args.suite} status: {report['status']}; report: {report_path}")
    if report["status"] == "failed":
        return 1
    return 0


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("suite", choices=("smoke", "full"))
    parser.add_argument("--repository", default=".")
    parser.add_argument("--java")
    parser.add_argument("--java-sha256")
    parser.add_argument("--tla-tools")
    parser.add_argument("--workers", type=int, default=1)
    parser.add_argument("--report", required=True)
    parser.add_argument("--dry-run", action="store_true")
    parser.add_argument("--timeout-seconds", type=float, default=3600.0)
    args = parser.parse_args()
    if args.workers < 1 or args.workers > 32:
        parser.error("--workers must be between 1 and 32")
    if args.timeout_seconds <= 0:
        parser.error("--timeout-seconds must be positive")
    try:
        raise SystemExit(run(args))
    except RuntimeError as error:
        print(f"artifact runner error: {error}", file=sys.stderr)
        raise SystemExit(2) from error


if __name__ == "__main__":
    main()
