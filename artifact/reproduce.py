#!/usr/bin/env python3
"""Top-level smoke/full release rehearsal for the ProveAI artifact."""

import argparse
import json
import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path


def fail(message):
    raise RuntimeError(message)


def command_exists(name):
    return shutil.which(name) is not None


def run_command(command, root, log_path, *, allow_missing=False):
    executable = command[0]
    if not command_exists(executable):
        if allow_missing:
            log_path.write_text(f"SKIPPED: missing executable {executable}\n", encoding="utf-8")
            return "skipped"
        fail(f"required executable is missing: {executable}")
    completed = subprocess.run(
        command,
        cwd=root,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
    )
    log_path.write_text(completed.stdout, encoding="utf-8")
    if completed.returncode != 0:
        raise RuntimeError(
            f"command failed ({completed.returncode}): {' '.join(command)}; log: {log_path}"
        )
    return "passed"


def run_artifact_runner(root, suite, report, dry_run, workers, timeout_seconds, logs):
    command = [
        sys.executable,
        "artifact/run-linux.py",
        suite,
        "--repository",
        str(root),
        "--report",
        str(report),
        "--workers",
        str(workers),
        "--timeout-seconds",
        str(timeout_seconds),
    ]
    if dry_run:
        command.append("--dry-run")
    return run_command(command, root, logs / "tla-runner.log")


def run_verus(root, report, logs, skip_verus, offline_bundle_root):
    if skip_verus:
        (logs / "verus.log").write_text("SKIPPED: --skip-verus\n", encoding="utf-8")
        return "skipped"
    if not command_exists("pwsh"):
        fail("PowerShell 7 (pwsh) is required for the Verus reproduction; use --skip-verus only for a TLA+/Rust rehearsal")
    command = [
        "pwsh",
        "-NoLogo",
        "-NoProfile",
        "-File",
        str(root / "mechanized" / "verify.ps1"),
        "-ReportPath",
        str(report),
    ]
    if offline_bundle_root:
        command.extend(["-OfflineBundleRoot", str(Path(offline_bundle_root).resolve())])
    return run_command(command, root, logs / "verus.log")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("suite", choices=("smoke", "full"))
    parser.add_argument("--repository", default=".")
    parser.add_argument("--output-directory")
    parser.add_argument("--offline-bundle-root", help="use a hash-checked offline Verus/Rust bundle")
    parser.add_argument("--workers", type=int, default=1)
    parser.add_argument("--timeout-seconds", type=float, default=3600.0)
    parser.add_argument("--dry-run", action="store_true", help="validate TLA+ packaging without executing TLC")
    parser.add_argument("--skip-verus", action="store_true", help="skip Verus; intended only for smoke preflight")
    parser.add_argument("--skip-rust", action="store_true", help="skip Rust checks; intended only for packaging preflight")
    args = parser.parse_args()
    if args.workers < 1 or args.workers > 32:
        parser.error("--workers must be between 1 and 32")
    if args.timeout_seconds <= 0:
        parser.error("--timeout-seconds must be positive")
    root = Path(args.repository).resolve()
    required_inputs = (
        root / "artifact" / "run-linux.py",
        root / "formal" / "model-suite.json",
        root / "mechanized" / "verify.ps1",
        root / "reference-broker" / "Cargo.toml",
    )
    missing_inputs = [str(path) for path in required_inputs if not path.is_file()]
    if missing_inputs:
        fail("repository snapshot is incomplete: " + ", ".join(missing_inputs))
    output = Path(args.output_directory).resolve() if args.output_directory else Path(tempfile.mkdtemp(prefix="proveai-reproduction-"))
    output.mkdir(parents=True, exist_ok=False) if not output.exists() else None
    logs = output / "logs"
    logs.mkdir()
    tla_report = output / f"tla-{args.suite}.json"
    verus_report = output / "verification-report.json"
    summary = {
        "schema_version": 1,
        "suite": args.suite,
        "dry_run": args.dry_run,
        "repository": str(root),
        "outputs": {"tla": str(tla_report), "verus": str(verus_report), "logs": str(logs)},
        "steps": {},
    }
    summary["steps"]["tla"] = run_artifact_runner(
        root, args.suite, tla_report, args.dry_run, args.workers, args.timeout_seconds, logs
    )
    run_command([sys.executable, "artifact/validate_report.py", str(tla_report)], root, logs / "tla-validate.log")
    summary["steps"]["tla_validate"] = "passed"
    if args.skip_rust:
        (logs / "cargo-fmt.log").write_text("SKIPPED: --skip-rust\n", encoding="utf-8")
        (logs / "cargo-test.log").write_text("SKIPPED: --skip-rust\n", encoding="utf-8")
        summary["steps"]["rust_fmt"] = "skipped"
        summary["steps"]["rust_test"] = "skipped"
    else:
        summary["steps"]["rust_fmt"] = run_command(["cargo", "fmt", "--manifest-path", str(root / "reference-broker" / "Cargo.toml"), "--", "--check"], root, logs / "cargo-fmt.log")
        summary["steps"]["rust_test"] = run_command(["cargo", "test", "--manifest-path", str(root / "reference-broker" / "Cargo.toml"), "--all-targets"], root, logs / "cargo-test.log")
    summary["steps"]["verus"] = run_verus(
        root,
        verus_report,
        logs,
        args.skip_verus or args.dry_run,
        args.offline_bundle_root,
    )
    summary_path = output / "reproduction-summary.json"
    summary_path.write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")
    print(f"reproduction {args.suite} complete: {summary_path}")


if __name__ == "__main__":
    try:
        main()
    except (OSError, RuntimeError, subprocess.SubprocessError) as error:
        print(f"reproduction error: {error}", file=sys.stderr)
        raise SystemExit(2) from error
