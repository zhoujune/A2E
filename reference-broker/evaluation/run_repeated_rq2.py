#!/usr/bin/env python3
"""Run independent M4 RQ2 repetitions and retain raw samples plus uncertainty."""

import argparse
import hashlib
import json
import math
import os
import platform
import statistics
import subprocess
import sys
import tempfile
import time
from pathlib import Path


Z_95 = 1.959963984540054
PRIMARY = ("mediated", "direct", "journaled_at_least_once")
RETRY = (
    "mediated_idempotent",
    "mediated_deduplicated",
    "journaled_at_least_once",
)
WORKLOAD_FIELDS = (
    "requests",
    "duration_ns",
    "throughput_requests_per_second",
    "wal_bytes",
    "flushes",
    "recovery_ns",
    "physical_invocations",
    "abstract_effects",
)
RETRY_FIELDS = (
    "requests",
    "duration_ns",
    "physical_invocations",
    "abstract_effects",
    "extra_invocations",
    "extra_effects",
    "wal_bytes",
    "flushes",
)
LATENCY_FIELDS = ("mean", "p50", "p95", "p99")


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha256(path):
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def source_revision():
    configured = os.environ.get("PROVEAI_SOURCE_REVISION")
    if configured:
        return configured
    return subprocess.check_output(
        ["git", "rev-parse", "HEAD"], text=True, stderr=subprocess.DEVNULL
    ).strip()


def filesystem_type(path):
    try:
        return subprocess.check_output(
            ["stat", "-f", "-c", "%T", str(path)],
            text=True,
            stderr=subprocess.DEVNULL,
        ).strip()
    except (OSError, subprocess.CalledProcessError):
        return "unknown"


def mount_provenance(path):
    try:
        raw = subprocess.check_output(
            [
                "findmnt",
                "--json",
                "--target",
                str(path),
                "--output",
                "SOURCE,TARGET,FSTYPE",
            ],
            text=True,
            stderr=subprocess.DEVNULL,
        )
        filesystems = json.loads(raw).get("filesystems", [])
        require(len(filesystems) == 1, "temporary mount lookup is ambiguous")
        filesystem = filesystems[0]
        source = filesystem.get("source")
        target = filesystem.get("target")
        filesystem_type_name = filesystem.get("fstype")
        require(
            all(
                isinstance(value, str) and value
                for value in (source, target, filesystem_type_name)
            ),
            "temporary mount provenance is incomplete",
        )
        # findmnt appends a bind-mount subpath in brackets; retain the backing device.
        source = source.partition("[")[0]
        return {
            "temporary_mount_source": source,
            "temporary_mount_target": target,
            "temporary_mount_filesystem": filesystem_type_name,
        }
    except (OSError, subprocess.CalledProcessError, json.JSONDecodeError, ValueError):
        return {}


def cpu_affinity():
    if hasattr(os, "sched_getaffinity"):
        return sorted(os.sched_getaffinity(0))
    return []


def run_once(binary, iterations, output, revision):
    environment = os.environ.copy()
    environment["PROVEAI_SOURCE_REVISION"] = revision
    completed = subprocess.run(
        [str(binary), "--iterations", str(iterations), "--output", str(output)],
        check=True,
        capture_output=True,
        text=True,
        env=environment,
    )
    with output.open("r", encoding="utf-8") as stream:
        report = json.load(stream)
    require(report["schema_version"] == 1, "single-run schema mismatch")
    require(report["rq1"]["all_passed"], "single-run RQ1 check failed")
    require(report["environment"]["build_profile"] == "release", "binary is not release mode")
    require(report["environment"]["source_revision"] == revision, "source revision mismatch")
    require(report["iterations"] == iterations, "iteration mismatch")
    return report, completed.stdout.strip()


def flatten_workload(workload):
    sample = {field: workload[field] for field in WORKLOAD_FIELDS}
    for field in LATENCY_FIELDS:
        sample[f"latency_{field}_ns"] = workload["latency_ns"][field]
    return sample


def flatten_retry(retry):
    sample = {field: retry[field] for field in RETRY_FIELDS}
    for field in LATENCY_FIELDS:
        sample[f"latency_{field}_ns"] = retry["latency_ns"][field]
    return sample


def metric_summary(values):
    count = len(values)
    mean = statistics.fmean(values)
    standard_deviation = statistics.stdev(values)
    margin = Z_95 * standard_deviation / math.sqrt(count)
    return {
        "mean": mean,
        "median": statistics.median(values),
        "standard_deviation": standard_deviation,
        "ci95_low": max(0.0, mean - margin),
        "ci95_high": mean + margin,
        "minimum": min(values),
        "maximum": max(values),
    }


def aggregate(samples):
    fields = samples[0].keys()
    return {field: metric_summary([sample[field] for sample in samples]) for field in fields}


def extract(report, primary_samples, retry_samples):
    workloads = report["rq2"]["workloads"]
    require(set(workloads) == set(PRIMARY), "primary workload coverage mismatch")
    for name in PRIMARY:
        primary_samples[name].append(flatten_workload(workloads[name]))
    retries = {entry["mechanism"]: entry for entry in report["rq2"]["retry_scenarios"]}
    require(set(retries) == set(RETRY), "retry workload coverage mismatch")
    for name in RETRY:
        retry_samples[name].append(flatten_retry(retries[name]))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--binary", type=Path, default=Path("target/release/evaluate"))
    parser.add_argument("--iterations", type=int, default=500)
    parser.add_argument("--warmups", type=int, default=5)
    parser.add_argument("--repetitions", type=int, default=30)
    parser.add_argument("--inter-run-delay-ms", type=int, default=25)
    parser.add_argument("--output", type=Path, required=True)
    arguments = parser.parse_args()
    require(arguments.iterations > 0, "iterations must be positive")
    require(arguments.warmups >= 0, "warmups cannot be negative")
    require(arguments.repetitions >= 5, "at least five measured repetitions are required")
    require(arguments.inter_run_delay_ms >= 0, "inter-run delay cannot be negative")
    binary = arguments.binary.resolve()
    require(binary.is_file(), f"benchmark binary not found: {binary}")
    revision = source_revision()
    primary_samples = {name: [] for name in PRIMARY}
    retry_samples = {name: [] for name in RETRY}

    with tempfile.TemporaryDirectory(prefix="proveai-rq2-repeated-") as temporary:
        temporary_path = Path(temporary)
        for index in range(arguments.warmups):
            run_once(binary, arguments.iterations, temporary_path / f"warmup-{index}.json", revision)
            print(f"warmup {index + 1}/{arguments.warmups}")
        first_environment = None
        retry_iterations = None
        for index in range(arguments.repetitions):
            report, message = run_once(
                binary,
                arguments.iterations,
                temporary_path / f"measured-{index}.json",
                revision,
            )
            if first_environment is None:
                first_environment = report["environment"]
                retry_iterations = report["retry_iterations"]
            else:
                require(report["environment"] == first_environment, "environment changed between runs")
                require(report["retry_iterations"] == retry_iterations, "retry iteration mismatch")
            extract(report, primary_samples, retry_samples)
            print(f"measured {index + 1}/{arguments.repetitions}: {message}")
            if arguments.inter_run_delay_ms:
                time.sleep(arguments.inter_run_delay_ms / 1000.0)

        result = {
            "schema_version": 1,
            "generated_unix_seconds": int(time.time()),
            "source_revision": revision,
            "benchmark_binary_sha256": sha256(binary),
            "protocol": {
                "warmups": arguments.warmups,
                "repetitions": arguments.repetitions,
                "iterations_per_primary_workload": arguments.iterations,
                "iterations_per_retry_workload": retry_iterations,
                "inter_run_delay_ms": arguments.inter_run_delay_ms,
                "process_isolation": "fresh evaluate process and fresh temporary WALs per run",
                "workload_order": list(PRIMARY),
                "confidence_method": "95% normal approximation over independent run-level measurements",
                "confidence_z": Z_95,
            },
            "environment": {
                **first_environment,
                "kernel_release": platform.release(),
                "python": platform.python_version(),
                "cpu_affinity": cpu_affinity(),
                "temporary_filesystem": filesystem_type(Path(tempfile.gettempdir())),
                **mount_provenance(Path(tempfile.gettempdir())),
            },
            "primary_workloads": {
                name: {"summary": aggregate(samples), "samples": samples}
                for name, samples in primary_samples.items()
            },
            "retry_workloads": {
                name: {"summary": aggregate(samples), "samples": samples}
                for name, samples in retry_samples.items()
            },
            "limitations": [
                "workload order is fixed within each run",
                "the direct tool is an in-process operation and is below reliable wall-clock granularity",
                "the service is local and synchronous; network latency is not modeled",
                "the temporary filesystem may not represent a physical storage device",
                "normal-approximation intervals do not replace a broader multi-host evaluation",
            ],
        }
    arguments.output.parent.mkdir(parents=True, exist_ok=True)
    arguments.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(f"retained {arguments.repetitions} measured RQ2 repetitions: {arguments.output}")


if __name__ == "__main__":
    main()
