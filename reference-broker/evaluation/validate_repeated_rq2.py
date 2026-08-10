#!/usr/bin/env python3
"""Validate repeated RQ2 samples, summaries, and protocol accounting."""

import json
import math
import sys
from pathlib import Path

from run_repeated_rq2 import PRIMARY, RETRY, aggregate


def require(condition, message):
    if not condition:
        raise ValueError(message)


def require_known_text(environment, field):
    value = environment.get(field)
    require(isinstance(value, str) and value.strip(), f"environment.{field} is missing")
    require(value.strip().lower() != "unknown", f"environment.{field} is unknown")


def compare_summary(actual, expected, location):
    require(set(actual) == set(expected), f"{location} metric fields mismatch")
    for metric in expected:
        require(set(actual[metric]) == set(expected[metric]), f"{location}.{metric} fields mismatch")
        for statistic, expected_value in expected[metric].items():
            actual_value = actual[metric][statistic]
            require(
                math.isclose(actual_value, expected_value, rel_tol=1e-12, abs_tol=1e-9),
                f"{location}.{metric}.{statistic} mismatch",
            )


def validate_samples(group, names, repetitions, requests, location):
    require(set(group) == set(names), f"{location} workload coverage mismatch")
    for name, evidence in group.items():
        samples = evidence["samples"]
        require(len(samples) == repetitions, f"{location}.{name} sample count mismatch")
        require(all(sample["requests"] == requests for sample in samples), f"{location}.{name} request mismatch")
        compare_summary(evidence["summary"], aggregate(samples), f"{location}.{name}.summary")


def main():
    if len(sys.argv) != 2:
        raise SystemExit("usage: validate_repeated_rq2.py REPORT.json")
    path = Path(sys.argv[1])
    with path.open("r", encoding="utf-8") as stream:
        report = json.load(stream)
    require(report["schema_version"] == 1, "unsupported schema version")
    require(len(report["source_revision"]) >= 7, "missing source revision")
    require(len(report["benchmark_binary_sha256"]) == 64, "binary hash length mismatch")
    protocol = report["protocol"]
    repetitions = protocol["repetitions"]
    primary_requests = protocol["iterations_per_primary_workload"]
    retry_requests = protocol["iterations_per_retry_workload"]
    require(protocol["warmups"] >= 1, "at least one warmup is required")
    require(repetitions >= 5, "at least five repetitions are required")
    require(protocol["workload_order"] == list(PRIMARY), "workload order mismatch")
    environment = report["environment"]
    require(environment["build_profile"] == "release", "report is not release mode")
    require(environment["source_revision"] == report["source_revision"], "environment revision mismatch")
    provenance_fields = (
        "hostname",
        "target",
        "rustc",
        "kernel_release",
        "python",
        "temporary_filesystem",
    )
    for field in provenance_fields:
        require_known_text(environment, field)
    mount_fields = (
        "temporary_mount_source",
        "temporary_mount_target",
        "temporary_mount_filesystem",
    )
    present_mount_fields = [field for field in mount_fields if field in environment]
    require(
        not present_mount_fields or len(present_mount_fields) == len(mount_fields),
        "temporary mount provenance is partial",
    )
    for field in present_mount_fields:
        require_known_text(environment, field)
    affinity = environment.get("cpu_affinity")
    require(isinstance(affinity, list) and affinity, "CPU affinity is missing")
    require(all(isinstance(cpu, int) and cpu >= 0 for cpu in affinity), "CPU affinity is invalid")
    require(report["limitations"], "limitations must be explicit")

    primary = report["primary_workloads"]
    retry = report["retry_workloads"]
    validate_samples(primary, PRIMARY, repetitions, primary_requests, "primary_workloads")
    validate_samples(retry, RETRY, repetitions, retry_requests, "retry_workloads")

    for sample in primary["mediated"]["samples"]:
        require(sample["flushes"] == primary_requests * 6, "mediated flush mismatch")
        require(sample["physical_invocations"] == primary_requests, "mediated invocation mismatch")
        require(sample["abstract_effects"] == primary_requests, "mediated effect mismatch")
    for sample in primary["direct"]["samples"]:
        require(sample["flushes"] == 0 and sample["wal_bytes"] == 0, "direct durability mismatch")
    for sample in primary["journaled_at_least_once"]["samples"]:
        require(sample["flushes"] == primary_requests * 2, "journaled flush mismatch")

    for name in ("mediated_idempotent", "mediated_deduplicated"):
        for sample in retry[name]["samples"]:
            require(sample["flushes"] == retry_requests * 8, f"{name} flush mismatch")
            require(sample["physical_invocations"] == retry_requests * 2, f"{name} invocation mismatch")
            require(sample["abstract_effects"] == retry_requests, f"{name} effect mismatch")
            require(sample["extra_effects"] == 0, f"{name} duplicated an effect")
    for sample in retry["journaled_at_least_once"]["samples"]:
        require(sample["flushes"] == retry_requests * 4, "retry journal flush mismatch")
        require(sample["abstract_effects"] == retry_requests * 2, "retry journal effect mismatch")
        require(sample["extra_effects"] == retry_requests, "retry journal duplicate mismatch")
    print(f"validated repeated RQ2 report: {path}")


if __name__ == "__main__":
    main()
