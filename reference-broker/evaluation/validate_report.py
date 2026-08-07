#!/usr/bin/env python3
"""Dependency-free validator for ProveAI evaluation report schema v1."""

import json
import sys
from pathlib import Path


ADAPTERS = {"uncontrolled", "idempotent", "deduplicated"}
CRASH_SITES = {
    "after_authorize",
    "after_prepare",
    "after_arm",
    "after_start",
    "after_invoke",
    "after_outcome",
    "after_terminal",
}
WORKLOADS = {"mediated", "direct", "journaled_at_least_once"}
RETRY_MECHANISMS = {
    "mediated_idempotent",
    "mediated_deduplicated",
    "journaled_at_least_once",
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def exact_keys(value, expected, location):
    require(isinstance(value, dict), f"{location} must be an object")
    actual = set(value)
    require(actual == set(expected), f"{location} keys: expected {sorted(expected)}, got {sorted(actual)}")


def integer(value, location, minimum=0):
    require(isinstance(value, int) and not isinstance(value, bool), f"{location} must be an integer")
    require(value >= minimum, f"{location} must be >= {minimum}")


def boolean(value, location):
    require(isinstance(value, bool), f"{location} must be a boolean")


def string(value, location):
    require(isinstance(value, str) and value, f"{location} must be a nonempty string")


def latency(value, location):
    exact_keys(value, {"mean", "p50", "p95", "p99"}, location)
    for name, measurement in value.items():
        integer(measurement, f"{location}.{name}")


def workload(value, location, requests):
    exact_keys(
        value,
        {
            "requests",
            "duration_ns",
            "throughput_requests_per_second",
            "latency_ns",
            "wal_bytes",
            "flushes",
            "recovery_ns",
            "physical_invocations",
            "abstract_effects",
        },
        location,
    )
    require(value["requests"] == requests, f"{location}.requests mismatch")
    for name in (
        "duration_ns",
        "wal_bytes",
        "flushes",
        "recovery_ns",
        "physical_invocations",
        "abstract_effects",
    ):
        integer(value[name], f"{location}.{name}")
    throughput = value["throughput_requests_per_second"]
    require(
        isinstance(throughput, (int, float)) and not isinstance(throughput, bool) and throughput >= 0,
        f"{location}.throughput_requests_per_second must be nonnegative",
    )
    latency(value["latency_ns"], f"{location}.latency_ns")


def retry(value, location, requests):
    exact_keys(
        value,
        {
            "mechanism",
            "requests",
            "duration_ns",
            "latency_ns",
            "physical_invocations",
            "abstract_effects",
            "extra_invocations",
            "extra_effects",
            "wal_bytes",
            "flushes",
        },
        location,
    )
    require(value["mechanism"] in RETRY_MECHANISMS, f"{location}.mechanism is invalid")
    require(value["requests"] == requests, f"{location}.requests mismatch")
    for name in (
        "duration_ns",
        "physical_invocations",
        "abstract_effects",
        "extra_invocations",
        "extra_effects",
        "wal_bytes",
        "flushes",
    ):
        integer(value[name], f"{location}.{name}")
    latency(value["latency_ns"], f"{location}.latency_ns")


def validate(report):
    exact_keys(
        report,
        {
            "schema_version",
            "generated_unix_seconds",
            "iterations",
            "retry_iterations",
            "environment",
            "rq1",
            "rq2",
        },
        "report",
    )
    require(report["schema_version"] == 1, "unsupported schema_version")
    integer(report["generated_unix_seconds"], "generated_unix_seconds")
    integer(report["iterations"], "iterations", 1)
    integer(report["retry_iterations"], "retry_iterations", 1)
    require(report["retry_iterations"] <= 100, "retry_iterations must be <= 100")

    environment = report["environment"]
    exact_keys(
        environment,
        {
            "hostname",
            "target",
            "rustc",
            "source_revision",
            "build_profile",
            "package_version",
            "logical_cpus",
        },
        "environment",
    )
    for name in ("hostname", "target", "rustc", "source_revision", "package_version"):
        string(environment[name], f"environment.{name}")
    require(environment["build_profile"] in {"debug", "release"}, "invalid build_profile")
    integer(environment["logical_cpus"], "environment.logical_cpus", 1)

    rq1 = report["rq1"]
    exact_keys(rq1, {"all_passed", "stale_delivery_rejected", "case_count", "cases"}, "rq1")
    boolean(rq1["all_passed"], "rq1.all_passed")
    boolean(rq1["stale_delivery_rejected"], "rq1.stale_delivery_rejected")
    require(rq1["all_passed"], "RQ1 did not pass")
    require(rq1["stale_delivery_rejected"], "stale delivery was not rejected")
    require(rq1["case_count"] == 21, "RQ1 case_count must be 21")
    require(isinstance(rq1["cases"], list) and len(rq1["cases"]) == 21, "RQ1 needs 21 cases")
    seen = set()
    case_keys = {
        "adapter",
        "crash_site",
        "terminal",
        "terminal_attempt",
        "physical_invocations",
        "abstract_effects",
        "terminal_records",
        "authorization_ancestry",
        "retry_bound_respected",
        "effect_oracle_satisfied",
        "passed",
    }
    for index, case in enumerate(rq1["cases"]):
        location = f"rq1.cases[{index}]"
        exact_keys(case, case_keys, location)
        require(case["adapter"] in ADAPTERS, f"{location}.adapter is invalid")
        require(case["crash_site"] in CRASH_SITES, f"{location}.crash_site is invalid")
        require(case["terminal"] in {"committed", "failed", "unknown"}, f"{location}.terminal is invalid")
        pair = (case["adapter"], case["crash_site"])
        require(pair not in seen, f"duplicate RQ1 pair {pair}")
        seen.add(pair)
        for name in ("terminal_attempt", "physical_invocations", "abstract_effects", "terminal_records"):
            integer(case[name], f"{location}.{name}")
        for name in ("authorization_ancestry", "retry_bound_respected", "effect_oracle_satisfied", "passed"):
            boolean(case[name], f"{location}.{name}")
            require(case[name], f"{location}.{name} must be true")
        require(case["terminal_records"] == 1, f"{location} does not have one terminal")
        require(case["terminal_attempt"] <= 3, f"{location} exceeds retry bound")
    expected_pairs = {(adapter, site) for adapter in ADAPTERS for site in CRASH_SITES}
    require(seen == expected_pairs, "RQ1 adapter/crash-site coverage mismatch")

    rq2 = report["rq2"]
    exact_keys(rq2, {"methodology", "workloads", "retry_scenarios"}, "rq2")
    exact_keys(
        rq2["methodology"],
        {"scope", "latency_clock", "mediated_flush_policy", "journaled_ablation"},
        "rq2.methodology",
    )
    for name, value in rq2["methodology"].items():
        string(value, f"rq2.methodology.{name}")
    exact_keys(rq2["workloads"], WORKLOADS, "rq2.workloads")
    for name, value in rq2["workloads"].items():
        workload(value, f"rq2.workloads.{name}", report["iterations"])

    mediated = rq2["workloads"]["mediated"]
    direct = rq2["workloads"]["direct"]
    journaled = rq2["workloads"]["journaled_at_least_once"]
    require(mediated["flushes"] == report["iterations"] * 6, "mediated flush count mismatch")
    require(mediated["physical_invocations"] == report["iterations"], "mediated invocation mismatch")
    require(mediated["abstract_effects"] == report["iterations"], "mediated effect mismatch")
    require(direct["wal_bytes"] == 0 and direct["flushes"] == 0, "direct baseline wrote a WAL")
    require(journaled["flushes"] == report["iterations"] * 2, "journaled flush count mismatch")

    scenarios = rq2["retry_scenarios"]
    require(isinstance(scenarios, list) and len(scenarios) == 3, "RQ2 needs three retry scenarios")
    by_name = {}
    for index, scenario in enumerate(scenarios):
        retry(scenario, f"rq2.retry_scenarios[{index}]", report["retry_iterations"])
        require(scenario["mechanism"] not in by_name, "duplicate retry mechanism")
        by_name[scenario["mechanism"]] = scenario
    require(set(by_name) == RETRY_MECHANISMS, "retry mechanism coverage mismatch")
    retry_requests = report["retry_iterations"]
    for name in ("mediated_idempotent", "mediated_deduplicated"):
        scenario = by_name[name]
        require(scenario["physical_invocations"] == retry_requests * 2, f"{name} invocation mismatch")
        require(scenario["abstract_effects"] == retry_requests, f"{name} effect mismatch")
        require(scenario["extra_invocations"] == retry_requests, f"{name} extra invocation mismatch")
        require(scenario["extra_effects"] == 0, f"{name} duplicated an effect")
        require(scenario["flushes"] == retry_requests * 8, f"{name} flush count mismatch")
    at_least_once = by_name["journaled_at_least_once"]
    require(at_least_once["physical_invocations"] == retry_requests * 2, "at-least-once invocation mismatch")
    require(at_least_once["abstract_effects"] == retry_requests * 2, "at-least-once effect mismatch")
    require(at_least_once["extra_effects"] == retry_requests, "at-least-once duplicate effect mismatch")
    require(at_least_once["flushes"] == retry_requests * 4, "at-least-once flush count mismatch")


def main():
    if len(sys.argv) != 2:
        raise SystemExit("usage: validate_report.py REPORT.json")
    path = Path(sys.argv[1])
    with path.open("r", encoding="utf-8") as stream:
        report = json.load(stream)
    validate(report)
    print(f"validated schema v1 report: {path}")


if __name__ == "__main__":
    main()
