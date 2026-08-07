#!/usr/bin/env python3
"""Validate internal accounting in a generated RQ3 proof-effort report."""

import json
import sys
from pathlib import Path


ADAPTERS = {
    "idempotent_ensure_member",
    "read_only_environment_sample",
    "deduplicated_keyed_decision",
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sum_field(targets, section, field):
    return sum(target[section][field] for target in targets)


def validate_summary(summary, targets, location):
    expected = {
        "target_count": len(targets),
        "source_bytes": sum_field(targets, "source", "bytes"),
        "source_lines": sum_field(targets, "source", "lines"),
        "nonblank_source_lines": sum_field(targets, "source", "nonblank_lines"),
        "proof_function_count": sum_field(targets, "source", "proof_function_count"),
        "spec_function_count": sum_field(targets, "source", "spec_function_count"),
        "executable_function_count": sum_field(targets, "source", "executable_function_count"),
        "type_declaration_count": sum_field(targets, "source", "type_declaration_count"),
        "verification_duration_ms": sum_field(targets, "verification", "duration_ms"),
        "non_duplicated_obligation_contribution": sum_field(
            targets, "verification", "non_duplicated_contribution"
        ),
    }
    for field, value in expected.items():
        require(summary[field] == value, f"{location}.{field} accounting mismatch")
    require(summary["person_hours"] is None, f"{location}.person_hours must remain null")


def validate_targets(targets, seen, location):
    require(isinstance(targets, list) and targets, f"{location} must contain targets")
    for target in targets:
        name = target["name"]
        require(name not in seen, f"target assigned twice: {name}")
        seen.add(name)
        source = target["source"]
        require(len(source["sha256"]) == 64, f"{name} source hash length")
        require(source["hash_validation"] in {"raw", "lf_normalized"}, f"{name} hash mode")
        require(source["proof_function_count"] == len(source["proof_functions"]), f"{name} proof count")
        require(target["verification"]["status"] == "passed", f"{name} did not pass")


def main():
    if len(sys.argv) != 2:
        raise SystemExit("usage: validate_rq3.py REPORT.json")
    path = Path(sys.argv[1])
    with path.open("r", encoding="utf-8") as stream:
        report = json.load(stream)
    require(report["schema_version"] == 1, "unsupported schema version")
    require(len(report["source_revision"]) >= 7, "missing source revision")
    verification = report["verification_report"]
    require(verification["registered_targets"] == verification["verified_targets"], "target failure")
    require(len(verification["sha256"]) == 64, "verification report hash length")

    seen = set()
    shared = report["shared_framework"]
    validate_targets(shared["targets"], seen, "shared_framework.targets")
    validate_summary(shared["summary"], shared["targets"], "shared_framework.summary")
    reusable = shared["summary"]["proof_function_count"]

    adapters = report["adapters"]
    require({adapter["name"] for adapter in adapters} == ADAPTERS, "adapter coverage mismatch")
    for adapter in adapters:
        location = f"adapters.{adapter['name']}"
        validate_targets(adapter["targets"], seen, f"{location}.targets")
        validate_summary(adapter["summary"], adapter["targets"], f"{location}.summary")
        require(
            adapter["summary"]["reusable_framework_proof_functions_available"] == reusable,
            f"{location} reusable proof count mismatch",
        )
        require(adapter["evidence_boundary"], f"{location} boundary is empty")
    print(f"validated RQ3 proof-effort report: {path}")


if __name__ == "__main__":
    main()
