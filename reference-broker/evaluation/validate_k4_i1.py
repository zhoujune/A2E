#!/usr/bin/env python3
"""Dependency-free validator for the fail-closed K4-I1 attestation."""

import json
import sys
from pathlib import Path

from validate_report import validate as validate_evaluation


def require(condition, message):
    if not condition:
        raise ValueError(message)


def exact_keys(value, expected, location):
    require(isinstance(value, dict), f"{location} must be an object")
    require(set(value) == set(expected), f"{location} keys are not exact")


def integer(value, location, minimum=0):
    require(isinstance(value, int) and not isinstance(value, bool), f"{location} must be an integer")
    require(value >= minimum, f"{location} must be >= {minimum}")


def main():
    if len(sys.argv) != 2:
        raise SystemExit("usage: validate_k4_i1.py REPORT.json")
    path = Path(sys.argv[1])
    report = json.loads(path.read_text(encoding="utf-8"))
    exact_keys(
        report,
        {"schema", "schema_version", "gate_profile", "broker_opens", "gate_evidence", "evaluation"},
        "report",
    )
    require(report["schema"] == "proveai.k4-i1-submission-evaluation", "wrong attestation schema")
    require(report["schema_version"] == 1, "unsupported attestation schema version")
    require(report["gate_profile"] == "k4-a4-required", "submission profile is not K4-A4-required")
    integer(report["broker_opens"], "broker_opens", 1)

    gate = report["gate_evidence"]
    exact_keys(
        gate,
        {
            "gates_created",
            "previews",
            "commits",
            "replays",
            "recoveries_started",
            "recoveries_finished",
            "recoveries_resumed",
        },
        "gate_evidence",
    )
    for name, value in gate.items():
        integer(value, f"gate_evidence.{name}")
    require(gate["gates_created"] == report["broker_opens"], "gate/open count mismatch")
    require(gate["previews"] > 0, "no K4 previews were observed")
    require(gate["previews"] == gate["commits"], "preview/commit count mismatch")
    require(gate["replays"] > 0, "no K4 replay was observed")
    require(gate["recoveries_started"] == report["broker_opens"], "recovery start count mismatch")
    require(
        gate["recoveries_finished"] + gate["recoveries_resumed"] == gate["recoveries_started"],
        "a K4 recovery instance was left open",
    )
    require(gate["recoveries_resumed"] > 0, "K4 resume branch was not exercised")

    validate_evaluation(report["evaluation"])
    print(f"validated K4-I1 submission attestation: {path}")


if __name__ == "__main__":
    main()
