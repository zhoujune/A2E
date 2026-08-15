#!/usr/bin/env python3
"""Dependency-free validator for the fail-closed K4-I1 attestation."""

import json
import sys
from pathlib import Path

REPOSITORY_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPOSITORY_ROOT))

from artifact.k4_i1_provenance import (  # noqa: E402
    source_manifest_sha256,
    source_revision_matches,
)

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


def hexadecimal(value, location, length):
    require(isinstance(value, str), f"{location} must be a string")
    require(len(value) == length and all(char in "0123456789abcdef" for char in value),
            f"{location} must be lowercase hexadecimal ({length} digits)")


def main():
    if len(sys.argv) != 2:
        raise SystemExit("usage: validate_k4_i1.py REPORT.json")
    path = Path(sys.argv[1])
    report = json.loads(path.read_text(encoding="utf-8"))
    exact_keys(
        report,
        {
            "schema",
            "schema_version",
            "provenance",
            "gate_profile",
            "broker_opens",
            "gate_evidence",
            "evaluation",
        },
        "report",
    )
    require(report["schema"] == "proveai.k4-i1-submission-evaluation", "wrong attestation schema")
    require(report["schema_version"] == 1, "unsupported attestation schema version")

    provenance = report["provenance"]
    exact_keys(
        provenance,
        {
            "source_revision",
            "source_manifest_sha256",
            "harness_sha256",
            "kernel_rlib_sha256",
            "broker_rlib_sha256",
            "verus_executable_sha256",
            "rustc_executable_sha256",
        },
        "provenance",
    )
    hexadecimal(provenance["source_revision"], "provenance.source_revision", 40)
    for name in (
        "source_manifest_sha256",
        "harness_sha256",
        "kernel_rlib_sha256",
        "broker_rlib_sha256",
        "verus_executable_sha256",
        "rustc_executable_sha256",
    ):
        hexadecimal(provenance[name], f"provenance.{name}", 64)
    require(
        source_revision_matches(REPOSITORY_ROOT, provenance["source_revision"]),
        "attestation source revision does not identify this checkout's manifest inputs",
    )
    require(
        provenance["source_manifest_sha256"] == source_manifest_sha256(REPOSITORY_ROOT),
        "attestation source manifest does not match this checkout",
    )

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
    require(
        report["evaluation"]["environment"]["source_revision"]
        == provenance["source_revision"],
        "evaluation environment revision does not match attestation revision",
    )
    print(f"validated K4-I1 submission attestation: {path}")


if __name__ == "__main__":
    main()
