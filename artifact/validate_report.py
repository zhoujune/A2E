#!/usr/bin/env python3
"""Validate Linux artifact runner reports without third-party dependencies."""

import json
import sys
from pathlib import Path


def require(condition, message):
    if not condition:
        raise ValueError(message)


def main():
    if len(sys.argv) != 2:
        raise SystemExit("usage: artifact/validate_report.py REPORT.json")
    path = Path(sys.argv[1])
    report = json.loads(path.read_text(encoding="utf-8"))
    require(report["schema_version"] == 1, "unsupported report schema")
    require(len(report["source_revision"]) >= 7, "source revision is missing")
    require(report["status"] in {"dry_run", "passed"}, "runner did not pass")
    require(report["suite"] in {"smoke", "full"}, "invalid suite")
    require(report["runner"]["sha256"] and len(report["runner"]["sha256"]) == 64, "runner hash missing")
    require(report["manifest"]["sha256"] and len(report["manifest"]["sha256"]) == 64, "manifest hash missing")
    inputs = report["snapshot"]["inputs"]
    hashes = report["snapshot"]["hashes"]
    require(report["snapshot"]["isolated_read_only"], "snapshot was not read-only")
    require(set(inputs) == set(hashes), "snapshot hash membership mismatch")
    expected_count = 13 if report["suite"] == "full" else 8
    require(len(report["scenarios"]) == expected_count, "scenario count mismatch")
    names = set()
    for scenario in report["scenarios"]:
        require(scenario["name"] not in names, "duplicate scenario")
        names.add(scenario["name"])
        require(scenario["module_sha256"] == hashes[scenario["module"]], "module hash mismatch")
        require(scenario["config_sha256"] == hashes[scenario["config"]], "config hash mismatch")
        require(scenario["status"] in {"dry_run", "passed"}, "scenario failed")
    if report["status"] == "passed":
        require(all(scenario["status"] == "passed" for scenario in report["scenarios"]), "root status mismatch")
        require(report["java"]["version"], "Java version missing")
        require(report["tla_tools"]["sha256"] and len(report["tla_tools"]["sha256"]) == 64, "TLA hash missing")
    print(f"validated Linux artifact report: {path}")


if __name__ == "__main__":
    main()
