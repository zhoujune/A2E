#!/usr/bin/env python3
"""Check the retained Redis case evidence against its summary report."""

import hashlib
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
REPORT = ROOT / "reference-broker/evaluation/results/redis-process-crash.json"
EVIDENCE = ROOT / "reference-broker/evaluation/evidence/redis-process-crash"


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    report = json.loads(REPORT.read_text(encoding="utf-8"))
    assert report["status"] == "passed"
    assert len(report["cases"]) == 8
    observed = set()
    for expected in report["cases"]:
        name = f"{expected['variant']}-{expected['scenario']}"
        assert name not in observed, name
        observed.add(name)
        case_dir = EVIDENCE / name
        case = json.loads((case_dir / "case.json").read_text(encoding="utf-8"))
        for key in ("variant", "scenario", "oracle", "terminal", "effect",
                    "preterminal_wal_sha256", "initial_wal_sha256"):
            assert case[key] == expected[key], f"{name}: {key} differs"
        assert sha256(case_dir / "preterminal.wal") == expected["preterminal_wal_sha256"]
        if expected["initial_wal_sha256"] is not None:
            assert sha256(case_dir / "initial.wal") == expected["initial_wal_sha256"]
        assert (case_dir / "service/appendonlydir/appendonly.aof.1.base.rdb").is_file()
        assert (case_dir / "service/appendonlydir/appendonly.aof.1.incr.aof").is_file()

    for variant in ("full", "without_failure_coverage"):
        before = EVIDENCE / f"{variant}-uninvoked_then_rejected"
        after = EVIDENCE / f"{variant}-effect_then_rejected"
        assert (before / "preterminal.wal").read_bytes() == (after / "preterminal.wal").read_bytes()
        assert (before / "initial.wal").read_bytes() == (after / "initial.wal").read_bytes()
    assert (EVIDENCE / "ablation.patch").is_file()
    print("validated Redis evidence: 8 cases, WAL hashes, paired prefixes, and ablation patch")


if __name__ == "__main__":
    main()
