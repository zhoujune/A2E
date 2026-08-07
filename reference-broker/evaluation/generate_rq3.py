#!/usr/bin/env python3
"""Generate adapter proof-effort evidence from the retained Verus report."""

import argparse
import hashlib
import json
import os
import re
import subprocess
import time
from pathlib import Path


PROOF_FN = re.compile(r"^\s*pub\s+proof\s+fn\s+([A-Za-z0-9_]+)", re.MULTILINE)
SPEC_FN = re.compile(r"^\s*pub\s+(?:open\s+)?spec\s+fn\s+([A-Za-z0-9_]+)", re.MULTILINE)
EXEC_FN = re.compile(r"^\s*pub\s+fn\s+([A-Za-z0-9_]+)", re.MULTILINE)
TYPE_DECL = re.compile(r"^\s*pub\s+(?:struct|enum)\s+([A-Za-z0-9_]+)", re.MULTILINE)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def load_json(path):
    with path.open("r", encoding="utf-8") as stream:
        return json.load(stream)


def sha256(path):
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def sha256_bytes(value):
    return hashlib.sha256(value).hexdigest()


def source_metrics(path, expected_sha256):
    require(path.is_file(), f"missing source: {path}")
    raw = path.read_bytes()
    actual_sha256 = sha256_bytes(raw)
    normalized_sha256 = sha256_bytes(raw.replace(b"\r\n", b"\n"))
    require(
        expected_sha256 in {actual_sha256, normalized_sha256},
        f"source hash mismatch: {path}",
    )
    text = raw.decode("utf-8")
    lines = text.splitlines()
    proof_functions = PROOF_FN.findall(text)
    spec_functions = SPEC_FN.findall(text)
    executable_functions = EXEC_FN.findall(text)
    type_declarations = TYPE_DECL.findall(text)
    return {
        "path": path.as_posix(),
        "sha256": expected_sha256,
        "hash_validation": "raw" if actual_sha256 == expected_sha256 else "lf_normalized",
        "bytes": path.stat().st_size,
        "lines": len(lines),
        "nonblank_lines": sum(bool(line.strip()) for line in lines),
        "proof_function_count": len(proof_functions),
        "spec_function_count": len(spec_functions),
        "executable_function_count": len(executable_functions),
        "type_declaration_count": len(type_declarations),
        "proof_functions": proof_functions,
    }


def revision():
    configured = os.environ.get("PROVEAI_SOURCE_REVISION")
    if configured:
        return configured
    try:
        return subprocess.check_output(
            ["git", "rev-parse", "HEAD"], text=True, stderr=subprocess.DEVNULL
        ).strip()
    except (OSError, subprocess.CalledProcessError):
        return "unknown"


def target_evidence(target, repository):
    source_path = repository / target["source_path"]
    metrics = source_metrics(source_path, target["source_sha256"])
    metrics["path"] = target["source_path"]
    return {
        "name": target["name"],
        "source": metrics,
        "verification": {
            "status": target["status"],
            "duration_ms": target["duration_ms"],
            "cumulative_verified_obligations": target["verified_obligations_total"],
            "non_duplicated_contribution": target["contribution_delta"],
            "contribution_mode": target["contribution_mode"],
            "contribution_parent": target["contribution_parent"],
        },
    }


def summarize(targets):
    return {
        "target_count": len(targets),
        "source_bytes": sum(target["source"]["bytes"] for target in targets),
        "source_lines": sum(target["source"]["lines"] for target in targets),
        "nonblank_source_lines": sum(target["source"]["nonblank_lines"] for target in targets),
        "proof_function_count": sum(target["source"]["proof_function_count"] for target in targets),
        "spec_function_count": sum(target["source"]["spec_function_count"] for target in targets),
        "executable_function_count": sum(target["source"]["executable_function_count"] for target in targets),
        "type_declaration_count": sum(target["source"]["type_declaration_count"] for target in targets),
        "verification_duration_ms": sum(target["verification"]["duration_ms"] for target in targets),
        "non_duplicated_obligation_contribution": sum(
            target["verification"]["non_duplicated_contribution"] for target in targets
        ),
        "person_hours": None,
    }


def generate(repository, report_path, manifest_path):
    report = load_json(report_path)
    manifest = load_json(manifest_path)
    require(report["status"] == "passed", "verification report did not pass")
    require(manifest["schema_version"] == 1, "unsupported manifest schema")
    by_name = {target["name"]: target for target in report["targets"]}

    shared_targets = [
        target_evidence(by_name[name], repository)
        for name in manifest["shared_framework_targets"]
    ]
    adapters = []
    assigned = set(manifest["shared_framework_targets"])
    for adapter in manifest["adapters"]:
        overlap = assigned.intersection(adapter["targets"])
        require(not overlap, f"targets assigned more than once: {sorted(overlap)}")
        assigned.update(adapter["targets"])
        targets = [target_evidence(by_name[name], repository) for name in adapter["targets"]]
        summary = summarize(targets)
        summary["reusable_framework_proof_functions_available"] = sum(
            target["source"]["proof_function_count"] for target in shared_targets
        )
        adapters.append(
            {
                "name": adapter["name"],
                "retry_class": adapter["retry_class"],
                "evidence_boundary": adapter["evidence_boundary"],
                "summary": summary,
                "targets": targets,
            }
        )

    return {
        "schema_version": 1,
        "generated_unix_seconds": int(time.time()),
        "source_revision": revision(),
        "verification_report": {
            "path": report_path.relative_to(repository).as_posix(),
            "sha256": sha256(report_path),
            "schema_version": report["schema_version"],
            "registered_targets": report["summary"]["registered_target_count"],
            "verified_targets": report["summary"]["verified_target_count"],
            "non_duplicated_verified_obligations": report["summary"][
                "non_duplicated_verified_obligations"
            ],
        },
        "measurement_notes": {
            "verification_time": "sum of retained per-target wall-clock durations; dependencies are rechecked in each target",
            "obligations": "sum of retained non-duplicated contribution deltas for explicitly assigned targets",
            "reusable_lemmas": "public proof functions in the shared T6-D0/E0/C0/S0 framework",
            "person_hours": "not contemporaneously recorded; null rather than inferred from source size",
        },
        "shared_framework": {
            "summary": summarize(shared_targets),
            "targets": shared_targets,
        },
        "adapters": adapters,
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--repository", type=Path, default=Path(".."))
    parser.add_argument(
        "--report", type=Path, default=Path("../mechanized/results/verification-report.json")
    )
    parser.add_argument("--manifest", type=Path, default=Path("evaluation/rq3-adapter-manifest.v1.json"))
    parser.add_argument("--output", type=Path, required=True)
    arguments = parser.parse_args()
    repository = arguments.repository.resolve()
    report_path = arguments.report.resolve()
    manifest_path = arguments.manifest.resolve()
    result = generate(repository, report_path, manifest_path)
    arguments.output.parent.mkdir(parents=True, exist_ok=True)
    arguments.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(f"generated RQ3 evidence for {len(result['adapters'])} adapters: {arguments.output}")


if __name__ == "__main__":
    main()
