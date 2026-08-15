#!/usr/bin/env python3
"""Fail-closed validator for theorem/premise traceability."""

import hashlib
import json
import sys
from pathlib import Path


ROOT_KEYS = {"schema", "schema_version", "verification_report", "paper_source", "entries"}
ENTRY_KEYS = {"id", "claim_class", "boundary", "paper", "formal", "evidence", "caveats"}
PAPER_KEYS = {"anchors", "claim"}
FORMAL_KEYS = {
    "source_files",
    "symbols",
    "premise_symbols",
    "conclusion_symbols",
    "premises",
    "conclusions",
}
EVIDENCE_KEYS = {"kind", "targets", "witnesses", "paths", "attestation"}
WITNESS_KEYS = {"path", "symbols"}
ATTESTATION_KEYS = {"path", "validator", "assertions"}
ASSERTION_KEYS = {"path", "equals"}


def fail(message):
    raise ValueError(message)


def exact_keys(value, expected, location):
    if not isinstance(value, dict) or set(value) != expected:
        fail(f"{location} keys are not exact")


def require(condition, message):
    if not condition:
        fail(message)


def safe_relative(path_value, location, root):
    path = Path(path_value)
    require(not path.is_absolute() and ".." not in path.parts, f"{location} must be relative")
    resolved = (root / path).resolve()
    require(resolved == root or root in resolved.parents, f"{location} escapes repository root")
    return resolved


def require_string_list(value, location, minimum=1):
    require(isinstance(value, list) and len(value) >= minimum, f"{location} must be a nonempty list")
    require(all(isinstance(item, str) and item for item in value), f"{location} contains a non-string")


def get_path(value, path_value):
    current = value
    for component in path_value.split("."):
        require(isinstance(current, dict) and component in current, f"attestation path is missing: {path_value}")
        current = current[component]
    return current


def validate(root, manifest_path):
    exact_keys(root, ROOT_KEYS, "manifest")
    require(root["schema"] == "proveai.theorem-premise-traceability", "wrong traceability schema")
    require(root["schema_version"] == 1, "unsupported traceability schema version")
    repository_root = manifest_path.resolve().parents[1]
    report_path = safe_relative(root["verification_report"], "verification_report", repository_root)
    paper_path = safe_relative(root["paper_source"], "paper_source", repository_root)
    require(report_path.exists(), f"verification report is missing: {report_path}")
    require(paper_path.exists(), f"paper source is missing: {paper_path}")
    paper_text = paper_path.read_text(encoding="utf-8")
    labels = set()
    for marker in ("\\label{",):
        start = 0
        while True:
            start = paper_text.find(marker, start)
            if start < 0:
                break
            end = paper_text.find("}", start + len(marker))
            require(end >= 0, "unterminated paper label")
            labels.add(paper_text[start + len(marker):end])
            start = end + 1

    report = json.loads(report_path.read_text(encoding="utf-8"))
    require(report.get("schema") == "vetra.verus-verification-report", "unsupported verification report")
    require(report.get("status") == "passed", "verification report is not passed")
    targets = {target["name"]: target for target in report.get("targets", [])}
    entries = root["entries"]
    require(isinstance(entries, list) and entries, "entries must be nonempty")
    seen_ids = set()
    for index, entry in enumerate(entries):
        location = f"entries[{index}]"
        exact_keys(entry, ENTRY_KEYS, location)
        require(entry["id"] not in seen_ids, f"duplicate entry id: {entry['id']}")
        seen_ids.add(entry["id"])
        require(isinstance(entry["claim_class"], str) and entry["claim_class"], f"{location}.claim_class missing")
        require(entry["boundary"] in {"proved", "conditional-composition", "kernel-in-loop-evidence", "dynamic-attestation", "unverified-implementation"}, f"{location}.boundary invalid")
        require_string_list(entry["caveats"], f"{location}.caveats")

        paper = entry["paper"]
        exact_keys(paper, PAPER_KEYS, f"{location}.paper")
        require_string_list(paper["anchors"], f"{location}.paper.anchors")
        require(all(anchor in labels for anchor in paper["anchors"]), f"{location}.paper has an unresolved label")
        require(isinstance(paper["claim"], str) and paper["claim"], f"{location}.paper.claim missing")

        formal = entry["formal"]
        exact_keys(formal, FORMAL_KEYS, f"{location}.formal")
        require_string_list(formal["source_files"], f"{location}.formal.source_files")
        require_string_list(formal["symbols"], f"{location}.formal.symbols")
        require_string_list(formal["premise_symbols"], f"{location}.formal.premise_symbols")
        require_string_list(formal["conclusion_symbols"], f"{location}.formal.conclusion_symbols")
        require_string_list(formal["premises"], f"{location}.formal.premises")
        require_string_list(formal["conclusions"], f"{location}.formal.conclusions")
        source_text = "\n".join(
            safe_relative(path_value, f"{location}.formal.source_files", repository_root).read_text(encoding="utf-8")
            for path_value in formal["source_files"]
        )
        for symbol_group, symbols in (
            ("symbols", formal["symbols"]),
            ("premise_symbols", formal["premise_symbols"]),
            ("conclusion_symbols", formal["conclusion_symbols"]),
        ):
            for symbol in symbols:
                require(symbol in source_text, f"{location}.{symbol_group} symbol is not present: {symbol}")

        evidence = entry["evidence"]
        require(isinstance(evidence, dict), f"{location}.evidence must be an object")
        require(set(evidence).issubset(EVIDENCE_KEYS), f"{location}.evidence has unknown keys")
        require(evidence.get("kind") in {"verus-target", "kernel-in-loop", "attestation", "documented-boundary"}, f"{location}.evidence.kind invalid")
        require_string_list(evidence.get("targets", []), f"{location}.evidence.targets", minimum=0)
        if "paths" in evidence:
            require_string_list(evidence["paths"], f"{location}.evidence.paths", minimum=0)
        require(isinstance(evidence.get("witnesses"), list), f"{location}.evidence.witnesses must be a list")
        for witness_index, witness in enumerate(evidence["witnesses"]):
            exact_keys(witness, WITNESS_KEYS, f"{location}.evidence.witnesses[{witness_index}]")
            witness_path = safe_relative(
                witness["path"],
                f"{location}.evidence.witnesses[{witness_index}].path",
                repository_root,
            )
            require(witness_path.exists(), f"missing witness: {witness_path}")
            require_string_list(witness["symbols"], f"{location}.evidence.witnesses[{witness_index}].symbols")
            witness_text = witness_path.read_text(encoding="utf-8")
            for symbol in witness["symbols"]:
                require(symbol in witness_text, f"witness symbol is not present: {symbol}")
        for path_value in evidence.get("paths", []):
            require(
                safe_relative(path_value, f"{location}.evidence.paths", repository_root).exists(),
                f"missing evidence path: {path_value}",
            )

        if evidence["kind"] == "verus-target":
            target_names = evidence.get("targets", [])
            require(target_names, f"{location} Verus evidence has no target")
            for target_name in target_names:
                require(target_name in targets, f"unknown verification target: {target_name}")
                target = targets[target_name]
                require(target["status"] == "passed" and target["verus_errors"] == 0, f"target is not passed: {target_name}")
                source_path = safe_relative(
                    target["source_path"],
                    f"target {target_name}.source_path",
                    repository_root,
                )
                require(source_path.exists(), f"target source is missing: {source_path}")
                digest = hashlib.sha256(source_path.read_bytes()).hexdigest()
                require(digest == target["source_sha256"], f"target source hash mismatch: {target_name}")
        elif evidence["kind"] == "attestation":
            attestation = evidence.get("attestation")
            require(isinstance(attestation, dict), f"{location} attestation evidence is missing details")
            exact_keys(attestation, ATTESTATION_KEYS, f"{location}.evidence.attestation")
            attestation_path = safe_relative(
                attestation["path"], f"{location}.attestation.path", repository_root
            )
            validator_path = safe_relative(
                attestation["validator"], f"{location}.attestation.validator", repository_root
            )
            require(attestation_path.exists() and validator_path.exists(), f"{location} attestation files are missing")
            attestation_value = json.loads(attestation_path.read_text(encoding="utf-8"))
            require(isinstance(attestation["assertions"], list) and attestation["assertions"], f"{location}.attestation.assertions empty")
            for assertion_index, assertion in enumerate(attestation["assertions"]):
                exact_keys(assertion, ASSERTION_KEYS, f"{location}.attestation.assertions[{assertion_index}]")
                require(get_path(attestation_value, assertion["path"]) == assertion["equals"], f"attestation assertion failed: {assertion['path']}")

    return len(entries)


def main():
    if len(sys.argv) != 2:
        raise SystemExit("usage: python formal/validate_traceability.py MANIFEST.json")
    manifest_path = Path(sys.argv[1])
    root = json.loads(manifest_path.read_text(encoding="utf-8"))
    count = validate(root, manifest_path)
    print(f"validated theorem/premise traceability: {manifest_path} ({count} entries)")


if __name__ == "__main__":
    try:
        main()
    except (OSError, UnicodeDecodeError, ValueError, json.JSONDecodeError) as error:
        print(f"traceability validation error: {error}", file=sys.stderr)
        raise SystemExit(2) from error
