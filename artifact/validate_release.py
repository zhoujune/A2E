#!/usr/bin/env python3
"""Validate an extracted NDSS artifact against its release manifest."""

import hashlib
import json
import sys
from pathlib import Path

from k4_i1_provenance import source_manifest_sha256


MANIFEST = Path("artifact/release-manifest.json")
EXCLUDED_DIRS = {".git", ".toolbox", "__pycache__", "target", "tmp"}


def digest(path):
    value = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            value.update(chunk)
    return value.hexdigest()


def fail(message):
    raise ValueError(message)


def main():
    root = Path(sys.argv[1] if len(sys.argv) == 2 else ".").resolve()
    manifest_path = root / MANIFEST
    if not manifest_path.is_file():
        fail(f"release manifest is missing: {manifest_path}")
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    if manifest.get("schema") != "proveai.fse.artifact-release":
        fail("unsupported release manifest schema")
    if manifest.get("schema_version") != 1:
        fail("unsupported release manifest version")
    if manifest.get("paper_material_included") is not False:
        fail("release manifest does not exclude paper material")
    if manifest.get("verified_source_manifest_sha256") != source_manifest_sha256(root):
        fail("release manifest does not match the packaged K4 source inputs")

    expected = manifest.get("files")
    if not isinstance(expected, dict) or not expected:
        fail("release manifest has no file map")
    observed = {}
    for path in root.rglob("*"):
        if not path.is_file() or path == manifest_path:
            continue
        relative = path.relative_to(root)
        if EXCLUDED_DIRS.intersection(relative.parts):
            continue
        observed[relative.as_posix()] = digest(path)
    if set(observed) != set(expected):
        missing = sorted(set(expected) - set(observed))
        extra = sorted(set(observed) - set(expected))
        fail(f"release membership mismatch; missing={missing}; extra={extra}")
    mismatched = sorted(path for path in expected if observed[path] != expected[path])
    if mismatched:
        fail(f"release file hash mismatch: {mismatched}")
    print(
        f"validated release manifest: {len(expected)} files; "
        f"archive_revision={manifest.get('archive_revision')}; "
        f"verified_source_revision={manifest.get('verified_source_revision')}; "
        f"dirty_snapshot={manifest.get('dirty_worktree_snapshot')}"
    )


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, json.JSONDecodeError) as error:
        print(f"release validation error: {error}", file=sys.stderr)
        raise SystemExit(2) from error
