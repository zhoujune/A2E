#!/usr/bin/env python3
"""Compute the source and executable provenance for the K4-I1 harness."""

import argparse
import hashlib
import json
import os
import re
import shlex
import subprocess
import sys
from pathlib import Path


REVISION = re.compile(r"^[0-9a-fA-F]{40}$")

# These files define the K4-I1 executable boundary. The reference-broker and
# mechanized source directories are expanded so a transitive linked module
# cannot silently leave the source-manifest hash unchanged.
FIXED_SOURCE_FILES = (
    "artifact/k4_i1_provenance.py",
    "artifact/k4-i0-broker-kernel-harness.rs",
    "artifact/run-k4-i0.sh",
    "artifact/run-k4-i1.sh",
    "artifact/toolchain.lock.json",
    "mechanized/k4_crash_recovery_control.rs",
    "mechanized/k4_terminal_recovery_bridge.rs",
    "reference-broker/Cargo.toml",
    "reference-broker/Cargo.lock",
    "reference-broker/evaluation/evaluation-report.schema.v1.json",
    "reference-broker/evaluation/k4-i1-submission-evaluation.schema.v1.json",
    "reference-broker/evaluation/validate_report.py",
    "reference-broker/evaluation/validate_k4_i1.py",
)


def fail(message):
    raise RuntimeError(message)


def sha256_file(path):
    digest = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def git_source_revision(root):
    if not (root / ".git").exists():
        return None
    try:
        revision = subprocess.check_output(
            ["git", "rev-parse", "HEAD"],
            cwd=root,
            text=True,
            stderr=subprocess.DEVNULL,
        ).strip().lower()
    except (OSError, subprocess.CalledProcessError) as error:
        fail(f"cannot resolve repository HEAD: {error}")
    if not REVISION.fullmatch(revision):
        fail("repository HEAD is not a 40-hex revision")
    return revision


def source_revision(root):
    configured = os.environ.get("PROVEAI_SOURCE_REVISION")
    if configured is not None:
        if not REVISION.fullmatch(configured):
            fail("PROVEAI_SOURCE_REVISION is not a 40-hex revision")
        configured = configured.lower()
        repository_revision = git_source_revision(root)
        if repository_revision is not None and repository_revision != configured:
            fail("PROVEAI_SOURCE_REVISION does not match repository HEAD")
        return configured
    repository_revision = git_source_revision(root)
    if repository_revision is not None:
        return repository_revision
    revision_file = root / "artifact" / "source-revision.txt"
    if revision_file.is_file():
        revision = revision_file.read_text(encoding="utf-8").strip()
        if REVISION.fullmatch(revision):
            return revision.lower()
    fail("K4-I1 requires a 40-hex source revision")


def repository_source_revision(root):
    """Resolve a checkout revision, using an explicit value only for archives."""
    revision = git_source_revision(root)
    if revision is not None:
        return revision
    revision_file = root / "artifact" / "source-revision.txt"
    if revision_file.is_file():
        revision = revision_file.read_text(encoding="utf-8").strip()
        if REVISION.fullmatch(revision):
            return revision.lower()
    configured = os.environ.get("PROVEAI_SOURCE_REVISION")
    if configured is not None:
        if not REVISION.fullmatch(configured):
            fail("PROVEAI_SOURCE_REVISION is not a 40-hex revision")
        return configured.lower()
    fail("K4-I1 repository has no 40-hex source revision")


def source_paths(root):
    paths = {Path(relative) for relative in FIXED_SOURCE_FILES}
    source_dir = root / "reference-broker" / "src"
    if not source_dir.is_dir():
        fail(f"missing reference-broker source directory: {source_dir}")
    paths.update(
        path.relative_to(root)
        for path in source_dir.rglob("*.rs")
        if path.is_file()
    )
    mechanized_dir = root / "mechanized"
    if not mechanized_dir.is_dir():
        fail(f"missing mechanized source directory: {mechanized_dir}")
    paths.update(
        path.relative_to(root)
        for path in mechanized_dir.rglob("*.rs")
        if path.is_file()
    )
    return sorted(paths, key=lambda path: path.as_posix())


def source_manifest_sha256(root):
    manifest = hashlib.sha256()
    for relative in source_paths(root):
        path = root / relative
        if not path.is_file():
            fail(f"missing K4-I1 source file: {relative}")
        manifest.update(relative.as_posix().encode("utf-8"))
        manifest.update(b"\0")
        manifest.update(sha256_file(path).encode("ascii"))
        manifest.update(b"\n")
    return manifest.hexdigest()


def source_revision_matches(root, revision):
    """Check that a report revision still identifies the manifest inputs."""
    if not REVISION.fullmatch(revision):
        return False
    head = git_source_revision(root)
    if head is None:
        archive_revision = repository_source_revision(root)
        if archive_revision == revision.lower():
            return True
        release_manifest = root / "artifact" / "release-manifest.json"
        if not release_manifest.is_file():
            return False
        try:
            release = json.loads(release_manifest.read_text(encoding="utf-8"))
        except (OSError, ValueError):
            return False
        return (
            release.get("schema") == "proveai.fse.artifact-release"
            and release.get("archive_revision") == archive_revision
            and release.get("verified_source_revision") == revision.lower()
            and release.get("verified_source_manifest_sha256")
                == source_manifest_sha256(root)
        )
    if head == revision.lower():
        return True
    try:
        tracked = subprocess.check_output(
            ["git", "ls-tree", "-r", "--name-only", revision],
            cwd=root,
            text=True,
            stderr=subprocess.DEVNULL,
        ).splitlines()
    except (OSError, subprocess.CalledProcessError):
        return False
    source_names = {path.as_posix() for path in source_paths(root)}
    if not source_names.issubset(set(tracked)):
        return False
    result = subprocess.run(
        ["git", "diff", "--quiet", revision, "--", *sorted(source_names)],
        cwd=root,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
        check=False,
    )
    if result.returncode == 0:
        return True
    if result.returncode == 1:
        return False
    fail(f"cannot compare source manifest against revision {revision}")


def require_hash(path, description):
    path = Path(path)
    if not path.is_file():
        fail(f"missing {description}: {path}")
    return sha256_file(path)


def provenance(root, harness, kernel, broker, verus, rustc):
    return {
        "source_revision": source_revision(root),
        "source_manifest_sha256": source_manifest_sha256(root),
        "harness_sha256": require_hash(harness, "K4-I1 harness executable"),
        "kernel_rlib_sha256": require_hash(kernel, "proof-erased K4 kernel"),
        "broker_rlib_sha256": require_hash(broker, "reference-broker library"),
        "verus_executable_sha256": require_hash(verus, "Verus executable"),
        "rustc_executable_sha256": require_hash(rustc, "Rust compiler executable"),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repository", required=True)
    parser.add_argument("--harness", required=True)
    parser.add_argument("--kernel", required=True)
    parser.add_argument("--broker", required=True)
    parser.add_argument("--verus", required=True)
    parser.add_argument("--rustc", required=True)
    parser.add_argument("--shell", action="store_true")
    args = parser.parse_args()
    root = Path(args.repository).resolve()
    values = provenance(root, args.harness, args.kernel, args.broker, args.verus, args.rustc)
    if args.shell:
        environment_names = {
            "source_revision": "PROVEAI_SOURCE_REVISION",
            "source_manifest_sha256": "PROVEAI_K4_I1_SOURCE_MANIFEST_SHA256",
            "harness_sha256": "PROVEAI_K4_I1_HARNESS_SHA256",
            "kernel_rlib_sha256": "PROVEAI_K4_I1_KERNEL_RLIB_SHA256",
            "broker_rlib_sha256": "PROVEAI_K4_I1_BROKER_RLIB_SHA256",
            "verus_executable_sha256": "PROVEAI_K4_I1_VERUS_SHA256",
            "rustc_executable_sha256": "PROVEAI_K4_I1_RUSTC_SHA256",
        }
        for key, environment_name in environment_names.items():
            print(f"export {environment_name}={shlex.quote(values[key])}")
    else:
        import json

        print(json.dumps(values, indent=2, sort_keys=True))


if __name__ == "__main__":
    try:
        main()
    except (OSError, RuntimeError, subprocess.CalledProcessError) as error:
        print(f"K4-I1 provenance error: {error}", file=sys.stderr)
        raise SystemExit(2)
