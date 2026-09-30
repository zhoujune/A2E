#!/usr/bin/env python3
"""Build an anonymous artifact-only archive from the current source tree."""

import argparse
import gzip
import hashlib
import json
import os
import subprocess
import tarfile
import tempfile
import re
from pathlib import Path, PurePosixPath


PREFIX = "proveai-fse-artifact"
REVISION = re.compile(r"^[0-9a-f]{40}$")
SHA256 = re.compile(r"^[0-9a-f]{64}$")
ROOT_FILES = (
    ".gitattributes",
    "ARTIFACT.md",
    "DEPENDENCIES.md",
    "TROUBLESHOOTING.md",
    "LICENSE-APACHE",
    "LICENSE-MIT",
    "reproduce.sh",
    "reproduce.ps1",
    "artifact/release_package.py",
)
ROOT_DIRS = ("artifact", "formal", "kernel", "mechanized", "reference-broker")
EXCLUDED_DIRS = {
    ".git", ".toolbox", "__pycache__", "target", "tmp",
    "redis-process-crash-runs",
}
EXCLUDED_SUFFIXES = {
    ".pyc", ".pdf", ".tex", ".aux", ".log", ".out", ".blg", ".bbl",
    ".png", ".jpg", ".jpeg", ".svg", ".eps", ".rdb", ".aof", ".manifest",
}
EXCLUDED_FILES = {
    "artifact/README.md",
    "artifact/results/archive-smoke-preflight-7fc87a7.json",
    "artifact/results/linux-smoke-preflight.json",
    "artifact/results/README.md",
    "artifact/results/tla-full-5d8e8ed.json",
    "artifact/results/tla-smoke-5d8e8ed.json",
    "formal/README.md",
    "formal/agentbound-motivating-example.md",
    "formal/fse-2027-submission-contract.md",
    "formal/related-work-audit.md",
    "formal/results/README.md",
    "mechanized/README.md",
    "mechanized/results/README.md",
    "mechanized/results/verification-report-linux-5d8e8ed.json",
    "mechanized/results/verification-report-linux-9a45d39.json",
    "mechanized/results/verification-report-linux-offline-079f209.json",
    "reference-broker/evaluation/results/README.md",
}


def fail(message):
    raise RuntimeError(message)


def sha256(path):
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def revision(root):
    try:
        return subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=root, text=True,
            stderr=subprocess.DEVNULL,
        ).strip()
    except (OSError, subprocess.CalledProcessError):
        return "unavailable"


def dirty(root):
    try:
        return bool(subprocess.check_output(
            ["git", "status", "--porcelain=v1"], cwd=root, text=True,
            stderr=subprocess.DEVNULL,
        ).strip())
    except (OSError, subprocess.CalledProcessError):
        return None


def admitted(relative):
    path = PurePosixPath(relative.as_posix())
    if any(part in EXCLUDED_DIRS for part in path.parts):
        return False
    if any(part in {"paper", "paper-ndss"} or part.startswith("paper-") for part in path.parts):
        return False
    return (
        path.as_posix() not in EXCLUDED_FILES
        and path.suffix.lower() not in EXCLUDED_SUFFIXES
    )


def selected_files(root):
    tracked = None
    if (root / ".git").exists():
        try:
            result = subprocess.check_output(
                ["git", "ls-tree", "-r", "--name-only", "HEAD"],
                cwd=root,
            )
        except (OSError, subprocess.CalledProcessError) as error:
            fail(f"cannot enumerate committed release files: {error}")
        tracked = set(result.decode("utf-8").splitlines())
    paths = []
    for name in ROOT_FILES:
        path = root / name
        if not path.is_file():
            fail(f"required release file is missing: {name}")
        if tracked is not None and name not in tracked:
            fail(f"required release file is not committed: {name}")
        paths.append(path)
    for name in ROOT_DIRS:
        base = root / name
        if not base.is_dir():
            fail(f"required release directory is missing: {name}")
        for path in base.rglob("*"):
            if path.is_symlink():
                fail(f"symbolic links are not admitted: {path.relative_to(root)}")
            relative = path.relative_to(root)
            if (path.is_file() and admitted(relative)
                    and (tracked is None or relative.as_posix() in tracked)):
                paths.append(path)
    return sorted(set(paths), key=lambda item: item.relative_to(root).as_posix())


def add_file(archive, source, arcname):
    info = archive.gettarinfo(str(source), arcname)
    if PurePosixPath(arcname).suffix == ".sh":
        info.mode = 0o755
    info.uid = info.gid = 0
    info.uname = info.gname = ""
    info.mtime = 0
    with source.open("rb") as stream:
        archive.addfile(info, stream)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repository", default=".")
    parser.add_argument("--output", required=True)
    parser.add_argument("--allow-dirty", action="store_true")
    parser.add_argument("--verified-source-revision", required=True)
    parser.add_argument("--verified-source-manifest-sha256", required=True)
    args = parser.parse_args()
    root = Path(args.repository).resolve()
    output = Path(args.output).resolve()
    if not REVISION.fullmatch(args.verified_source_revision.lower()):
        fail("--verified-source-revision must be a 40-digit lowercase hexadecimal revision")
    if not SHA256.fullmatch(args.verified_source_manifest_sha256.lower()):
        fail("--verified-source-manifest-sha256 must be a 64-digit lowercase hexadecimal digest")
    try:
        from k4_i1_provenance import source_manifest_sha256, source_revision_matches
        observed_manifest = source_manifest_sha256(root)
        if observed_manifest != args.verified_source_manifest_sha256.lower():
            fail("verified source manifest does not match the release checkout")
        if not source_revision_matches(root, args.verified_source_revision.lower()):
            fail("verified source revision does not identify the release checkout")
    except ImportError as error:
        fail(f"cannot load K4 provenance checker: {error}")

    if output.exists():
        fail(f"refusing to overwrite release archive: {output}")
    state = dirty(root)
    if state and not args.allow_dirty:
        fail("worktree is dirty; commit the release snapshot or pass --allow-dirty")

    files = selected_files(root)
    with tempfile.TemporaryDirectory(prefix="proveai-fse-release-") as temporary:
        staging = Path(temporary) / PREFIX
        for source in files:
            relative = source.relative_to(root)
            destination = staging / relative
            destination.parent.mkdir(parents=True, exist_ok=True)
            destination.write_bytes(source.read_bytes())
            mode = source.stat().st_mode & 0o777
            if relative.suffix == ".sh" or relative.name == "reproduce.sh":
                mode = 0o755
            destination.chmod(mode)

        exported_revision = revision(root)
        (staging / "artifact" / "source-revision.txt").write_text(
            args.verified_source_revision.lower() + "\n", encoding="utf-8"
        )

        manifest_files = {}
        for path in sorted(staging.rglob("*")):
            if path.is_file():
                manifest_files[path.relative_to(staging).as_posix()] = sha256(path)
        manifest = {
            "schema": "proveai.fse.artifact-release",
            "schema_version": 1,
            "created_utc": "1970-01-01T00:00:00+00:00",
            "archive_revision": exported_revision,
            "verified_source_revision": args.verified_source_revision.lower(),
            "verified_source_manifest_sha256": args.verified_source_manifest_sha256.lower(),
            "dirty_worktree_snapshot": state,
            "paper_material_included": False,
            "files": manifest_files,
        }
        manifest_path = staging / "artifact" / "release-manifest.json"
        manifest_path.write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")

        output.parent.mkdir(parents=True, exist_ok=True)
        with output.open("wb") as raw:
            with gzip.GzipFile(fileobj=raw, mode="wb", filename="", mtime=0) as compressed:
                with tarfile.open(fileobj=compressed, mode="w", format=tarfile.PAX_FORMAT) as archive:
                    for path in sorted(staging.rglob("*")):
                        if path.is_file():
                            add_file(archive, path, f"{PREFIX}/{path.relative_to(staging).as_posix()}")

    print(f"created {output}")
    print(f"sha256 {sha256(output)}")
    print(f"files {len(files) + 1}; paper material included: false; dirty snapshot: {state}")


if __name__ == "__main__":
    try:
        main()
    except (OSError, RuntimeError, subprocess.CalledProcessError, tarfile.TarError) as error:
        print(f"release error: {error}", file=os.sys.stderr)
        raise SystemExit(2) from error
