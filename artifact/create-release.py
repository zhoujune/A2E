#!/usr/bin/env python3
"""Create and validate an anonymous ProveAI source artifact archive."""

import argparse
import subprocess
import sys
import tarfile
import tempfile
from pathlib import Path, PurePosixPath


PREFIX = "proveai-artifact"


def fail(message):
    raise RuntimeError(message)


def git_output(root, *arguments):
    try:
        return subprocess.check_output(
            ["git", *arguments], cwd=root, text=True, stderr=subprocess.STDOUT
        ).strip()
    except (OSError, subprocess.CalledProcessError) as error:
        fail(f"git {' '.join(arguments)} failed: {error}")


def validate_members(archive):
    with tarfile.open(archive, "r:gz") as stream:
        members = stream.getmembers()
        if not members:
            fail("release archive is empty")
        for member in members:
            path = PurePosixPath(member.name)
            if path.is_absolute() or ".." in path.parts:
                fail(f"unsafe archive member: {member.name}")
            if not path.parts or path.parts[0] != PREFIX:
                fail(f"archive member is outside the release prefix: {member.name}")
            if ".git" in path.parts:
                fail(f"Git metadata leaked into archive: {member.name}")
            if member.issym() or member.islnk():
                fail(f"release archive does not admit links: {member.name}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", required=True)
    parser.add_argument("--repository", default=".")
    args = parser.parse_args()
    root = Path(args.repository).resolve()
    output = Path(args.output).resolve()
    if output.exists():
        fail(f"refusing to overwrite release archive: {output}")
    if not output.parent.is_dir():
        fail(f"release archive parent directory is missing: {output.parent}")
    if git_output(root, "status", "--porcelain=v1"):
        fail("release archive requires a clean Git worktree")
    revision = git_output(root, "rev-parse", "HEAD")
    subprocess.run(
        [
            "git",
            "archive",
            "--format=tar.gz",
            f"--prefix={PREFIX}/",
            f"--output={output}",
            "HEAD",
        ],
        cwd=root,
        check=True,
    )
    validate_members(output)
    with tempfile.TemporaryDirectory(prefix="proveai-release-check-") as temporary:
        extraction = Path(temporary)
        with tarfile.open(output, "r:gz") as stream:
            stream.extractall(extraction)
        archive_root = extraction / PREFIX
        archived_revision = (archive_root / "artifact" / "source-revision.txt").read_text(
            encoding="utf-8"
        ).strip()
        if archived_revision != revision:
            fail(
                f"archive source revision mismatch: expected {revision}, observed {archived_revision}"
            )
        subprocess.run(
            [sys.executable, "artifact/check-release.py", "--repository", str(archive_root)],
            cwd=archive_root,
            check=True,
        )
    print(f"release archive created: {output}; source revision: {revision}")


if __name__ == "__main__":
    try:
        main()
    except (OSError, RuntimeError, subprocess.CalledProcessError, tarfile.TarError) as error:
        print(f"release archive error: {error}", file=sys.stderr)
        raise SystemExit(2) from error
