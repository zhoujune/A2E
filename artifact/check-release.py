#!/usr/bin/env python3
"""Fail-closed checks for an anonymous, archiveable ProveAI checkout."""

import argparse
import re
import subprocess
import sys
from pathlib import Path


REQUIRED = (
    ".gitattributes",
    ".github/workflows/ci.yml",
    "DEPENDENCIES.md",
    "LICENSE-MIT",
    "LICENSE-APACHE",
    "TROUBLESHOOTING.md",
    "reproduce.sh",
    "reproduce.ps1",
    "artifact/reproduce.py",
    "artifact/source-revision.txt",
)

ROOT_HOME = "/" + "root" + "/"
HOME_PREFIX = "/" + "home" + "/"
FORBIDDEN = (
    (re.compile(r"(?i)authorization\s*:\s*bearer\s+[a-z0-9._~-]+"), "bearer credential"),
    (re.compile(r"(?i)(?:password|passwd|secret|access[_ -]?token)\s*[:=]\s*[^\s`]+"), "credential assignment"),
    (re.compile(r"(?i)(?:[a-z0-9._%+-]+):(?:[^\s/@]+)@[^\s/]+"), "credential-bearing URL"),
    (
        re.compile(
            r"(?:[A-Za-z]:\\Users\\|[A-Za-z]:/Users/|"
            + re.escape(ROOT_HOME)
            + r"|"
            + re.escape(HOME_PREFIX)
            + r"[^/\s]+/)"
        ),
        "absolute user path",
    ),
    (re.compile(r"\b172\.30\.60\.189\b"), "private server address"),
)


def fail(message):
    raise RuntimeError(message)


def tracked_files(root):
    if not (root / ".git").exists():
        return [path.relative_to(root) for path in root.rglob("*") if path.is_file()]
    try:
        result = subprocess.run(
            ["git", "ls-files", "-z"],
            cwd=root,
            check=True,
            stdout=subprocess.PIPE,
        )
    except (OSError, subprocess.CalledProcessError) as error:
        fail(f"could not enumerate tracked files: {error}")
    return [Path(item) for item in result.stdout.decode("utf-8").split("\0") if item]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repository", default=".")
    args = parser.parse_args()
    root = Path(args.repository).resolve()
    files = tracked_files(root)
    file_set = {path.as_posix() for path in files}
    missing = [path for path in REQUIRED if path not in file_set]
    if missing:
        fail("required release files are missing: " + ", ".join(missing))
    findings = []
    for relative in files:
        path = root / relative
        try:
            content = path.read_text(encoding="utf-8")
        except (UnicodeDecodeError, OSError):
            continue
        for pattern, description in FORBIDDEN:
            if pattern.search(content):
                findings.append(f"{description}: {relative}")
    if findings:
        fail("release scan rejected tracked content: " + "; ".join(findings))
    print(f"release scan passed: {len(files)} files; no credentials or machine paths")


if __name__ == "__main__":
    try:
        main()
    except RuntimeError as error:
        print(f"release scan error: {error}", file=sys.stderr)
        raise SystemExit(2) from error
