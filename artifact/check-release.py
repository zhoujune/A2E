#!/usr/bin/env python3
"""Fail-closed checks for an anonymous, archiveable ProveAI checkout."""

import argparse
import re
import sys
from pathlib import Path

from importlib.util import module_from_spec, spec_from_file_location


REQUIRED = (
    ".gitattributes",
    "DEPENDENCIES.md",
    "LICENSE-MIT",
    "LICENSE-APACHE",
    "TROUBLESHOOTING.md",
    "reproduce.sh",
    "reproduce.ps1",
    "artifact/reproduce.py",
    "artifact/release_package.py",
    "artifact/source-revision.txt",
)

ROOT_HOME = "/" + "root" + "/"
HOME_PREFIX = "/" + "home" + "/"
FORBIDDEN = (
    (re.compile(r"(?i)authorization\s*:\s*bearer\s+[a-z0-9._~-]+"), "bearer credential"),
    (re.compile(r"(?i)(?:password|passwd|secret|access[_ -]?token)\s*[:=]\s*[^\s`]+"), "credential assignment"),
    (
        re.compile(
            r"(?i)(?:[a-z0-9._%+-]+):(?:[^\s/@]+)@(?:[a-z0-9][a-z0-9.-]*)"
        ),
        "credential-bearing URL",
    ),
    (
        re.compile(
            r"(?:[A-Za-z]:\\Users\\|[A-Za-z]:/Users/|/mnt/[a-z]/Users/|"
            + re.escape(ROOT_HOME)
            + r"|"
            + re.escape(HOME_PREFIX)
            + r"[^/\s]+/)"
        ),
        "absolute user path",
    ),
    (re.compile(r"\b172\.30\.60\.189\b"), "private server address"),
    (re.compile(r'(?i)"hostname"\s*:\s*"(?!anonymous-)[^"]+"'), "identifying hostname"),
)

def fail(message):
    raise RuntimeError(message)


def release_files(root):
    path = root / "artifact" / "release_package.py"
    spec = spec_from_file_location("release_builder", path)
    module = module_from_spec(spec)
    spec.loader.exec_module(module)
    return [item.relative_to(root) for item in module.selected_files(root)]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repository", default=".")
    args = parser.parse_args()
    root = Path(args.repository).resolve()
    files = release_files(root)
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
