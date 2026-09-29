#!/usr/bin/env python3
"""Build an anonymous artifact-only archive from the current source tree."""

import argparse
import hashlib
import json
import os
import subprocess
import tarfile
import tempfile
from datetime import datetime, timezone
from pathlib import Path, PurePosixPath


PREFIX = "proveai-fse-artifact"
ROOT_FILES = (
    ".gitattributes",
    ".gitignore",
    "ARTIFACT.md",
    "README.md",
    "DEPENDENCIES.md",
    "TROUBLESHOOTING.md",
    "LICENSE-APACHE",
    "LICENSE-MIT",
    "reproduce.sh",
    "reproduce.ps1",
)
ROOT_DIRS = (".github", "artifact", "formal", "kernel", "mechanized", "reference-broker")
EXCLUDED_DIRS = {".git", ".toolbox", "__pycache__", "target", "tmp"}
EXCLUDED_SUFFIXES = {
    ".pyc", ".pdf", ".tex", ".aux", ".log", ".out", ".blg", ".bbl",
    ".png", ".jpg", ".jpeg", ".svg", ".eps", ".rdb", ".aof", ".manifest",
}
EXCLUDED_FILES = {
    "reference-broker/evaluation/results/decision-discrimination.json",
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


def portable_bytes(source, root):
    data = source.read_bytes()
    try:
        text = data.decode("utf-8")
    except UnicodeDecodeError:
        return data
    root_text = str(root).replace("\\", "/")
    mounted_workspace = "/mnt/c/" + "Users/" + "57408/Documents/ProveAI-worktrees/fse-executable"
    replacements = {
        root_text: ".",
        mounted_workspace: ".",
        "/home/june/.cache/proveai-review-rust-1.96": "<toolchain-cache>",
        "C:\\Users\\57408\\Documents\\ProveAI-worktrees\\fse-executable": ".",
    }
    for old, new in replacements.items():
        text = text.replace(old, new)
    return text.encode("utf-8")


def selected_files(root):
    paths = []
    for name in ROOT_FILES:
        path = root / name
        if not path.is_file():
            fail(f"required release file is missing: {name}")
        paths.append(path)
    for name in ROOT_DIRS:
        base = root / name
        if not base.is_dir():
            fail(f"required release directory is missing: {name}")
        for path in base.rglob("*"):
            if path.is_symlink():
                fail(f"symbolic links are not admitted: {path.relative_to(root)}")
            if path.is_file() and admitted(path.relative_to(root)):
                paths.append(path)
    return sorted(set(paths), key=lambda item: item.relative_to(root).as_posix())


def add_file(archive, source, arcname):
    info = archive.gettarinfo(str(source), arcname)
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
    args = parser.parse_args()

    root = Path(args.repository).resolve()
    output = Path(args.output).resolve()
    if output.exists():
        fail(f"refusing to overwrite release archive: {output}")
    state = dirty(root)
    if state and not args.allow_dirty:
        fail("worktree is dirty; commit the release snapshot or pass --allow-dirty")

    files = selected_files(root)
    with tempfile.TemporaryDirectory(prefix="proveai-ndss-release-") as temporary:
        staging = Path(temporary) / PREFIX
        for source in files:
            relative = source.relative_to(root)
            destination = staging / relative
            destination.parent.mkdir(parents=True, exist_ok=True)
            destination.write_bytes(portable_bytes(source, root))

        exported_revision = revision(root)
        (staging / "artifact" / "source-revision.txt").write_text(
            exported_revision + "\n", encoding="utf-8"
        )

        manifest_files = {}
        for path in sorted(staging.rglob("*")):
            if path.is_file():
                manifest_files[path.relative_to(staging).as_posix()] = sha256(path)
        manifest = {
            "schema": "proveai.fse.artifact-release",
            "schema_version": 1,
            "created_utc": datetime.now(timezone.utc).replace(microsecond=0).isoformat(),
            "archive_revision": exported_revision,
            "verified_source_revision": exported_revision,
            "dirty_worktree_snapshot": state,
            "paper_material_included": False,
            "files": manifest_files,
        }
        manifest_path = staging / "artifact" / "release-manifest.json"
        manifest_path.write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")

        output.parent.mkdir(parents=True, exist_ok=True)
        with tarfile.open(output, "w:gz", format=tarfile.PAX_FORMAT) as archive:
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
