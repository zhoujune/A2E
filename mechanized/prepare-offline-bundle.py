#!/usr/bin/env python3
"""Build a hash-checked offline bundle for the Verus verifier."""

import argparse
import hashlib
import json
import platform
import shutil
import sys
from pathlib import Path


def fail(message):
    raise RuntimeError(message)


def sha256(path):
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def require_file(path, description):
    if not path.is_file():
        fail(f"missing {description}: {path}")


def copy_checked(source, destination, expected, description):
    require_file(source, description)
    actual = sha256(source)
    if actual.lower() != expected.lower():
        fail(f"{description} SHA-256 mismatch: expected {expected}, observed {actual}")
    destination.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(source, destination)
    return actual


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", required=True)
    parser.add_argument("--verus-archive", required=True)
    parser.add_argument("--rustup-archive", required=True)
    parser.add_argument("--rustup-executable", required=True)
    parser.add_argument("--rust-toolchain", required=True)
    parser.add_argument("--repository", default=".")
    args = parser.parse_args()

    root = Path(args.repository).resolve()
    lock = json.loads((root / "mechanized" / "toolchain.lock.json").read_text(encoding="utf-8"))
    if platform.system() == "Linux" and platform.machine().lower() in {"x86_64", "amd64"}:
        platform_key = "linux-x64"
        executable_leaf = "rustup"
    elif platform.system() == "Windows" and platform.machine().lower() in {"x86_64", "amd64"}:
        platform_key = "windows-x64"
        executable_leaf = "rustup.exe"
    else:
        fail("offline bundle preparation supports only x86-64 Linux and Windows")
    selected = lock["platforms"][platform_key]
    output = Path(args.output).resolve()
    if output.exists():
        fail(f"refusing to overwrite offline bundle: {output}")
    output.mkdir(parents=True)

    verus_archive = Path(args.verus_archive).resolve()
    rustup_archive = Path(args.rustup_archive).resolve()
    rustup_executable = Path(args.rustup_executable).resolve()
    toolchain = Path(args.rust_toolchain).resolve()
    if not toolchain.is_dir():
        fail(f"missing Rust toolchain directory: {toolchain}")
    verus_hash = copy_checked(
        verus_archive,
        output / "archives" / selected["verus"]["archive"],
        selected["verus"]["sha256"],
        "Verus archive",
    )
    rustup_hash = copy_checked(
        rustup_archive,
        output / "archives" / selected["rustup"]["archive"],
        selected["rustup"]["sha256"],
        "rustup archive",
    )
    executable_hash = copy_checked(
        rustup_executable,
        output / "rustup" / executable_leaf,
        selected["rustup"]["sha256"],
        "rustup executable",
    )
    destination_toolchain = output / "toolchains" / selected["rust"]["toolchain"]
    shutil.copytree(toolchain, destination_toolchain)
    for leaf in ("rustc", "cargo") if platform_key == "linux-x64" else ("rustc.exe", "cargo.exe"):
        require_file(destination_toolchain / "bin" / leaf, f"staged {leaf}")
    manifest = {
        "schema_version": 1,
        "platform": platform_key,
        "verus_archive_sha256": verus_hash,
        "rustup_archive_sha256": rustup_hash,
        "rustup_executable_sha256": executable_hash,
        "rust_toolchain": selected["rust"]["toolchain"],
        "source_paths_not_retained": True,
    }
    (output / "MANIFEST.json").write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
    print(f"offline bundle created: {output}")


if __name__ == "__main__":
    try:
        main()
    except (OSError, RuntimeError, KeyError) as error:
        print(f"offline bundle error: {error}", file=sys.stderr)
        raise SystemExit(2) from error
