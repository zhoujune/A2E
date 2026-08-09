#!/usr/bin/env bash
set -eu

repo_root="$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)"
suite="${1:-smoke}"
shift || true
exec python3 "$repo_root/artifact/run-linux.py" "$suite" --repository "$repo_root" "$@"
