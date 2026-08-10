#!/usr/bin/env bash
set -eu

repo_root="$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
exec python3 "$repo_root/artifact/reproduce.py" "$@"
