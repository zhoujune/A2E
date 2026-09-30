#!/usr/bin/env python3
"""Check maintained Rust code without rewriting hash-bound experiment sources."""

import subprocess
from pathlib import Path


root = Path(__file__).resolve().parents[1]
broker = root / "reference-broker"
sources = sorted((broker / "src").rglob("*.rs"))
sources += sorted((broker / "tests").rglob("*.rs"))
if not sources:
    raise SystemExit("no Rust sources found")
subprocess.run(["rustfmt", "--edition", "2021", "--check", *map(str, sources)], check=True)
