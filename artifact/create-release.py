#!/usr/bin/env python3
"""Create the authoritative anonymous FSE artifact archive."""

import runpy
import sys
from pathlib import Path

script = Path(__file__).with_name("create-ndss-release.py")
sys.argv[0] = str(script)
runpy.run_path(str(script), run_name="__main__")
