"""Run the four controlled scenarios; retain output and actual source hashes."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
from datetime import datetime, timezone

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--cargo", default="cargo")
parser.add_argument("--output", type=Path, required=True)
args = parser.parse_args()
crate = Path(__file__).resolve().parents[1]
repo = crate.parent
command = [args.cargo, "test", "--offline", "--manifest-path", str(crate / "Cargo.toml"),
           "--test", "decision_discrimination", "--test", "adapter_semantics",
           "--test", "recovery_interruption", "--", "--nocapture"]
run = subprocess.run(command, cwd=repo, text=True, capture_output=True)
matches = re.findall(r"DISCRIMINATION[|]([^|\s]+)[|]([01])[|](Commit|Fail|Unknown)[|](Commit|Fail)", run.stdout)
cases = [dict(scenario=n, service_effect=int(e), broker_terminal=b, response_only_terminal=r)
         for n, e, b, r in sorted(matches)]
expected = {"uninvoked_then_rejected", "effect_then_rejected", "conclusive_failure", "success"}
passed = run.returncode == 0 and len(cases) == 4 and {c["scenario"] for c in cases} == expected
paths = sorted(set(crate.glob("src/**/*.rs")) | set(crate.glob("tests/**/*.rs"))
               | {crate / "Cargo.toml", Path(__file__).resolve()})
revision = subprocess.run(["git", "rev-parse", "HEAD"], cwd=repo, text=True, capture_output=True)
rustc = subprocess.run([os.environ.get("RUSTC", "rustc"), "--version"], text=True, capture_output=True)
report = {
    "schema_version": 1, "status": "passed" if passed else "failed",
    "generated_at_utc": datetime.now(timezone.utc).isoformat(),
    "base_revision": revision.stdout.strip(),
    "source_sha256": {p.relative_to(repo).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
    "rustc": rustc.stdout.strip(), "command": command,
    "cases": cases, "exit_code": run.returncode,
    "stdout": run.stdout, "stderr": run.stderr,
    "scope": {"broker": "ungated reference Broker::open",
              "service": "fresh child process per call, synced marker file",
              "crash": "injected broker error and reopen; not process kill or power loss",
              "comparison": "last retained response mapped to terminal; not another workflow implementation",
              "verification": "Rust tests only; no new Verus or TLA+ run"},
}
args.output.parent.mkdir(parents=True, exist_ok=True)
args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
print(json.dumps({k: report[k] for k in ("status", "rustc", "cases")}, indent=2))
if not passed:
    print(run.stdout, run.stderr)
    raise SystemExit(1)
