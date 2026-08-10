# Linux artifact runner

`run-linux.py` is the Linux counterpart for the TLA+ part of the existing
PowerShell runner. It uses the repository's exact `formal/model-suite.json`,
copies only the selected `.tla`/`.cfg` inputs into a temporary read-only
snapshot, hashes every copied input, verifies the pinned TLA+ Tools v1.7.4 JAR,
and records every scenario result.

## Prerequisites

- Linux x86-64
- Python 3.9 or newer, standard library only
- Eclipse Temurin Java `21.0.11+10` for Linux x64, pinned in
  `artifact/toolchain.lock.json`
- TLA+ Tools `v1.7.4` with SHA-256
  `936a262061c914694dfd669a543be24573c45d5aa0ff20a8b96b23d01e050e88`
- `chmod`, `python3`, and a writable temporary directory

The repository intentionally does not silently download a JRE. Set `JAVA_HOME`
and `PROVEAI_TLA_TOOLS`, or pass `--java` and `--tla-tools` explicitly. Real
runs verify the selected Java executable against the locked SHA-256
`fd85538801d8ca61d3558c87a57a600e1868d8ac9e918d0860dd64281b548643`.
`--java-sha256` or `PROVEAI_JAVA_SHA256` may supply an explicit release-package
pin; otherwise the runner uses the lock. The lock also records Adoptium's
published JRE archive hash.

The current server preflight is retained at
`artifact/results/linux-smoke-preflight.json`; it validates the smoke snapshot
without claiming TLC execution.

The clean-room run at source revision `5d8e8ed39e492b05f52ba093782a043d204f1192`
is retained as `artifact/results/tla-smoke-5d8e8ed.json` and
`artifact/results/tla-full-5d8e8ed.json`. Smoke passed 8/8 scenarios; full passed
13/13 scenarios with 32 workers and a 1,200-second per-scenario bound.

## Smoke and full commands

The release-facing entry point is at the repository root. It creates a new
output directory, refuses to overwrite reports, and records command logs:

```sh
./reproduce.sh smoke --dry-run --skip-verus --skip-rust
./reproduce.sh smoke --workers 2
./reproduce.sh full --workers 32 --timeout-seconds 1200
```

The PowerShell equivalent is `./reproduce.ps1 smoke -DryRun -SkipVerus -SkipRust`.
`--skip-verus` is only appropriate for a packaging preflight; the full command
requires PowerShell 7 and runs the hash-bound Verus verifier into the new output
directory. The top-level runner does not invoke `formal/check-model.ps1`.

```sh
./artifact/run.sh smoke --dry-run --report /tmp/proveai-tla-smoke.json
python3 artifact/validate_report.py /tmp/proveai-tla-smoke.json

./artifact/run.sh smoke --workers 2 --timeout-seconds 3600 \
  --report artifact/results/tla-smoke.json
./artifact/run.sh full --workers 2 --timeout-seconds 3600 \
  --report artifact/results/tla-full.json
```

The smoke manifest selects 8 scenarios; full selects all 13. Reports refuse
to overwrite existing files and include runner/manifest/input hashes, Java/TLC
versions and hashes, isolated snapshot membership, per-scenario timing, exit
status, timeout bounds, and an output byte count/hash. The runner rechecks exact
snapshot membership and hashes after every scenario. Dry-run validates packaging
and snapshot integrity without claiming model-checking execution.

The Verus runner remains `pwsh -NoLogo -NoProfile -File
mechanized/verify.ps1`; its existing Linux branch downloads the separately
locked Verus/Rust artifacts and emits the retained verification report. The
clean-room release command should invoke this runner after the Linux JRE and
TLC prerequisites are packaged.
