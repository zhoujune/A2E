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

## Smoke and full commands

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
