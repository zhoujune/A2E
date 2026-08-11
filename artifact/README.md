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

On the server used for the current checkpoint, the full TLA+ phase took 357232
ms with 32 workers and the Verus phase took 2394429 ms. Plan for at least 32
logical CPUs, 16 GiB RAM, and 15 GiB of free disk for a full run; a smoke
preflight needs substantially less. These are conservative scheduling budgets,
not universal performance guarantees.

The clean-room run at source revision `5d8e8ed39e492b05f52ba093782a043d204f1192`
is retained as `artifact/results/tla-smoke-5d8e8ed.json` and
`artifact/results/tla-full-5d8e8ed.json`. Smoke passed 8/8 scenarios; full passed
13/13 scenarios with 32 workers and a 1,200-second per-scenario bound.
The current packaging checkpoint repeats the full suite at source revision
`9a45d391e8c19d3f069a3df271005b1fd6b39b60` as
`artifact/results/tla-full-9a45d39.json` (13/13, 32 workers, 357232 ms).

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
An offline full run adds `--offline-bundle-root /path/to/bundle`.

Before archiving an anonymous release candidate, run:

```sh
python3 artifact/check-release.py
python3 artifact/create-release.py --output /tmp/proveai-artifact.tar.gz
```

It scans tracked text files and fails on credentials, private server addresses,
or absolute user/home paths. The archive builder requires a clean worktree,
uses `git archive` without repository metadata, binds the exported source
revision, rejects unsafe members, and reruns the release scan after extraction.
The retained rehearsal built an archive at source revision `7fc87a7`, with
SHA-256 `087b6d2770aa34a9358080b8205a651f3fbe3e476af8e5f83f75eec6bdf2c45d`;
its unpacked smoke preflight and Rust checks passed on Linux.

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

## K3 proof-erased runtime spike

`run-k3-runtime-spike.sh` verifies the executable K3 layer with the pinned
Verus toolchain using `--compile`, links the resulting proof-erased
`libk3_append_linearization_kernel.rlib` into
`k3-runtime-harness.rs`, and runs a one-record `Call -> Linearize -> Return`
smoke. It then builds the standard-Rust M4 crate into the temporary directory,
runs a K3-profile M4 Idempotent execution, maps the resulting six durable
records into K3's public record vocabulary, and accepts every record through
the compiled K3 `Call -> Linearize -> Return` API at its exact LSN. Set
`VERUS_BIN`, `RUSTC`, and `VERUS_Z3_PATH` to the hash-bound server toolchain
paths before invoking it. The matching `rustup` must be on `PATH`, with its
`RUSTUP_HOME` and `CARGO_HOME` exported; Verus invokes that `rustup` during
compilation. The runner obtains `libvstd.rlib` and `libverus_builtin.rlib` from
the pinned Verus directory and supplies them to the ordinary Rust linker
explicitly.

```sh
VERUS_BIN=/path/to/verus \
RUSTC=/path/to/rustc \
VERUS_Z3_PATH=/path/to/z3 \
./artifact/run-k3-runtime-spike.sh
```

The M4 certificate uses K3's fixed Idempotent profile: request `1`, capability
`1`, digest `1`, no stable key, and a budget of `4`. It is a checked concrete
execution certificate, not an M4 implementation-refinement theorem. The record
mapping is ordinary Rust, K3 still has its fixed demonstration configuration
and serialized append-only boundary, and the standard-Rust broker's recovery,
byte WAL, adapters, and deployment wrapper remain outside this check.
K4-R0/R1 separately parameterize and verify the Authorize, Prepare, and Start
guards over the M4 manifest shape, K4-R2/R3 parameterize the accepted Authorize
and Prepare durable mutations, K4-R4 adds Arm guard/mutation refinement,
K4-R5 adds the accepted Start attempt-log mutation, K4-R6 adds the Outcome
guard/mutation, and K4-R7 adds Commit guard/mutation. They do not extend this
six-record certificate to Revoke/Fail/Unknown, materialization, append state,
or byte-WAL implementation. K4-A0 separately carries the same six-record
Idempotent profile through a manifest-parameterized generic B1/C1 append
certificate with all-prefix replay checkpoints and exact K3 record projection;
it remains a bounded semantic certificate rather than a refinement of the
Rust broker or a parameterization of arbitrary K3 executions.
