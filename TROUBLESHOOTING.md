# Troubleshooting

## Artifact runner rejects Java

The runner requires the exact Linux x64 Temurin 21.0.11+10 executable hash.
Set `JAVA_HOME` to that JRE or pass `--java /path/to/java`; do not substitute a
different Java build. Check the expected values in `artifact/toolchain.lock.json`.

## TLA+ Tools is missing or has the wrong hash

Download `tla2tools.jar` from the URL in the lock file, verify its SHA-256, and
set `PROVEAI_TLA_TOOLS` or pass `--tla-tools`. `--dry-run` is available when
only packaging and input-snapshot integrity need to be checked.

## Verus cannot start

The full top-level rehearsal needs PowerShell 7 (`pwsh`) and the network or
offline archives specified by `mechanized/toolchain.lock.json`. Use a writable
temporary directory and enough disk for isolated Rust/Verus toolchains. A
TLA+/Rust-only smoke preflight may use `--skip-verus`; that is not a full proof
reproduction.

## Preparing an offline Verus bundle

Use `mechanized/prepare-offline-bundle.py` with the exact lock-matching Verus
archive, rustup archive/executable, and Rust toolchain directory. The script
refuses hash mismatches and refuses to overwrite an existing bundle. Pass the
result with `--offline-bundle-root` to the top-level full command.

## Rust checks fail

Run `cargo fmt --check` and `cargo test --all-targets` from `reference-broker`.
The crate intentionally has no third-party dependencies. Delete only an
evaluator-owned `target/` directory if a stale build is suspected, then retry.

## RQ2 temporary storage is unexpected

Set `TMPDIR` before `evaluation/run_repeated_rq2.py`. On Linux, inspect the
retained report's `temporary_mount_source`, `temporary_mount_target`, and
`temporary_mount_filesystem` fields. `tmpfs` is a memory-backed control; an
NVMe-backed ext4 result is physical-storage evidence but not independent-host
replication.

## Reports already exist

All reproduction commands fail rather than overwrite evidence. Choose a new
output directory or report path. Retained reports under `artifact/results`,
`mechanized/results`, and `reference-broker/evaluation/results` are immutable
inputs to the paper.
