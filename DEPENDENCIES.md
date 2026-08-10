# Dependency Inventory

This inventory describes the dependencies needed to reproduce the frozen
artifact. Hashes and download locations for external proof tools are recorded
in `artifact/toolchain.lock.json` and `mechanized/toolchain.lock.json`.

## Runtime and scripts

- Python 3.9 or newer: standard library only for artifact runners, validators,
  and report generators.
- Rust and Cargo: the `reference-broker` crate has no third-party Cargo
  dependencies. `Cargo.lock` is retained for deterministic metadata.
- PowerShell 7 (`pwsh`): runs `mechanized/verify.ps1` on Linux or Windows.

## Formal tools

- Eclipse Temurin JRE 21.0.11+10, Linux x64 HotSpot. The release archive and
  executable SHA-256 values are pinned in `artifact/toolchain.lock.json`.
- TLA+ Tools v1.7.4 (`tla2tools.jar`), pinned by SHA-256 in the same lock.
- Verus, rustup, Rust, and Z3: archives, versions, and hashes are pinned in
  `mechanized/toolchain.lock.json`; `mechanized/verify.ps1` provisions isolated
  tool directories and records observed hashes in its report.

## Optional validation tools

- A Draft 2020-12 JSON Schema validator such as Python `jsonschema` can check
  the retained report schemas. The repository's validators do not require it.
- `taskset` and `findmnt` improve Linux RQ2 provenance and CPU pinning but are
  optional; their absence is recorded or reported by the repetition runner.

## Offline evaluation

For an offline TLA+ run, place the exact hash-matching JRE executable (or
unpacked JRE) and `tla2tools.jar` on the evaluator's filesystem and pass
`--java` and `--tla-tools` to `artifact/run-linux.py`, or set `JAVA_HOME` and
`PROVEAI_TLA_TOOLS`. Build a Verus/Rust bundle with
`mechanized/prepare-offline-bundle.py`, then pass its directory to
`reproduce.sh full --offline-bundle-root <bundle>`. The bundle contains the
hash-checked Verus and rustup archives, rustup executable, and Rust toolchain;
the verifier copies the toolchain into a fresh run root and performs the same
tree and source-integrity checks without invoking a network download. No
credential or mutable remote branch is required.
