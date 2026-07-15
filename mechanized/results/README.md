# Verification evidence

Running `mechanized/verify.ps1` writes `verification-report.json` here by
default. The JSON document uses schema `vetra.verus-verification-report`,
version 1, defined by `verification-report.schema.v1.json`. The report records:

- overall and per-target status, UTC timestamps, and durations;
- SHA256 hashes for the schema, every registered Verus source, `verify.ps1`,
  and `toolchain.lock.json`;
- an exact read-only per-run source snapshot, including its tree digest and
  validation counts;
- declared lock metadata and hashes/versions observed during the run, including
  a stable digest of the complete extracted Verus tool tree;
- a fresh per-run Rust installation, its deterministic tree digest, and the
  official rustup distribution endpoints used to obtain it;
- source-coverage, proof-policy, and immediate-parent-import validation;
- each target's cumulative obligation total, contribution parent and delta,
  and the running non-duplicated obligation total.

The stable path contains the most recent run and is replaced atomically. Use
`-ReportPath <path>` for a separate destination or `-NoReport` when no evidence
file should be written. A passed report is meaningful only for the exact hashes
recorded in that report; editing any registered source, the verification driver,
the report schema, or the toolchain lock invalidates that evidence and requires
a new run.

For a passed report, the schema requires completed timestamps, zero-error
targets invoked only with `--crate-type lib --no-cheating`, complete source-
snapshot evidence, and a stable fresh Rust toolchain tree. The driver also
checks relationships that JSON Schema cannot express directly: target/source
count equality, unique names and paths, parent-delta arithmetic, running and
final non-duplicated totals, and summary totals. The Rust toolchain is trusted
through the exact version fetched by the pinned rustup executable from the
official distribution service; its observed tree hash is evidence, not an
independently predeclared hash for every Rust component.
