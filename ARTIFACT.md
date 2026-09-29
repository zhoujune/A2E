# ProveAI Artifact

This package contains the formal models, mechanized proofs, executable broker,
evaluation harnesses, retained reports, and reproduction scripts underlying
the submission. It intentionally contains no paper source, paper PDF, figures,
or LaTeX build products.

## Start here

The fastest package and evidence checks require only Python 3.9 or newer:

```sh
python3 artifact/validate_release.py
python3 artifact/check-release.py
python3 formal/validate_traceability.py \
  formal/theorem-premise-traceability.v1.json
python3 artifact/validate_report.py artifact/results/tla-full-9a45d39.json
python3 reference-broker/evaluation/validate_k4_i1.py \
  reference-broker/evaluation/results/k4-i1-submission.json
```

Run the standard-Rust implementation tests with:

```sh
cd reference-broker
cargo test --all-targets
```

The top-level smoke and full entry points are:

```sh
./reproduce.sh smoke --workers 2
./reproduce.sh full --workers 32 --timeout-seconds 1200
```

The PowerShell equivalents use `reproduce.ps1`. The full run checks all 13
TLA+ scenarios, the registered Verus targets, and the Rust implementation. It
requires the hash-locked tools described in `DEPENDENCIES.md` and may take
approximately one hour on a high-core-count Linux host. A smoke run is the
recommended first evaluator action.

## Evidence map

`artifact/CLAIMS.md` maps each theorem and evaluation result to exact source,
report, validator, and reproduction entry points. The canonical structured map
is `formal/theorem-premise-traceability.v1.json`.

The main retained reports are:

- `mechanized/results/verification-report.json`
- `artifact/results/tla-full-9a45d39.json`
- `reference-broker/evaluation/results/k4-i1-submission.json`
- `reference-broker/evaluation/results/rq2-repeated-*.json`
- `reference-broker/evaluation/results/rq3-proof-effort.json`

Retained reports record their own source revision, toolchain, environment, and
hash provenance. Historical performance reports intentionally retain the
revision on which they were measured; they are not represented as fresh runs
of the packaged snapshot.

## Scope

The artifact proves typed-history and conditional protected-effect results at
the boundaries documented in the traceability record. The standard-Rust
broker, byte-WAL encoding, filesystem durability, transport, production
adapters, and deployment are not covered by whole-program refinement. K4-I1 is
finite kernel-in-the-loop integration evidence, not such a refinement.

## Package layout

- `formal/`: TLA+ models, configurations, theorem maps, and validators.
- `mechanized/`: Verus sources, verification driver, schemas, and reports.
- `reference-broker/`: Rust prototype, tests, evaluation harnesses, and data.
- `artifact/`: release checks, runners, tool locks, evidence map, and reports.
- `kernel/`: executable-kernel support source.

See `TROUBLESHOOTING.md` for common toolchain and platform issues.
