# A2E Artifact

This repository contains the formal models, Verus proofs, executable broker,
evaluation scripts, and retained evidence for authorization-to-effect
consistency (A2E). The reviewer archive excludes the manuscript, build output,
and development notes.

## Quick Check

From the root of an extracted reviewer archive, run:

```sh
python3 artifact/validate_release.py
python3 artifact/check-release.py
python3 formal/validate_traceability.py formal/theorem-premise-traceability.v1.json
python3 reference-broker/evaluation/validate_k4_i1.py \
  reference-broker/evaluation/results/k4-i1-submission.json
python3 artifact/validate_report.py artifact/results/tla-full-9a45d39.json
python3 reference-broker/evaluation/validate_redis_evidence.py
```

To exercise the Rust implementation, run
`cargo test --manifest-path reference-broker/Cargo.toml --all-targets`.
For a fresh smoke or full reproduction, use `bash reproduce.sh smoke --workers 2`
or `bash reproduce.sh full --workers 32 --timeout-seconds 1200`. The full run
requires the pinned tools listed in [DEPENDENCIES.md](DEPENDENCIES.md).

## Contents

- `formal/`: TLA+ specifications and claim-to-premise traceability.
- `mechanized/`: Verus sources and the retained verification report.
- `reference-broker/`: Rust broker, tests, evaluation runners, and reports.
- `artifact/`: reproduction, provenance, and archive validation tools.
- `kernel/`: executable-kernel support source.

The retained K4-I1 attestation describes finite kernel-in-the-loop executions.
The Redis process-crash raw evidence is under
`reference-broker/evaluation/evidence/redis-process-crash/`.
The protected-effect theorem depends on the adapter and deployment premises
listed in [ARTIFACT.md](ARTIFACT.md) and [artifact/CLAIMS.md](artifact/CLAIMS.md).
The Rust broker and byte-level WAL do not have a whole-program refinement proof.
