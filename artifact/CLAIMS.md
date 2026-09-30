# Claim-to-Evidence Map

This index lets an evaluator trace the submission's claims without requiring
the paper source or PDF.

| Claim or result | Primary source | Retained evidence | Validation or reproduction |
|---|---|---|---|
| A2E history obligations and evidence-complete classifier | `formal/EffectBroker.tla`, `mechanized/t1_broker_contract.rs`, `mechanized/t1_durable_queries.rs`, `mechanized/t1_replay.rs` | `mechanized/results/verification-report.json` | `pwsh mechanized/verify.ps1` |
| Journal/WAL crash-prefix and recovery refinement | `formal/EffectBrokerJournal.tla`, `formal/EffectBrokerJournalRefinement.tla`, `formal/EffectBrokerWALRefinement.tla`, T4/T5 Verus targets | TLA+ and Verus reports | `./reproduce.sh full --workers 32 --timeout-seconds 1200` |
| Three-law adapter interface and terminal semantics | `mechanized/t6_terminal_definitions.rs`, `mechanized/t6_adapter_semantic_closure.rs` | registered T6 targets in the Verus report | `pwsh mechanized/verify.ps1` |
| Read-only, idempotent, and deduplicated packages | `mechanized/t6_readonly_operational.rs`, `mechanized/t6_deduplicated_invariant.rs`, related T6 adapter files | adapter target groups in the Verus report | `pwsh mechanized/verify.ps1` |
| Typed executable kernel and crash/recovery gate | `mechanized/k1_executable_kernel.rs`, `mechanized/k2_executable_kernel_refinement.rs`, `mechanized/k3_append_linearization_kernel.rs`, `mechanized/k4_*` | K4 targets and K4-I0/I1 reports | `artifact/run-k4-i0.sh`, `artifact/run-k4-i1.sh` |
| RQ1: 21 crash/restart cases | `reference-broker/tests/`, `reference-broker/evaluation/` | `reference-broker/evaluation/results/k4-i1-submission.json` | `reference-broker/evaluation/validate_k4_i1.py` |
| K4-I1 integration counts: 47 opens/gates, 1,573 preview/commit pairs, 675 replayed records, 40 completed recoveries, 7 verified resumes | gate harness and provenance scripts in `artifact/` and `reference-broker/` | `reference-broker/evaluation/results/k4-i1-submission.json` | `artifact/run-k4-i1.sh` and its independent validator |
| RQ2: repeated latency and storage sensitivity | `reference-broker/evaluation/run_repeated_rq2.py` and Rust benchmark harness | `reference-broker/evaluation/results/rq2-repeated-*.json` | `reference-broker/evaluation/validate_repeated_rq2.py` |
| RQ3: 72 registered targets and 1,534 dependency-aware non-duplicated obligations | Verus sources and target registry | `mechanized/results/verification-report.json`, `reference-broker/evaluation/results/rq3-proof-effort.json` | `mechanized/verify.ps1`, `reference-broker/evaluation/generate_rq3.py` |
| Theorem premises, witnesses, and excluded boundaries | formal and mechanized sources | `formal/theorem-premise-traceability.v1.json` | `formal/validate_traceability.py` |

## Important interpretation rules

- TLA+ results are bounded model-checking evidence, not unbounded proofs.
- Verus reports bind registered proof targets to exact source and tool hashes.
- K4-I1 counts finite executions through the checked gate; it does not verify
  the complete Rust broker or byte persistence.
- Performance JSON files preserve their measurement environment and revision.
  Cross-environment differences are storage sensitivity, not universal ratios.
- Released report hostnames are anonymized; source hashes, tool hashes,
  measurements, and outcomes are retained.
- The protected-effect result is conditional on adapter rely relations,
  primitive laws, request-indexed coverage, and a closed modeled interface.
