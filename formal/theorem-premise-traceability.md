# Theorem and Premise Traceability

This index is the human-readable companion to
[`theorem-premise-traceability.v1.json`](theorem-premise-traceability.v1.json).
The JSON manifest is authoritative for exact symbols, source paths, target
status, hashes, and attestation assertions; this file explains how to read the
boundary in paper terms.

Validate the manifest from the repository root:

```sh
python3 formal/validate_traceability.py \
  formal/theorem-premise-traceability.v1.json
```

## Claim map

| Entry | Paper claim | Formal/evidence boundary | Main premises | Evidence |
|---|---|---|---|---|
| `T5-R1-durable-success-recovery` | Recovery history extends monotonically; a recovery `Commit` cites a crash-prefix durable `Outcome`. | Typed-WAL recovery theorem | Finite admitted WAL execution; recovery episode; non-online repair guard; exact request/attempt/value/reference match. | `T5-R1`, H2 witness, T5-C0 export |
| `T6-X0-contextual-protected-effect-composition` | The generic contextual lift transports terminal/effect refinement from a plugged WAL to the canonical Broker, with a separate mediation transport lemma. | Conditional generic composition | Well-formed paper config, storage context, plugged WAL, `AdapterVerified`, `AdapterRely`, terminal evidence, and (for mediation) P0 prefix coupling. | `T6-X0`; the retained executable witness is a concrete EnsureMember instance, not a universal coverage witness |
| `T6-DD5-request-indexed-family-composition` | A request-indexed Deduplicated family discharges the generic composition obligations for every covered terminal request. | Conditional specialized family composition | `dd5_operational_member_valid`, family coverage, DD4 prefix product, coupled protected execution, and the shared T6-X0 context premises. | `T6-DD5`, DD5 non-vacuity witness |
| `K4-A4-executable-recovery-kernel` | The typed executable kernel checks append order, crash/recovery, durable-success `Commit`, and class-sensitive resume. | Verified executable kernel | Well-formed immutable manifest; durable LSN supplied after WAL; proved resume predicate. | `K4-A4` |
| `K4-I0-kernel-in-loop-traces` | Selected real broker append/replay traces pass through K4 at exact cuts. | Finite kernel-in-loop integration | Proof-erased K4-A4 library; manifest-bound broker; preview before WAL and commit after durable LSN; full-prefix replay. | Harness and `run-k4-i0.sh` |
| `K4-I1-fail-closed-submission-profile` | The retained evaluation has no ungated broker open and attests gate, preview/commit, replay, and recovery closure. | Dynamic evaluation attestation | Immutable admission manifests; `open_with_gate` for every evaluation broker; independent report validator. | Retained K4-I1 JSON and validator |
| `rust-reference-boundary` | The Rust broker and byte persistence are not a whole-program refinement. | Explicit unverified/trusted boundary | Translation, filesystem, adapters, transport, and deployment remain outside the checked gate. | README, threat model, refinement boundary |

## Reading rules

`proved` entries are Verus theorems whose target status and source hash are
checked against the retained verification report. Each formal entry carries
both prose premises/conclusions and `premise_symbols`/`conclusion_symbols`;
the validator checks all of those symbols against the listed source files.
`conditional-composition` entries are theorems whose protected-effect
conclusion requires the listed coverage and interface premises. The generic
T6-X0 entry is intentionally separate from the DD5 request-indexed family
entry. `kernel-in-loop-evidence` and
`dynamic-attestation` entries are executable evidence, not refinement proofs.
The final entry is a negative claim that prevents the paper from silently
promoting the Rust reference implementation into the formal model.

The paper's main theorem is labeled
`thm:authorization-to-effect`; the appendix gives the compact claim map while
the JSON manifest carries exact proof symbols and premise text.
