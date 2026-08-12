# ProveAI minimal reference broker (M4)

This crate is the executable M4 reference system from the FSE 2027 submission
contract. It provides a small, deterministic broker around the K1-K3 protocol
vocabulary. It is an implementation and evaluation vehicle, not a new verified
refinement theorem.

## Boundary

| Component | Status | Evidence or assumption |
|---|---|---|
| Nine `JournalRecord` variants and one-based LSN references | Mirrored from verified K3 concepts | K3 proves its Verus records and serialized `Call -> Linearize -> Return` append loop refine the typed Journal boundary. |
| Durable phase summary and record ancestry checks | Mirrored from verified K1-K3 concepts | The standard-Rust replay code independently checks exact references and legal local phase changes; this code is not verified. |
| `Broker` wrapper and single executor slot | Trusted standard-Rust wrapper | Correct use of the verified concepts depends on this crate's tests and code review. |
| Frame encoding, CRC32, file append, flush, `sync_data`, and tail truncation | Unverified platform code | Filesystem and OS durability semantics are assumed. No theorem connects byte frames to the typed-WAL model. |
| Adapter implementations and remote effects | Unverified application code | The three adapters are executable examples, not proofs that arbitrary production services satisfy an adapter contract. |
| Process lifecycle, transport, access control, and deployment | Out of scope | A production refinement or complete-mediation claim requires additional evidence. |

In particular, passing these tests does **not** establish that this file WAL
refines the typed-WAL theorem, that arbitrary production executions inhabit the
DD5 request family, or that an operating-system deployment enforces exclusive
mediation.

The artifact's K3 runtime bridge additionally executes one K3-profile M4
Idempotent run and feeds its actual six durable records into the compiled,
verified K3 append kernel. This is a concrete typed-record certificate for that
run, not a proof that arbitrary M4 code paths, recovery, byte frames, adapters,
or deployment refine the Verus model.

The example `DeduplicatedAdapter` keeps its keyed decisions in memory. Crash
tests restart the `Broker` while retaining the adapter object, modeling an
independently durable remote service. Restarting that adapter discards its
decisions and does not satisfy the Deduplicated contract. A production adapter
must keep its memo at least as long as the broker can retry the key, or provide
an authoritative accepted-record reconciliation path.

The configured capability IDs and initial budgets are trusted immutable input.
Opening a WAL creates or verifies a deterministic `<wal>.config` sidecar, so a
restart with altered capability budgets is rejected before replay. Replay
reconstructs every budget consumption and revocation from that bound input plus
the durable records.

`BrokerConfig::admission_manifest` is an optional verified-profile input. Each
binding fixes an expected request ID, capability, digest, retry class, and key
before `Authorize`; the broker rejects mismatches at both `admit` and `prepare`.
Deduplicated keys must be unique across the current namespace-zero manifest.
The versioned configuration sidecar binds the complete manifest, so reopening
with changed request metadata fails before replay. This gives a finite M4
execution the static request metadata required by K3's formal configuration.
K4-R0/R1 additionally verify the executable manifest lookup and Authorize,
Prepare, and Start decisions against Q1/R1 for every well-formed manifest.
K4-R2/R3 verify the accepted Authorize and Prepare durable mutations, K4-R4
verifies the Arm guard and mutation, K4-R5/R6 verify the Start and Outcome
guard/mutations, and K4-R7 verifies Commit. Revoke, Fail, Unknown, and the
remaining materialization, append control, and byte-WAL refinement remain
outside that result. K4-A0 adds a bounded manifest-carrying B1/C1 append
certificate for the six-record Idempotent profile and exact K3 record
projection. K4-A1 threads the same profile through concrete K3 durable,
journal, acknowledgment, and append-control state with generic K4 mutations
and exact LSN/cut agreement. Neither checkpoint turns this standard-Rust crate
into an implementation refinement of the Verus model. K4-A2 generalizes the
checked bridge to arbitrary legal sequences of the six supported record kinds
under a well-formed manifest, but still does not refine this Rust crate, its
byte WAL, or Revoke/Fail/Unknown behavior.
The sidecar's byte-level durability remains an M4 platform assumption, not a
typed-WAL refinement theorem.

## Protocol

1. `admit` generates a monotonically increasing immutable request ID, validates
   a configured capability, consumes one budget unit, and durably appends
   `Authorize`.
2. `prepare` fixes the digest, retry class, and optional deduplication key and
   appends `Prepare` with the exact authorization LSN.
3. The first attempt appends `Arm` and `Start`. The `Start` LSN is also the
   invocation ID.
4. A delivery is accepted only when its invocation ID occupies the sole
   executor slot. An old or mismatched delivery is rejected without a WAL
   append.
5. `Outcome` and exactly one of `Commit`, `Fail`, or `Unknown` make the result
   recoverable through `terminal`.
6. Recovery converts an unmatched `Start` into an ambiguous `Outcome`.
   Uncontrolled execution becomes `Unknown`; Idempotent and Deduplicated
   execution may retry within its class-derived attempt limit (three attempts
   for Idempotent and Deduplicated, one for Uncontrolled and ReadOnly). The
   `run` argument must match that limit; manual `begin_attempt` and
   `accept_delivery` paths enforce it directly.

Every record is stored in a versioned length frame with a CRC32 checksum. An
incomplete or checksum-invalid final frame is discarded on open; corruption
before the final frame is rejected.

## Deterministic fault sites

`CrashPlan` can stop execution after each durable or volatile boundary:

- `AfterAuthorize`
- `AfterPrepare`
- `AfterArm`
- `AfterStart`
- `AfterInvoke`
- `AfterOutcome`
- `AfterTerminal`

A simulated crash error is terminal for that `Broker` instance. All mutating
operations are rejected with `Crashed`; drop it and reopen the same WAL to model
process restart. A failed WAL append similarly poisons the in-memory WAL and
requires reopening before further appends.

## Commands

```sh
cargo fmt --check
cargo clippy --all-targets --all-features
cargo test --all-targets
cargo run --release --bin evaluate -- --iterations 100 \
  --output evaluation/results/rq1-rq2-linux.json
```

The crate has no third-party dependencies.

The [evaluation guide](evaluation/README.md) defines the RQ1/RQ2 report fields,
ablations, schema validation, and limits of the retained microbenchmark data.
