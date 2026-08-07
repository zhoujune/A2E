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

The configured capability IDs and initial budgets are trusted immutable input
and must be identical when reopening an existing WAL. Replay reconstructs every
budget consumption and revocation from that input plus the durable records.

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
   execution may retry within the caller's attempt limit.

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

A simulated crash error is terminal for that `Broker` instance. Drop it and
reopen the same WAL to model process restart.

## Commands

```sh
cargo fmt --check
cargo clippy --all-targets --all-features
cargo test --all-targets
```

The crate has no third-party dependencies.
