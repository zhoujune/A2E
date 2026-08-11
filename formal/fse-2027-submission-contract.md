# FSE 2027 Submission Contract

Status: **scope frozen**

Frozen: 2026-08-01

Baseline: `codex/linux-verification-runner` at `f0f533e`
Target: FSE 2027 paper submission and companion artifact

This document fixes the intended first-paper claim, contribution structure,
scope, required evidence, and artifact exit criteria. It is a project control
document, not a theorem statement. The normative mathematical statement remains
[`mechanization-contract.md`](mechanization-contract.md), and the security
boundary remains [`threat-model.md`](threat-model.md).

## 1. Submission decision

The first paper is a **verified protocol architecture** paper. It is not a claim
of a fully verified production agent runtime.

The paper studies a serialized effect broker placed between an untrusted agent
and effectful tools. The broker makes authorization durable, records physical
attempt intent, mediates invocation, recovers after fail-stop crashes, and
interprets retry outcomes through an explicit adapter contract.

The working paper claim is:

> For every finite execution admitted by the verified broker model, under a
> well-formed configuration, a serialized writer and executor, and fail-stop
> crash assumptions, every physical invocation has durable authorization
> ancestry, every logical request has at most one terminal commit, and recovery
> preserves the committed history. For each terminal request additionally
> covered by a paired operational/protected execution-family member satisfying
> the verified adapter contract and closed-interface premises, every protected
> effect is mediated and the terminal outcome refines the adapter's declared
> abstract-effect semantics.

This claim deliberately says **mediated**, not production-global. Production
process isolation, credential custody, network routing, and operating-system
handle exclusivity remain deployment assumptions unless separately validated.

The paper must not claim generic physical exactly-once execution. It proves the
guarantee appropriate to each adapter class:

| Adapter class | Permitted retry interpretation |
|---|---|
| ReadOnly | Repetition contributes no protected mutation. |
| Idempotent | Repetition refines one abstract mutation under the adapter law. |
| Deduplicated | A stable key is atomically memoized and accepted at most once. |
| Uncontrolled | The broker does not retry after arming; uncertainty may end in `Unknown`. |

## 2. Primary contributions

The paper will make three primary contributions.

### C1. Crash-aware effect semantics for agent tool use

Define an effect-broker protocol that separates:

- logical requests from physical attempts;
- durable authorization from invocation intent;
- physical delivery from persisted observation;
- terminal broker outcomes from external abstract effects; and
- conclusive failure from irreducible ambiguity.

The semantics integrate capability scope, capability budget, revocation,
durable retry state, stale-delivery rejection, and the four adapter classes in
one explicit safety contract.

### C2. Compositional end-to-end mechanization

Mechanize a refinement chain from the broker specification through an atomic
Journal, typed WAL, storage-parametric context, and independently defined
protected-service execution. The proof uses prefix-indexed weak simulations,
trace projection, recovery-history preservation, complete mediation, and
authorization provenance rather than assuming whole-trace equality as an
unexplained premise.

The paper-facing theorem must state exactly which parts are generic and which
parts are instantiated by a concrete adapter execution.

### C3. Executable witnesses and reproducible evaluation artifact

Provide non-vacuous crash/retry executions for the supported adapter classes,
a minimal executable Rust reference broker, fault-injection experiments, and a
reproducible TLA+/Verus artifact. The artifact binds reports to the exact source,
runner, lock, schema, and toolchain inputs.

## 3. Novelty test

The novelty is the verified connection among established mechanisms, not a
claim that any individual mechanism is new.

| Established area | What this work must add |
|---|---|
| Capability systems/reference monitors | Durable authorization ancestry tied to each physical attempt and terminal effect. |
| Durable workflow engines | A machine-checked effect-safety contract rather than operational retry reliability alone. |
| Idempotency keys/deduplication | A proof that broker retry behavior refines the service's keyed decision semantics. |
| Crash-consistent storage | Refinement from recovery history to agent-visible logical outcome and protected effect. |
| Verified systems | An agent-tool boundary with explicit ambiguity, adapter laws, and complete mediation. |

The source-backed [related-work audit](related-work-audit.md), with a search
cutoff of 2026-08-10, rejects broad priority language. PoE already joins
authorization, an enforced execution path, durable effects, and replay in the
AI-agent setting. Machine-Checked Dual-Write Recovery already gives an
Isabelle/HOL treatment of crash ambiguity, sink acceptance, fencing,
deduplication, and evidence lifetime. CaMeL and Guardians of the Agents already
place capability or static-policy enforcement at the agent tool boundary.

The paper must therefore use this narrower, qualified proposition:

> Based on the sources checked through 2026-08-10, we are not aware of prior
> work that machine-checks a coverage-conditioned compositional refinement for
> a serialized AI tool-effect broker from durable capability authorization and
> complete mediation for protected Idempotent and Deduplicated instances,
> through fail-stop crash/recovery, to an abstract adapter layer that explicitly
> distinguishes ReadOnly, Idempotent, Deduplicated, and Uncontrolled effects,
> including `Unknown` for irreducible ambiguity. The ReadOnly operational
> instance is proved only through its adapter/WAL/Broker refinement boundary.

This is a synthesis claim about the complete chain, not a claim that capability
enforcement, durable workflows, crash refinement, ambiguous retry,
deduplication, or AI-tool policy verification is individually new. The search
must be refreshed at the submission freeze and the wording narrowed again if a
closer system appears.

## 4. Claim-to-evidence map

| Paper claim | Current evidence | Submission status |
|---|---|---|
| Broker authorization, budget, provenance, and terminal safety | T1 and its Journal/physical-history prerequisites | Complete |
| Atomic-Journal refinement | T2 | Complete |
| Typed-WAL weak simulation and recovery durability | T3, T4, and T5 | Complete at the typed-record abstraction |
| Storage-parametric contextual replacement | T4-C1/C2 | Complete |
| Generic terminal evidence and retry-class compatibility | T6-D0/E0/C0/S0 | Complete |
| Idempotent operational adapter refinement | T6-A0/A1 | Complete |
| Protected execution, no bypass, and authorization ancestry for the idempotent witness | T6-M0 | Complete in the formal deployment model |
| Prefix product and contextual terminal theorem for the idempotent witness | T6-P0/X0 | Complete |
| ReadOnly operational witness | T6-RO0 | Complete at the adapter/WAL boundary |
| Deduplicated invariant, rely, and terminal refinement | T6-DD0/DD1 | Complete |
| Deduplicated crash/retry witness | T6-DD2 | Complete at the adapter/WAL boundary |
| Deduplicated protected execution and mediation | T6-DD3 | Complete for the distinguished DD2 execution |
| Deduplicated P0/X0 instantiation | T6-DD4 | Complete for the distinguished DD2 execution |
| Request-indexed family of operational/protected executions | T6-DD5 coverage-conditioned family theorem with DD2 nonvacuity | Complete at the formal family boundary; production construction remains an implementation refinement |
| Finite M4 admission-manifest configuration refinement | K4-C0 maps executable capability budgets and immutable request bindings into a total well-formed R1 configuration; K4-R0/R1 prove parameterized Authorize, Prepare, and Start guards; K4-R2/R3 prove accepted Authorize and Prepare durable mutations; K4-R4 proves the Arm guard and mutation; K4-R5 proves the Start attempt-log mutation; K4-R6 proves the Outcome guard and mutation; M4 binds and validates the matching manifest | Configuration, five core admission/attempt/outcome guards, and five accepted budget/phase/attempt/outcome mutations complete; Commit, remaining mutations, materialization, and K3 state threading remain open |
| Executable broker event loop and physical WAL | M4 `reference-broker`: generated IDs, capability budgets, one slot, framed file WAL, recovery, correlation, terminal retrieval, and three adapters | Complete as an unverified reference prototype; no production or byte-WAL refinement claim |
| Byte/fsync/filesystem refinement | Typed-record abstraction only | Explicitly out of theorem scope; assumptions must be evaluated and documented |

The ReadOnly row is intentionally not a complete-mediation row. T6-RO0 does
not construct a separate protected-service execution or instantiate M0, P0,
or X0 for that class. The paper must not generalize the Idempotent and
Deduplicated protected/contextual results to ReadOnly.

## 5. Frozen scope

### 5.1 In scope

- arbitrary finite executions of the stated transition systems;
- arbitrary well-formed request/capability configurations within theorem types;
- capability matching, budget consumption, and prospective revocation;
- one serialized WAL writer and one serialized executor slot;
- fail-stop crashes and the documented typed-WAL recovery model;
- stale, duplicate, malformed, failed, and ambiguous tool outcomes;
- adapter-specific safety for ReadOnly, Idempotent, Deduplicated, and
  Uncontrolled operations at the level explicitly proved for each class;
- complete mediation inside a closed formal deployment interface;
- a minimal executable reference implementation and crash-injection evaluation;
- safety and refinement, not availability.

### 5.2 Out of scope for the first theorem

- liveness, fairness, and bounded recovery time;
- concurrent writers, concurrent executor slots, and global linearizability;
- verification of a production network stack, TLS implementation, or remote
  service code;
- operating-system process isolation, descriptor custody, ACLs, or sandboxing;
- byte encoding, checksum implementation, flush/fsync, disk-controller, and
  filesystem correctness below the stated persistence contract;
- confidentiality, side channels, and denial-of-service resistance;
- correctness or least privilege of the capability issuance policy;
- semantic coalescing of two separately admitted requests;
- arbitrary storage corruption, rollback, or Byzantine hardware.

These exclusions must appear in the abstract, theorem statement, evaluation,
and artifact documentation where relevant. They must not be hidden only in an
appendix.

## 6. Required technical milestones

### M1. Deduplicated protected execution and mediation (completed T6-DD3)

Construct the protected-service execution corresponding to DD2 and prove:

- exact adapter/protected call coupling;
- a closed interface with no out-of-band protected invocation;
- exactly one protected linearization for the stable key;
- memoized success on the retry without a second mutation;
- equality of protected calls with the mediated invocation projection; and
- durable authorization ancestry for every protected linearization.

T6-DD3 completes this checkpoint for the distinguished DD2 execution. It
constructs the independent protected machine, proves exact adapter/service
coupling and one keyed decision, derives complete mediation under the closed M0
exclusive-handle context, and establishes exact WAL authorization ancestry for
both calls and every protected decision.

### M2. Deduplicated prefix/contextual composition (completed T6-DD4)

Instantiate or generalize P0/X0 for the Deduplicated execution and prove:

- adapter/protected/WAL effect-state agreement at every related prefix;
- complete mediation at every mapped prefix;
- canonical WAL-to-Broker contextual replacement;
- source and target terminal refinement; and
- a premise-free non-vacuity package for the DD2 execution.

T6-DD4 completes all five criteria for the distinguished DD2 execution. It
proves the adapter/protected/WAL prefix product, composes its canonical weak
index with T4-C2's WAL/Broker map, retains context and mediation facts at every
mapped prefix, transports terminal refinement to the Broker trace, and exposes
a premise-free non-vacuity package. This does not by itself establish the
request-indexed execution family considered by M3.

### M3. Claim quantification audit (completed T6-DD5)

T6-DD5 takes the stronger outcome at the formal family boundary:

1. a total request-indexed family maps every request to a paired operational and
   protected member;
2. a coverage predicate requires a valid member for every request terminal in
   the shared WAL; and
3. every covered terminal receives DD4 prefix-product and X0 source/target
   refinement and mediation.

The DD2/DD3 family discharges coverage without premises. The paper must state
family coverage as part of the admitted formal execution boundary; constructing
members directly from production adapter executions remains outside the current
implementation refinement.

### M4. Minimal reference broker (completed)

Extend the executable kernel into a small Rust system containing:

- request admission and immutable request identifiers;
- capability validation and budget consumption;
- a file-backed append/recovery boundary;
- one executor slot and explicit crash points;
- invocation correlation and stale-delivery rejection;
- terminal result retrieval; and
- adapter interfaces for at least Uncontrolled, Idempotent, and Deduplicated
  examples.

The `reference-broker` standard-Rust crate now provides all of these elements.
Its dependency-free WAL uses versioned length frames, CRC32, synchronous file
flushes, exact one-based LSNs, and deterministic torn-tail recovery. The
`Start` LSN is the invocation identifier, so only the invocation occupying the
single volatile executor slot can deliver an outcome. Recovery conservatively
records an unmatched `Start` as ambiguous before either retrying an Idempotent
or Deduplicated request or terminalizing an Uncontrolled request as Unknown.

The test suite covers all nine record codecs, capability rejection and budget
reconstruction, normal and ambiguous adapter behavior, stale-delivery
rejection, lost terminal returns, torn final frames, and the product of all
seven durable/volatile crash sites with all three required adapter examples
(21 crash cases). `cargo fmt --check`, Clippy, and all 14 integration tests pass
with the pinned Rust 1.96 toolchain on Linux.

The crate README explicitly separates K1-K3 concepts from the trusted
standard-Rust wrapper and the unverified filesystem, encoding, adapter,
transport, and deployment layers. M4 does not prove that its byte WAL refines
the typed-WAL model or that production executions inhabit T6-DD5's covered
family.

## 7. Evaluation contract

The evaluation must answer four questions.

### RQ1. Does the protocol prevent unsafe outcomes under crashes and retries?

Run systematic crash injection at every durable/volatile boundary for each
adapter example. Check terminal uniqueness, retry bounds, stale-delivery
rejection, authorization ancestry, and the adapter-specific effect oracle.

The schema-v1 M4 harness now retains this 21-case product for the three
reference adapters and seven explicit crash sites. Every retained case has one
terminal, respects the retry bound, has exact authorization ancestry, and
satisfies its adapter effect oracle; the separate stale-delivery check also
passes without a WAL mutation. This is executable reference-system evidence,
not a refinement of the byte WAL or deployment into the verified model.

### RQ2. What does durable mediation cost?

Measure request latency, throughput, WAL bytes, flushes, recovery time, and
retry overhead against two ablations:

- direct tool invocation without durable mediation; and
- a journaled at-least-once retry loop without adapter effect contracts.

The initial release-mode harness records every required metric for 100-request
mediated, direct, and journaled-at-least-once local workloads, plus three
ambiguous-result retry workloads. A controlled follow-up adds five warmups,
thirty independent process repetitions, raw samples, 95% normal-approximation
intervals, and CPU affinity on Linux. A paired follow-up at source revision
`de33054` holds the binary, host, CPU, and protocol fixed while comparing
overlayfs and tmpfs temporary WALs. It confirms that the measured cost is
storage-path sensitive while preserving the adapter-effect accounting. Because
tmpfs is not durable across a host restart and the endpoint resolves to the same
container hostname as the earlier baseline, independent-host, physical-device,
and remote-service measurements remain open. A further follow-up at source
revision `01fbcdd` places the temporary WAL on `/nix`, reported as an
`/dev/nvme3n1`-backed `ext4` mount. This closes the physical-storage condition
on the server while leaving independent-host replication and pod-lifecycle
durability open.

### RQ3. How much work is required to verify an adapter?

Report model/proof source size, proof obligations, verification time, reusable
lemmas, adapter-specific lemmas, and the effort for each completed adapter.

The schema-v1 RQ3 generator now derives source size, public proof/spec/function
counts, non-duplicated obligation deltas, and retained per-target verification
time from the hash-bound report for the shared framework and all three
adapters. It records each adapter's different evidence boundary. Person-hours
remain explicitly unavailable (`null`) because contemporaneous work logs do
not exist; source size is not presented as a fabricated substitute.

### RQ4. Which failures are converted to safe completion, failure, or unknown?

Present a fault matrix covering reservation/send, send/linearization,
linearization/delivery, delivery/persistence, persistence/terminalization, and
recovery interruption. Explain the safety/availability tradeoff for every cell.

The versioned M4 matrix covers all 18 adapter/window cells and supplies a
recovery action, safety basis, and availability tradeoff for each. A new test
interrupts recovery after its durable synthetic Outcome and resumes it for all
three adapters. The matrix explicitly marks the synchronous adapter's internal
send/linearization point as assumption-dependent rather than claiming an M4
crash hook that does not exist.

External system comparisons should be semantic, not only performance-based.
The paper must compare the provided guarantees with capability systems,
transactional outbox patterns, idempotency-key APIs, and durable workflow
engines without claiming that they share identical goals.

## 8. Artifact-ready exit criteria

The companion artifact is ready only when all of the following are true.

### 8.1 Reproduction

- A fresh Linux x86-64 environment can run a documented artifact smoke
  preflight; an executed smoke run requires the pinned Java/TLA+ package.
- A documented full command reproduces the retained Verus and TLA+ evidence.
- The TLA+ bootstrap is Linux-capable or supplied in a pinned container.
- First-run dependencies are vendored or fetched from documented, hash-pinned
  locations with a supported offline artifact-evaluation path.
- Expected runtime, CPU, memory, and disk requirements are stated.

### 8.2 Integrity

- Every paper theorem maps to an exact source symbol and retained report.
- Registered-source and import coverage is complete.
- No forbidden proof escape hatch is present.
- Reports validate against a versioned schema and bind source, runner, lock,
  and tool hashes.
- Smoke and full reports are clearly distinguished.

### 8.3 Usability

- The repository has a license, artifact guide, dependency inventory, and
  troubleshooting section.
- One top-level command selects smoke or full reproduction.
- The reference broker includes deterministic tests and crash-injection cases.
- No credentials, private endpoints, machine-specific paths, or mutable remote
  branches are required.
- The artifact can be anonymized and archived without changing its evidence.

### 8.4 Paper consistency

- Every headline claim is represented in the claim-to-evidence map.
- Known exclusions agree across the abstract, body, theorem, threat model, and
  artifact guide.
- Evaluation data is generated by versioned scripts in the artifact.
- Reported obligation counts and timings come from retained machine-readable
  evidence rather than manually copied console output.

## 9. Submission blockers and priorities

| Priority | Blocker | Exit condition |
|---|---|---|
| Closed | Headline claim scope audit | M1-M3 are complete and the working claim is limited to admitted, coverage-conditioned formal executions rather than production-global mediation |
| Closed | No complete reference broker | M4 reference crate and deterministic crash matrix completed |
| Closed | Paper-grade empirical evaluation incomplete | RQ1-RQ4 baseline, overlayfs/tmpfs storage sensitivity, NVMe-backed ext4 evidence, WSL2 independent-host replication, and semantic external comparison are retained; WSL2 is explicitly virtual persistent storage rather than native direct-device evidence |
| Closed | Linux TLA+ execution package incomplete | Hash-pinned Temurin/TLA+ artifacts and clean-room smoke/full reports retained at source revisions `5d8e8ed` and `9a45d39` |
| Closed | No top-level artifact packaging, CI, or license | Root smoke/full entry points, dual license texts, dependency inventory, troubleshooting guide, and CI checks are present; the full entry point passed on Linux at `9a45d39` |
| Closed | Final release rehearsal and offline/anonymous packaging | The lock-matching offline bundle passed 56/56 Verus targets at `079f209`; the metadata-free anonymous archive at `7fc87a7` passed revision binding, release scanning, TLA+ smoke preflight, and Rust checks |
| Closed | Novelty is not established against related work | Source-backed audit retained; broad priority claims rejected and the surviving synthesis claim qualified through the 2026-08-10 search cutoff |
| Closed | ReadOnly lacks a protected/contextual instantiation | The operational claim is explicitly limited to T6-RO0's adapter/WAL/Broker refinement boundary and excluded from the protected-service, complete-mediation, P0, and X0 claims |

## 10. Planned work order

1. M1 and M2 are complete on the verified Linux branch.
2. M3 is complete at the coverage-conditioned formal family boundary.
3. M4 is complete as the explicitly unverified single-slot reference broker.
4. The versioned RQ1 generator and initial RQ2 performance/ablation harness are
   complete, with a retained schema-v1 Linux baseline.
5. RQ3 proof-effort generation and the RQ4 fault-classification matrix are
   complete at the M4/reference-artifact boundary.
6. The Linux artifact runner, pinned Java/TLA+ package, clean-room smoke/full
   reports, and clean-room Verus report are complete.
7. The paired RQ2 overlayfs/tmpfs storage control, NVMe-backed ext4 follow-up,
   WSL2 independent-host replication, and related-work novelty audit are
   complete. Write the paper around the qualified frozen claim, not around the
   chronological proof history.
8. The anonymous release builder, offline Verus bundle, and unpacked Linux
   smoke rehearsal are complete. Regenerate the release archive at the final
   paper revision.

## 11. Change control

This contract freezes the first-paper scope. A proposed new headline property
must identify:

- the paper claim it changes;
- the theorem and implementation work it requires;
- its evaluation requirement;
- the schedule impact; and
- which frozen item it displaces.

Work that does not close a P0/P1 blocker should not delay the submission unless
this document is explicitly revised. In particular, concurrency, liveness,
cryptographic capabilities, and full filesystem verification are follow-on
projects rather than implicit prerequisites for the scoped first paper.

## 12. Immediate next checkpoint

The clean-room Linux artifact checkpoint is complete: hash-pinned Java/TLA+
artifacts, TLA+ smoke/full reports, and a 56-target Verus report are retained
at source revisions `5d8e8ed` and `9a45d39`. The current root `reproduce.sh`
full rehearsal passed 13/13 TLA+ scenarios, Rust checks, and 56/56 Verus
targets at `9a45d39`. The paired RQ2 overlayfs/tmpfs checkpoint is also
complete at source revision `de33054`; it is not independent-host replication.
The semantic external-system comparison and related-work novelty audit are now
retained with a 2026-08-10 search cutoff. The NVMe-backed ext4 physical-storage
checkpoint is retained at source revision `01fbcdd`; it uses the same host and
Kubernetes pod. The offline-bundle verifier passed 56/56 targets at `079f209`,
the anonymous archive rehearsal passed at `7fc87a7`, and the WSL2 report closes
the independent-host RQ2 condition; artifact P1 and P2 are closed. The next
step is paper claim-to-evidence integration and final release regeneration.
M3 remains closed only at the coverage-conditioned
formal family boundary; production adapter/service executions are not yet
refined into the Verus operational types. ReadOnly P2 is closed by limiting its
operational claim to T6-RO0 rather than asserting an unproved protected or
contextual instantiation.
