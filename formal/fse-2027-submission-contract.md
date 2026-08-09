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
> well-formed configuration, a serialized writer and executor, a closed
> protected-service interface, fail-stop crash assumptions, and a verified
> adapter contract, every mediated physical invocation has durable
> authorization ancestry; every logical request has at most one terminal
> commit; recovery preserves the committed history; and the terminal outcome
> refines the adapter's declared abstract-effect semantics.

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

Before submission, related work must test and either support or narrow the
following novelty proposition:

> No prior system provides a mechanized refinement from durable capability
> authorization, through crash/retry execution and physical invocation
> mediation, to adapter-specific abstract-effect guarantees for AI tool use.

If prior work already provides this complete chain, the contribution must be
narrowed to the missing semantic or mechanization component rather than using a
priority claim.

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
| Executable broker event loop and physical WAL | M4 `reference-broker`: generated IDs, capability budgets, one slot, framed file WAL, recovery, correlation, terminal retrieval, and three adapters | Complete as an unverified reference prototype; no production or byte-WAL refinement claim |
| Byte/fsync/filesystem refinement | Typed-record abstraction only | Explicitly out of theorem scope; assumptions must be evaluated and documented |

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
intervals, and CPU affinity on Linux. It remains a local overlayfs measurement:
remote-service latency and physical-device controls are outside this baseline.

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
| P0 | Final claim currently exceeds some operational instantiations | Complete M1-M3 and run a claim audit |
| Closed | No complete reference broker | M4 reference crate and deterministic crash matrix completed |
| P0 | Paper-grade empirical evaluation incomplete | RQ1-RQ4 baseline evidence exists; add repeated hosts/storage conditions and complete external comparisons |
| P1 | Linux TLA+ execution package incomplete | Runner and dry-run preflight exist; package the hash-pinned Java/TLA+ dependency or container |
| P1 | No top-level artifact packaging, CI, or license | Complete Section 8 |
| P1 | Novelty is not established against related work | Complete a structured comparison and narrow priority language as needed |
| P2 | ReadOnly lacks a protected/contextual instantiation | Complete it or explicitly limit the corresponding operational claim |

## 10. Planned work order

1. M1 and M2 are complete on the verified Linux branch.
2. M3 is complete at the coverage-conditioned formal family boundary.
3. M4 is complete as the explicitly unverified single-slot reference broker.
4. The versioned RQ1 generator and initial RQ2 performance/ablation harness are
   complete, with a retained schema-v1 Linux baseline.
5. RQ3 proof-effort generation and the RQ4 fault-classification matrix are
   complete at the M4/reference-artifact boundary.
6. The Linux artifact runner and smoke/full command surface are implemented;
   package the pinned Java/TLA+ dependency and execute clean-room smoke/full.
7. Run the related-work novelty test and write the paper around the frozen
   claim, not around the chronological proof history.
8. Produce an anonymous release candidate and execute a clean-room artifact
   rehearsal.

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

The next evaluation checkpoint is the clean-room Linux artifact run: supply the
hash-pinned Java/TLA+ package, execute smoke and full TLA+ plus Verus commands,
and retain their reports. External RQ2 host/storage conditions and semantic
comparisons follow. M3 remains closed only at the
coverage-conditioned formal family boundary; production adapter/service
executions are not yet refined into the Verus operational types.
