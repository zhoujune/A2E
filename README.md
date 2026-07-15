# ProveAI: Verified Agent Effect Broker

This repository aims to develop a narrow verified core for AI agents that invoke
external tools. The core is an effect broker: an untrusted agent submits a
request, and the broker authorizes, journals, invokes, and records the request
according to a formal state machine explored by bounded TLA+ model checking.
The mechanized T1 theorem proves Broker safety for arbitrary finite executions,
T2 proves that an independently defined atomic-Journal runtime simulates that
Broker machine, and T3 proves that an independently defined typed-WAL runtime
weakly simulates the atomic Journal while preserving acknowledged durability
across every later parsed medium. T4-C0 composes those two closed simulations
into a direct typed-WAL-to-Broker weak simulation and transfers T1 safety to
the resulting Broker execution and every mapped Broker prefix. T4-C1 adds the
machine-checked storage-parametric context boundary: ordered normalized
observations, a masked runtime view, and prefix-closed plugged executions for
the WAL, Journal, and Broker machines. T4-C2 completes T4 by constructing the
canonical plugged Broker execution and proving finite forward contextual
replacement with exact context-state and ordered endpoint-view equality at
every canonical mapped prefix. T5-S0 begins the recovery theorem by proving
exact one-step committed-history laws for the Broker, atomic Journal, and typed
WAL machines. T5-E0 lifts those laws to arbitrary intervals of every finite
execution. T5-R0 proves exact committed-history equality from a selected
`Crash` through the first later `FinishRecover`. T5-C0 completes T5 by proving
committed-history equality at every canonical WAL-to-Broker mapped prefix and
exporting recovery endpoint equality through the storage-parametric contextual
replacement theorem. H1 closes the cumulative artifact's configuration-level
nonvacuity gap with a concrete well-formed configuration and binds verification
evidence to the exact checked sources and toolchain. T6-D0 then freezes the
request-local adapter rely, duplicate-rejecting terminal and delivery
selectors, configuration-explicit outcome evidence, compatibility branches,
and separate Journal/WAL bridge statement boundaries without claiming the
bridge theorem.

The first research target is deliberately smaller than a complete agent
runtime. T1 establishes the Broker-side form of the claim:

> For each broker-generated internal request identifier, every logical
> completion recorded by the broker was authorized by a valid capability,
> appears at most once in the broker history, and has exact Journal and physical
> provenance across crashes and recovery.

The model also makes the limits of this claim explicit. None of T1--T5 proves
that a physical call sequence
denotes one external abstract effect. A remote tool call can have an ambiguous
outcome. Idempotence can collapse repeated mutations into one abstract effect,
while physical at-most-once acceptance requires a remote deduplication or
transactional contract; those adapter laws enter the later end-to-end theorem.

## Formal model

- [Formal model](formal/README.md) defines the scope and modeling decisions.
- [Research contract and threat model](formal/threat-model.md) fixes the
  adversary, trusted base, guarantees, assumptions, and non-goals.
- [Mathematical specification](formal/specification.md) defines traces,
  transitions, abstraction, and the theorem statements.
- [Mechanization contract](formal/mechanization-contract.md) is the normative
  statement of theorem V1, including the independent abstract and concrete
  machines, labeled executions, rely conditions, and theorem layers T1--T6.
- [Verified mechanization checkpoints](mechanized/README.md) document M0, R1,
  B1, C1, D1, Q1, B2-R, B2-C, B2-P0, B2-P1, B2-P2, B2-P3, B2-L, B2-A,
  G0, G1-P, G1-E, T1, T2-J0, T2-J1, T2-E, T2-R, T2, T3-W0,
  T3-W1-T, T3-W1-E, T3-W1-R, T3, T4-C0, T4-C1, T4-C2, T5-S0, T5-E0,
  T5-R0, T5-C0, H1, and T6-D0.
  M0 checks a reduced atomic-Journal safety slice; R1 checks the complete typed record language and
  replay invariants; B1 checks a
  generic crash-reset append protocol and acknowledgment trace; C1 composes B1
  record eligibility with R1 structural legality; D1 couples that trace to a
  separately stored durable replay state; Q1 proves the durable retry and
  recovery queries used by executable Broker guards; and B2-R proves the
  record-side Broker, executor-slot, and recovery invariant for every finite
  prefix; B2-C refines full immutable requests, capabilities, and canonical
  call descriptors into R1's verified configuration; B2-P0 adds verified
  Invoke/Deliver transitions and exact physical trace projection. Physical
  B2-P1 then proves per-attempt physical order/uniqueness, acknowledged Start
  cuts, non-retroactivity, and exact live-slot delivery sources. B2-P2 adds
  aggregate retry bounds, full acknowledged authorization ancestry, failure-safe
  invocation cuts, and exact Outcome-after-Delivered ordering. B2-P3 adds
  exact Commit and Failure physical provenance, durable Unknown anchors, and
  recovery-source preservation. B2-L packages the exact thirteen-clause
  `BrokerInvariant`; B2-A lifts the complete local Broker through B1's append
  protocol and classifies crash-free append epochs; G0 provides the complete
  22-constructor event alphabet and exact 11/11 Broker/backend partition; G1-P
  proves the normative global trace projections; G1-E defines the relational
  configuration-sequence execution semantics; T1 proves parameterized Broker
  safety and prefix closure; and T2 constructs an exact atomic-Journal-to-Broker
  simulation with per-prefix representation and projection agreement. T3-W0
  defines the independent Full/Torn typed-WAL runtime, its exact 17-constructor
  event boundary, LSN-sensitive parser, recovery scanner, and eight-clause WAL
  invariant. T3-W1-T through T3 then derive WAL trace agreement, define the
  exact 12-match/5-stutter translation, prove the field-explicit WAL/Journal
  representation and step commutation, construct the compressed Journal
  execution and weak index map, and prove per-prefix representation,
  observation equality, and acknowledged-prefix durability. T4-C0 composes the
  T3 and T2 maps and relations, proves a direct WAL-to-Broker weak simulation,
  and establishes T1 safety for the complete Broker witness and every mapped
  prefix. T4-C1 defines the ordered context history, masks append
  linearization, gives a nonvacuous relational `ProgramContext<S>` over masked
  endpoint views, and proves structural WAL/Journal/Broker plugging,
  closed-execution erasure, hidden-step stuttering, prefix closure, translation
  compatibility, and shared zero-step and visible-step witnesses. T4-C2
  compresses context states exactly for events whose T3 translation is `Some`,
  rather than according to context-delta visibility, constructs the canonical
  plugged Journal and Broker executions, and proves
  exact context-state and ordered `ContextView` equality at every canonical
  mapped prefix while retaining C0 simulation, projection, T1, and mapped-prefix
  T1 conclusions. T5-S0 defines the backend-specific committed-history
  abstractions and proves that each accepted machine step either stutters or
  appends exactly the `CommitEntry` carried by its own durable Commit
  linearization. T5-E0 proves committed-history prefix monotonicity between any
  two ordered configuration indices in a finite Broker, Journal, or WAL
  execution. T5-R0 defines a first-`FinishRecover` episode using only event
  positions, derives recovery-repair classification and commit stuttering for
  every episode step, and proves exact endpoint equality. Minimal Broker,
  Journal, and WAL episodes plus a repeated-`Crash` Broker episode establish
  nonvacuity. T5-C0 proves exact WAL/Broker committed-history equality at every
  canonical mapped prefix, carries R0 equality to the mapped Broker prefixes at
  `mu[crash]` and `mu[finish + 1]`, and instantiates the complete contextual
  theorem on a six-event WAL recovery execution with seven inert context states.
  H1 constructs a total `FullConfig`, proves it well formed, and unconditionally
  inhabits the complete T5-C0 premise/conclusion package. T6-D0 introduces the
  complete adapter/terminal definition surface, verifies unique selector and
  branch-unfolding sanity obligations, and fixes one shared core plus separate
  Journal and WAL T6-S0 statements.
- [Adapter refinement](formal/adapter-refinement.md) defines how concrete
  retries and outcomes denote abstract effects for each adapter class.
- [Value refinement](formal/value-refinement.md) specifies and model-checks
  provenance of committed successful payloads.
- [Refinement structure](formal/refinement.md) records the checked mappings,
  completed T1--T5 theorems, the bounded composed product, and the remaining T6
  proof layer.
- [TLA+ model](formal/EffectBroker.tla) is an executable finite-state version
  of the broker protocol.
- [Typed Journal](formal/EffectBrokerJournal.tla) defines record legality,
  replay, references, and terminal provenance.
- [Journal refinement](formal/EffectBrokerJournalRefinement.tla) checks the
  coupled `Journal -> EffectBroker` simulation.
- [Typed WAL](formal/EffectBrokerWAL.tla) models Full/Torn frames, flush
  acknowledgement, crash recovery, and temporal refinement to Journal.
- [Composed WAL refinement](formal/EffectBrokerWALRefinement.tla) checks the
  direct bounded `BrokerContext[WAL] -> EffectBroker` refinement.
- [TLC configurations](formal/model-suite.json) exercise broker retry classes,
  both refinement links, their composed product, and targeted storage crash
  states.
- [Tooling notes](formal/tooling.md) document smoke/full suites, pinned
  dependencies, coverage, and platform prerequisites.

Run `powershell -ExecutionPolicy Bypass -File formal/check-model.ps1` to fetch
the pinned model-checking runtime, validate complete configuration registration,
copy the selected TLA+ inputs into an isolated read-only, hash-checked temporary
snapshot, and explore the smoke and full state spaces. The runner emits a
source-hashed JSON report by default. Add `-Suite smoke` for a fast regression
run or `-Coverage` for TLC coverage data.
Run `powershell -ExecutionPolicy Bypass -File mechanized/verify.ps1` to fetch
the hash-pinned Verus and rustup artifacts plus the version-pinned Rust
toolchain into a fresh per-run environment, verify from an exact read-only
source snapshot, enforce the proof/import policy, and emit a source-hashed
verification report with the observed Rust tree digest.
The current result is M0 21, R1 86, B1 39, C1 128,
  D1 144, Q1 144, B2-R 169, B2-C 175, B2-P0 193, B2-P1 251, B2-P2 276,
  B2-P3 292, B2-L 310, B2-A 335, G0 342, G1-P 410, G1-E 429, T1 461,
  T2-J0 475, T2-J1 486, T2-E 508, T2-R 520, T2 531, T3-W0 577,
  T3-W1-T 588, T3-W1-E 626, T3-W1-R 641, T3 659, T4-C0 676, T4-C1 720,
  T4-C2 734, T5-S0 743, T5-E0 747, T5-R0 769, T5-C0 783, H1 786, and T6-D0
  799 obligations, all with zero errors. At T5-R0, 34 registered targets contained
  806 dependency-aware non-duplicated obligations; T5-C0 had 35 targets and 820;
  H1 had 36 targets and 823; the current T6-D0 registry has 37 targets and 839.

## Current boundary

The bounded model covers capability authorization with request-to-capability
maps and per-capability budgets, including small cross-capability scenarios;
durable operation states; explicit send/delivery/persistence crash windows;
retries and ambiguous outcomes; typed Journal replay; interruptible symbolic
torn-write recovery; and logical completion. Symbolic tail removal is still
one atomic transition. Theorem V1 deliberately remains safety-only and uses a
globally serialized writer and executor. It does not yet model capability
delegation, concurrent resource conflicts, delivery of committed results back
to the agent, confidentiality, liveness, semantic replay coalescing, or
byte-level WAL encoding.

The TLA+ modules are finite model-checking oracles. Their `MaxJournalLength`,
scenario-wide `MaxAttempts`, and shared `AllowedResults` constants bound
exploration. Theorem V1 has no logical Journal-length limit, gives each request
an immutable `max_attempts(r)`, and uses request-indexed result predicates. A
bounded implementation must report capacity failure before staging rather
than silently disabling an append.

The parameterized T1 Broker-safety proof is complete. M0 proves
authorization-before-invocation, per-capability budget conservation, terminal
uniqueness, and administrative commit-history stuttering for a reduced atomic
Journal machine. R1 adds the full typed Journal record language, total replay,
exact reference legality, authorization/attempt/terminal projections, and
durable value/failure/Unknown provenance for every legal prefix. Append and
acknowledgment traces are now proved separately in generic B1, including
delayed return, DiskFull normalization, crash reset, and all-prefix projection
agreement. C1 now discharges the record-level composition: every admissible B1
linearization preserves R1 Journal legality and replay safety at every prefix.
D1 proves that a separately stored durable state changes exactly at such a
linearization and remains equal to replay. Q1 proves total durable attempt and
outcome queries, ghost-free recovery guards, and the implication from full
structural record legality to the reference-erased executable guard. B2-R adds
the actual record-side Broker modes, complete slot ADT and record transformer,
append/recovery control, durable slot agreement, and all-prefix trace theorem.
Its local event language omits Invoke and Deliver. B2-C supplies rich
request/capability scope and canonical-call refinement, and B2-P0 supplies the
physical transition and trace substrate. B2-P1 proves per-attempt physical
causality and live-slot source validity. B2-P2 proves aggregate retry,
acknowledged authorization, and Outcome/delivery refinement. B2-P3 proves
terminal physical provenance and recovery-source preservation. B2-L packages
the exact thirteen-clause Broker invariant without hiding the stronger
inductive predicate inside it. B2-A establishes the append-protocol bridge,
exact acknowledgment returns, and crash-free epoch language. G0 and G1-P define
the closed global event alphabet and all normative projections, while G1-E
gives the independent relational `Exec` semantics and rejects backend-only
events from Broker steps. The exported generic T1 theorem then proves exact
per-prefix trace agreement, invariant preservation, append/recovery structure,
authorization and retry safety, terminal uniqueness, and committed-value
provenance for every finite execution. It is deliberately independent of any
adapter-effect interpretation.

T2 is also complete. Its specification-level runtime stores only the atomic
Journal, executor slot, mode, and append control; proof evidence is separate,
and no Broker durable state or replay shadow is embedded. T2 is a
specification-to-specification refinement theorem, not verification of
executable Rust. It proves the runtime's
operational admissibility and per-prefix `TraceAgreement`, gives the exact
`Representation` relation, renames only `JournalAppendLinearize` to
`BrokerLinearize`, constructs the Broker execution and identity weak-index map,
and proves equality of all required append, authorization, Journal, physical,
adapter, control, and logical projections.

T3 is complete. Its independently defined specification-level runtime
stores only typed Full/Torn frames, a volatile cache and current-epoch
acknowledgment watermark, scan state, executor slot, mode, and append control.
`Parse` stops at a Torn frame or unexpected LSN. The checked eight-clause
invariant covers sequential LSNs, the unique Torn tail, Journal legality,
append/cache/media shapes, current-epoch acknowledged durability, scan/recovery
shape, and canonical truncation. The proof establishes exact 17-of-22 event
closure, parsed-history monotonicity, acknowledged-prefix containment, and
invariant preservation at every finite execution state. It then compresses the
five private torn-write/recovery actions to zero Journal steps, maps each of the
twelve visible actions to its atomic counterpart, constructs the Journal
execution and nondecreasing weak-index map, and proves the full field-level
representation and all normalized projection equalities at every related
prefix. Every acknowledged prefix at an earlier WAL state is also proved to be
a prefix of every later `Parse(media)`.

T4-C0 is complete. It composes T3's compressed WAL-to-Journal map with T2's
identity Journal-to-Broker map, proves direct event and representation
composition at every related prefix, preserves all normalized observations and
acknowledged-prefix durability, and applies T1 to the complete Broker witness
and every mapped Broker prefix. This theorem ranges over the three closed
runtime relations. It does not define context state or plugging semantics,
prove storage-parametric noninspection, or establish the full contextual T4
replacement rule.

T4-C1 is complete. Its normalized history preserves ordering across append
Call/Return, cut-erased Invoke/Deliver, and crash/recovery control; `DiskFull`
emits an atomic Call/Full-return pair. Its runtime view hides both the slot
update and Called-versus-Linearized phase while an append is pending. A
`ProgramContext<S>` receives only the immutable request map, the masked pre- and
post-step views, and a nonempty normalized delta. The mechanization proves
exact append-I/O recovery, matched-event and whole-trace compatibility through
T3 and T2, hidden-step state/view stuttering, structural plugged executions for
all three backends, erasure, prefix closure, an accepting inert context, a
shared zero-step witness, and a positive shared one-`Crash` execution.

T4-C2 is complete. It compresses the source context-state sequence according to
whether T3's `translate_event` returns `Some`, not according to `context_delta`,
constructs canonical plugged Journal and Broker executions, and proves exact
shared context-state and ordered
endpoint `ContextView` equality at every canonical mapped prefix. The exported
theorem explicitly assumes `StorageParametricContext` and a plugged WAL
execution, and retains C0 weak simulation, projection agreement, full T1 safety,
and mapped-prefix T1 safety. The result is forward replacement only: reverse
equivalence, liveness, autonomous context steps, protected-handle exclusivity,
adapter effect refinement, and byte-level WAL correctness remain outside T4.

T5-S0 is complete. It uses the Broker durable `commit_log` as
`alpha_commit_B`; for the Journal and WAL it uses
`Replay(JournalView).commit_log`, with the WAL view equal to `Parse(media)`.
Only `BrokerLinearize(CommitRec)`, `JournalAppendLinearize(CommitRec)`, and
`WalWriteFull(CommitRec)` or `WalFinishTorn(CommitRec)` append one exact
`CommitEntry`; every other accepted step stutters. The WAL law assumes the
runtime `wal_invariant`, which excludes ghost-evidence agreement, and
additionally proves exact parsed-view behavior, including Torn-write stuttering
and equality across tail truncation. Reachable states obtain this premise from
T3-W0's `basic_invariant`.

T5-E0 is complete. For every finite Broker, atomic-Journal, or typed-WAL
execution and configuration indices `i <= j < configs.len()`, the committed
history at `i` is a prefix of the history at `j`. The WAL theorem exposes only
the WAL `Exec` predicate: reachability supplies `basic_invariant` and discharges
the local `wal_invariant` premise internally.

T5-R0 is complete. For event indices `crash < finish < events.len()`, an episode
starts with `Crash`, ends with `FinishRecover`, and contains no earlier
`FinishRecover`. Valid execution semantics, rather than an episode assumption,
force every intermediate durable linearization to be a conclusive `FailRec` or
recovery `UnknownRec`. Every event at `crash <= i <= finish` has zero commit
delta and preserves `alpha_commit`; consequently `configs[crash]` and
`configs[finish + 1]` have exactly equal committed histories. The WAL theorem
discharges its invariants internally. Minimal Broker, Journal, and full
scan/truncate WAL episodes, plus a repeated-`Crash` Broker episode, prove the
predicate is inhabited. This is closed-machine committed-history equality only:
T5-C0 supplies the separate mapped/contextual export.

T5-C0 is complete. For every source configuration index `i`, it proves exact
equality between the WAL committed history at `i` and the Broker committed
history at the canonical mapped prefix `mu[i]`. Given a source WAL
`RecoveryEpisode(crash,finish)`, it proves source endpoint equality and the
corresponding cross-backend and Broker endpoint equalities at `mu[crash]` and
`mu[finish + 1]`. The exported theorem retains T4-C2's well-formed
configuration, storage-parametric context, and plugged WAL execution premises,
plus the source episode premise. A minimal six-event WAL recovery trace with
seven identical inert context states proves that this premise conjunction and
the final conclusion are inhabited. T5 does not transport `RecoveryEpisode` to
the Broker event trace, equate full machine or context state across recovery,
or interpret physical invocations as external effects. T6 is the next open
semantic theorem.

H1 is complete. Its concrete configuration maps every request to an
uncontrolled, single-attempt request with no stable key and gives every
capability unit budget with universal resource and argument scope. The
premise-free H1 theorem instantiates the inert context and minimal contextual
recovery execution, proving that the cumulative T5-C0 package is inhabited.
This is a consistency result: the witness does not contain a nonempty pre-crash
commit history or an external adapter effect. H1 also hardens the artifact
boundary with isolated model/tool snapshots for TLC, strict manifest coverage,
exact source snapshots and source-hashed Verus reports, immediate-parent import
validation, and complete proof-policy scanning. T6-S0, the terminal evidence
and compatibility bridge, remains open. T6-D0 now fixes its definitions;
T6-E0, the terminal-evidence half, is next.
