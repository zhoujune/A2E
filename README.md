# ProveAI: Verified Agent Effect Broker

The frozen first-paper scope, contribution structure, required evaluation, and
artifact exit criteria are defined in
[`formal/fse-2027-submission-contract.md`](formal/fse-2027-submission-contract.md).
The source-backed [related-work and novelty audit](formal/related-work-audit.md)
records the surviving qualified contribution claim and the closest competing
systems through its 2026-08-10 search cutoff.

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
bridge theorem. T6-E0 proves the generic Broker-side evidence half: an
invariant Broker snapshot whose Journal and physical histories equal the event
projections and whose trace has a unique terminal outcome satisfies
`OutcomeEvidence` over the request-local adapter projection. T6-C0 proves
the complementary `BrokerOutcomeCompatible` implication under the frozen
`AdapterRely` assumptions, by a complete retry-class and terminal-outcome case
analysis. T6-S0 combines those two implications into the frozen
`OutcomeEvidence && BrokerOutcomeCompatible` conclusion and transports it
through both the atomic-Journal and typed-WAL representation boundaries. T6-A0
closes the first concrete adapter instance: it proves the generic
terminal-bridge-to-`Refines` implication, verifies an idempotent `EnsureMember`
set-insertion contract, and inhabits that contract with a nonempty terminal
typed-WAL execution. T6-A1 refines an explicit adapter/service protocol machine
to that semantic contract, derives `AdapterRely` from its transition invariant,
and composes it with a reachable crash/recovery/retry WAL execution ending in
`Unknown(NonConclusiveFailure)`. T6-M0 adds a separately defined protected-
service machine, related to A1 event by event, and a storage-parametric closed-
interface audit context. It derives
`CompleteMediation` from their generated invocation traces and proves that every
target mutation is a service linearization rooted in a durably authorized
Broker invocation. This exclusivity is structural inside the formal deployment
model; production adapter, network, operating-system, and remote-service
implementations remain outside the verified boundary.
T6-P0 then replaces the concrete witness's whole-trace-only coupling boundary
with a reusable prefix-indexed execution-pair relation. A weak index advances
once for each observed global event and stutters for silent service
linearization or environment interference. From independently valid A1,
protected-service, and typed-WAL executions satisfying that step coupling, P0
derives exact observed-trace and request-history agreement, complete mediation,
and adapter/protected effect-state agreement at every related prefix, together
with prefix closure. This is a conditional product theorem: it does not
construct a typed-WAL execution from an arbitrary adapter execution. T6-X0 now
composes that adapter-to-WAL index with T4-C2's canonical WAL-to-Broker index.
For every related adapter prefix, the resulting storage-parametric contextual
product preserves the exact request history, context state and masked view, and
T1 safety at the mapped Broker prefix. Its terminal theorem transports
`Refines`, per-request effect refinement, and `CompleteMediation` from the WAL
trace to the canonical Broker trace while grounding the external run in the
independently executed protected-service state. T6-RO0 adds a second
executable adapter instance, for the ReadOnly retry class: a read linearizes
by sampling an environment-owned Boolean at an explicit environment-history
cut, only environment transitions change that Boolean, and `zero_effect`
factors the post-state as the initial state plus those transitions. Its
premise-free 33-event adapter/31-event WAL crash/retry witness terminates in
a conclusive `Fail` on attempt 2 despite attempt 1's delivered Success,
making the ReadOnly branch of `Refines` non-vacuous with an operational
model. This ReadOnly claim stops at the adapter/WAL/Broker refinement boundary:
it does not instantiate a separate protected-service execution, complete
mediation, the P0 prefix product, or the X0 contextual lift. T6-DD0 starts the
third instance, for the Deduplicated retry class, by
defining the keyed decision/memoization semantics, a well-formed fixed
configuration, and the operational transition system. T6-DD1 proves that
machine's inductive invariant, derives the deduplication service law and
`AdapterRely` for every finite execution, and discharges `AdapterVerified`.
T6-DD2 makes that safety theorem operationally non-vacuous with a premise-free
31-adapter-event/30-WAL-event witness: attempt 1 silently applies and memoizes a
value, a crash occurs before its delivery, and attempt 2 reuses the stable key,
receives the memoized Success, and commits exactly that one effect. T6-DD3
couples that witness to an independent 31-event protected-service execution,
proves the stable key has exactly one service decision and that the retry is a
memoized return rather than a second mutation, derives complete mediation, and
connects every protected decision to its exact durably authorized WAL invoke.
T6-DD4 adds the projection-length adapter/WAL weak index, proves effect-state,
history, and mediation agreement at every adapter prefix, composes that index
with T4-C2's canonical WAL/Broker replacement, and transports the DD2 source
terminal refinement and complete mediation to the contextual Broker trace.
T6-DD5 makes the operational/protected premise request-indexed: a family maps
each request to a paired member, coverage is required for every terminal request
in the shared WAL, and the generic theorem transports every covered terminal
through DD4 and X0. The DD2 family discharges coverage without premises.

K1, K2, and K3 add a separate executable-kernel refinement track at the durable
Journal boundary. K1 implements a concrete `u64`/vector durable summary and
proves its Authorize and Start decisions equal Q1's specification guards for a
fixed four-lane demo configuration. K2-G0 completes all nine reference-erased
record guards. K2-T0 adds accepted-record mutations, including fresh
request/capability insertion, and proves exact coupling to `apply_record` and
legal-prefix `replay_push`. K3-A0 adds an executable nine-variant Journal record
whose LSN references remain exact `u64` values, resolves those references by
scanning the concrete Journal, and implements a serialized
`Call`/`Linearize`/`Return` append loop. Every successful concrete trace from
the initial state has exact projections to B1's `pi_append`, `pi_journal`, and
`pi_ack`. `u64` LSN-space exhaustion or structural-admission rejection at
`Call`, a mismatched or out-of-phase `Linearize`, and an out-of-phase `Return`
leave the concrete state unchanged.
K3-A0 is still not a complete broker event loop: concurrent writers, executor
slots, invocation, crash/recovery, transport, physical persistence, and
deployment remain outside this executable kernel.
K4-C0 adds a finite executable admission-manifest configuration matching M4's
profile fields. Its total formal `Config` view derives attempt limits from the
retry class, defaults unbound requests conservatively, and proves `config_wf`
for every well-formed manifest, with a premise-free Idempotent profile witness.
K4-R0 threads that configuration through the executable Authorize guard, proves
its decision equals R1's durable semantic guard for every well-formed manifest,
and supplies a premise-free accepted M4/K3 Idempotent profile. K4-R1 adds
manifest-parameterized request-field, retry-class, capability, and attempt
profiles plus the executable Prepare and Start guards. K4-R2 adds the first
manifest-parameterized accepted-record mutation for Authorize, including a
premise-free budget-decrement and witness-update execution. K4-R3 adds the
accepted Prepare phase mutation and an Authorize-to-Prepare execution witness.
K4-R4 fills the Arm gap with a manifest-parameterized guard, accepted phase
mutation, and Authorize-to-Prepare-to-Arm witness. K4-R5 adds the accepted Start
attempt-log mutation and reaches the first pending attempt. The remaining
guards, mutations, materialization, and K3 append state still use the fixed
demo config.

M4 adds a separate standard-Rust
[`reference-broker`](reference-broker/README.md) prototype around that verified
conceptual boundary. It implements generated request IDs, configured
capability budgets, exact record ancestry, a checksummed file WAL with torn-tail
recovery, one executor slot, invocation correlation, terminal retrieval, and
Uncontrolled, Idempotent, and Deduplicated example adapters. Its deterministic
tests cover all seven durable/volatile crash sites for all three adapters. M4
does not extend the Verus theorem boundary: the Rust wrapper, byte encoding,
filesystem calls, adapters, transport, and deployment remain trusted or
unverified exactly as listed in the crate README.

The first versioned RQ1/RQ2
[`evaluation report`](reference-broker/evaluation/results/README.md) reruns the
21-case crash matrix, validates stale-delivery rejection and exact ancestry,
and records release-mode latency, throughput, WAL, flush, recovery, retry, and
effect measurements against direct and journaled-at-least-once ablations. A
controlled follow-up adds five warmups, thirty measured repetitions, confidence
intervals, and CPU pinning on Linux; it still does not claim universal
performance. A paired overlayfs/tmpfs run now holds source, binary, host, CPU,
and protocol fixed, demonstrating storage-path sensitivity without treating
memory-backed tmpfs as durable-media or independent-host evidence.
An additional retained run uses the server's `/dev/nvme3n1`-backed ext4 mount;
it supplies physical-storage evidence but remains same-host Kubernetes data.
The retained `rq2-repeated-wsl2-ext4.json` run adds a separate physical-host
condition from WSL2 on the laptop, with persistent ext4 virtual storage and
explicit WSL2 kernel/mount provenance. It is not native direct-device evidence.
The [Linux artifact runner](artifact/README.md) now provides fail-closed smoke
and full TLA+ commands with isolated input snapshots; an executed run still
requires the pinned Java/TLA+ package described there.
The release-facing [`reproduce.sh`](reproduce.sh) and [`reproduce.ps1`](reproduce.ps1)
commands select smoke or full reproduction and write a fresh summary directory;
[`DEPENDENCIES.md`](DEPENDENCIES.md) and [`TROUBLESHOOTING.md`](TROUBLESHOOTING.md)
document the offline toolchain and common failures.
The same evaluation package now generates RQ3 adapter effort directly from the
hash-bound Verus report and supplies an 18-cell RQ4 safety/availability matrix,
including an executable recovery-interruption test.

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
- [M4 reference broker](reference-broker/README.md) documents and tests the
  executable prototype and its verified/trusted/unverified boundary.
- [Research contract and threat model](formal/threat-model.md) fixes the
  adversary, trusted base, guarantees, assumptions, and non-goals.
- [Mathematical specification](formal/specification.md) defines traces,
  transitions, abstraction, and the theorem statements.
- [Mechanization contract](formal/mechanization-contract.md) is the normative
  statement of theorem V1, including the independent abstract and concrete
  machines, labeled executions, rely conditions, and theorem layers T1--T6.
- [Verified mechanization checkpoints](mechanized/README.md) document M0, R1,
  B1, C1, D1, Q1, K1, K2-G0, K2-T0, K3-A0, K4-C0, K4-R0, K4-R1, K4-R2, K4-R3, K4-R4, K4-R5, B2-R, B2-C, B2-P0, B2-P1, B2-P2,
  B2-P3, B2-L, B2-A,
  G0, G1-P, G1-E, T1, T2-J0, T2-J1, T2-E, T2-R, T2, T3-W0,
  T3-W1-T, T3-W1-E, T3-W1-R, T3, T4-C0, T4-C1, T4-C2, T5-S0, T5-E0,
  T5-R0, T5-C0, H1, T6-D0, T6-E0, T6-C0, T6-S0, T6-A0, T6-A1, T6-M0,
  T6-P0, T6-X0, T6-RO0, T6-DD0, T6-DD1, T6-DD2, T6-DD3, T6-DD4, and T6-DD5.
  M0 checks a reduced atomic-Journal safety slice; R1 checks the complete typed record language and
  replay invariants; B1 checks a
  generic crash-reset append protocol and acknowledgment trace; C1 composes B1
  record eligibility with R1 structural legality; D1 couples that trace to a
  separately stored durable replay state; Q1 proves the durable retry and
  recovery queries used by executable Broker guards. K1 implements and refines
  the Authorize/Start guards over a concrete durable summary; K2-G0 completes
  all nine reference-erased record guards; K2-T0 refines accepted-record
  mutations to exact durable replay updates; and K3-A0 adds exact concrete LSN
  reference validation, serialized append control, unchanged rejection paths,
  and exact successful-trace refinement to B1. K4-C0 maps a finite executable
  M4 admission manifest to a well-formed formal configuration; K4-R0 uses its
  finite lookups in the first parameterized executable Authorize guard, and
  K4-R1 adds the corresponding Prepare and Start guards. K4-R2 parameterizes
  the accepted Authorize durable mutation, and K4-R3 adds Prepare mutation.
  K4-R4 adds the Arm guard and mutation, and K4-R5 adds Start mutation. B2-R proves the
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
  Journal and WAL T6-S0 statements. T6-E0 derives the generic/event
  `OutcomeEvidence` conclusion from the Broker invariant and exact Journal and
  physical projection equalities, including strict-prefix Commit/Fail
  references, uniquely selected deliveries, and exact Unknown structural
  evidence. T6-C0 imports that evidence theorem and proves
  `BrokerOutcomeCompatible`: ReadOnly needs only exact evidence; Idempotent
  failure covers every invocation with a durable Failure delivery;
  Deduplicated failure excludes a Success or InvalidResult observation by the
  adapter consistency law; and Uncontrolled outcomes inherit the Broker's
  single-invocation retry bound. Unknown outcomes additionally recover their
  exact reason guard and durable cause from Journal legality. T6-S0 combines
  the completed evidence and compatibility halves, exports the frozen core
  statement, and discharges the atomic-Journal and typed-WAL wrapper statements
  using final-prefix trace agreement and the existing representation relations.
  T6-A0 proves that this frozen conjunction, together with a verified adapter
  contract, entails `Refines` and per-request effect refinement under Journal
  legality and `AdapterRely`. Its concrete
  idempotent `EnsureMember` adapter interprets an external run as set insertion,
  proves zero/one-effect nondegeneracy and retry-collapse laws, and supplies an
  exact 20-event typed-WAL terminal witness plus a premise-free package theorem.
  T6-A1 adds an operational adapter state machine with explicit invocation,
  service-linearization, crash/recovery, and environment steps. Its premise-free
  witness couples 32 adapter events (one silent linearization) to 31 WAL events
  and seven durable records: attempt 1 succeeds and linearizes, recovery retries
  attempt 2, attempt 2 fails without linearizing, and the selected terminal is
  `Unknown(NonConclusiveFailure)`. The proof derives `AdapterRely`, `Refines`,
  per-request effect refinement, exact one effect, and impossibility of `Fail`.
  T6-M0 couples that A1 execution event by event to a separate protected-service
  execution, derives its call trace rather than postulating it, and proves that
  the sole target-changing action references a prior canonical invocation with
  T1 durable authorization ancestry. A separately defined closed-interface
  audit context derives the same mediation equality for the plugged WAL witness.
  T6-P0 packages the A1, protected-service, and typed-WAL executions into a
  weakly indexed prefix product. It proves all-prefix trace/history agreement,
  mediation, effect-state agreement, and prefix closure, and instantiates the
  product with the 32-step adapter/protected and 31-event WAL crash/retry
  witness. It is an execution-pair theorem, not a forward-existence result.
  T6-RO0 adds a second operational adapter instance, for the ReadOnly retry
  class, whose reads sample an environment-owned Boolean at an explicit
  environment-history cut that only environment transitions change. Its
  premise-free 33-adapter-event/31-WAL-event crash/retry witness selects the
  conclusive terminal `Fail` on attempt 2 despite attempt 1's delivered
  Success, which the ReadOnly class permits because only Idempotent failure
  requires every invocation to have failed. T6-DD0 defines the Deduplicated
  adapter interpretation, fixed configuration, and memoizing service machine.
  T6-DD1 proves its invariant and finite-execution closure, derives the
  deduplication service law and `AdapterRely`, and proves the adapter's generic
  Commit/Fail/Unknown refinement obligation. T6-DD2 supplies the coupled
  terminal witness: attempt 1 invokes and silently memoizes an applied value,
  crashes before delivery, and attempt 2 receives the replayed Success for the
  same stable key and durably commits it. The concrete package proves exact
  adapter/WAL projection, WAL/Broker representation, terminal refinement, one
  effect, and no attempt-1 delivery. T6-DD3 adds the independently executed
  protected-service side of that witness. Its closed event alphabet permits the
  sole slot mutation only at `ServiceDecide`, aligns both adapter invokes with
  protected calls, aligns attempt 2's delivery with a memoized `ServiceReturn`,
  proves exact one-decision provenance for the stable key, derives complete
  mediation, and reuses T6-M0's exclusive-handle context and durable-
  authorization theorem for both calls and every decision. T6-DD4 relates every
  adapter prefix to the protected-service and WAL prefixes, composes its
  canonical weak index with T4-C2, and proves source/target terminal refinement,
  context-state/view agreement, complete mediation, and mapped-prefix T1 safety
  for the distinguished DD2 execution without premises.
  T6-DD5 generalizes the terminal boundary over a request-indexed family of
  operational/protected members: every terminal request must be covered by a
  valid coupled member, whose DD4 prefix product and X0 contextual transport
  then establish source/target refinement and mediation. The concrete DD2 family
  proves the coverage premise and is non-vacuous.
- [Adapter refinement](formal/adapter-refinement.md) defines how concrete
  retries and outcomes denote abstract effects for each adapter class.
- [Value refinement](formal/value-refinement.md) specifies and model-checks
  provenance of committed successful payloads.
- [Refinement structure](formal/refinement.md) records the checked mappings,
  completed T1--T5 theorems, the bounded composed product, the completed T6-S0
  terminal bridge, the T6-A0 semantic instance, and the completed T6-A1
  operational adapter refinement, T6-M0 model-level mediation boundary, and
  T6-P0 prefix-indexed execution product.
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
Run `powershell -ExecutionPolicy Bypass -File mechanized/verify.ps1` on Windows,
or `pwsh -NoLogo -NoProfile -File mechanized/verify.ps1` on Linux, to fetch the
platform-selected hash-pinned Verus and rustup artifacts plus the
version-pinned Rust toolchain into a fresh per-run environment. The driver
verifies from an exact read-only source snapshot, enforces the proof/import
policy, and emits a source-hashed verification report with the observed Rust
tree digest.
The current result is M0 21, R1 86, B1 39, C1 128,
D1 144, Q1 144, K1 159, K2-G0 179, K2-T0 208, K3-A0 248, K4-C0 255, K4-R0 266, K4-R1 274, K4-R2 276, K4-R3 278, K4-R4 281, K4-R5 283,
B2-R 169, B2-C 175,
B2-P0 193, B2-P1 251, B2-P2 276,
B2-P3 292, B2-L 310, B2-A 335, G0 342, G1-P 410, G1-E 429, T1 462,
T2-J0 476, T2-J1 487, T2-E 509, T2-R 521, T2 532, T3-W0 578,
T3-W1-T 589, T3-W1-E 627, T3-W1-R 642, T3 660, T4-C0 677, T4-C1 721,
T4-C2 735, T5-S0 744, T5-E0 748, T5-R0 770, T5-C0 784, H1 787, T6-D0
800, T6-E0 818, T6-C0 835, T6-S0 841, T6-A0 864, T6-A1 916, T6-M0 977,
T6-P0 1,000, T6-X0 1,022, T6-RO0 1,083, T6-DD0 1,085, T6-DD1 1,111,
T6-DD2 1,143, T6-DD3 1,182, T6-DD4 1,222, and T6-DD5 1,228 obligations, all
with zero errors. K1 adds 15 obligations beyond Q1, K2-G0 adds 20 beyond K1,
K2-T0 adds 29 beyond K2-G0, K3-A0 adds 40 beyond K2-T0, K4-C0 adds 7 beyond
K3-A0, K4-R0 adds 11 beyond K4-C0, K4-R1 adds 8 beyond K4-R0, K4-R2 adds 2 beyond K4-R1, K4-R3 adds 2 beyond K4-R2, K4-R4 adds 3 beyond K4-R3, K4-R5 adds 2 beyond K4-R4, T6-X0 adds 22 beyond
T6-P0, T6-RO0 adds 61 beyond T6-X0, T6-DD0 adds 2 beyond T6-RO0, and T6-DD1
adds 26 beyond T6-DD0; T6-DD2 adds 32 beyond T6-DD1; T6-DD3 adds 39 beyond
T6-DD2; T6-DD4 adds 40 beyond T6-DD3; T6-DD5 adds 6 beyond T6-DD4. The new
conservative definitional `PaperConfig` accessor lemma
lives in T1, so every cumulative target from T1 is one obligation above its
historical checkpoint count. The original T6-S0 checkpoint had 40 targets, 840
cumulative obligations, and 880 dependency-aware non-duplicated obligations.
The historical retained T6-A1 run had 42 targets, 956 non-duplicated
obligations, and 20,867 summed target obligations. The historical retained
T6-X0 run had 45 targets, 1,062 non-duplicated obligations, and 23,866 summed
target obligations. The current retained run passes all 63/63 registered
targets, contains 1,407 dependency-aware non-duplicated obligations, and sums
to 34,627 target obligations.

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
structural record legality to the reference-erased executable guard. The
separate K1--K3 executable track instantiates those guards over a concrete
durable summary, applies accepted records, preserves exact `u64` references,
and refines its serialized successful append traces to B1. K4-R0/R1 replace
the fixed configuration in the Authorize, Prepare, and Start decisions with
the finite M4 manifest and prove equality to Q1's semantic guards; K4-R2/R3
parameterize the accepted Authorize and Prepare durable mutations, and K4-R4
adds the Arm guard and mutation. K4-R5 parameterizes the accepted Start
attempt-log mutation. The remaining guards, mutations, materialization, and
append state are not yet parameterized. K3-A0 does not yet
add executor, invocation, crash/recovery, transport, or physical-storage
behavior. B2-R adds
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
or interpret physical invocations as external effects. That adapter-effect
obligation was the historical T5-C0 boundary. T6-A0 and T6-A1 now discharge it
for the semantic and operational `EnsureMember` instance, respectively. T6-M0
  additionally discharges `CompleteMediation` and model-level no-bypass for its
  separately generated protected-service execution and concrete plugged WAL
  witness. T6-P0 establishes the conditional prefix-indexed
adapter/protected/WAL product and its prefix closure. T6-X0 completes its
storage-parametric lift through the canonical plugged Broker execution and
derives the conditional single-request terminal, refinement, and mediation
conclusions at both WAL and Broker boundaries.

H1 is complete. Its concrete configuration maps every request to an
uncontrolled, single-attempt request with no stable key and gives every
capability unit budget with universal resource and argument scope. The
premise-free H1 theorem instantiates the inert context and minimal contextual
recovery execution, proving that the cumulative T5-C0 package is inhabited.
This is a consistency result: the witness does not contain a nonempty pre-crash
commit history or an external adapter effect. H1 also hardens the artifact
boundary with isolated model/tool snapshots for TLC, strict manifest coverage,
exact source snapshots and source-hashed Verus reports, immediate-parent import
validation, and complete proof-policy scanning. T6-D0 fixes the terminal
definitions, and T6-E0 proves the generic `OutcomeEvidence` half over the
event-level request projection. T6-C0 proves the complementary
`BrokerOutcomeCompatible` half under `AdapterRely`, including the Idempotent,
Deduplicated, and Uncontrolled retry obligations and Unknown-cause recovery.
T6-S0 combines the two halves into `OutcomeEvidence &&
BrokerOutcomeCompatible`, then proves the atomic-Journal and typed-WAL wrapper
statements by transporting final execution evidence through their existing
trace-agreement and representation boundaries. T6-A0 adds the first concrete
semantic closure: a verified idempotent set-insertion adapter, generic
bridge-to-`Refines` lemmas, a nonempty 20-event typed-WAL terminal execution,
and an exact premise-free package/nonvacuity theorem. T6-A1 adds the explicit
operational adapter/service protocol and a realizable typed-WAL sequence
`Invoke1, Success1, Crash, recover, Invoke2, Failure2`. The first attempt's
success is not journaled before the crash; the second attempt becomes current,
its failure is nonconclusive because the first invocation succeeded, and the
seven-record execution therefore terminates `Unknown`, not `Fail`, while
  denoting exactly one abstract set-insertion effect. T6-M0 separately
  constructs the protected-service call trace and a closed-interface audit context,
derives `CompleteMediation` for both, and proves the sole target mutation has T1
durable authorization ancestry. T6-P0 relates those independently valid
executions to the WAL by a weak prefix index, derives the complete all-prefix
product, and proves the product prefix closed. Its canonical map consumes one
WAL label per observed adapter event and stutters at the silent attempt-1
  linearization. The result is conditional on a coupled execution pair and does
not construct a matching WAL run for every adapter run. T6-X0 composes its
33-point adapter-to-WAL map with T4-C2's WAL-to-Broker map and proves the
all-prefix contextual relation. The premise-free 32-adapter/32-protected/31-WAL
crash/retry witness reaches the exact `Unknown(NonConclusiveFailure)` terminal,
denotes one rather than zero effects, retains complete mediation at the
canonical Broker endpoint, and has exactly one durably authorized protected
linearization. T6-RO0 separately supplies the complete ReadOnly operational
instance and witness. T6-DD1 now proves the Deduplicated machine invariant,
decision/history provenance, memoized observation consistency, execution-to-
`AdapterRely` theorem, and `AdapterVerified`. T6-DD2 closes its concrete coupled
terminal witness and WAL/Broker refinement with a crash before attempt 1's
reply and a memoized Success committed by attempt 2. T6-DD3 couples that run to
an independent protected-service machine, proves exact one-decision memoization,
complete mediation, and durable authorization ancestry under the closed M0
exclusive-handle context. T6-DD4 closes the all-prefix adapter/protected/WAL
product and its T4-C2 contextual Broker composition for that distinguished run,
including source/target terminal refinement and mediation at every mapped
prefix. T6-DD5 closes the request-indexed family theorem for admitted shared
WAL executions, with explicit terminal-request coverage and a premise-free DD2
family witness. This verifies the protocol
and deployment models, not production
adapter/network/service code or operating-system handle isolation. Matching-WAL
construction of family members from production adapter runs, byte/fsync
persistence, `ReturnResult`,
multi-request linearizability, least privilege, and liveness remain open.
