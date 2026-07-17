# Verified mechanization checkpoints

This directory contains machine-checked Verus checkpoints for the normative
proof contract in `formal/mechanization-contract.md`. The checkpoints are
cumulative research artifacts. The completed T2 target proves the atomic-
Journal runtime simulation on top of T1 parameterized Broker safety, and the
completed T3 target proves that the independent typed-WAL runtime weakly
simulates that atomic Journal with exact per-prefix representation and
observation agreement. The completed T4-C0 checkpoint composes those closed
runtime simulations into a direct WAL-to-Broker weak simulation and transfers
T1 safety to every mapped Broker prefix. The completed T4-C1 checkpoint fixes
the storage-parametric context observation and plugging interface. The completed
T4-C2 checkpoint constructs the canonical plugged Broker execution and proves
finite forward contextual replacement. T5-S0 proves exact one-step committed-
history laws for the Broker, atomic Journal, and typed WAL. T5-E0 lifts those
laws over arbitrary finite execution intervals. T5-R0 proves exact recovery-
episode equality and nonvacuity. T5-C0 proves all-prefix mapped committed-
history equality and contextual mapped recovery endpoint preservation. H1
closes the cumulative artifact's remaining configuration-level nonvacuity gap
with a concrete well-formed configuration and contextual recovery execution.
T6-D0 freezes the request-local adapter interpretation, unique terminal and
delivery selectors, evidence and compatibility branches, and shared-core plus
backend-specific bridge statement interfaces. T6-E0 proves the generic/event
Broker `OutcomeEvidence` implication over the request-local adapter projection.
T6-C0 proves the complementary `BrokerOutcomeCompatible` implication under the
frozen adapter rely. T6-S0 combines both implications and discharges the atomic-
Journal and typed-WAL bridge statements through their verified trace-agreement
and representation boundaries. T6-A0 closes the first concrete semantic adapter
instance: it derives `Refines` and per-request refinement from the frozen bridge,
proves an idempotent `EnsureMember` set-insertion contract, and supplies an exact
nonempty typed-WAL terminal witness. T4, T5, the T6 terminal bridge, and the
first adapter-semantic closure are complete; executable adapter refinement and
the full conditional end-to-end theorem remain open.

## M0: reduced atomic-Journal safety

`m0.rs` is the original reduced checkpoint. It uses unbounded natural-number
request, capability, and attempt identifiers, arbitrary total
request-to-capability and initial-budget maps, a collapsed record language, and
an atomic Journal transition.

M0 proves:

1. every physical invocation has an earlier matching authorization in the
   Journal prefix named by its immutable cut;
2. per-capability budget conservation;
3. terminal uniqueness and phase/terminal-count agreement;
4. commit-history projection agreement; and
5. crash/recovery-control commit-history stuttering.

M0 erases full record references, observations, values, deliveries, retry
classes, revocation, executor slots, append acknowledgment, and WAL state.

## R1: typed Journal replay safety

`t1_replay.rs` is the first full-record checkpoint on the path to T1. It uses
distinct unbounded, natural-backed wrapper sorts for request IDs, capability
IDs, digests, stable keys, adapter namespaces, valid values, and invalid
values. Attempts and one-based LSNs remain natural numbers because their
arithmetic is part of the model.

R1 mechanizes:

- the complete `JournalRecord` ADT, including Revoke, Outcome, values, failure,
  reason-specific Unknown records, and exact one-based references;
- total `ApplyRecord` and `Replay`, including saturated off-domain budget
  subtraction;
- total record lookups, deterministic latest-evidence selection,
  `StructuralEnabled`, and `JournalLegal`;
- exact auth, attempt, and commit projections from the Journal into replayed
  durable state;
- authorization uniqueness, witness agreement, prefix validity, durable scope
  confinement, and per-capability budget conservation;
- sequential attempts `1..started`, bounded retries, unique Outcomes,
  Start-prefix discipline, and at most one uncontrolled Start;
- terminal uniqueness, exact committed/failed/unknown field agreement,
  valid recorded Success values, durable Commit/Fail provenance, and
  reason-specific Unknown prefix provenance; and
- preservation under one legal extension plus the invariant for every legal
  Journal prefix.

The exported theorem is:

```text
config_wf(cfg) and journal_legal(cfg,j)
  implies r1_replay_invariant(cfg,j)
```

R1 is a replay-focused subset of proof groups 1--3. It does not yet mechanize
the complete Request/Capability/CallDescriptor vocabulary, canonical physical
calls, append Call--Linearize--Return control, acknowledgment cuts, executor
slots, physical Invoke/Deliver histories, crash/recovery steps, per-prefix
event projections, or any physical-delivery provenance. `matches` and
request-indexed valid results remain abstract configuration relations.

## B1: generic append and trace safety

`t1_append.rs` is a record-type-polymorphic append theorem. It does not inspect
record contents, so the full Broker proof can instantiate it with R1's
`JournalRecord` rather than duplicating append reasoning.

B1 mechanizes:

- Idle, Called, and Linearized append control;
- Call, matching Linearize, delayed successful Return, DiskFull, Crash, and
  unrelated stuttering labels;
- DiskFull normalization to an adjacent Call and `AppendFull` Return with no
  Journal or acknowledgment update;
- exact Journal, successful-ack, and normalized append projections;
- historical acknowledgment cuts, acknowledged prefixes, bounded and
  nondecreasing successful cuts, and one-step prefix monotonicity;
- Crash reset of append control without fabricating or deleting historical
  acknowledgment evidence;
- exact agreement between the derived protocol witness and the reached append
  control; and
- the checkpoint and Crash-aware protocol property for every executable
  prefix.

B1 also accepts an arbitrary record-eligibility predicate
`spec_fn(Seq<R>,R)->bool` and proves that admissibly executable calls,
linearizations, and DiskFull attempts preserve the corresponding control and
trace property. Instantiating that predicate with R1 `StructuralEnabled` and
proving the combined Broker append step preserves `JournalLegal` is the next
composition obligation. B1 itself does not claim record legality, executor
causality, tool invocation, or crash-recovery mode correctness.

## C1: legal append/replay composition

`t1_replay_append.rs` imports R1 and B1 and instantiates B1's eligibility
predicate with R1 `structural_enabled(cfg, records, record)`.

C1 proves by exhaustive finite-event induction that:

- every Linearize is structurally enabled at the exact preceding projected
  Journal;
- Call, ReturnOk, DiskFull, Crash, and Stutter do not change the Journal
  projection;
- every Linearize applies `r1_legal_extension` exactly once;
- `pi_journal` and the append state's reached record history are legal Journals
  satisfying the full `r1_replay_invariant`; and
- the combined B1 checkpoint, crash-aware append protocol, eligibility trace,
  Journal legality, and R1 replay invariant hold at every finite prefix.

C1 is the first checked composition between proof layers. It is not B2 or T1:
the complete immutable Request/Capability/CallDescriptor model, Broker durable
state, executor slot, physical Invoke/Deliver histories, source indices,
recovery gating, and the full Event ADT remain outside this checkpoint.

## D1: durable/append coupling

`t1_durable_append.rs` adds a genuinely separate stored durable projection. A
Linearize updates that field with `apply_record` and appends one proof-history
record; replay appears only in the coupling invariant, not as the field's
definition. Call, successful Return, DiskFull, and Crash preserve durable state.

D1 proves exact projection into C1, replay agreement, Journal legality, R1
safety, append/ack safety, and every-prefix preservation. It separates
`control_enabled` from proof-side `evidence_admissible`; their conjunction is
deliberately named `admissibly_enabled`, not an executable Broker guard. The
executor is fixed Idle and recovery is absent, so D1 is an append-fragment
coupling theorem rather than B2.

## Q1: durable retry/recovery queries

`t1_durable_queries.rs` defines total durable-state queries for started
attempts, recorded outcomes, latest attempts, conclusive failure, durable
uncertainty, unsafe uncontrolled requests, and exact recovery completion. It
proves each query agrees with its Journal counterpart under legal replay.

Q1 also defines reference-erased `abstract_record_enabled` over stored durable
state and proves every structurally enabled Journal record satisfies that
operational durable guard. Exact LSN references remain proof-side obligations;
the converse implication is intentionally false. Q1 supplies the missing
ghost-free guards needed by the full record-side Broker checkpoint.

## B2-R: record-side Broker safety

`t1_broker_records.rs` adds the actual record-side Broker state: Online,
Crashed, and Recovering modes; the complete executor-slot ADT; separately
stored durable and append-control fields; and proof-only record and
acknowledgment histories. Its total `durable_slot_update` covers every typed
Journal record in Online and Recovering modes. Operational guards inspect only
configuration and Broker state; exact LSN references and acknowledgment cuts
remain separately named proof-side admissibility obligations.

B2-R proves, for every finite admissible execution and every prefix:

- exact durable replay, R1 Journal safety, and C1 append/acknowledgment safety;
- durable slot agreement for Ready, InFlight, Received, and all Observed forms;
- exact Call--Linearize--Return, DiskFull, retry-release, stale-response,
  Crash, BeginRecover, and FinishRecover transitions;
- ghost-free recovery completion and crash/recovery shape;
- `ReadyReleaseAgreement`, so an Idle-append Ready slot has an acknowledged
  matching Start; and
- exact Journal, acknowledgment-prefix, and append-control trace projections.

The local event language deliberately omits Invoke and Deliver. Consequently,
closed executions from the initial state do not yet reach the InFlight,
Received, or Observed forms, although preservation covers record transitions
from arbitrary states satisfying the invariant. Physical histories, canonical
calls, delivery and commit source indices, and the unified global Event ADT
remain outside B2-R. It is therefore a record-side Broker theorem, not full T1.

## B2-C: rich configuration refinement

`t1_full_config.rs` defines immutable Request and Capability records with
principal, tool, operation, resource, arguments, retry metadata, digest,
adapter namespace, stable key, and budget fields. It derives capability
matching from those fields and their resource/argument sets, defines the full
canonical tool-call descriptor, and erases the rich configuration into R1's
already verified map representation without duplicating replay or Broker types.

B2-C proves universally that a well-formed rich configuration erases to an R1
`config_wf`; budgets, request metadata, matching, and valid-result predicates
agree exactly; stable-key namespace injectivity is preserved; every canonical
call copies all immutable call-descriptor fields; and every derived match implies the
complete scope checks. The carrier wrappers remain unbounded but countable,
and adapter interpretations are deferred to the later effect-refinement layer.
B2-C is a configuration foundation for physical invocation safety, not T1.

## B2-P0: physical transition and trace substrate

`t1_broker_physical.rs` wraps B2-R using B2-C's rich configuration. It adds
Invoke and Deliver labels, an explicit physical-event history, transient
`slot_source`, a full-domain `commit_source` map, canonical-call checks, and
separate proof-side Journal/acknowledgment cuts. Nonphysical events delegate to
B2-R; Invoke and Deliver change the executor slot while preserving its
record-side invariant.

B2-P0 proves for every finite admissible execution and every prefix:

- preservation of the complete B2-R invariant through physical and record
  transitions;
- the source-update mechanics, including Commit transfer and crash/retry/
  terminal clearing of the transient source;
- a full-domain commit-source map and non-Online transient-source clearing; and
- exact Journal, acknowledgment-cut, acknowledged-prefix, physical-history,
  and durable-replay projections.

This is deliberately a substrate theorem. It does not yet prove Invoke/Deliver
uniqueness or ordering, prior-return non-retroactivity, physical retry bounds,
semantic validity of source indices, Outcome--Delivered correspondence,
Commit/Fail physical provenance, append-control projection, the unified global
Event rejection theorem, full `TraceAgreement`, complete `BrokerInvariant`, or
T1. Those facts belong to B2-P and the final T1 assembly.

## B2-P1: physical causality and live-slot sources

`t1_broker_physical_causality.rs` strengthens P0 without changing its runtime
guards. It derives physical safety from the serialized executor slot, R1 Start
discipline, append-only records, and proof-side cut evidence.

B2-P1 proves for every finite admissible execution and every prefix:

- at most one Invoke and one Delivered event per request-attempt pair;
- every delivery has exactly one matching Invoke in its strict physical prefix;
- every Invoke carries the canonical `CallDescriptor`, bounded Journal and
  acknowledgment cuts, and a matching Start inside the acknowledged cut;
- the Invoke's acknowledgment cut occurs in the strict prior `pi_ack` trace,
  so later returns cannot retroactively authorize it;
- Ready, InFlight, Received, and Observed slots agree exactly with physical
  counts and the in-bounds matching delivery source; and
- all B2-P0 projection and B2-R invariant facts continue to hold.

B2-P1 does not yet prove aggregate retry or uncontrolled-invocation bounds,
an explicit acknowledged Authorize witness, Outcome-after-Deliver LSN order,
terminal `commit_source` validity, Commit/Fail/Unknown physical provenance,
adapter effects, the complete global Event rejection theorem, or T1.

## B2-P2: retry, authorization, and Outcome refinement

`t1_broker_physical_refinement.rs` strengthens P1 without adding a physical
attempt counter or any ghost-dependent runtime guard. A proof-only Ready credit
relates durable Starts to physical Invokes, while acknowledged prefixes and
live delivery sources provide the historical witnesses.

B2-P2 proves for every finite admissible execution and every prefix:

- aggregate Invoke counts do not exceed each request's immutable
  `max_attempts`, and uncontrolled requests have at most one Invoke;
- every Invoke's acknowledged prefix contains an earlier Start and an earlier
  Authorize that was valid at its own strict prefix, including exact
  capability, scope, digest, New phase, nonrevocation, and positive budget;
- an Invoke occurs neither after a conclusive failure at its stored Journal
  cut nor from a Start reserved after a conclusive failure;
- every durable Outcome has an earlier exact Delivered event with the same
  request, attempt, and observation, whose Journal cut is strictly below the
  Outcome LSN; and
- all B2-P1 causality, non-retroactivity, live-source, and B2-P0 projection
  facts continue to hold.

B2-P2 is safety-only: a delivery need not eventually acquire an Outcome. It
does not yet prove terminal `commit_source` validity, Commit/Fail physical
provenance, adapter effects, the complete global Event rejection theorem,
the exact execution-structure `TraceAgreement`, or T1.

## B2-P3: terminal physical provenance

`t1_broker_terminal_provenance.rs` closes the terminal-source portion of the
local physical Broker theorem. It stores no new failure source: recovery-safe
Failure provenance is reconstructed from the durable Outcome and P2's exact
Outcome-to-Delivered relation.

B2-P3 proves for every finite admissible execution and every prefix:

- `commit_source(r)` is defined exactly when the durable committed field is
  defined; it names the exact zero-based Delivered Success source for the same
  request, attempt, and value, and that value satisfies the result predicate;
- every Failed request names the latest attempt, has a conclusive durable
  Failure, and has an exact earlier physical Failure delivery whose Journal
  cut is strictly below its Outcome LSN, including Fail repaired in recovery;
- Unknown terminal provenance retains its exact reason-specific durable
  Journal anchor without claiming that hidden physical activity was absent;
- every enabled recovery linearization is either a conclusive Fail repair or
  an unsafe uncontrolled Recovery-Unknown repair and preserves the complete
  `commit_source` map; Crash also preserves that map; and
- all B2-P2 retry, authorization, Outcome, causality, trace, and all-prefix
  facts continue to hold.

B2-P3 still uses the local Broker event language. The following checkpoints
assemble it into T1 without changing P3's physical transition system. Adapter
effects remain outside this local provenance result and outside T1.

## B2-L: exact local Broker contract

`t1_broker_contract.rs` packages the local proof into the exact thirteen
numbered clauses of the normative `BrokerInvariant`. The contract predicate is
kept distinct from the stronger P3 predicate used for induction, so the theorem
does not conceal additional conclusions inside the paper invariant.

B2-L proves, for every finite admissible local execution and every prefix:

- replay agreement and budget conservation counted from the durable
  authorization log;
- authorization soundness and rich scope confinement, including the exact
  zero-activity shape for an unmatched request;
- attempt shape, two-way physical delivery/Outcome causality, retry discipline,
  and complete Start-backed executor-slot cases;
- terminal uniqueness plus Commit, Failure, and Unknown provenance;
- crash-mode shape and the complete append-interface shape, including
  `ReadyReleaseAgreement`; and
- both the exact thirteen-clause contract and the separately named stronger
  local inductive invariant at every prefix.

## B2-A: append protocol and epoch bridge

`t1_broker_append_bridge.rs` maps every local Broker label to exactly one B1
label. Invoke, Deliver, and administrative labels map to explicit, distinct
stutters, preserving local prefix indices instead of filtering the trace.

B2-A proves exact append-state homomorphism; Journal and acknowledgment
projection agreement; exact cuts on successful returns; B1 checkpoint,
eligibility, and append-protocol safety; and a regular-language classification
of every maximal crash-free append epoch. A successful transaction has
Call--Linearize--Return shape, a capacity failure has adjacent Call--ReturnFull
shape, and the final suffix is determined exactly by the current append
control.

## G0: complete global event closure

`t1_global_event.rs` defines the single 22-constructor event alphabet shared by
the paper's Broker, atomic-Journal, and typed-WAL layers. An exhaustive decoder,
with no wildcard arm, accepts exactly the 11 Broker constructors and rejects
exactly the 11 backend-only constructors. G0 also proves the total Broker
embedding and partial decoder are inverse on the accepted image and that the
embedding is injective.

## G1-P: normative global projections

`t1_global_projections.rs` defines the paper projections over the complete
global alphabet, including append, Journal, physical, acknowledgment, control,
logical, WAL, authorization, invocation, and adapter views. It proves exact
correspondence with every local projection on embedded Broker traces, preserves
prefix indices through encode/decode, relates logical terminals to Journal
records, and supplies the global append-protocol and crash-free-epoch views.

## G1-E: relational Broker executions

`t1_broker_execution.rs` defines `BrokerExecution` as an event sequence paired
with its authoritative configuration sequence and defines `Exec` relationally,
rather than by the earlier functional local runner. G1-E proves exact
initial/step correspondence, prefix closure, length-preserving decode into an
admissible local trace, agreement with the local runner at every configuration,
and explicit rejection of every backend-only label from a Broker execution.

## T1: parameterized Broker safety

`t1_parameterized_broker_safety.rs` exports the paper theorem over
`PaperConfig<A>`, where the adapter interpretation `A` remains completely
opaque. For every well-formed configuration and every finite relational Broker
execution, T1 proves:

- exact `TraceAgreement` at every prefix, including Journal, physical, and
  acknowledgment projections and non-retroactive successful-return cuts;
- all thirteen `BrokerInvariant` clauses at every reached configuration;
- global append-protocol safety and the classification of every maximal
  crash-free append interval;
- recovery-transition obligations, including source preservation and exact
  recovery completion;
- canonical, previously authorized invocation ancestry, bounded retry, and
  uncontrolled physical at-most-once safety;
- terminal uniqueness and exact committed-success physical/value provenance;
  and
- prefix closure as an exported theorem suitable for later simulations.

Append-protocol and all-configuration predicates are proved strengthening
conclusions, not additional semantic premises. T1 assumes only well-formed
Broker configuration and membership in the exact relational `Exec` relation.
It proves Broker safety, not adapter-specific external-effect refinement, WAL
runtime simulation, contextual replacement, or the T6 end-to-end theorem.

## T2-J0: independent atomic-Journal runtime

`t2_atomic_runtime.rs` defines `ConcreteRuntime` with exactly an atomic Journal,
executor slot, mode, and append control. Its separate six-field proof evidence
contains record, physical, acknowledgment, and source histories. J0 defines an
exhaustive 11-of-22 global-event boundary, direct runtime guards and state
updates, relational execution/prefix semantics, and preservation of Journal
legality, storage agreement, and the generic append invariant. It does not call
the Broker step or state transformer and stores no `DurableBroker` or replay
shadow.

## T2-J1: atomic-runtime trace agreement

`t2_atomic_trace.rs` exposes the operational `AdmissibleJournalTrace` predicate
and proves that every runtime execution satisfies it. It proves exact Journal,
physical, and acknowledgment projection agreement at every prefix, bounded and
monotone successful cuts, exact acknowledged-prefix reconstruction, and prefix
closure of the complete atomic-runtime `TraceAgreement`.

## T2-E: event and projection refinement

`t2_event_projection.rs` maps `JournalAppendLinearize(rec)` to
`BrokerLinearize(rec)` and preserves every other accepted label. It proves that
no accepted atomic-runtime event is silent in all T2-observed projections and
establishes exact equality of append, authorization, Journal, physical,
per-request adapter, control, logical, acknowledgment, and append-I/O
projections for the translated trace.

## T2-R: exact representation

`t2_representation.rs` defines the proof-only abstraction from the concrete
atomic runtime to Broker state and states `Representation` field by field. It
includes the exact `InvocationsAcknowledged` and `SourceAgreement` predicates,
including same-payload invalid-result provenance, and derives them from the
already verified local inductive Broker invariant without using that stronger
invariant as the representation definition.

## T2: atomic-Journal runtime simulation

`t2_atomic_journal_simulation.rs` proves one-step commutation, constructs the
target relational Broker execution, and supplies an identity weak-simulation
index map with exact endpoints and per-prefix representation. The exported
generic theorem accepts only a well-formed paper configuration, an atomic
runtime execution, operational admissibility, and runtime `TraceAgreement`; it
constructs the Broker execution and map existentially and proves all normative
T2 projection equalities. The canonical theorem is stronger: runtime `Exec`
itself derives operational admissibility and `TraceAgreement`.

## T3-W0: independent typed-WAL runtime and invariant

`t3_wal_runtime.rs` imports the complete T2 root once and defines a separate
typed-WAL runtime containing only Full/Torn frames, the volatile cache,
current-epoch `acked_len`, scan state, executor slot, mode, and append control.
Historical records, physical events, acknowledgment cuts, and source indices
remain in the shared proof-only `GhostEvidence`; there is no parsed-Journal,
replayed Broker, or durable-state shadow in the concrete runtime.

T3-W0 mechanizes:

- an LSN-sensitive, end-recursive `Parse` that stops permanently at the first
  Torn or unexpected-LSN frame, plus `FullFrames` and frame-record projections;
- parser algebra for complete frames, Torn tails, tail completion, canonical
  truncation, frame shape, and parsed-prefix monotonicity;
- the exact 17-of-22 WAL event boundary and direct transitions for Stage,
  full/torn writes, flush acknowledgment, DiskFull, physical execution,
  crash, scan/abort/truncation, and recovery;
- all eight normative `WALInvariant` clauses, with explicit media/cache length
  correspondence, plus the local strengthening equating ghost records with
  `Parse(media)` and reusing B1 append safety;
- initial and one-step preservation, exact event closure, execution-prefix
  closure, and the invariant at every state of every finite WAL execution; and
- two exported consequences needed by the next layer: the parsed Journal never
  shrinks, and every ghost acknowledged prefix is a prefix of the current
  parsed medium.

These local results are the foundation consumed by the completed T3-W1 proof.

## T3-W1-T: WAL trace admissibility and agreement

`t3_wal_trace.rs` proves operational admissibility and exact `TraceAgreement`
for every finite WAL runtime execution and each of its prefixes. It connects
the state invariant to `Parse(media)`, proves successful-return cut exactness
and Invoke cut agreement, and derives the trace premises used by the exported
T3 theorem directly from `Exec`.

## T3-W1-E: exact event compression and observations

`t3_wal_event_projection.rs` defines the partial WAL-to-Journal translation.
Twelve WAL actions map to one atomic-Journal action; `WalWriteTorn`,
`BeginScan`, `FinishScan`, `TruncateTail`, and `AbortScan` are exactly the five
zero-step actions. The module proves compressed-trace length, prefix, and index
lemmas, Journal closure of the translated trace, exact silence classification,
and equality of append, authorization, Journal, physical, per-request adapter,
control, logical, acknowledgment, and append-I/O projections. `pi_wal` is
intentionally excluded because it exposes the implementation backend.

## T3-W1-R: WAL/Journal representation and step commutation

`t3_wal_representation.rs` states `Representation` field by field: the atomic
Journal equals `Parse(media)`, executor mode and slot agree, append control
agrees, and all proof-only evidence agrees. It proves the initial relation,
transfers the atomic runtime invariant, proves that each visible WAL step
commutes with its translated Journal step, and proves that each internal WAL
step preserves the Journal projection exactly.

## T3: typed-WAL runtime simulation

`t3_wal_journal_simulation.rs` constructs a deterministic compressed Journal
execution and reuses T2's `WeakIndexMap`. Each source-prefix index maps to the
number of translated events in that prefix, so adjacent points differ by zero
or one. The proof establishes Journal `Exec`, exact event matching or stutter,
field-level `Representation` and normalized projection agreement at every
related prefix, and the exported existential theorem over `PaperConfig<A>`.
It also proves the cross-prefix durability result: an acknowledged prefix at
any execution state is a prefix of every later parsed WAL medium. This is a
specification-level typed-frame refinement; byte encoding, checksums, `fsync`,
and filesystem correctness remain below the theorem boundary.

## T4-C0: closed WAL-to-Broker composition

`t4_closed_composition.rs` composes the T3 WAL-to-Journal weak simulation with
the T2 Journal-to-Broker weak simulation. It defines generic weak-index-map
composition, proves that T2 cannot erase an accepted Journal step, composes the
two step correspondences, and derives direct WAL-to-Broker representation and
normalized projection agreement at every related prefix. For the canonical
witness, T2's identity map makes the composed map extensionally equal to T3's
compression map.

The exported theorem over `PaperConfig<A>` proves WAL trace admissibility and
agreement, acknowledged-prefix durability, existence of a Broker `Exec`, the
direct weak simulation and full projection agreement, T1 safety for the Broker
witness, and T1 safety for every mapped Broker prefix. T4-C0 deliberately
contains no program-context state, plugging semantics, or
`StorageParametricContext` proof. T4-C1 and T4-C2 discharge those additional
obligations in the completed full T4 theorem.

## T4-C1: context observation and plugging interface

`t4_context_interface.rs` imports only T4-C0 so every nested runtime type keeps
the same nominal identity. It defines a backend-independent `ContextEvent`
history for append Call/Return, cut-erased Invoke/Deliver, IgnoreStale,
RetryRelease, Crash, BeginRecover, and FinishRecover. `DiskFull` contributes a
two-event Call/Full-return delta; append linearization, torn writes, and WAL
scan/truncation actions contribute the empty delta.

The context also receives a masked runtime view. When append control is Idle it
sees `(mode,slot)`; while an append is Called or Linearized it sees only
`AppendPending(mode,record)`. This prevents the context from observing either
the hidden linearization phase or the slot update performed there. The complete
`ContextView` contains only the immutable request map, ordered normalized
history, and masked runtime state.

`ProgramContext<S>` is a pair of `ISet` relations. Its transitions receive the
masked pre- and post-step views and a nonempty normalized delta, never the raw
backend event, backend identity, concrete store, or proof ghosts.
`StorageParametricContext` requires a state at the exact fixed initial view,
rejects any other admitted initial view, and constrains both endpoint views to
the configured request map and every admitted delta to a valid nonempty one.

T4-C1 proves exact context-delta classification, ordered history extension,
recovery of `pi_append_io`, T3/T2 matched-event and whole-trace history
compatibility, projection-silent empty deltas, equal masked views under the T3,
T2, and composed representations, and identical initialized views for WAL,
Journal, and Broker. It defines structural `PluggedWalExecution<S>`,
`PluggedJournalExecution<S>`, and `PluggedBrokerExecution<S>` predicates, proves
their erasure to the existing closed `Exec` relations and their prefix closure,
and proves every accepted hidden backend step preserves the complete context
view while context state stutters. An accepting inert context, a shared
zero-step plugged execution, and a positive shared one-`Crash` execution
establish nonvacuity for both initialization and visible-step wiring.

T4-C1 alone does not compress context states along a weak map or construct a
target plugged execution. T4-C2 discharges those contextual-lifting
obligations. T4-C1 also does not assume protected-handle exclusivity, adapter
effect refinement, liveness, or executable Rust correctness.

## T4-C2: contextual replacement and composition

`t4_contextual_composition.rs` imports only T4-C1 and closes theorem T4 for
arbitrary finite plugged WAL executions. It defines a canonical plugged Journal
execution and a canonical plugged Broker execution. Their context-state sequence
is compressed exactly when T3's `translate_event` returns `Some`, rather than
when `context_delta` is nonempty. Thus every retained Journal/Broker step has
one synchronized context-state step, while every private WAL step remains in
one canonical map fiber and preserves the source context state.

The mechanization proves the compressed sequence has exactly one more state
than events, recovers the source context state at every compression-map point,
transfers every admitted context step through the canonical Journal execution,
and then lifts that plugged execution lockstep through T2. The resulting
canonical Broker construction satisfies `PluggedBrokerExec`. At every prefix
named by `canonical_composed_map`, both the shared context state and the complete
ordered endpoint `ContextView` are exactly equal between the WAL source and
Broker target.

The exported `t4_c2_contextual_replacement` theorem explicitly requires a
well-formed paper configuration, `StorageParametricContext`, and
`PluggedWalExec`. Its conclusion retains T4-C0's weak simulation, normalized
projection agreement, full-execution T1 safety, and mapped-prefix T1 safety in
addition to the plugged Broker construction and exact mapped state/view
equalities. This is canonical finite forward contextual replacement. It does
not establish reverse contextual equivalence, liveness, autonomous context
steps, protected-handle exclusivity, adapter-specific external-effect
refinement, or byte-level WAL/filesystem refinement.

## T5-S0: exact one-step committed-history laws

`t5_commit_step.rs` imports only T4-C2 and fixes the committed-history
abstraction separately for each theorem machine. `alpha_commit_broker` is the
Broker durable `commit_log`. `alpha_commit_journal` and `alpha_commit_wal` are
`Replay(JournalView).commit_log`; for the WAL, `JournalView` is exactly
`Parse(media)`.

The checkpoint proves an exact equation, not only prefix monotonicity. An
accepted Broker step appends one `CommitEntry` exactly when its event is
`BrokerLinearize(CommitRec)`. An accepted atomic-Journal step does so exactly
at `JournalAppendLinearize(CommitRec)`. An accepted WAL step does so exactly at
`WalWriteFull(CommitRec)` or `WalFinishTorn(CommitRec)`. Every other accepted
step preserves the corresponding committed history by equality. Prefix
monotonicity follows immediately from these exact equations.

The WAL theorem requires only the runtime `wal_invariant` at the pre-state; it
does not require the ghost-evidence agreement included in `basic_invariant`.
Reachable executions can derive this premise from T3-W0's `basic_invariant`.
The proof first establishes the stronger parsed-view equation: only
`WalWriteFull` and `WalFinishTorn` extend `JournalView`, while every other
accepted WAL step stutters. In particular, `WalWriteTorn` leaves the parsed
view unchanged and `TruncateTail` preserves it exactly. Replay projection then
yields the one-step committed-history law.

T5-S0 is only the local step layer. T5-E0 discharges arbitrary execution-
interval monotonicity, T5-R0 discharges equality from a `Crash` through the
first `FinishRecover`, and T5-C0 exports the result across T4's mapped
WAL-to-Broker prefixes.

## T5-E0: finite execution-interval monotonicity

`t5_commit_execution.rs` imports only T5-S0 and lifts its one-step prefix laws
by induction on the later configuration index. For each Broker, atomic-Journal,
and typed-WAL execution it proves:

```text
Exec(Cfg,execution)
and i <= j < execution.configs.len()
implies
  alpha_commit(execution.configs[i])
    <=p alpha_commit(execution.configs[j]).
```

The public premise is only the backend's exact `Exec` predicate together with
the index bounds. In particular, the WAL interval theorem does not expose
`wal_invariant` or `basic_invariant` as an additional premise. It invokes the
existing every-configuration reachability theorem internally, obtains
`basic_invariant`, projects the runtime `wal_invariant`, and applies T5-S0 at
each inductive step. A generic transitivity lemma composes the adjacent prefix
relations.

T5-E0 proves monotonic extension but not equality by itself. T5-R0 proves that
the interval from `Crash` through the first `FinishRecover` contains no Commit
append, and T5-C0 carries that equality through T4's canonical map.

## T5-R0: exact recovery-episode preservation

`t5_commit_recovery.rs` imports only T5-E0. Its backend-independent
`recovery_episode(events,crash,finish)` predicate requires
`crash < finish < events.len()`, `events[crash]=Crash`,
`events[finish]=FinishRecover`, and no `FinishRecover` strictly between those
indices. It does not assume that intermediate records are recovery repairs.

For Broker, atomic-Journal, and typed-WAL executions, the proof derives that
every pre-state after the selected Crash and through the endpoint is non-Online.
Any accepted durable linearization in such a state is therefore a conclusive
`FailRec` or a recovery `UnknownRec`; the corresponding commit delta is empty.
The exported step theorems establish, for every
`crash <= index <= finish`, both recovery-repair classification of any
linearization and exact `alpha_commit` stuttering. The endpoint theorems combine
T5-E0 prefix monotonicity with equal commit-log length:

```text
Exec(Cfg,execution)
and recovery_episode(execution.events,crash,finish)
implies
  alpha_commit(execution.configs[crash])
    == alpha_commit(execution.configs[finish + 1]).
```

The WAL endpoint theorem exposes only `Exec` and the episode predicate;
reachability supplies `basic_invariant` and the local runtime `wal_invariant`
internally. R0 is mechanically nonvacuous. It constructs the minimal traces
`Crash, BeginRecover, FinishRecover` for Broker and Journal; the WAL trace
`Crash, BeginScan, FinishScan, TruncateTail, BeginRecover, FinishRecover`; and
the repeated-Crash Broker trace
`Crash, BeginRecover, Crash, BeginRecover, FinishRecover`. Initial durable and
Journal recovery completeness makes each endpoint enabled.

R0 proves equality only for committed history. Repair records, the complete
Journal, WAL media, runtime state, and physical history may change. It is
conditional on a later first `FinishRecover`, makes no liveness claim, and does
not itself export the equality through T4's contextual mapping; T5-C0 supplies
that separate bridge.

## T5-C0: contextual mapped recovery preservation

`t5_commit_contextual.rs` imports only T5-R0. It first proves exact commit-delta
commutation through T3, source-qualified T2, and their composed T4 event
translation. For each weak-simulation step, an erased WAL step has an empty
commit delta, while a matched step has exactly the same WAL and Broker commit
delta. The representation relations then imply, for every source configuration
prefix `i`,

```text
alpha_commit_W(source.configs[i])
  == alpha_commit_B(target.configs[mu[i]]).
```

For a source WAL `recovery_episode(events,crash,finish)`, the mapped recovery
theorem proves all four endpoint equalities:

```text
alpha_W(configs[crash]) == alpha_W(configs[finish + 1])
alpha_W(configs[crash]) == alpha_B(target.configs[mu[crash]])
alpha_W(configs[finish + 1])
  == alpha_B(target.configs[mu[finish + 1]])
alpha_B(target.configs[mu[crash]])
  == alpha_B(target.configs[mu[finish + 1]]).
```

The exported `t5_c0_contextual_recovery_preservation` theorem retains exactly
T4-C2's paper-configuration well-formedness, storage-parametric context, and
plugged WAL execution premises, together with the source `RecoveryEpisode`
premise. Its conclusion contains the complete T4-C2 contextual replacement
statement, all-prefix mapped committed-history equality, and mapped endpoint
equality for the canonical plugged Broker target.

The checkpoint is nonvacuous as a combined theorem. A six-event WAL execution
`Crash, BeginScan, FinishScan, TruncateTail, BeginRecover, FinishRecover` with
seven identical inert context states satisfies storage parametricity, plugging,
and `RecoveryEpisode(0,5)`, and the proof explicitly instantiates the final
contextual theorem. T5-C0 does not transport `RecoveryEpisode` to the Broker
trace: private WAL fibers can be erased, and the target endpoints are
`mu[crash]` and `mu[finish + 1]`. It also makes no liveness, full-state,
external-effect, byte-level WAL, or filesystem claim.

## H1: cumulative artifact nonvacuity

`h1_artifact_nonvacuity.rs` imports only T5-C0. It defines a concrete total
`FullConfig`: every request is uncontrolled, has no stable key, and permits one
attempt; every capability admits all resources and arguments with unit budget;
and all request-result pairs are valid. The proof establishes
`full_config_wf` directly. In particular, deduplicated-key injectivity is
vacuous because no request is classified as deduplicated; it is not introduced
as an assumption.

The exported `h1_artifact_nonvacuity` theorem instantiates that configuration
with T4's inert context and T5-C0's six-event minimal contextual recovery
execution. It exhibits concrete witnesses with `crash == 0` and `finish == 5`
for which all T5-C0 premises and the complete T5-C0 conclusion hold together.
H1 therefore establishes inhabitation of the cumulative T1--T5 artifact, not
external-effect refinement, a realistic adapter configuration, liveness, or
byte-level implementation correctness. Those remain outside H1.

## T6-D0: terminal and adapter definition freeze

`t6_terminal_definitions.rs` imports T5-C0 directly; H1's concrete witness is
not a semantic dependency. The checkpoint defines `ExternalRun<X,I>`, the
first-class adapter interpretation, request-local `AdapterRelyTrace`, the
request-free `TerminalOutcome`, the total unique `delivery` selector, and the
duplicate-rejecting `terminal_record` selector, whose successful result is a
one-based `IndexedTerminalRecord`. Duplicate deliveries or terminal records
produce `None` rather than selecting arbitrary evidence.

The definition surface gives Commit, Fail, and Unknown separate
`OutcomeEvidence` and `BrokerOutcomeCompatible` branches. The evidence
predicate takes `FullConfig` explicitly because Unknown validates the exact
configuration-dependent `StructuralEnabled` rule. `AdapterVerified` is a
derived universal predicate over legal Journals, adapter relies, outcome
evidence, and compatibility; it is not a field supplied by an adapter. The
later concrete-adapter theorem must establish that predicate uniformly for
every compatible well-formed `PaperConfig`, while an end-to-end instance uses
it at one selected configuration. The
effect and result relations receive one `ExternalRun`, so their pre/post states
cannot disagree with independently repeated arguments.

T6-D0 also freezes one broker-state core statement and separate atomic-Journal
and typed-WAL wrapper statements over the existing T2 and T4-C0 representation
relations. Its proofs cover empty, singleton, and duplicate terminal selection;
concrete unique and duplicate delivery cases; exhaustive Commit/Fail/Unknown
unfolding; exact decomposition of the replay-layer Unknown rule into reason and
anchor predicates; projection of `AdapterRely`; and elimination of
`AdapterVerified`. It does not
prove `OutcomeEvidence`, compatibility, or external-effect refinement for an
arbitrary terminal execution; the subsequent T6-E0 checkpoint supplies the
evidence proof without retroactively strengthening T6-D0.

## T6-E0: generic terminal evidence

`t6_terminal_evidence.rs` imports T6-D0 directly. Its adapter-independent
full-history theorem proves

```text
JournalLegal(erase_config(cfg), records)
and PhysicalUnique(history)
and DurableOutcomesFollowDeliveries(records, history)
and terminal_from_records(records, request) == Some(outcome)
implies OutcomeEvidence(cfg, records, request, history, outcome).
```

The exported event theorem then obtains these premises from the Broker contract
invariant and proves

```text
BrokerInvariant(cfg, broker)
and broker.core.evidence.records == pi_journal(events)
and broker.physical.physical == pi_physical(events)
and terminal(events, request) == Some(outcome)
implies OutcomeEvidence(
  cfg, broker.core.evidence.records,
  request, pi_adapter(events, request), outcome).
```

The proof establishes soundness of the duplicate-rejecting terminal selector,
exact reconstruction of referenced Outcome records, prefix preservation of
durable Outcome-to-delivery causality, the per-attempt delivery-count bound
implied by physical uniqueness, unique latest-delivery selection, and exact
preservation of delivery counts and observations by the request-local adapter
projection. Thus Commit and Fail terminal records resolve an exact Outcome in
their strict prefix and select the unique corresponding physical delivery.
Unknown obtains the exact prefix `StructuralEnabled` rule and reason-specific
durable anchor from Journal legality; it makes no claim that unpersisted
physical outcomes are absent.

T6-E0 verifies 817 cumulative obligations with zero errors, adding 18 over its
T6-D0 parent. Both the focused source check and the retained 38-target run pass;
the retained report records 17,390 summed target obligations and 857
dependency-aware non-duplicated obligations.
The result does not use an `ExternalRun`, `AdapterRely`, or adapter effect
relation, and it does not prove `BrokerOutcomeCompatible`, `Refines`, an
`AdapterVerified` instance, T6-S0, either Journal/WAL wrapper, or external-effect
refinement. T6-C0 subsequently supplies compatibility without retroactively
strengthening T6-E0, and T6-S0 combines the results and discharges the backend
wrappers.

## T6-C0: terminal compatibility

`t6_terminal_compatibility.rs` imports T6-E0 directly and proves the
compatibility half of the frozen terminal bridge:

```text
PaperConfigWf(paper)
and BrokerInvariant(paper_broker_config(paper), broker)
and broker.records == pi_journal(events)
and broker.physical == pi_physical(events)
and AdapterRely(paper, events, request, run)
and terminal(events, request) == Some(outcome)
implies BrokerOutcomeCompatible(
  paper_broker_config(paper), broker.records, request,
  pi_adapter(events, request), outcome).
```

The proof consumes T6-E0's exact terminal evidence and closes every frozen
compatibility branch. Request-local projection preserves per-attempt and
aggregate invocation counts, and a selected ordered delivery establishes that
its attempt was invoked. The Broker retry bound therefore gives Uncontrolled
Unknown at most one invocation, while an exact Commit or Fail delivery makes
that invocation unique. For an Idempotent Fail, terminal replay provenance
establishes `all_attempts_failed`; acknowledged invocation refinement then
places every invoked attempt in the durable attempt range, and durable
Outcome-to-delivery causality selects its Failure delivery. For a Deduplicated
Fail, the adapter's pairwise observation-consistency rely excludes any Success
or InvalidResult delivery. For Unknown, exact T6-E0 evidence plus Journal
legality recovers the reason guard and durable cause required by
`unknown_cause`.

T6-C0 verifies 834 cumulative obligations with zero errors, adding 17 over its
T6-E0 parent. The retained 39-target run passes and records 18,224 summed target
obligations and 874 dependency-aware non-duplicated obligations. Historical
T6-E0 remains 817 cumulative obligations, 38 targets, 17,390 summed target
obligations, and 857 dependency-aware non-duplicated obligations.

This checkpoint proves no adapter effect relation, `Refines`, or
`AdapterVerified` instance. It also does not state the combined T6-S0 theorem
or discharge either the atomic-Journal or typed-WAL wrapper. T6-S0 subsequently
combines the completed E0 and C0 halves and proves those backend wrappers. H1's
concrete witness is inert and does not inhabit this terminal `AdapterRely`
antecedent, so the compatibility result remains conditional; a concrete
terminal adapter/run witness belongs to the later adapter checkpoint.

## T6-S0: terminal bridge composition

`t6_terminal_bridge.rs` imports T6-C0 directly and completes the frozen
terminal bridge. Its generic event theorem invokes T6-E0 and T6-C0 under their
shared Broker invariant, exact Journal/physical projection, `AdapterRely`, and
unique-terminal premises, proving the conjunction

```text
OutcomeEvidence(cfg, records, request, pi_adapter(events, request), outcome)
and BrokerOutcomeCompatible(
  cfg, records, request, pi_adapter(events, request), outcome).
```

The exported `t6_s0_core` theorem proves the implication fixed in T6-D0. The
atomic-Journal wrapper takes the final trace-agreement prefix, uses the T2
representation to equate the Broker ghost Journal and physical histories with
the final runtime evidence, and transports the core conjunction to the frozen
`journal_t6_s0_statement`. The typed-WAL wrapper follows the same argument using
WAL trace agreement and T4-C0's composed WAL-to-Broker representation, whose
Journal projection carries the same evidence, to prove the frozen
`wal_t6_s0_statement`.

T6-S0 verifies 840 cumulative obligations with zero errors, adding 6 over its
T6-C0 parent. The retained 40-target run passes and records 19,064 summed target
obligations and 880 dependency-aware non-duplicated obligations.

This is a conditional composition and backend-transport result. It defines no
adapter-specific external effect, proves no `Refines` relation or
`AdapterVerified` instance, and supplies no concrete terminal adapter/run
witness or caller-visible `ReturnResult` property. In particular, H1's inert
recovery witness does not inhabit the terminal `AdapterRely` antecedent. Those
obligations belong to the subsequent adapter checkpoint.

## T6-A0: concrete adapter semantic closure

`t6_adapter_semantic_closure.rs` imports only T6-S0. Its generic closure lemmas
show that `AdapterVerified`, Journal legality, `AdapterRely`, and T6-S0's frozen
`TerminalEvidenceAndCompatibility` conclusion entail `Refines`. Event,
atomic-Journal, and typed-WAL wrappers select the terminal outcome and derive
`PerRequestEffectRefinement`; the outcome-free wrappers case-split on whether a
terminal exists.

The concrete `EnsureMember` instance uses an external set of resources. For a
request `r`, its target is the resource named by `r.id`; the interference
baseline is the pre-state union the environment's additions. Zero effect is
exactly that baseline and one effect additionally contains the target. The rely
forbids environment insertion of the target, requires every witness-marked
linearized attempt to have been invoked, and selects the one-effect relation
when that set is nonempty and the zero-effect relation otherwise. A successful
value with id 1 marks its
attempt as linearized, while Failure marks it as non-linearized. All requests
are Idempotent with at most two attempts. The proof establishes
`AdapterVerified` for this fixed well-formed paper configuration, proves that
one effect differs from zero on a concrete run, and proves retry collapse for a
crash-erased Invoke/Success/Invoke/Failure adapter history.

The nonvacuity theorem is not an inert trace. It constructs a 20-event,
21-configuration typed-WAL execution containing six acknowledged records
(`Authorize`, `Prepare`, `Arm`, `Start`, `Outcome`, and `Commit`), one physical
Invoke, and one delivered Success. The exact terminal Commit, final
representation, adapter history, external run, and one-effect/not-zero result
are exported by a premise-free existential package.

T6-A0 verifies 864 cumulative obligations with zero errors, adding 23 over the
current 841-obligation T6-S0 closure. The retained 41-target run records 19,951
summed target obligations and 904 dependency-aware non-duplicated obligations.
T6-S0's originally retained checkpoint remains 840 cumulative obligations over
40 targets and 880 non-duplicated obligations; the current closure is one larger
because T6-A0 adds a conservative definitional `PaperConfig` accessor lemma in
the shared T1 layer.

The result verifies a semantic adapter contract, not executable adapter code or
the external service. The mixed retry example is not a realizable Broker/WAL
crash trace. The checkpoint also does not establish byte/fsync persistence,
`CompleteMediation` or protected-handle exclusivity, `ReturnResult`,
multi-request/global linearizability, or liveness. Its full-capability
configuration is a consistency witness rather than a least-privilege design.

## Reproducible verification

The toolchain is locked in `toolchain.lock.json`:

- Verus `0.2026.07.05.49b8806`, Windows x86-64 release archive, SHA256
  `c45489d535f85de6d6f3204a70462ba437fbf98875361d84ff5213d89e3d8130`;
- rustup `1.29.0`, Windows MSVC archive, SHA256
  `86478e53f769379d7f0ebfa7c9aa97cb76ca92233f79aa2cc0dbee2efaac73c7`;
- Rust `1.96.0-x86_64-pc-windows-msvc`, matching the Verus release metadata.

Run from the repository root:

```powershell
.\mechanized\verify.ps1
```

By default the run atomically writes the machine-readable evidence file
`mechanized/results/verification-report.json`. `-ReportPath <path>` selects a
different JSON destination, while `-NoReport` retains console-only operation.
The report records run and per-target status/timestamps, the normative schema
SHA256, every registered source SHA256, the verifier-driver and toolchain-lock
SHA256 values, source-snapshot metadata, declared and observed toolchain
metadata, target totals, contribution parents and deltas, and the running non-
duplicated total.

The verifier downloads hash-pinned Verus and rustup artifacts, reconstructs and
tree-hashes the complete Verus executable tree from its checked archive, and
installs the exact Rust
version into fresh per-run `CARGO_HOME` and `RUSTUP_HOME` directories from the
official rustup distribution endpoints. It records and rechecks a deterministic
tree hash of that installation, restores the caller's environment, serializes
shared-download access, and rejects unsupported platforms. The Rust tree hash
is observed evidence; the Rust component tree is not independently pre-hashed
in `toolchain.lock.json`. The driver queries the rustup executable with no
selected toolchain, then performs the pinned toolchain installation explicitly;
the version query therefore cannot populate the fresh Rust home implicitly.

Before verification, every registered `.rs` file is copied into an exact flat,
read-only per-run snapshot. Verus is invoked only on snapshot paths. The runner
checks exact snapshot membership, source hashes, and read-only attributes before
and after every target, while separately confirming the live registered sources,
driver, lock, and report schema remain unchanged. It accepts only the repository's
simple one-line `#[path = "file.rs"]` plus immediate `mod` grammar, rejects
implicit or include-based module loading, requires every direct import to resolve
to a registered source, and validates that each delta-counted cumulative target
imports exactly its declared immediate predecessor.

The lexical proof policy rejects `assume`, `admit`, axioms, external proof-body
mechanisms, `get_Some`, `recommends`, and verifier resource-limit or spinoff
constructs. All target-specific extra verifier arguments are rejected. Every
target is invoked exactly with `--crate-type lib --no-cheating`; the driver
checks target/source counts, parent-delta arithmetic, running totals, and final
summary consistency before assigning `status: "passed"`.

The current result is:

```text
M0 verified obligations: 21
R1 verified obligations: 86
B1 verified obligations: 39
C1 verified obligations: 128
D1 verified obligations: 144
Q1 verified obligations: 144
B2-R verified obligations: 169
B2-C verified obligations: 175
B2-P0 verified obligations: 193
B2-P1 verified obligations: 251
B2-P2 verified obligations: 276
B2-P3 verified obligations: 292
B2-L verified obligations: 310
B2-A verified obligations: 335
G0 verified obligations: 342
G1-P verified obligations: 410
G1-E verified obligations: 429
T1 verified obligations: 462
T2-J0 verified obligations: 476
T2-J1 verified obligations: 487
T2-E verified obligations: 509
T2-R verified obligations: 521
T2 verified obligations: 532
T3-W0 verified obligations: 578
T3-W1-T verified obligations: 589
T3-W1-E verified obligations: 627
T3-W1-R verified obligations: 642
T3 verified obligations: 660
T4-C0 verified obligations: 677
T4-C1 verified obligations: 721
T4-C2 verified obligations: 735
T5-S0 verified obligations: 744
T5-E0 verified obligations: 748
T5-R0 verified obligations: 770
T5-C0 verified obligations: 784
H1 verified obligations: 787
T6-D0 verified obligations: 800
T6-E0 verified obligations: 818
T6-C0 verified obligations: 835
T6-S0 verified obligations: 841
T6-A0 verified obligations: 864
Non-duplicated verified artifact obligations: 904
```

C1's 128 obligations include the 86 R1 and 39 B1 obligations imported into the
composition crate, plus 3 composition-specific obligations. D1 and Q1 each
include that same C1 closure plus 16 new obligations. B2-R includes Q1 and adds
25 record-side Broker obligations. B2-C includes B2-R and adds 6 rich
configuration-refinement obligations. B2-P0 includes B2-C and adds 18 physical
transition/projection obligations. B2-P1 includes P0 and adds 58
physical-causality, live-source, and all-prefix obligations. B2-P2 includes P1
and adds 25 retry, acknowledged-authorization, Outcome-provenance, and
all-prefix obligations. B2-P3 includes P2 and adds 16 terminal-source,
recovery-repair, derived Failure/Unknown provenance, and all-prefix
obligations. B2-L adds 18 exact-contract obligations; B2-A adds 25 append-bridge
and crash-free-epoch obligations; G0 adds 7 global-event closure obligations;
G1-P adds 68 global-projection obligations; G1-E adds 19 relational-execution
obligations; T1 adds 33 paper-theorem and configuration-accessor obligations;
T2-J0 adds 14 independent
runtime obligations; T2-J1 adds 11 trace obligations; T2-E adds 22 event and
projection obligations; T2-R adds 12 exact-representation obligations; and T2
adds 11 step/execution simulation obligations. T3-W0 adds 46 typed-frame parser,
runtime-boundary, transition, invariant, monotonicity, and execution-closure
obligations. T3-W1-T adds 11 WAL trace obligations; T3-W1-E adds 38 event
compression, closure, silence, and projection obligations; T3-W1-R adds 15
representation and step-commutation obligations; and T3 adds 18 compressed-
execution, weak-index, per-prefix, durability, and exported-theorem obligations.
T4-C0 adds 17 closed-composition obligations for generic index-map composition,
lockstep preservation through T2, direct event/representation/projection
composition, mapped-prefix T1 safety, and the exported closed theorem.
T4-C1 adds 44 context-interface obligations for normalized ordered
observations, append-I/O recovery, masked endpoint-view preservation,
translation and representation compatibility, nonvacuous relational contexts,
three structural plugged executions, erasure, prefix closure, and shared
zero-step and visible-step witnesses. T4-C2 adds 14 contextual-composition
obligations for T3-selected context compression, canonical plugged Journal and
Broker construction, context-step transfer, and exact mapped context-state and
ordered endpoint-view equality. T5-S0 adds 9 one-step committed-history
obligations for the exact Broker, Journal, and WAL delta equations, parsed WAL
view behavior, and their prefix-monotonicity corollaries. T5-E0 adds 4
execution-level obligations for generic prefix transitivity and Broker,
Journal, and WAL interval monotonicity. T5-R0 adds 22 obligations: 5 for initial
recovery completeness and inhabited minimal/repeated-Crash episodes, 2 generic
record/sequence lemmas, and three each for mode confinement, non-Online commit
stuttering, episode-prefix invariants, per-episode-step stuttering, and endpoint
equality across the Broker, Journal, and WAL. T5-C0 adds 14 obligations: 13 for
event-delta translation, matched-or-erased step correspondence,
representation-to-commit-history bridges, all-prefix mapped equality, mapped
recovery endpoints, and contextual export; plus 1 combined inert-context
recovery witness that instantiates the final theorem. H1 adds 3 obligations for
the concrete total configuration, the concrete T5-C0 premise/conclusion
package, and the final existential artifact-nonvacuity theorem. T6-D0 imports
T5-C0 directly and adds 16 definition-boundary obligations for the three
evidence branches, three compatibility branches, empty/singleton/duplicate
terminal selection, unique/duplicate delivery cases, exact Unknown-rule
decomposition, and adapter-rely and adapter-verification unfolding.
T6-E0 imports T6-D0 directly and adds 18 terminal-evidence obligations for
terminal-selector soundness, exact Outcome projection, durable-causality prefix
closure, physical-delivery uniqueness and selection, request-local projection
preservation, Commit/Fail/Unknown evidence, and the generic history/event
exports.
T6-C0 imports T6-E0 directly and adds 17 compatibility obligations for
request-local invocation-count preservation, selected-delivery invocation
ancestry, acknowledged-invocation witnesses and durable ranges, Idempotent
all-invocations-failed closure, Deduplicated conflicting-observation exclusion,
Uncontrolled invocation bounds, Unknown-cause reconstruction, and the generic
event/core compatibility exports.
T6-S0 imports T6-C0 directly and adds 6 composition and backend-transport
obligations: the generic conjunction and frozen core statement, plus the
requires-style and implication-style atomic-Journal and typed-WAL wrappers.
T6-A0 imports T6-S0 directly and adds 23 obligations for generic refinement
closure, the concrete `EnsureMember` adapter laws and `AdapterVerified` instance,
the typed-WAL execution/rely witness, exact terminal package, and premise-free
semantic nonvacuity theorem.
The non-duplicated total therefore
counts M0, C1, each independent D1/Q1 delta, the B2-R delta over Q1, and the
B2-C through T5-C0 deltas along their dependency chain, plus the independent H1
and T6-D0 deltas over T5-C0, the T6-E0 delta over T6-D0, the T6-C0 delta over
T6-E0, the T6-S0 delta over T6-C0, and the T6-A0 delta over T6-S0. The registry
now contains 41 Verus targets and 904 non-duplicated obligations; the retained
run sums 19,951 target obligations. The historical retained T6-S0 checkpoint
had 40 targets, 880 non-duplicated obligations, and a 19,064 target sum before
the conservative definitional T1 accessor lemma was added.

The next adapter checkpoint should refine executable adapter and external-
service protocol steps to the T6-A0 semantic contract and construct a realizable
crash/retry execution. After that, complete mediation and protected-handle
exclusivity can connect this adapter instance to the full conditional T6 theorem.
