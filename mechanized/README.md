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
nonempty typed-WAL terminal witness. T6-A1 refines an explicit operational
adapter/service protocol to that semantic contract, derives `AdapterRely` from
the protocol execution, and supplies an exact crash/recovery/retry execution
whose terminal Unknown coexists with one abstract external effect. T6-M0 adds a
first-class protected-service execution and a closed-interface audit context,
derives `CompleteMediation` from their generated traces, and connects each
target action to T1 durable authorization ancestry. T6-P0 adds a conditional
weak-index product over the A1, protected-service, and typed-WAL executions,
derives trace/history, mediation, and effect-state agreement at every related
prefix, and proves prefix closure. T6-X0 composes that index with T4-C2's
canonical WAL-to-Broker index, lifts the product through a supplied
storage-parametric plugged execution, and proves the conditional terminal
end-to-end theorem for the operational `EnsureMember` instance. T6-RO0 adds a
second executable adapter instance, for the ReadOnly retry class: it samples
an environment-owned Boolean at an explicit environment-history cut, derives
`AdapterRely` from its transition invariant, and proves a premise-free
crash/retry witness whose conclusive `Fail` terminal makes the `zero_effect`
branch of `Refines` operationally non-vacuous. T6-DD0 begins a third,
Deduplicated instance by defining its memoized keyed-decision semantics,
well-formed fixed configuration, and transition system. T6-DD1 proves its
inductive invariant, finite-execution `AdapterRely` derivation, and
`AdapterVerified`. T6-DD2 supplies the premise-free coupled terminal witness:
attempt 1 silently applies and memoizes the keyed effect, a crash occurs before
any delivery, and attempt 2 receives that memoized Success and commits it.
T6-DD3 adds the matching independent protected-service execution, exact adapter/
service event coupling, one keyed decision, memoized retry return, complete
mediation, and durable authorization ancestry under the closed M0 context.
T6-DD4 proves the all-prefix adapter/protected/WAL product, composes its weak
index with T4-C2's contextual Broker replacement, and closes source/target
terminal refinement and mediation for the distinguished DD2 execution.
T6-DD5 adds the request-indexed operational/protected family theorem. A family
member is required for every request terminal in a shared WAL; DD1 derives its
request-local rely, DD4 derives its all-prefix product, and X0 transports its
source terminal to the canonical Broker. The DD2 family discharges coverage
without premises.
In a separate implementation-refinement track, K1, K2, K3, K4-C0, K4-R0,
K4-R1, K4-R2, and K4-R3 connect concrete
`u64`/vector
durable-summary and Journal code to Q1, R1, and B1: K1 verifies Authorize and
Start, K2-G0 completes all nine reference-erased record guards, K2-T0 couples
accepted-record mutations exactly to `apply_record` and legal-prefix
`replay_push`, and K3-A0 adds exact `u64` references plus a serialized concrete
append loop whose successful traces project exactly to B1. K4-C0 maps M4's
finite admission-manifest shape into a total well-formed formal configuration.
K4-R0 uses that finite configuration in the first parameterized executable
Authorize guard, K4-R1 adds parameterized Prepare and Start guards, and K4-R2
adds the parameterized accepted Authorize durable mutation. K4-R3 adds the
accepted Prepare phase mutation.
T4, T5,
the T6 terminal bridge, semantic adapter closure, executable adapter
refinement, model-level mediation/no-bypass, prefix product, the X0
single-request contextual theorem,
the RO0 read-only operational instance, the DD2 Deduplicated coupled witness,
and the K3-A0 concrete append layer are complete. Production deployment
isolation, caller-visible return refinement,
concurrency, crash/recovery in the concrete kernel, and generalization to
arbitrary adapters and all requests remain open.

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

## K1/K2/K3: executable durable-summary and append refinement

`k1_executable_kernel.rs` imports Q1 and replaces its unbounded durable maps
with an executable `KDurable` summary backed by vectors of `u64` request and
capability entries. For a fixed demo configuration whose request IDs select
ReadOnly, Idempotent, Deduplicated, and Uncontrolled lanes, K1 verifies the
empty initial coupling, total vector lookup, conclusive-failure scanning, and
the Authorize and Start guards. Each guard's postcondition is equality with
Q1's reference-erased `abstract_record_enabled`, not merely a one-way safety
implication. K1 verifies 159 cumulative obligations with zero errors, adding
15 over Q1.

`k2_executable_kernel_refinement.rs` adds executable Revoke, Prepare, Arm,
Outcome, Commit, Fail, and Unknown decisions. Together with K1, K2-G0 covers
all nine record forms in `abstract_record_enabled`, including retry-class,
latest-attempt, uncertainty, terminal, digest, and stable-key branches. K2-G0
is guard-only: it verifies 179 cumulative obligations with zero errors, adding
20 over K1, but does not mutate `KDurable`.

`k2_durable_record_kernel.rs` adds the mutation side. Its strengthened coupling
excludes outcomes beyond the recorded started-attempt prefix. Verified helpers
insert fresh request/capability entries and update authorization, revocation,
Start and Outcome data, plus the Prepare, Arm, Commit, Fail, and Unknown phases.
Accepted-record wrappers cover all nine record forms. Their postconditions are
exact `replay_layer::apply_record` coupling, and the legal-extension lemma lifts
that coupling through `replay_push`. K2-T0 verifies 208 cumulative obligations
with zero errors, adding 29 over K2-G0.

`k3_append_linearization_kernel.rs` imports K2-T0 and adds an executable
nine-form `KJournalRecord` whose identifiers, attempts, and exact record
references are represented by `u64`. A shared reverse scanner searches the
concrete Journal itself for Authorize, Prepare, Arm, Start, and Outcome evidence
and proves that each result is the corresponding one-based replay LSN. The
executable exact-reference checker also covers every Unknown evidence branch.
Combining that checker with the K2 semantic guard is proved equivalent to R1
`StructuralEnabled` for every legal concrete Journal.

K3-A0 stores the concrete durable summary, Journal, acknowledgment cuts, and a
serialized Idle/Called/Linearized control. An enabled Call stores the exact
record without changing durable or Journal state; Linearize accepts only that
called record, applies the record's exact durable transition, pushes it exactly
once, and returns the one-based LSN `old Journal length + 1`; Return records the
exact current Journal cut and resets control to Idle without changing the durable
summary or Journal. A structurally invalid Call while Idle, a mismatched or
non-Called Linearize, and a Return outside Linearized leave the complete state
unchanged. The replay-push coupling proves the post-linearization durable
summary equals replay of the extended Journal. Over concrete successful traces,
the executable append history, Journal, and acknowledgment cuts agree exactly
with B1 `pi_append`, `pi_journal`, and `pi_ack`. K3-A0 verifies 248 cumulative
obligations with zero errors, adding 40 over K2-T0.

## K4-C0: finite admission-manifest configuration refinement

`k4_manifest_config_refinement.rs` imports K3-A0 and defines executable vectors
of capability budgets and immutable request bindings. A total specification
view supplies R1's capability, class, digest, key, namespace, attempt-limit,
scope-match, and valid-result components. Absent requests default to a
ReadOnly/no-key/one-attempt profile, preserving totality without admitting a
manifest request.

`k_manifest_wf` requires nonzero unique capability and request identifiers,
known binding capabilities, exact retry-class/key shape, and unique
Deduplicated keys in the namespace-zero M4 profile. Attempt limits are derived
from the retry class rather than trusted as a separate field. The generic
`k_manifest_config_is_well_formed` theorem proves R1 `config_wf`; the executable
one-request Idempotent manifest inhabits the complete premise and conclusion.
K4-C0 verifies 255 cumulative obligations, adding 7 beyond K3-A0.

## K4-R0: parameterized manifest Authorize guard

`k4_parameterized_authorize.rs` imports K4-C0 and implements linear executable
lookups over the finite capability and request vectors. Soundness, completeness,
and uniqueness lemmas connect those searches to K4-C0's total `Config` view.
`k_manifest_authorize_enabled` consumes the real manifest plus the existing
concrete durable summary and proves its Boolean decision equals Q1's
`abstract_record_enabled` Authorize branch for every well-formed manifest.

The premise-free witness constructs the M4/K3 Idempotent profile, the initial
concrete durable state, and an accepted `Authorize(1, 1, 1)` decision. K4-R0
verifies 266 cumulative obligations, adding 11 beyond K4-C0.

## K4-R1: parameterized Prepare and Start guards

`k4_parameterized_prepare_start.rs` imports K4-R0 and implements executable
manifest decisions for immutable digest/key fields, retry class, expected
capability, and class-derived attempt profiles. The generic Prepare guard proves
phase, class, field, and authorization-witness equality to Q1. The generic
Start guard additionally reuses K1's configuration-generic conclusive-failure
scan and proves next-attempt, retry-limit, and Uncontrolled freshness equality.

The premise-free profile witness validates the M4/K3 Idempotent digest, class,
and three-attempt profile. K4-R1 verifies 274 cumulative obligations, adding 8
beyond K4-R0.

## K4-R2: parameterized Authorize mutation

`k4_parameterized_authorize_mutation.rs` imports K4-R1 and wraps K2's
configuration-generic Authorize delta lemma with the finite manifest `Config`
view. For every well-formed manifest and coupled materialized state, an accepted
Authorize mutation sets the request phase and capability witness, decrements
the matching budget, and refines exactly to R1 `apply_record`.

The premise-free Idempotent witness materializes request and capability entries
from the empty K1 state, accepts `Authorize(1, 1, 1)`, observes budget `4 -> 3`
and witness `1`, and preserves the generic update invariant. K4-R2 verifies 276
cumulative obligations, adding 2 beyond K4-R1.

## K4-R3: parameterized Prepare mutation

`k4_parameterized_prepare_mutation.rs` imports K4-R2 and wraps K2's generic
phase-record delta with the finite manifest `Config` view. For every
well-formed manifest and coupled materialized state, an accepted Prepare
mutation changes exactly the request phase to `Prepared` and refines to R1
`apply_record` without changing budget, witness, outcomes, or capabilities.

The premise-free Idempotent witness chains the K4-R2 Authorize mutation to the
K4-R1 Prepare guard and the new mutation, observing `Prepared`, budget 3, and
capability witness 1. K4-R3 verifies 278 cumulative obligations, adding 2
beyond K4-R2.

`kernel/kernel_core.rs` re-exports K4-R3 as the latest checked layer. K4-R3 is
not yet a parameterized append kernel: the remaining K1-K3 guards and durable
mutations, generic materialization, and append state still use the fixed demo
configuration. Parameterizing the Start attempt-log mutation is the next
implementation-refinement checkpoint.
K3-A0 is
not a complete executable Broker: it retains the fixed demo configuration and
a serialized successful append path. DiskFull, crash/recovery, concurrent
callers, executor slots, physical Invoke/Deliver, caller-visible Broker results,
byte/fsync persistence, transport, MCP integration, and production deployment
remain later milestones.

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
effect/refinement and concrete-witness obligations are subsequently discharged
for `EnsureMember` by T6-A0, and T6-A1 derives the rely from an operational
adapter/service execution. Caller-visible `ReturnResult` remains open.

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

## T6-A1: executable adapter refinement

`t6_adapter_executable_refinement.rs` imports only T6-A0 and gives the
`EnsureMember` instance an explicit small-step adapter/service protocol. Its
state records the online, crashed, or recovering mode; the active attempt;
observed global and physical histories; service linearizations; environment
additions; and the resulting external membership set. Protocol events separate
observable global events from silent service linearization and environment
interference. Enabledness requires canonical positive and unique invocations,
responses after their invocations, Success only after service linearization,
Failure only before service linearization, no linearization after Failure,
well-bracketed crash/recovery transitions, and non-target environment additions.
Service linearization is guarded by a previously invoked, still-undelivered,
not-yet-linearized, nonfailed remote attempt; it deliberately does not require
the local adapter to remain Online or active, because an already-sent remote
request may take effect after a local crash.
`a1_service_linearize_step_has_remote_provenance` exports this guard as a
checked causal theorem and proves that the silent step inserts the target while
leaving observed global and physical history unchanged.

The inductive machine invariant establishes exact global/physical projection,
request locality, invocation uniqueness and ordering, observation
classification, exact zero-or-one-effect membership, and linearization
provenance. Finite-execution induction then proves
`ensure_member_exec_derives_adapter_rely`: `AdapterRely` is derived from the
operational transition system rather than assumed as an enabledness premise.
The generic `ensure_member_executable_wal_terminal_refines` theorem composes an
executable adapter execution, exact full-global-trace coupling, a typed-WAL
execution, and its selected terminal outcome to derive `AdapterRely`, `Refines`,
and `PerRequestEffectRefinement`.

The concrete witness contains 32 adapter events, including one silent
`ServiceLinearize(1)`, whose projection is exactly 31 global events. The coupled
typed-WAL execution has exactly 32 configurations and seven acknowledged
records: `Authorize`, `Prepare`, `Arm`, `Start(1)`, `Start(2)`,
`Outcome(2, Failure)`, and `Unknown(2, NonConclusiveFailure)`. Operationally it
executes `Invoke(1)`, `Success(1)`, Crash, recovery, `Invoke(2)`, and
`Failure(2)`. Attempt 1 linearizes and inserts the target, but its Success is not
journaled before the crash; attempt 2 becomes current after recovery and fails
without linearizing. The selected terminal is therefore
`UnknownOutcome { attempt: Some(2), reason: NonConclusiveFailure }`, while the
external run satisfies the one-effect relation and not the zero-effect relation.
The proof also establishes that no `Fail` terminal can be selected: the
Idempotent failure branch requires every invocation to have failed, which the
delivered Success for attempt 1 contradicts. The exported premise-free package
and `t6_a1_executable_crash_retry_nonvacuity` theorem jointly expose the exact
operational execution, terminal selection, derived rely, semantic refinement,
single abstract effect, and Fail impossibility.

`a1_retry_has_explicit_crash_recovery_shape` separately proves the exact
31-event ordering of Crash, scan/truncation, recovery, the three-step durable
`Start(2)` append, `Invoke(2)`, and `Failure(2)`. Thus the advertised recovery
sequence is fixed directly, not only through projections that erase control
events.

T6-A1 verifies 916 cumulative obligations with zero errors, adding 52 over its
T6-A0 parent. The historical retained T6-A1 42-target run records 20,867 summed
target obligations and 956 dependency-aware non-duplicated obligations.

This is an executable operational protocol model, not production Rust adapter,
network, operating-system, or external-service code. Persistence remains at the
typed-record abstraction and does not model byte layout or fsync behavior. The
checkpoint does not prove complete mediation or protected-handle exclusivity,
does not connect a terminal outcome to caller-visible `ReturnResult`, and does
not address multi-request concurrency, global linearizability, or liveness. The
generic A1 theorem assumes exact equality of the complete observed adapter and
typed-WAL traces; it does not yet provide a prefix-indexed stuttering simulation
or combined adapter/WAL state invariant.

## T6-M0: mediation and protected-handle exclusivity

`t6_mediation_exclusivity.rs` imports only T6-A1 and makes the protected
deployment boundary operational. `M0ProtectedExecution` is a separately defined
service transition system. Each `M0ProtectedCall` stores its request, attempt,
call descriptor, Journal and acknowledgment cuts, and source-event index;
eventwise coupling proves those fields equal the canonical A1/WAL Invoke. Its
event alphabet contains `BrokerInvoke`, call-indexed
`ServiceLinearize` and `ServiceReturn`, nontarget `EnvironmentAdd`, and
`Stutter`; it has no raw context-owned protected invocation or target-mutation
constructor.

Only `ServiceLinearize(call_ref)` can change target membership. Its guard names
a prior incomplete call, while environment steps cannot insert the target.
`m0_target_change_requires_linearization`,
`m0_environment_cannot_add_target`, and
`m0_protected_exec_derives_target_action_provenance` expose those structural
facts. `m0_call_key_fresh` and
`m0_broker_invoke_step_is_local_and_fresh` additionally enforce request-local,
fresh `(request,attempt)` call keys. This is stronger than selecting a protected
trace after the fact: `m0_coupled_exec` relates A1 and service steps lock-step,
and prefix induction proves that erasing the separately accumulated cut-bearing
service calls equals
`pi_invocations` of the observed global trace.

`m0_coupled_exec_derives_complete_mediation` derives the legacy
`CompleteMediation` predicate from that execution relation. Separately,
`M0ProtectedHandleState` and `m0_exclusive_handle_context` define a T4-C1
closed-interface context that can only audit masked `ContextEvent::Invoke`
observations.
The context transition relation has no service state, handle, or mutation
parameter. `m0_exclusive_context_is_storage_parametric` proves the context
admissible, `m0_wal_exec_has_exclusive_handle_context` constructs its states for
every typed-WAL execution, and
`m0_exclusive_context_derives_complete_mediation` derives the same invocation
equality for every admitted plugged execution under this context.

The authorization chain does not stop at service-call ancestry.
`m0_coupled_every_configuration_has_call_origins` proves every stored call has
an exact prior A1/WAL Invoke origin. T4-C0 maps that source event to the
canonical Broker execution, and T1 `invoke_temporal_at` supplies canonical-call,
positive-cut, acknowledged Authorize/Start, uniqueness, and strict-prior append-
return facts. `m0_coupled_linearization_is_durably_authorized` packages this
chain for every coupled target-changing service action.

`m0_deployment_exec` collects the well-formed configuration, A1 execution,
protected execution, eventwise coupling, typed-WAL execution, and exact A1/WAL
trace agreement into one reusable boundary. The generic theorem
`m0_deployment_derives_authorized_linearizations` proves the quantified
`m0_every_linearization_durably_authorized` predicate, which is retained by the
concrete package. A standalone `m0_protected_exec` specifies only the service
transition grammar: accepting `BrokerInvoke` is not itself an authorization
decision. The authorization claim is therefore explicitly scoped to the
deployment predicate rather than overclaimed for arbitrary service traces.

The premise-free witness separately constructs a 32-event protected-service
execution and then couples it lock-step to the A1 execution and its 31-event WAL
projection. It accepts calls at global
indices 12 and 23; call 0, for attempt 1, is the sole linearization; both calls
return; attempt 2 never linearizes; and there is no environment addition. Both
calls are durably authorized. The closed-interface audit context is plugged into
the
same WAL execution, and its generated invocation trace equals the service trace
and `pi_invocations`. `t6_m0_executable_crash_retry_mediation` retains A1's
Unknown-not-Fail and exactly-one-effect conclusions, while
`t6_m0_mediation_nonvacuity` exposes the complete package existentially without
premises.

The T6-M0 target verifies 977 cumulative obligations with zero errors, adding
61 over T6-A1. At the retained M0 checkpoint, all 43/43 targets passed, with
1,017 dependency-aware non-duplicated obligations and 21,844 summed target
obligations.

This is a closed-alphabet no-bypass property of the formal deployment interface,
not verified production Rust, transport, remote-service, operating-system descriptor, ACL,
or process-isolation code. T6-M0 also adds no byte/fsync persistence,
caller-visible `ReturnResult`, least privilege, multi-request/global
linearizability, or liveness theorem. Its prefix inductions establish service-
call and audit-trace mediation; they do not establish the general combined A1/
WAL prefix-indexed stuttering simulation or the storage-parametric end-to-end T6
lift.

## T6-P0: prefix-indexed adapter/WAL/protected product

`t6_prefix_simulation.rs` imports only T6-M0. It defines a weak index over a
conditionally paired A1 adapter execution and typed-WAL execution.
`p0_a1_wal_step_match` advances the index by exactly one for
`A1AdapterEvent::Observe` and requires the same WAL global label. It stutters
for `ServiceLinearize` and `EnvironmentAdd`. `p0_a1_wal_coupled` adds the
existing `WeakIndexMap` shape, and `p0_a1_wal_related_prefix_at` states exact
projected-global and request-local-history equality at each mapped prefix.

`p0_execution_pair` packages an independently valid `m0_coupled_exec`, a valid
typed-WAL execution, and that weak step coupling. It does not assert that a WAL
execution exists for every A1 execution. The principal theorem
`p0_execution_pair_derives_prefix_product` derives `p0_prefix_product`, whose
per-prefix clauses include:

- exact A1-global/WAL-prefix and request-local adapter-history agreement;
- valid truncated A1/protected and typed-WAL executions;
- `p0_effect_state_agreement` for request, initial/current membership,
  environment additions, and exactly the protected calls that denote
  linearized attempts;
- equality between the protected accepted-call trace and the mapped WAL
  invocation projection; and
- `CompleteMediation` at the mapped prefix.

`p0_execution_pair_prefix_closed` and `p0_prefix_product_closed` truncate both
A1-indexed executions, the WAL execution at the mapped point, and the weak map
at the same boundary. `p0_canonical_index_map` counts observed global events in
each A1 prefix. `p0_canonical_map_couples_trace_equal_execution` and
`p0_trace_equal_execution_pair` show that the older whole-trace equality
premise yields this canonical step coupling. They transform already supplied
executions; they are not forward-existence proofs.

`t6_p0_executable_crash_retry_prefix_product` instantiates the relation with
the 32-event A1 execution, separately constructed 32-event protected-service
execution, and 31-event typed-WAL execution. The canonical map has 33 points,
begins at 0, ends at 31, and stutters between points 13 and 14 at
`ServiceLinearize { attempt: 1 }`. The theorem retains complete mediation and
final A1/protected effect-state agreement.
`t6_p0_prefix_product_nonvacuity` exposes the package existentially without
premises.

T6-P0 verifies 1,000 cumulative obligations with zero errors, adding 23 over
T6-M0. It remains a fixed single-request `EnsureMember` model result and does
not construct WAL executions from arbitrary A1 runs. T6-X0 supplies its
storage-parametric contextual lift.

## T6-X0: storage-parametric contextual end to end

`t6_contextual_end_to_end.rs` imports only T6-P0. It defines
`x0_adapter_broker_map` by composing P0's adapter-to-WAL map with T4-C2's
canonical WAL-to-Broker map. For adapter prefix `k`, WAL prefix
`w = mu[k]`, and Broker prefix `b = nu[w]`, `x0_contextual_prefix_at` retains
the P0 prefix product and proves:

- valid plugged WAL and canonical Broker executions truncated at `w` and `b`;
- equality of the A1 request history with `pi_adapter` of the canonical Broker
  prefix;
- equality of the source and target context states and masked `ContextView`s;
- T1 parameterized safety for the canonical Broker prefix; and
- equality between the A1 external-run state and the independently executed
  protected-service state, including exact linearized attempts.

`x0_contextual_product` packages those all-prefix facts with
`StorageParametricContext`, the admitted `PluggedWalExecution<S>`, the P0
execution pair, T4-C2 contextual replacement, and the weak shape of the
composed map. `x0_lift_p0_through_context` is the principal generic lift: it
requires the storage-parametric context, admitted plugged WAL execution, and
P0 prefix product, and derives the contextual product. This is conditional on
the supplied source executions and context admission; it does not construct a
WAL execution for every A1 run or prove that every context admits the run.

`x0_contextual_broker_terminal_outcome_refines<X,I,S>` is the paper-facing
generic contextual theorem. Given a well-formed adapter-bearing `PaperConfig`,
a storage-parametric context admitting a plugged WAL execution,
`AdapterVerified`, `AdapterRely`, and a selected source terminal, it constructs
T4-C2's canonical plugged Broker execution and proves that the target selects
the same terminal and satisfies `Refines` and
`PerRequestEffectRefinement`. The P0/M0 instance below discharges and extends
those premises with operational and protected-state facts for `EnsureMember`.

`t6_x0_ensure_member_terminal_end_to_end` is the principal selected-terminal
theorem. For one distinguished `EnsureMember` request it additionally assumes
`terminal(plugged.machine.events, request) = Some(outcome)` and proves:

- source WAL terminal evidence and compatibility, `Refines`, complete
  mediation, final A1/protected effect agreement, and durable authorization of
  every protected linearization;
- preservation of the same selected terminal, `Refines`, per-request effect
  refinement, and complete mediation on T4-C2's canonical Broker trace; and
- the all-prefix contextual product and grounding of the semantic external run
  in the protected execution.

`t6_x0_executable_crash_retry_end_to_end` supplies a premise-free instance
using M0's exclusive-handle audit context, the 32-event A1 adapter execution,
the independent 32-event protected-service execution, and the 31-event
typed-WAL execution. The canonical Broker also terminates
`Unknown(NonConclusiveFailure)`. The package proves one abstract insertion
effect and not zero, exactly one protected linearization, final target
membership, complete mediation on both WAL and Broker traces, equality of the
canonical Broker context's final invocation audit with the protected accepted
calls, and durable authorization for every linearization.
`t6_x0_contextual_end_to_end_nonvacuity` exports the package existentially.

T6-X0 verifies 1,022 cumulative obligations with zero errors, adding 22 over
T6-P0. At the retained X0 checkpoint, all 45/45 targets passed, with 1,062
dependency-aware non-duplicated obligations and 23,866 summed target
obligations.

The operational protected-state theorem is the conditional single-request
`EnsureMember` instance. The generic contextual terminal theorem is
adapter-polymorphic, but it assumes `AdapterVerified` and `AdapterRely` and
does not supply a request-indexed family of operational adapter/protected
executions. X0 does not verify production Rust/runtime or transport code,
deployment/OS isolation, byte encoding or fsync, caller-visible
`ReturnResult`, least privilege, multi-request/global linearizability,
concurrency, or liveness. M0's exclusive-handle conclusion remains a
closed-alphabet formal-model property.

## T6-RO0: read-only operational adapter

`t6_readonly_operational.rs` imports only T6-X0 and adds the second executable
adapter instance, for the ReadOnly retry class; the first was T6-A1's
idempotent `EnsureMember`. The protected target is an environment-owned
Boolean. A read linearizes by sampling that Boolean at an explicit
environment-history cut, and each recorded sample also stores the
physical-history cut at which the remote read took effect, witnessing
invocation before read before delivery without exposing the silent service
action as a Broker or WAL label. Neither sampling nor retry changes the
Boolean: `EnvironmentSet` is the only transition that changes it, so
`zero_effect` factors the post-state as the initial state plus the recorded
environment transitions, rather than treating an arbitrary post-state as
read-only. The `one_effect` relation is constantly false, and observation
classification requires every delivered Success to carry the value encoded by
a matching sample and every delivered Failure to have no sample for its
attempt. The checkpoint therefore makes the ReadOnly `zero_effect` branch of
`Refines` non-vacuous with an operational model.

The operational machine mirrors the A1 pattern. Its state records the online,
crashed, or recovering mode; the active attempt; observed global and physical
histories; read samples; failed attempts; environment updates; and the current
Boolean. `ServiceRead` is enabled only for an Online, active, previously
invoked, still-undelivered, not-yet-sampled, nonfailed attempt. The inductive
machine invariant establishes exact global/physical projection, request
locality, invocation uniqueness and ordering, sample well-formedness and
history provenance, and observation classification.
`ro_exec_derives_adapter_rely` then derives `AdapterRely` from the transition
system rather than assuming it, and `ro_adapter_is_verified` establishes
`AdapterVerified` for the fixed all-ReadOnly two-attempt configuration.

The concrete witness contains 33 adapter events, including the two silent
events `ServiceRead { attempt: 1 }` and `EnvironmentSet { present: true }`,
whose projection is exactly 31 global events. The coupled typed-WAL execution
has 31 events and seven acknowledged records: `Authorize`, `Prepare`, `Arm`,
`Start(1)`, `Start(2)`, `Outcome(2, Failure)`, and `Fail(2)`. Operationally it
executes `Invoke(1)`, a silent read that samples the absent target, a
delivered `Success` carrying value id 0, Crash, recovery, a silent environment
insertion of the target, the durable `Start(2)` append, `Invoke(2)`, and
`Failure(2)`. Attempt 1's Success is never journaled. The selected terminal is
`Fail { attempt: 2 }`: the delivered Success means not every invocation
failed, but `failure_conclusive` requires all attempts to have failed only for
the Idempotent class, so the ReadOnly Fail record is legal and the
`Unknown(2, NonConclusiveFailure)` record is proved disabled. This inverts
A1, whose Idempotent class made `Fail` impossible and terminated `Unknown`.
`ro_wal_terminal_refines` derives the terminal selection, `Refines`, and
`PerRequestEffectRefinement` at the typed-WAL boundary, and
`t6_ro0_executable_crash_retry_nonvacuity` proves the premise-free operational
and semantic crash/retry package.

T6-RO0 verifies 1,083 cumulative obligations with zero errors, adding 61 over
its T6-X0 parent. The retained RO0 checkpoint passed all 46/46 targets,
contained 1,123 dependency-aware non-duplicated obligations, and summed to
24,949 target obligations.

The theorem deliberately stops at the WAL/Broker boundary: `ServiceRead` and
`EnvironmentSet` are adapter-local events that stutter in the global trace, so
a deployment-level service/transport refinement remains a separate obligation.
T6-RO0 also does not couple a separate protected-service execution, construct
an M0-style audit context, or instantiate the P0 prefix product or X0
contextual lift for the ReadOnly instance.

## T6-DD0: deduplicated operational adapter definitions

`t6_deduplicated_operational.rs` imports T6-RO0 and begins the third executable
adapter instance, for the Deduplicated retry class. Its protected target is a
service-owned keyed slot. A silent `ServiceDecide` transition can apply and
memoize one value or memoize rejection; later deliveries replay that decision.
The recorded decision includes an invocation-history cut so the intended
Invoke--decide--delivery provenance is explicit without exposing the silent
service action as a Broker/WAL event.

DD0 defines the adapter interpretation, the fixed all-Deduplicated
configuration and its well-formedness proof, and the operational modes,
events, state, enabledness, transition, execution, and prefix relations. As a
standalone definitions checkpoint it deliberately stops before the invariant,
rely derivation, and concrete terminal witness.

T6-DD0 verifies 1,085 cumulative obligations with zero errors, adding 2 over
T6-RO0.

## T6-DD1: deduplicated invariant and adapter rely

`t6_deduplicated_invariant.rs` imports DD0 and proves its operational safety
boundary. The invariant equates the physical history with the request
projection, retains request-local canonical positive and uniquely ordered
events, and connects the at-most-one memoized decision to an invocation-backed,
delivery-free history cut. It also factors the protected slot through that
decision, classifies every delivered Success or Failure by the memo, and gives
an active attempt exactly one invocation and no delivery.

The initial state and both `Observe` and silent `ServiceDecide` steps preserve
the invariant, so induction covers every configuration of every finite DD
execution. The resulting theorems derive pairwise deduplicated observation
consistency, the configured service law, `AdapterRelyTrace`, and `AdapterRely`
over the projected global trace. `dd_adapter_is_verified` then closes the
generic terminal obligation: Commit selects the applied memo and one effect,
Fail selects the rejected memo and zero effects, and Unknown admits the
factored zero-or-one alternatives.

T6-DD1 verifies 1,111 cumulative obligations with zero errors, adding 26 over
T6-DD0. DD1 is the universal safety parent of the concrete DD2 witness.

## T6-DD2: deduplicated coupled crash/retry witness

`t6_deduplicated_witness.rs` imports DD1 and constructs matching executions of
the memoizing adapter and typed WAL. Starting from an empty protected slot,
attempt 1 invokes the operation and the adapter performs one silent
`ServiceDecide(Applied(value))` at physical-history cut 1. The decision is not
a global/WAL label. A crash follows the invocation before any delivery or
Outcome record; scan, truncation, and recovery retain the service-owned memo
while resetting the active attempt. Attempt 2 uses the same stable key,
receives the replayed Success, and durably appends its Outcome and Commit.

The resulting adapter execution has 31 events and projects exactly to the
30-event WAL execution. The physical projection is exactly Invoke 1, Invoke 2,
Delivered Success 2: attempt 1 has no delivery, but its invocation-backed
decision is the unique applied effect. The final seven-record Journal contains
Authorize, Prepare, Arm, Start 1, Start 2, Outcome Success 2, and Commit 2, and
the keyed slot is `Some(value)`. The proof establishes WAL reachability and
trace agreement, canonical closed WAL/Broker representation, the exact terminal
Commit, `AdapterRely`, `Refines`, per-request effect refinement, and combined
premise-free operational and semantic nonvacuity packages.

T6-DD2 verifies 1,143 cumulative obligations with zero errors, adding 32 over
T6-DD1. DD2 stops at the adapter/WAL/Broker model boundary. Its historical
retained suite passed all 53/53 targets with 1,287 dependency-aware non-
duplicated obligations and 29,082 summed target obligations. A separate P0/X0
contextual instantiation for this adapter, a request-indexed family of external
runs, caller-visible
`ReturnResult`, production transport/code refinement, byte/fsync persistence,
multi-request concurrency, and liveness remain open.

## T6-DD3: deduplicated protected execution and mediation

`t6_deduplicated_mediation.rs` imports DD2 and constructs a separate keyed
protected-service machine for the same 31 adapter steps. Its closed event
alphabet contains broker invocation, service decision, memoized service return,
and stutter. Only `ServiceDecide` can change the protected slot, and a stable key
can acquire at most one decision. The concrete run couples adapter invoke 1 to
protected call 1, the adapter's sole silent decision to exactly one applied
protected decision, adapter invoke 2 to protected call 2, and the retry delivery
to a memoized `ServiceReturn`; the second call performs no mutation.

The proof derives complete mediation from exact event coupling, proves the two
protected calls equal the WAL invocation projection, and relates the same call
sequence to T6-M0's storage-parametric exclusive-handle context. Exact WAL source
indices 12 and 22 discharge durable authorization for both calls, while the only
protected decision is shown to inherit that authorization. The final package
retains DD2's terminal/effect theorem and is inhabited without premises.

T6-DD3 verifies 1,182 cumulative obligations with zero errors, adding 39 over
T6-DD2. Its historical retained suite passed all 54/54 targets, contained 1,326
dependency-aware non-duplicated obligations, and summed to 30,264 target
obligations. DD3 closes protected-service execution and mediation for the
distinguished DD2 run; that checkpoint left contextual composition to DD4.

## T6-DD4: deduplicated contextual composition

`t6_deduplicated_contextual.rs` imports DD3 as its sole direct parent and builds
the projection-length canonical weak index from the 31 adapter steps to the 30
WAL events. Generic prefix induction proves exact adapter/WAL trace and history
agreement, valid adapter/protected/WAL prefixes, effect-state agreement, and
complete mediation at every related adapter prefix.

The proof composes that index with T4-C2's canonical WAL/Broker weak map. At
every mapped prefix it retains context-state and context-view equality, complete
mediation, and T1 safety. Separate terminal lemmas prove source refinement from
the adapter's final history and transport the same outcome, `Refines`, and per-
request effect refinement to the canonical Broker trace. A premise-free closed
package retains the DD2 crash/retry and DD3 mediation packages.

T6-DD4 verifies 1,222 cumulative obligations with zero errors, adding 40 over
T6-DD3. The retained suite passes all 55/55 targets, contains 1,366 dependency-
aware non-duplicated obligations, and sums to 31,486 target obligations. DD4
closes M2 for the distinguished DD2 execution; DD5 closes M3 at the
coverage-conditioned request-indexed family boundary.

## T6-DD5: request-indexed operational/protected family

`t6_deduplicated_request_family.rs` imports DD4 and defines a total family from
request identifiers to paired adapter/protected executions. Its coverage
predicate applies to every request with a terminal outcome in the shared WAL.
For each covered member, the theorem derives DD1's `AdapterRely`, reconstructs
DD4's canonical adapter/WAL prefix product, derives complete mediation from the
protected coupling, and invokes the generic X0 terminal transport for both the
source WAL and canonical Broker traces.

The concrete DD2 family is premise-free: the retained WAL has exactly one
terminal request, request 0, and its family member is the DD2/DD3 pair. Thus the
family theorem is request-indexed and non-vacuous while keeping family coverage
as an explicit admission condition for arbitrary shared executions.

T6-DD5 verifies 1,228 cumulative obligations with zero errors, adding 6 over
T6-DD4. With K4-R3 registered, the retained suite passes all 61/61 targets,
contains 1,402 dependency-aware non-duplicated obligations, and sums to 34,063
target obligations. M3 is
closed as a coverage-conditioned family theorem; constructing members directly
from production adapter executions remains an implementation refinement.

## Reproducible verification

The platform-specific toolchains are locked in `toolchain.lock.json`. The
Windows-x64 entry uses Verus `0.2026.07.05.49b8806` and Rust
`1.96.0-x86_64-pc-windows-msvc`; the Linux-x64 entry uses the matching Verus
release and Rust `1.96.0-x86_64-unknown-linux-gnu`. The Linux Verus archive is
SHA256 `cb4fe7db423fdda5e9aa77b2c3e632f8a618b6a991509283aae591f0a914d34c`,
and the Linux rustup installer is SHA256
`4acc9acc76d5079515b46346a485974457b5a79893cfb01112423c89aeb5aa10`.

Run from the repository root:

```powershell
.\mechanized\verify.ps1
```

On Linux with PowerShell 7:

```bash
pwsh -NoLogo -NoProfile -File mechanized/verify.ps1
```

The Linux runner requires `chmod` and `unzip`, and explicitly binds Verus to
the Z3 executable inside the hash-checked Verus tree. The source-current
retained run passes all 61/61 targets with 1,402 dependency-aware
non-duplicated obligations and 34,063 summed target obligations.

The clean-room Linux run at source revision
`5d8e8ed39e492b05f52ba093782a043d204f1192` is retained as
`mechanized/results/verification-report-linux-5d8e8ed.json`. It passed all 56
targets with fresh Rust/Verus toolchain isolation and post-run source/tree
integrity checks.

The current packaging checkpoint at source revision
`9a45d391e8c19d3f069a3df271005b1fd6b39b60` is retained as
`mechanized/results/verification-report-linux-9a45d39.json`. It passed all
56/56 targets with 1,372 dependency-aware non-duplicated obligations and
32,714 summed target obligations. SHA-256:
`dce3cbf95f4eeda2203888533123a391f8fed30778b03281b460da085b49599a`.

The offline-bundle verifier checkpoint at source revision
`079f20900b25ce90447f873c252566f8c9d5e764` is retained as
`mechanized/results/verification-report-linux-offline-079f209.json`. It copied
the lock-matching Rust toolchain into a fresh run root, recorded
`rustup_dist_server` and `rustup_update_root` as `offline-bundle`, invoked no
artifact download, and passed all 56/56 targets with the same 1,372
non-duplicated and 32,714 summed obligations. SHA-256:
`926d6834e17a46c8cb1edaefd85c9bb26b702aeabcb98e83c51ee72c5f47c012`.

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

The cumulative target counts and aggregates below come from the current
retained 61-target full suite:

```text
M0 verified obligations: 21
R1 verified obligations: 86
B1 verified obligations: 39
C1 verified obligations: 128
D1 verified obligations: 144
Q1 verified obligations: 144
K1 verified obligations: 159
K2-G0 verified obligations: 179
K2-T0 verified obligations: 208
K3-A0 verified obligations: 248
K3-A0 target delta over K2-T0: 40
K4-C0 verified obligations: 255
K4-C0 target delta over K3-A0: 7
K4-R0 verified obligations: 266
K4-R0 target delta over K4-C0: 11
K4-R1 verified obligations: 274
K4-R1 target delta over K4-R0: 8
K4-R2 verified obligations: 276
K4-R2 target delta over K4-R1: 2
K4-R3 verified obligations: 278
K4-R3 target delta over K4-R2: 2
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
T6-A1 verified obligations: 916
T6-M0 verified obligations: 977
T6-P0 verified obligations: 1,000
T6-P0 target delta over T6-M0: 23
T6-P0 non-duplicated verified artifact obligations: 1,174
T6-P0 summed target obligations: 24,987
T6-X0 verified obligations: 1,022
T6-X0 target delta over T6-P0: 22
T6-X0 non-duplicated verified artifact obligations: 1,196
T6-X0 summed target obligations: 26,009
T6-RO0 verified obligations: 1,083
T6-RO0 target delta over T6-X0: 61
T6-RO0 non-duplicated verified artifact obligations: 1,257
T6-RO0 summed target obligations: 27,092
T6-DD0 verified obligations: 1,085
T6-DD0 target delta over T6-RO0: 2
T6-DD0 non-duplicated verified artifact obligations: 1,259
T6-DD0 summed target obligations: 28,177
T6-DD1 verified obligations: 1,111
T6-DD1 target delta over T6-DD0: 26
T6-DD1 non-duplicated verified artifact obligations: 1,285
T6-DD1 summed target obligations: 29,288
T6-DD2 verified obligations: 1,143
T6-DD2 target delta over T6-DD1: 32
T6-DD2 non-duplicated verified artifact obligations: 1,317
T6-DD2 summed target obligations: 30,431
T6-DD3 verified obligations: 1,182
T6-DD3 target delta over T6-DD2: 39
T6-DD3 non-duplicated verified artifact obligations: 1,356
T6-DD3 summed target obligations: 31,613
T6-DD4 verified obligations: 1,222
T6-DD4 target delta over T6-DD3: 40
T6-DD4 non-duplicated verified artifact obligations: 1,396
T6-DD4 summed target obligations: 32,835
T6-DD5 verified obligations: 1,228
T6-DD5 target delta over T6-DD4: 6
T6-DD5 non-duplicated verified artifact obligations: 1,402
T6-DD5 summed target obligations: 34,063
```

C1's 128 obligations include the 86 R1 and 39 B1 obligations imported into the
composition crate, plus 3 composition-specific obligations. D1 and Q1 each
include that same C1 closure plus 16 new obligations. K1 imports Q1 and adds 15
executable-summary and guard obligations; K2-G0 imports K1 and adds 20 guard
obligations; K2-T0 imports K2-G0 and adds 29 mutation/coupling obligations; and
K3-A0 imports K2-T0 and adds 40 exact-reference, append-state, replay-coupling,
and B1 projection obligations. K4-C0 imports K3-A0 and adds 7 finite-manifest
lookup, configuration-refinement, well-formedness, and nonvacuity obligations.
K4-R0 imports K4-C0 and adds 11 executable-search, arbitrary-manifest
Authorize-refinement, and premise-free accepted-profile obligations. K4-R1
imports K4-R0 and adds 8 manifest-profile, Prepare/Start-refinement, and
premise-free profile obligations. K4-R2 imports K4-R1 and adds 2 generic
Authorize-mutation and premise-free mutation-witness obligations. K4-R3
imports K4-R2 and adds 2 generic Prepare-mutation and chained-witness
obligations.
B2-R independently includes Q1 and adds 25 record-side Broker obligations.
B2-C includes B2-R and adds 6 rich
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
T6-A1 imports T6-A0 directly and adds 52 obligations for the operational
adapter/service transition system, its inductive invariant and finite-execution
closure, derivation of `AdapterRely`, generic executable-to-WAL refinement,
exact crash/recovery/retry executions, the seven-record Unknown terminal,
one-effect refinement, Fail impossibility, and the premise-free executable
nonvacuity package.
T6-M0 imports T6-A1 directly and adds 61 obligations for the separately defined
protected-service transition system, eventwise A1 coupling and prefix trace
derivation, request-local fresh call keys, structural target-mutation
restriction, the storage-parametric closed-interface audit context and plugged
WAL witness, the packaged deployment relation and quantified authorization
theorem, canonical T4-C0/T1 durable-authorization ancestry, exact concrete
mediation package, and premise-free nonvacuity theorem.
T6-P0 imports T6-M0 directly and adds 23 obligations for the weak A1/WAL step
relation and index map, every-prefix trace/history agreement, A1/protected
effect-state preservation, the combined prefix product, execution-pair and
product prefix closure, the canonical map for already trace-equal executions,
and the concrete prefix-product and nonvacuity theorems.
T6-X0 imports T6-P0 directly and adds 22 obligations for composition of the
adapter-to-WAL and canonical WAL-to-Broker maps, every-prefix plugged/context/
T1 agreement, grounding the A1 external run in protected state, generic
contextual Broker terminal refinement under `AdapterVerified` and
`AdapterRely`, source and target mediation transport, the conditional
single-request `EnsureMember` theorem, and its premise-free crash/retry and
existential nonvacuity packages.
T6-RO0 imports T6-X0 directly and adds 61 obligations for the read-only
adapter interpretation and its `AdapterVerified` instance, the sampled-read
operational machine, its inductive invariant and finite-execution closure,
derivation of `AdapterRely`, the coupled crash/retry adapter and typed-WAL
executions, the seven-record conclusive `Fail` terminal and disabled
nonconclusive Unknown, zero-effect refinement, and the premise-free executable
nonvacuity package.
T6-DD0 imports T6-RO0 directly and adds 2 obligations for the fixed
Deduplicated configuration's well-formedness. The adapter interpretation and
memoizing operational transition system are defined. T6-DD1 imports T6-DD0
directly and adds 26 obligations for decision/history provenance, slot and
observation invariants, step and finite-execution preservation, pairwise
deduplicated consistency, the service law and `AdapterRely` derivation, and
the Deduplicated `AdapterVerified` instance. T6-DD2 imports T6-DD1 directly and
adds 32 obligations for the exact adapter and typed-WAL crash/retry executions,
stable-key memo replay, trace and evidence projections, the canonical closed
WAL/Broker representation, terminal and effect refinement, exact one-effect
classification, and the premise-free combined nonvacuity package. T6-DD3 imports
T6-DD2 directly and adds 39 obligations for the protected-service machine,
event coupling, exact one-decision provenance, memoized return, trace-derived
complete mediation, closed exclusive-handle context, and durable authorization
of every protected decision. T6-DD4 imports T6-DD3 directly and adds 40
obligations for the canonical adapter/WAL weak index, prefix trace/history and
effect-state agreement, contextual WAL/Broker composition, mapped-prefix
mediation and safety, source/target terminal transport, and the closed
premise-free DD4 package.
T6-DD5 imports T6-DD4 directly and adds 6 obligations for the request-indexed
operational/protected family interface, terminal-request coverage, generic
all-terminal source/target refinement and mediation, and the premise-free DD2
family witness.
The historical T6-A1 non-duplicated total
counts M0, C1, each independent D1/Q1 delta, the B2-R delta over Q1, and the
B2-C through T5-C0 deltas along their dependency chain, plus the independent H1
and T6-D0 deltas over T5-C0, the T6-E0 delta over T6-D0, the T6-C0 delta over
T6-E0, the T6-S0 delta over T6-C0, the T6-A0 delta over T6-S0, and the T6-A1
delta over T6-A0. That registry contained 42 Verus targets and 956
non-duplicated obligations; the retained run summed 20,867 target obligations.
The historical retained T6-M0 checkpoint contained 43 targets and 1,017
dependency-aware non-duplicated obligations and summed to 21,844 target
obligations. The historical T6-P0 registry contained 44 targets and 1,040
dependency-aware non-duplicated obligations and summed to 22,844 target
obligations. The historical T6-X0 registry contained 45 targets and 1,062
dependency-aware non-duplicated obligations and summed to 23,866 target
obligations. The historical T6-RO0 registry contained 46 targets and 1,123
dependency-aware non-duplicated obligations and summed to 24,949 target
obligations. The current registry adds K1, K2-G0, K2-T0, K3-A0, K4-C0, K4-R0,
K4-R1, K4-R2, K4-R3, T6-DD0, T6-DD1, T6-DD2, T6-DD3, T6-DD4, and T6-DD5: it
contains 61 targets and 1,402 dependency-aware non-duplicated obligations, and
the retained run sums to 34,063 obligations.
The historical retained T6-A0 checkpoint had 41 targets, 904 non-duplicated
obligations, and a 19,951 target sum. The historical retained T6-S0 checkpoint
had 40 targets, 880 non-duplicated obligations, and a 19,064 target sum before
the conservative definitional T1 accessor lemma was added.

T6-X0 completes the conditional end-to-end contextual lift for the operational
`EnsureMember` instance, T6-RO0 adds the ReadOnly operational instance, T6-DD0
defines the Deduplicated machine, and T6-DD1 proves its invariant, rely, and
generic terminal refinement. T6-DD2 closes its concrete coupled witness and
WAL/Broker terminal refinement. T6-DD3 closes the independent protected-service
execution and complete-mediation layer for that witness. T6-DD4 closes its all-
prefix contextual P0/X0 composition. T6-DD5 closes the coverage-conditioned
request-indexed family theorem and its DD2 nonvacuity witness. Constructing
family members from production executions, caller-visible `ReturnResult`,
production deployment
isolation, byte/fsync refinement, multi-request concurrency, and liveness remain
explicit subsequent extensions.
