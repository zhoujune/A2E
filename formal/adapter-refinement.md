# Adapter-Specific Refinement

## 1. Purpose

The broker controls when a tool is invoked, but the meaning of repeated calls
depends on the tool. This document defines the refinement relation between a
concrete broker/tool history and one abstract operation.

The key distinction is:

- **effect consistency**: repeated calls change the protected external state as
  no more than one abstract operation would;
- **result consistency**: repeated calls return the same definitive outcome and
  value.

Idempotence provides effect consistency. Deduplication can provide both.

## 2. Traces and projections

Let `tau` be a finite broker execution trace containing authorization,
journal, invocation, observation, crash, recovery, and logical-outcome events.
For request `r`, define `eta_r` as the projection of `tau` onto

```text
Invoke(r,a), Success(r,a,v), Failure(r,a), Ambiguous(r,a),
InvalidResult(r,a,v_bad).
```

Normatively, `tau` is a finite prefix-closed execution from the labeled ADT in
[mechanization-contract.md](mechanization-contract.md#6-events-steps-executions-and-projections),
and `eta_r = pi_adapter(tau,r)` retains the physical payloads of `InvokeEvent`
and `DeliverEvent`. Authorization is a linearized `Authorize` Journal record,
not an element of this physical projection.

Here `a` is a stable per-request attempt identifier. Every outcome must name
the unique earlier invocation with the same `(r,a)` pair. Late responses may
not be silently attached to a newer retry. The executor presents `a` with each
delivery; the broker accepts the delivery only if `a` is the current in-flight
attempt and otherwise ignores it.

This is the physical projection. `ReserveAttempt(r)` creates durable
`Started(r,a)` but contributes no external event. `SendAttempt(r,a)` contributes
`Invoke(r,a)`. `Deliver*` contributes the corresponding physical outcome, while
`Persist*` later places that outcome in the durable attempt log. Thus a crash
can leave a reservation without a send or a delivered outcome without a
durable outcome record.

Crash and recovery do not directly mutate the external abstract state, so they
are erased by this projection. They remain important because they explain why
a previously observed result may be lost and why another `Invoke` occurs.

`Failure` means a definitive adapter result delivered for the current physical
invocation. It becomes durable, recoverable broker knowledge only after
`PersistErr`. `Ambiguous` means the adapter cannot establish whether that
invocation affected the external system. Transport errors and timeouts are
therefore normally `Ambiguous`, not `Failure`.

`InvalidResult` means the tool returned data that did not satisfy the adapter's
typed result contract. It is effect-uncertain like `Ambiguous` and cannot be
committed as a successful value. Delivery and persistence are separate: a
crash after `DeliverInvalidResult` but before `PersistInvalidResult` loses the
broker's recoverable classification.

An `Invoke` with no later outcome in the projection is also effect-uncertain.
This occurs when the broker crashes while a request is in flight. Absence of a
response is not evidence that the call had no effect.

Conversely, an outcome can appear in `eta_r` without appearing in durable
`attemptLog` when a crash occurs after delivery but before `Persist*`. Adapter
refinement interprets the full physical trace; recovery and retry decisions
must use the durable attempt log rather than the full trace.

## 3. Primary refinement relation

For adapter class `c`, external pre-state `x0`, post-state `x1`, and logical
outcome `o`, the primary contract is

```text
Refines_c(eta_r, x0, x1, o)
```

under an explicit rely condition describing permitted interference by other
principals and services. This relation must establish the correct target,
arguments, state transition, and result semantics. The effect-count summary
below is derived from this relation; it is not by itself a functional
correctness proof.

Theorem V1 makes the rely explicit as
`AdapterRely(P,tau,r,run)` and packages the class relation as
`Refines(P,r,eta_r,run,o)`. Here `P : PaperConfig<Adapter<X,I>>` contains the
adapter interpretation and `Cfg = paper_broker_config(P) : FullConfig` is the
derived broker configuration. A concrete adapter theorem must establish
`AdapterVerified(P)` for its selected well-formed paper configuration; a
reusable family theorem may quantify over a class of compatible `P` values. An
end-to-end instance assumes the theorem for its selected `P`. T6 then
concludes `PerRequestEffectRefinement` for every terminal request. This is a
per-request result, not global linearizability across adapters or requests.

T6-D0 freezes this interface in Verus. An `ExternalRun<X,I>` contains the only
pre- and post-state values passed to the effect and result relations.
Standalone `AdapterRelyTrace(P,...)` inputs must contain only events for their
named request. `Delivery` and `TerminalRecord` return `Some` only for unique
matching evidence. The broker-only predicate
`OutcomeEvidence(Cfg,j,r,eta,o)` takes the derived `FullConfig` explicitly
because the Unknown branch checks a configuration-dependent structural rule.
Commit and Fail references are resolved only in the strict prefix preceding
their terminal record. The Unknown guard/anchor decomposition is proved equal
to the replay layer's rule, preventing the two definitions from silently
drifting.
These definitions do not themselves establish the T6 bridge.

T6-E0 proves the adapter-independent evidence implication. At the history
level, Journal legality, physical-delivery uniqueness, durable
Outcome-to-delivery causality, and a selected terminal outcome imply
`OutcomeEvidence(Cfg,j,r,eta,o)`. At the event level, the Broker contract
invariant, exact equality of the Broker Journal and physical histories with
`pi_journal(tau)` and `pi_physical(tau)`, and
`terminal(tau,r)=Some(o)` imply `OutcomeEvidence` over
`pi_adapter(tau,r)`. Commit and Fail resolve their references in the strict
pre-terminal prefix and select the unique matching delivery; Unknown reuses
the exact prefix `StructuralEnabled` rule and its durable reason-specific
anchor. This proof consumes no adapter run or semantic effect relation. It does
not establish `BrokerOutcomeCompatible`, `Refines`, an `AdapterVerified`
instance, the Journal/WAL T6-S0 wrappers, or an external-effect theorem.

T6-C0 proves `BrokerOutcomeCompatible` at the event level under the frozen
`PaperConfigWF`, Broker-invariant, exact-projection, `AdapterRely`, and terminal
premises. It invokes T6-E0 for causal evidence and discharges the compatibility
case split as follows:

- Commit selects the exact successful delivery; `Uncontrolled` additionally
  proves that its attempt is the only invoked attempt.
- Fail selects the exact failure delivery. `ReadOnly` needs no further retry
  condition. `Idempotent` proves that every invoked attempt has a selected
  Failure delivery. `Deduplicated` uses pairwise observation consistency to
  exclude Success and InvalidResult from a history containing the selected
  failure. `Uncontrolled` proves one invocation and that invocation's failure.
- Unknown proves Journal legality, the exact unique `UnknownRec`, and the
  reason-specific guard over its strict pre-terminal prefix;
  `Uncontrolled` additionally has at most one invocation.

These are broker/history compatibility facts. T6-S0 now combines T6-E0 and
T6-C0 into the frozen `TerminalEvidenceAndCompatibility` conclusion: under a
well-formed paper configuration, the Broker invariant, exact Journal and
physical projections, `AdapterRely`, and a selected terminal outcome, both
`OutcomeEvidence` and `BrokerOutcomeCompatible` hold for that request-local
history. Separate implication-form core and direct event-level theorems expose
the same result.

T6-S0 also transports this conjunction through both verified storage
boundaries. The atomic-Journal wrapper derives the exact final evidence
projections from Journal execution, trace agreement, and final-state
representation; the typed-WAL wrapper does the same through WAL execution,
trace agreement, and `WalBrokerRepresentation`. These are wrapper/transport
theorems over the already verified representations, not new backend
simulations. At the retained T6-S0 checkpoint, the target verified 840
cumulative obligations, 6 beyond T6-C0; that historical 40-target registry
contained 880 dependency-aware non-duplicated obligations, with cumulative-
target sum 19,064.

T6-S0 still does not interpret the external pre/post-state run, prove
`Refines` or `AdapterVerified`, establish any adapter effect, supply a concrete
terminal `AdapterRely` witness, cover `ReturnResult`, or establish broader
security, liveness, or global-linearizability claims. Adapter-effect proofs and
concrete adapter instances were deferred to a later checkpoint.

### T6-A0: concrete semantic closure

T6-A0 closes the next, deliberately semantic, layer. Its generic theorem takes
Journal legality, `AdapterRely`, `AdapterVerified`, and T6-S0's exact
`TerminalEvidenceAndCompatibility` conjunction and derives
`Refines(P,r,pi_adapter(tau,r),run,o)`. Selected-terminal event, atomic-Journal,
and typed-WAL exports also derive `PerRequestEffectRefinement`; outcome-free
exports case split on the unique terminal selector. Thus the adapter proof and
the Broker/history proof meet through the frozen T6-D0 interface rather than a
new storage simulation.

The concrete instance is the idempotent `EnsureMember` operation. Its external
state is a set of resources. For request `r`, the protected operation inserts
`target(r)` into the set. The interference witness records environment
additions and the broker attempts that linearized at the external service. The
rely excludes an environment insertion of `target(r)` and requires every
recorded linearized attempt to have an invocation in the request-local history.
`ZeroEffect` is equality with the pre-state plus environment additions;
`OneEffect` additionally inserts `target(r)`. Set insertion makes any positive
number of recorded linearized attempts observationally one effect. A successful
observation is classified only when its attempt linearized and its value has
identifier 1; the result relation additionally requires the post-state to
contain the target. A failure is classified only for a non-linearized attempt.
The proof establishes `AdapterVerified` and separately shows that the one-effect
model is nontrivial, including a state satisfying one effect but not zero.

The inhabitation result is exact and premise free. It constructs a well-formed
paper configuration, a 20-event/21-state typed-WAL execution with six durable
records, one physical invocation and one successful delivery, the represented
final Broker, a Commit outcome, and an external run that satisfies
`AdapterRely`. The resulting package contains WAL execution, admissibility,
trace agreement, representation, Broker invariant, Journal legality, terminal
evidence and compatibility, `Refines`, per-request effect refinement, and the
strict one-effect/not-zero conclusion. The final existential theorem fixes all
of those witnesses rather than merely asserting that compatible premises might
exist.

At the retained T6-A0 checkpoint, 41/41 registered targets verified. Because a
shared conservative definitional T1 accessor adds one transitive obligation,
the imported T6-S0 target is 841 rather than its historical 840. T6-A0 verifies
864 obligations with zero errors, a delta of 23 over that current T6-S0 parent.
That checkpoint's dependency-aware non-duplicated total is 904 and the sum of
all target obligations is 19,951.

This checkpoint verifies a mathematical adapter contract, not executable Rust
adapter code or the remote membership service. Its total synthetic
configuration grants every capability universal resource and argument scope;
it witnesses consistency, not least-privilege deployment. It adds no byte
encoding, checksum, filesystem, or flush/fsync proof, no `CompleteMediation` or
protected-handle theorem, no caller-visible `ReturnResult`, and no multi-request
or global-effect linearizability or liveness result.

### T6-A1: executable protocol refinement

T6-A1 supplies an explicit operational refinement for the T6-A0
`EnsureMember` semantics. The adapter machine observes the global WAL/Broker
event stream and adds two adapter-only steps: `ServiceLinearize(attempt)` and
`EnvironmentAdd(resource)`. Its state tracks the initial and current membership
sets, environment additions, linearized and failed attempts, the complete
observed global trace, its request-local physical projection, the active
attempt, and an `Online`/`Crashed`/`Recovering` mode. Silent adapter-only steps
are erased by `a1_global_trace`; every observed global event is preserved
exactly.

The transition guards make classification operational. An invocation must be
online, canonical, positive, within budget, unique for its attempt, and issued
with no active attempt. A Success must answer the active attempt after that
attempt has linearized and must carry `Value{id=1}`. A Failure must answer the
active attempt before it has linearized, and a failed attempt cannot linearize
later. A service linearization requires a prior undelivered, nonfailed
invocation and inserts `target(r)`. Environment steps may add only nontarget
resources. Crash clears the active attempt, and the observed recovery events
move the machine through its explicit recovery modes.

The service-linearization guard deliberately does not require the local adapter
mode to be Online or the attempt to remain in the volatile active slot. This
models a remote request that was invoked before a local crash and can still
linearize afterward. The required provenance is instead the durable physical
condition: the attempt was invoked, has no delivery, has not already
linearized, and has not failed. A production transport refinement must justify
this late-linearization behavior or prove stronger cancellation semantics.

The machine-checked `a1_service_linearize_step_has_remote_provenance` theorem
exports this boundary directly: every service-linearization step starts in the
named pending-remote condition, inserts the target, records the attempt as
linearized, and leaves both observed global and physical history unchanged.

The inductive invariant proves exact global and request-local history
projections, request locality, canonical invocation payloads, positive unique
ordered attempts, observation classification, linearization provenance, and
the exact set equation

```text
members = initial_members union environment_additions
          union ({target(r)} if any attempt linearized else empty).
```

Thus `ensure_member_exec_derives_adapter_rely` derives the complete T6-A0
`AdapterRely` predicate from every finite adapter-machine execution. The
composition theorem `ensure_member_executable_wal_terminal_refines` needs only
an adapter execution, exact equality between its observed global trace and a
typed-WAL execution, WAL execution, and a selected terminal. It obtains
`AdapterRely`, then concludes `Refines` and
`PerRequestEffectRefinement` through the already verified T6-A0 closure.

The premise-free T6-A1 witness couples 32 adapter events, including one silent
service linearization, to exactly 31 global WAL events and 32 WAL
configurations. Seven full, acknowledged Journal records survive in order:

```text
Authorize, Prepare, Arm, Start(1), Start(2),
Outcome(2, Failure, start_ref=5),
Unknown(attempt=Some(2), NonConclusiveFailure, evidence_ref=6).
```

Its physical history is exactly

```text
Invoke(1, journal_cut=4, ack_cut=4),
Success(1, Value{id=1}, journal_cut=4),
Invoke(2, journal_cut=5, ack_cut=5),
Failure(2, journal_cut=5).
```

Attempt 1 is the sole service linearization. Its Success is delivered but not
journaled before the crash. After `BeginScan`, `FinishScan`, `TruncateTail`,
`BeginRecover`, and `FinishRecover`, the durable four-record prefix permits
`Start(2)`. Attempt 2 fails without linearizing, its Failure is persisted, and
the terminal record is `Unknown(NonConclusiveFailure)`. The exact package proves
`AdapterRely`, `Refines`, per-request effect refinement, one abstract effect and
not zero, and that terminal Fail is impossible because not every invocation
failed. `t6_a1_executable_crash_retry_nonvacuity` inhabits the combined
operational and semantic package without premises.

The public `a1_retry_has_explicit_crash_recovery_shape` theorem additionally
fixes the concrete event ordering itself, including Crash, scan/truncation,
recovery, the three-step durable `Start(2)` append, `Invoke(2)`, and
`Failure(2)`. The crash/retry claim therefore does not depend only on Journal
or physical projections that erase those control events.

The retained T6-A1 run verifies 42/42 registered targets. T6-A1 verifies 916
obligations with zero errors, 52 beyond T6-A0; the dependency-aware
non-duplicated total is 956 and the sum of all target obligations is 20,867.

Here executable denotes a mechanized operational adapter/service model and a
reachable execution of that model coupled to the typed WAL. It is not a proof
of production Rust adapter code, network behavior, or the remote membership
service. Byte/fsync persistence, complete mediation, protected-handle
exclusivity, caller-visible `ReturnResult`, multi-request linearizability,
least privilege, and liveness remain outside this checkpoint.

## 4. Abstract effect summary

For adapter class `c`, let

```text
Effects(c, eta_r) subseteq {0, 1}
```

be the possible number of abstract mutating effects represented by the
history. The set contains both `0` and `1` when the effect cannot be determined.

### Read-only

```text
Effects(ReadOnly, eta_r) = {0}
```

Every invocation preserves the protected abstract state. Repeated reads may
return different values if the environment changes concurrently. A committed
result must equal one observed successful result; result stability requires an
additional snapshot or version contract.

Read-only is relative to the chosen abstract state. Audit logs, billing, rate
limits, or access counters must be included in the abstract state if they are
security-relevant effects.

### Idempotent

Let the request denote a state transformer `f_r`. The adapter must prove

```text
f_r(f_r(x)) = f_r(x)
```

for every state satisfying its precondition and rely condition. Under external
interference, the proof must establish observational equivalence to one
application rather than apply this equation without qualification. Then:

```text
Success in eta_r                         => Effects = {1}
no Success and uncertain outcome         => Effects = {0, 1}
only definitive Failure events           => Effects = {0}
no invocation                             => Effects = {0}
```

Different physical invocations may return different transport-level results.
A definitive failure after an earlier success, unresolved invocation,
ambiguity, or invalid result does not establish that no effect occurred. The
broker must commit a known success, reconcile the state, or return `Unknown`;
it must not record a clean logical failure.

### Deduplicated

Every physical invocation carries the same stable idempotency key `key(r)`.
The current abstract model assumes `key(r)` is derived injectively from the
adapter namespace and the broker-generated request identifier; the concrete
Journal `Prepared` record must contain its encoding or digest, and the WAL must
preserve that field exactly.
The remote service must atomically associate that key with one execution and a
memoized terminal result. Retries return the same terminal outcome and value.
If the memoized response is received but fails local validation, every replay
must carry the same rejected payload; it cannot later become `Success` or
`Failure` under the immutable adapter and schema.

```text
Success in eta_r                         => Effects = {1}
Failure in eta_r                         => Effects = {0}
only uncertain or unresolved calls        => Effects = {0, 1}
no invocation                             => Effects = {0}
```

A history containing both `Success` and `Failure` for the same key violates
the deduplication contract. So does a history combining `InvalidResult` with
either status, or two different invalid payloads. A failure following ambiguity
is conclusive only because the service promises that it is the memoized
terminal result for the key, not merely the result of the most recent network
attempt.

### Uncontrolled

The broker permits at most one `Invoke` event:

```text
Success                                  => Effects = {1}
Failure                                  => Effects = {0}
Ambiguous or InvalidResult               => Effects = {0, 1}
no invocation                            => Effects = {0}
```

After persisted ambiguity or a crash in the armed state, the logical outcome
is normally `Unknown`. A conclusive failure already present in the durable
attempt log is repaired as `Failed` during gated recovery; an unpersisted
failure delivery is not sufficient. Otherwise a second physical invocation is
forbidden.

## 5. Logical-outcome refinement

For a mutating request, the broker's terminal state must satisfy:

```text
Committed  => Effects(c, eta_r) = {1}
Failed     => Effects(c, eta_r) = {0}
Unknown    => no exact effect-count claim
```

For a read-only request, `Committed` means that the committed return value
refines one successful observation; it does not imply a mutation.

Per-internal-request logical at-most-once completion is consequently different
from physical exactly-once: a committed request has one abstract commit-log
entry, while an idempotent or deduplicated adapter may contain multiple
physical `Invoke` events.

## 6. Example sequence

T6-A1 now mechanizes the previously semantic-only mixed sequence as a reachable
adapter/WAL execution. Suppressing record-append substeps, its observable
control flow is:

```text
Invoke(1), Success(1), Crash, recover, Invoke(2), Failure(2)
```

The full adapter projection erases the crash and recovery events and is exactly
`Invoke(1), Success(1), Invoke(2), Failure(2)`. The operational machine also
contains one silent `ServiceLinearize(1)` between the first invocation and its
Success. There is no `ServiceLinearize(2)`. Consequently, from an initially
empty membership set, the post-state contains `target(r)` and satisfies
`OneEffect` but not `ZeroEffect`.

The first attempt starts under the four-record durable prefix
`Authorize, Prepare, Arm, Start(1)`. Its successful response is delivered but
no `Outcome(1,Success)` is appended before the crash. Recovery scans and
retains that prefix, then appends `Start(2)`. Attempt 2 uses
`journal_cut=ack_cut=5`, delivers Failure, and records
`Outcome(2,Failure,start_ref=5)`. The final append is
`Unknown(Some(2),NonConclusiveFailure,evidence_ref=6)`.

This terminal is forced by the distinction between current durable evidence
and the full physical history. Commit lacks a durable successful Outcome.
Idempotent Fail is also unavailable: its compatibility rule requires every
physical invocation to have a Failure delivery, but attempt 1 delivered
Success, so `all_invocations_failed` is false. Attempt 2's definitive local
Failure therefore does not establish zero effect for the whole request. The
legal terminal is Unknown, while the external effect is exactly one insertion.

The witness contains 31 global events and 32 WAL configurations; the coupled
adapter execution contains 32 events because service linearization is silent in
the global projection. This reachability and refinement result is about the A1
operational protocol model. It does not establish that production adapter,
network, or remote-service code implements that model.

## 7. Adapter proof obligations

Every adapter must discharge the following obligations:

1. **Request stability**: every retry sends the same abstract operation;
   retry-relevant serialization cannot change after `Prepared`.
2. **Scope preservation**: the concrete endpoint, resource, and arguments are
   exactly those approved by capability matching.
3. **Event classification**: `Failure` is emitted only when its no-effect or
   memoized-result meaning is justified; uncertain errors become `Ambiguous`.
4. **Attempt correlation**: each delivered response carries an authenticated or
   channel-bound attempt identifier; stale responses are rejected rather than
   relabeled as the current retry.
5. **Class law**: read-only preservation, transformer idempotence, remote
   deduplication, or uncontrolled at-most-once behavior is proved as declared.
6. **Outcome refinement**: each concrete response maps to an allowed abstract
   observation and result value.
7. **Persistence handoff**: the request, attempt identifier, outcome kind, and
   payload cannot change between `Deliver*` and `Persist*`; a crash before
   persistence yields an unresolved durable attempt rather than an invented
   outcome.
8. **Crash compatibility**: retry decisions after recovery use only durable
   request data and the declared class contract.

Deduplicated adapters additionally prove:

- stable and collision-free key derivation within the service's key domain;
- atomic key registration and operation execution;
- terminal-result persistence for at least the broker's retry lifetime;
- identical terminal status and complete accepted or rejected result payload
  on replay;
- namespace separation between principals or capabilities where required.

Idempotent adapters additionally prove that all relevant secondary effects are
idempotent. A nominally idempotent resource update that also sends a new email
or charges a payment on every call is not idempotent under the broker's
abstract state.

## 8. Model correspondence

`EffectBroker.tla` checks broker-side compatibility conditions under declared
adapter-environment assumptions through:

- `PossibleEffectCounts`, the executable form of `Effects`;
- `FailureIsConclusive`, which prevents unsound idempotent failure;
- `DeduplicatedOutcomeConsistent`, which excludes contradictory terminal
  results for one deduplication key;
- `DeduplicatedValueConsistent`, which covers both successful values and
  rejected invalid-result payloads;
- `AttemptLogBackedByHistory`, which permits reserved-but-unsent attempts and
  delivered-but-unpersisted outcomes while requiring every durable outcome to
  have physical backing;
- `TerminalEffectClassification`, which connects terminal broker states to the
  derived effect summary;
- `RecordUnknown`, which handles a definitive retry failure after an earlier
  idempotent success, unresolved attempt, ambiguity, or invalid result;
- `RecordObservedUnknown`, which gives an uncontrolled persisted ambiguity or
  invalid result its own terminal Journal record;
- `RetryAfterUncertainFailure`, which makes an idempotent reconciliation retry
  explicit instead of letting a crash unlock it;
- the `ReserveAttempt -> SendAttempt -> Deliver* -> Persist*` staging, which
  exposes the relevant crash windows;
- the durable attempt log, which prevents retry and gated-recovery decisions
  from depending on ghost history.

The deduplicated outcome guards restrict environment transitions and therefore
encode assumptions; TLC does not independently prove the remote service obeys
them. The model now includes two distinct invalid payloads so the bounded runs
exercise this replay constraint. The general obligation belongs to
`Refines_Deduplicated`.

The generic Journal model deliberately does not repeat these guards in its
storage-level `Outcome` rule. `EffectBrokerJournalRefinement` restricts the
realizable subset by conjoining each Outcome append with the corresponding
Broker `Persist*` action, so the adapter assumptions are checked at the caller
boundary. The standalone WAL-to-Journal proof is therefore a storage theorem;
the contextual composition theorem must preserve this caller rely condition.
The coupled product is bounded proof instrumentation. In the parameterized
contract, independently defined Journal and WAL runtimes are related to the
Broker under `AdmissibleContext`, while `AdapterRely` remains a separate
environment premise through T2--T6.

Successful response payloads, commit provenance, and deduplicated replay
equality are defined in [value-refinement.md](value-refinement.md).
