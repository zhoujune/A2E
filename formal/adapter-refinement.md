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
`AdapterVerified(P)` uniformly over every compatible well-formed `P`; an
end-to-end instance then assumes it for its selected `P`. T6 then
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

Consider:

```text
Invoke, Success, Crash, Invoke, Failure
```

The external projection is `Invoke, Success, Invoke, Failure`.
One broker-level realization is
`ReserveAttempt(r)` yielding `a1`, `SendAttempt(r,a1)`,
`DeliverOK(r,a1,v)`, and `Crash` before `PersistOK`, followed after recovery by
`ReserveAttempt(r)` yielding `a2`, `SendAttempt(r,a2)`,
`DeliverErr(r,a2)`, and `PersistErr(r)`. The first success remains physical
history but is absent from durable broker knowledge.

| Adapter class | Valid history? | Abstract mutation | Permitted broker outcome |
|---|---|---|---|
| `ReadOnly` | Yes | Zero | Commit an observed read result or record failure according to result policy |
| `Idempotent` | Yes | Exactly one | Reconcile/retry if budget remains, commit a reobserved success, or return `Unknown`; never clean `Failed` |
| `Deduplicated` | No | Contract violation | Adapter/service is outside its declared specification |
| `Uncontrolled` | No | Not applicable | Second `Invoke` violates broker safety |

This example demonstrates why idempotence alone is insufficient for reliable
result replay. It protects external state from duplicate mutation but does not
make contradictory responses impossible.

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
