# Value-Level Result Refinement

## 1. Objective

Effect refinement establishes whether zero or one abstract mutation occurred.
Value refinement establishes that a value durably committed by the broker was
neither invented nor altered and satisfies the adapter's typed result
specification. Returning that value to the agent is a separate protocol outside
theorem V1.

The first value theorem is:

> If request `r` is committed with value `v` and source index `i`, then
> for the durable `commitAttempt(r)=a`,
> `externalHistory[i] = Success(r,a,v)`, `v` passed the finite model's result
> validation abstraction, and the durable commit log contains `(r,v)`.

This is a provenance theorem. Whether `v` truthfully describes the external
world is conditional on the adapter's semantic refinement proof.
`source index i` is proof-only ghost evidence; the stable implementation-facing
provenance identifier is the durable attempt `a` together with the terminal
Journal record. The concrete WAL must preserve and reconstruct that record.

## 2. Typed result interface

Each adapter defines:

```text
Output_r                 typed successful result domain
decode_r : Bytes -> Result<Output_r, DecodeError>
ResultSpec_r(x, x', v)   semantic result relation
```

`x` and `x'` are the relevant abstract external states before and after the
selected operation. A raw response may become a physical `Success(r,a,v)`
delivery only after decoding, schema validation, attempt correlation, and any
adapter-specific checks succeed. `PersistOK` subsequently records the accepted
classification in durable broker state.

A malformed response cannot become a successful observation. It produces an
`InvalidResult` history event carrying the rejected raw abstract value. For a
mutating operation, this event is effect-uncertain like `Ambiguous` unless a
separate adapter rule proves that no effect occurred.

The finite TLA+ oracle uses one shared set `AllowedResults`. It therefore checks
value provenance and global validation, not adapter-specific typing. Theorem V1
already replaces this abstraction with `result_pred(r,v)`; the Rust interface
will realize it with associated output types and request-indexed postconditions.

## 3. Delivery, persistence, and durable commit

After `DeliverOK(r,a,v)`, the broker has appended the physical success to
`externalHistory` and holds volatile received state:

```text
r in received
receivedKind[r] = Success
receivedValue[r] = v
receivedSource[r] = index of this Success event
receivedAttempt[r] = a
```

`PersistOK(r)` consumes that received token, appends durable
`Success(r,a)` to `attemptLog`, and creates the volatile observation used by
`Commit`:

```text
r in observedOK
observedValue[r] = v
observedSource[r] = receivedSource[r]
observedAttempt[r] = a
```

Both received and observed state are volatile. A crash after delivery but
before `PersistOK` leaves the physical `Success(r,a,v)` only in ghost history;
the durable attempt remains unresolved. A crash after `PersistOK` but before
`Commit` preserves the durable success classification but loses the value and
its volatile provenance. Recovery cannot inspect ghost history to recreate
`v`; the broker must re-observe a valid value or leave the operation unresolved.

The Journal layer is intentionally stronger: its successful `Outcome` record
stores `v`, so the concrete prefix retains information that `EffectBroker`
forgets. `EffectBrokerJournalRefinement` erases that extra value in
`ReplayCoupling` and still requires the live Broker `observedOK` token before a
Commit record may be appended. A replayed Journal success therefore cannot by
itself produce abstract completion after crash. This is concrete state
strengthening, not fabricated Broker knowledge.

`Commit(r)` atomically:

1. changes the durable phase to `Committed`;
2. stores `committedValue[r] = observedValue[r]`;
3. stores proof-only `commitSource[r] = observedSource[r]`;
4. stores durable `commitAttempt[r] = observedAttempt[r]`;
5. appends `(r, observedValue[r])` to the commit log;
6. clears the volatile observation and provenance.

No transition can commit a literal value supplied by the agent or synthesized
by recovery. The terminal data above is an abstract Journal record; a concrete
WAL implementation must refine its atomicity and recovery semantics.

## 4. Core value properties

### Event shape

Every external event has a value field. `Success` carries a validated result,
`InvalidResult` carries a rejected value, and `Invoke`, `Failure`, and
`Ambiguous` carry `NoResult`.

```text
event.kind = Success  => event.value in AllowedResults
event.kind = InvalidResult => event.value not in AllowedResults
all other kinds => event.value = NoResult
```

### Commit provenance

```text
phase[r] = Committed =>
    committedValue[r] in AllowedResults
    and externalHistory[commitSource[r]]
        = Success(r, commitAttempt[r], committedValue[r])
```

### Absence of fabricated terminal values

```text
phase[r] != Committed =>
    committedValue[r] = NoResult
    and commitSource[r] = 0
    and commitAttempt[r] = 0
```

### Commit-log agreement

```text
phase[r] = Committed =>
    exists i. commitLog[i] = (r, committedValue[r])
```

The request projection of the commit log remains duplicate-free.

### Volatile-state agreement

```text
r in received <=> receivedKind[r] != None
r in received <=> receivedSource[r] > 0
r in received <=> receivedAttempt[r] > 0
externalHistory[receivedSource[r]]
    = ExternalEvent(r, receivedAttempt[r], receivedKind[r], receivedValue[r])

r in observedOK <=> observedValue[r] != NoResult
r in observedOK <=> observedSource[r] > 0
r in observedOK <=> observedAttempt[r] > 0
externalHistory[observedSource[r]]
    = Success(r, observedAttempt[r], observedValue[r])
```

The received outcome has no durable outcome entry until `Persist*`; an observed
success has exactly one durable `Success` entry for its attempt. These
relations prevent a stale value from surviving after either volatile token is
cleared.

## 5. Adapter-specific value rules

### Read-only

Retries may return different valid values because the external state can
change between reads. A commit selects the currently observed value. To claim
snapshot consistency or monotonic reads, the adapter needs an additional
version, timestamp, or transaction relation.

### Idempotent

Repeated state transformations denote one abstract effect, but their returned
values need not be identical. The broker may commit any currently observed
value satisfying `ResultSpec_r` for a successful invocation. Applications that
require stable result replay need a stronger reconciliation or deduplication
contract.

### Deduplicated

All definitive replays for one stable key must return exactly the same status
and complete payload. This includes a response rejected by local validation:

```text
Success(r,a,v) in history and Success(r,b,w) in history => v = w
InvalidResult(r,a,x) and InvalidResult(r,b,y) in history => x = y
InvalidResult in history => no Success or Failure in history
```

The TLA+ transition relation assumes this remote replay law and
`DeduplicatedValueConsistent` checks that reachable histories remain compatible
with it. The adapter proof must independently establish equality of the
complete typed payload, not merely an identifier or selected fields.
The generic Journal storage rule does not impose this law. The checked coupled
refinement adds it as an explicit rely condition by pairing each Outcome append
with the Broker transition that enforces the deduplicated guards.
The parameterized proof expresses the same boundary with `AdapterRely` and an
independently defined runtime `Representation`, rather than embedding Broker
durable shadows in concrete state.

### Uncontrolled

At most one invocation occurs, so any committed value comes from that single
invocation. After ambiguity, no value is committed unless a separate
reconciliation protocol is introduced.

## 6. Example histories

Consider:

```text
Invoke(a1), Success(a1,v1), Crash, Invoke(a2), Success(a2,v2)
```

The first `Success` may have been delivered but not persisted, or persisted but
not committed. In both cases crash clears the only broker-held copy of `v1`.

| Adapter class | Valid when `v1 != v2`? | Permitted committed value |
|---|---|---|
| `ReadOnly` | Yes | `v2`, if it is the live observation at commit |
| `Idempotent` | Yes | `v2`, subject to `ResultSpec` |
| `Deduplicated` | No | Replays for one key must agree exactly |
| `Uncontrolled` | No | The second invocation is forbidden |

The broker cannot commit `v1` after the crash merely because it remains in the
ghost history. The volatile copy was lost.

## 7. Mechanized obligations

The executable model checks:

- `ExternalEventValueShape`;
- `AttemptLogBackedByHistory`;
- `DeduplicatedValueConsistent`;
- `ValueRefinementSound`;
- value-bearing `CommitLogSound`;
- causal agreement across `received`, `observedOK`, values, and exact source
  and attempt identifiers.

The source index is ghost evidence; the attempt identifier is durable broker
state. The abstract Journal must preserve that identifier together with the
committed value or canonical encoding so the audit record identifies the exact
accepted response that caused terminalization. The WAL must refine and recover
that Journal record.

The implementation proof must establish:

1. decoded values inhabit the adapter's Rust output type;
2. validation covers the complete payload used by the agent;
3. `DeliverOK` records the validated value and exact attempt without
   modification;
4. `PersistOK` appends the durable success classification and transfers the
   received value and provenance to a volatile observation without
   modification; a pre-persist crash creates no durable outcome, while a
   post-persist crash preserves the classification but loses the value;
5. `Commit` copies the validated volatile observed value without modification;
6. Journal serialization and WAL recovery preserve the committed value
   exactly;
7. deduplicated equality covers canonical typed values or canonical encoded
   bytes, with the choice stated explicitly;
8. returning a committed value to the agent reads only the durable terminal
   record for the matching request identifier.

Failure payloads and error-code refinement are deferred. The current TLA+
oracle checks successful-value provenance in bounded configurations and treats
failure only as a classified terminal status. T1 and T6 in the
[mechanization contract](mechanization-contract.md#10-theorem-statements) are
the parameterized value-provenance result and end-to-end proof target. T1
already proves durable commit provenance. T6-E0 now proves that, under the
Broker invariant and exact event projections, a terminal Commit carries an
exact strict-prefix successful Outcome reference and the unique matching
request-local delivery. This is causal `OutcomeEvidence`, not the adapter's
`result_spec` or one-effect relation. T6-C0 now derives
`BrokerOutcomeCompatible` for Commit from that exact successful delivery and,
for `Uncontrolled`, proves that it belongs to the only invoked attempt. This
is combined by T6-S0 with `OutcomeEvidence` into the frozen
`TerminalEvidenceAndCompatibility` conclusion. T6-S0 also transports that
conjunction through the atomic-Journal and typed-WAL final-state
representations, preserving the exact evidence records selected at the backend
boundary. It verifies 840 cumulative obligations, 6 beyond T6-C0; the
historical 40-target registry contains 880 dependency-aware non-duplicated
obligations with cumulative-target sum 19,064.

This transport does not establish `Refines`, `AdapterVerified`, value semantics
over the external pre/post-state, any adapter effect, a concrete adapter
instance or terminal `AdapterRely` witness, or broader security or liveness
claims. Those statements remain the exact boundary of the historical T6-S0
checkpoint.

### T6-A0 value and effect closure

T6-A0 proves the generic semantic step from T6-S0 to value/effect refinement:
Journal legality, `AdapterRely`, `AdapterVerified`, and
`TerminalEvidenceAndCompatibility` imply `Refines`, and the event,
atomic-Journal, and typed-WAL exports imply per-request effect refinement. Its
concrete `EnsureMember` adapter accepts a successful value only when its
identifier is 1 and the corresponding attempt is recorded as externally
linearized. The result specification additionally requires the post-state set
to contain the request's target resource. The set-insert postcondition is
idempotent, and the proof distinguishes a genuine one-effect state from zero
effect.

The premise-free package uses a nonempty 20-event typed-WAL execution with one
physical invocation, one successful delivery, a durable successful Outcome,
and a Commit carrying that value. It proves the concrete `AdapterRely`, exact
terminal evidence and compatibility, `Refines`, per-request effect refinement,
and one-effect/not-zero conclusion together. An auxiliary mixed
`Success`-retry-`Failure` lemma checks only adapter-level classification after
crash erasure; that sequence is not claimed to be a realizable Broker/WAL crash
trace.

At the historical T6-A0 checkpoint, all 41 registered targets passed. A
conservative definitional T1 accessor raises the current T6-S0 cumulative
closure from its historical 840 to 841 obligations. T6-A0 verifies 864
obligations with zero errors, adding 23 over that parent; that registry contained
904 dependency-aware non-duplicated obligations and summed 19,951 target
obligations.

### T6-A1 operational value/effect witness

T6-A1 derives the same `EnsureMember` semantic contract from an explicit
adapter/service execution rather than assuming `AdapterRely`. The operational
machine tracks external membership exactly and permits a silent
`ServiceLinearize(attempt)` only for a previously invoked, still-undelivered,
nonfailed remote attempt. The guard intentionally does not require the local
adapter to remain online or active: a request already sent to the service may
linearize after a local crash. Its invariant proves that the final external
pre/post-state and the projected physical history agree with the T6-A0
zero-or-one-effect interpretation.

The premise-free witness realizes `Invoke1, Success1, Crash, recover, Invoke2,
Failure2`. Attempt 1 performs the unique set insertion before its success is
lost at the Journal boundary; attempt 2 returns a nonconclusive failure without
linearizing. Consequently `all_invocations_failed` is false, the durable
terminal must be Unknown rather than Fail, and the external run satisfies the
one-effect branch but not the zero-effect branch. All 42/42 retained targets
pass. T6-A1 verifies 916 obligations with zero errors, 52 beyond T6-A0; the
registry contains 956 dependency-aware non-duplicated obligations and sums to
20,867 target obligations.

The T6-A1 adapter is executable as an explicit finite transition system with a
mechanized reachable execution; it is not verified production Rust, network,
or remote-service code. Its synthetic total configuration grants universal
resource and argument scope and therefore does not establish least privilege.
T6-A0/A1 prove no byte encoding or flush/fsync behavior, no
`CompleteMediation` or protected-handle property, no multi-request/global
linearizability, and no liveness. Neither T1 nor T6-A0 covers delivery to the
agent; caller-visible `ReturnResult` remains outside theorem V1.
