# Mechanization Contract for Theorem V1

## 1. Status and theorem boundary

This document is the normative proof contract for the first parameterized
mechanization. The TLA+ modules remain executable finite models of the design;
where their finite constants or proof shadows differ from this document, this
document defines the unbounded theorem statement.

The historical retained T6-S0 terminal-bridge checkpoint verified 840 proof
obligations with zero errors, 6 beyond its T6-C0 parent. Across its 40 registered
targets, the dependency-aware non-duplicated total was 880 obligations and the
sum of all target obligations was 19,064. T6-A0 completed the first concrete
adapter-semantic closure at 864 cumulative obligations. T6-A1 completes the
first executable adapter-protocol refinement. Its target verifies 916
cumulative obligations with zero errors, 52 beyond T6-A0. Across the historical
retained 42-target A1 registry, the dependency-aware non-duplicated total is 956 and the
sum of all target obligations is 20,867. T6-M0 adds a first-class protected-
service execution and a closed-interface audit context. Its target
verifies 977 cumulative obligations with zero errors, 61 beyond T6-A1, and
derives protected-trace mediation and durable authorization provenance for the
concrete crash/retry execution. T6-P0 completes the
prefix-indexed execution product at 1,000 cumulative obligations with zero
errors, 23 beyond T6-M0. T6-X0 completes the storage-parametric contextual
lift and conditional single-request `EnsureMember` end-to-end theorem at 1,022
cumulative obligations with zero errors, 22 beyond T6-P0. The current retained
run passes all 45/45 registered targets, contains 1,062 dependency-aware
non-duplicated obligations, and sums to 23,866 target obligations; the
artifact-generated verification report records the exact source and tool
hashes. The one-obligation
increase in the
imported T6-S0 closure is a conservative definitional `PaperConfig` accessor
lemma added at T1 for the concrete package. The preceding
T6-C0 compatibility checkpoint verified 834 cumulative obligations across 39
targets and 874 non-duplicated obligations; T6-E0 verified 817 cumulative
obligations across 38 targets and 857 non-duplicated obligations; T6-D0
verified 799 cumulative obligations across 37 targets and 839 non-duplicated
obligations. T5-C0 remains
a historical boundary: it verified 783 cumulative obligations across 35
targets and 820 non-duplicated obligations. T4-C2 closes theorem T4 with
canonical finite forward contextual replacement. T5-S0 proves the exact
one-step committed-history laws, T5-E0
lifts them over arbitrary finite execution intervals, T5-R0 proves exact first-
`FinishRecover` episode equality, and T5-C0 exports those equalities through
T4's canonical contextual map. H1 proves the resulting premise/conclusion
package inhabited under a concrete total configuration and records the hardened
artifact evidence. Theorem T5 and H1 are complete. T6-D0 freezes the terminal
and adapter definition boundary, T6-E0 proves the generic Broker-side
`OutcomeEvidence` implication, and T6-C0 proves the corresponding
`BrokerOutcomeCompatible` implication under `AdapterRely`. T6-S0 combines
those conclusions and proves the frozen atomic-Journal and typed-WAL wrapper
statements. T6-A0 derives `Refines` from that conjunction and proves a concrete
idempotent `EnsureMember` adapter instance with a nonempty terminal typed-WAL
witness. T6-A1 gives that instance an operational adapter/service protocol,
derives `AdapterRely` from its transition invariant, and composes it with an
exact reachable crash/recovery/retry typed-WAL execution. T6-X0 composes the
adapter-to-WAL and canonical WAL-to-Broker prefix maps, transports the P0
product through an arbitrary admitting `ProgramContext<S>`, and proves the
conditional terminal theorem for the distinguished `EnsureMember` request.
The contextual terminal transport is adapter-polymorphic; generalization of
the operational/protected-state package to a request-indexed family of
executions remains outside theorem V1.

Theorem V1 is a safety and refinement theorem for arbitrary **finite**
executions. It assumes one globally serialized WAL writer and one globally
serialized executor slot. It proves properties of durable committed values;
delivery of a value to the agent (`ReturnResult`) is not in the transition
system. Persistence is a typed-frame Full/Torn contract with atomic
`TruncateTail`. Byte encoding, checksums, `fsync`, filesystem ordering, partial
physical truncation, and hardware durability lie below that contract.

External semantics are proved per broker-generated request under an adapter
rely condition. V1 does not claim a global linearization order for external
effects belonging to different requests, physical exactly-once execution,
liveness, multi-writer concurrency, or global external-state linearizability.

There is no logical `MaxJournalLength`. A finite execution may use any finite
number of records. A bounded implementation must expose `DiskFull` before
staging a record and stutter on all logical and adapter projections; silently
disabling append at a model bound is not a theorem-V1 behavior.

## 2. Mathematical vocabulary and immutable parameters

`Seq<T>` is the set of finite sequences over `T`; `epsilon` is empty,
`s ++ [x]` appends one element, `s <=p t` means prefix, and `prefix(s,n)` is the
first `n` elements. Indices are zero-based. `filter_map(f,s)` retains the
defined results of `f` in order. `Option<T>` has constructors `None` and
`Some(x)`. All maps mentioned below are total over their stated domain.

The Broker proof uses pairwise-disjoint nominal carrier sorts, each represented
as an unbounded natural-backed newtype. It quantifies over all values of these
sorts and over total maps on them; no carrier is finitely bounded by the model
checker. The current theorem is therefore countably encoded, not
representation-polymorphic over arbitrary or uncountable carrier types.
`ExternalState` and `InterferenceWitness`, used only by adapter refinement in
Section 9 and T6, remain arbitrary adapter-supplied types.

```text
RequestId R       = nominal Nat         CapabilityId K    = nominal Nat
Principal P       = nominal Nat         Tool T            = nominal Nat
Operation O       = nominal Nat         Resource U        = nominal Nat
Arguments A       = nominal Nat         Value V           = nominal Nat
InvalidValue VBad = nominal Nat         Digest D          = nominal Nat
StableKey Q       = nominal Nat         AdapterNamespace N = nominal Nat
ExternalState X   = arbitrary           InterferenceWitness I = arbitrary
AttemptId = Nat+  Lsn = Nat+            PhysicalIndex = Nat (zero-based)
```

The finite retry and status types are:

```text
RetryClass = ReadOnly | Idempotent | Deduplicated | Uncontrolled
Phase      = New | Authorized | Prepared | Armed
           | Committed | Failed | Unknown
Mode       = Online | Crashed | Recovering
ScanPhase  = Idle | Scanning | Scanned | Truncated

Observation = Success(V) | Failure | Ambiguous | InvalidResult(VBad)
UnknownReason = Exhausted | Recovery | NonConclusiveFailure
              | AmbiguousOutcome | InvalidResultReason
LogicalOutcome = Commit(AttemptId,V)
               | Fail(AttemptId)
               | UnknownOutcome(Option<AttemptId>,UnknownReason)
```

Immutable requests and capabilities are records:

```text
Request = { principal:P, tool:T, operation:O, resource:U, arguments:A,
            capability:K, retry_class:RetryClass, digest:D,
            adapter_namespace:N, stable_key:Option<Q>, max_attempts:Nat+ }

Capability = { principal:P, tool:T, operation:O,
               resource_pred:U -> Prop, argument_pred:A -> Prop,
               initial_budget:Nat }
```

`Cfg` contains total maps `request:R -> Request` and
`capability:K -> Capability`, a request-indexed predicate
`result_pred(r,v)`, and the adapter interpretation defined in Section 9.
Request identifiers and digests are immutable. For a deduplicated request,
`stable_key` is defined and injective in `(adapter_namespace,r)`; it is `None`
for the other classes in V1.

The theorem quantifies only over well-formed immutable configurations:

```text
CfgWellFormed(Cfg) :=
  (forall r. max_attempts(r) > 0)
  and (forall r.
         class(r)=Deduplicated
           <=> exists q. request(r).stable_key=Some(q))
  and (forall r.
         class(r)!=Deduplicated => request(r).stable_key=None)
  and (forall r1,r2,q.
         class(r1)=Deduplicated
         and class(r2)=Deduplicated
         and request(r1).adapter_namespace=request(r2).adapter_namespace
         and request(r1).stable_key=Some(q)
         and request(r2).stable_key=Some(q)
         => r1=r2)
```

Total-map domains, immutable fields, and the request-indexed result predicate
are part of the `Cfg` type rather than additional dynamic invariants.

Write `initial_budget(k)` for `capability(k).initial_budget`,
`max_attempts(r)` for `request(r).max_attempts`, and `class(r)` for
`request(r).retry_class`.

```text
CallDescriptor = { principal:P, tool:T, operation:O,
                   resource:U, arguments:A, digest:D,
                   adapter_namespace:N, key:Option<Q> }

CanonicalCall(r) = { every CallDescriptor field copied exactly from request(r) }
```

```text
Matches(r,k) :=
  request(r).capability = k
  and request(r).principal = capability(k).principal
  and request(r).tool = capability(k).tool
  and request(r).operation = capability(k).operation
  and capability(k).resource_pred(request(r).resource)
  and capability(k).argument_pred(request(r).arguments)

Valid(d,r,k) :=
  request(r).capability=k and Matches(r,k)
  and k notin d.revoked and d.remaining(k)>0
```

This replaces the singleton-capability `CHOOSE` used only to bound the TLA+
state space.

## 3. Typed Journal and replay

Journal references are LSNs. A reference in record at LSN `i` must be in
`1..i-1`. The record ADT is:

```text
JournalRecord =
  Authorize { r:R, k:K, digest:D }
| Revoke    { k:K }
| Prepare   { r:R, class:RetryClass, digest:D, key:Option<Q>, auth_ref:Lsn }
| Arm       { r:R, digest:D, key:Option<Q>, prepare_ref:Lsn }
| Start     { r:R, attempt:AttemptId, digest:D, key:Option<Q>, arm_ref:Lsn }
| Outcome   { r:R, attempt:AttemptId, observation:Observation,
              digest:D, key:Option<Q>, start_ref:Lsn }
| CommitRec { r:R, attempt:AttemptId, value:V, digest:D,
              key:Option<Q>, outcome_ref:Lsn }
| FailRec   { r:R, attempt:AttemptId, digest:D,
              key:Option<Q>, outcome_ref:Lsn }
| UnknownRec { r:R, attempt:Option<AttemptId>, reason:UnknownReason,
               digest:D, key:Option<Q>, evidence_ref:Lsn }
```

The replayed durable state is independent of process and storage state:

```text
DurableBroker = {
  phase:R -> Phase,
  remaining:K -> Nat,
  revoked:Set<K>,
  witness:R -> Option<K>,
  auth_log:Seq<(R,K)>,
  attempt_log:Seq<(R,AttemptId,AttemptKnowledge)>,
  commit_log:Seq<(R,V)>,
  committed:R -> Option<(AttemptId,V)>,
  failed_attempt:R -> Option<AttemptId>,
  unknown_reason:R -> Option<(Option<AttemptId>,UnknownReason)>
}

AttemptKnowledge = Started | Recorded(Observation)
```

`D0` maps every request to `New`, every capability `k` to its
`initial_budget`, all options and sets to empty, and all logs to `epsilon`.
`Replay(j)` is `fold(ApplyRecord,D0,j)`. Replay is total even for an illegal
sequence: define `pred0(n)=if n>0 then n-1 else 0`, and use `pred0` for the
budget update below. `StructuralEnabled` proves that the zero case is
unreachable in a legal Journal, so this off-domain totalization does not alter
legal behavior. `ApplyRecord` performs exactly these updates and leaves every
unlisted field unchanged:

| record | replay update |
|---|---|
| `Authorize(r,k,_)` | phase `Authorized`; remaining `k := pred0(remaining(k))`; witness `Some(k)`; append `(r,k)` to `auth_log` |
| `Revoke(k)` | insert `k` in `revoked` |
| `Prepare(r,...)` | phase `Prepared` |
| `Arm(r,...)` | phase `Armed` |
| `Start(r,a,...)` | append `(r,a,Started)` to `attempt_log` |
| `Outcome(r,a,o,...)` | append `(r,a,Recorded(o))` to `attempt_log` |
| `CommitRec(r,a,v,...)` | phase `Committed`; committed `Some(a,v)`; append `(r,v)` to `commit_log` |
| `FailRec(r,a,...)` | phase `Failed`; failed attempt `Some(a)` |
| `UnknownRec(r,a,q,...)` | phase `Unknown`; unknown reason `Some(a,q)` |

For a prefix `j`, define total Option-valued lookups `idx(j,tag,r)`,
`start_idx(j,r,a)`, and `outcome_idx(j,r,a)` as the greatest matching LSN, or
`None` when none exists. `JournalLegal` proves that every lookup class used as
a reference is unique, so greatest and unique coincide on theorem inputs. Define
`started(j,r)` as the number of `Start` records for `r`, `latest(j,r)` as
`Some(started(j,r))` when nonzero, and `outcome(j,r,a)` as the unique recorded
observation when present. `FailureConclusive(j,r)` holds when the latest
attempt has outcome `Failure` and, if the class is `Idempotent`, every started
attempt has outcome `Failure`. `DurablyUncertain(j,r)` holds when some started
attempt has no outcome or has `Success`, `Ambiguous`, or `InvalidResult`.
Define total `latest_evidence_lsn(j,r):Option<Lsn>` deterministically as the `Arm` LSN when no
attempt has started; otherwise it is the latest attempt's `Outcome` LSN when
that outcome exists, and that attempt's `Start` LSN otherwise. It may be `None`
off a legal/Armed input; every enabled Unknown requires it to be `Some` of the
record's reference.

The abstract Broker computes retry and recovery guards from its stored durable
state, never from proof ghosts. Define these total durable queries:

```text
d_started(d,r) :=
  count((r,_,Started), d.attempt_log)

d_outcome(d,r,a) :=
  the last o with (r,a,Recorded(o)) in d.attempt_log, or None

d_latest(d,r) :=
  if d_started(d,r)=0 then None else Some(d_started(d,r))

d_all_failed(d,r) :=
  d_started(d,r)>0
  and forall 1<=a<=d_started(d,r). d_outcome(d,r,a)=Some(Failure)

d_failure_conclusive(Cfg,d,r) :=
  d_started(d,r)>0
  and d_outcome(d,r,d_started(d,r))=Some(Failure)
  and (class(r)=Idempotent => d_all_failed(d,r))

d_uncertain(d,r) :=
  exists 1<=a<=d_started(d,r).
    d_outcome(d,r,a)=None
    or d_outcome(d,r,a)=Some(Success(_))
    or d_outcome(d,r,a)=Some(Ambiguous)
    or d_outcome(d,r,a)=Some(InvalidResult(_))
```

All functions remain defined for malformed durable states. For every
`CfgWellFormed(Cfg)` and legal Journal `j`, the replay bridge proves:

```text
d_started(Replay(j),r) = started(j,r)
d_outcome(Replay(j),r,a) = outcome(j,r,a)
d_all_failed(Replay(j),r) <=> AllAttemptsFailed(j,r)
d_failure_conclusive(Cfg,Replay(j),r) <=> FailureConclusive(j,r)
d_uncertain(Replay(j),r) <=> DurablyUncertain(j,r)
```

`StructuralEnabled(j,rec)` is the following exhaustive relation. All record
digests, classes, and keys must equal the immutable request fields, and every
named reference must point to the stated unique earlier record.

| record | additional guard in `Replay(j)` |
|---|---|
| `Authorize(r,k)` | phase is `New`; `Matches(r,k)`; `k` is not revoked; remaining `k > 0` |
| `Revoke(k)` | `k` is not revoked |
| `Prepare(r,auth_ref)` | phase is `Authorized`; reference is `Authorize(r,witness(r))` |
| `Arm(r,prepare_ref)` | phase is `Prepared`; reference is `Prepare(r)` |
| `Start(r,a,arm_ref)` | phase is `Armed`; `a = started(j,r)+1 <= max_attempts(r)`; no conclusive failure; reference is `Arm(r)`; if uncontrolled, `a=1` |
| `Outcome(r,a,o,start_ref)` | phase is `Armed`; `a=latest(j,r)`; no earlier outcome for `(r,a)`; reference is `Start(r,a)`; `Success(v)` requires `result_pred(r,v)` |
| `CommitRec(r,a,v,outcome_ref)` | phase is `Armed`; latest outcome is `Success(v)` for `a`; reference names it |
| `FailRec(r,a,outcome_ref)` | phase is `Armed`; `FailureConclusive(j,r)`; reference names the latest failure |
| `UnknownRec(r,a,q,evidence_ref)` | phase is `Armed`; the reason-specific guard below holds; reference names the latest evidence |

The reason-specific guards and references are exact. `Exhausted` requires
`attempt=latest(j,r)=Some(max_attempts(r))`, durable uncertainty, and
`latest_evidence_lsn(j,r)=Some(evidence_ref)`. `Recovery` requires an uncontrolled
request and no conclusive failure; before any Start it uses `attempt=None` and
the `Arm` LSN, and otherwise uses `attempt=latest(j,r)` and
`latest_evidence_lsn(j,r)=Some(evidence_ref)`. `NonConclusiveFailure` requires
`attempt=latest(j,r)`, a latest `Failure` that is not conclusive, and the equal
latest `Outcome` LSN. `AmbiguousOutcome` and `InvalidResultReason` require an
uncontrolled request, `attempt=latest(j,r)`, the corresponding latest outcome,
and its equal `Outcome` LSN. No other absent-attempt or evidence-reference form
is structurally enabled.

```text
JournalLegal(j) :=
  forall i < len(j).
    StructuralEnabled(prefix(j,i), j[i])
```

The atomic Journal deliberately checks structure, not physical delivery or a
live volatile value. Those caller obligations are exactly
`AdmissibleJournalTrace` below.

## 4. Typed WAL

```text
AppendControl = AppendIdle
              | AppendCalled(JournalRecord)
              | AppendLinearized(JournalRecord)

Frame = Full { lsn:Lsn, record:JournalRecord }
      | Torn { lsn:Lsn, record:JournalRecord }

TypedWAL = {
  cache:Seq<JournalRecord>, media:Seq<Frame>,
  acked_len:Nat,
  scan_phase:ScanPhase, scan_result:Seq<JournalRecord>
}
```

`Parse(media)` consumes exactly the longest initial sequence
`Full(1,r1),...,Full(n,rn)` and returns `[r1,...,rn]`; it stops at a Torn frame,
an unexpected LSN, or end of media. `FullFrames(j)` is
`[Full(i+1,j[i]) | i < len(j)]`.

`WALInvariant(w,mode,append)` is the conjunction:

1. frame LSNs equal their one-based positions; every Torn frame, if any, is
   the unique tail frame;
2. `JournalLegal(Parse(w.media))`;
3. in `Crashed` mode, `cache=epsilon`, `acked_len=0`, and
   `append=AppendIdle`;
4. outside `Crashed`, `append=AppendIdle` implies
   `cache=Parse(media)` and `acked_len=len(cache)`;
   `append=AppendCalled(rec)` implies
   `len(cache)=acked_len+1`, `last(cache)=rec`, and
   `Parse(media)=prefix(cache,acked_len)`; and
   `append=AppendLinearized(rec)` implies
   `cache=Parse(media)`, `len(cache)=acked_len+1`, and `last(cache)=rec`;
5. `prefix(cache,acked_len)=prefix(Parse(media),acked_len)` and
   `acked_len <= len(Parse(media))` whenever mode is not `Crashed`;
6. outside `Crashed`, `Parse(media) <=p cache`, their lengths differ by at
   most one, `len(media) <= len(cache)`, and every media frame carries the
   equal cache record at its position;
7. a non-`Idle` scan phase implies `mode=Crashed`; `Idle` and `Scanning` have
   empty `scan_result`; `Scanned` and `Truncated` have
   `scan_result=Parse(media)`;
8. `Truncated` implies `media=FullFrames(scan_result)`; whenever media has no
   Torn frame, `media=FullFrames(Parse(media))`.

Historical acknowledgment is deliberately absent from `TypedWAL`. It is
proof-only evidence derived from successful append-return events and lives in
`GhostEvidence` below. `acked_len` is only the concrete current-epoch control
watermark; crash may reset it without erasing proof that an earlier Invoke was
released by an acknowledged Start.

The transition relation is the following; unlisted fields are unchanged.

| action | guard and update |
|---|---|
| `Stage(rec)` | not Crashed; quiescent; structurally enabled; append `rec` to cache and change `AppendIdle` to `AppendCalled(rec)`; this is the WAL append-call event |
| `WalDiskFull(rec,q)` | optional capacity-limited extension, checked under the same quiescent pre-Stage record guard with `q=len(Parse(media))`; emit a failed normalized call/return and leave all runtime, storage, and ghost state unchanged |
| `WriteFull` | `AppendCalled(rec)`, no Torn tail, and `rec` remains structurally/runtime enabled; append `Full(len(media)+1,rec)` and enter `AppendLinearized(rec)` |
| `WriteTorn` | `AppendCalled(rec)`, no Torn tail, and `rec` remains structurally/runtime enabled; append `Torn(len(media)+1,rec)` and remain `AppendCalled(rec)` |
| `FinishTorn` | `AppendCalled(rec)` equals the Torn tail and `rec` remains structurally/runtime enabled; replace that tail by equal Full and enter `AppendLinearized(rec)` |
| `FlushAck` | `AppendLinearized(rec)` and `cache=Parse(media)`; set `acked_len=len(cache)`, enter `AppendIdle`, and emit a successful append return whose cut is `len(cache)` |
| `Crash` | not Crashed; preserve media; clear cache, append control, current-epoch acknowledgment count, and scan result; enter Crashed/Idle scan |
| `BeginScan` | Crashed/Idle to Scanning |
| `FinishScan` | Crashed/Scanning; store `Parse(media)` and enter Scanned |
| `TruncateTail` | Crashed/Scanned; atomically set `media=FullFrames(scan_result)` and enter Truncated |
| `AbortScan` | Crashed and non-Idle scan; clear scan result and enter Idle |
| `BeginRecover` | Crashed/Truncated with canonical media, Idle slot, and Idle append control; install `scan_result` in cache, set `acked_len` to its length, keep append control Idle, clear scan state, and enter Recovering |
| `FinishRecover` | Recovering with an Idle slot, quiescent WAL, and `RecoveryComplete(Cfg,Parse(media))`; enter Online |

`WriteFull` and `FinishTorn` are the only normal transitions that extend
`Parse(media)`; each adds exactly the `AppendCalled` record. `TruncateTail` changes
media to `FullFrames(Parse(media))` without changing the parse. Every other
action stutters on `Parse(media)`.

The completion actions recheck the record guard. This check is redundant on
reachable executions because no record-visible state changes between Stage and
completion, but it is required for the stated preservation theorem from an
arbitrary state satisfying `WALInvariant`: that invariant alone does not encode
the structural eligibility of the record stored in `AppendCalled`.

```text
WALQuiescent(w,append) :=
  append=AppendIdle
  and w.cache=Parse(w.media)
  and w.acked_len=len(w.cache)
  and w.scan_phase=Idle
```

The atomic Journal uses the same `AppendControl`: call changes Idle to Called,
linearization appends the record and changes Called to Linearized, and a later
successful return changes Linearized to Idle. The return is immediately
enabled but may be delayed. This explicit delay gives the WAL state after a
complete frame but before `FlushAck` an atomic-Journal counterpart.

## 5. Abstract, concrete, and ghost state

The single executor slot is:

```text
ExecSlot = IdleSlot
 | Ready(R,AttemptId)
 | InFlight(R,AttemptId)
 | Received(R,AttemptId,Observation)
 | ObservedSuccess(R,AttemptId,V)
 | ObservedFailure(R,AttemptId)
 | ObservedUnknown(R,AttemptId,UnknownReason)
```

The abstract state contains the shared append-interface control but no WAL
representation:

```text
BrokerState B = {
  durable:DurableBroker, slot:ExecSlot, mode:Mode,
  append:AppendControl
}
```

The implementation runtime is independently defined and contains no Broker
durable variables or replay shadow:

```text
Store = AtomicJournal { journal:Seq<JournalRecord> }
      | WALStore { wal:TypedWAL }

ConcreteRuntime C<S:Store> = {
  store:S, slot:ExecSlot, mode:Mode, append:AppendControl
}
```

The concrete implementation may compute `Replay(JournalView(C))`, but it does
not store a second `phase`, `commit_log`, or other abstract shadow.

Proof-only evidence is separate and cannot be inspected by a transition guard:

```text
PhysicalEvent =
  Invoke { r:R, attempt:AttemptId, call:CallDescriptor,
           journal_cut:Nat, ack_cut:Nat }
| Delivered { r:R, attempt:AttemptId, observation:Observation,
              journal_cut:Nat }

GhostEvidence G = {
  records:Seq<JournalRecord>,
  physical:Seq<PhysicalEvent>,
  ack_cuts:Seq<Nat>,
  acknowledged_prefix:Seq<JournalRecord>,
  slot_source:Option<PhysicalIndex>,
  commit_source:R -> Option<PhysicalIndex>
}
```

Journal LSNs are one-based; `PhysicalIndex` values are zero-based sequence
indices. Thus `1 <= lsn <= len(records)` addresses `records[lsn-1]`, while
`i < len(physical)` addresses `physical[i]`. `records` witnesses record order;
`physical` witnesses actual broker sends and
accepted deliveries. `ack_cuts` records the Journal length carried by every
successful append return, and `acknowledged_prefix` is the prefix ending at the
latest such cut. Both are historical proof evidence, not concrete WAL fields.
A successful `commit_source(r)=Some(i)` points to the exact
`Delivered(r,a,Success(v))` copied through Received and ObservedSuccess. Crash
clears `slot_source` but preserves all ghost histories and terminal sources.
Ghost fields may appear in invariants and postconditions, never in executable
branch conditions. The executable append/slot control flow releases a Ready
slot only by returning its linearized Start; `ReadyReleaseAgreement` below
relates that control fact to acknowledgment evidence.

`journal_cut` is set to `len(G.records)` when a physical event is appended. It
orders physical interaction against durable record linearization without
inventing a separate Authorize-event alphabet. An Invoke additionally stores
`ack_cut=len(G.acknowledged_prefix)` at that instant. Its Start reference must
already lie at or before `ack_cut`; a later successful return therefore cannot
retroactively justify an earlier physical invocation.

```text
JournalView(C) := C.store.journal                  if AtomicJournal
                Parse(C.store.wal.media)           if WALStore

alpha_commit_B(B) := B.durable.commit_log
alpha_commit_J(C_J) := Replay(JournalView(C_J)).commit_log
alpha_commit_W(C_W) := Replay(JournalView(C_W)).commit_log
JournalView(C_W) := Parse(C_W.store.wal.media)
```

## 6. Events, steps, executions, and projections

Every transition has one label from this ADT:

```text
AppendResult = AppendOk | AppendFull

Event =
  BrokerLinearize(JournalRecord)
| JournalAppendCall(JournalRecord)
| JournalAppendLinearize(JournalRecord)
| JournalAppendReturn(Nat)                 // successful journal_cut
| JournalDiskFull(JournalRecord,Nat)       // rejected call and current cut
| WalStage(JournalRecord)                  // WAL append call
| WalWriteFull(JournalRecord)
| WalWriteTorn(JournalRecord)
| WalFinishTorn(JournalRecord)
| WalFlushAck(Nat)                         // successful journal_cut
| WalDiskFull(JournalRecord,Nat)           // rejected call and current cut
| InvokeEvent(R,AttemptId,CallDescriptor,Nat,Nat)
                                              // journal_cut, ack_cut
| DeliverEvent(R,AttemptId,Observation,Nat)    // journal_cut
| IgnoreStale(R,AttemptId)
| RetryRelease(R)
| Crash
| BeginScan | FinishScan | TruncateTail | AbortScan
| BeginRecover | FinishRecover
```

`LinearizedRecord(e)` is the contained record for `BrokerLinearize`,
`JournalAppendLinearize`, `WalWriteFull`, and `WalFinishTorn`, and `None`
otherwise. `WalWriteTorn` does not linearize a record. A DiskFull event is one
rejected append call and return with no intervening linearization; the theorem
has no finite capacity, but this label specifies the required behavior of a
capacity-limited implementation.

An append return is the storage API's completion notification to the broker.
It is not `ReturnResult` and does not deliver a tool value to the agent.

The ADT constructors are disjoint, and an execution entry contains exactly one
label. Equal before/after states may occur under different explicit stutter
labels, but one step occurrence is never multiply classified. Authorization
is observed only by a linearized `Authorize` record; there is no second
authorization event whose ordering could disagree with the Journal.

A machine is `(State, Init, Step)`. Its typed configuration is
`Config_M={state:M.State, ghost:GhostEvidence}`, with
`Init:Config_M -> Prop` and
`Step:Config_M x Event x Config_M -> Prop`. For machine `M`, a finite execution
is a pair `tau=(configs,events)` satisfying:

```text
len(configs) = len(events)+1
M.Init(configs[0])
forall i < len(events).
  M.Step(configs[i], events[i], configs[i+1])
```

`Exec(M)` is exactly the set of such pairs. For
`0 <= n <= len(events)`, `prefix(tau,n)` retains configurations `0..n` and
events `0..n-1`. Hence, by definition, `tau in Exec(M)` implies every such
`prefix(tau,n)` is in `Exec(M)`.

The required trace projections are order-preserving concatenating maps.
Projections that emit at most one item per label are `filter_map` special
cases; a DiskFull label emits the two adjacent normalized append events below:

```text
AppendEvent = AppendCall(JournalRecord)
            | AppendLinearize(JournalRecord)
            | AppendReturn(AppendResult,Nat)

pi_append(tau) maps:
  JournalAppendCall(rec), WalStage(rec) -> AppendCall(rec)
  BrokerLinearize(rec), JournalAppendLinearize(rec),
  WalWriteFull(rec), WalFinishTorn(rec)
                                      -> AppendLinearize(rec)
  JournalAppendReturn(q), WalFlushAck(q)
                                      -> AppendReturn(AppendOk,q)
  JournalDiskFull(rec,q), WalDiskFull(rec,q)
                                      -> [AppendCall(rec),
                                          AppendReturn(AppendFull,q)]

pi_auth(tau) =
  Authorize(r,k) for linearized Authorize records,
  Revoke(k) for linearized Revoke records

pi_journal(tau) = every defined LinearizedRecord, in order

pi_wal(tau) = WalStage, WalWriteFull, WalWriteTorn, WalFinishTorn,
              WalFlushAck, WalDiskFull, Crash, BeginScan, FinishScan,
              TruncateTail, AbortScan, BeginRecover, FinishRecover

pi_physical(tau) = the PhysicalEvent values carried by all Invoke and Deliver
                   labels, in order

ProtectedInvocation = { r:R, attempt:AttemptId, call:CallDescriptor }
ProtectedTrace = Seq<ProtectedInvocation>

pi_invocations(tau) = each Invoke in pi_physical(tau), with proof cuts erased

CompleteMediation(tau,omega:ProtectedTrace) :=
  omega = pi_invocations(tau)

pi_adapter(tau,r) = filter the r events from pi_physical(tau)

pi_control(tau) = IgnoreStale, RetryRelease, Crash, BeginRecover,
                  and FinishRecover labels, in order

pi_logical(tau) = (r,Commit(a,v)), (r,Fail(a)), or (r,UnknownOutcome(a,q))
                  for each corresponding linearized record

pi_ack(tau) = the cuts q from AppendReturn(AppendOk,q) in pi_append(tau)

pi_append_io(tau) = pi_append(tau) with AppendLinearize events erased
```

Here `omega` denotes an independently generated deployment trace, not a trace
chosen to make the equality true. In T6-M0 it is instantiated by erasing proof
metadata from the accepted calls of a well-formed first-class
`M0ProtectedExecution`; eventwise coupling and execution induction derive the
equality. The two-argument predicate remains the legacy theorem interface,
while the protected execution premise supplies its semantic content.

Because `Crash` may interrupt either a called or a linearized append, the raw
`pi_append` sequence need not be one uninterrupted Call--Linearize--Return
prefix. Define the crash-reset protocol over the full labeled execution:

```text
AppendProtocolStep(c,e,c') :=
  e=JournalAppendCall(rec) or e=WalStage(rec):
      c=AppendIdle and c'=AppendCalled(rec)
| LinearizedRecord(e)=Some(rec):
      c=AppendCalled(rec) and c'=AppendLinearized(rec)
| e=JournalAppendReturn(q) or e=WalFlushAck(q):
      exists rec. c=AppendLinearized(rec) and c'=AppendIdle
| e=JournalDiskFull(rec,q) or e=WalDiskFull(rec,q):
      c=AppendIdle and c'=AppendIdle
| e=Crash:
      c'=AppendIdle
| otherwise:
      c'=c

AppendProtocolPrefix(tau) :=
  exists controls.
    len(controls)=len(tau.events)+1
    and controls[0]=AppendIdle
    and forall i<len(tau.events).
          AppendProtocolStep(controls[i],tau.events[i],controls[i+1])
```

Thus every maximal segment between Crash labels has a normalized append
projection that is a prefix of the serialized protocol. A DiskFull label emits
the complete adjacent `AppendCall(rec), AppendReturn(AppendFull,q)` segment.
A Crash aborts the current append epoch: a previously linearized record remains
in `pi_journal`, but no successful append return or acknowledgment is invented.

For a nonempty execution prefix `rho`, let `G_rho` be its last ghost state and
let `last_or_zero(epsilon)=0` and `last_or_zero(s)=last(s)` otherwise.
`TraceAgreement(tau)` means that, for every
`0 <= n <= len(tau.events)` and `rho=prefix(tau,n)`:

```text
G_rho.records = pi_journal(rho)
G_rho.physical = pi_physical(rho)
G_rho.ack_cuts = pi_ack(rho)
let q = last_or_zero(G_rho.ack_cuts) in
  q <= len(G_rho.records)
  and G_rho.acknowledged_prefix = prefix(G_rho.records,q)
```

Every successful append-return label with cut `q` additionally satisfies
`q=len(pi_journal(prefix(tau,i)))` immediately before that return step;
successful cuts are nondecreasing. At an Invoke step, its `journal_cut` equals
the current record length and its `ack_cut` equals the current acknowledged
prefix length. Thus `TraceAgreement` connects state invariants and source
indices to the labeled projections used by refinement, for every prefix rather
than only at termination.

`terminal(tau,r)` is the unique outcome for `r` in `pi_logical(tau)`, if one
exists. Uniqueness is a proved invariant, not an assumption.

## 7. Exact broker, WAL, representation, and context predicates

### 7.1 `BrokerInvariant`

Define the exact recovery guard over a legal Journal:

```text
UnsafeUncontrolledD(Cfg,d,r) :=
  d.phase(r)=Armed
  and class(r)=Uncontrolled
  and not d_failure_conclusive(Cfg,d,r)

RecoveryCompleteD(Cfg,d) :=
  forall r.
    not UnsafeUncontrolledD(Cfg,d,r)
    and not (d.phase(r)=Armed
             and d_failure_conclusive(Cfg,d,r))

UnsafeUncontrolled(Cfg,j,r) :=
  Replay(j).phase(r)=Armed
  and class(r)=Uncontrolled
  and not FailureConclusive(j,r)

RecoveryComplete(Cfg,j) :=
  forall r.
    not UnsafeUncontrolled(Cfg,j,r)
    and not (Replay(j).phase(r)=Armed and FailureConclusive(j,r))
```

For every legal `j`, the durable-query bridge gives:

```text
UnsafeUncontrolledD(Cfg,Replay(j),r)
  <=> UnsafeUncontrolled(Cfg,j,r)

RecoveryCompleteD(Cfg,Replay(j))
  <=> RecoveryComplete(Cfg,j)
```

Thus recovery may finish with retry-safe uncertain requests still Armed, but
not with an unsafe uncontrolled request or any conclusive durable failure. A
repair record makes its request terminal, so completion is expressed as the
absence of those Armed cases rather than as an Armed request simultaneously
having a terminal record.

`BrokerInvariant(Cfg,B,G)` is the conjunction of all clauses below, with
`j=G.records` and `d=Replay(j)`:

1. **Replay agreement:** `JournalLegal(j)` and `B.durable=d`.
2. **Budget conservation:** for every `k`,
   `d.remaining(k) + count(d.auth_log,(_,k)) = initial_budget(k)`.
3. **Authorization soundness:** each `Authorize(r,k)` at LSN `i` satisfies
   `Valid(Replay(prefix(j,i-1)),r,k)` and `r` is New in that replay. Each
   request has at most one authorization and its witness equals that `k`.
4. **Scope confinement:** if `not Matches(r,request(r).capability)`, then `r`
   is New and has no Start, physical Invoke, or commit entry.
5. **Attempt shape:** attempts for each request are exactly `1..started(j,r)`;
   each has one Start and at most one later Outcome referencing that Start.
6. **Physical causality:** for every `(r,a)`, there is at most one Invoke and
   one Delivered event; a delivery follows its unique Invoke. For an Invoke
   with `journal_cut=n` and `ack_cut=q`, `q<=n`, the cut `q` is in
   `G.ack_cuts`, and the unique Authorize and Start records for `(r,a)` occur
   in `prefix(G.records,q)`. For a Delivered event with cut `n`, its Invoke
   precedes it, and its matching durable Outcome, if any, has LSN greater than
   `n`. Every durable Outcome has exactly one such earlier equal Delivered
   event. The converses need not hold.
7. **Retry discipline:** uncontrolled requests have at most one Start and one
   Invoke. Other retries do not exceed `max_attempts(r)` and occur only when
   no conclusive failure exists.
8. **Slot agreement:** the slot's request is Armed; its attempt is the latest
   started attempt; Ready has a Start and no Invoke, InFlight has its Invoke
   and no delivery, Received has its exact delivery, and each Observed token
   has its exact durable Outcome. At most one slot exists globally.
9. **Terminal uniqueness:** each request has at most one terminal record;
    terminal records are mutually exclusive; the request projection of
    `commit_log` is duplicate-free; phase, committed value, failure attempt,
    unknown reason, and terminal record agree exactly. Concretely, for every
    `r`, `phase(r)=Committed` iff the unique terminal record is
    `CommitRec(r,a,v,...)`, `committed(r)=Some(a,v)`, and both other terminal
    option fields are `None`; the analogous biconditionals hold for
    `Failed`/`FailRec`/`failed_attempt` and
    `Unknown`/`UnknownRec`/`unknown_reason`. In every nonterminal phase all
    three terminal option fields are `None`, and `commit_log` is exactly the
    ordered projection of Commit records.
10. **Value provenance:** if `d.committed(r)=Some(a,v)`, then
    `result_pred(r,v)`, `G.commit_source(r)=Some(i)`, and
    `G.physical[i]=Delivered(r,a,Success(v))`. Noncommitted requests have no
    commit source.
11. **Failure provenance:** `Failed` names the latest attempt `a`, its durable
    outcome is `Failure`, `FailureConclusive(j,r)` holds, and there exists a
    (by clause 6 unique) zero-based physical index `i` and cut `n` such that
    `G.physical[i]=Delivered(r,a,Failure,n)` and the matching durable Outcome
    has LSN strictly greater than `n`.
12. **Crash shape:** `B.mode` other than Online implies `B.slot=IdleSlot`, and
    `G.slot_source=None`. `Crashed` additionally implies
    `B.append=AppendIdle`.
13. **Append interface shape:** `AppendCalled(rec)` implies
    `StructuralEnabled(j,rec)` and a defined
    `DurableSlotUpdate(Cfg,B.durable,B.mode,B.slot,rec)`;
    `AppendLinearized(rec)` implies there exist `j0` and `slot0` such that
    `j=j0++[rec]`, `StructuralEnabled(j0,rec)`,
    `B.durable=ApplyRecord(Replay(j0),rec)`, and
    `DurableSlotUpdate(Cfg,Replay(j0),B.mode,slot0,rec)=Some(B.slot)`.

The inductive strengthening `ReadyReleaseAgreement(B,G)` also holds:

```text
ReadyReleaseAgreement(B,G) :=
  forall r,a. B.slot=Ready(r,a) =>
    exists s. start_idx(G.records,r,a)=Some(s)
      and 1 <= s <= len(G.records)
      and (s <= len(G.acknowledged_prefix)
           or (exists rec.
                 B.append=AppendLinearized(rec)
                 and rec is Start(r,a,...)
                 and s=len(G.records)
                 and G.records[s-1]=rec))
```

Consequently,
`Ready(r,a)` together with `AppendIdle` implies that the matching Start was
covered by an earlier successful append return. This is a historical safety
fact, not an executable guard or a ghost value read by the runtime;
`BrokerInvariant` includes it as part of clause 13.

Recovery-source preservation is a relational step obligation rather than a
single-state conjunct of `BrokerInvariant`. If an enabled
`BrokerLinearize(rec)` step begins in `Recovering`, then `rec` is a conclusive
`FailRec` or an uncontrolled `UnknownRec` with reason `Recovery`, and
`G'.commit_source = G.commit_source`. In particular, recovery repair preserves
every existing commit source and cannot define a new one. This lemma is proved
alongside invariant preservation and is used by T1 and T5.

### 7.2 `WALInvariant`

`WALInvariant` is exactly the eight-clause predicate in Section 4, instantiated
as `WALInvariant(C.store.wal,C.mode,C.append)`.

`InvocationsAcknowledged(G)` means that `G.acknowledged_prefix <=p G.records`;
every `q` in `G.ack_cuts` is at most `len(G.records)`; and every ghost
`Invoke(r,a,...,ack_cut=q)` has `q` in `G.ack_cuts` and its matching Start at an
LSN at most `q`. `TraceAgreement` strengthens this state predicate with the
temporal fact that the named successful return preceded the Invoke. The caller
rule makes the predicate inductive for both backends even though WAL crash
resets concrete `acked_len`.

### 7.3 `Representation`

```text
Representation(Cfg,C,G,B) :=
  G.records = JournalView(C)
  and B.durable = Replay(G.records)
  and B.slot = C.slot
  and B.mode = C.mode
  and B.append = C.append
  and BrokerInvariant(Cfg,B,G)
  and (C.store is AtomicJournal
       or WALInvariant(C.store.wal,C.mode,C.append))
  and InvocationsAcknowledged(G)
  and SourceAgreement(C,G)
```

`SourceAgreement(C,G)` means `slot_source=None` for Idle, Ready, and InFlight;
for `Received(r,a,o)` it points to exactly `Delivered(r,a,o)`; for each
Observed slot it points to the equal delivery and `JournalView(C)` contains
the equal Outcome; and every defined `commit_source(r)` points to
`Delivered(r,a,Success(v))` where replayed committed state is `Some(a,v)`.
No other source entries are defined.

This is a relation, not an embedding of `B` in `C`. In particular, concrete
WAL state has no `shadowJournal`, Broker durable fields, or historical
acknowledgment log. `B.append` is storage-interface control, not a WAL
representation: call and return stutter on durable Broker state, while the
linearization step updates the Journal, Broker durable state, and caller slot
together.

### 7.4 Operational trace admissibility and context boundary

The operational caller rules are clauses 1--10 and 13 below; `C` and `G`
denote a step's preconfiguration runtime and ghost evidence. Clauses 11 and 12
are context/deployment hyperproperties rather than properties of one trace.

1. a record offered to either storage backend satisfies
   `StructuralEnabled(JournalView(C),rec)`;
2. every ordinary record call is made only in `Online` mode. Start is offered
   only with `IdleSlot`; Outcome only from `Received(r,a,o)` with the identical
   observation; Commit only from `ObservedSuccess(r,a,v)`; ordinary Fail only
   from the matching `ObservedFailure`; Ambiguous/InvalidResult Unknown only
   from the matching `ObservedUnknown`; NonConclusiveFailure Unknown only from
   the matching `ObservedFailure`; and Exhausted Unknown only from `IdleSlot`
   with its durable reason guard;
3. in `Recovering`, the only record calls are a conclusive Fail repair or an
   uncontrolled Recovery Unknown, both from `IdleSlot`. `FinishRecover`
   requires `RecoveryComplete(Cfg,JournalView(C))`;
4. the atomic backend obeys
   `JournalAppendCall -> JournalAppendLinearize -> JournalAppendReturn`; the
   return is immediately enabled after linearization but may be delayed. The
   WAL call is `WalStage`, its linearization is either `WalWriteFull` or
   `WalFinishTorn` after `WalWriteTorn`, and its return is `WalFlushAck`. Both
   protocols carry the same record through
   `AppendCalled(rec)` and `AppendLinearized(rec)` without alteration;
5. a successful append return carries the current Journal length `q`, appends
   `q` to `G.ack_cuts`, and sets
   `G.acknowledged_prefix=prefix(G.records,q)`. No other transition changes
   either field, and DiskFull does not create acknowledgment evidence;
6. an Invoke is allowed only online, with `Ready(r,a)`, `C.append=AppendIdle`,
   a quiescent store, and the matching Start in `G.acknowledged_prefix`. It
   atomically changes the slot to InFlight and appends the matching ghost
   Invoke with `CanonicalCall(r)`, the current record-history length as
   `journal_cut`, and the current acknowledged-prefix length as `ack_cut`.
   The mechanized runtimes share the guard `StartCoveredByCut(G.records,r,a,
   ack_cut)`; T2-R proves that it places the same Start in
   `prefix(G.records,ack_cut)`. Journal legality supplies uniqueness of that
   Start, so this guard does not select a different attempt witness;
7. an accepted Deliver is allowed only online, with `C.append=AppendIdle`, a
   quiescent store, and the exact current `InFlight(r,a)`; it changes the slot
   to Received and appends
   the matching ghost delivery with the current record-history length as
   `journal_cut`. A mismatched response can only `IgnoreStale`
   and stutters on state and ghost histories;
8. `JournalAppendLinearize`, `WalWriteFull`, or `WalFinishTorn` applies the
   record's runtime slot update atomically with extending the Journal view.
   Append call and return preserve the slot and logical Journal projection;
9. Invoke, accepted Deliver, retry release, and the next append call require
   append Idle; WAL operational actions additionally require
   `WALQuiescent(C.store.wal,C.append)`.
   Raw transport arrival is not an event and may be buffered;
10. Crash is fail-stop: it preserves the durable Journal view, record/physical/
    acknowledgment histories, terminal commit sources, and WAL media; it
    clears the transient `slot_source`, executor slot, append control, and
    volatile WAL fields, and enters Crashed. Scan, truncation, and abort keep
    the WAL runtime Crashed.
    WAL `BeginRecover` requires Truncated and installs exactly `Parse(media)`;
    recovery may crash again;
11. the context is storage-parametric: an event-synchronized choice depends
    only on its own state, the complete masked pre- and post-step
    `ContextView`s defined below, and the nonempty normalized delta. The
    immutable request map is carried in both endpoint views. This permits an
    immediate context reaction to the post-event masked state, including the
    `Quiescent` slot revealed by append return. The context cannot observe
    append linearization, raw append control, WAL frames, Torn contents, scan
    internals, or proof ghosts;
12. all protected tool handles made available to the context are
    broker-exclusive, so the context cannot invoke one except through the
    broker interface. Equality with the deployment's external protected-handle
    trace is the separate `CompleteMediation(tau,omega)` premise of T6, not a
    free variable or hidden premise of `StorageParametricContext` or T4-C1.
    T4-C1 alone does not prove handle exclusivity. T6-M0 supplies one concrete
    protected-service machine and audit context whose closed alphabets contain
    no independent protected-call or target-mutation action. It does not model a
    handle-ownership object; arbitrary contexts and production deployments still
    require a separate refinement argument;
13. the slot and append protocol are globally serialized. Each of
    `JournalDiskFull` and `WalDiskFull` denotes a normalized append Call
    followed immediately by
    `AppendReturn(AppendFull,q)`, performs no linearization, preserves state and
    all non-append projections, and is visible to the context as a failed
    append return.

For T4-C1 and T4-C2, caller observation is one ordered alphabet rather than a raw
`GlobalEvent` or an unordered tuple of projections:

```text
ContextEvent ::=
    AppendCall(rec)
  | AppendReturn(result,cut)
  | Invoke(r,a,call)
  | Deliver(r,a,observation)
  | IgnoreStale(r,a)
  | RetryRelease(r)
  | Crash
  | BeginRecover
  | FinishRecover
```

`ContextDelta(e):Seq<ContextEvent>` is defined eventwise. `WalStage` and
`JournalAppendCall` produce one `AppendCall`; `WalFlushAck` and
`JournalAppendReturn` produce one successful `AppendReturn`; and each WAL or
Journal `DiskFull` event produces the two-element sequence `AppendCall` then
`AppendReturn(Full,cut)` in the same runtime step. Invoke, Deliver, IgnoreStale,
RetryRelease, Crash, BeginRecover, and FinishRecover produce their corresponding
singleton. Invoke erases `journal_cut` and `ack_cut`, and Deliver erases
`journal_cut`: these are proof evidence, not context observations.
`BrokerLinearize`, `JournalAppendLinearize`, `WalWriteFull`,
`WalWriteTorn`, `WalFinishTorn`, BeginScan, FinishScan, TruncateTail, and
AbortScan produce the empty sequence. Define `ContextTrace(tau)` by flattening
these deltas in runtime order.

The context may additionally inspect only the following masked runtime view:

```text
ContextRuntimeView(C) =
  match C.append {
    Idle            => Quiescent(C.mode,C.slot),
    Called(rec)     => AppendPending(C.mode,rec),
    Linearized(rec) => AppendPending(C.mode,rec)
  }
```

Thus a hidden append linearization cannot reveal either the `Called` versus
`Linearized` phase or the slot update performed at linearization. A visible
append call changes `Quiescent` to `AppendPending`; a successful return changes
`AppendPending` to the updated `Quiescent` state. Every accepted empty-delta
backend step preserves this masked view. The prefix view is:

```text
ContextView(tau,i) = {
  requests: Cfg.request,
  history: ContextTrace(prefix(tau,i)),
  runtime: ContextRuntimeView(tau.configs[i])
}
```

The normalized append-I/O projection is recoverable exactly from
`ContextTrace`; `pi_ack` is redundant because every successful return already
carries its cut. The cut-erased Invoke and Deliver observations deliberately do
not reconstruct raw `pi_physical`. Separate equality of normalized projections
is not itself the contextual theorem because it forgets ordering between
channels. The context never receives capabilities, budgets, result predicates,
raw Journal or WAL state, append control, `pi_wal`, ghost evidence, proof cuts,
protected handles, or hidden-step counts.

The operational clauses are the rely condition missing from the generic
Journal storage model; they exclude syntactically legal but
broker-unrealizable runtime traces.

For a finite `tau_J in Exec(JournalRuntime(Cfg))`, define
`AdmissibleJournalTrace(Cfg,tau_J)` to mean that every prefix step satisfies
clauses 1--10 and 13, instantiated with the atomic-Journal branches of those
rules. Define `AdmissibleWALTrace(Cfg,tau_W)` analogously for a finite
`tau_W in Exec(WALRuntime(Cfg))`, using the WAL branches. These are trace
predicates; neither includes storage parametricity or protected-handle
exclusivity.

The current T2 mechanization uses a closed relational `JournalRuntimeStep` that
already incorporates clauses 1--10 and 13, so its `Exec` predicate implies
`AdmissibleJournalTrace`; the explicit premise is retained in the exported
paper theorem. T4-C1 now reconstructs each backend execution structurally
inside its plugged predicate and proves erasure to the corresponding closed
`Exec`. T4-C2 constructs the canonical plugged Journal and Broker executions
along the composed weak simulation and proves exact context-state and endpoint-
view equality at every canonical mapped prefix.

T4-C1 represents a program context over one shared state type `S` by arbitrary
relational sets, not by a deterministic context function:

```text
ContextInitial<S> = { view:ContextView, state:S }
ContextTransition<S> = {
  before:S, view:ContextView, delta:Seq<ContextEvent>,
  after_view:ContextView, after:S
}
ProgramContext<S> = {
  initial:ISet<ContextInitial<S>>,
  transitions:ISet<ContextTransition<S>>
}
```

A visible transition receives the context state, the complete masked pre- and
post-step `ContextView`s, and the nonempty ordered delta. It receives no raw
event, backend identity, or concrete machine state. This permits an arbitrary
context to react synchronously to state exposed by a visible return, including
the `Quiescent(mode,slot)` view revealed after `AppendReturn`, without exposing
the hidden append linearization. A hidden step is accepted only when the
complete post-view equals the pre-view and the context state stutters exactly.
Autonomous context steps between machine events remain outside T4-C1.

`StorageParametricContext(Cfg,Ctxt)` is the exact clause-11 contract. It
requires (1) at least one admitted state at the fixed initial view, (2) every
admitted initial entry to have exactly that view, and (3) every admitted
transition's pre- and post-views to contain exactly `Cfg.request` and its delta
to be nonempty and equal to `ContextDelta(e)` for some global event. The two
backends use the same state type `S`, with exact equality as context-state
correspondence; equal endpoint views and deltas therefore transfer transition
membership definitionally. No empty initial relation can satisfy the contract.

T4-C1 defines separate structural `PluggedWalExecution<S>`,
`PluggedJournalExecution<S>`, and `PluggedBrokerExecution<S>` products. Each
has one context state per machine configuration, the exact backend initial
configuration, an admitted initial context entry, the backend's step relation
at every index, and the context-acceptance rule above. These predicates do not
assume or conjoin the corresponding closed `Exec`; the verified embedding
lemmas derive that `Exec` afterward.

The completed checkpoint proves exact delta classification and append-I/O
recovery, T3/T2 matched-event and whole-trace context-history compatibility,
masked-view compatibility for the T3, T2, and composed T4 representations,
complete-view and context-state stuttering for accepted hidden steps, erasure
of all three plugged products to closed executions, prefix closure for all
three products, and identical initial views for WAL, Journal, and Broker. An
inert context witnesses `StorageParametricContext`; it has both a shared
zero-step witness and a positive one-Crash plugged witness, and every
storage-parametric context admits one shared context state yielding zero-step
plugged executions for all three machines. `ProtectedHandlesExclusive` remains
a separate T6 deployment/mediation premise; it is deliberately not part of
T4-C1.

## 8. Step relations

`DurableSlotUpdate(Cfg,d,mode,slot,rec)=Some(slot')` is the following exhaustive
partial function over replayed durable state. Its phase, attempt, outcome,
failure-conclusiveness, and uncertainty queries are exactly `d_started`,
`d_latest`, `d_outcome`, `d_failure_conclusive`, and `d_uncertain` above; it does
not inspect `GhostEvidence`. For a concrete runtime define
`RuntimeSlotUpdate(Cfg,j,mode,slot,rec) :=
DurableSlotUpdate(Cfg,Replay(j),mode,slot,rec)`. The latter reads the concrete
Journal view supplied by the storage API, not a proof-only replay shadow.

1. in `Online`, Authorize, Revoke, Prepare, and Arm preserve the slot;
2. in `Online`, Start requires `IdleSlot` and produces `Ready(r,a)`;
3. in `Online`, Outcome requires equal `Received(r,a,o)` and produces
   `ObservedSuccess(r,a,v)` for Success, `ObservedFailure(r,a)` for Failure,
   `ObservedUnknown(r,a,AmbiguousOutcome|InvalidResultReason)` for the equal
   uncontrolled uncertain observation, and `IdleSlot` for a retry-safe
   Ambiguous or InvalidResult;
4. in `Online`, Commit requires and clears equal `ObservedSuccess`;
5. in `Online`, ordinary Fail requires an equal `ObservedFailure` and a
   conclusive durable failure, and produces `IdleSlot`;
6. in `Online`, Unknown with reason `AmbiguousOutcome` or
   `InvalidResultReason` requires and clears the equal `ObservedUnknown`;
   `NonConclusiveFailure` requires and clears equal `ObservedFailure`;
   `Exhausted` requires `IdleSlot`, all attempts reserved, and durable
   uncertainty and preserves `IdleSlot`. Every enabled Online Unknown produces
   `IdleSlot`. The absent-attempt form is not allowed in Online mode;
7. in `Recovering`, Fail requires `IdleSlot` and a conclusive durable failure
   and preserves `IdleSlot`;
   Recovery Unknown requires `IdleSlot`, an unsafe uncontrolled request, and
   preserves Idle. No other record is enabled outside `Online`.

No other `(d,mode,slot,rec)` tuple is defined. In particular, an Armed request
cannot Start while Crashed or Recovering, and retry-safe uncertainty can reach
Exhausted Unknown from Idle after its volatile observation has been cleared.

`AbstractRecordEnabled(Cfg,d,rec)` is the exhaustive record table in Section 3
with numerical-reference conjuncts erased and every Journal attempt/outcome
query replaced by its durable counterpart above. In particular, Start,
Outcome, Fail, and reason-specific Unknown use the `d_*` queries rather than a
ghost Journal. The replay bridge proves the required one-way implication:

```text
JournalLegal(j) and StructuralEnabled(Cfg,j,rec)
  => AbstractRecordEnabled(Cfg,Replay(j),rec)
```

The converse is intentionally false because exact LSN references were erased.
Define:

```text
AbstractEnabled(Cfg,B,rec) :=
  AbstractRecordEnabled(Cfg,B.durable,rec)
  and DurableSlotUpdate(Cfg,B.durable,B.mode,B.slot,rec).is_some
```

`BrokerStep` uses the same abstract append protocol as the atomic runtime:

1. `JournalAppendCall(rec)` requires `B.append=AppendIdle` and
   `AbstractEnabled(Cfg,B,rec)`, with the erased proof assertion
   `StructuralEnabled(G.records,rec)`; it preserves durable state and the slot
   and sets `B.append=AppendCalled(rec)`;
2. `BrokerLinearize(rec)` requires the identical
   `B.append=AppendCalled(rec)` and `AbstractEnabled(Cfg,B,rec)`. It updates durable
    state by `ApplyRecord`, updates the slot by `DurableSlotUpdate`, sets
   `B.append=AppendLinearized(rec)`, appends `rec` to `G.records`, and proves
   `StructuralEnabled(old(G.records),rec)`, including exact references;
3. `JournalAppendReturn(q)` requires
   `B.append=AppendLinearized(rec)` and `q=len(G.records)`, preserves durable
   state and the slot, sets `B.append=AppendIdle`, and advances acknowledgment
   ghost evidence;
4. `JournalDiskFull(rec,q)` requires `B.append=AppendIdle` and
    the same `AbstractEnabled(Cfg,...)` and erased `StructuralEnabled` obligations as a
    call, with `q=len(G.records)`; it is a rejected call/return stutter.

Thus every abstract linearization has a matching earlier call. It has a
matching later return in its append epoch unless Crash aborts that epoch; Crash
never fabricates acknowledgment for an interrupted append.
Append control adds no storage representation to `BrokerState`; it makes
`pi_append`, acknowledgment causality, and prefix `Representation` exact. No
executable branch reads a ghost field; reference and source checks are erased
proof assertions.

Invoke requires Online, `B.append=AppendIdle`, and Ready, and changes Ready to
InFlight. `ReadyReleaseAgreement` proves that this control state can be reached
only after a successful append return whose acknowledged prefix contains its
Start; the proof records that return's cut in `ack_cut`. No executable branch
reads acknowledgment ghosts. An accepted Deliver requires Online and AppendIdle
and changes InFlight to Received; `RetryRelease(r)` requires Online and
AppendIdle and changes a nonconclusive `ObservedFailure(r,a)` to Idle only
while attempts remain. Crash changes any slot to Idle and clears append
control; its Broker guard is `B.mode!=Crashed`, so both Online execution and an
interrupted Recovering episode may crash, while an already Crashed machine has
no second Crash step. `IgnoreStale(r,a)` requires Online, AppendIdle, and a slot other than
the equal `InFlight(r,a)`, and stutters. BeginRecover changes Crashed to
Recovering with AppendIdle. FinishRecover requires AppendIdle and the executable
durable guard `RecoveryCompleteD(Cfg,B.durable)` before changing Recovering to
Online. Replay agreement proves this equal to the Journal guard
`RecoveryComplete(Cfg,G.records)` without reading the ghost in the transition.
Delivery sets `slot_source` to the appended physical index; Outcome carries it
to an Observed slot or clears it when the slot becomes Idle; Commit moves it to
`commit_source(r)` and clears it; every other terminalization, retry release,
and Crash clears it without creating a commit source.

`JournalDiskFull(rec,q)` is enabled only from AppendIdle for an otherwise
`AbstractEnabled(Cfg,...)` and `StructuralEnabled` record, with
`q=len(G.records)`; it
stutters on Broker and ghost state while its normalized projection reports the
failed call and return. `JournalAppendLinearize`, every `Wal*` label, and every
other backend-only label, including BeginScan, FinishScan, TruncateTail, and
AbortScan, are explicitly absent from `BrokerStep`; exhaustive event matches
must reject them rather than accept them through a wildcard. T3 matches those
WAL scan labels with zero Journal and Broker steps.

`JournalRuntimeStep` is the same independent runtime using `AtomicJournal`.
`JournalAppendCall(rec)` stores `AppendCalled(rec)` after checking structural
and caller preconditions. `JournalAppendLinearize(rec)` appends the identical
record, performs its caller-side slot update, appends it to `G.records`, and
sets `AppendLinearized(rec)`. `JournalAppendReturn(q)` may occur later, requires
`q=len(journal)`, returns to AppendIdle, and advances the ghost acknowledgment
prefix. `JournalDiskFull` is the optional rejected-call extension and performs
no state update. Invoke, accepted Deliver, `IgnoreStale`, and RetryRelease use
the Broker guards and updates; `IgnoreStale(r,a)` therefore requires Online,
AppendIdle, and a slot unequal to `InFlight(r,a)`, and stutters.

`WALRuntimeStep` implements the corresponding weakly refined protocol: Stage
is append call; Torn writes are internal stutters; WriteFull or FinishTorn is
append linearization and performs the same slot/ghost-record update; FlushAck
is successful append return and advances the same ghost acknowledgment
evidence. Crash clears append control for either backend. These definitions
keep the three machines independent while making their normalized append,
Journal, executor, and physical projections comparable.
The WAL runtime implements the same Invoke, accepted Deliver, IgnoreStale, and
RetryRelease transitions with the additional `WALQuiescent` guard required by
the caller rules.

The step relations are closed over the global Event ADT. Their accepted
constructors are exactly:

| machine | accepted Event constructors |
|---|---|
| Broker | `JournalAppendCall`, `BrokerLinearize`, `JournalAppendReturn`, `JournalDiskFull`, `InvokeEvent`, `DeliverEvent`, `IgnoreStale`, `RetryRelease`, `Crash`, `BeginRecover`, `FinishRecover` |
| Journal runtime | `JournalAppendCall`, `JournalAppendLinearize`, `JournalAppendReturn`, `JournalDiskFull`, `InvokeEvent`, `DeliverEvent`, `IgnoreStale`, `RetryRelease`, `Crash`, `BeginRecover`, `FinishRecover` |
| WAL runtime | `WalStage`, `WalWriteFull`, `WalWriteTorn`, `WalFinishTorn`, `WalFlushAck`, `WalDiskFull`, `InvokeEvent`, `DeliverEvent`, `IgnoreStale`, `RetryRelease`, `Crash`, `BeginScan`, `FinishScan`, `TruncateTail`, `AbortScan`, `BeginRecover`, `FinishRecover` |

Every unlisted constructor makes that machine's Step relation false. Proofs
must use exhaustive matches, so adding a future Event constructor creates an
explicit new proof obligation rather than a wildcard stutter.

Initial states are definitionally fixed. Broker starts at
`(D0,IdleSlot,Online,AppendIdle)`; the Journal runtime starts with an empty Journal,
IdleSlot, Online, and AppendIdle; the WAL runtime additionally has empty cache,
media, and scan result, with `acked_len=0` and `scan_phase=Idle`. All ghost
record, physical, and acknowledgment histories and all sources are initially
empty.
These are the respective `Init` predicates used by `Exec`.

## 9. Adapter rely and per-request effect refinement

This section distinguishes the two configuration levels used by the
mechanization. Let `P : PaperConfig<Adapter<X,I>>` contain both the generic
broker parameters and the adapter interpretation, and let
`Cfg = paper_broker_config(P) : FullConfig`. Predicates that interpret external
effects take `P`; broker-only legality, evidence, compatibility, invariant, and
representation predicates take `Cfg`.

An adapter interpretation supplies total predicates and relations:

```text
Adapter = {
  env_rely:(R,Seq<PhysicalEvent>,ExternalRun) -> Prop,
  classification_ok:(R,AttemptId,Observation,ExternalRun) -> Prop,
  zero_effect:(R,ExternalRun) -> Prop,
  one_effect:(R,ExternalRun) -> Prop,
  result_spec:(R,V,ExternalRun) -> Prop,
  read_preserves:(R,ExternalRun) -> Prop,
  idempotent_under_rely:(R,ExternalRun) -> Prop,
  dedup_service_law:(R,N,Q,Seq<PhysicalEvent>,ExternalRun) -> Prop
}

ExternalRun = { pre:X, post:X, interference:I }
```

`I` is an opaque interference-witness type interpreted by the adapter
proof. The pre- and post-states are read only from `ExternalRun`; they are not
repeated as independent relation arguments, so an interpretation cannot be
called with state arguments inconsistent with the run. `zero_effect` and
`one_effect` factor out permitted environment
interference and respectively mean observational equivalence to zero or one
execution of the immutable request operation.

For a per-request history `eta`,
`AdapterRelyTrace(P,r,eta,run)` is exactly:

1. `env_rely(r,eta,run)`;
2. every event belongs to `r`, and every Invoke carries `CanonicalCall(r)`,
   including the adapter namespace, declared stable key, and the same immutable
   target, resource, and complete arguments;
3. attempt identifiers are positive and unique; each delivery names its
   unique earlier Invoke and there is at most one delivery per attempt;
4. every delivered observation satisfies `classification_ok`; every
   `Success(v)` also satisfies `result_pred(r,v)`;
5. the class law holds: `read_preserves` for ReadOnly,
   `idempotent_under_rely` for Idempotent, `dedup_service_law` for
   Deduplicated, and no environmental repetition law for Uncontrolled;
6. a deduplicated trace uses one stable key and has one memoized terminal
   status and payload: Success values agree, invalid values agree, and
   Success, Failure, and InvalidResult cannot conflict.

```text
AdapterRely(P,tau,r,run) :=
  AdapterRelyTrace(P,r,pi_adapter(tau,r),run)
```

For a well-formed `eta`, define `Invoked(eta)` as its attempt identifiers and
`Delivery(eta,a)` as the optional unique delivered observation for `a`. Define:

```text
AllInvocationsFailed(eta) :=
  forall a in Invoked(eta). Delivery(eta,a)=Some(Failure)

SingleFailure(eta,a) :=
  Invoked(eta)={a} and Delivery(eta,a)=Some(Failure)

DedupFailureResolved(eta,a) :=
  Delivery(eta,a)=Some(Failure)
  and no Success or InvalidResult occurs in eta
```

The last predicate permits earlier unresolved or Ambiguous calls: under
`dedup_service_law`, the named Failure is the memoized terminal result for the
stable key and resolves them as no-effect calls.

Define `Refines(P,r,eta,run,o)` as trace well-formedness above plus:

```text
o = Commit(a,v):
  Delivered(r,a,Success(v)) occurs in eta
  and result_spec(r,v,run)
  and (class(r)=ReadOnly
       ? zero_effect(r,run)
       : one_effect(r,run))

o = Fail(a):
  Delivered(r,a,Failure) occurs in eta
  and zero_effect(r,run)

o = UnknownOutcome(_,_):
  zero_effect(r,run)
  or one_effect(r,run)
```

Let `TerminalRecord(j,r)` be the Option-valued pair `(u,rec)` containing the
unique terminal record and its LSN, when present.
`OutcomeEvidence(Cfg,j,r,eta,o)` is the causal predicate. The configuration
argument is explicit because the Unknown branch checks the exact
`StructuralEnabled` rule, including retry class, attempt bound, digest, and
stable-key fields:

```text
o = Commit(a,v):
  TerminalRecord(j,r)=Some(u,CommitRec(r,a,v,...,outcome_ref))
  and outcome_ref names Outcome(r,a,Success(v)) in prefix(j,u-1)
  and Delivery(eta,a)=Some(Success(v))

o = Fail(a):
  TerminalRecord(j,r)=Some(u,FailRec(r,a,...,outcome_ref))
  and outcome_ref names Outcome(r,a,Failure) in prefix(j,u-1)
  and Delivery(eta,a)=Some(Failure)

o = UnknownOutcome(a,q):
  TerminalRecord(j,r)=Some(u,UnknownRec(r,a,q,...,evidence_ref))
  and evidence_ref is the exact reason-specific durable anchor selected by
      StructuralEnabled(prefix(j,u-1),j[u-1])
```

Unknown evidence is deliberately durable evidence, not a negative assertion
about physical history. In particular, it does not require the absence of an
unpersisted physical Success or Failure.

`UnknownCause(Cfg,j,r,a,q)` requires `JournalLegal(j)` and holds when there
exist `u` and `evidence_ref` such that
`TerminalRecord(j,r)=Some(u,UnknownRec(r,a,q,...,evidence_ref))` and the
reason-specific guard is true in `j0=prefix(j,u-1)`: Exhausted means
`started(j0,r)=max_attempts(r)` and `DurablyUncertain(j0,r)`; Recovery means
Uncontrolled and not `FailureConclusive(j0,r)`; NonConclusiveFailure means the
latest durable outcome is Failure but `FailureConclusive(j0,r)` is false;
AmbiguousOutcome or InvalidResultReason means the equal latest durable outcome
and Uncontrolled. The anchor is checked separately by StructuralEnabled.
For Exhausted, `latest_evidence_lsn(j0,r)=Some(evidence_ref)` is an ordering anchor;
the existential attempt establishing `DurablyUncertain` may be earlier and is
the causal uncertainty witness.

`BrokerOutcomeCompatible(Cfg,j,r,eta,o)` is exactly:

```text
o = Commit(a,v):
  Delivery(eta,a)=Some(Success(v))
  and (class(r)!=Uncontrolled or Invoked(eta)={a})

o = Fail(a):
  Delivery(eta,a)=Some(Failure)
  and match class(r) {
    ReadOnly      => true,
    Idempotent    => AllInvocationsFailed(eta),
    Deduplicated  => DedupFailureResolved(eta,a),
    Uncontrolled  => SingleFailure(eta,a)
  }

o = UnknownOutcome(a,q):
  UnknownCause(Cfg,j,r,a,q)
  and (class(r)!=Uncontrolled or |Invoked(eta)|<=1)
```

Thus an Idempotent Fail is permitted only when every physical invocation has a
definitive no-effect Failure. A Deduplicated Fail may resolve earlier
uncertainty through its memoized Failure law. Unknown admits unresolved,
ambiguous, invalid, delivered-but-unpersisted, and mixed evidence; the adapter
law must still prove the external history represents zero or one effect.

`AdapterVerified(P)` means that for every `r`, finite Journal `j`,
finite `eta`, run, and `o`, the conjunction

```text
JournalLegal(erase_config(Cfg),j)
and AdapterRelyTrace(P,r,eta,run)
and OutcomeEvidence(Cfg,j,r,eta,o)
and BrokerOutcomeCompatible(Cfg,j,r,eta,o)
```

implies `Refines(P,r,eta,run,o)`. A per-adapter theorem must establish this
uniformly for every compatible well-formed `P`; each end-to-end instance uses
the result at its selected `P`. It is not proved by the generic broker.

```text
PerRequestEffectRefinement(P,tau,r,run) :=
  terminal(tau,r)=Some(o) implies
    Refines(P,r,pi_adapter(tau,r),run,o)
```

This permits multiple physical invocations for retry-safe classes but never
more than one abstract request effect. `Unknown` intentionally leaves the
choice between zero and one unresolved.

The generic proof exposes the following bridge rather than leaving the adapter
premise implicit. Journal and WAL executions have different types, so the
mechanization freezes one broker-state core and two typed wrappers rather than
an untyped disjunction. For either runtime execution `E`, write
`final(E) = E.configs[|E.events|]`. The exact frozen statement boundary is:

```text
T6S0Core(P,tau,B,r,run,o):
  paper_config_wf(P)
  and BrokerInvariant(Cfg,B)
  and B.core.evidence.records = pi_journal(tau)
  and B.physical.physical = pi_physical(tau)
  and AdapterRely(P,tau,r,run)
  and terminal(tau,r)=Some(o)
  implies
    TerminalEvidenceAndCompatibility(
      Cfg,tau,B.core.evidence.records,r,o)

JournalT6S0(P,E_J,B,r,run,o):
  paper_config_wf(P)
  and Exec(JournalRuntime(Cfg),E_J)
  and AdmissibleJournalTrace(Cfg,E_J)
  and TraceAgreement(Cfg,E_J)
  and Representation_J(Cfg,final(E_J),B)
  and AdapterRely(P,E_J.events,r,run)
  and terminal(E_J.events,r)=Some(o)
  implies TerminalEvidenceAndCompatibility(
      Cfg,E_J.events,final(E_J).evidence.records,r,o)

WalT6S0(P,E_W,B,r,run,o):
  paper_config_wf(P)
  and Exec(WALRuntime(Cfg),E_W)
  and AdmissibleWALTrace(Cfg,E_W)
  and TraceAgreement(Cfg,E_W)
  and WalBrokerRepresentation(Cfg,final(E_W),B)
  and AdapterRely(P,E_W.events,r,run)
  and terminal(E_W.events,r)=Some(o)
  implies TerminalEvidenceAndCompatibility(
      Cfg,E_W.events,final(E_W).evidence.records,r,o)
```

T6-E0 derives the `OutcomeEvidence` half from legal references, Broker
provenance, and exact record/physical projection equalities. Its event theorem
is adapter independent and concludes evidence over `pi_adapter(tau,r)` without
an `ExternalRun` or `AdapterRely` premise. T6-C0 derives the compatibility half
from retry discipline, physical causality, the T6-E0 evidence result, and
`AdapterRely`; its Deduplicated Fail branch uses the rely's pairwise
observation-consistency clause. T6-S0 combines the two conclusions and
transports the resulting conjunction through the already-assumed atomic-
Journal and typed-WAL execution, trace, and representation boundaries. This
checkpoint adds no new simulation invariant. An adapter-specific proof can
later consume the conjunction to establish its external semantic relation.

## 10. Theorem statements

T1--T5 are stated under the common premise `CfgWellFormed(Cfg)`; T1 repeats it
explicitly because it is the first exported mechanized result. T6 instead uses
`paper_config_wf(P)`, which includes the well-formed derived broker
configuration `Cfg = paper_broker_config(P)` and supplies the adapter
interpretation.

### T1. Parameterized Broker safety

For every `Cfg` satisfying `CfgWellFormed(Cfg)` and every
`tau in Exec(BrokerMachine(Cfg))`, `TraceAgreement(tau)` and
`AppendProtocolPrefix(tau)` hold, and every configuration's state and ghost
satisfy `BrokerInvariant`. In every maximal Crash-free interval (append epoch)
of the full execution—the initial interval, each interval between adjacent
`Crash` labels, and the final interval—the interval's normalized append
projection follows the serialized protocol:
a call either linearizes and returns `AppendOk`, returns `AppendFull` without a
linearization, or remains a pending prefix at the interval boundary. Moreover
each Invoke has a unique earlier
valid Authorize and Start record, its
`ack_cut` names a prior successful return covering that Start, uncontrolled
requests have at most one Invoke, each request has at most one logical terminal
record, and every committed value has exact successful-delivery provenance.

### T2. Atomic-Journal runtime simulation

For every `tau_J in Exec(JournalRuntime(Cfg))` satisfying
`AdmissibleJournalTrace(Cfg,tau_J)` and `TraceAgreement`, there exists
`tau_B in Exec(BrokerMachine(Cfg))` and a monotone weak-simulation index map
such that every pair of related prefixes satisfies `Representation`. Their
`pi_append`, `pi_auth`, `pi_journal`, `pi_physical`, every
`pi_adapter(_,r)`, `pi_control`, and `pi_logical` projections are equal.
Journal append call and return match abstract administrative steps;
`JournalAppendLinearize(rec)` matches `BrokerLinearize(rec)`; and only labels
that are absent from all these normalized projections match zero steps.

### T3. Typed-WAL simulation

If `WALInvariant(w,mode,append)` initially holds, every WAL-runtime step
preserves it and `TraceAgreement`. For every
`tau_W in Exec(WALRuntime(Cfg))` satisfying
`AdmissibleWALTrace(Cfg,tau_W)`, there exists
`tau_J in Exec(JournalRuntime(Cfg))` and a monotone weak-simulation index map
such that, at every pair of related prefixes:

```text
JournalView(C_J) = Parse(C_W.store.wal.media)
C_J.mode = C_W.mode
C_J.slot = C_W.slot
C_J.append = C_W.append
G_J = G_W
```

The executions have equal `pi_append`, `pi_auth`, `pi_journal`, `pi_physical`,
every `pi_adapter(_,r)`, `pi_control`, and `pi_logical` projections.
`WalStage(rec)` matches `JournalAppendCall(rec)`; WriteFull and FinishTorn match
`JournalAppendLinearize(rec)`; `WalFlushAck(q)` matches
`JournalAppendReturn(q)`; Crash, Invoke, Deliver, RetryRelease, BeginRecover,
IgnoreStale, FinishRecover, and `WalDiskFull` match their atomic-runtime
counterparts. Torn
writes, BeginScan, FinishScan, TruncateTail, and AbortScan are the internal WAL
stutters. The context cannot observe those stutters or a completed frame before
append return. Every ghost acknowledged prefix remains a prefix of every later
parsed medium, including across crash, scan abort, and truncation.

### T4-C0. Closed WAL-to-Broker composition

T4-C0 is the completed non-contextual composition checkpoint. For every
`Cfg` satisfying `CfgWellFormed(Cfg)` and every
`tau_W in Exec(WALRuntime(Cfg))`, instantiate T3 with its canonical compressed
Journal execution and instantiate T2 with that Journal execution. Composing
their weak-index maps yields `tau_B in Exec(BrokerMachine(Cfg))` such that each
WAL prefix is related to the mapped Broker prefix by the composed
WAL/Journal/Broker representation. The two executions have equal normalized
`pi_append`, `pi_auth`, `pi_journal`, `pi_physical`, `pi_ack`, `pi_append_io`,
`pi_control`, `pi_logical`, and every `pi_adapter(_,r)` projection. The full
Broker execution satisfies T1, and every Broker prefix named by the composed
map satisfies the corresponding prefix-closed T1 safety statement. T4-C0 also
retains T3's WAL trace agreement and cross-prefix acknowledged durability.

This theorem composes only the three closed runtime relations. It defines no
`ProgramContext`, context state, plugging operation, or relation between
source and target context states. Consequently T4-C0 is not the contextual
replacement theorem T4.

### T4-C1. Context observation and plugging foundation

T4-C1 is complete and machine checked. The cumulative Verus target through
this checkpoint verifies 720 obligations with zero errors. It defines the sole
storage-parametric observation boundary and structural plugging semantics over
one shared context state type `S`. It proves:

1. exact normalization for every backend constructor, including the two-event
   `DiskFull` delta and cut erasure from Invoke and Deliver;
2. exact projection of ordered context history to normalized append I/O;
3. equality of context deltas for T3 matches, T2 renaming, and composed T4-C0
   matches, emptiness for erased events, and whole-trace history preservation
   through the T3 and T2 translations;
4. equality of the masked runtime view under T3, T2, and composed
   representations, plus complete-view and context-state stuttering for every
   accepted hidden step;
5. nonvacuous `StorageParametricContext`: an exact fixed initial view and only
   valid nonempty deltas over masked pre/post views containing `Cfg.request`;
6. structural plugged WAL, Journal, and Broker executions and their erasure to
   the corresponding closed `Exec` relations;
7. prefix closure of all three plugged predicates; and
8. an accepting inert context, a shared zero-step WAL/Journal/Broker witness
   for every storage-parametric context, and a positive shared one-Crash
   execution for the inert context.

Each context transition is synchronized with one visible machine event and may
react to both masked endpoint views. T4-C1 excludes autonomous context-only
transitions between machine events.

T4-C1 alone does not construct a Journal or Broker execution from a plugged WAL
execution, prove contextual replacement, or use `ProtectedHandlesExclusive`.
T4-C2 discharges the execution construction and exact context-state lift.
Protected-handle exclusivity is a separate T6 deployment premise.

### T4-C2. Contextual replacement and composition

T4-C2 is complete and machine checked. Its cumulative target verifies 734
obligations with zero errors, 14 beyond T4-C1. It applies T4-C0 internally and
extends its canonical weak simulation with the completed T4-C1 context
semantics. The exported theorem retains storage parametricity as an explicit
premise. For every `Cfg`, storage-parametric context `Ctxt`, and finite plugged
WAL execution:

```text
CfgWellFormed(Cfg)
and StorageParametricContext(Cfg,Ctxt)
and PluggedWalExec(Cfg,Ctxt,tau_W^S)
implies
  let tau_B^S = CanonicalPluggedBrokerExecution(Cfg,tau_W^S);
  let mu = CanonicalComposedMap(tau_W^S.machine);
  PluggedBrokerExec(Cfg,Ctxt,tau_B^S)
  and tau_B^S.machine is the canonical T4-C0 Broker execution
  and WeakSimulationIndexMap(Cfg,tau_W^S.machine,tau_B^S.machine,mu)
  and MappedContextStatesEqual(tau_W^S,tau_B^S,mu)
  and MappedContextViewsEqual(Cfg,tau_W^S,tau_B^S,mu).
```

More explicitly, every finite plugged WAL execution erases to a
`WALRuntime(Cfg)` execution and therefore derives `AdmissibleWALTrace` and
`TraceAgreement`. T4-C0 then constructs the canonical Broker execution and
composed weak-index map. T4-C2 first constructs the canonical plugged Journal
execution and then lifts it lockstep to the canonical plugged Broker execution.
Its context sequence is compressed by the T3 translation criterion
`translate_event(e)=Some(_)`, not by whether `ContextDelta(e)` is empty:

```text
CompressContexts([s_0,...,s_n],[e_0,...,e_(n-1)])
  = [s_0] ++ [s_(i+1) | translate_event(e_i)=Some(_)].
```

This distinction retains every Journal/Broker step selected by T3 while private
WAL steps remain inside one compression-map fiber and preserve the source
context state exactly. The proof establishes exact equality of the shared
context state and the complete ordered endpoint `ContextView` at every prefix
named by the canonical composed map, not merely existence of an unspecified
relation. Each C0-matched step therefore presents equal pre-view, ordered delta,
and post-view tuples to the context relation. The constructed target satisfies
`PluggedBrokerExec`; its machine component and map retain T4-C0 weak simulation,
normalized projection agreement, full-execution T1 safety, and mapped-prefix T1
safety.

The proof uses the ordered context observation theorem, rather than only the
component projection equalities, and handles the two-observation `DiskFull`
step explicitly. It obtains the Broker witness from T4-C0 rather than accepting
T2 or T3 witnesses as theorem premises. This is the parameterized forward
replacement rule that the bounded coupled products instantiate. It does not
prove reverse contextual equivalence, liveness, autonomous context steps,
protected-handle exclusivity, adapter-specific external-effect refinement, or
refinement of a byte-level WAL and filesystem implementation.

### T5. Recovery and committed-history prefix preservation

T5-S0 is complete and machine checked. Its cumulative target verifies 743
obligations with zero errors, 9 beyond T4-C2. It defines the three abstraction
functions exactly as above and proves, for every accepted one-step transition:

```text
alpha_commit(after)
  = ExtendCommitHistory(alpha_commit(before), CommitDelta(event)).
```

`CommitDelta` is `Some(CommitEntry(r,v))` only for
`BrokerLinearize(CommitRec(r,...,v))` in the Broker,
`JournalAppendLinearize(CommitRec(r,...,v))` in the atomic Journal, and
`WalWriteFull(CommitRec(r,...,v))` or
`WalFinishTorn(CommitRec(r,...,v))` in the WAL. It is `None` for every other
accepted event. Thus every non-Commit linearization, including all append
Call/Return and DiskFull events, physical events, crashes, scan/truncation
events, recovery repair records, and `FinishRecover`, preserves the relevant
committed history by equality.

The WAL theorem requires only
`wal_invariant(Cfg,before.runtime.store,before.runtime.mode,before.runtime.append)`.
This is the runtime storage/control invariant and excludes the ghost-evidence
agreement included in `basic_invariant`. Every reachable execution state can
derive it from T3-W0's `basic_invariant`. The theorem proves a stronger exact
`JournalView` equation before projecting through replay: `WalWriteFull` and
`WalFinishTorn` append their full record, while every other accepted WAL step
preserves `Parse(media)`. In particular, `WalWriteTorn` is a parsed-view stutter
and `TruncateTail` preserves the parsed view exactly.

The immediate S0 prefix corollary is: for every machine above and every step
from configuration `c` to `c'`, using the corresponding `alpha_commit_B`,
`alpha_commit_J`, or `alpha_commit_W` on its machine state:

```text
alpha_commit(c.state) <=p alpha_commit(c'.state)
```

The extension is either empty or one new `(r,v)` from a Commit linearization.
Append call, append return, DiskFull, Crash, BeginScan, FinishScan,
TruncateTail, AbortScan, BeginRecover, recovery Fail or Unknown repair, and
FinishRecover preserve `alpha_commit` by equality.

T5-E0 is complete and machine checked. Its cumulative target verifies 747
obligations with zero errors, 4 beyond T5-S0. For the Broker, atomic Journal,
and typed WAL, it lifts the prefix relation to every interval of a finite
execution:

```text
Exec(M,Cfg,tau) and i <= j < tau.configs.len()
implies alpha_commit(tau.configs[i]) <=p alpha_commit(tau.configs[j]).
```

Each exported theorem exposes only the exact machine `Exec` predicate and the
index bounds. The WAL theorem has no separate `wal_invariant` or
`basic_invariant` premise. Its induction invokes the theorem that every
configuration of a WAL execution satisfies `basic_invariant`, projects the
runtime `wal_invariant`, applies T5-S0 to the final adjacent step, and composes
prefixes through a generic transitivity lemma.

T5-R0 is complete and machine checked. Its cumulative target verifies 769
obligations with zero errors, 22 beyond T5-E0. At that checkpoint, 34
registered targets contributed 806 dependency-aware non-duplicated
obligations. It defines the event-index predicate without assuming a record
classification:

```text
RecoveryEpisode(events,crash,finish) :=
  crash < finish
  and finish < events.len()
  and events[crash] = Crash
  and events[finish] = FinishRecover
  and forall k. crash < k < finish ==> events[k] != FinishRecover.
```

For every Broker, atomic-Journal, or typed-WAL execution and every
`crash <= index <= finish`, the corresponding R0 step theorem derives that any
backend durability linearization is a permitted recovery repair, its commit
delta is empty, and the step preserves `alpha_commit` exactly. The record
restriction is therefore a semantic consequence of non-Online enabledness:
the only admitted linearized records are conclusive `FailRec` and recovery
`UnknownRec`; `CommitRec` is impossible.

The main endpoint theorems are:

```text
Exec(M,Cfg,tau) and RecoveryEpisode(tau.events,crash,finish)
implies
  alpha_commit(tau.configs[crash])
    = alpha_commit(tau.configs[finish + 1]).
```

They combine T5-E0 prefix monotonicity with the equal commit-log length derived
through the episode. The WAL theorem exposes only `Exec` and the episode
predicate; its proof obtains `basic_invariant` and the runtime `wal_invariant`
internally.

Five obligations establish nonvacuity: initial durable and Journal recovery
completeness, minimal Broker and Journal episodes
`Crash; BeginRecover; FinishRecover`, a minimal WAL episode
`Crash; BeginScan; FinishScan; TruncateTail; BeginRecover; FinishRecover`, and
a repeated-Crash Broker episode
`Crash; BeginRecover; Crash; BeginRecover; FinishRecover`. The other 17 R0
obligations cover generic repair/sequence facts and the three-backend mode,
step, prefix, and endpoint theorems.

R0 proves committed-history equality only. Repair records, complete Journal and
WAL state, physical history, and runtime control may change. It is conditional
on a later first `FinishRecover`, makes no liveness claim, and does not export
the result through T4's contextual map.

T5-C0 is complete and machine checked. Its cumulative target verifies 783
obligations with zero errors, 14 beyond T5-R0. Thirteen new obligations prove
the mapped bridge/export, including exact commit-delta translation through T3
and T2, representation-level equality of the WAL, Journal, and Broker
abstractions, equality at every canonical mapped prefix, and recovery-endpoint
equality. One additional combined nonvacuity obligation constructs the minimal
WAL recovery episode under the inert storage-parametric context with seven
identical context states, proves all contextual theorem premises, and
instantiates the completed T5-C0 conclusion.

Normatively, write `T4C2Statement(Cfg,Ctxt,tau_W^S)` for the complete
conclusion in the preceding subsection. For every well-formed `Cfg`, storage-
parametric context `Ctxt`, finite plugged WAL execution `tau_W^S`, and recovery
indices `crash,finish`:

```text
CfgWellFormed(Cfg)
and StorageParametricContext(Cfg,Ctxt)
and PluggedWalExec(Cfg,Ctxt,tau_W^S)
and RecoveryEpisode(tau_W^S.machine.events,crash,finish)
implies
  let tau_B^S = CanonicalPluggedBrokerExecution(Cfg,tau_W^S);
  let mu = CanonicalComposedMap(tau_W^S.machine);
  T4C2Statement(Cfg,Ctxt,tau_W^S)
  and forall i:Nat. i <= tau_W^S.machine.events.len() ==>
        alpha_commit_W(tau_W^S.machine.configs[i])
          = alpha_commit_B(tau_B^S.machine.configs[mu[i]])
  and alpha_commit_W(tau_W^S.machine.configs[crash])
        = alpha_commit_W(tau_W^S.machine.configs[finish + 1])
  and alpha_commit_W(tau_W^S.machine.configs[crash])
        = alpha_commit_B(tau_B^S.machine.configs[mu[crash]])
  and alpha_commit_W(tau_W^S.machine.configs[finish + 1])
        = alpha_commit_B(tau_B^S.machine.configs[mu[finish + 1]])
  and alpha_commit_B(tau_B^S.machine.configs[mu[crash]])
        = alpha_commit_B(tau_B^S.machine.configs[mu[finish + 1]]).
```

The target endpoint is the Broker configuration at `mu[finish + 1]`, not
`mu[finish]`. T5-C0 proves equality at mapped configuration prefixes; it does
not transport `RecoveryEpisode` to the target Broker event trace. T5 as a whole
does not prove recovery liveness, full-state equality, external-effect
refinement, or byte-level WAL/filesystem correctness.

Theorem T5 is complete. H1 below checks that its cumulative package is
inhabited. T6-D0 then freezes the terminal/adapter interface, T6-E0 proves its
generic terminal-evidence half, T6-C0 proves the complementary generic
terminal-compatibility half, and T6-S0 composes both halves through the two
backend interfaces. Adapter-specific semantics are the next proof checkpoint.

### H1. Artifact and nonvacuity checkpoint

H1 imports only T5-C0 and defines a concrete total `FullConfig`. For every
request identifier, the request map returns an uncontrolled request with no
stable key and `max_attempts = 1`. For every capability identifier, the
capability map returns unit budget and universal resource and argument sets.
The valid-result relation is universal. The mechanization proves
`FullConfigWF` directly. In particular, stable-key injectivity is discharged
vacuously because the witness contains no deduplicated request; it is not an
extra assumption.

Let `Cfg_H1` be this configuration, `Inert(Cfg_H1,0)` T4's inert context, and
`MinRecovery(Cfg_H1,0)` T5-C0's six-event, seven-state plugged WAL execution.
The H1 package predicate is

```text
T5C0Package(Cfg,Ctxt,tau,crash,finish) :=
  FullConfigWF(Cfg)
  and StorageParametricContext(Cfg,Ctxt)
  and PluggedWalExec(Cfg,Ctxt,tau)
  and RecoveryEpisode(tau.machine.events,crash,finish)
  and T5C0Statement(Cfg,Ctxt,tau,crash,finish).
```

The two exported H1 results have no premises:

```text
T5C0Package(Cfg_H1,Inert(Cfg_H1,0),MinRecovery(Cfg_H1,0),0,5)

exists Cfg,Ctxt,tau,crash,finish.
  Cfg = Cfg_H1
  and crash = 0
  and finish = 5
  and T5C0Package(Cfg,Ctxt,tau,crash,finish).
```

H1 adds 3 obligations beyond T5-C0: well-formedness of the concrete total
configuration, the concrete T5-C0 package, and existential cumulative-artifact
inhabitation. Its cumulative target verifies 786 obligations with zero errors;
the historical H1 registry contained 36 targets and 823 dependency-aware
non-duplicated obligations.
This is a satisfiability result, not a stronger recovery theorem. The concrete
minimal witness does not exhibit a nonempty pre-crash commit history, realistic
adapter behavior, an external effect, liveness, or byte-level persistence.

The artifact evidence is part of H1's reproducibility boundary. The Verus
runner reports SHA-256 hashes for its schema, every registered source, the
runner, the toolchain lock, and the fresh Rust tree. It invokes Verus only on an
exact read-only source snapshot, requires complete source/import registration,
and validates each cumulative target's immediate predecessor. The TLC runner
validates exact manifest fields, unique scenario names and configurations, the
`smoke`/`full` tier alphabet, input existence, and registration of every
`formal/*.cfg`. It runs only from exact per-run model and tool snapshots and
checks their membership and hashes around each invocation. Both runners require
their bound metadata inputs to remain stable. These controls bind reports to
checked inputs; they do not enlarge the semantic theorem.

### T6-D0. Terminal and adapter definition freeze

T6-D0 imports T5-C0 directly and freezes the vocabulary consumed by the T6
proof without claiming the terminal bridge. The mechanized surface contains:

- generic `ExternalRun<X,I>` and total first-class adapter relations;
- request-local physical-history well-formedness, exact unique `Delivery`,
  invocation-count predicates, class laws, and deduplicated terminal-result
  consistency;
- the request-free `TerminalOutcome` datatype and a duplicate-rejecting
  `terminal_record` selector that returns a one-based `IndexedTerminalRecord`
  only for exactly one request terminal;
- `UnknownCause`, configuration-explicit `OutcomeEvidence`, and three separate
  outcome-indexed compatibility branches;
- derived `Refines`, `AdapterVerified`, and per-request refinement predicates;
  and
- one broker-state core statement plus separate atomic-Journal and typed-WAL
  T6-S0 wrapper statements over the representation relations already proved by
  T2 and T4-C0.

T6-D0 verifies 799 cumulative obligations with zero errors, 16 beyond its
T5-C0 parent. Together with the independent H1 delta, its 37-target checkpoint
contains 839 dependency-aware non-duplicated obligations.

`AdapterRelyTrace` itself requires every event in its input history to belong
to the named request; this is necessary because `AdapterVerified` quantifies
over arbitrary finite histories, not only values already produced by
`pi_adapter`. Both terminal-record and delivery selectors reject duplicates,
so malformed histories cannot acquire arbitrary evidence through a
last-element convention. Unknown evidence remains a durable structural anchor
and makes no negative claim about unpersisted physical outcomes.
The checkpoint also proves that replay-layer `unknown_enabled` is exactly the
conjunction of the frozen reason guard and evidence-anchor predicate, so a
future replay-rule change cannot silently drift from the T6 vocabulary.

The definition checkpoint proves only constructor/unfolding and selector
sanity obligations. T6-E0, described next, derives the `OutcomeEvidence` half;
T6-C0 derives `BrokerOutcomeCompatible`; T6-S0 combines them and discharges the
two backend wrappers.

### T6-E0. Terminal evidence

T6-E0 imports T6-D0 directly and proves an adapter-independent full-history
lemma:

```text
JournalLegal(erase_config(Cfg),j)
and PhysicalUnique(eta)
and DurableOutcomesFollowDeliveries(j,eta)
and terminal_from_records(j,r)=Some(o)
implies OutcomeEvidence(Cfg,j,r,eta,o).
```

It then discharges the event-level evidence half used by the frozen core:

```text
T6E0Core(Cfg,tau,B,r,o):
  BrokerInvariant(Cfg,B)
  and B.core.evidence.records = pi_journal(tau)
  and B.physical.physical = pi_physical(tau)
  and terminal(tau,r)=Some(o)
  implies OutcomeEvidence(
    Cfg,B.core.evidence.records,r,pi_adapter(tau,r),o).
```

The proof establishes soundness of the one-based terminal selector, exact
recovery of an Outcome record from its LSN and observation projections,
prefix closure of durable Outcome-to-delivery causality, the delivery-count
bound induced by global physical uniqueness, and preservation of delivery
counts and latest observations by the request-local adapter projection. In the
Commit and Fail branches, the terminal record's `outcome_ref` therefore names
the exact Outcome in the strict pre-terminal prefix, and the causally prior
matching physical delivery is the unique selected delivery. In the Unknown
branch, Journal legality supplies the exact prefix `StructuralEnabled` rule and
its reason-specific durable anchor; the proof makes no negative assertion
about unpersisted physical outcomes.

T6-E0 verifies 817 cumulative obligations with zero errors, 18 beyond its
T6-D0 parent. Its historical 38-target registry contained 857 dependency-aware
non-duplicated obligations. The theorem neither assumes nor proves an adapter
semantic interpretation: it does not establish `BrokerOutcomeCompatible`,
`Refines`, an `AdapterVerified` instance, external-effect refinement, the
combined T6-S0 conclusion, or either Journal/WAL wrapper. T6-C0, described
next, supplies the first of those missing conclusions; T6-S0 subsequently
combines the two halves and discharges the wrappers.

### T6-C0. Terminal compatibility

T6-C0 imports T6-E0 and proves the compatibility half of the frozen core
statement:

```text
T6C0Core(P,tau,B,r,run,o):
  let Cfg = paper_broker_config(P);
  paper_config_wf(P)
  and BrokerInvariant(Cfg,B)
  and B.core.evidence.records = pi_journal(tau)
  and B.physical.physical = pi_physical(tau)
  and AdapterRely(P,tau,r,run)
  and terminal(tau,r)=Some(o)
  implies BrokerOutcomeCompatible(
    Cfg,B.core.evidence.records,r,pi_adapter(tau,r),o).
```

The proof first reuses T6-E0 to obtain exact terminal evidence and proves that
the request-local adapter projection preserves per-attempt and aggregate
invocation counts. It then discharges every frozen compatibility branch:

- **Commit:** the selected successful delivery is exact. For an Uncontrolled
  request, the global retry bound and projection equality reduce the history
  to exactly one invoked attempt, namely the delivered attempt.
- **Fail/ReadOnly:** the selected Failure delivery is sufficient.
- **Fail/Idempotent:** terminal provenance makes the durable failure
  conclusive and hence records every started attempt as failed. A physical
  invocation has an acknowledged durable Start range; durable
  Outcome-to-delivery causality and physical uniqueness then select a Failure
  delivery for every invoked attempt.
- **Fail/Deduplicated:** the Failure delivery anchors the pairwise consistency
  clause supplied by `AdapterRelyTrace`. That clause excludes every Success or
  InvalidResult delivery for the request, establishing the frozen resolved-
  failure predicate.
- **Fail/Uncontrolled:** aggregate retry discipline plus the selected delivery
  establishes a single invoked attempt and therefore `single_failure`.
- **Unknown:** the T6-E0 structural witness is decomposed into the exact
  reason guard and durable evidence anchor, yielding `UnknownCause`. The
  Uncontrolled branch additionally inherits the at-most-one-invocation bound.

T6-C0 verifies 834 cumulative obligations with zero errors, 17 beyond its
T6-E0 parent. Its 39-target registry contains 874 dependency-aware
non-duplicated obligations, and the sum of all registered target obligations is
18,224. This checkpoint proves compatibility of the selected broker terminal
outcome with its request-local invocation history; it does not itself export
the conjunction with `OutcomeEvidence`, discharge the atomic-Journal or
typed-WAL wrappers, prove `Refines` or an `AdapterVerified` instance, interpret
an adapter-specific external effect, or establish the end-to-end T6 theorem.
Those composition and backend obligations are discharged by T6-S0 below;
adapter effects remain later work. H1's concrete configuration/package witness
is inert and does not inhabit a terminal `AdapterRely` run. T6-C0 is therefore
a conditional compatibility theorem; a concrete terminal adapter/run witness
remains an obligation of the later adapter checkpoint.

### T6-S0. Terminal evidence-and-compatibility bridge

T6-S0 imports T6-C0, and therefore T6-E0 transitively, and proves the frozen
core conclusion:

```text
T6S0Core(P,tau,B,r,run,o):
  let Cfg = paper_broker_config(P);
  paper_config_wf(P)
  and BrokerInvariant(Cfg,B)
  and B.core.evidence.records = pi_journal(tau)
  and B.physical.physical = pi_physical(tau)
  and AdapterRely(P,tau,r,run)
  and terminal(tau,r)=Some(o)
  implies TerminalEvidenceAndCompatibility(
    Cfg,tau,B.core.evidence.records,r,o).
```

The conclusion is exactly the frozen conjunction of `OutcomeEvidence` and
`BrokerOutcomeCompatible`, both over `pi_adapter(tau,r)`. The proof applies
T6-E0 to obtain the first conjunct and T6-C0 to obtain the second; it does not
weaken either premise set or introduce a new semantic relation.

The atomic-Journal wrapper takes the frozen `Exec`,
`AdmissibleJournalTrace`, `TraceAgreement`, and `Representation_J` premises.
Final-prefix trace agreement identifies the final concrete evidence with
`pi_journal` and `pi_physical`; the existing representation relation supplies
the Broker invariant and transfers those equalities to the represented Broker
state. The wrapper then instantiates the core theorem and rewrites its record
argument to `final(E_J).evidence.records`.

The typed-WAL wrapper follows the same pattern from `Exec`,
`AdmissibleWALTrace`, `TraceAgreement`, and `WalBrokerRepresentation`. The
existing WAL-to-Broker representation is the atomic-Journal representation of
the WAL's journal projection, so final-prefix agreement supplies the same
record and physical equalities before the core theorem is applied. Both
wrappers only transport the core result through assumed execution,
admissibility, trace-agreement, and representation facts. They neither prove
nor require an additional backend simulation invariant.

T6-S0 added 6 obligations beyond T6-C0. Its historical retained target verified
840 obligations with zero errors. That 40-target registry contained 880
dependency-aware non-duplicated obligations, and the sum of all registered
target obligations was 19,064. This checkpoint does not prove `Refines`, an
`AdapterVerified` instance, adapter-specific one-effect semantics, a concrete
terminal witness, terminal-premise inhabitation, or delivery of a result to a
caller (`ReturnResult`). In particular, H1's inert witness does not inhabit
`AdapterRely` for a terminal execution. Those obligations remain outside the
T6-S0 bridge.

### T6-A0. Concrete adapter semantic closure

T6-A0 imports only T6-S0. First, it discharges the generic semantic step that
T6-S0 intentionally left abstract. For
`Cfg = paper_broker_config(P)`, it proves:

```text
AdapterVerified(P)
and JournalLegal(erase(Cfg), j)
and AdapterRely(P, tau, r, run)
and TerminalEvidenceAndCompatibility(Cfg, tau, j, r, o)
implies Refines(P, r, pi_adapter(tau, r), run, o).
```

If `terminal(tau,r)=Some(o)`, the definition of
`PerRequestEffectRefinement` then yields per-request refinement. The event,
atomic-Journal, and typed-WAL exports obtain the frozen conjunction from their
corresponding T6-S0 theorem under the existing Broker-invariant or execution,
admissibility, trace-agreement, and representation premises. Their outcome-free
forms case-split on `terminal`; the `None` branch is the definitional trivial
case of `PerRequestEffectRefinement`.

The concrete instance is `EnsureMember`, with external state
`x : Set<Resource>` and target `target(r) = Resource{id = r.id}`. An external
run carries a set `E` of environment additions and a set `L` of attempt numbers
recorded as linearized. Its baseline and abstract effects are:

```text
baseline(x0,E) = x0 union E
ZeroEffect(x0,x1,E) iff x1 = baseline(x0,E)
OneEffect(r,x0,x1,E) iff x1 = baseline(x0,E) union {target(r)}.
```

The environment rely excludes `target(r)` from `E`, requires every attempt in
`L` to occur in the physical invocation history, and selects `OneEffect` when
`L` is nonempty and `ZeroEffect` otherwise. Success with the unique valid
`Value{id=1}` classifies its attempt as a member of `L`; Failure classifies its
attempt outside `L`; Ambiguous and InvalidResult remain unconstrained by this
classification clause. Every request in the fixed concrete paper is Idempotent,
has no stable key, and permits at most two attempts. The proof establishes
`AdapterVerified(ensure_member_paper())` uniformly over the legal records,
histories, runs, and outcomes quantified by that predicate. It also proves
nondegeneracy on an empty-baseline singleton run and shows that a crash-erased
Invoke/Success/Invoke/Failure adapter history denotes one effect. The latter is
an adapter-level sequence rule, not a proof that a matching Broker/WAL crash
execution is reachable.

The exact nonvacuity witness is a 20-event, 21-configuration typed-WAL
execution. It acknowledges six records in order--`Authorize`, `Prepare`, `Arm`,
`Start(attempt=1)`, `Outcome(Success(Value{id=1}))`, and `Commit`--using a
stage/full-write/flush triple for each append, and contains one Invoke and one
delivered Success. Its final WAL state represents the constructed Broker state;
the selected terminal is the exact Commit; and the exported premise-free
existential fixes the paper, request, external run, outcome, records, and
physical history while proving `Refines`, one effect, and not zero effect.

T6-A0 adds 23 obligations over the current T6-S0 closure and verifies 864 with
zero errors. The retained 41-target report contains 904 dependency-aware
non-duplicated obligations and sums 19,951 target obligations. This checkpoint
verifies a semantic adapter contract. It does not verify executable adapter or
external-service code, produce a realizable crash execution for the mixed
adapter history, prove byte-level/fsync persistence, discharge
`CompleteMediation` or protected-handle exclusivity, add `ReturnResult`, prove
multi-request/global linearizability or liveness, or establish least privilege
for its synthetic full-capability witness.

### T6-A1. Executable adapter protocol refinement

T6-A1 imports only T6-A0 and replaces the remaining adapter-semantic rely
assumption for `EnsureMember` with an explicit operational transition system.
Its adapter events are an observed global WAL/Broker event, a silent
`ServiceLinearize(attempt)` event, or an `EnvironmentAdd(resource)` event. Its
state records the initial and current membership sets, environment additions,
linearized and failed attempts, the observed global trace, its exact
request-local physical projection, an `Online`/`Crashed`/`Recovering` mode, and
the active attempt. `A1AdapterExecution` is a finite initial-state execution of
these enabled steps.

The operational guards require every target-request invocation to be positive,
within budget, canonical, unique, and issued online with no active attempt. A
Success delivery must name the active invocation, carry the unique valid
`Value{id=1}`, and follow a service linearization of that attempt. A Failure
delivery must name the active invocation before any such linearization; after
Failure, that attempt cannot linearize. A service linearization must refer to an
invoked, undelivered, nonfailed attempt and inserts the target into the external
membership set. Environment additions may insert only nontarget resources.
Crash clears the active adapter slot, while the recovery observations move the
adapter through the explicit crash and recovery modes.

The service-linearization guard intentionally does not require local Online
mode or a volatile active-attempt slot. It therefore admits the standard remote
call behavior in which an invocation sent before a local crash may linearize at
the service afterward. Its causal authority is the invoked, undelivered,
not-yet-linearized, nonfailed remote-attempt condition. Refinement of a concrete
transport must justify that behavior or establish a stronger cancellation
guarantee.

`a1_service_linearize_step_has_remote_provenance` exposes that assumption as a
checked step theorem: a service linearization starts from the named pending-
remote condition, inserts the target and the attempt into the corresponding
sets, and stutters both observed global and physical history.

The inductive invariant proves exact equality between stored global history and
the observed-event projection, exact equality between stored physical history
and `pi_adapter`, request locality, canonical calls, positive unique ordered
attempts, response classification, and linearization provenance. It also proves
the functional state equation

```text
members = initial_members union environment_additions
          union ({target(r)} if some attempt linearized else empty),
```

with the environment forbidden from adding `target(r)`. Consequently
`ensure_member_exec_derives_adapter_rely` derives `AdapterRely` for the final
external run of every A1 execution; `AdapterRely` is no longer an enabledness
premise of this protocol. The generic composition theorem
`ensure_member_executable_wal_terminal_refines` takes an A1 execution, exact
equality of its observed global trace with a typed-WAL execution, WAL execution,
and a selected terminal outcome. It derives `AdapterRely`, invokes the T6-A0
semantic closure, and concludes both `Refines` and
`PerRequestEffectRefinement`.

The closed crash/retry witness starts from an empty membership set and has 31
global WAL events, 32 WAL configurations, and 32 adapter events; the additional
adapter event is the silent `ServiceLinearize(1)`. Each record append expands to
`WalStage`, `WalWriteFull`, and `WalFlushAck`. The seven acknowledged records
are, in order:

```text
Authorize, Prepare, Arm, Start(1), Start(2),
Outcome(2, Failure, start_ref=5),
Unknown(attempt=Some(2), NonConclusiveFailure, evidence_ref=6).
```

The exact physical history is

```text
Invoke(1, journal_cut=4, ack_cut=4),
Success(1, Value{id=1}, journal_cut=4),
Invoke(2, journal_cut=5, ack_cut=5),
Failure(2, journal_cut=5).
```

Between the first Success and `Start(2)`, the global execution performs
`Crash`, `BeginScan`, `FinishScan`, `TruncateTail`, `BeginRecover`, and
`FinishRecover`. The first Success is delivered after its service
linearization but is not journaled before the crash. Recovery therefore retains
only the four-record prefix through `Start(1)`, and the retry makes attempt 2
current. Attempt 2 fails without linearizing; its durable Failure cannot justify
terminal Fail because the Idempotent Fail rule requires every invocation to
have failed, while attempt 1 delivered Success. There is no durable successful
Outcome from which to Commit. The legal terminal is therefore exactly
`UnknownOutcome{attempt=Some(2), reason=NonConclusiveFailure}`. The external
run denotes exactly one abstract insertion, not zero, because attempt 1
linearized and attempt 2 did not.

`a1_retry_has_explicit_crash_recovery_shape` proves the exact positions of the
Crash, scan/truncation, recovery, three-step `Start(2)` append, `Invoke(2)`, and
`Failure(2)` events in the 31-event trace. This makes the crash/retry execution
shape an exported theorem rather than an inference from projections that erase
control events.

`t6_a1_executable_crash_retry_refines` proves `AdapterRely`, `Refines`,
per-request effect refinement, exact one effect, not zero effect, the selected
Unknown terminal, and failure of `all_invocations_failed`. The exact operational
and semantic package is inhabited without premises by
`t6_a1_executable_crash_retry_nonvacuity`. T6-A1 verifies 916 obligations with
zero errors, 52 beyond T6-A0. The retained 42-target report contains 956
dependency-aware non-duplicated obligations and sums 20,867 target obligations.

Here executable means that the adapter/service protocol is an explicit finite
transition system with a mechanized reachable execution. T6-A1 does not verify
production Rust adapter code, network transport, or the remote membership
service. It also does not add byte-level/fsync persistence, protected-handle
mediation, `ReturnResult`, least privilege, multi-request/global
linearizability, or liveness. Its generic composition premise is exact equality
of the complete observed adapter trace and typed-WAL event trace; T6-A1 does not
yet prove a prefix-indexed stuttering simulation or combined adapter/WAL state
invariant. That combined relation is supplied later in the dependency order:
T6-M0 closes the service-mediation boundary,
T6-P0 supplies the combined prefix product, and T6-X0 completes its contextual
lift for this instance.

### T6-M0. Mediation and protected-handle exclusivity

T6-M0 imports only T6-A1 and replaces the caller-supplied protected trace with
separately defined protected-service and audit-context executions, related to
A1 or the WAL by explicit eventwise relations.
`M0ProtectedExecution` is a first-class service transition system. Its accepted
calls store request, attempt, call descriptor, Journal cut, acknowledged cut,
and source-event index. The Invoke coupling proves these fields equal the
canonical A1/WAL event; the deployment theorem supplies authorization.
`BrokerInvoke` additionally requires a request-local, fresh `(request,attempt)`
key. A service linearization names a
previous call by `call_ref`; a return names the same call index. Only
`ServiceLinearize(call_ref)` can insert the protected target. Environment steps
are enabled only for nontarget resources, and the event alphabet contains no
raw or context-owned target-mutation constructor.

The protected service is related to A1 event by event. An observed Broker/WAL
Invoke becomes `BrokerInvoke`, a delivery becomes `ServiceReturn`, a silent A1
linearization becomes the call-indexed service linearization, and all unrelated
storage/control events stutter. Final invocation equality is deliberately not
part of this coupling relation. Prefix induction instead proves that the
service-generated call trace, after erasing cuts and source indices, equals
`pi_invocations` of the A1 observed global trace. A second execution induction
proves that stored service calls are exactly those generated by service events;
their equality therefore derives the legacy `CompleteMediation` predicate
rather than satisfying it by choosing its right-hand side.

`M0ProtectedHandleState` supplies a separate T4-C1 program context. It can only
audit `ContextEvent::Invoke` labels present in the masked storage view. Its
transition relation has no protected-service state, handle, invocation, or
mutation parameter, and any transition delta without an Invoke leaves its
audit trace unchanged. The concrete context is proved
`StorageParametricContext`; every typed-WAL execution can be paired with its
deterministically accumulated context states, and every admitted plugged WAL
execution under this context derives the same `CompleteMediation` equality.
This is a closed-alphabet no-bypass property of the formal deployment interface.
It is not a verification of OS descriptor distribution, process isolation,
network ACLs, or production service authentication.

The target-action theorem has two layers. First, every service linearization
references a prior, incomplete call owned by the target request, and every
nonlinearization step preserves target membership. Second, eventwise coupling
proves that every stored call's source index names its exact prior A1 global
Invoke. Under whole-trace A1/WAL equality and typed-WAL execution, T4-C0 maps
that exact Invoke to the canonical Broker execution. T1's
`invoke_temporal_at` then establishes the canonical call, positive and bounded
acknowledged cut, acknowledged authorized Start ancestry, unique Authorize and
Start counts, and a successful append return strictly before invocation.
`m0_coupled_linearization_is_durably_authorized` packages this chain for any
coupled target action without a new semantic assumption.

`m0_deployment_exec` is the reusable premise that packages a well-formed
configuration, the A1 and protected-service executions, their eventwise
coupling, a valid typed-WAL execution, and exact A1/WAL global-trace agreement.
The quantified predicate `m0_every_linearization_durably_authorized` ranges over
every protected event index. The generic theorem
`m0_deployment_derives_authorized_linearizations` derives that predicate from
the deployment package, and the concrete M0 result retains it as a named
conjunct. A bare `m0_protected_exec` is only the service transition grammar; its
`BrokerInvoke` constructor is not by itself an authorization check. Durable
authorization is claimed only under `m0_deployment_exec` (or the stronger
concrete package).

The premise-free M0 witness reuses the exact A1 execution, separately constructs
a 32-step protected-service execution, and couples it lock-step to A1. It accepts two calls, at
global source indices 12 and 23; call 0 (attempt 1) is the sole linearization;
both calls return, call 1 (attempt 2) never linearizes, and no environment step
occurs. Both cut-bearing calls satisfy T1 durable authorization. The closed-
interface audit context is plugged into the 31-event typed-WAL execution, and
both its
trace and the service trace equal the WAL invocation projection. The retained
A1 result still supplies Unknown rather than Fail and exactly one abstract
insertion effect. These facts are exported by
`t6_m0_executable_crash_retry_mediation` and the premise-free existential
`t6_m0_mediation_nonvacuity`.

T6-M0 does not prove production Rust, transport, OS, or service refinement;
byte-level/fsync persistence; caller-visible `ReturnResult`; least privilege;
multi-request/global linearizability; or liveness. It also does not establish a
general prefix-indexed stuttering simulation between arbitrary A1 executions
and typed-WAL executions. The completed prefix arguments are internal to the
service/call trace and closed-interface audit context. P0, below, adds the
conditional combined prefix product; X0 then supplies its contextual lift.

### T6-P0. Prefix-indexed adapter/WAL/protected product

T6-P0 imports only T6-M0 and defines the weakly indexed product used by the
remaining end-to-end lift. Its source is
`mechanized/t6_prefix_simulation.rs`. The result is scoped to the fixed
single-request `EnsureMember` configuration inherited from A1; it does not yet
quantify over arbitrary adapter classes or requests.

For an A1 event `e`, typed-WAL execution `W`, and adjacent map points `i,j`,
`p0_a1_wal_step_match(e,W,i,j)` has exactly two cases:

```text
e = Observe(g)                         => j = i + 1 and W.events[i] = g
e = ServiceLinearize(_) | EnvironmentAdd(_) => j = i
```

`p0_a1_wal_coupled` conjoins those matches with `weak_index_shape`, including
zero and final endpoints and zero-or-one advancement. At each A1 prefix index
`k`, `p0_a1_wal_related_prefix_at` requires

```text
a1_global_trace(A.events[..k]) = W.events[..mu[k]]
A.configs[k].globals           = W.events[..mu[k]]
A.configs[k].history           = pi_adapter(W.events[..mu[k]], request).
```

The relation deliberately pairs executions rather than asserting their
existence. `p0_execution_pair` assumes a valid `m0_coupled_exec` for A1 and the
separately defined protected service, a valid typed-WAL execution, and the
weak step coupling. It does not construct a typed-WAL execution from an
arbitrary A1 execution and therefore is not a forward-existence theorem.

`p0_effect_state_agreement` relates the A1 and protected-service states by
request, initial and current membership, environment additions, and the exact
set of linearized attempts. The protected set is reconstructed only from
in-range call references owned by the request, preventing a later call append
from retroactively validating an earlier out-of-range ghost reference.
`p0_prefix_product_at` combines this effect relation with related-prefix trace
and request-history agreement, valid protected and WAL execution prefixes,
equality between accepted protected calls and the WAL invocation projection,
and `CompleteMediation` at the mapped prefix.

The principal generic theorem is
`p0_execution_pair_derives_prefix_product`. From `p0_execution_pair`, it proves
`p0_prefix_product`, final projected-trace equality, final complete mediation,
and final effect-state agreement. Its supporting exports are:

- `p0_a1_wal_prefix_trace_agreement` and
  `p0_a1_wal_steps_derive_related_prefixes`, which derive exact agreement at
  every weakly related prefix;
- `p0_coupled_every_prefix_effect_state_agreement`, which preserves the
  adapter/protected effect relation at every A1 configuration;
- `p0_execution_pair_prefix_closed` and `p0_prefix_product_closed`, which
  truncate the A1 and protected executions at `k`, the WAL execution at
  `mu[k]`, and the index map at `k+1` while retaining the respective relation;
- `p0_canonical_index_map`, which maps an adapter prefix to the length of its
  observed global projection; and
- `p0_canonical_map_couples_trace_equal_execution` and
  `p0_trace_equal_execution_pair`, which recover the step-coupled execution
  pair from the older whole-trace equality premise. These lemmas transform an
  already supplied execution pair; they do not prove that a matching WAL run
  exists for every A1 run.

The concrete theorem `t6_p0_executable_crash_retry_prefix_product` applies the
canonical map to A1's 32-event adapter execution, M0's independent 32-event
protected execution, and A1's 31-event typed-WAL execution. The map has 33
points, begins at zero, ends at 31, and satisfies `mu[13] = mu[14]` at
`ServiceLinearize { attempt: 1 }`. It retains complete mediation and final
effect-state agreement. `t6_p0_prefix_product_nonvacuity` exports the same
package existentially without premises.

T6-P0 verifies 1,000 cumulative obligations with zero errors, 23 beyond
T6-M0. It establishes no storage-parametric plugged-execution theorem, no
conditional end-to-end T6 conclusion, no production Rust/network/service or
OS-isolation refinement, no byte/fsync result, no caller-visible result action,
and no concurrency, global-linearizability, least-privilege, or liveness
property. T6-X0, below, adds the contextual lift without changing those
implementation and deployment boundaries.

### T6-X0. Storage-parametric contextual end to end

T6-X0 imports only T6-P0. Its source is
`mechanized/t6_contextual_end_to_end.rs`. It composes P0's adapter-to-WAL weak
index `mu` with T4-C2's canonical WAL-to-Broker weak index `nu`:

```text
chi = compose_index_maps(mu, nu)
chi[k] = nu[mu[k]].
```

For every A1 prefix `k`, `x0_contextual_prefix_at` writes `w = mu[k]` and
`b = chi[k]`. It retains `p0_prefix_product_at(k)`, proves valid plugged WAL
and canonical Broker executions truncated at `w` and `b`, and establishes:

```text
A.configs[k].history = pi_adapter(B.events[..b], request)
C_W[w]               = C_B[b]
WalContextView(W,w)  = BrokerContextView(B,b)
T1Safety(B[..b]).
```

The same prefix also grounds the A1 `ExternalRun` in the independently
executed protected-service state: initial and final membership, environment
additions, and the exact set of protected linearized attempts agree.
`x0_contextual_product` combines those all-prefix clauses with
`StorageParametricContext`, `PluggedWalExec`, the P0 execution pair, T4-C2's
contextual replacement statement, and the weak shape of `chi`.
`x0_lift_p0_through_context` proves this product for every supplied
storage-parametric context and plugged WAL execution satisfying the premises.
It does not assert that every context admits the execution, and it does not
construct a matching WAL execution for an arbitrary A1 run.

`x0_contextual_broker_terminal_outcome_refines<X,I,S>` is the paper-facing
generic theorem at the contextual boundary. For every well-formed
adapter-bearing `PaperConfig`, storage-parametric context and admitted plugged
WAL execution, it assumes `AdapterVerified`, request-local `AdapterRely`, and a
selected source terminal outcome. It constructs T4-C2's canonical plugged
Broker execution and proves that its target trace selects the same outcome and
satisfies `Refines` and `PerRequestEffectRefinement`. This theorem is
polymorphic in adapter state, interference witness, and context state; it does
not by itself provide an operational adapter execution or protected-service
mediation.

The principal terminal theorem is
`t6_x0_ensure_member_terminal_end_to_end`. For a distinguished request, it
assumes the storage-parametric context, an admitted plugged WAL execution, the
P0 prefix product, and a selected source terminal outcome. It proves the
combined `x0_ensure_member_terminal_statement`:

- the source WAL terminal has `TerminalEvidenceAndCompatibility`, satisfies
  `Refines`, retains `CompleteMediation`, final effect-state agreement, and
  durable authorization for every protected linearization;
- the canonical plugged Broker execution selects the same terminal outcome
  and satisfies `Refines` and `PerRequestEffectRefinement`; and
- `CompleteMediation` is preserved on the canonical Broker trace, while the
  composed product carries T1 safety and context equality at every related
  prefix.

The theorem is conditional on supplied valid executions and a context that
admits the source run. It is the machine-checked single-request
`EnsureMember` instance of the generalized T6 shape, not a theorem for every
`PaperConfig`, adapter class, request, or external-run family.

`t6_x0_executable_crash_retry_end_to_end` instantiates the theorem without
premises using M0's exclusive-handle audit context, A1's 32-event adapter run,
M0's independent 32-event protected execution, and the 31-event typed-WAL
run. The canonical Broker terminal is the same
`Unknown(NonConclusiveFailure)` outcome. The package proves exactly one
abstract insertion effect and not zero, exactly one protected linearization,
final target membership, source and target `CompleteMediation`, equality of
the canonical Broker context's final invocation audit with the protected
accepted-call trace, and durable authorization of every linearization.
`t6_x0_contextual_end_to_end_nonvacuity` exports this package existentially.

T6-X0 verifies 1,022 cumulative obligations with zero errors, 22 beyond
T6-P0. With T6-X0 registered, the retained suite passes 45/45 targets, contains
1,062 dependency-aware non-duplicated obligations, and sums to 23,866 target
obligations.

T6-X0 does not verify production Rust adapter/runtime code, transport or
remote-service behavior, OS/process/descriptor isolation, byte encoding or
`fsync`, caller-visible `ReturnResult`, least privilege, multi-request or
global external-effect linearizability, concurrency, or liveness. The
exclusive-handle result remains a closed-alphabet property of the formal M0
deployment interface.

### T6. Generalized conditional end-to-end theorem

The following is the intended full-system generalization of X0. X0 proves its
contextual source-to-target terminal-refinement component for an arbitrary
adapter-bearing `PaperConfig`, one selected request and external run under
`AdapterVerified` and `AdapterRely`. It proves the additional operational,
protected-state, mediation, and all-prefix product obligations for
`EnsureMember`, one distinguished request, and any supplied
storage-parametric context admitting the paired WAL run. T6-DD5 now supplies a
coverage-conditioned request-indexed family theorem: every terminal request in
the shared WAL must have a valid operational/protected member, and that member's
DD4 product and X0 transport are proved generically.

For every `P : PaperConfig<Adapter<X,I>>`, let
`Cfg = paper_broker_config(P)`. For every `ProgramContext<S>` value `Ctxt`,
finite plugged WAL execution `tau_W^S`, protected-handle trace
`omega:ProtectedTrace`, and map
`runs:R -> ExternalRun`, if:

```text
paper_config_wf(P)
and StorageParametricContext(Cfg,Ctxt)
and PluggedWalExec(Cfg,Ctxt,tau_W^S)
and AdmissibleWALTrace(Cfg,tau_W^S.machine)
and TraceAgreement(tau_W^S.machine)
and the initial WAL invariant holds
and ProtectedHandlesExclusive(Cfg,Ctxt)
and CompleteMediation(tau_W^S.machine,omega)
and AdapterVerified(P)
and forall r. AdapterRely(P,tau_W^S.machine.events,r,runs(r)),
```

then T4-C2, invoking T4-C0 internally, produces a prefix-related plugged Broker
execution, so T1's
authorization, budget, scope, attempt-causality, retry, terminal uniqueness,
crash-prefix, failure-provenance, and value-provenance properties hold for
`tau_W^S.machine`. For each terminal request,
`TerminalEvidenceAndCompatibility` supplies the exact premise consumed by
`AdapterVerified`; therefore every request `r` satisfies
`PerRequestEffectRefinement(P,tau_W^S.machine.events,r,runs(r))`. In particular, every
committed mutating request refines one authorized abstract effect, every
committed read refines zero protected mutations and one valid observation, and
no request contributes two commit-log entries.

This is the completed coverage-conditioned generic T6 claim at the formal family
boundary. It does not assert that production code automatically constructs the
family members or the coverage predicate.
T6-A1 supplies an operational `EnsureMember` adapter refinement and a closed
crash/retry typed-WAL witness without assuming `AdapterRely`. T6-M0 adds the
protected-service execution, a storage-parametric closed-interface audit
context, derived mediation, and authorized target-action provenance for that
witness. T6-P0 supplies the conditional prefix-indexed execution product and
its prefix closure. T6-X0 completes the contextual lift, source and target
terminal refinement, and concrete nonvacuity theorem for that `EnsureMember`
instance. T6-DD5 supplies the interface connecting a family of operational
adapter/protected executions to all terminal requests; production refinement
must still construct members satisfying that interface.

The conclusion is conditional on adapter semantics, complete mediation, and
the typed persistence contract. It does not conclude that a committed value
was returned to the agent or that effects of different requests are globally
linearizable.

T4-C1's plugged-execution embedding derives membership of `tau_W^S.machine` in
`Exec(WALRuntime(Cfg))`; that membership is the typed-frame persistence
premise and need not be repeated as an untyped side condition. Applying T6 to
a byte or filesystem implementation first requires a separate refinement into
`WALRuntime` under explicit encoding, checksum, flush, ordering, truncation,
and hardware-durability assumptions. `CompleteMediation` is separate because
it relates the protected physical-world invocation trace to the events present
in `tau_W^S.machine`.

## 11. Rust + Verus lemma dependency order

The mechanization should use the following dependency order; each numbered
group has only backward dependencies.

1. **Pure sequence and execution library:** `prefix_transitive`,
   `filter_map_prefix`, `concat_map_prefix`, bounded execution prefixes,
   `unique_index`, and `fold_append_one`.
2. **Typed records and calls:** request immutability, adapter-namespace and
   canonical-call equality, `CfgWellFormed`, deterministic latest-evidence
   references, reference typing, value shape, and
   `structural_enabled_is_well_typed`.
3. **Total replay:** totality of every `ApplyRecord` case, irrelevance of
   off-domain budget saturation for legal Journals, `journal_legal_prefix`,
   `replay_budget`, `replay_phase_unique`, `replay_attempt_shape`, and
   `replay_commit_unique`; then the durable attempt/outcome query bridges and
   `RecoveryCompleteD` equivalence.
4. **Append and trace evidence:** append-control phase lemmas, normalized
   `pi_append`, crash-reset `AppendProtocolPrefix`, successful-return cut
   monotonicity, `ReadyReleaseAgreement`, per-prefix `TraceAgreement`, and
   non-retroactive Invoke acknowledgment.
5. **Abstract steps:** one `broker_step_preserves_*` lemma per Event variant,
   `structural_enabled_implies_abstract_record_enabled`, exact
   `RecoveryCompleteD`, Online gating, reason-specific Unknown cases, then
   `broker_step_preserves_invariant` and finite-trace induction T1.
6. **WAL parsing:** `parse_fullframes`, `parse_torn_tail`,
   `truncate_preserves_parse`, and `complete_extends_parse_once`.
7. **WAL preservation:** one lemma per WAL action, then
   `wal_step_preserves_invariant`, append-control correspondence,
   acknowledged-prefix monotonicity, and the weak runtime simulation T3.
8. **Caller rules:** one lemma per record showing that
   `AdmissibleJournalTrace` and `AdmissibleWALTrace` supply the
   volatile/physical premise omitted by `StructuralEnabled`; prove especially
   Outcome, Commit, recovery Fail, and each reason-specific Unknown.
9. **Journal/runtime simulation:** initialize `Representation`, prove append
   call/linearize/return matching and other one-step cases, then lift the weak
   simulation by trace induction to T2.
10. **Composition and context lifting:** compose the closed T3 and T2 weak
    simulations and derive T1 safety (completed T4-C0); define the ordered
    context alphabet, masked runtime view, relational plugging, erasure,
    prefix closure, and passive/shared-visible witnesses (completed T4-C1);
    compress context states by T3 translation, construct the canonical plugged
    Broker execution, and prove exact state/view equality at mapped prefixes
    (completed T4-C2/T4).
11. **Recovery (completed T5):** use the completed T5-S0 one-step laws, T5-E0
    interval monotonicity, and T5-R0 Crash-to-first-`FinishRecover` equality;
    export the exact endpoint equalities through T4's canonical contextual map
    in T5-C0 and close theorem T5.
12. **Artifact nonvacuity (completed H1):** construct a total well-formed
    configuration, instantiate the complete T5-C0 package without premises,
    and bind verification reports to the checked source snapshots.
13. **Definition freeze (completed T6-D0):** mechanize the adapter relations,
    unique terminal/delivery selectors, outcome evidence, compatibility, and
    separate Journal/WAL bridge statement boundaries.
14. **Terminal evidence (completed T6-E0):** derive `OutcomeEvidence` from
    terminal Journal records, reference validity, exact physical provenance,
    and the request-local event projection.
15. **Terminal compatibility (completed T6-C0):** derive
    `BrokerOutcomeCompatible` by retry-class case analysis under
    `AdapterRelyTrace`.
16. **Terminal bridge (completed T6-S0):** combine T6-E0 and T6-C0 and
    discharge the atomic-Journal and typed-WAL wrapper statements using the
    existing execution, admissibility, trace-agreement, and representation
    premises, without adding a simulation invariant.
17. **First adapter semantics (completed T6-A0):** prove the generic frozen-
    bridge-to-`Refines` closure, a concrete idempotent `EnsureMember`
    `AdapterVerified` instance, and an exact nonempty typed-WAL terminal package.
18. **Executable adapter refinement (completed T6-A1):** define the operational
    `EnsureMember` adapter/service machine, derive `AdapterRely` from its
    invariant, compose it with T6-A0 and the typed-WAL runtime, and prove the
    exact reachable crash/retry Unknown package without premises.
19. **Mediation and model no-bypass (completed T6-M0):** define a first-class
    protected-service execution and a context whose closed alphabet contains no
    out-of-band protected invocation; prove exact target-mutation
    provenance, equality with the Broker/WAL invocation projection, and a
    premise-free A1 mediation witness.
20. **Prefix product (completed T6-P0):** relate valid A1, protected-service,
    and typed-WAL executions with a weak index; prove trace/history, mediation,
    and effect-state agreement at every related prefix; prove product prefix
    closure; and inhabit it with the concrete crash/retry execution.
21. **Contextual end to end (completed T6-X0):** compose the P0 adapter-to-WAL
    index with T4-C2's canonical WAL-to-Broker index, lift the all-prefix
    product through a storage-parametric plugged execution, transport terminal
    refinement and mediation to the canonical Broker trace, and inhabit the
    conditional `EnsureMember` theorem with the crash/retry execution.
22. **ReadOnly operational instance (completed T6-RO0):** define sampled reads
    and environment transitions, prove the transition invariant and
    execution-to-`AdapterRely` theorem, and close a conclusive-Fail crash/retry
    witness with zero abstract effect.
23. **Deduplicated operational safety (completed T6-DD0/T6-DD1):** define the
    keyed memoizing service machine; prove unique decision and history-cut
    provenance, slot factoring, delivered-result consistency, finite-execution
    invariant closure, the deduplication service law, execution-to-
    `AdapterRely`, and the generic `AdapterVerified` terminal refinement.
24. **Deduplicated coupled witness (completed T6-DD2):** construct exact
    adapter and typed-WAL executions in which attempt 1 silently applies and
    memoizes a value, crashes before delivery, and attempt 2 replays that value
    under the same stable key and commits it; prove exact projection, closed
    WAL/Broker representation, terminal and per-request effect refinement, one
    effect, and premise-free operational and semantic nonvacuity packages.
25. **Deduplicated protected execution and mediation (completed T6-DD3):**
    construct an independent keyed protected-service execution for the DD2
    witness; couple adapter invokes, the unique service decision, and the
    memoized retry return event by event; prove that only the decision mutates
    the protected slot, that the stable key has exactly one decision, and that
    the retry does not mutate again; derive complete mediation and equality with
    the closed M0 exclusive-handle context; and establish exact durable WAL
    authorization ancestry for both protected calls and every decision.
26. **Deduplicated contextual composition (completed T6-DD4):** construct the
    projection-length adapter/WAL weak index for the DD2 execution; prove exact
    trace/history, effect-state, and mediation agreement at every adapter prefix;
    compose that index with T4-C2's canonical WAL/Broker map; preserve context
    state, masked view, complete mediation, and T1 safety at every mapped prefix;
    transport source terminal refinement to the canonical Broker trace; and
    inhabit the complete package without premises while retaining DD2 and DD3.
27. **Request-indexed operational/protected family (completed T6-DD5):** define
    a total family of paired Deduplicated adapter/protected executions; require
    valid coverage for every terminal request in a shared WAL; derive each
    member's request-local `AdapterRely`, DD4 all-prefix product, complete
    mediation, and X0 source/target terminal transport; and inhabit the family
    coverage predicate with the DD2/DD3 witness without premises.

The first executable proof checkpoint is groups 1--5 over the atomic Journal
runtime. T6-A0 is the first publishable semantic-adapter checkpoint for one
Idempotent instance, and T6-A1 is the completed operational refinement of that
instance. T6-M0 completes the mediation/model-no-bypass checkpoint, T6-P0
completes the prefix product, and T6-X0 completes its storage-parametric
conditional end-to-end lift for `EnsureMember`. T6-RO0 completes the ReadOnly
operational instance, while T6-DD1 completes the Deduplicated invariant,
`AdapterRely`, and `AdapterVerified` boundary, and T6-DD2 completes its concrete
coupled crash/retry terminal witness at the adapter/WAL/Broker boundary. T6-DD3
completes the independent protected-service execution and mediation layer for
that distinguished run, and T6-DD4 completes its prefix/contextual P0/X0
composition. T6-DD5 completes the coverage-conditioned request-indexed family
theorem and its DD2 nonvacuity witness. Constructing family members directly
from production adapter executions remains a later implementation refinement;
production-code and byte/fsync refinements remain separate
implementation layers.
