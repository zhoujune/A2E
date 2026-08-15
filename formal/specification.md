# Verified Effect Broker: Mathematical Specification

This document presents the mathematical design and its correspondence to the
executable TLA+ oracle. The normative statement for theorem V1 is
[mechanization-contract.md](mechanization-contract.md): it separates abstract
Broker state, independently defined Journal/WAL runtimes, and proof-only ghost
evidence; defines a labeled step ADT and prefix-closed `Exec`; and fixes the
theorem layers T1--T6. Finite constants and coupled shadows described here are
model-checking devices, not theorem semantics.

## 1. Domains

Let the following sets be pairwise disjoint:

\[
R, K, P, T, O, U, A, V
\]

where `R` is the set of request identifiers, `K` capabilities, `P` principals,
`T` tools, `O` operations, `U` resources, `A` complete argument values, and
`V` normalized successful result values.
The representation-independent equations below apply to any such disjoint
sets. The normative V1 mechanization contract instantiates the Broker-facing
sets as distinct, unbounded natural-backed newtypes; arbitrary-carrier
polymorphism is a possible strengthening, not a claim of the current Verus
theorem. External state and interference witnesses remain adapter-parametric.
Each request is immutable and has projections

\[
principal_r : R \to P,\quad tool_r : R \to T,\quad
operation_r : R \to O,\quad resource_r : R \to U,\quad
arguments_r : R \to A,\quad cap_r : R \to K.
\]

Theorem V1 also assigns every request an immutable positive attempt bound
`max_attempts(r)`. The finite TLA+ oracle uses one scenario-wide `MaxAttempts`
constant, so each checked configuration is a uniform finite instantiation of
this request-indexed function rather than its theorem-level definition.

Each adapter supplies a request-indexed result predicate

\[
resultPred : R \to (V \to Prop).
\]

Each capability has immutable projections

\[
principal_k : K \to P,\quad tool_k : K \to T,\quad
operation_k : K \to O,\quad resourcePred_k : K \to (U \to Prop),
\quad argumentPred_k : K \to (A \to Prop),\quad
budget_0 : K \to \mathbb{N}.
\]

Scope matching is defined by

\[
Matches(r,k) \triangleq principal_r(r)=principal_k(k) \land
tool_r(r)=tool_k(k) \land operation_r(r)=operation_k(k) \land
resourcePred_k(k)(resource_r(r)) \land
argumentPred_k(k)(arguments_r(r)).
\]

The argument predicate is evaluated over the complete typed argument value,
not selected fields supplied by the agent. Expiry and delegation will later
strengthen `Valid`; they do not change the transition structure.

The broker allocates each `r` freshly. Abstractly, the deduplication key is an
injective function of the adapter namespace and `r`. A client replay identifier
is admitted only after it is bound to an immutable request digest; conflicting
reuse is rejected outside this transition system.

## 2. State

The broker state is

\[
S=(phase,remaining,revoked,witness,authCount,authLog,attemptLog,
externalHistory,commitCount,commitLog,committedValue,commitSource,
commitAttempt,failureAttempt,ready,readyAttempt,inflight,inflightAttempt,
received,receivedKind,receivedValue,receivedSource,receivedAttempt,
observedOK,observedValue,observedSource,observedAttempt,observedErr,
observedErrSource,observedErrAttempt,observedUnknown,crashed,recovering).
\]

For each request, `phase` is one of:

```text
New -> Authorized -> Prepared -> Armed -> Committed
                                      \-> Failed
                                      \-> Unknown
```

`Authorized` means the authority decision and budget consumption are durable.
`Prepared` means the immutable adapter request and stable key have been fixed
abstractly. The finite model represents their encoding and digest symbolically;
the typed Journal records already carry those fields, and a later byte-level
WAL refinement must preserve their concrete encodings. `Armed` means an attempt
may be reserved and sent.
`Committed` and `Failed` are definitive logical outcomes. `Unknown` means the
broker cannot safely choose either retry or completion.

`authLog`, `attemptLog`, and `commitLog` are ordered durable histories.
`ready`, `readyAttempt`, `inflight`, `inflightAttempt`, `received`, the
`received*` metadata, `observedOK`, `observedValue`, `observedSource`,
`observedAttempt`, `observedErr`, `observedErrSource`, `observedErrAttempt`, and
`observedUnknown`, and the recovery-control flag are volatile.
`externalHistory` is an append-only ghost trace of physical broker sends and
tool deliveries accepted by the broker, not a complete record of hidden
external effects or rejected stale deliveries. `receivedSource`,
`observedSource`, and `commitSource` are proof-only ghost indices into this
trace. No broker decision inspects the ghost trace. Post-crash recovery uses
only durable Journal state; normal terminalization and reconciliation may also
consume volatile observations whose classifications have already been
persisted.

This tuple is the finite Broker-oracle presentation and uses per-request sets
for volatile tokens. Theorem V1 normalizes those tokens into one `ExecSlot`, so
at most one request is Ready, InFlight, Received, or Observed globally. That
restriction is a theorem-boundary choice, not a claim that the finite oracle
already proves a concurrent executor implementation.

Let the external event alphabet be

\[
E = \{Invoke, Success(v), Failure, Ambiguous, InvalidResult(v)\}.
\]

Then

\[
externalHistory \in (R \times \mathbb{N} \times E)^*.
\]

The natural-number field is a per-request attempt identifier. Each delivery
must present the identifier assigned to its invocation. The broker accepts a
delivery only when that identifier equals the current in-flight attempt.
Accepted outcomes therefore name the unique earlier `Invoke` with the same
request and attempt identifier; a delayed outcome for an older attempt is
ignored.

The durable `attemptLog` records `Started` when an attempt is reserved and
records `Success`, `Failure`, `Ambiguous`, or `InvalidResult` only when the
corresponding delivery is persisted. `Started` is therefore durable send
intent, not proof that a physical invocation occurred. The relationship is:

```text
physical Invoke events <= durable Started records
durable outcome records <= physical delivered outcomes
```

Both inclusions can be strict at a crash. The durable attempt log is the
broker's recoverable knowledge: its `Started` records cover physical sends and
its outcome records are a history-backed subset of physical deliveries. The
larger ghost trace is specification evidence.

An invocation is physically unresolved when it has no corresponding delivered
outcome in `externalHistory`. Durable state is unresolved more broadly when a
`Started` record has no persisted outcome. This includes a crash after
reservation but before send, a crash with a request in flight, and a crash
after delivery but before `Persist*`. These states are intentionally
indistinguishable to recovery without consulting ghost history and are treated
as effect-uncertain according to the adapter class.

## 3. Authority

A capability is valid in state `S` when

\[
Valid(S,r,k) \triangleq cap_r(r)=k \land Matches(r,k) \land
k \notin revoked(S) \land remaining(S,k)>0.
\]

Authorization is one atomic durable transition. It changes `New` to
`Authorized`, records `witness(r)=k`, appends `(r,k)` to `authLog`, decrements
`remaining(k)`, and increments `authCount(k)`. This atomicity prevents a crash
from recording authority without consuming its budget, or consuming budget
without recording which request received it.

Revocation prevents future authorization. It does not retroactively invalidate
an already durable authorization witness. Strong revocation of prepared or
in-flight operations is a separate protocol and is intentionally out of scope.

## 4. Invocation and observation

`Prepare` changes `Authorized` to `Prepared`. `Arm` changes `Prepared` to
`Armed` durably before external execution. The attempt pipeline then has four
separate steps.

1. `ReserveAttempt(r)` allocates the next attempt identifier, durably appends
   `Started(r,attempt)`, and creates volatile `ready` state. It requires an
   authorization witness, no other live token for `r`, available attempt
   budget, and the adapter retry rule. For `Uncontrolled` adapters, no earlier
   durable attempt may exist.
2. `SendAttempt(r,attempt)` consumes the matching ready token, appends the
   physical `Invoke` to `externalHistory`, and creates volatile `inflight`
   state. It does not append a durable record.
3. `DeliverOK`, `DeliverErr`, `DeliverAmbiguous`, or
   `DeliverInvalidResult` consumes the matching in-flight token, appends the
   accepted physical delivery to `externalHistory`, and creates volatile
   `received` state. A stale delivery is ignored as a stuttering step. Raw
   transport arrival precedes this modeled acceptance and is outside the state
   machine.
4. The corresponding `Persist*` action consumes `received` and appends the
   outcome classification to `attemptLog`. Successful and failed outcomes then
   create volatile observation tokens used by `Commit`, `RecordFailure`,
   `RecordUnknown`, or retry policy. Persisted ambiguity or invalid data leaves
   a retry-safe request `Armed`. For an uncontrolled request it creates an
   `observedUnknown` token; `RecordObservedUnknown` then records the separate
   terminal `Unknown` transition.

A crash may occur between any adjacent steps. A delivered outcome that has not
reached `Persist*` is physical history but not durable broker knowledge. A
successful result value remains volatile until `Commit`; an invalid result can
never become a successful observation.

For an idempotent request, a failure following earlier uncertainty is not a
clean no-effect result. If attempts remain, the scheduler may explicitly clear
the volatile failure token and retry as a reconciliation step; it may instead
record `Unknown`. A crash does not create a retry option that normal execution
lacks. A conclusive failure is never retried.

`ReserveAttempt` and each `Persist*` action are abstract Journal operations;
`SendAttempt` and `Deliver*` are physical interaction events. The intended
refinement chain is `WAL -> Journal -> EffectBroker`. The bounded WAL model
checks the first arrow using typed Full/Torn frames. The coupled
`EffectBrokerJournalRefinement` model checks the second arrow: the Journal is
the implementation-facing durable authority, proof-only broker shadows equal
`Replay(journal)`, and each append is conjoined with its corresponding broker
action. This supplies physical and volatile preconditions, including the
deduplicated replay guards, without claiming that every generic Journal trace
is broker-realizable. Broker send, delivery, crash, and retry-control actions
stutter under the durable Journal projection.

The coupled product above is a bounded simulation harness and contains
proof-only Broker shadows. The theorem-V1 machines do not. They independently
define an abstract `BrokerState` and concrete Journal/WAL runtimes, with
durable state obtained from `Replay(JournalView(C))`, and relate them through
the contract's `Representation` predicate.

## 5. Crash and recovery

`Crash` preserves durable state and the ghost trace, sets `crashed=true`, resets
`recovering`, and clears all volatile ready, in-flight, received, and observed
request, attempt, value, and source state. Consequently, a physical delivery
that was not persisted is unavailable to recovery.

Recovery is a gated multi-step protocol. `BeginRecover` changes the process
from crashed to recovering; normal broker actions remain disabled. In the TLA+
oracle, `QuarantineUncontrolled(r)` changes each unsafe armed uncontrolled
request to `Unknown`, and `RecoverRecordedFailure(r)` repairs an armed request
whose latest durable attempt is a conclusive failure by recording `Failed` and
its attempt identifier. In the theorem event ADT these terminal repairs are
linearized `UnknownRec` and `FailRec` Journal records while the machine is in
Recovering mode; the TLA action names are not additional theorem labels.
`FinishRecover` is enabled only when every unsafe uncontrolled request has been
quarantined and every conclusive durable failure has been repaired. Recovery
itself may crash and restart. After finishing, an armed
retry-safe request without a conclusive failure may reserve another attempt
only according to its adapter class and remaining attempt budget. This includes
both an unresolved durable attempt and a persisted success whose volatile value
was lost before commit.

In the composed physical model, abstract `BeginRecover` is refined by an
interruptible prelude. `BeginScan` and `FinishScan` capture `Parse(media)`,
`TruncateTail` removes a Torn suffix without changing that parsed prefix, and
`AbortScan` restarts an interrupted scan. The Broker remains crashed throughout
these steps. The paired WAL/Broker `BeginRecover` transition occurs only when
the canonical prefix is installed into the process cache. `TruncateTail`
remains atomic at the typed-frame layer; partial filesystem truncation belongs
to the later byte-level refinement.

Define backend-specific committed-history abstractions:

\[
\begin{aligned}
\alpha_B(B) &\triangleq B.durable.commitLog,\\
\alpha_J(J) &\triangleq Replay(JournalView(J)).commitLog,\\
\alpha_W(W) &\triangleq Replay(JournalView(W)).commitLog,\\
JournalView(W) &\triangleq Parse(W.store.media).
\end{aligned}
\]

Each commit-log entry is a request/value pair. The completed T5-S0 theorem
proves that one accepted step either preserves the appropriate abstraction or
appends the single entry carried by its durable Commit linearization. The
completed T5-E0 theorem lifts prefix monotonicity across every ordered pair of
configurations in a finite execution. The completed T5-R0 theorem proves exact
equality across a first-`FinishRecover` episode with no recovery Commit. T5-R1
proves the general prefix-extension result and requires every recovery Commit
to cite an exact successful Outcome already present at the crash boundary. The
completed T5-C0 theorem lifts both forms through T4's canonical contextual
mapping; together these results show that recovery cannot remove, reorder, or
alter a committed logical result, or invent a recovered Commit's value or
evidence.

## 6. Safety properties

### Capability budget

\[
\forall k.\ authCount(k)+remaining(k)=budget_0(k).
\]

### Invocation authorization

\[
\forall i.\ externalHistory[i].kind=Invoke \Rightarrow
witness(externalHistory[i].request)\neq\bot \land
Matches(externalHistory[i].request,witness(externalHistory[i].request)).
\]

The transition proof additionally establishes that the witness was neither
revoked nor exhausted at its authorization linearization point.

### Scope confinement

\[
\forall r.\ \neg Matches(r,cap_r(r)) \Rightarrow
phase(r)=New \land DurableAttempts(r)=0 \land commitCount(r)=0.
\]

A resource- or argument-scope violation therefore cannot consume capability
budget, reach an adapter, or appear in the logical commit history.

### Unique logical completion

\[
\forall r.\ commitCount(r)\leq 1.
\]

This property is per broker-generated internal request identifier. Two fresh
identifiers carrying equal payloads are distinct logical requests unless a
separate replay-key admission map coalesces them.

### Uncontrolled physical at-most-once

\[
\forall r.\ RetryClass(r)=Uncontrolled \Rightarrow
Invokes(r) \leq DurableAttempts(r)\leq 1.
\]

Here `DurableAttempts` counts reserved `Started` records. The first inequality
is supplied by `AttemptLogBackedByHistory`; thus a reservation bound implies a
physical-send bound even when a reserved attempt was never sent.

### External-history well-formedness

For every request and attempt identifier,

\[
Outcomes(externalHistory,r,attempt)
\leq Invokes(externalHistory,r,attempt) \leq 1.
\]

Every delivered outcome has an earlier `Invoke` for the same request and
attempt, and at most one physical outcome is delivered per attempt. The durable
attempt log is backed by, but need not equal, the physical trace: every
`Invoke` has a durable `Started`, and every persisted outcome has a matching
physical delivery. A durable `Started` may lack an `Invoke`, and a physical
delivery may lack a durable outcome record, because crash clears the
intermediate volatile stage.

### Commit-log soundness

The commit log contains no duplicate request identifier. For a committed
request `r`, it contains exactly one pair `(r,committedValue(r))`, and

\[
\exists v.\ (r,v) \in range(commitLog) \Longleftrightarrow commitCount(r)=1
\Longleftrightarrow phase(r)=Committed.
\]

### Failure provenance

For a failed request, `failureAttempt(r)` names the latest durable attempt and
that attempt has exactly one accepted `Failure` outcome in both the attempt log
and ghost trace. If the request is not failed, `failureAttempt(r)=0`.

### Value provenance

\[
phase(r)=Committed \Rightarrow
resultPred(r)(committedValue(r)) \land
externalHistory[commitSource(r)]
=Success(r,commitAttempt(r),committedValue(r)).
\]

If `r` is not committed, `committedValue(r)=NoResult` and
`commitSource(r)=commitAttempt(r)=0`. For a deduplicated request, all successful
observations in the history carry the same value; all invalid observations
carry the same rejected value and cannot coexist with success or failure.

## 7. Parameterized theorem statement

The [mechanization contract](mechanization-contract.md#6-events-steps-executions-and-projections)
defines a disjoint labeled `Event` ADT and a machine step relation over state,
ghost evidence, and one label. `Exec(M)` is the set of finite state/event pairs
starting at `M.Init` and satisfying `M.Step` at every index; it is prefix-closed
by construction. Authorization is not part of the physical tool-event
alphabet. It is observed exactly when an `Authorize` Journal record linearizes
under `BrokerLinearize`, `JournalAppend`, `WalWriteFull`, or `WalFinishTorn`.

T1 states that every `tau in Exec(BrokerMachine(Cfg))` satisfies the Broker
safety invariant. For each `InvokeEvent(r,attempt,...)`, the unique earlier
authorization witness is the linearized `Authorize(r,k,...)` Journal record,
and `Valid` holds in the replayed prefix immediately before that record. This
removes the former ambiguity between an undefined `Authorize` trace event and
the physical `externalHistory` alphabet.

The completed [T4-C0 checkpoint](mechanization-contract.md#t4-c0-closed-wal-to-broker-composition) composes the canonical T3
`WALRuntime -> JournalRuntime` execution with the canonical T2
`JournalRuntime -> BrokerMachine` execution. It constructs the composed
weak-index map, relates every WAL prefix to its mapped Broker prefix, preserves
all normalized storage, authority, physical, adapter, control, logical,
acknowledgment, and append-I/O projections, and applies T1 both to the complete
Broker execution and to every mapped Broker prefix. This is a theorem about the
closed runtime machines only. It does not define an `AdmissibleContext`, a
plugging semantics, or shared context-state semantics; T4-C1 and T4-C2 supply
those additional layers in the completed contextual replacement theorem T4.

The completed [T4-C1 checkpoint](mechanization-contract.md#t4-c1-context-observation-and-plugging-foundation)
fixes that interface before attempting the lift. It uses one ordered
`ContextEvent` trace containing append Call/Return, Invoke/Deliver, and
Crash/BeginRecover/FinishRecover/RetryRelease/IgnoreStale observations.
`DiskFull` contributes Call followed by a failed Return in one runtime step.
The context may also inspect a masked executor view that merges
`AppendCalled(rec)` and `AppendLinearized(rec)` into the same
`AppendPending(mode,rec)` state; it sees the full mode and slot only while
append control is Idle. Consequently a hidden linearization cannot reveal its
slot update. Raw `pi_append`, Journal/logical/authority projections, WAL frames,
scan state, and ghosts remain private.

T4-C1 uses event-synchronized context semantics. A visible runtime step supplies
the context relation with its current context state, the masked pre-step
`ContextView`, the nonempty normalized event delta, and the masked post-step
`ContextView`; the latter is also the view at the next execution prefix. Thus a
context may react immediately to the executor slot exposed by an append return
without learning the hidden linearization point. Hidden events preserve the
complete view and context state exactly. This V1 interface does not model
autonomous context-only transitions or a separate observation transition after
the machine execution terminates; claims about those behaviors require a
stronger interface.

Plugged executions are defined structurally and independently for the WAL,
Journal, and Broker: each contains one context state per machine configuration,
the exact backend initialization, and the exact backend step relation. T4-C1
proves erasure to each closed `Exec`, prefix closure, matched-history and masked-
view compatibility, an accepting inert context, shared zero-step witnesses,
and a positive shared one-`Crash` witness. T4-C1 alone does not construct a
target plugged execution. The completed
[T4-C2 checkpoint](mechanization-contract.md#t4-c2-contextual-replacement-and-composition)
performs that lift. It compresses context states exactly for WAL events whose
T3 `translate_event` result is `Some`, rather than by context-delta visibility,
constructs canonical plugged Journal and Broker executions, and proves exact
shared context-state and complete ordered
endpoint `ContextView` equality at every prefix named by the canonical composed
map. Under the exported `StorageParametricContext` premise, the Broker product
retains C0 weak simulation, normalized projection agreement, full T1 safety,
and mapped-prefix T1 safety. The cumulative target verifies 735 obligations.

The completed T5-S0 checkpoint then proves exact one-step committed-history
laws for all three machines. `alpha_B` is the Broker durable `commit_log`;
`alpha_J` and `alpha_W` are `Replay(JournalView).commit_log`, with the WAL
`JournalView` equal to `Parse(media)`. Only
`BrokerLinearize(CommitRec)`, `JournalAppendLinearize(CommitRec)`, and
`WalWriteFull(CommitRec)` or `WalFinishTorn(CommitRec)` append one exact
`CommitEntry`; every other accepted step stutters. Its WAL theorem requires
only the runtime `wal_invariant`, excluding ghost-evidence agreement, and proves
exact parsed-view behavior first, including `WalWriteTorn` stuttering and
equality across `TruncateTail`. Reachable states derive that premise from
T3-W0's `basic_invariant`. The cumulative target verifies 744 obligations; the
T5-S0 dependency delta is 9.

Consequently every accepted theorem-machine step extends committed history by
at most one Commit record:

\[
\alpha_{commit}(S) \preceq \alpha_{commit}(S').
\]

The exact S0 classification implies that `Crash`, `BeginScan`, `FinishScan`,
`TruncateTail`, `AbortScan`, `BeginRecover`, recovery-mode
`BrokerLinearize(FailRec)` or `BrokerLinearize(UnknownRec)`, and
`FinishRecover` preserve `alpha_commit` by equality. A recovery-mode
`CommitRec` instead appends its one exact `CommitEntry`. The completed T5-E0 theorem
states, for each backend execution `tau` and indices
`i <= j < tau.configs.len()`,

\[
\alpha_{commit}(\tau.configs[i])
  \preceq \alpha_{commit}(\tau.configs[j]).
\]

Its only machine premise is the corresponding `Exec`; the WAL proof derives
`basic_invariant` for reachable configurations and discharges `wal_invariant`
internally. T5-E0 verifies 748 cumulative obligations, 4 beyond T5-S0; the 33
targets registered through T5-E0 contained 784 dependency-aware non-duplicated
obligations.

T5-R0 defines, for event indices `crash` and `finish`,

\[
\begin{aligned}
RecoveryEpisode(\tau,crash,finish) \triangleq{}&
crash < finish < |\tau.events| \\
&\land\ \tau.events[crash]=Crash \\
&\land\ \tau.events[finish]=FinishRecover \\
&\land\ \forall k.\ crash<k<finish
   \Rightarrow \tau.events[k]\ne FinishRecover.
\end{aligned}
\]

For Broker, atomic-Journal, and typed-WAL executions it proves that any durable
linearization in the episode is a permitted recovery repair: `CommitRec`,
conclusive `FailRec`, or recovery `UnknownRec`. Define

\[
CommitStutteringEpisode(\tau,c,f) \triangleq
RecoveryEpisode(\tau,c,f) \land
\forall k.\ c<k<f \Rightarrow \neg RecoveryCommit(\tau.events[k]).
\]

Under this explicit no-Commit premise, every episode commit delta is empty and
`alpha_commit` is unchanged. Consequently,

\[
Exec(Cfg,\tau) \land CommitStutteringEpisode(\tau,crash,finish)
\Rightarrow
\alpha_{commit}(\tau.configs[crash])
=\alpha_{commit}(\tau.configs[finish+1]).
\]

The WAL theorem derives its invariants from `Exec`. Minimal Broker and Journal
episodes, a complete scan/truncate WAL episode, and a repeated-`Crash` Broker
episode prove the equality corollary nonvacuous. T5-R0 verifies 773 cumulative
obligations, 23 beyond T5-E0.

T5-R1 states the general WAL recovery result without the stuttering premise:

\[
\begin{aligned}
Exec(Cfg,\tau) \land RecoveryEpisode(\tau,c,f)
\Rightarrow{}&
\alpha_W(\tau.configs[c]) \preceq
\alpha_W(\tau.configs[f+1])\\
&\land\ \forall k.\ c<k<f \land RecoveryCommit(\tau.events[k])\\
&\qquad\Rightarrow CrashPrefixBacked(\tau,c,\tau.events[k]).
\end{aligned}
\]

For `CommitRec(request,attempt,value,outcome_ref)`, `CrashPrefixBacked` requires
the Journal parsed at `configs[c]` to contain exactly
`Outcome(request,attempt,Success(value))` at `outcome_ref`. Recovery terminal
records preserve both Outcome observation and LSN queries, so evidence cannot
appear retroactively. The executable proof surface makes the decision boundary
explicit:

```text
RecoveryDecision(record) =
  Commit   if record is CommitRec
  Fail     if record is FailRec
  Unknown  if record is UnknownRec
  NotRecovery otherwise
```

Every record enabled outside `Online` is proved to classify as Commit, Fail, or
Unknown. Commit is the only class with an effect-value claim, and its guard is
sound and complete exactly when `DurableSuccess` holds in the pre-state; Fail
and Unknown are terminal repairs without a successful-value claim. A separate
one-step theorem composes this classification and guard with exact committed-
history extension. T5-R1 verifies 787 cumulative obligations, 14 beyond
T5-R0. H2 gives a premise-free 26-event witness whose crash history has length
zero and recovered history has length one; its old stuttering premise is false.

For T5-C0, let `tau_W^S` be the source plugged WAL execution, `tau_B^S` be
T4-C2's canonical plugged Broker execution, `tau_W` and `tau_B` be their machine
components, and `mu` be the canonical composed map. The all-prefix bridge is

\[
\forall i \le |\tau_W.events|.\quad
\alpha_W(\tau_W.configs[i])
=\alpha_B(\tau_B.configs[\mu[i]]).
\]

For every source `RecoveryEpisode(tau_W,crash,finish)`, C0 first transports the
general theorem: both the WAL history and the mapped Broker history at the
crash endpoint are prefixes of their histories at `finish+1`, and the WAL
episode satisfies crash-prefix Commit provenance. For a
`CommitStutteringEpisode`, C0 additionally proves the four endpoint equalities

\[
\begin{aligned}
\alpha_W(\tau_W.configs[crash])
  &= \alpha_W(\tau_W.configs[finish+1]),\\
\alpha_W(\tau_W.configs[crash])
  &= \alpha_B(\tau_B.configs[\mu[crash]]),\\
\alpha_W(\tau_W.configs[finish+1])
  &= \alpha_B(\tau_B.configs[\mu[finish+1]]),\\
\alpha_B(\tau_B.configs[\mu[crash]])
  &= \alpha_B(\tau_B.configs[\mu[finish+1]]).
\end{aligned}
\]

The target endpoint is `mu[finish+1]`; C0 does not prove that the canonical
Broker trace itself satisfies `RecoveryEpisode`. Its stepwise bridge instead
proves exact equality of WAL and Broker commit deltas for matched steps and an
empty WAL commit delta for weakly erased steps.

The general full-configuration theorem requires `FullConfigWF`,
`StorageParametricContext`, `PluggedWalExec`, and a source recovery episode; its
conclusion includes T4-C2, all-prefix mapped equality, mapped prefix extension,
and crash-prefix provenance. The equality export additionally requires the
commit-stuttering predicate; its paper wrapper replaces `FullConfigWF` with
`PaperConfigWF`. A combined inert-context
witness uses the six WAL events
`Crash; BeginScan; FinishScan; TruncateTail; BeginRecover; FinishRecover`, seven
machine configurations, and seven equal context states; it proves the complete
C0 premise conjunction and conclusion are inhabited.

T5-C0 verifies 805 cumulative obligations, 18 beyond T5-R1: commit-delta,
representation, mapped-prefix, general prefix/provenance transport, equality-
corollary, and contextual bridge/export obligations plus the combined witness.
The oracle actions
`RecoverRecordedFailure` and `QuarantineUncontrolled` are the executable
counterparts of those two recovery-mode terminal records.

H1 follows T5-C0 as an artifact/nonvacuity checkpoint. It defines a total
`FullConfig` in which every request is uncontrolled, has no stable key, and has
`max_attempts = 1`; every capability has unit budget and universal resource and
argument scope; and every request/result pair is valid. `FullConfigWF` is proved
directly, with deduplicated-key injectivity vacuous because the configuration
contains no deduplicated request. The premise-free H1 package theorem combines
that configuration, the inert context, and the six-event minimal contextual WAL
recovery execution at `crash = 0`, `finish = 5`, and establishes the entire
T5-C0 premise conjunction and conclusion. H1 adds 3 obligations: the total
configuration witness, the concrete T5-C0 package, and its existential
inhabitation theorem. The cumulative result is 804 verified obligations with
zero errors.

This H1 witness establishes consistency of the cumulative package, not a new
recovery or adapter theorem. In particular, the concrete minimal execution does
not exhibit a nonempty pre-crash commit history or an external effect. The
Verus evidence report records SHA-256 hashes for its schema, every registered
source, the runner, the toolchain lock, and the fresh Rust tree; complete
source/import registration and immediate-predecessor checks are enforced, and
Verus reads only an exact read-only source snapshot checked around each target.
TLC separately runs from hash-checked per-run model and tool snapshots. Its
manifest validation rejects duplicate names/configurations, invalid tiers or
fields, missing inputs, and any unregistered `formal/*.cfg`, and its unique
machine-readable report is enabled by default.

T6-D0 follows as a definition-only semantic checkpoint. It introduces the
generic external run and adapter interpretation, requires standalone adapter
histories to be request-local, and makes terminal-record and delivery lookup
total while returning `Some` only for unique evidence. `OutcomeEvidence` takes
the configuration explicitly because Unknown evidence checks the exact
configuration-dependent structural rule. Commit, Fail, and Unknown evidence
and compatibility are separate named branches. One shared broker-state
statement and separate Journal/WAL wrappers fix the shape of the later T6-S0
proof without establishing it at D0; T6-S0 now discharges that frozen shape.
The T6-D0 target verifies 821 cumulative obligations with zero errors, 16
beyond T5-C0.

T6-E0 proves the generic terminal-evidence implication. Given a Broker contract
invariant, exact equality of its durable records and physical history with the
corresponding event projections, and `terminal(tau,r)=Some(o)`, it derives
`OutcomeEvidence(Cfg,B.core.evidence.records,r,pi_adapter(tau,r),o)`. Commit and
Fail references name exact Outcome records in the strict pre-terminal prefix
and select the unique matching delivery. Unknown reuses the exact prefix
`StructuralEnabled` rule and its durable reason-specific anchor. The result is
independent of an external run or adapter effect relation. T6-E0 verifies 839
cumulative obligations with zero errors, 18 beyond T6-D0. Together with H1's
independent 3-obligation delta, its historical 38-target registry contained 857
dependency-aware non-duplicated obligations.

T6-C0 proves the compatibility half of the frozen Broker statement under
`PaperConfigWF`, the Broker contract invariant, exact Journal and physical
event projections, `AdapterRely`, and a selected terminal outcome. It reuses
T6-E0's evidence theorem and proves the class-specific branches of
`BrokerOutcomeCompatible`. Commit requires the exact successful delivery and,
for `Uncontrolled`, that it belongs to the only invoked attempt. Fail requires
the exact failure delivery; `ReadOnly` adds no retry condition, `Idempotent`
requires a selected failure for every physical invocation, `Deduplicated`
requires a resolved failure with no Success or InvalidResult observation, and
`Uncontrolled` requires a single failure on its only invoked attempt. Unknown
requires a legal Journal, the exact unique `UnknownRec`, and its reason guard
over the strict pre-terminal prefix; an `Uncontrolled` history must additionally
contain at most one invocation. T6-C0 verifies 856 cumulative obligations with
zero errors, 17 beyond T6-E0. Its 39 registered targets contain 874
dependency-aware non-duplicated obligations, and the sum of their cumulative
target obligations is 18,224.

T6-S0 combines the T6-E0 and T6-C0 conclusions into the frozen
`TerminalEvidenceAndCompatibility` predicate. Its atomic-Journal wrapper uses
the assumed runtime execution, trace admissibility, final-prefix trace
agreement, and existing Journal-to-Broker representation to recover the core
Broker invariant and exact Journal/physical projection equalities. Its typed-
WAL wrapper performs the same transport through the existing WAL-to-Broker
representation, which exposes the Journal projection of the final WAL state.
Neither wrapper proves a new backend simulation invariant: both consume the
already-stated execution, admissibility, trace-agreement, and representation
premises and rewrite the core conclusion to the final backend evidence records.

T6-S0 adds 6 obligations beyond T6-C0 and its current target verifies 862
cumulative obligations with zero errors. Its historical retained target
verified 840 cumulative obligations. That 40-target registry
contained 880 dependency-aware non-duplicated obligations, and the sum of its
cumulative target obligations was 19,064. T6-S0 does not establish `Refines`, `AdapterVerified`,
external one-effect semantics, a concrete terminal witness or premise-
inhabitation theorem, or `ReturnResult`. H1's inert witness does not inhabit
the terminal `AdapterRely` premise.

T6-A0 closes the first adapter-semantic instance. Its generic theorem combines
`AdapterVerified` with T6-S0's `TerminalEvidenceAndCompatibility` conclusion,
Journal legality, and `AdapterRely` to derive `Refines`; selected-terminal
event, Journal, and WAL wrappers derive `PerRequestEffectRefinement`. The
concrete idempotent `EnsureMember` interpretation models an external resource
set. Environment additions define the interference baseline, zero effect leaves
that baseline unchanged, and one effect adds the request's target. Recorded
linearized attempts must have been invoked; their set selects the one-effect
branch when nonempty and the zero-effect branch otherwise. The proof establishes
`AdapterVerified` for the fixed concrete paper and nondegeneracy on an exact
empty-to-singleton run.

The concrete package contains a 20-event, 21-configuration typed-WAL execution
with six acknowledged records (`Authorize`, `Prepare`, `Arm`, `Start`,
`Outcome`, `Commit`), one Invoke, one delivered Success, exact final
representation, and a selected Commit. The premise-free existential fixes the
paper, request, run, outcome, records, and physical history. T6-A0 verifies 885
cumulative obligations with zero errors, 23 beyond the current 862-obligation
T6-S0 closure. The historical 41-target registry contained 904 dependency-aware
non-duplicated obligations and sum 19,951 target obligations. The current T6-S0
count is one above its historical checkpoint because T6-A0 adds a conservative
definitional configuration-accessor lemma at T1.

At the historical T6-A0 checkpoint, 41 registered targets contained 904
dependency-aware non-duplicated obligations and summed 19,951 target
obligations. T6-A0 verifies a semantic adapter contract, not executable adapter
or remote-service code. Its crash-erased Invoke/Success/Invoke/Failure example
is an adapter sequence law rather than a Broker/WAL execution.

T6-A1 closes that model-level execution gap for `EnsureMember`. Its explicit
adapter/service transition system models observed global events, silent service
linearization, environment interference, crash/recovery modes, active attempts,
and exact membership state. The machine invariant derives `AdapterRely`, and a
generic theorem couples such an operational execution to the T6-A0 typed-WAL
terminal theorem. A premise-free witness realizes `Invoke1, Success1, Crash,
recover, Invoke2, Failure2`: attempt 1 linearizes but its success is not
journaled before the crash, while attempt 2 fails without linearizing. The
terminal is Unknown, not Fail, and the run denotes exactly one abstract
insertion. T6-A1 verifies 937 obligations with zero errors, 52 beyond T6-A0.
At the historical pre-K4 checkpoint, all 42/42 targets passed, with 956 dependency-aware
non-duplicated obligations and 20,867 summed target obligations.

T6-A1 verifies an operational transition system and reachable execution, not
production Rust, network transport, or remote-service code. T6-A0/A1 by
themselves do not prove byte/fsync persistence, `CompleteMediation`, protected
handles, `ReturnResult`, multi-request/global linearizability, liveness, or
least privilege for the synthetic full-capability witness.

T6-M0 adds a separately defined protected-service execution. Each accepted
call stores its request, attempt, descriptor, Journal and acknowledged cuts,
and source index; eventwise coupling proves these equal the canonical A1/WAL
Invoke. `BrokerInvoke` also requires a request-local, fresh attempt key. Service linearization and return
transitions reference that call by sequence index. Only
`ServiceLinearize(call_ref)` can mutate the target; nontarget environment
additions are separate, and the service alphabet contains no raw or
context-owned target-mutation constructor.

The A1 and protected executions are related event by event, but final protected
trace equality is not assumed by the coupling definition. Prefix induction
derives that the service-generated, cut-erased calls equal `pi_invocations` of
the observed global trace. A second execution induction proves that stored
service calls are precisely those generated calls. Thus `CompleteMediation` is
derived across independently defined executions rather than made true by
choosing the protected trace to equal the Broker projection.

T6-M0 also supplies a separate storage-parametric T4-C1 context. Its state audits
only `ContextEvent::Invoke` labels exposed through the masked storage view; its
interface contains no protected-service state, handle, invocation primitive, or
mutation field. Every admitted plugged WAL execution under this context derives
the same invocation-projection equality. This is a closed-alphabet no-bypass
property in the formal model, not verification of descriptor distribution,
process isolation, network ACLs, or production service authentication.

Under the coupled deployment relation, every protected call's source index names
an exact WAL Invoke. T4-C0 maps that
nonsilent event into the canonical Broker execution, and T1's
`invoke_temporal_at` proves canonicality, positive and bounded acknowledged
cuts, acknowledged authorized Start ancestry, unique Authorize and Start
counts, and a successful append return strictly before invocation. The coupled
linearization theorem applies this durable-authorization provenance to each
target action without an added semantic premise.

The reusable `m0_deployment_exec` relation packages the well-formed
configuration, A1/protected eventwise coupling, typed-WAL execution, and exact
A1/WAL trace agreement. From it, T6-M0 generically derives the quantified property
that every `ServiceLinearize` references a durably authorized call. A bare
protected-service execution defines only the service transition grammar and is
not, on its own, an authorization judgment.

The premise-free T6-M0 witness reuses A1's 32 adapter events and 31 typed-WAL
events, and independently constructs a 32-step protected execution. It accepts
two calls originating at zero-based WAL indices 12 and 23; attempt 1 is the sole
linearization and returns Success, while attempt 2 returns Failure without
linearizing. Both calls are durably authorized, no environment addition occurs,
and the protected-service and audit-context traces both equal the WAL
invocation projection. The T6-M0 target verifies 998 cumulative obligations
with zero errors, 61 beyond T6-A1. The historical pre-K4 T6-M0 checkpoint had
43/43 targets, 1,017 dependency-aware non-duplicated obligations, and 21,844
summed target obligations. The current retained suite extends this target
through T6-DD5 and is reported below.

T6-M0 does not verify production Rust, transport, OS isolation, or remote-
service code; byte/fsync persistence; `ReturnResult`; least privilege;
multi-request/global linearizability; or liveness. It also does not establish a
general prefix-indexed A1-to-WAL stuttering simulation or the contextual T6
lift. Its completed prefix arguments concern the protected call trace and
closed-interface audit context.

T6-P0 adds that prefix-indexed relation for the fixed single-request
`EnsureMember` model. A weak map relates each A1 configuration to a typed-WAL
configuration: `Observe(global)` consumes exactly one identical WAL label,
while `ServiceLinearize` and `EnvironmentAdd` stutter. From valid A1,
protected-service, and WAL executions satisfying this step coupling, the
generic T6-P0 theorem derives at every mapped prefix exact global-trace and
request-history agreement, valid truncated executions, equality between
accepted protected calls and the WAL invocation projection,
`CompleteMediation`, and agreement on membership, environment additions, and
linearized attempts.

Both the execution-pair relation and the full product are closed under taking
an A1/protected prefix and its mapped WAL prefix. A canonical map counts the
observed global events in each A1 prefix and recovers the step relation when
whole-trace equality is already supplied. T6-P0 is therefore a conditional
execution-pair theorem, not a theorem constructing a matching typed-WAL
execution for every A1 execution.

The T6-P0 witness uses the existing 32 A1 events, the separately constructed 32
protected events, and 31 WAL events. Its 33-point map stutters across the
attempt-1 service linearization at points 13 and 14 and retains complete
mediation and final effect-state agreement. T6-P0 verifies 1,021 cumulative
obligations with zero errors, 23 beyond T6-M0.

T6-X0 supplies the storage-parametric contextual lift. It composes the T6-P0
adapter-to-WAL map with T4-C2's canonical WAL-to-Broker map and proves an exact
all-prefix relation: request-local adapter history agrees with the mapped Broker
projection, plugged context state and masked view agree at the composed points,
the external run is grounded in the protected-service state, and each mapped
Broker prefix satisfies T1. Given a selected terminal, the conditional theorem
transports the exact terminal, `Refines`, per-request effect refinement, and
`CompleteMediation` from the WAL trace to the canonical Broker trace.

The concrete X0 theorem reuses the 32-adapter/32-protected/31-WAL execution and
T6-M0's exclusive audit context. Its exact terminal is
`Unknown(NonConclusiveFailure)`; the run denotes one rather than zero effects;
the protected target changes through exactly one durably authorized
linearization; and mediation holds at the canonical Broker endpoint.
`t6_x0_contextual_end_to_end_nonvacuity` exports this package without premises.
T6-X0 verifies 1,043 cumulative obligations with zero errors, 22 beyond T6-P0.
The historical pre-K4/DD run passed all 45/45 registered targets, contained
1,062 dependency-aware non-duplicated obligations, and summed to 23,866 target
obligations. The current retained run passes all 72/72 registered targets,
contains 1,511 dependency-aware non-duplicated obligations, and sums to 38,952
target obligations.

The complete hierarchy is T1 parameterized Broker safety, T2 independent
atomic-Journal runtime simulation, T3 typed-WAL simulation, completed T4-C0
closed-machine composition, completed T4-C1 context observation and structural
plugging, completed T4-C2 contextual replacement and composition, T5 committed-
history prefix preservation, and T6 conditional end-to-end per-request effect
refinement. T1--T5, H1, T6-D0, T6-E0 evidence, T6-C0 compatibility, T6-S0
composition plus backend wrappers, the first concrete T6-A0 adapter semantics,
the T6-A1 operational refinement, and T6-M0 model-level mediation and no-bypass
and T6-P0 prefix-indexed execution product, and the conditional single-request
T6-X0 contextual end-to-end theorem are now complete.
Under the complete stated
persistence, mediation, context, and adapter rely conditions, the broker
provides authorized, per-internal-request at-most-once logical completion and
crash-stable abstract history. It does **not** claim physical exactly-once
execution, coalescing of separately admitted equal payloads, liveness, returned
result delivery, global linearizability of effects across requests, reverse
contextual equivalence, autonomous context steps, production protected-handle
isolation, matching-WAL construction for arbitrary adapter runs, additional
adapter classes, or byte-level WAL correctness.

## 8. Component proof obligations

| Component | Assumption supplied | Obligation discharged |
|---|---|---|
| Request boundary | Immutable decoded request | No unchecked field reaches capability matching or an adapter |
| Capability monitor | Capability metadata authenticity | Authorization implies matching scope and available budget |
| Journal bridge | Typed atomic append and adapter rely conditions | Bounded coupled simulation checks `ReplayCoupling`; T2 relates independently defined Journal and Broker runtimes |
| Typed WAL model | Symbolic Full/Torn frames, complete-frame linearization, and atomic tail removal | Bounded temporal traces with interrupted recovery refine Journal |
| Composed WAL/Broker product | One pending record and WAL-quiescence-gated external steps | Bounded WAL, Journal, and Broker temporal projections agree; every Invoke has an acknowledged Start |
| Closed runtime composition | T2 and T3 simulation premises over their independent runtime executions | T4-C0 constructs a direct WAL-to-Broker weak simulation and derives T1 safety for the target and every mapped prefix |
| Context observation and plugging | Ordered `ContextEvent`, masked endpoint views, event-synchronized context relations, and exact backend runtime steps | Completed T4-C1: structural WAL/Journal/Broker plugging, erasure, prefix closure, hidden stuttering, inert and zero-step witnesses, and a positive shared `Crash` witness |
| Contextual replacement | Well-formed configuration, storage-parametric context, a plugged WAL execution, and the completed T4-C0/T4-C1 results | Completed T4-C2: canonical plugged Broker construction; T3-translation-selected context compression; exact context-state and ordered endpoint-view equality at every canonical mapped prefix; inherited C0 simulation, projection, T1, and mapped-prefix T1 conclusions |
| Verified executable record kernel | Well-formed finite manifest and a legal sequence over the eight supported non-Revoke records | K4-A4 preserves replay/durable coupling, exact LSN/cuts, terminal evidence, and Online/Crashed/Recovering control; recovery admits only terminal Commit/Fail/Unknown, includes a durable-success Commit witness, and leaves recovery only when every Armed request satisfies the class-sensitive resume predicate |
| Rust append/replay integration | Ordinary Rust record translation and an explicitly supplied K4 `AppendGate` | K4-I0 forces its selected broker append/replay traces through K4 preview before WAL and K4 commit after the durable LSN; K4-I1 additionally removes the ungated opener from submission evaluation, requires immutable manifests, and attests preview/commit, replay, terminal recovery, and verified resume coverage. Both are finite integration evidence, not whole-program refinement |
| Byte-level WAL implementation | Encoding, checksum, partial-truncation, flush/fsync, atomic-write, and filesystem assumptions | Concrete bytes and recovery parsing refine the typed WAL/Journal contract |
| Scheduler | One globally serialized executor slot in V1 | No simultaneous invocation; multi-worker ownership is deferred |
| Adapter semantics | Declared retry and environment contract | T6-A0 proves the first concrete `EnsureMember` semantic interpretation refines zero or one abstract set insertion |
| Executable adapter model | Concrete adapter/service protocol steps | T6-A1 proves the operational `EnsureMember` execution refines the T6-A0 semantic contract; refinement of production Rust/network/service code remains open |
| Protected-service mediation | Eventwise A1/service coupling plus the structurally restricted storage-parametric audit context | T6-M0 derives the independent service and context traces from the WAL invocation projection, proves that only a prior call can cause a target action, and connects each such action to T1 durable authorization; production OS/network isolation remains open |
| Prefix execution product | Valid A1/protected and typed-WAL executions plus weak event coupling | T6-P0 proves exact mapped-prefix trace/history, mediation, and effect-state agreement and prefix closure for conditionally paired executions; T6-P0 alone neither constructs a matching WAL execution nor includes a contextual lift |
| Contextual end-to-end composition | Storage-parametric context, plugged WAL execution, T6-P0 prefix product, and selected terminal | T6-X0 composes the adapter/WAL and WAL/Broker maps, proves exact all-prefix history/context/view and T1 transport, and transports terminal refinement and complete mediation to the canonical Broker trace; the premise-free 32/32/31 witness ends Unknown with one abstract effect and one durably authorized protected linearization |
| Recovery | Durable journal is readable | Committed history extends monotonically; every recovery Commit has crash-prefix successful-Outcome provenance; without a recovery Commit the endpoints are equal; unsafe retries are rejected |
| Terminal bridge | `AdapterRely`, a selected terminal, and the existing Journal/WAL execution, admissibility, trace-agreement, and representation premises | T6-S0 combines terminal evidence with compatibility and transports the result to each backend's final evidence records without adding a simulation invariant |
| Adapter closure | `AdapterVerified`, Journal legality, `AdapterRely`, and terminal evidence/compatibility | T6-A0 derives `Refines` and per-request effect refinement and supplies an exact nonempty typed-WAL witness |

The proof hierarchy is therefore:

```text
WAL  ->  Journal  ->  EffectBroker
```

The Broker theorem assumes atomic Journal operations. The Journal model
establishes record, prefix, reference, and replay safety. The coupled bridge
supplies the physical delivery and volatile-token witnesses required by
`Persist*`, constrains appends with the Broker's adapter-environment guards,
and checks a temporal refinement to `EffectBroker`. The WAL model checks
`WAL -> Journal` over symbolic Full/Torn frames, where a completed Full frame
is the Journal linearization point. The composed
`EffectBrokerWALRefinement` model replaces the atomic append in the bridge and
checks all three temporal projections directly. Its state relation is

```text
shadowJournal = Parse(media)
BrokerDurable = Replay(Parse(media)).
```

The Journal may retain more information than the abstract Broker. In
particular, a successful `Outcome` record contains the value even though
`EffectBroker` loses its volatile copy after a pre-commit crash. This is valid
concrete strengthening: `ReplayCoupling` erases the extra value, and the bridge
requires a live `observedOK` token before appending `Commit`, so replay alone
cannot fabricate terminal success. The bounded composed model checks this
replacement for uncontrolled and idempotent-retry configurations, including
complete unacknowledged frames, aborted recovery scans before and after tail
truncation, and replay installation. The corresponding unbounded finite forward
rule is now the machine-checked
[T4-C2 parameterized contextual replacement theorem](mechanization-contract.md#t4-c2-contextual-replacement-and-composition).
A later byte-level refinement must
also add record decoding, checksums, partial-truncation behavior, and concrete
flush/fsync assumptions.

The equalities above describe the bounded coupled product only. The
parameterized proof does not store `shadowJournal` or Broker durable variables
inside the concrete runtime. Its `Representation` relation instead states
`G.records = JournalView(C)` and `B.durable = Replay(G.records)` between
independent states. Similarly, `MaxJournalLength` bounds only TLC exploration;
theorem V1 admits any finite Journal and requires an explicit pre-stage
`DiskFull` behavior for bounded implementations. The TLA+ `MaxAttempts`
constant is also an oracle instantiation; theorem V1 uses the request field
`max_attempts(r)` in reservation and retry obligations.

Here "atomic Journal" refers to the durability linearization, not an
indivisible caller interaction. The mechanization contract gives both storage
backends the same append Call -> Linearize -> Return protocol. AtomicJournal
may delay Return after its atomic linearization; WAL linearizes at a completed
Full frame and returns at `FlushAck`. This shared protocol is what makes the
post-write/pre-ack crash window compositional rather than an implicit timing
assumption.

## 9. Adapter refinement

For each request `r`, the primary adapter contract is a trace-refinement
relation

\[
Refines_c(\eta_r,x_0,x_1,outcome),
\]

relating the attempt-specific interaction trace, external pre-state,
post-state, and logical outcome under stated interference assumptions. The
effect-count set `{0}`, `{1}`, or `{0,1}` is only a derived diagnostic summary.
The broker may record `Committed` or `Failed` only when the class-specific
relation permits that terminal outcome; otherwise it retries, reconciles, or
records `Unknown`.

Read-only adapters always denote zero mutations. Idempotent adapters collapse
repeated applications to one abstract mutation but do not promise consistent
results. Deduplicated adapters use a stable remote key and exclude conflicting
terminal results. Uncontrolled adapters allow only one physical invocation.

The complete definitions, the treatment of contradictory post-crash outcomes,
and adapter proof obligations are given in
[adapter-refinement.md](adapter-refinement.md).

## 10. Value refinement

A successful observation carries a typed value `v`. It is volatile until the
matching `Outcome` append, which durably stores the request, attempt, and exact
successful value. `Commit` then stores `v` in the durable committed-value map,
stores the durable attempt identifier, records a proof-only source index, and
appends `(r,v)` to the commit log. A crash before `Outcome` clears the volatile
value; a crash after `Outcome` may recover `Commit`, but only by citing that
crash-prefix Outcome and its exact LSN. The abstract terminal Journal record contains
the request, attempt, value or canonical encoding, and any response digest
needed for audit; it does not contain a ghost-history index. The concrete WAL
must preserve and recover that Journal record exactly.

The finite TLA+ oracle represents adapter result predicates with one global
`AllowedResults` set. This validates payload provenance but not
adapter-specific typing. Theorem V1 instead quantifies over `result_pred(r,v)`,
and each adapter's semantic proof uses a request-indexed relation
`ResultSpec_r(x,x',v)` connecting the external pre-state, post-state, and typed
result. Full definitions and proof obligations are given in
[value-refinement.md](value-refinement.md).
