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
equality across a first-`FinishRecover` episode. The completed T5-C0 theorem
lifts committed-history agreement through T4's canonical contextual mapping;
together these results show that recovery cannot invent, remove, reorder, or
alter a committed logical result.

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
and mapped-prefix T1 safety. The cumulative target verifies 734 obligations.

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
T3-W0's `basic_invariant`. The cumulative target verifies 743 obligations; the
T5-S0 dependency delta is 9.

Consequently every accepted theorem-machine step extends committed history by
at most one Commit record:

\[
\alpha_{commit}(S) \preceq \alpha_{commit}(S').
\]

The exact S0 classification implies that `Crash`, `BeginScan`, `FinishScan`,
`TruncateTail`, `AbortScan`, `BeginRecover`, recovery-mode
`BrokerLinearize(FailRec)` or `BrokerLinearize(UnknownRec)`, and
`FinishRecover` preserve `alpha_commit` by equality. The completed T5-E0 theorem
states, for each backend execution `tau` and indices
`i <= j < tau.configs.len()`,

\[
\alpha_{commit}(\tau.configs[i])
  \preceq \alpha_{commit}(\tau.configs[j]).
\]

Its only machine premise is the corresponding `Exec`; the WAL proof derives
`basic_invariant` for reachable configurations and discharges `wal_invariant`
internally. T5-E0 verifies 747 cumulative obligations, 4 beyond T5-S0; the 33
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

For Broker, atomic-Journal, and typed-WAL executions it proves, for every
`crash <= k <= finish`, that any durable linearization is a permitted recovery
repair, the commit delta is empty, and `alpha_commit` is unchanged by that
step. Consequently,

\[
Exec(Cfg,\tau) \land RecoveryEpisode(\tau,crash,finish)
\Rightarrow
\alpha_{commit}(\tau.configs[crash])
=\alpha_{commit}(\tau.configs[finish+1]).
\]

The restriction to `FailRec` and recovery `UnknownRec` is derived from machine
enabledness, not assumed by `RecoveryEpisode`. The WAL theorem derives its
invariants from `Exec`. Minimal Broker and Journal episodes, a complete
scan/truncate WAL episode, and a repeated-`Crash` Broker episode prove
nonvacuity. T5-R0 verifies 769 cumulative obligations, 22 beyond T5-E0; the 34
registered targets contain 806 dependency-aware non-duplicated obligations.

For T5-C0, let `tau_W^S` be the source plugged WAL execution, `tau_B^S` be
T4-C2's canonical plugged Broker execution, `tau_W` and `tau_B` be their machine
components, and `mu` be the canonical composed map. The all-prefix bridge is

\[
\forall i \le |\tau_W.events|.\quad
\alpha_W(\tau_W.configs[i])
=\alpha_B(\tau_B.configs[\mu[i]]).
\]

For every source `RecoveryEpisode(tau_W,crash,finish)`, C0 proves the four
endpoint equalities

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

The full-configuration theorem requires `FullConfigWF`,
`StorageParametricContext`, `PluggedWalExec`, and a source recovery episode. The
paper export replaces `FullConfigWF` with `PaperConfigWF` and otherwise retains
those premises. Its conclusion includes the complete T4-C2 contextual statement
plus the all-prefix and four endpoint equalities above. A combined inert-context
witness uses the six WAL events
`Crash; BeginScan; FinishScan; TruncateTail; BeginRecover; FinishRecover`, seven
machine configurations, and seven equal context states; it proves the complete
C0 premise conjunction and conclusion are inhabited.

T5-C0 verifies 783 cumulative obligations, 14 beyond T5-R0: 13 commit-delta,
representation, mapped-prefix, and contextual bridge/export obligations plus
the combined witness. At that historical checkpoint, 35 registered targets
contained 820 dependency-aware non-duplicated obligations. The oracle actions
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
inhabitation theorem. The cumulative result is 786 verified obligations with
zero errors; 36 registered targets contain 823 dependency-aware non-duplicated
obligations.

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
proof without establishing it.
The T6-D0 target verifies 799 cumulative obligations with zero errors, 16
beyond T5-C0. Together with H1's independent 3-obligation delta, the current 37
registered targets contain 839 dependency-aware non-duplicated obligations.

The complete hierarchy is T1 parameterized Broker safety, T2 independent
atomic-Journal runtime simulation, T3 typed-WAL simulation, completed T4-C0
closed-machine composition, completed T4-C1 context observation and structural
plugging, completed T4-C2 contextual replacement and composition, T5 committed-
history prefix preservation, and T6 conditional end-to-end per-request effect
refinement. T1--T5, H1, and the T6-D0 definition boundary are now complete;
T6-E0, the `OutcomeEvidence` half of
`TerminalEvidenceAndCompatibility`, is the next open proof frontier.
Under the complete stated
persistence, mediation, context, and adapter rely conditions, the broker
provides authorized, per-internal-request at-most-once logical completion and
crash-stable abstract history. It does **not** claim physical exactly-once
execution, coalescing of separately admitted equal payloads, liveness, returned
result delivery, global linearizability of effects across requests, reverse
contextual equivalence, autonomous context steps, protected-handle exclusivity
from T4, adapter effect refinement from T4, or byte-level WAL correctness.

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
| Byte-level WAL implementation | Encoding, checksum, partial-truncation, flush/fsync, atomic-write, and filesystem assumptions | Concrete bytes and recovery parsing refine the typed WAL/Journal contract |
| Scheduler | One globally serialized executor slot in V1 | No simultaneous invocation; multi-worker ownership is deferred |
| Adapter | Declared retry and environment contract | Concrete protocol traces refine one abstract tool operation |
| Recovery | Durable journal is readable | Committed history is preserved; unsafe retries are rejected |

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

A successful observation carries a typed value `v`. The broker keeps this
value only in volatile state until `Commit`, which atomically stores `v` in the
durable committed-value map, stores the durable attempt identifier, records a
proof-only source index, and appends `(r,v)` to the commit log. A crash before
commit clears the volatile value and source, so recovery cannot fabricate or
resurrect an uncommitted result. The abstract terminal Journal record contains
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
