# Formal Model

The dated [related-work and novelty audit](related-work-audit.md) compares the
verified boundary with agent-policy systems, durable workflows, exactly-once
mechanisms, dual-write recovery, capability systems, and machine-checked crash
refinement. Its bibliography is retained in
[`related-work.bib`](related-work.bib).

## Verification boundary

The agent and external tools are adversarial or nondeterministic environment
components. They are not verified. The broker is the reference monitor between
them and is the subject of verification.

The initial model has five logical components:

1. **Request boundary**: converts an untrusted request into an immutable typed
   request identifier and payload.
2. **Capability monitor**: checks authority and atomically consumes capability
   budget when authorization is durably recorded.
3. **Journal**: stores durable authorization, attempt, phase, and terminal
   records in an ordered history.
4. **Adapter executor**: invokes a tool according to its retry class and
   translates tool observations into broker outcomes.
5. **Crash and recovery coordinator**: crash clears volatile execution state;
   gated recovery repairs conclusive failures, quarantines unsafe uncontrolled
   requests, and resumes normal execution only after the recovery predicate is
   satisfied.

The mathematical state and transition system are defined in
[specification.md](specification.md). `EffectBroker.tla` is intended to expose
state-machine mistakes early; it is not itself the final foundational proof.
The normative target for the parameterized proof is
[mechanization-contract.md](mechanization-contract.md). It fixes the labeled
step ADT, prefix-closed executions, independent abstract and concrete states,
representation relation, admissible caller context, adapter rely condition,
and theorem layers T1--T6. Where a finite TLA+ constant or proof shadow differs
from that contract, the contract defines theorem V1.
The Verus mechanization checkpoints are documented in
[mechanized/README.md](../mechanized/README.md). M0 through B2-P3 establish the
typed Journal/replay foundation, generic append protocol, durable coupling,
record-side Broker, rich immutable configuration, physical Invoke/Deliver
histories, retry and authorization safety, and terminal physical provenance.
B2-L then packages the exact thirteen-clause `BrokerInvariant`; B2-A projects
the complete local trace into B1 and classifies crash-free append epochs; G0
defines the 22-constructor global event alphabet with an exact 11 accepted/11
rejected Broker boundary; G1-P proves all normative projections; and G1-E
defines the independent relational configuration-sequence `Exec`. T1 proves
parameterized Broker safety and prefix closure for every finite execution. T2
defines an independent replay-shadow-free atomic-Journal runtime, proves its
trace agreement and exact representation, and constructs a lockstep weak
simulation into the Broker. T3 defines the independent replay-shadow-free
typed-WAL runtime, proves its parser algebra and eight-clause invariant, and
constructs a compressed weak simulation into the atomic Journal with exact
per-prefix representation, observation agreement, and cross-prefix
acknowledged durability. T4-C0 now generically composes the T3 and T2
weak-index maps and simulations, constructs the canonical closed WAL-to-Broker
witness, composes the state and normalized observation relations, and applies
T1 to the target execution and every mapped prefix. T4-C1 then defines the
ordered cut-erased context observation trace, masked endpoint views, arbitrary
relational `ProgramContext<S>`, and structural plugged executions for the WAL,
Journal, and Broker. It proves exact append-I/O recovery, hidden-step
stuttering, T2/T3 history compatibility, erasure, prefix closure, shared
zero-step witnesses, and a positive shared one-`Crash` witness. The cumulative
T4-C1 target verifies 721 obligations, 44 beyond T4-C0. T4-C2 then compresses
context states exactly for WAL events whose T3 translation is `Some`, constructs
the canonical plugged Journal and Broker executions, and proves exact context-
state and ordered endpoint `ContextView` equality at every canonical mapped
prefix. Its cumulative target verifies 735 obligations, 14 beyond T4-C1; the 31
targets registered through T4-C2 contained 771 dependency-aware non-duplicated
obligations. T5-S0 now proves exact one-step committed-history laws for all
three theorem machines. Its cumulative target verifies 744 obligations, 9
beyond T4-C2. T5-E0 lifts those laws across arbitrary finite execution
intervals and verifies 748 cumulative obligations, 4 beyond T5-S0. T5-R0 proves
exact first-`FinishRecover` equality under a no-recovery-Commit predicate and
verifies 773 cumulative obligations, 23 beyond T5-E0. T5-R1 proves general
recovery prefix extension and crash-prefix successful-Outcome provenance,
exhaustive Commit/Fail/Unknown decision classification, and durable-success
guard composition, verifying 787 obligations, 14 beyond T5-R0. T5-C0 completes the contextual
mapped export and verifies 805 cumulative obligations, 18 beyond T5-R1. H1 is
the stuttering artifact/nonvacuity checkpoint: it adds 3 obligations and
verifies 808 cumulative obligations. H2 independently adds a premise-free
strict-extension recovery-Commit witness. H1
constructs a concrete total well-formed `FullConfig` and, without premises,
inhabits the complete T5-C0 premise/conclusion package. T1--T5 are complete;
T6-D0 subsequently freezes the machine-checked adapter, terminal-outcome,
unique selector, outcome-evidence, compatibility, and Journal/WAL bridge
statement interfaces. Its target verifies 821 cumulative obligations, 16
beyond its T5-C0 parent. T6-E0 then proves the generic/event Broker
`OutcomeEvidence` implication from the Broker invariant, exact Journal and
physical projections, and a unique terminal outcome. It verifies 839
cumulative obligations, 18 beyond T6-D0. T6-C0 then proves the corresponding
generic/event `BrokerOutcomeCompatible` implication under `AdapterRely`, by
terminal-outcome and retry-class case analysis. It verifies 856 cumulative
obligations, 17 beyond T6-E0. T6-S0 combines the evidence and compatibility
implications into the frozen conjunction and transports it through the atomic-
Journal and typed-WAL backend statements. Its current target verifies 862
cumulative obligations, 6 beyond T6-C0; the historical retained checkpoint
verifies 858. T6-A0 then proves the generic
conjunction-to-`Refines` closure under Journal legality and `AdapterRely`, and
the first concrete `AdapterVerified` instance: an idempotent `EnsureMember`
set-insertion semantics with an exact nonempty typed-WAL terminal witness.
T6-A1 then defines an operational `EnsureMember` adapter/service machine with
explicit invocation, service linearization, crash/recovery, and environment
steps. Its transition invariant derives `AdapterRely`, and its generic
composition theorem couples the derived rely to an exact typed-WAL execution.
The premise-free witness realizes `Invoke1, Success1, Crash, recover, Invoke2,
Failure2`: the first invocation linearizes but its success is not journaled
before the crash, the second invocation fails without linearizing, and the
seven-record execution terminates `Unknown(NonConclusiveFailure)` while
denoting exactly one abstract set-insert effect. The T6-A1 target
verifies 937 cumulative obligations with zero errors, 52 beyond T6-A0's 885.
At the retained T6-A1 checkpoint, all 42/42 registered targets passed, containing
956 dependency-aware non-duplicated obligations and 20,867 summed target
obligations. T6-M0 then introduces a separately defined protected-service
machine, related to A1 event by event, and a storage-parametric closed-interface
audit context. Its prefix
proofs derive both generated invocation traces, establish
`CompleteMediation`, and connect every target-changing service linearization to
a prior canonical Broker invocation with T1 durable authorization ancestry. The
T6-M0 target verifies 998 cumulative obligations with zero errors, 61 beyond
T6-A1. T6-P0 verifies 1,021 cumulative obligations with zero errors, 23
beyond T6-M0. It relates independently valid A1, protected-service, and
typed-WAL executions with a weak prefix index: observed global events consume
one WAL label, while service linearization and environment interference
stutter. The resulting product establishes exact trace/history agreement,
complete mediation, and effect-state agreement at every related prefix and is
itself prefix closed. This is a conditional execution-pair theorem, not a
construction of a WAL execution for every A1 execution. T6-X0 composes that
adapter-to-WAL index with T4-C2's canonical WAL-to-Broker index and lifts the
P0 product through every supplied storage-parametric context admitting the
plugged WAL run. Its generic contextual theorem transports any verified
adapter's selected terminal refinement to the canonical plugged Broker under
`AdapterVerified` and `AdapterRely`. Its conditional single-request
`EnsureMember` theorem additionally proves source and canonical-target
terminal refinement, all-prefix context and T1
safety agreement, complete mediation, and durable authorization; the concrete
crash/retry theorem grounds the external run in the independently executed
protected state and proves exactly one abstract effect. T6-X0 verifies 1,043
cumulative obligations with zero errors, 22 beyond T6-P0. The historical
pre-K4/DD run passed all 45/45 registered targets, contained 1,062 dependency-aware
non-duplicated obligations, and sums to 23,866 target obligations. The
one-obligation change to every cumulative target from T1 onward is inherited
from a conservative definitional T1 configuration-accessor lemma required by
the concrete package.
The adversary, trusted base, guarantees, and non-goals are fixed in
[threat-model.md](threat-model.md).
Adapter-specific trace interpretation and proof obligations are defined in
[adapter-refinement.md](adapter-refinement.md).
Successful payload provenance and replay consistency are defined in
[value-refinement.md](value-refinement.md).
The checked mappings, bounded product, completed T1--T5 theorems, completed
T6-S0 terminal bridge, T6-A0 semantic closure, and T6-A1 operational adapter
refinement, T6-M0 model-level mediation boundary, T6-P0 prefix product, and
T6-X0 contextual end-to-end instance are summarized in
[refinement.md](refinement.md).
`EffectBrokerJournal.tla` defines the typed append-only Journal and replay
function. `EffectBrokerWAL.tla` defines a bounded Full/Torn-frame WAL with
interruptible recovery scanning, atomic symbolic tail truncation, and replay
installation, and checks its temporal refinement to Journal.
`EffectBrokerJournalRefinement.tla` is a
coupled product whose Journal is the durable authority and whose proof-only
broker shadow is constrained to `Replay(journal)`; TLC checks that this product
refines `EffectBroker`. `EffectBrokerWALRefinement.tla` replaces the atomic
Journal append with the staged Full/Torn WAL in the same Broker context.

The main full TLC configurations have four requests sharing one capability with an
authorization budget of two. Two requests are in scope: one retry-safe request
and one uncontrolled request. The reachable retry-safe class is varied across
deduplicated, idempotent, and read-only scenarios. Two other requests violate
resource or argument scope. A smoke configuration additionally covers base
scope rejection, budget contention among three valid requests, and
`MaxAttempts = 1`. A second small smoke configuration uses one idempotent
request and `MaxAttempts = 3` to exercise retry after a nonconclusive failure
without requiring a crash. Additional smoke scenarios check Journal replay,
uncontrolled and idempotent Journal-to-Broker simulations, and the typed
Full/Torn WAL refinement plus an uncontrolled composed Broker context. The
idempotent composed WAL retry scenario is part of the full tier. Targeted
cross-capability configurations instantiate two requests, two capabilities, a
nonuniform request-to-capability map, and different initial budgets; a small
two-request composed WAL product is included to exercise the same separation
through the direct bounded refinement. Its five-record bound covers
cross-request interleavings and recovery quarantine but is intentionally too
short for the six-record normal terminal path. The one-request composed
scenarios cover Commit, Fail, and outcome-driven Unknown behavior.

The current suite is run with TLA+ Tools `v1.7.4` and Temurin JRE
`21.0.11+10`. State counts are intentionally not embedded here because they
change with the model; the checker reports generated/distinct states, depth,
coverage when requested, and duration for each settled run.

## Adapter retry classes

| Class | Physical retry | Required environment contract |
|---|---|---|
| `ReadOnly` | Allowed | Repetition has no externally visible mutation |
| `Idempotent` | Allowed | Repetition denotes the same abstract effect |
| `Deduplicated` | Allowed | The tool honors the broker's stable request key |
| `Uncontrolled` | Forbidden after arming | No useful retry or transaction guarantee |

For an `Uncontrolled` request, the model conservatively treats every crash
after the durable `Armed` state as unsafe unless a conclusive failure is already
durable. In particular, `ReserveAttempt` may persist `Started` before
`SendAttempt`, and a response may be delivered before its `Persist*` action.
A crash clears the volatile stage, so durable broker state cannot use an
unpersisted send or delivery to justify retry or completion. Gated recovery
therefore quarantines the request as `Unknown`, or repairs a persisted
conclusive failure to `Failed`, without another invocation.

## Durable and volatile state

The following state is durable in the abstract machine:

- operation phase;
- `capRemaining`, `authWitness`, and `authCount`;
- ordered authorization and attempt logs;
- logical commit count, committed value, durable commit attempt, durable
  failure attempt, and ordered commit log;
- capability revocation state.

The execution pipeline has four distinct stages:

1. `ReserveAttempt` appends durable `Started(r,a)` and creates volatile
   `ready` state.
2. `SendAttempt` consumes `ready`, records the physical `Invoke(r,a)` in
   `externalHistory`, and creates volatile `inflight` state.
3. `Deliver*` records acceptance of a correlated physical response in
   `externalHistory` and creates volatile `received` state. Raw transport
   arrival is outside the model and may be buffered before this action.
4. `Persist*` appends the outcome to the durable attempt log. `PersistOK` and
   `PersistErr` create volatile observations for later terminalization or
   reconciliation. For an uncontrolled request, `PersistAmbiguous` or
   `PersistInvalidResult` creates a volatile `observedUnknown` token, and the
   separate `RecordObservedUnknown` transition appends the terminal `Unknown`
   record. Retry-safe requests remain `Armed`.

`ready`, `inflight`, `received`, their attempt and payload metadata, observed
success/failure/unknown tokens, and the `recovering` control flag are volatile.
A crash clears or resets all of them. The append-only `externalHistory` is a proof-only
trace of physical sends and accepted deliveries; it is not a complete history
of hidden external effects or rejected stale deliveries. The two logs satisfy
the `AttemptLogBackedByHistory` relation rather than equality: every physical
`Invoke` is covered by durable `Started`, while every durable outcome is backed
by a physical delivery. Thus `Started` may precede a send, and a delivered
outcome may be lost before `Persist*`.
`observedSource`, `receivedSource`, and `commitSource` are proof-only indices
into the ghost trace. A concrete journal record stores stable attempt identity
and result data, not a ghost sequence index. Adapter refinement relates the
physical trace to external state. No broker decision inspects ghost history.
Post-crash recovery uses only durable Journal state; normal terminalization and
reconciliation may consume volatile observations whose attempt classification
has already been persisted.

The bounded Broker oracle represents these tokens as per-request sets and can
interleave several live requests through atomic transitions. Theorem V1
intentionally chooses the smaller implementation core: one globally serialized
executor slot and one WAL writer. Neither model proves data-race freedom or
multi-worker linearizability.

Each delivered response presents its attempt identifier. The broker accepts it
only when it equals the current in-flight attempt; a late response for an older
attempt is ignored and represented as a stuttering step. This is the
executor/adapter correlation contract that the Rust implementation must
enforce.

The executable modules take `RequestCap` as an arbitrary total operator over
the configured finite request and capability domains and `InitialBudget` as an
arbitrary per-capability natural-number operator. Most regression scenarios
remain single-capability to control state growth, while the targeted
multi-capability scenarios exercise separation. Scope is still abstracted by
separate finite sets for base, resource, and argument matching;
`specification.md` and the mechanization contract give the intended
predicate-valued fields. The reported TLC results are exhaustive only for
their finite configurations; they are validation evidence, not a parameterized
proof. Each configuration also uses one scenario-wide `MaxAttempts` value;
theorem V1 instead fixes an immutable `max_attempts(r)` for every request.

The artifact runners make this evidence boundary reproducible. The Verus
runner verifies only an exact read-only copy of the registered proof sources,
checks that snapshot around every target, validates each cumulative target's
immediate predecessor, and records the schema, driver, lock, sources, and fresh
Rust toolchain tree by hash. The TLC runner validates unique scenario names,
exact tiers and fields, unique configuration registration, and complete
coverage of every `formal/*.cfg`; it executes from isolated model and tool
snapshots with exact membership and hash checks around each invocation. Both
runners also require their bound driver/schema/manifest or lock inputs to remain
stable. Thus the reported hashes name the files actually checked, while the
finite TLC runs remain bounded validation rather than theorem evidence.

## Initial proof target

Let `BrokerSafety` be the conjunction of:

- `TypeOK`;
- `CapabilityBudget`;
- `WitnessSound`;
- `AuthLogSound`;
- `AttemptLogWellFormed`;
- `AttemptLogBackedByHistory`;
- `AttemptAuthorizationSound`;
- `ScopeConfinement`;
- `InvocationsAuthorized`;
- `ExternalHistoryWellFormed`;
- `DeduplicatedOutcomeConsistent`;
- `TerminalEffectClassification`;
- `FailureKnowledgeSound`;
- `ExternalEventValueShape`;
- `DeduplicatedValueConsistent`;
- `ValueRefinementSound`;
- `UniqueLogicalCompletion`;
- `UncontrolledAtMostOnce`;
- `CommitLogSound`;
- `PhaseHasAuthority`;
- `PhaseAttemptConsistency`;
- `VolatileDisjoint`.

The first complete parameterized result is T1 in the
[mechanization contract](mechanization-contract.md#t1-parameterized-broker-safety):

```text
FullConfigWF(cfg) and Exec(cfg, execution)
  implies T1ParameterizedSafety(cfg, execution)
```

The complete [mechanized checkpoint chain](../mechanized/README.md) culminates
in this result. M0 through B2-P3 prove the reduced and full-record foundations,
append acknowledgment, stored-durable coupling, executable retry/recovery
queries, record and physical Broker transitions, canonical acknowledged
invocation ancestry, retry limits, Outcome ordering, and terminal physical
provenance. B2-L packages exactly the thirteen numbered `BrokerInvariant`
clauses while retaining the stronger inductive predicate separately. B2-A
establishes exact B1 append projection, successful-return cuts, and the
crash-free append-epoch language. G0 closes the global event alphabet and proves
the exact Broker/backend constructor partition. G1-P proves the normative
global projections, and G1-E proves that the relational configuration-sequence
`Exec` is prefix-closed, rejects backend-only events, and corresponds exactly
to the verified local transition system. Finally, the generic T1 theorem proves
per-prefix `TraceAgreement`, all-configuration Broker invariants, append and
recovery obligations, authorization and retry safety, terminal uniqueness, and
committed-value provenance for every finite `Exec`. Its adapter parameter is
opaque: no adapter effect law is assumed or concluded.

T5 separately strengthens recovery preservation. The completed T5-S0
checkpoint defines

```text
alpha_commit_B(B) = B.durable.commit_log
alpha_commit_J(J) = Replay(JournalView(J)).commit_log
alpha_commit_W(W) = Replay(JournalView(W)).commit_log,
                    where JournalView(W) = Parse(W.store.media).
```

For every accepted theorem-machine step, T5-S0 proves the exact delta equation
and hence:

```text
alpha_commit(s) is a prefix of alpha_commit(s').
```

Only `BrokerLinearize(CommitRec)`,
`JournalAppendLinearize(CommitRec)`, and `WalWriteFull(CommitRec)` or
`WalFinishTorn(CommitRec)` append one exact `CommitEntry`; all other accepted
steps preserve `alpha_commit` by equality. The WAL proof assumes only the
runtime `wal_invariant`, not ghost-evidence agreement. Reachable states derive
that premise from T3-W0's `basic_invariant`. It proves the stronger exact
parsed-view law first: Torn writes stutter and tail truncation preserves
`Parse(media)` exactly.

T5-E0 now proves the transitive interval claim. For every finite execution and
indices `i <= j < configs.len()`, the committed history at configuration `i` is
a prefix of the history at configuration `j`. Each exported theorem requires
only the corresponding Broker, Journal, or WAL `Exec` predicate and the index
bounds. The WAL proof obtains `basic_invariant` from reachability and discharges
the local `wal_invariant` premise internally.

T5-R0 now defines an episode by event positions alone: a selected `Crash`, the
first later `FinishRecover`, and no intervening `FinishRecover`. For every
episode event, accepted-machine semantics derive that any durable linearization
is a permitted recovery Commit, Fail, or Unknown repair. R0 separately defines
the no-recovery-Commit episode predicate; under it, `alpha_commit` stutters and
the histories at `configs[crash]` and `configs[finish + 1]` are exactly equal.
Minimal Broker, Journal, scan/truncate WAL, and repeated-`Crash` witnesses
inhabit this corollary.

T5-R1 proves the general result for every typed-WAL recovery episode: the crash
history is a prefix of the post-`FinishRecover` history, and every intervening
Commit cites the exact successful Outcome value and LSN already present in the
crash-prefix Journal. H2 inhabits strict extension with a 26-event execution
whose committed-history length grows from zero to one while Recovering.

T5-C0 now completes that bridge. For every related source prefix `i`, the WAL
and canonical Broker states at `i` and `mu[i]` have exactly equal
`alpha_commit`. For a source `RecoveryEpisode(crash,finish)`, it transports
general WAL/Broker endpoint prefix extension and crash-prefix Commit
provenance. Under the no-Commit predicate it proves four endpoint equalities:
equality of the two WAL endpoints, WAL/Broker equality at
`crash`, WAL/Broker equality at `finish + 1`, and equality of the two mapped
Broker endpoints. The target endpoint is `mu[finish + 1]`, not
`mu[finish] + 1`. Matched WAL/Broker steps have equal commit deltas, while a
weakly erased WAL step has empty commit delta.

The contextual export requires a well-formed full configuration, or a well-
formed `PaperConfig` at the paper boundary, plus `StorageParametricContext`, a
plugged WAL execution, and a source recovery episode. Its conclusion retains
the complete T4-C2 statement together with all-prefix and recovery-endpoint
committed-history agreement. It does not prove that the canonical Broker trace
satisfies `RecoveryEpisode`. A six-event, seven-state minimal WAL recovery
execution under the inert storage-parametric context proves the complete C0
premise conjunction and conclusion are inhabited. In the TLA+ oracle, the
recovery record labels correspond to
`RecoverRecordedFailure` and `QuarantineUncontrolled`.

H1 strengthens only the nonvacuity and artifact boundary. Its total
`FullConfig` maps every request to an uncontrolled request with no stable key
and one permitted attempt, maps every capability to unit budget with universal
resource and argument scope, and admits every request/result pair. The proof
derives `FullConfigWF` directly; deduplicated-key injectivity is vacuous because
no request is deduplicated. With T4's inert context and T5-C0's six-event
minimal contextual recovery execution, the premise-free H1 theorem exhibits
`crash = 0` and `finish = 5` and proves that all T5-C0 premises and its complete
conclusion hold together. This concrete witness does not exhibit a nonempty
pre-crash committed history, a realistic adapter, or an external effect; the
generic T5 theorem, rather than H1's witness, carries the conditional committed-
history preservation claim.

## Modeling and implementation assumptions

1. Journal updates are atomic and durable at the broker-model level.
   `ReserveAttempt` is separate from `SendAttempt`, and physical `Deliver*`
   actions are separate from durable `Persist*` actions. The remaining
   persistence assumption is that each authorization, reservation, outcome,
   phase, or terminal journal update is atomic. The bounded typed WAL model
   refines these updates to completed Full frames for every explored crash
   prefix, while treating physical tail removal as one atomic primitive. A
   byte-level implementation proof must discharge the corresponding encoding,
   truncation, and filesystem assumptions.
   In theorem V1, atomic durability is separated from API completion by an
   explicit append Call -> Linearize -> Return protocol. `WriteFull` or
   `FinishTorn` is the WAL linearization point and `FlushAck` is the successful
   return; the atomic-Journal specification may delay its return so both
   backends have matching post-linearization/pre-return states.
2. The broker allocates fresh internal request identifiers. The abstract
   deduplication key is derived injectively from the adapter namespace and that
   identifier. Client-supplied replay identifiers are rejected or bound to an
   immutable request digest before entering this model.
3. Capability metadata and request fields are immutable after admission.
4. Adapter retry-class declarations are trusted environment assumptions until
   adapter-specific refinement proofs are supplied.
5. Crashes stop broker execution and erase volatile memory but do not corrupt
   acknowledged durable journal records.
6. Cryptography, the operating system, storage hardware, transport security,
   and remote tool implementations are outside the first trusted proof.
7. The finite TLA+ model constrains adapter observations according to declared
   class laws; it does not independently verify a remote service or model its
   hidden state. The paper-level theorem is conditional on an adapter
   trace-refinement proof.
8. The executable modules support finite request-to-capability maps and
   per-capability budgets, but use one scenario-wide `MaxAttempts` and one
   global `AllowedResults` set. Theorem V1 replaces those abstractions with
   immutable `max_attempts(r)` and `result_pred(r,v)`; Rust adapters will use
   typed, request-indexed postconditions.
9. At-most-once logical completion is per fresh internal request identifier.
   Coalescing two admissions that carry the same semantic payload requires a
   separate durable replay-key map and is not yet modeled.

## Refinement hierarchy

The intended proof chain is:

```text
WAL  ->  Journal  ->  EffectBroker
```

Both bounded arrows and their direct composed product are now checked.
`EffectBrokerWAL -> EffectBrokerJournal` maps a completed
Full frame to one Journal append; staging, torn writes, flush acknowledgement,
scan, tail truncation, replay installation, and other recovery bookkeeping
stutter. `EffectBrokerJournalRefinement ->
EffectBroker` pairs each typed append with one broker durable transition and
checks `ReplayCoupling`, while send, delivery, crash, and retry-control steps
stutter on the Journal. `EffectBrokerWALRefinement` replaces atomic appends with
the WAL protocol and checks WAL, Journal, and Broker temporal projections in
one bounded product.

These products are deliberately coupled model-checking constructions: they
carry proof-only Broker durable shadows and constrain them to Journal replay.
They are not the concrete-state definition for theorem V1. The mechanization
contract independently defines `BrokerState`, `ConcreteRuntime<AtomicJournal>`,
`ConcreteRuntime<TypedWAL>`, and ghost evidence, then relates them with
`Representation`. T2 and T3 are stepwise simulations between those independent
machines. T2 is machine checked, and T3 now checks the independent WAL machine,
its inductive invariant, and its compressed WAL-to-Journal weak simulation.
The proof constructs the weak index map and establishes the representation and
all normalized cross-backend observations at every related prefix. T4-C0
composes the completed closed runtime simulations, including arbitrary
compatible weak-index maps, the canonical WAL-to-Broker witness, composed
state/projection relations, and T1 safety at every mapped prefix. T4-C1 is also
complete: it fixes the ordered context alphabet, masks append linearization in
both endpoint views, defines arbitrary relational context transitions, and
structurally plugs the WAL, Journal, and Broker. Its proofs cover erasure,
prefix closure, hidden-step state/view stuttering, T2/T3 whole-history
compatibility, an accepting inert context, shared zero-step executions, and a
shared visible `Crash` execution. T4-C2 is now complete: it compresses the WAL
context-state sequence according to T3 `translate_event(...)=Some(_)`, not
context-delta visibility, constructs the canonical plugged Journal and Broker
executions, and proves exact context-state and ordered endpoint `ContextView`
equality at every canonical mapped prefix. The constructed Broker product
retains C0 weak simulation, normalized projection agreement, T1 safety, and
mapped-prefix T1 safety.

The generic Journal legality relation intentionally omits physical delivery
witnesses and deduplicated-adapter guards. The coupled refinement supplies
those preconditions by conjoining every append with the corresponding broker
action, so it checks the realizable subset rather than claiming that every
syntactically legal Journal trace has a broker execution. A successful Outcome
record also retains more data than `EffectBroker`: `ReplayCoupling` erases that
extra value, and the bridge still requires a live `observedOK` token before a
Commit record can be appended. Thus Journal replay cannot manufacture a
post-crash commit. The product additionally checks that every physical Invoke
has an acknowledged Start record and that recovery staging is limited to its
terminal repair records. Physical sends and accepted deliveries are released
only when the WAL is quiescent. Recovery scanning and its abort/restart windows
occur while the Broker remains crashed; the symbolic tail-removal transition
itself remains atomic. Here `Deliver*` denotes broker acceptance of a correlated
response, not the remote response's transport-level arrival; an implementation
may buffer arrivals until the gate opens. T1 supplies the complete
parameterized Broker-safety theorem, and T2 supplies the independent
atomic-Journal-to-Broker simulation with exact per-prefix representation. T3
additionally supplies the independent typed-WAL state machine, LSN-sensitive
parser, crash/scan/recovery transitions, local preservation theorem, exact
12-match/5-stutter event compression, and the parameterized WAL-to-Journal weak
simulation. T4-C0 additionally proves the generic closed composition into the
Broker and transfers T1 safety to the canonical target and each related prefix.
T4-C1 additionally proves the common context-observation and structural
plugging foundation. T4-C2 additionally proves canonical finite forward
contextual replacement under its exported `StorageParametricContext` premise.
T5-S0 additionally proves exact one-step committed-history laws for the Broker,
Journal, and WAL, including exact parsed-view stuttering for Torn and truncation
steps. T5-E0 additionally proves prefix monotonicity across every ordered pair
of configurations in a finite execution. T5-R0 additionally proves exact
first-`FinishRecover` endpoint equality for no-Commit recovery episodes. T5-R1
proves general prefix extension and crash-prefix durable-success provenance.
T5-C0 additionally proves exact commit-delta refinement, all-prefix WAL/Broker
`alpha_commit` equality, and contextual transport of both recovery forms. H1
and H2 inhabit the stuttering and strict-extension branches. H1 additionally proves the cumulative
T1--T5 premise/conclusion package inhabited under a concrete total
configuration and hardens the source-hashed verification artifact. T5 is
complete. T6-D0 freezes the terminal and adapter definition boundary, and
T6-E0 proves the generic `OutcomeEvidence` half without proving compatibility
or the combined bridge. T6-C0 proves the compatibility half: Commit uses the
selected success delivery; Fail discharges ReadOnly, Idempotent,
Deduplicated, and Uncontrolled separately; and Unknown reconstructs its
durable cause while bounding Uncontrolled invocation multiplicity. T6-S0 then
combines both halves as `OutcomeEvidence && BrokerOutcomeCompatible` and proves
the frozen atomic-Journal and typed-WAL statements by transporting final-prefix
trace agreement through their existing representation relations. T6-A0 then
connects this conjunction to `Refines`, proves a concrete idempotent
`EnsureMember` semantic adapter contract, and inhabits it with an exact
20-event typed-WAL execution ending in Commit. Its premise-free package fixes
the request, run, outcome, records, and physical history. T6-A1 closes the next
model-level gap: an explicit adapter/service transition system derives
`AdapterRely` from its invariant and composes with the exact typed-WAL trace for
the realizable sequence `Invoke1, Success1, Crash, recover, Invoke2, Failure2`.
The first success linearizes the set insertion but is lost at the Journal
boundary; after recovery, attempt 2 becomes current and returns a nonconclusive
failure. The selected terminal outcome is therefore Unknown rather than Fail,
and the execution still refines exactly one abstract effect. T6-M0 closes the
model-level mediation gap for this witness: its separate protected-service
execution generates the two cut-bearing calls, only the first call linearizes,
and both calls have T1 durable authorization ancestry. Its closed-interface
audit context observes only Broker-generated `Invoke` events in the masked T4
interface and derives the same `CompleteMediation` equality. The synthetic
full-capability configuration is not a least-privilege result. T4 alone does not
prove reverse contextual equivalence, liveness, autonomous context steps, or
protected-handle exclusivity; T6-M0 supplies model-level no-bypass only for its
closed formal deployment interface. T6-P0 adds a weak-indexed product over the
A1, protected-service, and WAL executions. It proves related-prefix trace and
request-history equality, mediation, membership/environment/linearization
agreement, canonical-map existence under final trace equality, and closure
under taking a related prefix. The relation is conditional on the three
executions and their step coupling; it is not a forward simulation that creates
a WAL execution from an arbitrary A1 run. T6-X0 then composes the P0 map with
T4-C2's canonical WAL-to-Broker map. At every composed prefix it retains the P0
product, both plugged execution prefixes, exact context-state and masked-view
equality, the adapter history projected from the canonical Broker trace, and T1
safety. Its paper-facing generic theorem carries a selected source terminal to
the canonical Broker, proving target `Refines` and per-request effect
refinement under `AdapterVerified` and `AdapterRely`. Its operational
`EnsureMember` selected-terminal theorem additionally proves source and target
`Refines`, per-request effect refinement, source and target mediation, and durable
authorization for the fixed `EnsureMember` instance. This operational and
protected-state theorem remains conditional on a supplied P0 execution product
and a context admitting the plugged WAL run; it neither constructs a WAL run
from an arbitrary adapter run nor proves the fully quantified family of
operational adapter/protected executions required by the all-request T6
generalization. The
cumulative track now also contains the complete T6-RO0 ReadOnly operational
instance. T6-DD0/DD1 define the keyed Deduplicated machine and prove its
invariant, `AdapterRely`, and generic terminal refinement; T6-DD2 constructs the
concrete crash/retry adapter and WAL witness; and T6-DD3 couples that witness to
an independent protected-service execution with exactly one keyed decision,
memoized retry return, complete mediation, and durable authorization ancestry.
T6-DD4 proves the Deduplicated all-prefix adapter/protected/WAL product, composes
it through T4-C2's canonical contextual Broker replacement, and closes source
and target terminal refinement plus mediation for that distinguished witness.
T6-DD5 generalizes the terminal boundary over a request-indexed family of
operational/protected members, requiring coverage for every terminal request in
the shared WAL and proving source/target refinement and mediation for each
covered member. Its DD2 family discharges coverage without premises. Constructing
family members from production executions remains an implementation refinement.
The
cumulative result still does not verify production Rust adapter/runtime code,
network or remote-service behavior, operating-system descriptor isolation,
`ReturnResult`, multi-request/global linearizability, or byte-level WAL
correctness. The WAL is still a symbolic typed-frame model, not a byte decoder,
checksum proof, or filesystem/fsync proof.

`MaxJournalLength` is only a TLC state-space bound. It is absent from theorem
V1, whose executions may contain any finite number of Journal records. A
capacity-limited implementation must expose `DiskFull` before staging and
stutter on logical and adapter projections; silent append disablement is not a
permitted theorem behavior. The checked properties and theorem V1 are
safety-only. The theorem additionally fixes one globally serialized WAL writer
and executor slot; the finite Broker oracle uses per-request volatile tokens
but only atomic transitions. Neither makes a liveness, multi-worker
linearizability, `ReturnResult`, or cross-request external-effect
linearizability claim.

The theorem roadmap is [T1 parameterized Broker safety](mechanization-contract.md#t1-parameterized-broker-safety),
[T2 atomic-Journal runtime simulation](mechanization-contract.md#t2-atomic-journal-runtime-simulation),
[T3 typed-WAL simulation](mechanization-contract.md#t3-typed-wal-simulation),
[T4-C0 closed WAL-to-Broker composition](mechanization-contract.md#t4-c0-closed-wal-to-broker-composition),
[T4-C1 context observation and plugging](mechanization-contract.md#t4-c1-context-observation-and-plugging-foundation),
[T4-C2 contextual replacement and composition](mechanization-contract.md#t4-c2-contextual-replacement-and-composition),
[T5 committed-history recovery preservation](mechanization-contract.md#t5-recovery-and-committed-history-prefix-preservation),
[T6-D0 terminal and adapter definition freeze](mechanization-contract.md#t6-d0-terminal-and-adapter-definition-freeze),
[T6-E0 terminal evidence](mechanization-contract.md#t6-e0-terminal-evidence),
[T6-C0 terminal compatibility](mechanization-contract.md#t6-c0-terminal-compatibility),
[T6-S0 terminal bridge composition and backend transport](mechanization-contract.md#t6-s0-terminal-evidence-and-compatibility-bridge),
[T6-A0 concrete adapter semantic closure](mechanization-contract.md#t6-a0-concrete-adapter-semantic-closure),
[T6-A1 executable adapter refinement](mechanization-contract.md#t6-a1-executable-adapter-protocol-refinement),
[T6-M0 mediation and protected-handle exclusivity](mechanization-contract.md#t6-m0-mediation-and-protected-handle-exclusivity),
[T6-P0 prefix-indexed adapter/WAL/protected product](mechanization-contract.md#t6-p0-prefix-indexed-adapterwalprotected-product),
[T6-X0 storage-parametric contextual end to end](mechanization-contract.md#t6-x0-storage-parametric-contextual-end-to-end),
and [generalized T6 conditional end-to-end effect refinement](mechanization-contract.md#t6-generalized-conditional-end-to-end-theorem).

## Next formal increments

1. Refine production adapter/service executions into the DD5 family-member
   interface and discharge terminal-request coverage without a formal premise.
2. Refine the operational adapter/runtime model to verified production Rust and
   specify the trusted network and remote-service interface precisely.
3. Extend the current typed-frame `WAL -> Journal` proof to concrete
   record bytes, checksums, flush/fsync semantics, and a verified parser under
   crash injection at every record boundary.
4. Add and refine the `ReturnResult` path so caller-visible results are released
   only from the verified durable terminal state.
5. Add multiple workers, ownership of operation tokens, and global
   linearizability across requests and external effects.
6. Add capability expiry and attenuation, then conditional progress and
   liveness under explicit fairness and service-response assumptions.
