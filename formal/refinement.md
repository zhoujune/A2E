# Refinement Structure

## 1. Layers

The current formal development uses three semantic layers and one composed
product:

```text
EffectBrokerWAL
    refines EffectBrokerJournal
        is coupled to EffectBroker by EffectBrokerJournalRefinement

EffectBrokerWALRefinement = BrokerContext[EffectBrokerWAL]
    refines EffectBroker directly in bounded scenarios
```

`EffectBroker` is the safety specification. `EffectBrokerJournal` is the
typed atomic-append interface and replay function. `EffectBrokerWAL` is a
symbolic physical representation with complete and torn frames. The coupled
module supplies the physical-history and volatile-token witnesses that a
Journal prefix alone intentionally omits. `EffectBrokerWALRefinement` replaces
the coupled model's atomic append with staged, torn, complete, acknowledged,
and recovered WAL states.

These are bounded TLA+ model-checking products. Their Broker durable variables
and `shadowJournal` are proof shadows used to make the simulation relation
executable for TLC; they are not fields of the theorem-V1 implementation. The
normative [mechanization contract](mechanization-contract.md) independently
defines `BrokerState`, `ConcreteRuntime<AtomicJournal>`,
`ConcreteRuntime<TypedWAL>`, and ghost evidence, then relates them with
`Representation`.

## 2. WAL to Journal

For WAL state `w`, the refinement mapping is

```text
pi_WJ(w).journal = Parse(w.media) = w.shadowJournal.
```

`Parse` returns the longest prefix of sequential Full frames and ignores a
Torn tail. A complete frame is the logical Journal linearization point.

| WAL action | Journal action |
|---|---|
| `Stage(rec)` | stutter |
| `WriteFull` | `AppendOne(rec)` |
| `WriteTorn` | stutter |
| `FinishTorn` | `AppendOne(rec)` |
| `FlushAck` | stutter |
| `Crash` | stutter; clear volatile writer state and initialize scan control |
| `BeginScan` | stutter; begin a physical recovery scan while the Broker remains crashed |
| `FinishScan` | stutter; capture `Parse(media)` in `scanResult` |
| `TruncateTail` | stutter; atomically replace media with `FullFrames(scanResult)` |
| `AbortScan` | stutter; restart a scan interrupted before or after truncation |
| `BeginRecover` | stutter; install the scanned prefix and enter Broker recovery |
| `FinishRecover` | stutter |

The Broker remains crashed throughout `BeginScan`, `FinishScan`,
`TruncateTail`, and `AbortScan`. Only `BeginRecover` installs the recovered
prefix in the process cache and changes the Broker to recovering. The WAL
writer then remains available because recovery may need to append terminal
`Fail` or `Unknown` records. In the composed model, normal staging is disabled
during recovery, pending recovery records are restricted to conclusive `Fail`
or `Unknown("Recovery")`, and `FinishRecover` requires both WAL quiescence and
Broker `RecoveryComplete`.

`TruncateTail` is intentionally the remaining atomic storage primitive in the
typed-frame model. The model exposes crashes before scanning completes and
after truncation completes, but not a partially applied filesystem truncation.
Concrete byte- and filesystem-level refinement must discharge or further split
that primitive.

The table above is the bounded TLA+ Journal projection. The theorem-V1 storage
interface is more precise about the caller-visible operation: `Stage` is the
append call, `WriteFull`/`FinishTorn` is append linearization, and `FlushAck` is
the successful append return. The atomic Journal uses the same three-phase
protocol and may delay Return, which is necessary to relate the WAL state that
has durable data but has not yet acknowledged the caller.

`MaxJournalLength` is only a finite TLC bound on records, references, and
frames. Theorem V1 has no logical Journal capacity: any finite execution may
append any finite number of records. A capacity-limited implementation must
take an explicit pre-stage `DiskFull` step that preserves all logical and
adapter projections; silently disabling append at the exploration bound is not
part of the theorem. Likewise, each TLC configuration supplies one global
`MaxAttempts`, while theorem V1 uses the immutable request-indexed bound
`max_attempts(r)`.

The checked representation invariants include:

- sequential LSNs;
- at most one Torn frame, at the tail;
- `shadowJournal = Parse(media)`;
- one pending record;
- acknowledged-prefix containment;
- crash-stable containment of every historically acknowledged prefix;
- scan results equal the stable parsed prefix in `Scanned` and `Truncated`;
- non-idle scan phases imply that both WAL and Broker remain crashed;
- Journal safety for the parsed prefix.

TLC checks `JournalRefinement == Journal!Spec` as a temporal property.

## 3. Journal to Broker

`EffectBrokerJournalRefinement` contains:

- `logicalJournal`, the implementation-facing durable authority;
- proof-only broker durable shadows;
- the same volatile execution tokens and ghost external history as
  `EffectBroker`.

Let

```text
rho(j) = EffectBrokerJournal!Replay(j).
```

`ReplayCoupling` equates the broker shadows for phase, capabilities, attempt
history, terminal state, and provenance with `rho(logicalJournal)`. The source
index into `externalHistory` remains proof-only ghost state and is not stored
in the Journal.

| Coupled action | Journal record | Broker action |
|---|---|---|
| authorization | `Authorize` | `Authorize` |
| revocation | `Revoke` | `Revoke` |
| request preparation | `Prepare` | `Prepare` |
| execution arming | `Arm` | `Arm` |
| attempt reservation | `Start` | `ReserveAttempt` |
| physical invocation | none | `SendAttempt` |
| response delivery | none | `Deliver*` |
| durable outcome | `Outcome` | `Persist*` |
| successful completion | `Commit` | `Commit` |
| conclusive failure | `Fail` | `RecordFailure` or `RecoverRecordedFailure` |
| persisted uncontrolled uncertainty | `Unknown` | `RecordObservedUnknown` |
| retry exhaustion | `Unknown` | `ExhaustedUnknown` |
| recovery quarantine | `Unknown` | `QuarantineUncontrolled` |
| crash and recovery control | none | `Crash`, `BeginRecover`, or `FinishRecover` |

Every append is conjoined with the corresponding Broker action. This is
important: the generic Journal storage rule accepts a broader set of typed
records, while the coupled model supplies delivery tokens, exact attempts,
adapter-result guards, and recovery mode. The refinement theorem concerns this
realizable subset, not every syntactically legal Journal sequence.

TLC checks both `JournalRefinement == Journal!Spec` and
`BrokerRefinement == Broker!Spec` under the coupled specification.

## 4. Extra Concrete Information

A successful Journal `Outcome` stores its value, while `EffectBroker` treats
the value as volatile until `Commit`. This does not invalidate refinement.
`ReplayCoupling` erases the extra outcome value, and the coupled Commit action
still requires a live `observedOK` token. After a crash, replayed outcome data
cannot independently create an abstract commit.

The same principle applies to request digests, stable keys, record references,
and future serialized call bytes: concrete audit and recovery metadata may be
erased when mapping to the smaller Broker abstraction.

## 5. Composed Model

The bounded composed result checked by `EffectBrokerWALRefinement` is

```text
BrokerContext[EffectBrokerWAL] => EffectBroker!Spec.
```

Staging and torn writes stutter at both Journal and Broker levels. `WriteFull`
or `FinishTorn` appends the record and performs the paired Broker transition.
`FlushAck` stutters on the Broker/Journal data abstraction but is the
caller-visible successful append return and releases subsequent operational
work.
`Crash`, replay-installing `BeginRecover`, and `FinishRecover` occur in
lockstep in the WAL and Broker projections. `BeginScan`, `FinishScan`,
`TruncateTail`, and `AbortScan` stutter on the Broker while it remains crashed.
The checked coupling is

```text
shadowJournal = Parse(media)
BrokerDurable = Replay(Parse(media)).
```

The product also checks that every physical `Invoke(r,a)` has an acknowledged
`Start(r,a)` record. `WALQuiescent` gates `SendAttempt`, every accepted
`Deliver*`, retry release, and the next durable command. Abstract Commit itself
linearizes when its complete frame reaches crash-stable media; delivery of a
committed result to the agent remains outside the current model and must later
be gated by flush acknowledgment.

`Deliver*` denotes acceptance of an already arrived, correlated response into
Broker volatile state. It does not prevent a remote service or transport from
returning bytes while the WAL is busy. A concrete executor must buffer such an
arrival until `WALQuiescent`, or leave it unaccepted and conservatively retain
the durable attempt as unresolved; no response-arrival liveness claim is made.

The general parameterized contextual replacement theorem is now machine
checked:

```text
WAL refines AtomicJournal
and BrokerContext[AtomicJournal] refines EffectBroker
implies BrokerContext[WAL] refines EffectBroker.
```

The bounded product validates this alignment only for the configured domains;
the completed T4 theorem establishes its finite forward form for arbitrary
storage-parametric contexts.

In the mechanization this obligation is split rather than proved with coupled
state: T2 relates the independent atomic-Journal runtime to the Broker, T3
relates typed WAL to atomic Journal through `Parse(media)`, and T4 lifts and
composes those simulations for every storage-parametric context.
The closed composition core T4-C0 is now machine checked: it generically
composes compatible weak-index maps and simulations, constructs the canonical
WAL-to-Broker witness, composes the state and normalized projection relations,
and applies T1 to the resulting Broker execution and every mapped prefix.
T4-C1 is also machine checked: it defines one ordered cut-erased observation
alphabet, masked pre/post runtime views that cannot expose append linearization,
arbitrary relational context state, and structural WAL/Journal/Broker plugging.
It proves erasure, prefix closure, hidden-step stuttering, T2/T3 whole-history
compatibility, shared zero-step witnesses, and a positive shared one-`Crash`
witness. T4-C2 completes the lift. It compresses source context states exactly
for WAL events whose T3 `translate_event` result is `Some`, rather than by
context-delta visibility, constructs the canonical plugged Journal and Broker
executions, and proves exact shared
context-state and complete ordered endpoint `ContextView` equality at every
canonical mapped prefix. Under the exported `StorageParametricContext` premise,
the target retains C0 weak simulation, normalized projection agreement, full T1
safety, and mapped-prefix T1 safety. Neither T4-C0 nor T4-C1 alone is the
replacement theorem.
T5-S0 is now machine checked as the local recovery foundation. It defines
`alpha_B` as the Broker durable `commit_log` and `alpha_J`/`alpha_W` as
`Replay(JournalView).commit_log`, where the WAL view is `Parse(media)`. It
proves exact one-step deltas: only the backend's durable Commit linearization
appends one `CommitEntry`; every other accepted step stutters. Under the WAL
runtime `wal_invariant`, which excludes ghost-evidence agreement, the proof also
establishes exact parsed-view behavior for Full completion, Torn completion,
Torn stuttering, and truncation equality. Reachable states obtain this premise
from T3-W0's `basic_invariant`.
T5-E0 is also machine checked. It uses the exact backend `Exec` relations and
proves committed-history prefix monotonicity for every pair of indices
`i <= j < configs.len()`. The WAL theorem exposes no additional invariant
premise: its proof derives `basic_invariant` for reachable configurations and
then projects the runtime `wal_invariant` internally.
T5-R0 is machine checked as well. Its event-only episode predicate selects a
`Crash` and the first later `FinishRecover`. Backend enabledness derives
non-Online mode confinement, recovery-repair classification for every durable
linearization, zero commit delta, and exact per-step `alpha_commit` stuttering.
The endpoint theorem equates `configs[crash]` with `configs[finish+1]`. Minimal
Broker, Journal, and WAL witnesses plus a repeated-`Crash` Broker witness prove
the predicate is inhabited.
T5-C0 completes the contextual mapped bridge. Exact T3, T2, and composed T4
commit-delta laws show that erased WAL steps have empty deltas and matched steps
have equal WAL/Broker deltas. The representation relation then yields
`alpha_commit` equality at every canonical mapped prefix. For a source recovery
episode, the theorem exports the source endpoint equality, both source/target
endpoint equalities, and mapped Broker endpoint equality at `mu[crash]` and
`mu[finish+1]`. It does not establish a target Broker `RecoveryEpisode`. A
six-event, seven-state WAL recovery execution under the inert context proves
the complete contextual premise conjunction is inhabited.
H1 then closes the cumulative artifact's configuration-level nonvacuity gap.
It proves a concrete total `FullConfig` well formed, instantiates the inert
context and the same minimal recovery execution at `crash = 0`, `finish = 5`,
and, without premises, establishes the complete T5-C0 premise/conclusion
package. H1 does not strengthen the refinement relation: its concrete witness
has no demonstrated nonempty pre-crash commit history and no external-effect
interpretation.
T6-D0 then freezes the adapter interpretation, request-local physical-history
rely, unique terminal/delivery selectors, configuration-explicit outcome
evidence, compatibility branches, and the shared-core plus two-backend bridge
statement boundary. It proves definition sanity, not the bridge conclusion.
T6-E0 proves the generic Broker-side evidence half. Broker invariant and exact
Journal/physical event projections, together with a selected terminal outcome,
imply `OutcomeEvidence` over the request-local adapter projection. This result
does not consume adapter semantics and does not prove compatibility or either
backend wrapper. T6-C0 proves the complementary generic compatibility half
under `AdapterRely`. It reuses the exact T6-E0 evidence, preserves invocation
counts through the request-local projection, and discharges Commit, Fail, and
Unknown for every retry class. It does not combine evidence and compatibility,
transport the result through either backend, or interpret an external effect.
Adapter laws are explicit `AdapterRely` assumptions, not unrestricted Journal
legality.
T6-S0 completes the frozen generic bridge by conjoining the T6-E0 evidence and
T6-C0 compatibility results. Its atomic-Journal and typed-WAL wrappers derive
the core Broker premises from final-prefix trace agreement and the existing
representation relations, then rewrite the core result to the final backend
evidence records. The wrappers transport through assumed execution,
admissibility, trace agreement, and representation; they add no simulation
invariant. T6-S0 does not supply an adapter effect interpretation or a terminal
execution satisfying `AdapterRely`. In particular, the inert H1 witness does
not inhabit that rely premise. It establishes neither `Refines` nor
`AdapterVerified`, external one-effect semantics, a concrete terminal witness
or premise-inhabitation result, or the unmodeled `ReturnResult` action.

### T6-A0, T6-A1, T6-M0, and T6-P0: semantic through prefix-product boundaries

T6-A0 closes that semantic gap for one idempotent adapter. Generically,
`AdapterVerified`, Journal legality, `AdapterRely`, and T6-S0's
`TerminalEvidenceAndCompatibility` conclusion imply `Refines`; the event,
atomic-Journal, and typed-WAL exports then imply per-request effect refinement.
The concrete `EnsureMember` contract interprets the external state as a set and
the operation as inserting the request's resource. Its rely separates
environment additions from broker-linearized attempts, forbids the environment
from inserting the target, and makes any nonempty set of recorded linearizations
observationally one effect. A premise-free theorem instantiates a nonempty
20-event typed-WAL Commit execution, its represented Broker, the request-local
success history, a relying external run, and a strict one-effect/not-zero
post-state. This is adapter-contract and model inhabitation, not verification of
executable adapter or service code.

T6-A1 replaces A0's crash-erased mixed-history check with an operational
adapter/service transition system. The machine has explicit Online, Crashed,
and Recovering modes and distinguishes observed global events, silent service
linearization, and non-target environment additions. Its inductive invariant
establishes exact global and physical projections, request locality, canonical
calls, invocation/response order and uniqueness, success/failure consistency
with service linearization, and an exact zero-or-one set-insertion effect. Thus
`AdapterRely` is derived from executable-model reachability rather than assumed
as an enabledness premise. The generic A1 theorem composes that derived rely
with any exactly coupled terminal typed-WAL execution and obtains `Refines` and
per-request effect refinement.

The premise-free A1 witness couples 32 adapter events, including one silent
service linearization, to 31 global/WAL events and 32 WAL configurations. Its
seven records are Authorize, Prepare, Arm, Start1, Start2,
Outcome2(Failure), and Unknown. The realized sequence is `Invoke1, Success1,
Crash, recover, Invoke2, Failure2`: attempt 1 inserts the member but its Success
is not journaled before the crash; attempt 2 becomes current after recovery and
fails without linearizing. Because not every invocation failed, terminal Fail
is impossible. The selected `Unknown(NonConclusiveFailure)` nevertheless
refines exactly one abstract insertion effect.

T6-A1 verifies an operational protocol model and its exact typed-WAL coupling,
not production Rust adapter/runtime code, network transport, or the remote
service implementation. The total synthetic configuration gives capabilities
universal resource and argument scope, so it is not a least-privilege result.
At the A1 checkpoint, byte/filesystem and flush/fsync refinement,
`CompleteMediation`, protected-handle exclusivity, `ReturnResult`,
concurrency/global linearizability, and liveness remained outside the proved
boundary.

T6-M0 closes the model-level mediation boundary with a separately defined
protected-service execution. Accepted calls store request, attempt, descriptor,
durable cuts, and source index; eventwise coupling proves these equal the
canonical A1/WAL Invoke. `BrokerInvoke` additionally requires a request-local,
fresh attempt key. Only a call-indexed `ServiceLinearize` transition can mutate the target; nontarget
environment additions are separate, and the service alphabet contains no raw
context mutation. Eventwise A1/service coupling generates the protected call
trace, and prefix induction proves that its cut-erased calls equal the Broker/WAL
invocation projection. `CompleteMediation` is therefore derived from the two
executions rather than satisfied by choosing the protected trace from
`pi_invocations`.

A separate storage-parametric T4-C1 context records only Invoke labels exposed
by the masked storage view. Its interface has no protected handle, service call,
or mutation field, so every admitted plugged WAL execution derives the same
invocation-projection equality. This is a closed-alphabet no-bypass property
inside the formal deployment model, not verification of OS descriptors,
process isolation, network ACLs, or production service authentication.

Under the coupled deployment relation, each protected call has an exact WAL
Invoke origin. T4-C0 maps that
nonsilent event into the canonical Broker execution, where T1's
`invoke_temporal_at` supplies canonicality, acknowledged Authorize/Start
ancestry, unique authorization and start counts, and a successful append return
strictly before invocation. The coupled target-action theorem applies this
durable-authorization chain to every service linearization. The deployment
predicate packages these coupling, WAL, and configuration premises;
a generic quantified theorem proves every linearization durably authorized. The
premise-free M0 witness reuses A1's crash/retry execution, separately constructs
32 protected steps and couples them lock-step to A1, accepts the two calls
originating at WAL indices 12 and 23, linearizes
only attempt 1, and proves that the service trace and audit-context trace
both equal the WAL invocation projection.

T6-M0 does not prove a general prefix-indexed A1/WAL stuttering simulation or
the contextual end-to-end T6 lift. Production code and isolation, byte/fsync
persistence, `ReturnResult`, least privilege, concurrency/global
linearizability, and liveness also remain open.

T6-P0 adds the general relation needed above M0 for the fixed `EnsureMember`
model. `p0_a1_wal_step_match` advances a weak index by one for each
`Observe(global)` and stutters it for `ServiceLinearize` and `EnvironmentAdd`.
The execution-pair premise contains independently valid A1,
protected-service, and typed-WAL executions plus this step coupling. It is not
an existence theorem constructing a WAL execution from an arbitrary A1 run.

At every mapped prefix, the derived product equates the projected global
trace, A1 accumulated globals, and request-local adapter history; retains valid
A1/protected and WAL prefixes; equates protected calls with the WAL invocation
projection; derives `CompleteMediation`; and relates membership, environment
additions, and the exact set of linearized attempts across the A1 and protected
states. The execution-pair and full product are both prefix closed. A canonical
map based on the length of each A1 projected prefix recovers the step coupling
when the older final-trace equality premise is already available.

The premise-free witness relates 32 A1 events, 32 independently constructed
protected-service events, and 31 typed-WAL events using 33 map points. It
stutters at points 13 and 14 for the silent attempt-1 linearization and retains
complete mediation and final effect-state agreement. T6-P0 verifies 1,000
cumulative obligations with zero errors, 23 beyond T6-M0. It does not construct
a matching WAL execution for every adapter execution.

### T6-X0: contextual end-to-end composition

T6-X0 composes P0's adapter-to-WAL weak index with T4-C2's canonical
WAL-to-Broker index. Given a storage-parametric program context, a plugged WAL
execution, and the P0 product, `x0_contextual_product` relates every adapter
prefix to its mapped Broker prefix. The relation retains P0's trace, mediation,
and effect-state facts; equates the request-local adapter history with the
Broker projection; preserves the exact plugged context state and masked view;
and establishes T1 safety at the mapped Broker prefix. This is a conditional
lift of supplied executions, not a construction of a WAL execution from an
arbitrary adapter run.

For a selected terminal, `t6_x0_ensure_member_terminal_end_to_end` combines the
contextual product with the frozen terminal bridge. Exact normalized projection
agreement transports the terminal, `Refines`, and per-request effect refinement
from the WAL trace to the canonical Broker trace; physical-projection agreement
transports `CompleteMediation`. The protected-state relation grounds the
external run in the separately executed service state.

The premise-free 32-adapter/32-protected/31-WAL witness terminates
`Unknown(NonConclusiveFailure)`, denotes one rather than zero effects, contains
exactly one durably authorized protected linearization, and retains mediation
at the canonical Broker endpoint. T6-X0 verifies 1,022 cumulative obligations
with zero errors, 22 beyond T6-P0.

## 6. Theorem Roadmap

The normative proof layers are:

| Layer | Statement |
|---|---|
| [T1](mechanization-contract.md#t1-parameterized-broker-safety) | Parameterized Broker safety over every finite prefix-closed execution |
| [T2](mechanization-contract.md#t2-atomic-journal-runtime-simulation) | Independent atomic-Journal runtime simulates the Broker |
| [T3](mechanization-contract.md#t3-typed-wal-simulation) | Typed WAL simulates atomic Journal and preserves acknowledged prefixes |
| [T4-C0](mechanization-contract.md#t4-c0-closed-wal-to-broker-composition) | Closed T3/T2 weak simulations compose into a direct WAL-to-Broker result with T1 safety |
| [T4-C1](mechanization-contract.md#t4-c1-context-observation-and-plugging-foundation) | Ordered context observations and masked-state relational plugging are nonvacuous and prefix closed |
| [T4-C2](mechanization-contract.md#t4-c2-contextual-replacement-and-composition) | Storage-parametric contextual replacement lifts the closed T4-C0 composition through T4-C1 plugging |
| [T5-S0](mechanization-contract.md#t5-recovery-and-committed-history-prefix-preservation) | Exact one-step committed-history laws for Broker, Journal, and WAL; only durable Commit linearization appends one entry |
| [T5-E0](mechanization-contract.md#t5-recovery-and-committed-history-prefix-preservation) | Every ordered configuration interval of a finite Broker, Journal, or WAL execution monotonically extends committed history |
| [T5-R0](mechanization-contract.md#t5-recovery-and-committed-history-prefix-preservation) | Every first-`FinishRecover` episode stutters committed history at each step and preserves it exactly at the endpoint |
| [T5-C0](mechanization-contract.md#t5-recovery-and-committed-history-prefix-preservation) | T4's canonical contextual map preserves commit deltas, all-prefix committed history, and source-recovery endpoint equality |
| [T5](mechanization-contract.md#t5-recovery-and-committed-history-prefix-preservation) | Every step extends committed history; recovery preserves it exactly |
| [H1](mechanization-contract.md#h1-artifact-and-nonvacuity-checkpoint) | A concrete total well-formed configuration unconditionally inhabits the cumulative T5-C0 premise/conclusion package, and the source-hashed artifact records the checked inputs |
| [T6-D0](mechanization-contract.md#t6-d0-terminal-and-adapter-definition-freeze) | Adapter and terminal vocabulary, duplicate-rejecting selectors, evidence/compatibility branches, and Journal/WAL bridge statement interfaces are frozen without claiming the bridge theorem |
| [T6-E0](mechanization-contract.md#t6-e0-terminal-evidence) | Broker invariants and exact event projections imply configuration-explicit terminal `OutcomeEvidence` over the request-local adapter history |
| [T6-C0](mechanization-contract.md#t6-c0-terminal-compatibility) | Under `AdapterRely`, Broker invariants and exact projections imply retry-class-specific `BrokerOutcomeCompatible` for the selected terminal outcome |
| [T6-S0](mechanization-contract.md#t6-s0-terminal-evidence-and-compatibility-bridge) | The generic terminal conclusions compose, and existing final-prefix agreement plus Journal/WAL representation discharge the frozen backend wrappers without a new simulation invariant |
| [T6-A0](mechanization-contract.md#t6-a0-concrete-adapter-semantic-closure) | `AdapterVerified` closes the frozen terminal bridge to `Refines`; a concrete idempotent set-insert adapter and nonempty typed-WAL Commit execution inhabit the complete semantic package |
| [T6-A1](mechanization-contract.md#t6-a1-executable-adapter-protocol-refinement) | An operational `EnsureMember` adapter/service machine derives `AdapterRely` and composes with an exact crash/recovery/retry typed-WAL execution whose Unknown terminal denotes one abstract effect |
| [T6-M0](mechanization-contract.md#t6-m0-mediation-and-protected-handle-exclusivity) | A separately defined protected-service execution and closed-interface storage-parametric context derive complete mediation, target-action provenance, and durable authorization for the concrete crash/retry witness |
| [T6-P0](mechanization-contract.md#t6-p0-prefix-indexed-adapterwalprotected-product) | A conditional weak-index product relates A1, protected-service, and typed-WAL executions at every prefix, preserving trace/history, mediation, and effect-state agreement and admitting prefix truncation |
| [T6-X0](mechanization-contract.md#t6-x0-storage-parametric-contextual-end-to-end) | The P0 and T4-C2 maps compose into an all-prefix adapter/WAL/Broker contextual product; terminal refinement and mediation transport exactly to the canonical Broker trace |
| [T6](mechanization-contract.md#t6-conditional-end-to-end-theorem) | Under persistence, mediation, context, and adapter relies, each terminal request refines its class-specific abstract effect |

T1--T5 are machine checked. T3 includes
the independent typed-WAL machine, parser algebra, local representation
invariant, event closure, parsed-prefix monotonicity, all-execution-state
preservation, and the compressed WAL-to-Journal weak simulation with per-prefix
representation and observation agreement. T4-C0 composes that simulation with
T2, supplies a canonical prefix-related Broker execution, and establishes T1
safety for it and every mapped prefix. T4-C1 supplies the ordered observation,
masked endpoint-view, relational context, and three-backend structural plugging
foundation. T4-C2 supplies canonical finite forward contextual replacement.
T5-S0 supplies the exact local step laws, T5-E0 supplies finite execution-
interval monotonicity, and T5-R0 supplies Crash-to-first-`FinishRecover`
equality. T5-C0 supplies exact delta commutation, all-prefix mapped
`alpha_commit` equality, and contextual recovery endpoint export. T6-D0 fixes
the complete terminal/adapter interface and separate backend statement
boundaries. T6-E0 proves the `OutcomeEvidence` half of the generic bridge from
the Broker invariant and exact event projections. T6-C0 proves the
`BrokerOutcomeCompatible` half by terminal-outcome and retry-class analysis.
T6-S0 completes their conjunction and the two frozen backend wrappers by
reusing final-prefix trace agreement and the existing representation
relations. It introduces no new simulation invariant. T6-A0 then applies an
`AdapterVerified` interpretation to obtain generic `Refines` and per-request
effect-refinement exports and inhabits them with `EnsureMember` plus a terminal
typed-WAL execution. T6-A1 then derives the previously assumed `AdapterRely`
for an operational `EnsureMember` adapter/service execution, proves its exact
coupling to the typed-WAL trace, and exports a premise-free mixed-outcome
crash/retry package with one abstract effect. T6-M0 adds the separately defined,
lock-step-coupled protected service, derived complete mediation, closed-alphabet
audit context, and T1-backed durable authorization provenance for that witness.
T6-P0 adds the conditional prefix-indexed combined
adapter/protected/WAL product, all-prefix effect-state agreement, and prefix
closure. T6-X0 composes that map with T4-C2, proves the storage-parametric
all-prefix contextual product, and transports terminal refinement and mediation
to the canonical Broker trace.
H1 adds an unconditional configuration/package inhabitance theorem and artifact
evidence, not an external semantic interpretation; its inert witness does not
inhabit a terminal `AdapterRely` execution. A0's semantic witness and A1's
operational witness separately close those nonvacuity obligations.

T1--T5 and the conditional single-request T6-X0 theorem are proved safety and
refinement results for arbitrary finite executions with
one globally serialized writer and executor slot. They do not include verified
production Rust/network/service code, `ReturnResult`, liveness, multi-worker
linearizability, or a global linearization order for external effects of
different requests. T4 specifically does not establish reverse contextual
equivalence, autonomous context steps, or protected-handle exclusivity. A0/A1
establish per-request adapter effect refinement for `EnsureMember`; M0 supplies
model-level complete mediation and closed-alphabet no-bypass through an additional
protected execution and context. None of these checkpoints supplies byte-level
WAL correctness or production OS/network isolation.

## 7. Current Boundary

| Claim | Current status |
|---|---|
| Broker safety invariants | Exhaustively checked in finite scenarios and proved for arbitrary finite relational Broker executions by T1 |
| Typed Journal prefix and replay safety | Exhaustively checked in a bounded scenario and proved for arbitrary legal finite Journals by R1 |
| Independent atomic-Journal-to-Broker refinement | Proved for arbitrary finite relational runtime executions by T2, with exact per-prefix `Representation` and projection agreement |
| Coupled Journal-to-Broker refinement | Temporal property additionally checked in uncontrolled and idempotent-retry scenarios |
| Typed Full/Torn WAL local invariant | Proved for arbitrary finite relational WAL executions by T3-W0, including the LSN-sensitive parser, all 17 WAL actions, interrupted scans, canonical truncation, parsed-prefix monotonicity, and acknowledged-prefix containment |
| Typed Full/Torn WAL-to-Journal refinement | Proved for arbitrary finite relational WAL executions by T3, with exact 12-match/5-stutter compression, a nondecreasing weak-index map, per-prefix `Representation`, normalized projection agreement, and cross-prefix acknowledged durability; also checked in bounded TLC scenarios |
| Closed typed-WAL-to-Broker composition | Proved for arbitrary finite relational WAL executions by T4-C0: generic weak-index and simulation composition, canonical WAL-to-Broker witness, composed state/projection relations, and T1 safety for the target and every mapped prefix; context state, plugging, and lifting are excluded |
| Context observation and plugging | Completed T4-C1: one ordered cut-erased context trace, masked endpoint views, arbitrary relational contexts, exact WAL/Journal/Broker structural plugging, erasure, prefix closure, hidden stuttering, translation compatibility, and zero-step plus visible-`Crash` nonvacuity witnesses |
| Parameterized contextual replacement | Completed T4-C2 for arbitrary finite plugged WAL executions: T3-translation-selected context compression, canonical plugged Broker construction, exact context-state and ordered endpoint-view equality at every canonical mapped prefix, and inherited C0 simulation/projection/T1 conclusions |
| Exact one-step committed history | Completed T5-S0 for all accepted Broker, atomic-Journal, and typed-WAL steps: exact zero-or-one-entry delta equations, backend-specific durable linearization points, prefix monotonicity, and WAL parsed-view equality under the runtime `wal_invariant`, including Torn and truncation stuttering |
| Finite execution committed-history monotonicity | Completed T5-E0 for Broker, atomic-Journal, and typed-WAL executions: for all `i <= j < configs.len()`, the history at `i` is a prefix of the history at `j`; WAL exposes only `Exec` and discharges its runtime invariant internally |
| Exact recovery-episode committed history | Completed T5-R0 for all three closed executions: event-only first-Finish predicate, derived recovery-repair classification, per-step zero delta and stuttering, exact pre-Crash/post-Finish equality, and inhabited minimal plus repeated-Crash witnesses |
| Contextual mapped committed history | Completed T5-C0: exact T3/T2/T4 delta refinement, WAL/Broker `alpha_commit` equality at every canonical mapped prefix, four source/mapped recovery endpoint equalities, exported storage-parametric contextual theorem, and a combined inert-context six-event/seven-state witness; no target Broker episode is concluded |
| Terminal evidence and compatibility bridge | Completed T6-S0: T6-E0 evidence and T6-C0 compatibility compose at the Broker boundary; final-prefix trace agreement and the existing atomic-Journal/WAL representation relations discharge both frozen wrappers without a new simulation invariant; adapter effects and a concrete terminal `AdapterRely` witness remain excluded |
| Concrete adapter semantic closure | Completed T6-A0: the frozen bridge plus `AdapterVerified` implies `Refines` and per-request effect refinement; `EnsureMember` supplies an idempotent set-insert interpretation, nondegeneracy facts, and a premise-free nonempty 20-event typed-WAL Commit package satisfying `AdapterRely` |
| Executable adapter refinement | Completed T6-A1: an operational `EnsureMember` adapter/service model derives `AdapterRely` from its transition invariant and composes with the exact typed-WAL trace; the premise-free 32-adapter-event/31-WAL-event crash/retry witness terminates `Unknown(NonConclusiveFailure)`, excludes Fail, and denotes exactly one abstract effect |
| Mediation and protected boundary | Completed T6-M0: a separately constructed 32-step protected-service execution is lock-step coupled to A1 and derives equality with the WAL invocation projection; the closed audit-context alphabet has no independent protected-call or mutation action; every deployment linearization names a prior durably authorized call; the premise-free witness accepts two calls and linearizes exactly attempt 1 |
| Prefix-indexed adapter/protected/WAL product | Completed T6-P0 for conditionally paired executions: a weak index advances on observed global events and stutters on silent A1 events; every related prefix preserves trace/history, complete mediation, and A1/protected effect-state agreement; the product is prefix closed and inhabited by the 32/32/31-step crash/retry witness; no matching-WAL existence or contextual lift is claimed |
| Contextual adapter/WAL/Broker end-to-end lift | Completed T6-X0: P0's map composes with the T4-C2 WAL-to-Broker map; every adapter prefix retains exact request history, context state/view, effect grounding, and mapped-prefix T1 safety; terminal `Refines`, per-request effect refinement, and complete mediation transport to the Broker trace; the 32/32/31 witness ends Unknown with one abstract effect and one durably authorized protected linearization |
| Direct BrokerContext[WAL]-to-Broker refinement | Temporal projections checked with phased recovery in bounded uncontrolled and idempotent-retry products |
| Two-request/two-capability composed prefix | Checked for cross-request interleavings and recovery quarantine; the five-record bound does not reach normal terminal records |
| Verus M0 parameterized safety slice | 21 obligations verified with no admitted proof bodies; reduced atomic-Journal language only |
| Verus R1 typed Journal replay safety | 86 obligations verified with no admitted proof bodies; full record/replay and durable provenance, but no Broker event or physical-history theorem |
| Verus B1 generic append/trace safety | 39 obligations verified with no admitted proof bodies; crash-reset append control, DiskFull normalization, acknowledgments, and projections, but not yet instantiated with R1 legality |
| Verus C1 legal append/replay composition | 128 obligations verified transitively with no admitted proof bodies: 86 R1 + 39 B1 + 3 composition obligations; every admissible linearization preserves Journal legality and replay safety |
| Verus D1 durable/append coupling | 144 obligations verified transitively with no admitted proof bodies: the C1 closure plus 16 obligations proving that a separate durable state changes exactly at linearization and remains equal to replay; executor slot and recovery are excluded |
| Verus Q1 durable retry/recovery queries | 144 obligations verified transitively with no admitted proof bodies: the C1 closure plus 16 obligations for total durable attempt/outcome queries, replay bridges, ghost-free recovery predicates, and structural-to-abstract guard implication |
| Verus K4-C0 admission-manifest configuration refinement | 255 obligations verified transitively with no admitted proof bodies: the K3-A0 closure plus 7 obligations defining finite capability/request lookup, a total R1 `Config` view, manifest well-formedness, generic `config_wf` refinement, and a premise-free Idempotent witness; K1-K3 still execute against their fixed demo configuration |
| Verus K4-R0 parameterized Authorize guard | 266 obligations verified transitively with no admitted proof bodies: the K4-C0 closure plus 11 obligations for executable finite lookup, lookup soundness/completeness, arbitrary-manifest Authorize decision refinement to Q1/R1, and a premise-free accepted M4/K3 Idempotent profile; the remaining record guards, mutations, and append state still use the fixed demo configuration |
| Verus K4-R1 parameterized Prepare/Start guards | 274 obligations verified transitively with no admitted proof bodies: the K4-R0 closure plus 8 obligations for executable manifest field/class/capability/attempt profiles, arbitrary-manifest Prepare and Start decision refinement to Q1/R1, and a premise-free Idempotent profile witness; remaining guards, durable mutations, and append state still use the fixed demo configuration |
| Verus K4-R2 parameterized Authorize mutation | 276 obligations verified transitively with no admitted proof bodies: the K4-R1 closure plus 2 obligations for arbitrary-manifest accepted Authorize mutation refinement to R1 `apply_record` and a premise-free Idempotent execution that materializes entries, decrements budget from 4 to 3, records the capability witness, and preserves durable coupling; remaining mutations, materialization, and append state still use the fixed demo configuration |
| Verus K4-R3 parameterized Prepare mutation | 278 obligations verified transitively with no admitted proof bodies: the K4-R2 closure plus 2 obligations for arbitrary-manifest accepted Prepare phase mutation refinement to R1 `apply_record` and a premise-free Idempotent Authorize-to-Prepare execution that preserves budget 3 and capability witness 1; remaining mutations, materialization, and append state still use the fixed demo configuration |
| Verus K4-R4 parameterized Arm guard/mutation | 281 obligations verified transitively with no admitted proof bodies: the K4-R3 closure plus 3 obligations for arbitrary-manifest Arm decision refinement, accepted Arm phase mutation refinement to R1 `apply_record`, and a premise-free Idempotent Authorize-to-Prepare-to-Arm execution preserving budget 3 and capability witness 1; remaining guards, mutations, materialization, and append state still use the fixed demo configuration |
| Verus K4-R5 parameterized Start mutation | 283 obligations verified transitively with no admitted proof bodies: the K4-R4 closure plus 2 obligations for arbitrary-manifest accepted Start attempt-log mutation refinement to R1 `apply_record` and a premise-free Idempotent Authorize-to-Prepare-to-Arm-to-Start execution producing exactly one pending attempt while preserving phase and budget 3; remaining guards, mutations, materialization, and append state still use the fixed demo configuration |
| Verus K4-R6 parameterized Outcome guard/mutation | 286 obligations verified transitively with no admitted proof bodies: the K4-R5 closure plus 3 obligations for arbitrary-manifest Outcome decision refinement, accepted Outcome mutation refinement to R1 `apply_record`, and a premise-free Idempotent Authorize-to-Prepare-to-Arm-to-Start-to-Outcome execution recording a successful observation while preserving phase and budget 3; Commit, remaining mutations, materialization, and append state still use the fixed demo configuration |
| Verus K4-R7 parameterized Commit guard/mutation | 289 obligations verified transitively with no admitted proof bodies: the K4-R6 closure plus 3 obligations for arbitrary-manifest Commit decision refinement, accepted Commit phase mutation refinement to R1 `apply_record`, and a premise-free Idempotent Authorize-to-Prepare-to-Arm-to-Start-to-Outcome-to-Commit execution reaching `Committed` with value 1 while preserving the recorded attempt and budget 3; Revoke/Fail/Unknown, remaining mutations, materialization, and append state still use the fixed demo configuration |
| Verus K4-A0 bounded manifest append certificate | 301 obligations verified transitively with no admitted proof bodies: the K4-R7 closure plus 12 obligations for an Idempotent manifest profile, a generic legal-record-to-append encoder, C1 legal replay and all-prefix checkpoints, exact one-based acknowledgment cuts, projection into K3's concrete `KJournalRecord` vocabulary, and a premise-free witness combined with the K4-R7 mutation chain; arbitrary K3 transition parameterization and Rust-broker refinement remain open |
| Verus K4-A1 manifest-aware concrete append-state bridge | 309 obligations verified transitively with no admitted proof bodies: the K4-A0 closure plus 8 obligations for a manifest-indexed invariant over concrete K3 durable/journal/ack/control state, executable Call/Linearize/Return operations, six generic K4 durable-mutation dispatches, exact one-based LSN/cut agreement, a premise-free six-record state witness, and a terminal concrete-state theorem; arbitrary K3 transitions/record variants and Rust-broker refinement remain open |
| Verus K4-A2 generic supported-record append-state bridge | 326 obligations verified transitively with no admitted proof bodies: the K4-A1 closure plus 17 obligations for supported-record classification, manifest-budget capability materialization, generic request/capability ensuring, manifest-aware semantic and exact-reference guards, arbitrary legal Call/Linearize/Return state threading, exact LSN/cut agreement, request-generic committed-state reflection, and a premise-free terminal witness; Revoke/Fail/Unknown, crash/recovery, byte-WAL, and Rust-broker refinement remain open |
| K4-I0 compiled broker-to-kernel integration checkpoint | Executable artifact evidence, outside the cumulative Verus target count: the real reference broker produces an 8-record idempotent crash/reopen/retry WAL and a 6-record Deduplicated WAL; both are incrementally accepted by proof-erased K4-A2 at exact one-based cuts with terminal durable-state and budget checks; unsupported Revoke/Fail/Unknown mappings fail closed; this is not an implementation-refinement theorem |
| Verus B2-R record-side Broker safety | 169 obligations verified transitively with no admitted proof bodies: the Q1 closure plus 25 obligations for the complete slot ADT and record transformer, append and recovery control, durable slot agreement, exact record/ack/control projections, and every-prefix safety; physical events and source histories are excluded |
| Verus B2-C rich configuration refinement | 175 obligations verified transitively with no admitted proof bodies: the B2-R closure plus 6 obligations for immutable Request/Capability records, field-derived scope matching, canonical calls, exact R1 erasure, and stable-key preservation |
| Verus B2-P0 physical transition/trace substrate | 193 obligations verified transitively with no admitted proof bodies: the B2-C closure plus 18 obligations for Invoke/Deliver transitions, source-update mechanics, B2-R preservation, and exact per-prefix Journal/acknowledgment/physical projections; physical causality and provenance remain excluded |
| Verus B2-P1 physical causality safety | 251 obligations verified transitively with no admitted proof bodies: the B2-P0 closure plus 58 obligations for per-attempt Invoke/Delivered uniqueness and order, canonical proof cuts, acknowledged Start coverage, non-retroactive acknowledgment, exact live-slot delivery sources, and all-prefix preservation; aggregate retry bounds, durable Outcome ordering, and terminal provenance remain excluded |
| Verus B2-P2 retry/authorization/Outcome refinement | 276 obligations verified transitively with no admitted proof bodies: the B2-P1 closure plus 25 obligations for aggregate retry and uncontrolled-at-most-once bounds, valid acknowledged Authorize/Start ancestry, failure-safe invocation cuts, exact durable Outcome-after-Delivered ordering, and all-prefix preservation; terminal provenance and global T1 assembly remain excluded |
| Verus B2-P3 terminal physical provenance | 292 obligations verified transitively with no admitted proof bodies: the B2-P2 closure plus 16 obligations for exact commit-source definedness and payload provenance, recovery-safe physical Failure provenance, durable Unknown anchors, recovery-repair classification/source preservation, and all-prefix closure; global Event/Exec/append-protocol T1 assembly remains excluded |
| Verus B2-L exact Broker contract | 310 obligations verified transitively with no admitted proof bodies: the B2-P3 closure plus 18 obligations packaging exactly the thirteen numbered `BrokerInvariant` clauses, rich scope confinement, Start-backed slot cases, and all-prefix preservation |
| Verus B2-A append/epoch bridge | 335 obligations verified transitively with no admitted proof bodies: the B2-L closure plus 25 obligations for the index-preserving B1 append projection, exact successful-return cuts, append agreement, and maximal crash-free epoch classification |
| Verus G0 global event closure | 342 obligations verified transitively with no admitted proof bodies: the B2-A closure plus 7 obligations for the 22-constructor global event ADT, exact 11 accepted/11 rejected Broker boundary, and encode/decode inversion |
| Verus G1-P global projections | 410 obligations verified transitively with no admitted proof bodies: the G0 closure plus 68 obligations defining and relating all normative global projections without changing prefix indices |
| Verus G1-E relational execution | 429 obligations verified transitively with no admitted proof bodies: the G1-P closure plus 19 obligations for relational configuration-sequence `Exec`, prefix closure, backend-event rejection, and exact correspondence with the local verified runner |
| Verus T1 parameterized Broker safety | 462 obligations verified transitively with no admitted proof bodies: the G1-E closure plus 33 obligations for exact per-prefix `TraceAgreement`, including Invoke cut agreement, all thirteen invariant clauses, append/recovery structure, invocation and retry safety, terminal uniqueness, committed-value provenance, the exported generic theorem, and the conservative configuration-accessor lemma |
| Verus T2-J0 independent atomic runtime | 476 obligations verified transitively with no admitted proof bodies: the T1 closure plus 14 obligations for the replay-shadow-free concrete state, exact 11-constructor runtime boundary, direct transitions, relational execution, Journal legality, and append-invariant preservation |
| Verus T2-J1 atomic trace agreement | 487 obligations verified transitively with no admitted proof bodies: the T2-J0 closure plus 11 obligations for operational trace admissibility, exact per-prefix Journal/physical/acknowledgment and Invoke-cut agreement, successful cuts, and prefix closure |
| Verus T2-E event refinement | 509 obligations verified transitively with no admitted proof bodies: the T2-J1 closure plus 22 obligations for the one-label linearization renaming, non-silence of every accepted source step, trace translation, and equality of every normative T2 projection |
| Verus T2-R exact representation | 521 obligations verified transitively with no admitted proof bodies: the T2-E closure plus 12 obligations for proof-only abstraction, exact acknowledgment and source predicates, the full-history-to-acknowledged-prefix Start bridge, same-payload invalid-result provenance, and derivation from the local inductive invariant |
| Verus T2 atomic-Journal simulation | 532 obligations verified transitively with no admitted proof bodies: the T2-R closure plus 11 obligations for step commutation, constructed Broker execution, reusable weak-index shape, identity weak-index map, per-prefix representation/projection agreement, and the exported generic existential theorem |
| Verus T3-W0 typed-WAL runtime invariant | 578 obligations verified transitively with no admitted proof bodies: the T2 closure plus 46 obligations for LSN-sensitive Full/Torn parsing, exact 17-constructor runtime closure, direct crash/scan/recovery transitions, all eight `WALInvariant` clauses, B1/ghost coupling, parsed-history monotonicity, acknowledged-prefix durability, execution-prefix closure, and every-state preservation |
| Verus T3-W1-T WAL trace agreement | 589 obligations verified transitively with no admitted proof bodies: the T3-W0 closure plus 11 obligations for operational admissibility, exact successful-return cuts, per-prefix parsed-history agreement, Invoke cut agreement, and prefix closure |
| Verus T3-W1-E WAL event compression | 627 obligations verified transitively with no admitted proof bodies: the T3-W1-T closure plus 38 obligations for exact 12-match/5-stutter translation, compressed-prefix arithmetic, Journal closure, exact silence, and equality of every normalized T3 projection except the private `pi_wal` view |
| Verus T3-W1-R WAL/Journal representation | 642 obligations verified transitively with no admitted proof bodies: the T3-W1-E closure plus 15 obligations for the field-explicit parse relation, initial representation, projected invariants, visible-step commutation, and internal-step projection preservation |
| Verus T3 typed-WAL simulation | 660 obligations verified transitively with no admitted proof bodies: the T3-W1-R closure plus 18 obligations for the deterministic compressed Journal execution, reused weak-index shape, exact step matching, per-prefix representation/projection agreement, cross-prefix acknowledged durability, and the exported generic existential theorem |
| Verus T4-C0 closed WAL-to-Broker composition | 677 obligations verified transitively with no admitted proof bodies: the T3 closure plus 17 obligations for generic weak-index and weak-simulation composition, T2 lockstep collapse, composed representation and normalized projection agreement, the canonical WAL-to-Broker witness, and T1 safety for the target and every mapped prefix |
| Verus T4-C1 context observation and plugging | 721 obligations verified transitively with no admitted proof bodies: the T4-C0 closure plus 44 obligations for ordered normalized observations, exact append-I/O recovery, masked endpoint views, T2/T3 whole-history compatibility, three structural plugged products, erasure, hidden stuttering, prefix closure, and shared zero-step and visible-`Crash` witnesses |
| Verus T4-C2 contextual replacement and composition | 735 obligations verified transitively with no admitted proof bodies: the T4-C1 closure plus 14 obligations for T3-selected context compression, canonical plugged Journal/Broker construction, transferred context acceptance, exact mapped context-state and ordered endpoint-view equality, and the exported storage-parametric forward replacement theorem |
| Verus T5-S0 exact one-step committed history | 744 obligations verified transitively with no admitted proof bodies: the T4-C2 closure plus 9 obligations for exact Broker/Journal/WAL commit deltas, prefix monotonicity, and exact WAL parsed-view behavior under the runtime `wal_invariant` |
| Verus T5-E0 execution-interval monotonicity | 748 obligations verified transitively with no admitted proof bodies: the T5-S0 closure plus 4 obligations for generic prefix transitivity and Broker/Journal/WAL interval induction; the WAL export requires only `Exec` |
| Verus T5-R0 recovery-episode equality | 770 obligations verified transitively with no admitted proof bodies: the T5-E0 closure plus 22 obligations for recovery completeness/nonvacuity, generic repair and sequence facts, three-backend mode confinement, non-Online and per-episode step stuttering, prefix invariants, and endpoint equality; in the current report the first 34 registered targets contain 807 non-duplicated obligations |
| Verus T5-C0 contextual mapped recovery | 784 obligations verified transitively with no admitted proof bodies: the T5-R0 closure plus 13 delta-translation, weak-step, representation, mapped-prefix, recovery-endpoint, canonical, contextual, and paper-export obligations, plus 1 combined inert-context nonvacuity witness |
| Verus H1 artifact nonvacuity | 787 obligations verified transitively with no admitted proof bodies: the T5-C0 closure plus 3 obligations for a concrete total `FullConfig`, an unconditional concrete T5-C0 premise/conclusion package, and the existential cumulative-artifact inhabitance theorem |
| Verus T6-D0 terminal-definition freeze | 800 obligations verified transitively with no admitted proof bodies: the T5-C0 closure plus 16 obligations for evidence/compatibility branch unfolding, empty/singleton/duplicate terminal selection, unique/duplicate delivery cases, exact replay-Unknown decomposition, and adapter-rely/verification projections; it freezes statement interfaces but does not prove the T6 bridge |
| Verus T6-E0 terminal evidence | 818 obligations verified transitively with no admitted proof bodies: the T6-D0 closure plus 18 obligations for terminal-selector soundness, exact Outcome projection, causal-prefix preservation, physical-delivery uniqueness and selection, request-local projection preservation, the three terminal-evidence branches, and generic history/event exports; compatibility and backend wrappers remain excluded |
| Verus T6-C0 terminal compatibility | 835 obligations verified transitively with no admitted proof bodies: the T6-E0 closure plus 17 obligations for request-local invocation accounting, delivery-to-invocation selection, acknowledged-invocation witnesses, Deduplicated observation exclusion, Idempotent all-attempt failure coverage, Unknown-cause reconstruction, Uncontrolled invocation bounds, and the generic event/core compatibility exports; combined evidence, backend wrappers, and adapter effects remain excluded |
| Verus T6-S0 terminal bridge | 841 obligations verified transitively with no admitted proof bodies: the T6-C0 closure plus 6 obligations that combine T6-E0 evidence with T6-C0 compatibility, export the frozen core implication, and discharge the atomic-Journal and typed-WAL wrappers from their assumed execution, admissibility, final-prefix trace-agreement, and representation premises; no simulation invariant, adapter effect theorem, terminal `AdapterRely` witness, or caller-result action is added |
| Verus T6-A0 concrete semantic closure | 864 obligations verified transitively with no admitted proof bodies and zero errors: the current T6-S0 closure is 841 obligations after a conservative definitional T1 accessor, and A0 adds 23 obligations for generic `Refines`/per-request exports, the `EnsureMember` semantic contract and `AdapterVerified` proof, nondegeneracy and mixed-history semantic checks, the concrete 20-event WAL execution, its terminal rely/refinement package, and premise-free existential inhabitation |
| Verus T6-A1 executable adapter refinement | 916 obligations verified transitively with no admitted proof bodies and zero errors, 52 beyond T6-A0: operational adapter/service transitions and their inductive invariant derive exact global/physical projections and `AdapterRely`; a checked step theorem exposes remote-linearization provenance and a public trace theorem fixes the Crash/scan/recover/retry event ordering; the generic theorem composes an exactly coupled terminal typed-WAL execution to `Refines`; the premise-free seven-record witness couples 32 adapter events to 31 WAL events, excludes Fail, and establishes exactly one effect |
| Verus T6-M0 mediation and model no-bypass | 977 cumulative obligations verified with no admitted proof bodies and zero errors, 61 beyond T6-A1: a first-class protected-service execution, eventwise A1 coupling, derived invocation-trace mediation, closed-alphabet protected-action restriction in a storage-parametric context, exact WAL-to-T1 durable authorization provenance, and a premise-free two-call/one-linearization crash-retry package |
| Verus T6-P0 prefix-indexed execution product | 1,000 cumulative obligations verified with no admitted proof bodies and zero errors, 23 beyond T6-M0: weak A1/WAL step coupling, all-prefix trace/history and A1/protected effect-state agreement, derived per-prefix mediation, execution-pair and product prefix closure, a canonical map for already trace-equal executions, and a premise-free 32-adapter/32-protected/31-WAL witness |
| Verus T6-X0 contextual end-to-end composition | 1,022 cumulative obligations verified with no admitted proof bodies and zero errors, 22 beyond T6-P0: composed adapter-to-WAL-to-Broker weak indexing, exact all-prefix history/context/view and T1 transport, protected-run grounding, source/target terminal and effect refinement, endpoint mediation transport, and a premise-free 32/32/31 Unknown one-effect witness |
| Byte decoding and checksum correctness | Not yet modeled |
| Actual flush/fsync and filesystem contract | Assumed below the typed WAL |
| Parameterized proof | T6-X0 is the latest completed target at 1,022 cumulative obligations with zero errors, 22 beyond T6-P0. The current retained run passes 45/45 targets, contains 1,062 dependency-aware non-duplicated obligations, and sums to 23,866 target obligations. The historical retained T6-S0 checkpoint was 840 across 40 targets with 880 non-duplicated obligations, while the imported T6-S0 closure is 841 after the conservative accessor lemma. T1--T5, H1, T6-D0, T6-E0, T6-C0, T6-S0, T6-A0, T6-A1, T6-M0, T6-P0, and the conditional single-request T6-X0 theorem are complete; production-code and isolation refinement, matching-WAL existence, byte/fsync, caller-result, additional-adapter, concurrency/global-linearizability, and liveness boundaries remain open |

The TLA+ results are model-checking evidence for the architecture and theorem
statements. The TLC runner first validates exact manifest structure, unique
scenario names and configuration registrations, allowed tiers, input
existence, and complete registration of every `formal/*.cfg`. It then executes
from a read-only, hash-checked temporary copy of every local TLA+ module and the
selected configurations and an isolated per-run tool tree, and emits a unique
machine-readable report by default. The Verus runner invokes the verifier only
on an exact read-only source snapshot and records the schema, runner, lock,
sources, and fresh Rust tree by hash; complete source/import registration,
immediate-predecessor discipline, and pre/post-target snapshot checks fail
closed on artifact drift. These controls identify the checked inputs but do not
turn bounded TLC exploration into a parameterized proof.

M0 separately proves its reduced machine slice over unbounded
identifiers and arbitrary total capability maps. R1 proves the typed Journal,
total replay, legal references, exact durable projections, and replay
invariants for every legal prefix under a flattened immutable configuration.
B1 separately proves generic crash-reset append and acknowledgment traces.
C1 composes B1 eligibility with R1 structural legality at every prefix. D1
adds exact coupling to a separately stored durable replay state. Q1 supplies
the durable retry/recovery queries and proves their agreement with Journal
queries, allowing executable recovery guards to avoid ghost state. B2-R proves
the complete record-side Broker state and slot update, crash/recovery control,
append-interface shape, and all-prefix trace agreement. B2-C supplies the rich
configuration and proves its exact erasure into R1, including concrete scope
and canonical calls. B2-P0 verifies physical transitions and their per-prefix
trace substrate. B2-P1 verifies per-attempt physical causality,
acknowledged-Start cuts, and exact live-slot delivery sources. B2-P2 verifies
aggregate retry limits, valid acknowledged authorization, failure-safe
invocation cuts, and durable Outcome ordering. B2-P3 verifies terminal physical
provenance and recovery-source preservation. B2-L packages the exact local
contract, B2-A proves the append/epoch bridge, G0 and G1-P close the global
alphabet and projections, and G1-E supplies the relational execution semantics.
The exported T1 theorem proves parameterized Broker safety for every finite
execution and prefix, T2 proves the independent atomic-Journal runtime
simulation, and T3 proves the independent typed-WAL runtime invariant,
parser/recovery algebra, and compressed weak simulation into the Journal.
T4-C0 generically composes the T3 and T2 maps and relations, constructs the
canonical Broker witness, and discharges T1 safety for all mapped prefixes.
T4-C1 defines and verifies the common context observation and structural
plugging interface. T4-C2 completes the exact-state contextual lift and canonical
plugged Broker construction. T5-S0 proves the exact one-step committed-history
laws, T5-E0 proves finite execution-interval monotonicity, and T5-R0 proves
exact first-`FinishRecover` equality. T5-C0 completes contextual mapped
committed-history preservation. H1 proves the cumulative T5-C0 package is
inhabited under a concrete total configuration and records the hardened
artifact boundary. T6-E0 and T6-C0 establish the two generic terminal halves;
T6-S0 combines them and discharges both backend wrappers through the existing
trace-agreement and representation premises, without a new simulation
invariant. T6-A0 closes the generic result to `Refines` under
`AdapterVerified` and supplies the concrete `EnsureMember` semantic contract
and terminal `AdapterRely` witness. T6-A1 adds the operational adapter/service
machine, derives `AdapterRely` from its invariant, and composes that result with
the exact typed-WAL crash/recovery/retry execution. T6-M0 adds the independent
protected-service execution, derives complete mediation instead of selecting a
protected trace, proves closed-alphabet model no-bypass for the storage-parametric
audit context, and connects every protected target action to a prior T1-durably
authorized call. T6-P0 adds the conditional weak-indexed product across the A1,
protected, and WAL executions and proves its every-prefix invariants and prefix
closure. T6-X0 composes this relation with T4-C2, proves the conditional
storage-parametric contextual lift, and transports the selected terminal,
effect refinement, and mediation to the canonical Broker execution. No
production Rust/network/service or OS-isolation refinement, matching-WAL
existence for arbitrary adapter runs, byte/fsync proof, `ReturnResult`,
additional-adapter theorem, concurrency/global linearizability, or liveness
theorem is claimed.
