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
Adapter laws are explicit `AdapterRely` assumptions, not unrestricted Journal
legality.

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
`alpha_commit` equality, and contextual recovery endpoint export. T6 remains
open; its next checkpoint is T6-S0, the generic
`TerminalEvidenceAndCompatibility` bridge. H1 adds an unconditional
configuration/package inhabitance theorem and artifact evidence, not an
external semantic interpretation. None of the completed results yet interprets the
physical history as an external tool effect.

T1--T6 are safety and refinement results for arbitrary finite executions with
one globally serialized writer and executor slot. They do not include
`ReturnResult`, liveness, multi-worker linearizability, or a global
linearization order for external effects of different requests. T4 specifically
does not establish reverse contextual equivalence, autonomous context steps,
protected-handle exclusivity, adapter effect refinement, or byte-level WAL
correctness.

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
| Direct BrokerContext[WAL]-to-Broker refinement | Temporal projections checked with phased recovery in bounded uncontrolled and idempotent-retry products |
| Two-request/two-capability composed prefix | Checked for cross-request interleavings and recovery quarantine; the five-record bound does not reach normal terminal records |
| Verus M0 parameterized safety slice | 21 obligations verified with no admitted proof bodies; reduced atomic-Journal language only |
| Verus R1 typed Journal replay safety | 86 obligations verified with no admitted proof bodies; full record/replay and durable provenance, but no Broker event or physical-history theorem |
| Verus B1 generic append/trace safety | 39 obligations verified with no admitted proof bodies; crash-reset append control, DiskFull normalization, acknowledgments, and projections, but not yet instantiated with R1 legality |
| Verus C1 legal append/replay composition | 128 obligations verified transitively with no admitted proof bodies: 86 R1 + 39 B1 + 3 composition obligations; every admissible linearization preserves Journal legality and replay safety |
| Verus D1 durable/append coupling | 144 obligations verified transitively with no admitted proof bodies: the C1 closure plus 16 obligations proving that a separate durable state changes exactly at linearization and remains equal to replay; executor slot and recovery are excluded |
| Verus Q1 durable retry/recovery queries | 144 obligations verified transitively with no admitted proof bodies: the C1 closure plus 16 obligations for total durable attempt/outcome queries, replay bridges, ghost-free recovery predicates, and structural-to-abstract guard implication |
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
| Verus T1 parameterized Broker safety | 461 obligations verified transitively with no admitted proof bodies: the G1-E closure plus 32 obligations for exact per-prefix `TraceAgreement`, including Invoke cut agreement, all thirteen invariant clauses, append/recovery structure, invocation and retry safety, terminal uniqueness, committed-value provenance, and the exported generic theorem |
| Verus T2-J0 independent atomic runtime | 475 obligations verified transitively with no admitted proof bodies: the T1 closure plus 14 obligations for the replay-shadow-free concrete state, exact 11-constructor runtime boundary, direct transitions, relational execution, Journal legality, and append-invariant preservation |
| Verus T2-J1 atomic trace agreement | 486 obligations verified transitively with no admitted proof bodies: the T2-J0 closure plus 11 obligations for operational trace admissibility, exact per-prefix Journal/physical/acknowledgment and Invoke-cut agreement, successful cuts, and prefix closure |
| Verus T2-E event refinement | 508 obligations verified transitively with no admitted proof bodies: the T2-J1 closure plus 22 obligations for the one-label linearization renaming, non-silence of every accepted source step, trace translation, and equality of every normative T2 projection |
| Verus T2-R exact representation | 520 obligations verified transitively with no admitted proof bodies: the T2-E closure plus 12 obligations for proof-only abstraction, exact acknowledgment and source predicates, the full-history-to-acknowledged-prefix Start bridge, same-payload invalid-result provenance, and derivation from the local inductive invariant |
| Verus T2 atomic-Journal simulation | 531 obligations verified transitively with no admitted proof bodies: the T2-R closure plus 11 obligations for step commutation, constructed Broker execution, reusable weak-index shape, identity weak-index map, per-prefix representation/projection agreement, and the exported generic existential theorem |
| Verus T3-W0 typed-WAL runtime invariant | 577 obligations verified transitively with no admitted proof bodies: the T2 closure plus 46 obligations for LSN-sensitive Full/Torn parsing, exact 17-constructor runtime closure, direct crash/scan/recovery transitions, all eight `WALInvariant` clauses, B1/ghost coupling, parsed-history monotonicity, acknowledged-prefix durability, execution-prefix closure, and every-state preservation |
| Verus T3-W1-T WAL trace agreement | 588 obligations verified transitively with no admitted proof bodies: the T3-W0 closure plus 11 obligations for operational admissibility, exact successful-return cuts, per-prefix parsed-history agreement, Invoke cut agreement, and prefix closure |
| Verus T3-W1-E WAL event compression | 626 obligations verified transitively with no admitted proof bodies: the T3-W1-T closure plus 38 obligations for exact 12-match/5-stutter translation, compressed-prefix arithmetic, Journal closure, exact silence, and equality of every normalized T3 projection except the private `pi_wal` view |
| Verus T3-W1-R WAL/Journal representation | 641 obligations verified transitively with no admitted proof bodies: the T3-W1-E closure plus 15 obligations for the field-explicit parse relation, initial representation, projected invariants, visible-step commutation, and internal-step projection preservation |
| Verus T3 typed-WAL simulation | 659 obligations verified transitively with no admitted proof bodies: the T3-W1-R closure plus 18 obligations for the deterministic compressed Journal execution, reused weak-index shape, exact step matching, per-prefix representation/projection agreement, cross-prefix acknowledged durability, and the exported generic existential theorem |
| Verus T4-C0 closed WAL-to-Broker composition | 676 obligations verified transitively with no admitted proof bodies: the T3 closure plus 17 obligations for generic weak-index and weak-simulation composition, T2 lockstep collapse, composed representation and normalized projection agreement, the canonical WAL-to-Broker witness, and T1 safety for the target and every mapped prefix |
| Verus T4-C1 context observation and plugging | 720 obligations verified transitively with no admitted proof bodies: the T4-C0 closure plus 44 obligations for ordered normalized observations, exact append-I/O recovery, masked endpoint views, T2/T3 whole-history compatibility, three structural plugged products, erasure, hidden stuttering, prefix closure, and shared zero-step and visible-`Crash` witnesses |
| Verus T4-C2 contextual replacement and composition | 734 obligations verified transitively with no admitted proof bodies: the T4-C1 closure plus 14 obligations for T3-selected context compression, canonical plugged Journal/Broker construction, transferred context acceptance, exact mapped context-state and ordered endpoint-view equality, and the exported storage-parametric forward replacement theorem |
| Verus T5-S0 exact one-step committed history | 743 obligations verified transitively with no admitted proof bodies: the T4-C2 closure plus 9 obligations for exact Broker/Journal/WAL commit deltas, prefix monotonicity, and exact WAL parsed-view behavior under the runtime `wal_invariant` |
| Verus T5-E0 execution-interval monotonicity | 747 obligations verified transitively with no admitted proof bodies: the T5-S0 closure plus 4 obligations for generic prefix transitivity and Broker/Journal/WAL interval induction; the WAL export requires only `Exec` |
| Verus T5-R0 recovery-episode equality | 769 obligations verified transitively with no admitted proof bodies: the T5-E0 closure plus 22 obligations for recovery completeness/nonvacuity, generic repair and sequence facts, three-backend mode confinement, non-Online and per-episode step stuttering, prefix invariants, and endpoint equality; at this checkpoint 34 registered targets contained 806 non-duplicated obligations |
| Verus T5-C0 contextual mapped recovery | 783 obligations verified transitively with no admitted proof bodies: the T5-R0 closure plus 13 delta-translation, weak-step, representation, mapped-prefix, recovery-endpoint, canonical, contextual, and paper-export obligations, plus 1 combined inert-context nonvacuity witness |
| Verus H1 artifact nonvacuity | 786 obligations verified transitively with no admitted proof bodies: the historical T5-C0 closure plus 3 obligations for a concrete total `FullConfig`, an unconditional concrete T5-C0 premise/conclusion package, and the existential cumulative-artifact inhabitance theorem |
| Byte decoding and checksum correctness | Not yet modeled |
| Actual flush/fsync and filesystem contract | Assumed below the typed WAL |
| Parameterized proof | The current 36 registered Verus targets verify 823 dependency-aware non-duplicated obligations; the historical T5-C0 checkpoint was 783 cumulative obligations across 35 targets and 820 non-duplicated obligations; T1--T5 and H1 are complete, while T6-S0 remains open |

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
artifact boundary. Adapter effect refinement and end-to-end T6 remain open;
T6-S0 is next.
