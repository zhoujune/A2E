# Research Contract and Threat Model

## 1. Research claim

The Verified Agent Effect Broker is a reference monitor between an untrusted
agent and effectful tools. The first paper will establish the following claim:

> For every broker execution containing arbitrary agent requests, capability
> revocation, tool responses, retries, and fail-stop crashes, every physical
> invocation has a unique prior valid authorization; every committed logical
> effect appears at most once per broker-generated internal request identifier
> in a crash-stable abstract history; and retry behavior satisfies the declared
> adapter contract.

This is a claim about mediation of effects. It is not a claim that the agent's
plan, the external tool, or the resulting real-world effect is semantically
desirable.

## 2. System boundary

The target verified boundary comprises:

1. admission of an immutable typed request;
2. capability validation and budget consumption;
3. durable operation-state and attempt-reservation transitions;
4. adapter selection and physical invocation control;
5. correlated response delivery, durable outcome persistence, and logical
   terminalization;
6. gated crash recovery and retry decisions.

The agent can interact with tools only through this boundary. Tool credentials,
file handles, process handles, and network clients are not made available to
the agent runtime.

## 3. Protected assets

The broker protects:

- **authority**: which principal may perform which operation on which resource
  with which arguments;
- **capability budget**: how many requests may consume a capability;
- **effect integrity**: the association between request, authorization,
  durable attempt reservation, physical invocation, correlated delivery,
  persisted observation, and logical outcome;
- **result integrity**: a committed payload originates in a validated tool
  observation and is not fabricated or altered by the broker;
- **durable history**: the order and per-internal-request uniqueness of
  commit-log entries;
- **retry discipline**: whether a physical tool operation may be repeated;
- **audit provenance**: the durable evidence connecting a logical effect to
  its authorization decision.

Availability and confidentiality are important but are not primary theorem
targets for the first prototype.

## 4. Adversary model

### 4.1 Agent adversary

The agent may submit any byte sequence accepted by the unverified front end and
any well-typed internal request produced after decoding. It may:

- choose arbitrary tools, operations, resources, and arguments;
- reuse request payloads and capability references;
- submit requests that exceed capability scope or budget;
- exploit confused-deputy opportunities;
- issue requests in any order and abandon pending requests;
- observe all results intentionally returned to it.

The agent cannot directly forge the broker's internal capability identity,
mutate an admitted request, access broker memory, or bypass the broker to use
tool credentials. These are enforcement and deployment assumptions that must
be validated in the implementation architecture.

### 4.2 Tool and adapter environment

An external tool may return success, failure, malformed data, time out, or
produce an ambiguous outcome. It may be unavailable indefinitely. The initial
model does not assume that an uncontrolled tool is honest or idempotent.

An adapter declaration supplies a retry contract. Until an adapter refinement
proof is completed, that declaration is trusted. A later proof must show that
the concrete protocol implements its declared abstract relation.

### 4.3 Crash adversary

A fail-stop crash may occur between any two broker transitions, including
between reservation and send, delivery and outcome persistence, or two
recovery steps. A crash erases volatile `ready`, `inflight`, `received`, and
observed state, resets recovery control, and stops execution. Acknowledged
durable records remain intact and ordered. Arbitrary storage corruption,
rollback to an older durable image, and Byzantine hardware are excluded from
the first model.

The typed WAL additionally permits recovery scanning to be aborted and
restarted before or after Torn-tail removal while the Broker remains crashed.
The tail-removal transition itself is atomic in this layer. Partial filesystem
truncation, byte corruption, and reorderings below the Full/Torn-frame contract
remain outside the modeled crash adversary.

### 4.4 Concurrency adversary

The bounded Broker oracle interleaves operations atomically and represents
volatile execution state per request, so multiple requests may be live even
though every transition is atomic. Theorem V1 deliberately narrows the verified
implementation core to one globally serialized WAL writer and one globally
serialized executor slot. Neither level models data races or cancellation
races inside a transition. A later concurrent extension must add ownership and
linearizability arguments. V1 assumes exclusive ownership of the broker's
physical tool handles.

## 5. Capability contract

A request `r` is within capability `k` only when all of the following hold at
the authorization linearization point:

1. `r` names `k` as its capability;
2. the request principal equals the capability principal;
3. the requested tool and operation equal an authorized tool and operation;
4. the capability's resource predicate accepts the requested resource;
5. the capability's argument predicate accepts the complete argument value;
6. the capability is not revoked;
7. its remaining authorization budget is positive.

Authorization atomically records an authorization witness and consumes one
unit of logical-operation authority. Physical retries do not consume this
counter. `MaxAttempts` instead bounds durable attempt reservations; physical
sends are no more numerous than those reservations. Revocation is prospective:
it blocks new authorization but does not cancel an already authorized
operation. Strong revocation requires a separate cancellation protocol and is
deferred.

Here `MaxAttempts` names the finite oracle's scenario-wide instantiation. The
theorem-V1 request record carries an immutable `max_attempts(r)`, so different
requests may have different retry budgets without changing the generic proof.

The broker allocates a fresh internal request identifier at admission. A
deduplication key is derived from the adapter namespace and this identifier.
Any client-supplied replay identifier must be bound to an immutable request
digest; reusing it with different contents is rejected before authorization.
Equal payloads admitted under two fresh internal identifiers remain two logical
requests. Semantic replay coalescing requires a durable replay-key map and is
outside the current model.

Capability identities and metadata are immutable and authenticated. The first
prototype may realize them as broker-owned values rather than cryptographic
bearer tokens.

## 6. Adapter contracts

| Class | Broker retry rule | Environment obligation | Guarantee |
|---|---|---|---|
| `ReadOnly` | May retry | Repetition has no mutating external effect | At most one committed result; no protected mutation |
| `Idempotent` | May retry | Repetition is observationally equivalent to one abstract mutation | A commit refines one abstract operation under the idempotence relation |
| `Deduplicated` | May retry with stable key | Tool atomically deduplicates the key | At most one accepted abstract mutation and terminal result per key |
| `Uncontrolled` | Never retry after arming | None | At most one physical attempt; outcome may be `Unknown` |

Physical exactly-once execution is not claimed for arbitrary APIs. An
`Uncontrolled` call that crashes after durable arming becomes `Unknown` when no
conclusive failure was already persisted. This includes a crash after
reservation but before send, or after delivery but before persistence. Durable
broker state deliberately does not consult ghost physical history to
distinguish these cases. This loss of availability is required to preserve
physical at-most-once behavior.

## 7. Trusted computing base and assumptions

| Item | Initial status | Required justification |
|---|---|---|
| Abstract transition system | Model checked in finite instances; arbitrary finite request-to-capability maps are configuration parameters | TLA+ exploration plus machine-checked T1 Broker safety and T2 atomic-Journal simulation |
| Rust broker core | To be verified | Verus functional-correctness proof |
| Adapter retry declaration | Trusted per adapter | Replaced by an adapter refinement proof |
| Abstract Journal interface | T2 proves atomic-Journal-to-Broker simulation; T4-C0 closes WAL-to-Broker composition; T4-C1 establishes structural three-backend plugging; T4-C2 proves storage-parametric finite forward contextual replacement; T5-S0 proves exact one-step committed-history laws; T5-E0 proves finite execution-interval monotonicity; T5-R0 proves exact first-Finish recovery equality; T5-C0 exports the equality through the canonical contextual map and completes T5; H1 proves the cumulative package inhabited under a concrete total configuration | T6-S0 terminal evidence/compatibility and subsequent adapter/effect refinement remain |
| WAL model and implementation | Bounded typed-frame refinement with interruptible scan checked; implementation unverified | Extend `WAL -> Journal` to byte decoding, checksums, partial truncation, flush/fsync, atomic-write, and filesystem assumptions |
| Rust compiler and Verus toolchain | Trusted; the Verus and rustup archives are hash pinned, while the exact Rust version is freshly installed from the official rustup service and recorded by tree hash | Document versions and soundness assumptions; retain source-hashed verification reports |
| Verification evidence pipeline | Verus runs on an exact source snapshot and reports schema/source/runner/lock/tool hashes and counts; TLC runs from isolated model/tool snapshots and reports them by hash | Preserve complete source/import and configuration-manifest coverage; reports do not remove trust in Verus, TLC, Rust distribution services, Java, PowerShell, or SHA-256 implementations |
| OS, filesystem, hardware | Trusted below persistence contract | State exact flush and atomic-write assumptions |
| Serialization/front end | Untrusted input boundary | Validate before constructing an admitted request |
| TLS and remote service | Environment | State authenticity and retry assumptions per adapter |
| Agent model and prompt | Untrusted | No correctness assumption |

The paper must distinguish proof assumptions from engineering protections. For
example, process isolation can help enforce that the agent cannot bypass the
broker, but it is not automatically part of the Verus theorem.

The Broker model already separates `ReserveAttempt` from `SendAttempt` and each
physical `Deliver*` from its durable `Persist*` action. `externalHistory`
records physical sends and accepted deliveries. In `attemptLog`, durable
`Started` records cover physical sends, while durable outcome records are a
history-backed subset of physical deliveries. The remaining persistence
assumptions concern atomic Journal operations. The proof chain is
`WAL -> Journal -> EffectBroker`. The bounded WAL model checks the first arrow
over symbolic Full/Torn frames; completed Full frames advance Journal and other
WAL actions stutter. The coupled Journal/Broker model checks the second arrow:
every append is paired with the corresponding broker action, which supplies
physical-delivery witnesses, volatile tokens, and deduplicated-adapter rely
conditions. Journal replay may retain extra successful-value data, but the
mapping erases it and still requires a live observation before Commit, so it
cannot create a post-crash abstract completion. T1 proves parameterized Broker
safety, T2 proves the independent atomic-Journal runtime simulation, and T3
proves the typed-WAL-to-Journal weak simulation. T4-C0 now composes those two
closed runtime simulations, constructs a direct WAL-to-Broker weak simulation,
and derives T1 safety for the resulting Broker execution and every mapped
prefix. The completed
[T4-C1 checkpoint](mechanization-contract.md#t4-c1-context-observation-and-plugging-foundation)
now fixes the storage-parametric observation boundary and structural plugged
WAL, Journal, and Broker executions. It proves erasure, prefix closure, hidden
view/state stuttering, an accepting inert context, shared zero-step witnesses,
and a positive shared one-`Crash` witness. The completed
[T4-C2 contextual lift](mechanization-contract.md#t4-c2-contextual-replacement-and-composition)
now replaces the checked finite product with canonical finite forward
contextual replacement. It compresses context states exactly for WAL events
whose T3 translation is `Some`, not according to context-delta visibility,
constructs the canonical plugged Broker execution, proves exact context-state
and ordered endpoint `ContextView`
equality at every canonical mapped prefix, and inherits C0
simulation/projection/T1 and mapped-prefix T1 conclusions. Its exported theorem
retains `StorageParametricContext` as an explicit premise. T5-S0 now defines the
Broker abstraction as its durable `commit_log` and the Journal/WAL abstractions
as `Replay(JournalView).commit_log`, with WAL `JournalView=Parse(media)`. It
proves that only the backend's durable `CommitRec` linearization appends one
exact entry; every other accepted step stutters. Its WAL theorem assumes the
runtime `wal_invariant`, excluding ghost-evidence agreement, and includes Torn
stuttering and truncation equality. Reachable states derive that premise from
T3-W0's `basic_invariant`. T5-E0 lifts these laws to every pair
`i <= j < configs.len()` in a finite Broker, Journal, or WAL execution. Its WAL
export exposes only `Exec`; reachability discharges `wal_invariant`
internally. T5-R0 then selects a `Crash` and the first later `FinishRecover`,
derives recovery-repair classification and zero commit delta for every episode
step, and proves exact pre-Crash/post-Finish committed-history equality. Its WAL
theorem also discharges invariants internally. Minimal Broker, Journal, and WAL
episodes plus a repeated-`Crash` Broker episode establish nonvacuity. The T5-R0
target verifies 769 obligations, 22 beyond T5-E0; all 34 registered targets
contain 806 dependency-aware non-duplicated obligations. T5-C0 now proves that,
under `CfgWellFormed`, `StorageParametricContext`, `PluggedWalExec`, and a source WAL
`RecoveryEpisode(events,crash,finish)`, the canonical T4 Broker execution has
the same `alpha_commit` at every mapped prefix and in particular at
configurations `mu[crash]` and `mu[finish + 1]`. It retains the complete T4-C2
contextual replacement conclusion. Its target verifies 783 obligations, 14
beyond R0: 13 bridge/export obligations and one combined inert-context
nonvacuity obligation. At that historical checkpoint, 35 registered targets
contained 820 dependency-aware non-duplicated obligations. H1 then constructs a
total `FullConfig`: every request is uncontrolled with no stable key and one
attempt, every capability has unit budget and universal resource/argument
scope, and every request/result pair is valid. It proves this configuration
well formed and, without premises, instantiates the inert context and minimal
six-event recovery execution at `crash = 0`, `finish = 5`, so that the complete
T5-C0 premise conjunction and conclusion hold together. H1 adds 3 obligations,
for 786 cumulative obligations; the current 36 registered targets contain 823
dependency-aware non-duplicated obligations. T5 and H1 are complete, and T6-S0
is next.
This is mapped configuration-prefix equality, not a transported target Broker
`RecoveryEpisode`; it uses `mu[finish + 1]`, not `mu[finish]`, and proves no
liveness, full-state equality, external-effect refinement, or byte-level
WAL/filesystem correctness. H1 is only an inhabitance result: its minimal
witness does not demonstrate a nonempty pre-crash commit history or a real
adapter effect. The
product checks `BrokerDurable = Replay(Parse(media))`, synchronized WAL/Broker
crash control, Broker-stuttering scan/truncation/abort phases, recovery-only
terminal staging, WAL-quiescence-gated response acceptance, and acknowledged
Start records for every physical Invoke. A transport may return a response
while the WAL is busy; `Deliver*` models only its correlated acceptance into
Broker volatile state, so the executor must buffer it or conservatively leave
the attempt unresolved. Byte decoding, checksums, partial filesystem
truncation, and concrete filesystem/fsync behavior remain outside the
typed-frame model.

Theorem V1 separates an append operation's caller-visible Call and Return from
its durability linearization. AtomicJournal may delay Return after atomic
linearization; WAL linearizes at `WriteFull`/`FinishTorn` and returns at
`FlushAck`. The contextual boundary is an ordered trace of Call/Return,
Invoke/Deliver, and control observations, together with a masked executor view.
While an append is pending, that view exposes only `(mode,record)` and merges
the Called and Linearized phases; the updated slot becomes visible only after a
Return or another visible control transition. Contexts cannot inspect the
private linearization point, WAL frames, Torn contents, scan state, or ghosts.
This covers a crash after durable write but before acknowledgment without
granting the context a representation-dependent branch.

The T4-C1 context is event synchronized. For each visible machine step, its
relation receives the current context state, both masked endpoint
`ContextView`s, and the nonempty normalized delta. The post-step view is also the
view of the next execution prefix, so the context may react to a return-updated
slot without learning the hidden linearization point. Hidden events preserve
both the complete view and context state. The V1 threat model excludes
autonomous context-only transitions and a separate observation transition after
the machine execution terminates. Extending the theorem to those behaviors
requires a stronger context interface rather than an implicit assumption.
T4-C2 is forward replacement only; it does not prove reverse contextual
equivalence, liveness, protected-handle exclusivity, adapter-specific effect
refinement, or byte-level WAL/filesystem correctness.

The equalities and shadows in the coupled TLA+ products are finite
model-checking instrumentation. The theorem-V1 concrete runtime contains no
Broker durable shadow. The [mechanization contract](mechanization-contract.md)
defines independent abstract Broker, atomic-Journal runtime, and typed-WAL
runtime states. `Representation` and T2 now provide the atomic runtime's proved
relation to the Broker; T3 provides the WAL simulation, and T4-C0 composes the
closed WAL, Journal, and Broker executions. T4-C1 now supplies the common
observation and structural plugging semantics. T4-C2 constructs the canonical
plugged Broker execution and proves exact equality of both shared context state
and ordered endpoint `ContextView` at canonical mapped prefixes.
`MaxJournalLength` is likewise only
a TLC exploration bound. V1 has no silent capacity semantics: a bounded
implementation must expose `DiskFull` before staging and leave logical and
adapter projections unchanged. The oracle's global `MaxAttempts` is similarly
only an instantiation of theorem V1's per-request `max_attempts(r)`.

## 8. Security and correctness properties

The first paper targets the following properties:

- **complete mediation obligation**: deployment isolation and broker-exclusive
  tool handles ensure that no physical invocation bypasses the broker. The
  TLA+ model assumes this boundary by construction;
- **authorization soundness**: invocation implies a matching, historically
  valid authorization witness;
- **budget conservation**: consumed plus remaining authority equals initial
  authority;
- **scope confinement**: a request violating resource or argument scope never
  becomes authorized;
- **unique logical completion**: each internal request identifier occurs at
  most once in the commit history;
- **crash-prefix consistency**: crash and recovery preserve the committed
  abstract history. T5-S0 proves the exact local stuttering laws and T5-E0
  proves finite execution-interval monotonicity; T5-R0 proves exact equality
  through the first `FinishRecover`, and T5-C0 exports that equality to the
  canonical Broker configurations at `mu[crash]` and `mu[finish + 1]`;
- **retry safety**: physical repetitions are permitted only under a retry-safe
  adapter contract;
- **external-trace causality**: every accepted tool outcome carries an attempt
  identifier and follows the unique earlier broker invocation for the same
  request and attempt; stale responses are ignored, and every durable outcome
  record is backed by such a delivery even though a delivery may be lost before
  persistence;
- **value provenance**: every committed successful payload is causally linked
  to the exact validated successful observation copied into the terminal
  record;
- **audit soundness**: each commit is linked to one authorization record.

The mechanized T1 theorem establishes the Broker-internal safety obligations in
this list over the global event trace: authorization and budget safety, scope
confinement, retry bounds, physical/Journal causality, terminal uniqueness,
value provenance, and crash/recovery structure. Complete mediation remains a
deployment premise, and interpreting invocation histories as adapter effects is
deferred to T6.

Conditional liveness may be added later under scheduler-fairness, durable-I/O,
and responsive-tool assumptions. It must not be inferred from the safety
theorems.

The finite TLA+ oracle uses a shared `AllowedResults` set. Theorem V1 instead
uses `result_pred(r,v)` and proves value provenance per request. Its adapter
conclusion is also per request; it does not impose a global linearization order
on effects from different requests, and `ReturnResult` is outside the machine.

## 9. Explicit non-goals

The first prototype does not prove:

- correctness, alignment, or usefulness of the agent's plan;
- correctness of arbitrary external tools;
- physical exactly-once behavior for uncontrolled tools;
- termination when a tool or storage system stops responding;
- confidentiality or noninterference of secrets;
- Byzantine-fault tolerance, durable rollback protection, or storage
  corruption recovery;
- correctness of the full MCP, HTTP, TLS, operating-system, or Rust ecosystem;
- immediate revocation of an operation that was already authorized;
- distributed replication of the broker.

These exclusions keep the main theorem falsifiable and the trusted boundary
auditable.

## 10. Failure semantics

| Situation | Broker outcome |
|---|---|
| Scope, budget, or revocation check fails | Request remains unauthorized; no invocation |
| Tool returns a definitive success | Broker may durably commit one logical result |
| Tool returns a conclusive definitive failure | Broker may durably record failure |
| Tool response is delivered but crash occurs before `Persist*` | Physical delivery remains ghost evidence; durable state treats the attempt as unresolved |
| Idempotent failure follows an unresolved, successful, ambiguous, or invalid-result attempt | Broker may retry/reconcile if attempts remain, or records `Unknown`; never clean failure |
| Retry-safe tool is ambiguous | Request remains armed and may retry |
| Uncontrolled tool is ambiguous | Request becomes `Unknown` and cannot retry |
| Crash before `Armed` | Recovery may resume preparation |
| Crash after `Armed`, retry-safe adapter | Gated recovery repairs a conclusive durable failure; otherwise normal execution may later retry under the class contract and attempt budget |
| Crash after `Armed`, uncontrolled adapter | Gated recovery records `Unknown` unless it must repair a conclusive durable failure |
| Crash after logical commit | Recovery preserves the committed result |

An invocation with no observed outcome is never interpreted as a definitive
no-effect failure. It remains effect-uncertain until a class-specific
deduplication or reconciliation result resolves it.

If a conclusive `Failure` was already appended to the durable attempt log
before a crash, `RecoverRecordedFailure` records `Failed` without retry,
including for an uncontrolled adapter. `FinishRecover` is disabled until all
such failures are repaired and all unsafe uncontrolled requests are
quarantined. The `Unknown` row applies when no conclusive durable terminal
knowledge exists. Recovery may itself crash and restart without changing the
committed abstract history.

## 11. Proof-obligation map

| Threat or failure | Preventing mechanism | Formal obligation |
|---|---|---|
| Forged or over-scoped request | Immutable request plus capability monitor | `Matching` and authorization soundness |
| Budget reuse | Atomic authorization and consumption | `CapabilityBudget` and `AuthLogSound` |
| Invocation without authority | Broker-exclusive tool handles | Complete mediation and `InvocationsAuthorized` |
| Duplicate logical outcome | Durable phase machine | `UniqueLogicalCompletion` and `CommitLogSound` |
| Unsafe retry after ambiguity | Adapter retry class | `UncontrolledAtMostOnce` and adapter refinement |
| Send or delivery crosses a crash boundary | Separate reserve/send/deliver/persist stages | `AttemptLogBackedByHistory`, durable uncertainty, and gated recovery |
| Lost or invented commit after crash | Durable commit log and recovery | Recovery preservation of the abstraction function |
| Confused deputy | Principal, resource, and argument scope | Scope-confinement theorem |
| Concurrent duplicate execution | Affine operation token | Later linearizability and ownership proof |
| Outcome attached to the wrong retry | Stable attempt identifier | `AttemptLogWellFormed` and exact attempt provenance |
| Conflicting request-ID replay | Broker allocation or request-digest binding | Admission invariant and stable-key proof |

## 12. Paper acceptance criteria

The research contract is satisfied only when the artifact provides:

1. a mechanically checked abstract safety model;
2. an executable Rust broker refining that model;
3. a parameterized `Journal -> EffectBroker` proof, a concrete
   `WAL -> Journal` refinement, and their mechanized contextual composition;
4. verified adapters representing at least three retry classes;
5. systematic fault injection at persistence and invocation boundaries;
6. a precise accounting of trusted code and assumptions;
7. measurements of verification effort and runtime overhead.

T4-C0 supplies the closed-machine composition portion of item 3 and derives T1
safety for the composed Broker execution. T4-C1 supplies the machine-checked
observation boundary and structural WAL/Journal/Broker plugging semantics,
including erasure, prefix closure, and nonvacuity witnesses. T4-C2 completes
item 3 by constructing the canonical target plugged execution and proving
replacement for every admitted storage-parametric context. T5-S0 now proves
the exact one-step committed-history foundation, and T5-E0 proves finite
execution-interval monotonicity. T5-R0 now proves exact equality from `Crash`
through the first `FinishRecover`, including a mechanically inhabited repeated-
Crash episode. T5-C0 completes the mapped T4 bridge/export, including the
combined inert-context recovery witness, and closes theorem T5. T6 is the next
semantic layer; T6-S0, `TerminalEvidenceAndCompatibility`, is its next theorem
checkpoint. H1 additionally supplies a concrete total
configuration/package witness and hardened evidence capture: the Verus runner
checks an exact read-only source snapshot around every target and records its
schema, sources, runner, lock, and fresh Rust tree by hash; the TLC runner
rejects malformed, duplicate, missing, or unregistered manifest configurations
and executes from exact per-run model and tool snapshots. These controls
establish artifact provenance, not external semantics.

The parameterized proof is organized as
[T1 Broker safety](mechanization-contract.md#t1-parameterized-broker-safety),
[T2 atomic-Journal simulation](mechanization-contract.md#t2-atomic-journal-runtime-simulation),
[T3 typed-WAL simulation](mechanization-contract.md#t3-typed-wal-simulation),
[T4-C0 closed composition](mechanization-contract.md#t4-c0-closed-wal-to-broker-composition),
[T4-C1 context observation and plugging](mechanization-contract.md#t4-c1-context-observation-and-plugging-foundation),
[T4-C2 contextual composition](mechanization-contract.md#t4-c2-contextual-replacement-and-composition),
[T5 recovery preservation](mechanization-contract.md#t5-recovery-and-committed-history-prefix-preservation),
and [T6 conditional end-to-end refinement](mechanization-contract.md#t6-conditional-end-to-end-theorem).
