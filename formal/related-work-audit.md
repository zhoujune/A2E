# Related-work and novelty audit

Status: retained submission checkpoint

Search cutoff: 2026-08-10

This audit tests the novelty proposition in the
[FSE 2027 submission contract](fse-2027-submission-contract.md). It is a
targeted claim audit, not a systematic literature review. It searches for the
closest work across AI-agent enforcement, capabilities, durable workflows,
exactly-once RPC and deduplication, dual-write recovery, crash-consistent
storage, and verified distributed systems. Bibliographic metadata is retained
in [`related-work.bib`](related-work.bib).

## 1. Executive verdict

The broad claim that ProveAI is the first work to connect authorization and
durable effects for AI agents is not defensible. *Proof of Execution* (PoE)
already binds authorization, an enforced path, durable effects, a tamper-
evident history, and replay context into an AI-agent execution object. The
broad claim that ProveAI is the first machine-checked treatment of ambiguous
retry or deduplication is also not defensible. *Machine-Checked Dual-Write
Recovery from a Committed Log* gives an Isabelle/HOL account of post-crash
ambiguity, sink acceptance, fencing, deduplication, and evidence lifetime.

The surviving contribution is narrower and more technically specific:

> Based on the sources checked through 2026-08-10, we are not aware of prior
> work that machine-checks a coverage-conditioned compositional refinement for
> a serialized AI tool-effect broker from durable capability authorization and
> complete mediation for protected Idempotent and Deduplicated instances,
> through fail-stop crash/recovery, to an abstract adapter layer that explicitly
> distinguishes ReadOnly, Idempotent, Deduplicated, and Uncontrolled effects,
> including `Unknown` for irreducible ambiguity. The ReadOnly operational
> instance is proved only through its adapter/WAL/Broker refinement boundary.

This is a qualified synthesis claim, not an absolute priority claim. The paper
should lead with the exact verified composition and its boundary, not with
"first formal verification," "exactly once," or a generic novelty claim about
capabilities, logging, durable workflows, or idempotency keys.

## 2. Comparison axes

The comparison uses the following semantic axes.

- **Authorization**: policy or capability enforcement is tied to an action.
- **Durable ancestry**: durable evidence orders authorization before the
  physical attempt and terminal effect.
- **Crash/retry semantics**: failure windows and recovery choices are explicit.
- **Effect contract**: retry observations refine stated external abstract
  effects rather than only an internal completion record.
- **Complete mediation**: the modeled protected effect cannot bypass the
  enforcement path.
- **Machine checked**: the relevant theorem is checked by a proof assistant or
  model checker, not only argued on paper.
- **Executable evidence**: an implementation or evaluation exercises the
  claimed mechanism.

"Partial" means that a work covers a narrower object or makes the property a
deployment assumption rather than proving the ProveAI relation.

| Work | Authorization | Durable ancestry | Crash/retry | Effect contract | Complete mediation | Machine checked | Executable evidence |
|---|---|---|---|---|---|---|---|
| ProveAI | yes | yes | yes | four adapter classes | formal closed interface | TLA+/Verus | reference broker |
| PoE | contract and Gateway | completed trace | no crash-recovery protocol | deny/effect trace, not retry classes | credentialing assumption/lemma | no proof-assistant artifact found | TypeScript prototype |
| CaMeL | capabilities and data-flow policy | no | no | no | interpreter/tool-call boundary | analytical security argument | implementation and AgentDojo evaluation |
| Guardians of the Agents | pre-execution workflow policy | no | no | no | proposed verified-plan boundary | proposed static tools, not an end-to-end mechanization | design and later prototype work |
| Capsicum / seL4 | capability confinement | no | no external retry protocol | no | OS/kernel boundary | seL4 yes; Capsicum no | production OS mechanisms |
| Temporal / RSMs | application-defined | workflow history | workflow/task recovery | activities rely on idempotence | orchestration boundary only | no end-to-end proof of external effects | production/runtime systems |
| RIFL / idempotency-key APIs | no | completion or key record | yes | one deduplication contract | no | no | deployed mechanisms |
| Beldi | no | intent/log records | yes | exactly-once stateful function operations | runtime-managed operations | no machine-checked end-to-end proof | OSDI implementation |
| Dual-Write Recovery | no | source and sink records | yes | accepted-record, fence, and dedup semantics | no authorization monitor | Isabelle/HOL | theory artifact, no verified broker |
| FSCQ / Argosy | no | storage-level recovery state | yes | no external tool effect | storage boundary | Coq | verified storage artifacts |
| Disel / IronFleet | protocol-specific | protocol state | distributed failure semantics | protocol-specific | protocol boundary | Coq / Dafny | verified distributed systems |

## 3. Closest overlaps

### 3.1 Proof of Execution

[Rhodes and Kang, *Proof of Execution: Runtime Verification for Governed AI
Agent Actions*](https://arxiv.org/abs/2607.05397) is the closest work on the
AI-agent authorization side. PoE defines a contract, an Execution Causal Event
Stream, and replay context. Its validator checks authorization, path
compliance, deny-side null effect, history integrity, and replayability. Its
Prime Execution Model separates planning, enforcement, effect, and recording,
and its soundness theorem names both cryptographic and deployment-failure
assumptions.

This overlap rules out claiming novelty for putting an authorization monitor
below an LLM, associating a durable effect with an authorization decision, or
recording an auditable agent trajectory. The technical difference is that PoE
validates and attests a completed causal trace. It does not define a durable
crash/retry broker protocol, a WAL-to-broker recovery refinement, the four
adapter classes, or an `Unknown` outcome for an ambiguous physical call. The
paper does not report a proof-assistant or model-checking artifact.

PoE and ProveAI are complementary: PoE is stronger on cryptographic trace
attestation and replay context, while ProveAI is stronger on machine-checked
crash/recovery transition semantics and adapter-specific external effects.

### 3.2 Machine-checked dual-write recovery

[Andreakis, *Machine-Checked Dual-Write Recovery from a Committed
Log*](https://arxiv.org/abs/2608.00501) is the closest work on ambiguous
external effects. Its Isabelle/HOL theory proves that source-local durable
state cannot distinguish whether a sink accepted an effect after a send-before-
checkpoint crash. It then proves conditional escapes using the sink's accepted
record, arrival and claim fences, and persistent deduplication evidence. It
also proves that bounded deduplication memory and truncated source history can
void the guarantee.

This overlap rules out claiming novelty for the ambiguity observation, for
deduplication as the general answer to ambiguous retry, or for a machine-
checked crash/retry boundary by itself. ProveAI adds a different composition:
durable capability ancestry, a broker protocol and terminal classification,
complete mediation in a closed formal interface, four adapter classes, and
contextual refinement through Journal and typed-WAL layers. The dual-write
theory does not model authorization, an AI agent, or a verified broker
implementation; ProveAI does not prove its more general information bounds,
fence disciplines, concurrency results, or finite-retention theorems.

The retention result exposes a ProveAI assumption that must be stated: the
Deduplicated contract requires the service-owned memo to survive every retry
that the broker may issue. The current DD model has no memo-expiry transition.
Likewise, the typed theorem assumes the histories needed for recovery and
authorization ancestry remain available inside the admitted execution.

### 3.3 AI-agent policy enforcement

[CaMeL](https://arxiv.org/abs/2503.18813) separates trusted control flow from
untrusted data and uses capabilities at tool calls to prevent unauthorized data
flows. It reports provable security on 77% of AgentDojo tasks. [Guardians of the
Agents](https://queue.acm.org/detail.cfm?id=3762990) proposes generating a
structured workflow and statically verifying its safety before any tool runs,
using information-flow analysis, pre/postconditions, or automated solvers.

These works rule out "first verified policy layer for AI tools" and "first use
of capabilities for agent tool security." Their focus is prompt-injection and
plan/data-flow safety. They do not address fail-stop recovery, durable attempt
ancestry, ambiguous physical outcomes, or adapter-specific retry refinement.

### 3.4 Durable workflows and exactly-once runtimes

[Temporal](https://docs.temporal.io/workflow-execution) provides durable,
recoverable workflow execution by replaying an event history. Its own
[Activity documentation](https://docs.temporal.io/activity-execution) states
that an Activity may be lost after its function was called and then retried;
Temporal guidance therefore requires Activities to be idempotent.
[Reliable State Machines](https://doi.org/10.4230/LIPIcs.ECOOP.2019.18) offers
fault tolerance by construction for cloud services.
[Beldi](https://arxiv.org/abs/2010.06706) uses logging, intent tables, and
runtime protocols for fault-tolerant and transactional stateful serverless
workflows. [RIFL](https://doi.org/10.1145/2815400.2815416) converts at-least-once
RPC into linearizable exactly-once operations using unique RPC identifiers and
completion records.

These systems establish that durable replay, exactly-once function execution,
and retry idempotence are mature mechanisms. ProveAI must compare semantic
boundaries rather than imply they are missing. Its remaining distinction is
the machine-checked link from a durable capability decision and physical
mediation to an explicit external adapter law and broker terminal outcome.

The IETF [Idempotency-Key draft](https://datatracker.ietf.org/doc/draft-ietf-httpapi-idempotency-key-header/)
describes a request header for making POST/PATCH fault tolerant, but the latest
document is expired and archived, so it must not be described as an RFC or
completed standard. [Stripe's deployed API contract](https://docs.stripe.com/api/idempotent_requests)
also makes the retention boundary concrete: keys may be removed once they are
at least 24 hours old.

### 3.5 Capabilities and verified systems

[Capsicum](https://www.usenix.org/conference/usenixsecurity10/capsicum-practical-capabilities-unix)
provides practical capability confinement for UNIX applications.
[seL4](https://doi.org/10.1145/1629575.1629596) supplies a machine-checked
refinement from an abstract kernel specification to C and later security
properties. These are stronger implementation and isolation precedents than
ProveAI's model-only closed interface, but they do not connect a durable
authorization record to crash/retry tool effects.

[FSCQ](https://doi.org/10.1145/2815400.2815402) and
[Argosy](https://doi.org/10.1145/3314221.3314585) establish machine-checked
crash safety and recovery refinement for storage systems. Disel and IronFleet
establish machine-checked distributed-protocol and implementation precedents.
ProveAI therefore must not claim novelty for recovery refinement, weak
simulation, or machine-checked systems proof in isolation. Its contribution is
the domain-specific composition and terminal/effect contract.

## 4. Claim decisions

The paper must reject these formulations:

- "the first formal verification of AI-agent workflows";
- "the first durable authorization layer for agent actions";
- "the first verified treatment of crash ambiguity or exactly-once retry";
- "the first use of capabilities, WALs, idempotency keys, or deduplication for
  agent tools"; and
- any claim that ProveAI verifies a production runtime, filesystem, network, or
  remote service.

The paper may defend these contribution statements, with the existing scope
qualifiers:

1. A machine-checked broker semantics that puts authorization, attempt intent,
   delivery evidence, terminal outcomes, and abstract effects in one crash-
   aware transition system.
2. A compositional refinement chain from Broker through Journal, typed WAL,
   contextual replacement, and independently defined protected-service
   executions.
3. Explicit adapter-class theorems that distinguish ReadOnly, Idempotent,
   Deduplicated, and Uncontrolled effects rather than advertising generic
   exactly-once execution.
4. Non-vacuous crash/retry witnesses and an executable reference artifact that
   expose `Unknown` as the correct outcome when the external effect cannot be
   resolved safely.

## 5. Paper comparison structure

The related-work section should be organized around boundaries, not a catalog
of products:

1. **Agent authorization and information flow:** CaMeL, Guardians, and PoE.
2. **Durable orchestration and exactly-once mechanisms:** Temporal, RSMs,
   Beldi, RIFL, HTTP/Stripe idempotency contracts, and transactional outbox.
3. **Machine-checked crash and distributed systems:** Dual-Write Recovery,
   FSCQ, Argosy, Disel, IronFleet, and seL4.
4. **ProveAI's remaining composition:** durable capability ancestry plus
   crash/recovery mediation plus adapter-specific external effects.

Every comparison should say what event is counted, what evidence survives a
crash, what component owns deduplication, what bypass assumption is made, and
whether the result is machine checked.

## 6. Search record and limitations

The audit used targeted web and primary-source searches for combinations of:

- AI agent, tool authorization, capability, formal verification, durable
  execution, proof of execution;
- exactly-once RPC, idempotency key, deduplication, retry, crash recovery,
  intent log, transactional outbox;
- machine-checked dual-write recovery, accepted record, fencing;
- capability system, reference monitor, seL4, Capsicum; and
- crash Hoare logic, recovery refinement, verified distributed systems.

Primary arXiv, ACM, USENIX, Dagstuhl, IETF, and vendor documentation pages were
preferred over secondary summaries. The closest 2026 papers were inspected in
full-text HTML where available. This audit does not establish universal
absence. It must be refreshed before the submission freeze, especially for
2026-2027 work on governed agent execution and durable agent runtimes.
