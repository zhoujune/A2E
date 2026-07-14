use vstd::prelude::*;

verus! {

// R1 covers the typed Journal and total replay only. Broker execution,
// append protocols, physical invocation, recovery, and WAL refinement are later layers.

pub type AttemptId = nat;
pub type Lsn = nat;

#[derive(PartialEq, Eq)]
pub struct RequestId {
    pub id: nat,
}

#[derive(PartialEq, Eq)]
pub struct CapabilityId {
    pub id: nat,
}

#[derive(PartialEq, Eq)]
pub struct Digest {
    pub id: nat,
}

#[derive(PartialEq, Eq)]
pub struct StableKey {
    pub id: nat,
}

#[derive(PartialEq, Eq)]
pub struct AdapterNamespace {
    pub id: nat,
}

#[derive(PartialEq, Eq)]
pub struct Value {
    pub id: nat,
}

#[derive(PartialEq, Eq)]
pub struct InvalidValue {
    pub id: nat,
}

#[derive(PartialEq, Eq)]
pub enum RetryClass {
    ReadOnly,
    Idempotent,
    Deduplicated,
    Uncontrolled,
}

#[derive(PartialEq, Eq)]
pub enum Phase {
    New,
    Authorized,
    Prepared,
    Armed,
    Committed,
    Failed,
    Unknown,
}

#[derive(PartialEq, Eq)]
pub enum Observation {
    Success(Value),
    Failure,
    Ambiguous,
    InvalidResult(InvalidValue),
}

#[derive(PartialEq, Eq)]
pub enum UnknownReason {
    Exhausted,
    Recovery,
    NonConclusiveFailure,
    AmbiguousOutcome,
    InvalidResultReason,
}

#[allow(inconsistent_fields)]
#[derive(PartialEq, Eq)]
pub enum JournalRecord {
    Authorize {
        request: RequestId,
        capability: CapabilityId,
        digest: Digest,
    },
    Revoke {
        capability: CapabilityId,
    },
    Prepare {
        request: RequestId,
        class: RetryClass,
        digest: Digest,
        key: Option<StableKey>,
        auth_ref: Lsn,
    },
    Arm {
        request: RequestId,
        digest: Digest,
        key: Option<StableKey>,
        prepare_ref: Lsn,
    },
    Start {
        request: RequestId,
        attempt: AttemptId,
        digest: Digest,
        key: Option<StableKey>,
        arm_ref: Lsn,
    },
    Outcome {
        request: RequestId,
        attempt: AttemptId,
        observation: Observation,
        digest: Digest,
        key: Option<StableKey>,
        start_ref: Lsn,
    },
    CommitRec {
        request: RequestId,
        attempt: AttemptId,
        value: Value,
        digest: Digest,
        key: Option<StableKey>,
        outcome_ref: Lsn,
    },
    FailRec {
        request: RequestId,
        attempt: AttemptId,
        digest: Digest,
        key: Option<StableKey>,
        outcome_ref: Lsn,
    },
    UnknownRec {
        request: RequestId,
        attempt: Option<AttemptId>,
        reason: UnknownReason,
        digest: Digest,
        key: Option<StableKey>,
        evidence_ref: Lsn,
    },
}

#[derive(PartialEq, Eq)]
pub enum AttemptKnowledge {
    Started,
    Recorded(Observation),
}

#[derive(PartialEq, Eq)]
pub struct AuthEntry {
    pub request: RequestId,
    pub capability: CapabilityId,
}

#[derive(PartialEq, Eq)]
pub struct AttemptEntry {
    pub request: RequestId,
    pub attempt: AttemptId,
    pub knowledge: AttemptKnowledge,
}

#[derive(PartialEq, Eq)]
pub struct CommitEntry {
    pub request: RequestId,
    pub value: Value,
}

#[derive(PartialEq, Eq)]
pub struct CommittedValue {
    pub attempt: AttemptId,
    pub value: Value,
}

#[derive(PartialEq, Eq)]
pub struct UnknownEvidence {
    pub attempt: Option<AttemptId>,
    pub reason: UnknownReason,
}

pub struct Config {
    pub initial_budget: IMap<CapabilityId, nat>,
    pub request_capability: IMap<RequestId, CapabilityId>,
    pub request_class: IMap<RequestId, RetryClass>,
    pub request_digest: IMap<RequestId, Digest>,
    pub request_key: IMap<RequestId, Option<StableKey>>,
    pub request_namespace: IMap<RequestId, AdapterNamespace>,
    pub max_attempts: IMap<RequestId, nat>,
    pub matches: ISet<(RequestId, CapabilityId)>,
    pub valid_results: ISet<(RequestId, Value)>,
}

pub struct DurableBroker {
    pub phase: IMap<RequestId, Phase>,
    pub remaining: IMap<CapabilityId, nat>,
    pub revoked: ISet<CapabilityId>,
    pub witness: IMap<RequestId, Option<CapabilityId>>,
    pub auth_log: Seq<AuthEntry>,
    pub attempt_log: Seq<AttemptEntry>,
    pub commit_log: Seq<CommitEntry>,
    pub committed: IMap<RequestId, Option<CommittedValue>>,
    pub failed_attempt: IMap<RequestId, Option<AttemptId>>,
    pub unknown_reason: IMap<RequestId, Option<UnknownEvidence>>,
}

pub open spec fn config_wf(cfg: Config) -> bool {
    cfg.initial_budget.dom() == ISet::<CapabilityId>::full()
        && cfg.request_capability.dom() == ISet::<RequestId>::full()
        && cfg.request_class.dom() == ISet::<RequestId>::full()
        && cfg.request_digest.dom() == ISet::<RequestId>::full()
        && cfg.request_key.dom() == ISet::<RequestId>::full()
        && cfg.request_namespace.dom() == ISet::<RequestId>::full()
        && cfg.max_attempts.dom() == ISet::<RequestId>::full()
        && forall|r: RequestId| #[trigger] cfg.max_attempts[r] > 0
        && forall|r: RequestId|
            (#[trigger] cfg.request_class[r] == RetryClass::Deduplicated
                <==> cfg.request_key[r].is_some())
        && forall|left: RequestId, right: RequestId| #![auto]
            cfg.request_class[left] == RetryClass::Deduplicated
                && cfg.request_class[right] == RetryClass::Deduplicated
                && cfg.request_namespace[left] == cfg.request_namespace[right]
                && cfg.request_key[left] == cfg.request_key[right]
                    ==> left == right
}

pub open spec fn initial_durable(cfg: Config) -> DurableBroker {
    DurableBroker {
        phase: IMap::new(|_r: RequestId| true, |_r: RequestId| Phase::New),
        remaining: cfg.initial_budget,
        revoked: ISet::empty(),
        witness: IMap::new(|_r: RequestId| true, |_r: RequestId| Option::None),
        auth_log: Seq::empty(),
        attempt_log: Seq::empty(),
        commit_log: Seq::empty(),
        committed: IMap::new(|_r: RequestId| true, |_r: RequestId| Option::None),
        failed_attempt: IMap::new(|_r: RequestId| true, |_r: RequestId| Option::None),
        unknown_reason: IMap::new(|_r: RequestId| true, |_r: RequestId| Option::None),
    }
}

pub open spec fn pred0(n: nat) -> nat {
    if n > 0 { (n - 1) as nat } else { 0nat }
}

pub open spec fn request_fields_match(
    cfg: Config,
    request: RequestId,
    digest: Digest,
    key: Option<StableKey>,
) -> bool {
    digest == cfg.request_digest[request] && key == cfg.request_key[request]
}

pub open spec fn authorize_count_for_cap(
    journal: Seq<JournalRecord>, capability: CapabilityId,
) -> nat
    decreases journal.len()
{
    if journal.len() == 0 {
        0
    } else {
        authorize_count_for_cap(journal.drop_last(), capability)
            + match journal.last() {
                JournalRecord::Authorize { capability: k, .. } if k == capability => 1nat,
                _ => 0nat,
            }
    }
}

pub open spec fn authorize_count_for_request(
    journal: Seq<JournalRecord>, request: RequestId,
) -> nat
    decreases journal.len()
{
    if journal.len() == 0 {
        0
    } else {
        authorize_count_for_request(journal.drop_last(), request)
            + match journal.last() {
                JournalRecord::Authorize { request: r, .. } if r == request => 1nat,
                _ => 0nat,
            }
    }
}

pub open spec fn auth_projection(journal: Seq<JournalRecord>) -> Seq<AuthEntry>
    decreases journal.len()
{
    if journal.len() == 0 {
        Seq::empty()
    } else {
        let prior = auth_projection(journal.drop_last());
        match journal.last() {
            JournalRecord::Authorize { request, capability, .. } => {
                prior.push(AuthEntry { request, capability })
            },
            _ => prior,
        }
    }
}

pub open spec fn attempt_projection(journal: Seq<JournalRecord>) -> Seq<AttemptEntry>
    decreases journal.len()
{
    if journal.len() == 0 {
        Seq::empty()
    } else {
        let prior = attempt_projection(journal.drop_last());
        match journal.last() {
            JournalRecord::Start { request, attempt, .. } => {
                prior.push(AttemptEntry {
                    request, attempt, knowledge: AttemptKnowledge::Started,
                })
            },
            JournalRecord::Outcome { request, attempt, observation, .. } => {
                prior.push(AttemptEntry {
                    request,
                    attempt,
                    knowledge: AttemptKnowledge::Recorded(observation),
                })
            },
            _ => prior,
        }
    }
}

pub open spec fn auth_log_request_count(
    log: Seq<AuthEntry>, request: RequestId,
) -> nat
    decreases log.len()
{
    if log.len() == 0 {
        0
    } else {
        auth_log_request_count(log.drop_last(), request)
            + if log.last().request == request { 1nat } else { 0nat }
    }
}

pub open spec fn terminal_count(journal: Seq<JournalRecord>, request: RequestId) -> nat
    decreases journal.len()
{
    if journal.len() == 0 {
        0
    } else {
        terminal_count(journal.drop_last(), request)
            + match journal.last() {
                JournalRecord::CommitRec { request: r, .. } if r == request => 1nat,
                JournalRecord::FailRec { request: r, .. } if r == request => 1nat,
                JournalRecord::UnknownRec { request: r, .. } if r == request => 1nat,
                _ => 0nat,
            }
    }
}

pub open spec fn commit_count(journal: Seq<JournalRecord>, request: RequestId) -> nat
    decreases journal.len()
{
    if journal.len() == 0 {
        0
    } else {
        commit_count(journal.drop_last(), request)
            + match journal.last() {
                JournalRecord::CommitRec { request: r, .. } if r == request => 1nat,
                _ => 0nat,
            }
    }
}

pub open spec fn commit_projection(journal: Seq<JournalRecord>) -> Seq<CommitEntry>
    decreases journal.len()
{
    if journal.len() == 0 {
        Seq::empty()
    } else {
        let prior = commit_projection(journal.drop_last());
        match journal.last() {
            JournalRecord::CommitRec { request, value, .. } => {
                prior.push(CommitEntry { request, value })
            },
            _ => prior,
        }
    }
}

pub open spec fn commit_log_request_count(
    log: Seq<CommitEntry>, request: RequestId,
) -> nat
    decreases log.len()
{
    if log.len() == 0 {
        0
    } else {
        commit_log_request_count(log.drop_last(), request)
            + if log.last().request == request { 1nat } else { 0nat }
    }
}

pub open spec fn committed_projection(
    journal: Seq<JournalRecord>, request: RequestId,
) -> Option<CommittedValue>
    decreases journal.len()
{
    if journal.len() == 0 {
        Option::None
    } else {
        match journal.last() {
            JournalRecord::CommitRec { request: r, attempt, value, .. }
                if r == request => Option::Some(CommittedValue { attempt, value }),
            _ => committed_projection(journal.drop_last(), request),
        }
    }
}

pub open spec fn failed_projection(
    journal: Seq<JournalRecord>, request: RequestId,
) -> Option<AttemptId>
    decreases journal.len()
{
    if journal.len() == 0 {
        Option::None
    } else {
        match journal.last() {
            JournalRecord::FailRec { request: r, attempt, .. }
                if r == request => Option::Some(attempt),
            _ => failed_projection(journal.drop_last(), request),
        }
    }
}

pub open spec fn unknown_projection(
    journal: Seq<JournalRecord>, request: RequestId,
) -> Option<UnknownEvidence>
    decreases journal.len()
{
    if journal.len() == 0 {
        Option::None
    } else {
        match journal.last() {
            JournalRecord::UnknownRec { request: r, attempt, reason, .. }
                if r == request => Option::Some(UnknownEvidence { attempt, reason }),
            _ => unknown_projection(journal.drop_last(), request),
        }
    }
}

pub open spec fn started_count(journal: Seq<JournalRecord>, request: RequestId) -> nat
    decreases journal.len()
{
    if journal.len() == 0 {
        0
    } else {
        started_count(journal.drop_last(), request)
            + match journal.last() {
                JournalRecord::Start { request: r, .. } if r == request => 1nat,
                _ => 0nat,
            }
    }
}

pub open spec fn start_count(
    journal: Seq<JournalRecord>, request: RequestId, attempt: AttemptId,
) -> nat
    decreases journal.len()
{
    if journal.len() == 0 {
        0
    } else {
        start_count(journal.drop_last(), request, attempt)
            + match journal.last() {
                JournalRecord::Start { request: r, attempt: a, .. }
                    if r == request && a == attempt => 1nat,
                _ => 0nat,
            }
    }
}

pub open spec fn outcome_count(
    journal: Seq<JournalRecord>, request: RequestId, attempt: AttemptId,
) -> nat
    decreases journal.len()
{
    if journal.len() == 0 {
        0
    } else {
        outcome_count(journal.drop_last(), request, attempt)
            + match journal.last() {
                JournalRecord::Outcome { request: r, attempt: a, .. }
                    if r == request && a == attempt => 1nat,
                _ => 0nat,
            }
    }
}

pub open spec fn authorize_lsn(
    journal: Seq<JournalRecord>, request: RequestId,
) -> Option<Lsn>
    decreases journal.len()
{
    if journal.len() == 0 {
        Option::None
    } else {
        match journal.last() {
            JournalRecord::Authorize { request: r, .. } if r == request => {
                Option::Some(journal.len())
            },
            _ => authorize_lsn(journal.drop_last(), request),
        }
    }
}

pub open spec fn prepare_lsn(
    journal: Seq<JournalRecord>, request: RequestId,
) -> Option<Lsn>
    decreases journal.len()
{
    if journal.len() == 0 {
        Option::None
    } else {
        match journal.last() {
            JournalRecord::Prepare { request: r, .. } if r == request => {
                Option::Some(journal.len())
            },
            _ => prepare_lsn(journal.drop_last(), request),
        }
    }
}

pub open spec fn arm_lsn(journal: Seq<JournalRecord>, request: RequestId) -> Option<Lsn>
    decreases journal.len()
{
    if journal.len() == 0 {
        Option::None
    } else {
        match journal.last() {
            JournalRecord::Arm { request: r, .. } if r == request => {
                Option::Some(journal.len())
            },
            _ => arm_lsn(journal.drop_last(), request),
        }
    }
}

pub open spec fn start_lsn(
    journal: Seq<JournalRecord>, request: RequestId, attempt: AttemptId,
) -> Option<Lsn>
    decreases journal.len()
{
    if journal.len() == 0 {
        Option::None
    } else {
        match journal.last() {
            JournalRecord::Start { request: r, attempt: a, .. }
                if r == request && a == attempt => Option::Some(journal.len()),
            _ => start_lsn(journal.drop_last(), request, attempt),
        }
    }
}

pub open spec fn outcome_lsn(
    journal: Seq<JournalRecord>, request: RequestId, attempt: AttemptId,
) -> Option<Lsn>
    decreases journal.len()
{
    if journal.len() == 0 {
        Option::None
    } else {
        match journal.last() {
            JournalRecord::Outcome { request: r, attempt: a, .. }
                if r == request && a == attempt => Option::Some(journal.len()),
            _ => outcome_lsn(journal.drop_last(), request, attempt),
        }
    }
}

pub open spec fn outcome_observation(
    journal: Seq<JournalRecord>, request: RequestId, attempt: AttemptId,
) -> Option<Observation>
    decreases journal.len()
{
    if journal.len() == 0 {
        Option::None
    } else {
        match journal.last() {
            JournalRecord::Outcome {
                request: r, attempt: a, observation, ..
            } if r == request && a == attempt => Option::Some(observation),
            _ => outcome_observation(journal.drop_last(), request, attempt),
        }
    }
}

pub open spec fn authorize_at(
    journal: Seq<JournalRecord>, lsn: Lsn, request: RequestId,
) -> bool {
    1 <= lsn && lsn <= journal.len()
        && match journal[(lsn - 1) as int] {
            JournalRecord::Authorize { request: r, .. } => r == request,
            _ => false,
        }
}

pub open spec fn prepare_at(
    journal: Seq<JournalRecord>, lsn: Lsn, request: RequestId,
) -> bool {
    1 <= lsn && lsn <= journal.len()
        && match journal[(lsn - 1) as int] {
            JournalRecord::Prepare { request: r, .. } => r == request,
            _ => false,
        }
}

pub open spec fn arm_at(
    journal: Seq<JournalRecord>, lsn: Lsn, request: RequestId,
) -> bool {
    1 <= lsn && lsn <= journal.len()
        && match journal[(lsn - 1) as int] {
            JournalRecord::Arm { request: r, .. } => r == request,
            _ => false,
        }
}

pub open spec fn start_at(
    journal: Seq<JournalRecord>, lsn: Lsn,
    request: RequestId, attempt: AttemptId,
) -> bool {
    1 <= lsn && lsn <= journal.len()
        && match journal[(lsn - 1) as int] {
            JournalRecord::Start { request: r, attempt: a, .. } => {
                r == request && a == attempt
            },
            _ => false,
        }
}

pub open spec fn outcome_at(
    journal: Seq<JournalRecord>, lsn: Lsn,
    request: RequestId, attempt: AttemptId,
) -> bool {
    1 <= lsn && lsn <= journal.len()
        && match journal[(lsn - 1) as int] {
            JournalRecord::Outcome { request: r, attempt: a, .. } => {
                r == request && a == attempt
            },
            _ => false,
        }
}

pub open spec fn evidence_at(
    journal: Seq<JournalRecord>, lsn: Lsn,
    request: RequestId, attempt: AttemptId,
) -> bool {
    start_at(journal, lsn, request, attempt)
        || outcome_at(journal, lsn, request, attempt)
}

pub open spec fn latest_attempt(
    journal: Seq<JournalRecord>, request: RequestId,
) -> Option<AttemptId> {
    let count = started_count(journal, request);
    if count == 0 { Option::None } else { Option::Some(count) }
}

pub open spec fn latest_evidence_lsn(
    journal: Seq<JournalRecord>, request: RequestId,
) -> Option<Lsn> {
    match latest_attempt(journal, request) {
        Option::None => arm_lsn(journal, request),
        Option::Some(attempt) => match outcome_lsn(journal, request, attempt) {
            Option::Some(lsn) => Option::Some(lsn),
            Option::None => start_lsn(journal, request, attempt),
        },
    }
}

pub open spec fn all_attempts_failed(
    journal: Seq<JournalRecord>, request: RequestId,
) -> bool {
    started_count(journal, request) > 0
        && forall|attempt: AttemptId|
            1 <= attempt && attempt <= started_count(journal, request) ==>
                #[trigger] outcome_observation(journal, request, attempt)
                    == Option::Some(Observation::Failure)
}

pub open spec fn failure_conclusive(
    cfg: Config, journal: Seq<JournalRecord>, request: RequestId,
) -> bool {
    let attempt = started_count(journal, request);
    attempt > 0
        && outcome_observation(journal, request, attempt)
            == Option::Some(Observation::Failure)
        && (cfg.request_class[request] == RetryClass::Idempotent
            ==> all_attempts_failed(journal, request))
}

pub open spec fn durably_uncertain(
    journal: Seq<JournalRecord>, request: RequestId,
) -> bool {
    exists|attempt: AttemptId|
        1 <= attempt && attempt <= started_count(journal, request)
            && match #[trigger] outcome_observation(journal, request, attempt) {
                Option::None => true,
                Option::Some(Observation::Failure) => false,
                Option::Some(_) => true,
            }
}

pub open spec fn apply_record(
    durable: DurableBroker, record: JournalRecord,
) -> DurableBroker {
    match record {
        JournalRecord::Authorize { request, capability, .. } => DurableBroker {
            phase: durable.phase.insert(request, Phase::Authorized),
            remaining: durable.remaining.insert(capability, pred0(durable.remaining[capability])),
            witness: durable.witness.insert(request, Option::Some(capability)),
            auth_log: durable.auth_log.push(AuthEntry { request, capability }),
            ..durable
        },
        JournalRecord::Revoke { capability } => DurableBroker {
            revoked: durable.revoked.insert(capability),
            ..durable
        },
        JournalRecord::Prepare { request, .. } => DurableBroker {
            phase: durable.phase.insert(request, Phase::Prepared),
            ..durable
        },
        JournalRecord::Arm { request, .. } => DurableBroker {
            phase: durable.phase.insert(request, Phase::Armed),
            ..durable
        },
        JournalRecord::Start { request, attempt, .. } => DurableBroker {
            attempt_log: durable.attempt_log.push(AttemptEntry {
                request, attempt, knowledge: AttemptKnowledge::Started,
            }),
            ..durable
        },
        JournalRecord::Outcome { request, attempt, observation, .. } => DurableBroker {
            attempt_log: durable.attempt_log.push(AttemptEntry {
                request, attempt, knowledge: AttemptKnowledge::Recorded(observation),
            }),
            ..durable
        },
        JournalRecord::CommitRec { request, attempt, value, .. } => DurableBroker {
            phase: durable.phase.insert(request, Phase::Committed),
            committed: durable.committed.insert(
                request, Option::Some(CommittedValue { attempt, value }),
            ),
            commit_log: durable.commit_log.push(CommitEntry { request, value }),
            ..durable
        },
        JournalRecord::FailRec { request, attempt, .. } => DurableBroker {
            phase: durable.phase.insert(request, Phase::Failed),
            failed_attempt: durable.failed_attempt.insert(request, Option::Some(attempt)),
            ..durable
        },
        JournalRecord::UnknownRec { request, attempt, reason, .. } => DurableBroker {
            phase: durable.phase.insert(request, Phase::Unknown),
            unknown_reason: durable.unknown_reason.insert(
                request, Option::Some(UnknownEvidence { attempt, reason }),
            ),
            ..durable
        },
    }
}

pub open spec fn replay(cfg: Config, journal: Seq<JournalRecord>) -> DurableBroker
    decreases journal.len()
{
    if journal.len() == 0 {
        initial_durable(cfg)
    } else {
        apply_record(replay(cfg, journal.drop_last()), journal.last())
    }
}

pub open spec fn ref_is(reference: Lsn, expected: Option<Lsn>) -> bool {
    expected == Option::Some(reference)
}

pub open spec fn success_is_valid(
    cfg: Config, request: RequestId, observation: Observation,
) -> bool {
    match observation {
        Observation::Success(value) => cfg.valid_results.contains((request, value)),
        _ => true,
    }
}

pub open spec fn touches_attempt(record: JournalRecord, request: RequestId) -> bool {
    match record {
        JournalRecord::Start { request: r, .. }
        | JournalRecord::Outcome { request: r, .. } => r == request,
        _ => false,
    }
}

pub open spec fn unknown_enabled(
    cfg: Config,
    journal: Seq<JournalRecord>,
    request: RequestId,
    attempt: Option<AttemptId>,
    reason: UnknownReason,
    evidence_ref: Lsn,
) -> bool {
    let started = started_count(journal, request);
    match attempt {
        Option::None => {
            reason == UnknownReason::Recovery
                && started == 0
                && cfg.request_class[request] == RetryClass::Uncontrolled
                && !failure_conclusive(cfg, journal, request)
                && ref_is(evidence_ref, arm_lsn(journal, request))
        },
        Option::Some(a) => {
            a == started
                && started > 0
                && ref_is(evidence_ref, latest_evidence_lsn(journal, request))
                && match reason {
                    UnknownReason::Exhausted => {
                        started == cfg.max_attempts[request]
                            && durably_uncertain(journal, request)
                    },
                    UnknownReason::Recovery => {
                        cfg.request_class[request] == RetryClass::Uncontrolled
                            && !failure_conclusive(cfg, journal, request)
                    },
                    UnknownReason::NonConclusiveFailure => {
                        outcome_observation(journal, request, a)
                            == Option::Some(Observation::Failure)
                            && !failure_conclusive(cfg, journal, request)
                            && ref_is(evidence_ref, outcome_lsn(journal, request, a))
                    },
                    UnknownReason::AmbiguousOutcome => {
                        cfg.request_class[request] == RetryClass::Uncontrolled
                            && outcome_observation(journal, request, a)
                                == Option::Some(Observation::Ambiguous)
                            && ref_is(evidence_ref, outcome_lsn(journal, request, a))
                    },
                    UnknownReason::InvalidResultReason => {
                        cfg.request_class[request] == RetryClass::Uncontrolled
                            && exists|bad: InvalidValue| #![auto]
                                outcome_observation(journal, request, a)
                                    == Option::Some(Observation::InvalidResult(bad))
                            && ref_is(evidence_ref, outcome_lsn(journal, request, a))
                    },
                }
        },
    }
}

pub open spec fn structural_enabled(
    cfg: Config, journal: Seq<JournalRecord>, record: JournalRecord,
) -> bool {
    let durable = replay(cfg, journal);
    match record {
        JournalRecord::Authorize { request, capability, digest } => {
            durable.phase[request] == Phase::New
                && capability == cfg.request_capability[request]
                && cfg.matches.contains((request, capability))
                && !durable.revoked.contains(capability)
                && durable.remaining[capability] > 0
                && digest == cfg.request_digest[request]
        },
        JournalRecord::Revoke { capability } => {
            !durable.revoked.contains(capability)
        },
        JournalRecord::Prepare { request, class, digest, key, auth_ref } => {
            durable.phase[request] == Phase::Authorized
                && class == cfg.request_class[request]
                && request_fields_match(cfg, request, digest, key)
                && durable.witness[request] == Option::Some(cfg.request_capability[request])
                && ref_is(auth_ref, authorize_lsn(journal, request))
        },
        JournalRecord::Arm { request, digest, key, prepare_ref } => {
            durable.phase[request] == Phase::Prepared
                && request_fields_match(cfg, request, digest, key)
                && ref_is(prepare_ref, prepare_lsn(journal, request))
        },
        JournalRecord::Start { request, attempt, digest, key, arm_ref } => {
            durable.phase[request] == Phase::Armed
                && request_fields_match(cfg, request, digest, key)
                && attempt == started_count(journal, request) + 1
                && attempt <= cfg.max_attempts[request]
                && !failure_conclusive(cfg, journal, request)
                && ref_is(arm_ref, arm_lsn(journal, request))
                && (cfg.request_class[request] == RetryClass::Uncontrolled
                    ==> started_count(journal, request) == 0)
        },
        JournalRecord::Outcome {
            request, attempt, observation, digest, key, start_ref,
        } => {
            durable.phase[request] == Phase::Armed
                && request_fields_match(cfg, request, digest, key)
                && attempt > 0
                && attempt == started_count(journal, request)
                && outcome_count(journal, request, attempt) == 0
                && ref_is(start_ref, start_lsn(journal, request, attempt))
                && success_is_valid(cfg, request, observation)
        },
        JournalRecord::CommitRec {
            request, attempt, value, digest, key, outcome_ref,
        } => {
            durable.phase[request] == Phase::Armed
                && request_fields_match(cfg, request, digest, key)
                && attempt > 0
                && attempt == started_count(journal, request)
                && outcome_observation(journal, request, attempt)
                    == Option::Some(Observation::Success(value))
                && ref_is(outcome_ref, outcome_lsn(journal, request, attempt))
        },
        JournalRecord::FailRec {
            request, attempt, digest, key, outcome_ref,
        } => {
            durable.phase[request] == Phase::Armed
                && request_fields_match(cfg, request, digest, key)
                && attempt > 0
                && attempt == started_count(journal, request)
                && failure_conclusive(cfg, journal, request)
                && ref_is(outcome_ref, outcome_lsn(journal, request, attempt))
        },
        JournalRecord::UnknownRec {
            request, attempt, reason, digest, key, evidence_ref,
        } => {
            durable.phase[request] == Phase::Armed
                && request_fields_match(cfg, request, digest, key)
                && unknown_enabled(
                    cfg, journal, request, attempt, reason, evidence_ref,
                )
        },
    }
}

pub open spec fn record_fields_well_typed(
    cfg: Config, journal: Seq<JournalRecord>, record: JournalRecord,
) -> bool {
    match record {
        JournalRecord::Authorize { request, digest, .. } => {
            digest == cfg.request_digest[request]
        },
        JournalRecord::Revoke { .. } => true,
        JournalRecord::Prepare { request, class, digest, key, auth_ref } => {
            class == cfg.request_class[request]
                && request_fields_match(cfg, request, digest, key)
                && auth_ref > 0 && auth_ref <= journal.len()
        },
        JournalRecord::Arm { request, digest, key, prepare_ref } => {
            request_fields_match(cfg, request, digest, key)
                && prepare_ref > 0 && prepare_ref <= journal.len()
        },
        JournalRecord::Start { request, attempt, digest, key, arm_ref } => {
            request_fields_match(cfg, request, digest, key)
                && attempt > 0
                && arm_ref > 0 && arm_ref <= journal.len()
        },
        JournalRecord::Outcome {
            request, attempt, digest, key, start_ref, ..
        } => {
            request_fields_match(cfg, request, digest, key)
                && attempt > 0
                && start_ref > 0 && start_ref <= journal.len()
        },
        JournalRecord::CommitRec {
            request, attempt, digest, key, outcome_ref, ..
        }
        | JournalRecord::FailRec {
            request, attempt, digest, key, outcome_ref,
        } => {
            request_fields_match(cfg, request, digest, key)
                && attempt > 0
                && outcome_ref > 0 && outcome_ref <= journal.len()
        },
        JournalRecord::UnknownRec {
            request, digest, key, evidence_ref, ..
        } => {
            request_fields_match(cfg, request, digest, key)
                && evidence_ref > 0 && evidence_ref <= journal.len()
        },
    }
}

pub open spec fn reference_typed(
    journal: Seq<JournalRecord>, record: JournalRecord,
) -> bool {
    match record {
        JournalRecord::Authorize { .. } | JournalRecord::Revoke { .. } => true,
        JournalRecord::Prepare { request, auth_ref, .. } => {
            authorize_at(journal, auth_ref, request)
        },
        JournalRecord::Arm { request, prepare_ref, .. } => {
            prepare_at(journal, prepare_ref, request)
        },
        JournalRecord::Start { request, arm_ref, .. } => {
            arm_at(journal, arm_ref, request)
        },
        JournalRecord::Outcome { request, attempt, start_ref, .. } => {
            start_at(journal, start_ref, request, attempt)
        },
        JournalRecord::CommitRec { request, attempt, outcome_ref, .. }
        | JournalRecord::FailRec { request, attempt, outcome_ref, .. } => {
            outcome_at(journal, outcome_ref, request, attempt)
        },
        JournalRecord::UnknownRec { request, attempt, evidence_ref, .. } => {
            match attempt {
                Option::None => arm_at(journal, evidence_ref, request),
                Option::Some(a) => evidence_at(journal, evidence_ref, request, a),
            }
        },
    }
}

pub open spec fn journal_legal(cfg: Config, journal: Seq<JournalRecord>) -> bool {
    forall|i: int| 0 <= i < journal.len() ==>
        #[trigger] structural_enabled(cfg, journal.take(i), journal[i])
}

pub open spec fn journal_records_well_typed(
    cfg: Config, journal: Seq<JournalRecord>,
) -> bool {
    forall|i: int| 0 <= i < journal.len() ==> {
        let prefix = journal.take(i);
        let record = #[trigger] journal[i];
        record_fields_well_typed(cfg, prefix, record)
            && reference_typed(prefix, record)
    }
}

pub open spec fn terminal_phase(phase: Phase) -> bool {
    phase == Phase::Committed || phase == Phase::Failed || phase == Phase::Unknown
}

pub open spec fn replay_budget_ok(cfg: Config, journal: Seq<JournalRecord>) -> bool {
    forall|capability: CapabilityId|
        #[trigger] replay(cfg, journal).remaining[capability]
            + authorize_count_for_cap(journal, capability)
            == cfg.initial_budget[capability]
}

pub open spec fn replay_phase_unique_ok(
    cfg: Config, journal: Seq<JournalRecord>,
) -> bool {
    forall|request: RequestId| {
        let count = #[trigger] terminal_count(journal, request);
        count <= 1
            && (terminal_phase(replay(cfg, journal).phase[request]) <==> count == 1)
    }
}

pub open spec fn replay_attempt_shape_ok(
    cfg: Config, journal: Seq<JournalRecord>,
) -> bool {
    forall|request: RequestId| {
        let started = #[trigger] started_count(journal, request);
        started <= cfg.max_attempts[request]
            && forall|attempt: AttemptId| {
                let starts = #[trigger] start_count(journal, request, attempt);
                let outcomes = #[trigger] outcome_count(journal, request, attempt);
                starts == if 1 <= attempt && attempt <= started { 1nat } else { 0nat }
                    && outcomes <= 1
                    && (outcomes == 1 ==> 1 <= attempt && attempt <= started)
            }
    }
}

pub open spec fn replay_commit_unique_ok(
    journal: Seq<JournalRecord>,
) -> bool {
    forall|request: RequestId| #[trigger] commit_count(journal, request) <= 1
}

pub open spec fn replay_commit_log_unique_ok(
    cfg: Config, journal: Seq<JournalRecord>,
) -> bool {
    replay(cfg, journal).commit_log == commit_projection(journal)
        && forall|request: RequestId|
            #[trigger] commit_log_request_count(
                replay(cfg, journal).commit_log, request,
            ) <= 1
}

pub open spec fn replay_authorization_ok(
    cfg: Config, journal: Seq<JournalRecord>,
) -> bool {
    replay(cfg, journal).auth_log == auth_projection(journal)
        && forall|request: RequestId| {
            let count = #[trigger] authorize_count_for_request(journal, request);
            count <= 1
                && auth_log_request_count(replay(cfg, journal).auth_log, request) == count
                && replay(cfg, journal).witness[request]
                    == if count == 0 {
                        Option::None
                    } else {
                        Option::Some(cfg.request_capability[request])
                    }
        }
}

pub open spec fn replay_attempt_log_ok(
    cfg: Config, journal: Seq<JournalRecord>,
) -> bool {
    replay(cfg, journal).attempt_log == attempt_projection(journal)
}

pub open spec fn authorization_phase_count_ok(
    cfg: Config, journal: Seq<JournalRecord>,
) -> bool {
    forall|request: RequestId| {
        let count = #[trigger] authorize_count_for_request(journal, request);
        count <= 1
            && (replay(cfg, journal).phase[request] == Phase::New <==> count == 0)
    }
}

pub open spec fn authorization_prefix_valid(
    cfg: Config, journal: Seq<JournalRecord>,
) -> bool {
    forall|i: int| 0 <= i < journal.len() ==> match #[trigger] journal[i] {
        JournalRecord::Authorize { request, capability, digest } => {
            let prefix = journal.take(i);
            capability == cfg.request_capability[request]
                && cfg.matches.contains((request, capability))
                && digest == cfg.request_digest[request]
                && replay(cfg, prefix).phase[request] == Phase::New
                && !replay(cfg, prefix).revoked.contains(capability)
                && replay(cfg, prefix).remaining[capability] > 0
        },
        _ => true,
    }
}

pub open spec fn uncontrolled_single_attempt(
    cfg: Config, journal: Seq<JournalRecord>,
) -> bool {
    forall|request: RequestId|
        #[trigger] cfg.request_class[request] == RetryClass::Uncontrolled
            ==> started_count(journal, request) <= 1
}

pub open spec fn replay_terminal_fields_ok(
    cfg: Config, journal: Seq<JournalRecord>,
) -> bool {
    (forall|request: RequestId|
        #[trigger] replay(cfg, journal).committed[request]
            == committed_projection(journal, request))
        && (forall|request: RequestId|
            #[trigger] replay(cfg, journal).failed_attempt[request]
                == failed_projection(journal, request))
        && (forall|request: RequestId|
            #[trigger] replay(cfg, journal).unknown_reason[request]
                == unknown_projection(journal, request))
        && forall|request: RequestId| match #[trigger] replay(cfg, journal).phase[request] {
            Phase::Committed => replay(cfg, journal).committed[request].is_some()
                && replay(cfg, journal).failed_attempt[request].is_none()
                && replay(cfg, journal).unknown_reason[request].is_none(),
            Phase::Failed => replay(cfg, journal).committed[request].is_none()
                && replay(cfg, journal).failed_attempt[request].is_some()
                && replay(cfg, journal).unknown_reason[request].is_none(),
            Phase::Unknown => replay(cfg, journal).committed[request].is_none()
                && replay(cfg, journal).failed_attempt[request].is_none()
                && replay(cfg, journal).unknown_reason[request].is_some(),
            _ => replay(cfg, journal).committed[request].is_none()
                && replay(cfg, journal).failed_attempt[request].is_none()
                && replay(cfg, journal).unknown_reason[request].is_none(),
        }
}

pub open spec fn terminal_fields_phase_ok(
    cfg: Config, journal: Seq<JournalRecord>,
) -> bool {
    forall|request: RequestId| match #[trigger] replay(cfg, journal).phase[request] {
        Phase::Committed => replay(cfg, journal).committed[request].is_some()
            && replay(cfg, journal).failed_attempt[request].is_none()
            && replay(cfg, journal).unknown_reason[request].is_none(),
        Phase::Failed => replay(cfg, journal).committed[request].is_none()
            && replay(cfg, journal).failed_attempt[request].is_some()
            && replay(cfg, journal).unknown_reason[request].is_none(),
        Phase::Unknown => replay(cfg, journal).committed[request].is_none()
            && replay(cfg, journal).failed_attempt[request].is_none()
            && replay(cfg, journal).unknown_reason[request].is_some(),
        _ => replay(cfg, journal).committed[request].is_none()
            && replay(cfg, journal).failed_attempt[request].is_none()
            && replay(cfg, journal).unknown_reason[request].is_none(),
    }
}

pub open spec fn replay_terminal_provenance_ok(
    cfg: Config, journal: Seq<JournalRecord>,
) -> bool {
    (forall|request: RequestId| match #[trigger] replay(cfg, journal).committed[request] {
        Option::None => true,
        Option::Some(committed) => {
            outcome_observation(journal, request, committed.attempt)
                == Option::Some(Observation::Success(committed.value))
                && cfg.valid_results.contains((request, committed.value))
        },
    })
        && forall|request: RequestId| match #[trigger] replay(cfg, journal).failed_attempt[request] {
            Option::None => true,
            Option::Some(attempt) => {
                attempt == started_count(journal, request)
                    && failure_conclusive(cfg, journal, request)
                    && outcome_observation(journal, request, attempt)
                        == Option::Some(Observation::Failure)
            },
        }
}

pub open spec fn recorded_success_valid(
    cfg: Config, journal: Seq<JournalRecord>,
) -> bool {
    forall|request: RequestId, attempt: AttemptId, value: Value| #![auto]
        outcome_observation(journal, request, attempt)
            == Option::Some(Observation::Success(value))
                ==> cfg.valid_results.contains((request, value))
}

pub open spec fn replay_scope_confinement_ok(
    cfg: Config, journal: Seq<JournalRecord>,
) -> bool {
    (forall|i: int| 0 <= i < replay(cfg, journal).auth_log.len() ==> {
        let entry = #[trigger] replay(cfg, journal).auth_log[i];
        entry.capability == cfg.request_capability[entry.request]
            && cfg.matches.contains((entry.request, entry.capability))
    })
        && forall|request: RequestId| #![auto]
            !cfg.matches.contains((request, cfg.request_capability[request])) ==> {
                replay(cfg, journal).phase[request] == Phase::New
                    && authorize_count_for_request(journal, request) == 0
                    && started_count(journal, request) == 0
                    && terminal_count(journal, request) == 0
            }
}

pub open spec fn start_prefix_discipline_ok(
    cfg: Config, journal: Seq<JournalRecord>,
) -> bool {
    forall|i: int| 0 <= i < journal.len() ==> match #[trigger] journal[i] {
        JournalRecord::Start { request, attempt, arm_ref, .. } => {
            let prefix = journal.take(i);
            replay(cfg, prefix).phase[request] == Phase::Armed
                && attempt == started_count(prefix, request) + 1
                && attempt <= cfg.max_attempts[request]
                && !failure_conclusive(cfg, prefix, request)
                && arm_at(prefix, arm_ref, request)
                && (cfg.request_class[request] == RetryClass::Uncontrolled
                    ==> started_count(prefix, request) == 0)
        },
        _ => true,
    }
}

pub open spec fn unknown_terminal_provenance_ok(
    cfg: Config, journal: Seq<JournalRecord>,
) -> bool {
    forall|request: RequestId| match #[trigger] replay(cfg, journal).unknown_reason[request] {
        Option::None => true,
        Option::Some(evidence) => exists|i: int| 0 <= i < journal.len()
            && match #[trigger] journal[i] {
                JournalRecord::UnknownRec {
                    request: r, attempt, reason, evidence_ref, ..
                } => {
                    r == request
                        && attempt == evidence.attempt
                        && reason == evidence.reason
                        && unknown_enabled(
                            cfg, journal.take(i), r, attempt, reason, evidence_ref,
                        )
                },
                _ => false,
            },
    }
}

pub open spec fn unknown_records_are_prefix_valid(
    cfg: Config, journal: Seq<JournalRecord>,
) -> bool {
    forall|i: int| 0 <= i < journal.len() ==> match #[trigger] journal[i] {
        JournalRecord::UnknownRec {
            request, attempt, reason, evidence_ref, ..
        } => unknown_enabled(
            cfg, journal.take(i), request, attempt, reason, evidence_ref,
        ),
        _ => true,
    }
}

pub open spec fn r1_replay_invariant(
    cfg: Config, journal: Seq<JournalRecord>,
) -> bool {
    journal_legal(cfg, journal)
        && journal_records_well_typed(cfg, journal)
        && replay_domains_ok(cfg, journal)
        && replay_budget_ok(cfg, journal)
        && replay_authorization_ok(cfg, journal)
        && authorization_phase_count_ok(cfg, journal)
        && authorization_prefix_valid(cfg, journal)
        && replay_scope_confinement_ok(cfg, journal)
        && replay_attempt_log_ok(cfg, journal)
        && replay_attempt_shape_ok(cfg, journal)
        && start_prefix_discipline_ok(cfg, journal)
        && uncontrolled_single_attempt(cfg, journal)
        && replay_phase_unique_ok(cfg, journal)
        && replay_terminal_fields_ok(cfg, journal)
        && replay_commit_unique_ok(journal)
        && replay_commit_log_unique_ok(cfg, journal)
        && recorded_success_valid(cfg, journal)
        && replay_terminal_provenance_ok(cfg, journal)
        && unknown_records_are_prefix_valid(cfg, journal)
        && unknown_terminal_provenance_ok(cfg, journal)
}

pub open spec fn replay_domains_ok(
    cfg: Config, journal: Seq<JournalRecord>,
) -> bool {
    replay(cfg, journal).phase.dom() == ISet::<RequestId>::full()
        && replay(cfg, journal).remaining.dom() == ISet::<CapabilityId>::full()
        && replay(cfg, journal).witness.dom() == ISet::<RequestId>::full()
        && replay(cfg, journal).committed.dom() == ISet::<RequestId>::full()
        && replay(cfg, journal).failed_attempt.dom() == ISet::<RequestId>::full()
        && replay(cfg, journal).unknown_reason.dom() == ISet::<RequestId>::full()
}

pub proof fn replay_push(
    cfg: Config, journal: Seq<JournalRecord>, record: JournalRecord,
)
    ensures
        replay(cfg, journal.push(record)) == apply_record(replay(cfg, journal), record),
{
    assert(journal.push(record).drop_last() =~= journal);
    assert(journal.push(record).last() == record);
}

pub proof fn replay_domains(
    cfg: Config, journal: Seq<JournalRecord>,
)
    requires
        config_wf(cfg),
    ensures
        replay_domains_ok(cfg, journal),
    decreases journal.len(),
{
    broadcast use vstd::imap::group_imap_lemmas;
    broadcast use vstd::iset::group_iset_lemmas;
    if journal.len() == 0 {
        assert(journal =~= Seq::<JournalRecord>::empty());
    } else {
        let prior = journal.drop_last();
        let record = journal.last();
        let durable = replay(cfg, prior);
        assert(prior.push(record) =~= journal);
        replay_domains(cfg, prior);
        match record {
            JournalRecord::Authorize { request, capability, .. } => {
                vstd::imap::lemma_imap_insert_domain(
                    durable.phase, request, Phase::Authorized,
                );
                vstd::imap::lemma_imap_insert_domain(
                    durable.remaining, capability, pred0(durable.remaining[capability]),
                );
                vstd::imap::lemma_imap_insert_domain(
                    durable.witness, request, Option::Some(capability),
                );
            },
            JournalRecord::Prepare { request, .. } => {
                vstd::imap::lemma_imap_insert_domain(
                    durable.phase, request, Phase::Prepared,
                );
            },
            JournalRecord::Arm { request, .. } => {
                vstd::imap::lemma_imap_insert_domain(
                    durable.phase, request, Phase::Armed,
                );
            },
            JournalRecord::CommitRec { request, attempt, value, .. } => {
                vstd::imap::lemma_imap_insert_domain(
                    durable.phase, request, Phase::Committed,
                );
                vstd::imap::lemma_imap_insert_domain(
                    durable.committed,
                    request,
                    Option::Some(CommittedValue { attempt, value }),
                );
            },
            JournalRecord::FailRec { request, attempt, .. } => {
                vstd::imap::lemma_imap_insert_domain(
                    durable.phase, request, Phase::Failed,
                );
                vstd::imap::lemma_imap_insert_domain(
                    durable.failed_attempt, request, Option::Some(attempt),
                );
            },
            JournalRecord::UnknownRec { request, attempt, reason, .. } => {
                vstd::imap::lemma_imap_insert_domain(
                    durable.phase, request, Phase::Unknown,
                );
                vstd::imap::lemma_imap_insert_domain(
                    durable.unknown_reason,
                    request,
                    Option::Some(UnknownEvidence { attempt, reason }),
                );
            },
            _ => {},
        }
    }
    assert(replay(cfg, journal).phase.dom() == ISet::<RequestId>::full());
    assert(replay(cfg, journal).remaining.dom() == ISet::<CapabilityId>::full());
    assert(replay(cfg, journal).witness.dom() == ISet::<RequestId>::full());
    assert(replay(cfg, journal).committed.dom() == ISet::<RequestId>::full());
    assert(replay(cfg, journal).failed_attempt.dom() == ISet::<RequestId>::full());
    assert(replay(cfg, journal).unknown_reason.dom() == ISet::<RequestId>::full());
}

pub proof fn journal_legal_drop_last(cfg: Config, journal: Seq<JournalRecord>)
    requires
        journal.len() > 0,
        journal_legal(cfg, journal),
    ensures
        journal_legal(cfg, journal.drop_last()),
{
    assert forall|i: int| 0 <= i < journal.drop_last().len() implies
        #[trigger] structural_enabled(
            cfg, journal.drop_last().take(i), journal.drop_last()[i],
        ) by {
        assert(journal.drop_last().take(i) =~= journal.take(i));
        assert(journal.drop_last()[i] == journal[i]);
    }
}

pub proof fn journal_legal_last(cfg: Config, journal: Seq<JournalRecord>)
    requires
        journal.len() > 0,
        journal_legal(cfg, journal),
    ensures
        structural_enabled(cfg, journal.drop_last(), journal.last()),
{
    let i = journal.len() as int - 1;
    assert(journal.take(i) =~= journal.drop_last());
    assert(journal[i] == journal.last());
}

pub proof fn journal_legal_take(
    cfg: Config, journal: Seq<JournalRecord>, length: nat,
)
    requires
        journal_legal(cfg, journal),
        length <= journal.len(),
    ensures
        journal_legal(cfg, journal.take(length as int)),
    decreases journal.len(),
{
    if length == journal.len() {
        assert(journal.take(length as int) =~= journal);
    } else {
        assert(journal.len() > 0);
        journal_legal_drop_last(cfg, journal);
        journal_legal_take(cfg, journal.drop_last(), length);
        assert(journal.drop_last().take(length as int) =~= journal.take(length as int));
    }
}

pub proof fn journal_legal_push(
    cfg: Config, journal: Seq<JournalRecord>, record: JournalRecord,
)
    requires
        journal_legal(cfg, journal),
        structural_enabled(cfg, journal, record),
    ensures
        journal_legal(cfg, journal.push(record)),
{
    assert forall|i: int| 0 <= i < journal.push(record).len() implies
        #[trigger] structural_enabled(
            cfg, journal.push(record).take(i), journal.push(record)[i],
        ) by {
        if i < journal.len() {
            assert(journal.push(record).take(i) =~= journal.take(i));
            assert(journal.push(record)[i] == journal[i]);
        } else {
            assert(i == journal.len());
            assert(journal.push(record).take(i) =~= journal);
            assert(journal.push(record)[i] == record);
        }
    }
}

pub proof fn structural_enabled_is_well_typed(
    cfg: Config, journal: Seq<JournalRecord>, record: JournalRecord,
)
    requires
        structural_enabled(cfg, journal, record),
    ensures
        match record {
            JournalRecord::Authorize { request, digest, .. } => {
                digest == cfg.request_digest[request]
            },
            JournalRecord::Revoke { .. } => true,
            JournalRecord::Prepare { request, class, digest, key, auth_ref } => {
                class == cfg.request_class[request]
                    && request_fields_match(cfg, request, digest, key)
                    && auth_ref > 0 && auth_ref <= journal.len()
            },
            JournalRecord::Arm { request, digest, key, prepare_ref } => {
                request_fields_match(cfg, request, digest, key)
                    && prepare_ref > 0 && prepare_ref <= journal.len()
            },
            JournalRecord::Start { request, attempt, digest, key, arm_ref } => {
                request_fields_match(cfg, request, digest, key)
                    && attempt > 0
                    && arm_ref > 0 && arm_ref <= journal.len()
            },
            JournalRecord::Outcome {
                request, attempt, digest, key, start_ref, ..
            } => {
                request_fields_match(cfg, request, digest, key)
                    && attempt > 0
                    && start_ref > 0 && start_ref <= journal.len()
            },
            JournalRecord::CommitRec {
                request, attempt, digest, key, outcome_ref, ..
            }
            | JournalRecord::FailRec {
                request, attempt, digest, key, outcome_ref,
            } => {
                request_fields_match(cfg, request, digest, key)
                    && attempt > 0
                    && outcome_ref > 0 && outcome_ref <= journal.len()
            },
            JournalRecord::UnknownRec {
                request, digest, key, evidence_ref, ..
            } => {
                request_fields_match(cfg, request, digest, key)
                    && evidence_ref > 0 && evidence_ref <= journal.len()
            },
        },
{
    match record {
        JournalRecord::Prepare { request, auth_ref, .. } => {
            match authorize_lsn(journal, request) {
                Option::Some(lsn) => {
                    authorize_lsn_is_in_bounds(journal, request);
                },
                Option::None => {},
            }
        },
        JournalRecord::Arm { request, prepare_ref: _, .. } => {
            prepare_lsn_is_in_bounds(journal, request);
        },
        JournalRecord::Start { request, attempt: _, arm_ref: _, .. } => {
            arm_lsn_is_in_bounds(journal, request);
        },
        JournalRecord::Outcome { request, attempt, .. } => {
            start_lsn_is_in_bounds(journal, request, attempt);
        },
        JournalRecord::CommitRec { request, attempt, .. }
        | JournalRecord::FailRec { request, attempt, .. } => {
            outcome_lsn_is_in_bounds(journal, request, attempt);
        },
        JournalRecord::UnknownRec { request, attempt, .. } => {
            match attempt {
                Option::None => arm_lsn_is_in_bounds(journal, request),
                Option::Some(_) => latest_evidence_lsn_is_in_bounds(journal, request),
            }
        },
        _ => {},
    }
}

pub proof fn authorize_lsn_is_in_bounds(journal: Seq<JournalRecord>, request: RequestId)
    ensures
        match authorize_lsn(journal, request) {
            Option::None => true,
            Option::Some(lsn) => authorize_at(journal, lsn, request),
        },
    decreases journal.len(),
{
    if journal.len() > 0 {
        match journal.last() {
            JournalRecord::Authorize { request: r, .. } if r == request => {},
            _ => authorize_lsn_is_in_bounds(journal.drop_last(), request),
        }
    }
}

pub proof fn prepare_lsn_is_in_bounds(journal: Seq<JournalRecord>, request: RequestId)
    ensures
        match prepare_lsn(journal, request) {
            Option::None => true,
            Option::Some(lsn) => prepare_at(journal, lsn, request),
        },
    decreases journal.len(),
{
    if journal.len() > 0 {
        match journal.last() {
            JournalRecord::Prepare { request: r, .. } if r == request => {},
            _ => prepare_lsn_is_in_bounds(journal.drop_last(), request),
        }
    }
}

pub proof fn arm_lsn_is_in_bounds(journal: Seq<JournalRecord>, request: RequestId)
    ensures
        match arm_lsn(journal, request) {
            Option::None => true,
            Option::Some(lsn) => arm_at(journal, lsn, request),
        },
    decreases journal.len(),
{
    if journal.len() > 0 {
        match journal.last() {
            JournalRecord::Arm { request: r, .. } if r == request => {},
            _ => arm_lsn_is_in_bounds(journal.drop_last(), request),
        }
    }
}

pub proof fn start_lsn_is_in_bounds(
    journal: Seq<JournalRecord>, request: RequestId, attempt: AttemptId,
)
    ensures
        match start_lsn(journal, request, attempt) {
            Option::None => true,
            Option::Some(lsn) => start_at(journal, lsn, request, attempt),
        },
    decreases journal.len(),
{
    if journal.len() > 0 {
        match journal.last() {
            JournalRecord::Start { request: r, attempt: a, .. }
                if r == request && a == attempt => {},
            _ => start_lsn_is_in_bounds(journal.drop_last(), request, attempt),
        }
    }
}

pub proof fn outcome_lsn_is_in_bounds(
    journal: Seq<JournalRecord>, request: RequestId, attempt: AttemptId,
)
    ensures
        match outcome_lsn(journal, request, attempt) {
            Option::None => true,
            Option::Some(lsn) => outcome_at(journal, lsn, request, attempt),
        },
    decreases journal.len(),
{
    if journal.len() > 0 {
        match journal.last() {
            JournalRecord::Outcome { request: r, attempt: a, .. }
                if r == request && a == attempt => {},
            _ => outcome_lsn_is_in_bounds(journal.drop_last(), request, attempt),
        }
    }
}

pub proof fn latest_evidence_lsn_is_in_bounds(
    journal: Seq<JournalRecord>, request: RequestId,
)
    ensures
        match latest_evidence_lsn(journal, request) {
            Option::None => true,
            Option::Some(lsn) => match latest_attempt(journal, request) {
                Option::None => arm_at(journal, lsn, request),
                Option::Some(attempt) => evidence_at(journal, lsn, request, attempt),
            },
        },
{
    match latest_attempt(journal, request) {
        Option::None => arm_lsn_is_in_bounds(journal, request),
        Option::Some(attempt) => {
            outcome_lsn_is_in_bounds(journal, request, attempt);
            start_lsn_is_in_bounds(journal, request, attempt);
        },
    }
}

pub proof fn structural_enabled_reference_typed(
    cfg: Config, journal: Seq<JournalRecord>, record: JournalRecord,
)
    requires
        structural_enabled(cfg, journal, record),
    ensures
        reference_typed(journal, record),
{
    match record {
        JournalRecord::Authorize { .. } | JournalRecord::Revoke { .. } => {},
        JournalRecord::Prepare { request, .. } => {
            authorize_lsn_is_in_bounds(journal, request);
        },
        JournalRecord::Arm { request, .. } => {
            prepare_lsn_is_in_bounds(journal, request);
        },
        JournalRecord::Start { request, .. } => {
            arm_lsn_is_in_bounds(journal, request);
        },
        JournalRecord::Outcome { request, attempt, .. } => {
            start_lsn_is_in_bounds(journal, request, attempt);
        },
        JournalRecord::CommitRec { request, attempt, .. }
        | JournalRecord::FailRec { request, attempt, .. } => {
            outcome_lsn_is_in_bounds(journal, request, attempt);
        },
        JournalRecord::UnknownRec { request, attempt, .. } => {
            match attempt {
                Option::None => arm_lsn_is_in_bounds(journal, request),
                Option::Some(_) => latest_evidence_lsn_is_in_bounds(journal, request),
            }
        },
    }
}

pub proof fn legal_journal_records_well_typed(
    cfg: Config, journal: Seq<JournalRecord>,
)
    requires
        config_wf(cfg),
        journal_legal(cfg, journal),
    ensures
        journal_records_well_typed(cfg, journal),
{
    assert forall|i: int| 0 <= i < journal.len() implies {
        let prefix = journal.take(i);
        let record = #[trigger] journal[i];
        record_fields_well_typed(cfg, prefix, record)
            && reference_typed(prefix, record)
    } by {
        assert(structural_enabled(cfg, journal.take(i), journal[i]));
        structural_enabled_is_well_typed(cfg, journal.take(i), journal[i]);
        structural_enabled_reference_typed(cfg, journal.take(i), journal[i]);
    }
}

pub proof fn authorize_count_push(
    journal: Seq<JournalRecord>, capability: CapabilityId, record: JournalRecord,
)
    ensures
        authorize_count_for_cap(journal.push(record), capability)
            == authorize_count_for_cap(journal, capability)
                + match record {
                    JournalRecord::Authorize { capability: k, .. }
                        if k == capability => 1nat,
                    _ => 0nat,
                },
{
    assert(journal.push(record).drop_last() =~= journal);
    assert(journal.push(record).last() == record);
}

pub proof fn authorize_request_count_push(
    journal: Seq<JournalRecord>, request: RequestId, record: JournalRecord,
)
    ensures
        authorize_count_for_request(journal.push(record), request)
            == authorize_count_for_request(journal, request)
                + match record {
                    JournalRecord::Authorize { request: r, .. } if r == request => 1nat,
                    _ => 0nat,
                },
{
    assert(journal.push(record).drop_last() =~= journal);
    assert(journal.push(record).last() == record);
}

pub proof fn auth_projection_push(
    journal: Seq<JournalRecord>, record: JournalRecord,
)
    ensures
        auth_projection(journal.push(record))
            == match record {
                JournalRecord::Authorize { request, capability, .. } => {
                    auth_projection(journal).push(AuthEntry { request, capability })
                },
                _ => auth_projection(journal),
            },
{
    assert(journal.push(record).drop_last() =~= journal);
    assert(journal.push(record).last() == record);
}

pub proof fn attempt_projection_push(
    journal: Seq<JournalRecord>, record: JournalRecord,
)
    ensures
        attempt_projection(journal.push(record))
            == match record {
                JournalRecord::Start { request, attempt, .. } => {
                    attempt_projection(journal).push(AttemptEntry {
                        request, attempt, knowledge: AttemptKnowledge::Started,
                    })
                },
                JournalRecord::Outcome { request, attempt, observation, .. } => {
                    attempt_projection(journal).push(AttemptEntry {
                        request,
                        attempt,
                        knowledge: AttemptKnowledge::Recorded(observation),
                    })
                },
                _ => attempt_projection(journal),
            },
{
    assert(journal.push(record).drop_last() =~= journal);
    assert(journal.push(record).last() == record);
}

pub proof fn auth_log_request_count_push(
    log: Seq<AuthEntry>, request: RequestId, entry: AuthEntry,
)
    ensures
        auth_log_request_count(log.push(entry), request)
            == auth_log_request_count(log, request)
                + if entry.request == request { 1nat } else { 0nat },
{
    assert(log.push(entry).drop_last() =~= log);
    assert(log.push(entry).last() == entry);
}

pub proof fn terminal_count_push(
    journal: Seq<JournalRecord>, request: RequestId, record: JournalRecord,
)
    ensures
        terminal_count(journal.push(record), request)
            == terminal_count(journal, request)
                + match record {
                    JournalRecord::CommitRec { request: r, .. } if r == request => 1nat,
                    JournalRecord::FailRec { request: r, .. } if r == request => 1nat,
                    JournalRecord::UnknownRec { request: r, .. } if r == request => 1nat,
                    _ => 0nat,
                },
{
    assert(journal.push(record).drop_last() =~= journal);
    assert(journal.push(record).last() == record);
}

pub proof fn commit_count_push(
    journal: Seq<JournalRecord>, request: RequestId, record: JournalRecord,
)
    ensures
        commit_count(journal.push(record), request)
            == commit_count(journal, request)
                + match record {
                    JournalRecord::CommitRec { request: r, .. } if r == request => 1nat,
                    _ => 0nat,
                },
{
    assert(journal.push(record).drop_last() =~= journal);
    assert(journal.push(record).last() == record);
}

pub proof fn commit_projection_push(
    journal: Seq<JournalRecord>, record: JournalRecord,
)
    ensures
        commit_projection(journal.push(record))
            == match record {
                JournalRecord::CommitRec { request, value, .. } => {
                    commit_projection(journal).push(CommitEntry { request, value })
                },
                _ => commit_projection(journal),
            },
{
    assert(journal.push(record).drop_last() =~= journal);
    assert(journal.push(record).last() == record);
}

pub proof fn commit_log_request_count_push(
    log: Seq<CommitEntry>, request: RequestId, entry: CommitEntry,
)
    ensures
        commit_log_request_count(log.push(entry), request)
            == commit_log_request_count(log, request)
                + if entry.request == request { 1nat } else { 0nat },
{
    assert(log.push(entry).drop_last() =~= log);
    assert(log.push(entry).last() == entry);
}

pub proof fn replay_commit_projection(
    cfg: Config, journal: Seq<JournalRecord>,
)
    ensures
        replay(cfg, journal).commit_log == commit_projection(journal),
    decreases journal.len(),
{
    if journal.len() > 0 {
        replay_commit_projection(cfg, journal.drop_last());
    }
}

pub proof fn replay_auth_projection(
    cfg: Config, journal: Seq<JournalRecord>,
)
    ensures
        replay(cfg, journal).auth_log == auth_projection(journal),
    decreases journal.len(),
{
    if journal.len() > 0 {
        replay_auth_projection(cfg, journal.drop_last());
    }
}

pub proof fn replay_attempt_projection(
    cfg: Config, journal: Seq<JournalRecord>,
)
    ensures
        replay_attempt_log_ok(cfg, journal),
    decreases journal.len(),
{
    if journal.len() > 0 {
        replay_attempt_projection(cfg, journal.drop_last());
    }
}

pub proof fn auth_projection_count(
    journal: Seq<JournalRecord>, request: RequestId,
)
    ensures
        auth_log_request_count(auth_projection(journal), request)
            == authorize_count_for_request(journal, request),
    decreases journal.len(),
{
    if journal.len() > 0 {
        let prior = journal.drop_last();
        let record = journal.last();
        auth_projection_count(prior, request);
        match record {
            JournalRecord::Authorize { request: r, capability, .. } => {
                auth_log_request_count_push(
                    auth_projection(prior), request, AuthEntry { request: r, capability },
                );
            },
            _ => {},
        }
    }
}

pub proof fn replay_terminal_projections(
    cfg: Config, journal: Seq<JournalRecord>,
)
    ensures
        forall|request: RequestId|
            #[trigger] replay(cfg, journal).committed[request]
                == committed_projection(journal, request),
        forall|request: RequestId|
            #[trigger] replay(cfg, journal).failed_attempt[request]
                == failed_projection(journal, request),
        forall|request: RequestId|
            #[trigger] replay(cfg, journal).unknown_reason[request]
                == unknown_projection(journal, request),
    decreases journal.len(),
{
    if journal.len() == 0 {
        assert(journal =~= Seq::<JournalRecord>::empty());
    } else {
        let prior = journal.drop_last();
        let record = journal.last();
        replay_terminal_projections(cfg, prior);
        assert forall|request: RequestId|
            #[trigger] replay(cfg, journal).committed[request]
                == committed_projection(journal, request) by {}
        assert forall|request: RequestId|
            #[trigger] replay(cfg, journal).failed_attempt[request]
                == failed_projection(journal, request) by {}
        assert forall|request: RequestId|
            #[trigger] replay(cfg, journal).unknown_reason[request]
                == unknown_projection(journal, request) by {}
    }
}

pub proof fn commit_projection_count(
    journal: Seq<JournalRecord>, request: RequestId,
)
    ensures
        commit_log_request_count(commit_projection(journal), request)
            == commit_count(journal, request),
    decreases journal.len(),
{
    if journal.len() > 0 {
        let prior = journal.drop_last();
        let record = journal.last();
        commit_projection_count(prior, request);
        match record {
            JournalRecord::CommitRec { request: r, value, .. } => {
                commit_log_request_count_push(
                    commit_projection(prior), request, CommitEntry { request: r, value },
                );
            },
            _ => {},
        }
    }
}

pub proof fn started_count_push(
    journal: Seq<JournalRecord>, request: RequestId, record: JournalRecord,
)
    ensures
        started_count(journal.push(record), request)
            == started_count(journal, request)
                + match record {
                    JournalRecord::Start { request: r, .. } if r == request => 1nat,
                    _ => 0nat,
                },
{
    assert(journal.push(record).drop_last() =~= journal);
    assert(journal.push(record).last() == record);
}

pub proof fn start_count_push(
    journal: Seq<JournalRecord>, request: RequestId, attempt: AttemptId,
    record: JournalRecord,
)
    ensures
        start_count(journal.push(record), request, attempt)
            == start_count(journal, request, attempt)
                + match record {
                    JournalRecord::Start { request: r, attempt: a, .. }
                        if r == request && a == attempt => 1nat,
                    _ => 0nat,
                },
{
    assert(journal.push(record).drop_last() =~= journal);
    assert(journal.push(record).last() == record);
}

pub proof fn outcome_count_push(
    journal: Seq<JournalRecord>, request: RequestId, attempt: AttemptId,
    record: JournalRecord,
)
    ensures
        outcome_count(journal.push(record), request, attempt)
            == outcome_count(journal, request, attempt)
                + match record {
                    JournalRecord::Outcome { request: r, attempt: a, .. }
                        if r == request && a == attempt => 1nat,
                    _ => 0nat,
                },
{
    assert(journal.push(record).drop_last() =~= journal);
    assert(journal.push(record).last() == record);
}

pub proof fn outcome_observation_push(
    journal: Seq<JournalRecord>, request: RequestId, attempt: AttemptId,
    record: JournalRecord,
)
    ensures
        outcome_observation(journal.push(record), request, attempt)
            == match record {
                JournalRecord::Outcome {
                    request: r, attempt: a, observation, ..
                } if r == request && a == attempt => Option::Some(observation),
                _ => outcome_observation(journal, request, attempt),
            },
{
    assert(journal.push(record).drop_last() =~= journal);
    assert(journal.push(record).last() == record);
}

pub proof fn outcome_observation_some_implies_count(
    journal: Seq<JournalRecord>, request: RequestId, attempt: AttemptId,
)
    ensures
        outcome_observation(journal, request, attempt).is_some()
            ==> outcome_count(journal, request, attempt) > 0,
    decreases journal.len(),
{
    if journal.len() > 0 {
        outcome_observation_some_implies_count(
            journal.drop_last(), request, attempt,
        );
    }
}

pub proof fn attempt_evidence_stutters(
    cfg: Config, journal: Seq<JournalRecord>, record: JournalRecord,
    request: RequestId,
)
    requires
        !touches_attempt(record, request),
    ensures
        started_count(journal.push(record), request) == started_count(journal, request),
        forall|attempt: AttemptId|
            #[trigger] outcome_observation(journal.push(record), request, attempt)
                == outcome_observation(journal, request, attempt),
        all_attempts_failed(journal.push(record), request)
            == all_attempts_failed(journal, request),
        failure_conclusive(cfg, journal.push(record), request)
            == failure_conclusive(cfg, journal, request),
{
    started_count_push(journal, request, record);
    assert forall|attempt: AttemptId|
        #[trigger] outcome_observation(journal.push(record), request, attempt)
            == outcome_observation(journal, request, attempt) by {
        outcome_observation_push(journal, request, attempt, record);
    }
    if all_attempts_failed(journal, request) {
        assert forall|attempt: AttemptId|
            1 <= attempt && attempt <= started_count(journal.push(record), request)
                implies #[trigger] outcome_observation(
                    journal.push(record), request, attempt,
                ) == Option::Some(Observation::Failure) by {
            assert(outcome_observation(journal, request, attempt)
                == Option::Some(Observation::Failure));
        }
    }
    if all_attempts_failed(journal.push(record), request) {
        assert forall|attempt: AttemptId|
            1 <= attempt && attempt <= started_count(journal, request)
                implies #[trigger] outcome_observation(journal, request, attempt)
                    == Option::Some(Observation::Failure) by {
            assert(outcome_observation(journal.push(record), request, attempt)
                == Option::Some(Observation::Failure));
            assert(outcome_observation(journal.push(record), request, attempt)
                == outcome_observation(journal, request, attempt));
        }
    }
}

pub proof fn replay_budget(
    cfg: Config, journal: Seq<JournalRecord>,
)
    requires
        config_wf(cfg),
        journal_legal(cfg, journal),
    ensures
        replay_budget_ok(cfg, journal),
    decreases journal.len(),
{
    if journal.len() == 0 {
        assert forall|capability: CapabilityId|
            #[trigger] replay(cfg, journal).remaining[capability]
                + authorize_count_for_cap(journal, capability)
                == cfg.initial_budget[capability] by {
            assert(journal =~= Seq::<JournalRecord>::empty());
        }
    } else {
        let prior = journal.drop_last();
        let record = journal.last();
        journal_legal_drop_last(cfg, journal);
        journal_legal_last(cfg, journal);
        replay_budget(cfg, prior);
        assert forall|capability: CapabilityId|
            #[trigger] replay(cfg, journal).remaining[capability]
                + authorize_count_for_cap(journal, capability)
                == cfg.initial_budget[capability] by {
            match record {
                JournalRecord::Authorize { capability: k, .. } => {
                    if capability == k {
                        assert(replay(cfg, prior).remaining[k] > 0);
                    }
                },
                _ => {},
            }
        }
    }
}

pub proof fn authorization_phase_count(
    cfg: Config, journal: Seq<JournalRecord>,
)
    requires
        config_wf(cfg),
        journal_legal(cfg, journal),
    ensures
        authorization_phase_count_ok(cfg, journal),
    decreases journal.len(),
{
    if journal.len() == 0 {
        assert(journal =~= Seq::<JournalRecord>::empty());
    } else {
        let prior = journal.drop_last();
        let record = journal.last();
        assert(prior.push(record) =~= journal);
        journal_legal_drop_last(cfg, journal);
        journal_legal_last(cfg, journal);
        authorization_phase_count(cfg, prior);
        assert forall|request: RequestId| {
            let count = #[trigger] authorize_count_for_request(journal, request);
            count <= 1
                && (replay(cfg, journal).phase[request] == Phase::New <==> count == 0)
        } by {
            authorize_request_count_push(prior, request, record);
            match record {
                JournalRecord::Authorize { request: r, .. } => {
                    if request == r {
                        assert(replay(cfg, prior).phase[r] == Phase::New);
                        assert(authorize_count_for_request(prior, r) == 0);
                    }
                },
                JournalRecord::Prepare { request: r, .. }
                | JournalRecord::Arm { request: r, .. }
                | JournalRecord::CommitRec { request: r, .. }
                | JournalRecord::FailRec { request: r, .. }
                | JournalRecord::UnknownRec { request: r, .. } => {
                    if request == r {
                        assert(replay(cfg, prior).phase[r] != Phase::New);
                        assert(authorize_count_for_request(prior, r) == 1);
                    }
                },
                _ => {},
            }
        }
    }
}

pub proof fn replay_authorization(
    cfg: Config, journal: Seq<JournalRecord>,
)
    requires
        config_wf(cfg),
        journal_legal(cfg, journal),
    ensures
        replay_authorization_ok(cfg, journal),
{
    authorization_phase_count(cfg, journal);
    replay_auth_projection(cfg, journal);
    replay_authorization_maps(cfg, journal);
    assert forall|request: RequestId| {
        let count = #[trigger] authorize_count_for_request(journal, request);
        count <= 1
            && auth_log_request_count(replay(cfg, journal).auth_log, request) == count
            && replay(cfg, journal).witness[request]
                == if count == 0 {
                    Option::None
                } else {
                    Option::Some(cfg.request_capability[request])
                }
    } by {
        auth_projection_count(journal, request);
    }
}

pub proof fn replay_authorization_maps(
    cfg: Config, journal: Seq<JournalRecord>,
)
    requires
        config_wf(cfg),
        journal_legal(cfg, journal),
    ensures
        forall|request: RequestId| {
            let count = #[trigger] authorize_count_for_request(journal, request);
            replay(cfg, journal).witness[request]
                == if count == 0 {
                    Option::None
                } else {
                    Option::Some(cfg.request_capability[request])
                }
        },
    decreases journal.len(),
{
    if journal.len() == 0 {
        assert(journal =~= Seq::<JournalRecord>::empty());
    } else {
        let prior = journal.drop_last();
        let record = journal.last();
        assert(prior.push(record) =~= journal);
        journal_legal_drop_last(cfg, journal);
        journal_legal_last(cfg, journal);
        replay_authorization_maps(cfg, prior);
        authorization_phase_count(cfg, prior);
        assert forall|request: RequestId| {
            let count = #[trigger] authorize_count_for_request(journal, request);
            replay(cfg, journal).witness[request]
                == if count == 0 {
                    Option::None
                } else {
                    Option::Some(cfg.request_capability[request])
                }
        } by {
            authorize_request_count_push(prior, request, record);
            match record {
                JournalRecord::Authorize { request: r, capability, .. } => {
                    if request == r {
                        assert(capability == cfg.request_capability[r]);
                        assert(authorize_count_for_request(prior, r) == 0);
                    }
                },
                _ => {},
            }
        }
    }
}

pub proof fn authorization_records_are_prefix_valid(
    cfg: Config, journal: Seq<JournalRecord>,
)
    requires
        config_wf(cfg),
        journal_legal(cfg, journal),
    ensures
        authorization_prefix_valid(cfg, journal),
{
    assert forall|i: int| 0 <= i < journal.len() implies
        match #[trigger] journal[i] {
            JournalRecord::Authorize { request, capability, digest } => {
                let prefix = journal.take(i);
                capability == cfg.request_capability[request]
                    && cfg.matches.contains((request, capability))
                    && digest == cfg.request_digest[request]
                    && replay(cfg, prefix).phase[request] == Phase::New
                    && !replay(cfg, prefix).revoked.contains(capability)
                    && replay(cfg, prefix).remaining[capability] > 0
            },
            _ => true,
        } by {
        assert(structural_enabled(cfg, journal.take(i), journal[i]));
    }
}

pub proof fn replay_auth_log_scope(
    cfg: Config, journal: Seq<JournalRecord>,
)
    requires
        config_wf(cfg),
        journal_legal(cfg, journal),
    ensures
        forall|i: int| 0 <= i < replay(cfg, journal).auth_log.len() ==> {
            let entry = #[trigger] replay(cfg, journal).auth_log[i];
            entry.capability == cfg.request_capability[entry.request]
                && cfg.matches.contains((entry.request, entry.capability))
        },
    decreases journal.len(),
{
    if journal.len() == 0 {
        assert(journal =~= Seq::<JournalRecord>::empty());
    } else {
        let prior = journal.drop_last();
        let record = journal.last();
        assert(prior.push(record) =~= journal);
        journal_legal_drop_last(cfg, journal);
        journal_legal_last(cfg, journal);
        replay_auth_log_scope(cfg, prior);
        assert forall|i: int| 0 <= i < replay(cfg, journal).auth_log.len() implies {
            let entry = #[trigger] replay(cfg, journal).auth_log[i];
            entry.capability == cfg.request_capability[entry.request]
                && cfg.matches.contains((entry.request, entry.capability))
        } by {
            match record {
                JournalRecord::Authorize { request, capability, .. } => {
                    if i == replay(cfg, prior).auth_log.len() {
                        assert(replay(cfg, journal).auth_log[i]
                            == AuthEntry { request, capability });
                    } else {
                        assert(i < replay(cfg, prior).auth_log.len());
                        assert(replay(cfg, journal).auth_log[i]
                            == replay(cfg, prior).auth_log[i]);
                    }
                },
                _ => {},
            }
        }
    }
}

pub proof fn unmatched_request_stays_new(
    cfg: Config, journal: Seq<JournalRecord>,
)
    requires
        config_wf(cfg),
        journal_legal(cfg, journal),
    ensures
        forall|request: RequestId| #![auto]
            !cfg.matches.contains((request, cfg.request_capability[request])) ==> {
                replay(cfg, journal).phase[request] == Phase::New
                    && authorize_count_for_request(journal, request) == 0
                    && started_count(journal, request) == 0
                    && terminal_count(journal, request) == 0
            },
    decreases journal.len(),
{
    if journal.len() == 0 {
        assert(journal =~= Seq::<JournalRecord>::empty());
    } else {
        let prior = journal.drop_last();
        let record = journal.last();
        assert(prior.push(record) =~= journal);
        journal_legal_drop_last(cfg, journal);
        journal_legal_last(cfg, journal);
        unmatched_request_stays_new(cfg, prior);
        assert forall|request: RequestId| #![auto]
            !cfg.matches.contains((request, cfg.request_capability[request])) implies {
                replay(cfg, journal).phase[request] == Phase::New
                    && authorize_count_for_request(journal, request) == 0
                    && started_count(journal, request) == 0
                    && terminal_count(journal, request) == 0
            } by {
            authorize_request_count_push(prior, request, record);
            started_count_push(prior, request, record);
            terminal_count_push(prior, request, record);
            match record {
                JournalRecord::Authorize { request: r, capability, .. } => {
                    if request == r {
                        assert(capability == cfg.request_capability[r]);
                        assert(cfg.matches.contains((r, capability)));
                    }
                },
                JournalRecord::Prepare { request: r, .. }
                | JournalRecord::Arm { request: r, .. }
                | JournalRecord::Start { request: r, .. }
                | JournalRecord::Outcome { request: r, .. }
                | JournalRecord::CommitRec { request: r, .. }
                | JournalRecord::FailRec { request: r, .. }
                | JournalRecord::UnknownRec { request: r, .. } => {
                    if request == r {
                        assert(replay(cfg, prior).phase[r] == Phase::New);
                        assert(replay(cfg, prior).phase[r] != Phase::New);
                    }
                },
                _ => {},
            }
        }
    }
}

pub proof fn replay_scope_confinement(
    cfg: Config, journal: Seq<JournalRecord>,
)
    requires
        config_wf(cfg),
        journal_legal(cfg, journal),
    ensures
        replay_scope_confinement_ok(cfg, journal),
{
    replay_auth_log_scope(cfg, journal);
    unmatched_request_stays_new(cfg, journal);
}

pub proof fn start_records_are_prefix_disciplined(
    cfg: Config, journal: Seq<JournalRecord>,
)
    requires
        config_wf(cfg),
        journal_legal(cfg, journal),
    ensures
        start_prefix_discipline_ok(cfg, journal),
{
    assert forall|i: int| 0 <= i < journal.len() implies
        match #[trigger] journal[i] {
            JournalRecord::Start { request, attempt, arm_ref, .. } => {
                let prefix = journal.take(i);
                replay(cfg, prefix).phase[request] == Phase::Armed
                    && attempt == started_count(prefix, request) + 1
                    && attempt <= cfg.max_attempts[request]
                    && !failure_conclusive(cfg, prefix, request)
                    && arm_at(prefix, arm_ref, request)
                    && (cfg.request_class[request] == RetryClass::Uncontrolled
                        ==> started_count(prefix, request) == 0)
            },
            _ => true,
        } by {
        assert(structural_enabled(cfg, journal.take(i), journal[i]));
        structural_enabled_reference_typed(cfg, journal.take(i), journal[i]);
    }
}

pub proof fn unknown_records_prefix_valid(
    cfg: Config, journal: Seq<JournalRecord>,
)
    requires
        config_wf(cfg),
        journal_legal(cfg, journal),
    ensures
        unknown_records_are_prefix_valid(cfg, journal),
{
    assert forall|i: int| 0 <= i < journal.len() implies
        match #[trigger] journal[i] {
            JournalRecord::UnknownRec {
                request, attempt, reason, evidence_ref, ..
            } => unknown_enabled(
                cfg, journal.take(i), request, attempt, reason, evidence_ref,
            ),
            _ => true,
        } by {
        assert(structural_enabled(cfg, journal.take(i), journal[i]));
    }
}

pub proof fn replay_phase_unique(
    cfg: Config, journal: Seq<JournalRecord>,
)
    requires
        config_wf(cfg),
        journal_legal(cfg, journal),
    ensures
        replay_phase_unique_ok(cfg, journal),
    decreases journal.len(),
{
    if journal.len() == 0 {
        assert forall|request: RequestId| {
            let count = #[trigger] terminal_count(journal, request);
            count <= 1
                && (terminal_phase(replay(cfg, journal).phase[request]) <==> count == 1)
        } by {
            assert(journal =~= Seq::<JournalRecord>::empty());
        }
    } else {
        let prior = journal.drop_last();
        let record = journal.last();
        journal_legal_drop_last(cfg, journal);
        journal_legal_last(cfg, journal);
        replay_phase_unique(cfg, prior);
        assert forall|request: RequestId| {
            let count = #[trigger] terminal_count(journal, request);
            count <= 1
                && (terminal_phase(replay(cfg, journal).phase[request]) <==> count == 1)
        } by {
            terminal_count_push(prior, request, record);
            match record {
                JournalRecord::Authorize { request: r, .. }
                | JournalRecord::Prepare { request: r, .. }
                | JournalRecord::Arm { request: r, .. } => {
                    if request == r {
                        assert(!terminal_phase(replay(cfg, prior).phase[r]));
                    }
                },
                JournalRecord::CommitRec { request: r, .. }
                | JournalRecord::FailRec { request: r, .. }
                | JournalRecord::UnknownRec { request: r, .. } => {
                    if request == r {
                        assert(replay(cfg, prior).phase[r] == Phase::Armed);
                        assert(!terminal_phase(replay(cfg, prior).phase[r]));
                    }
                },
                _ => {},
            }
        }
    }
}

pub proof fn terminal_fields_phase(
    cfg: Config, journal: Seq<JournalRecord>,
)
    requires
        config_wf(cfg),
        journal_legal(cfg, journal),
    ensures
        terminal_fields_phase_ok(cfg, journal),
    decreases journal.len(),
{
    if journal.len() == 0 {
        assert(journal =~= Seq::<JournalRecord>::empty());
    } else {
        let prior = journal.drop_last();
        let record = journal.last();
        assert(prior.push(record) =~= journal);
        journal_legal_drop_last(cfg, journal);
        journal_legal_last(cfg, journal);
        terminal_fields_phase(cfg, prior);
        assert forall|request: RequestId|
            match #[trigger] replay(cfg, journal).phase[request] {
                Phase::Committed => replay(cfg, journal).committed[request].is_some()
                    && replay(cfg, journal).failed_attempt[request].is_none()
                    && replay(cfg, journal).unknown_reason[request].is_none(),
                Phase::Failed => replay(cfg, journal).committed[request].is_none()
                    && replay(cfg, journal).failed_attempt[request].is_some()
                    && replay(cfg, journal).unknown_reason[request].is_none(),
                Phase::Unknown => replay(cfg, journal).committed[request].is_none()
                    && replay(cfg, journal).failed_attempt[request].is_none()
                    && replay(cfg, journal).unknown_reason[request].is_some(),
                _ => replay(cfg, journal).committed[request].is_none()
                    && replay(cfg, journal).failed_attempt[request].is_none()
                    && replay(cfg, journal).unknown_reason[request].is_none(),
            } by {
            match record {
                JournalRecord::Authorize { request: r, .. }
                | JournalRecord::Prepare { request: r, .. }
                | JournalRecord::Arm { request: r, .. }
                | JournalRecord::CommitRec { request: r, .. }
                | JournalRecord::FailRec { request: r, .. }
                | JournalRecord::UnknownRec { request: r, .. } => {
                    if request == r {
                        assert(replay(cfg, prior).committed[r].is_none());
                        assert(replay(cfg, prior).failed_attempt[r].is_none());
                        assert(replay(cfg, prior).unknown_reason[r].is_none());
                    }
                },
                _ => {},
            }
        }
    }
}

pub proof fn replay_terminal_fields(
    cfg: Config, journal: Seq<JournalRecord>,
)
    requires
        config_wf(cfg),
        journal_legal(cfg, journal),
    ensures
        replay_terminal_fields_ok(cfg, journal),
{
    replay_terminal_projections(cfg, journal);
    terminal_fields_phase(cfg, journal);
}

pub proof fn replay_terminal_provenance(
    cfg: Config, journal: Seq<JournalRecord>,
)
    requires
        config_wf(cfg),
        journal_legal(cfg, journal),
    ensures
        replay_terminal_provenance_ok(cfg, journal),
    decreases journal.len(),
{
    replay_recorded_success_valid(cfg, journal);
    if journal.len() == 0 {
        assert(journal =~= Seq::<JournalRecord>::empty());
    } else {
        let prior = journal.drop_last();
        let record = journal.last();
        assert(prior.push(record) =~= journal);
        journal_legal_drop_last(cfg, journal);
        journal_legal_last(cfg, journal);
        replay_terminal_provenance(cfg, prior);
        replay_terminal_fields(cfg, prior);
        assert forall|request: RequestId|
            match #[trigger] replay(cfg, journal).committed[request] {
                Option::None => true,
                Option::Some(committed) => {
                    outcome_observation(journal, request, committed.attempt)
                        == Option::Some(Observation::Success(committed.value))
                        && cfg.valid_results.contains((request, committed.value))
                },
            } by {
            match record {
                JournalRecord::CommitRec { request: r, attempt, value, .. } => {
                    if request == r {
                        outcome_observation_push(prior, r, attempt, record);
                    } else {
                        attempt_evidence_stutters(cfg, prior, record, request);
                    }
                },
                JournalRecord::Start { request: r, .. }
                | JournalRecord::Outcome { request: r, .. } => {
                    if request == r && replay(cfg, prior).committed[request].is_some() {
                        assert(replay(cfg, prior).phase[request] == Phase::Committed);
                        assert(replay(cfg, prior).phase[request] == Phase::Armed);
                    }
                    if replay(cfg, journal).committed[request].is_some() {
                        assert(!touches_attempt(record, request));
                        attempt_evidence_stutters(cfg, prior, record, request);
                    }
                },
                _ => attempt_evidence_stutters(cfg, prior, record, request),
            }
        }
        assert forall|request: RequestId|
            match #[trigger] replay(cfg, journal).failed_attempt[request] {
                Option::None => true,
                Option::Some(attempt) => {
                    attempt == started_count(journal, request)
                        && failure_conclusive(cfg, journal, request)
                        && outcome_observation(journal, request, attempt)
                            == Option::Some(Observation::Failure)
                },
            } by {
            match record {
                JournalRecord::FailRec { request: r, attempt, .. } => {
                    if request == r {
                        attempt_evidence_stutters(cfg, prior, record, request);
                    } else {
                        attempt_evidence_stutters(cfg, prior, record, request);
                    }
                },
                JournalRecord::Start { request: r, .. }
                | JournalRecord::Outcome { request: r, .. } => {
                    if request == r && replay(cfg, prior).failed_attempt[request].is_some() {
                        assert(replay(cfg, prior).phase[request] == Phase::Failed);
                        assert(replay(cfg, prior).phase[request] == Phase::Armed);
                    }
                    if replay(cfg, journal).failed_attempt[request].is_some() {
                        assert(!touches_attempt(record, request));
                        attempt_evidence_stutters(cfg, prior, record, request);
                    }
                },
                _ => attempt_evidence_stutters(cfg, prior, record, request),
            }
        }
    }
}

pub proof fn unknown_projection_has_record(
    journal: Seq<JournalRecord>, request: RequestId, evidence: UnknownEvidence,
)
    requires
        unknown_projection(journal, request) == Option::Some(evidence),
    ensures
        exists|i: int| 0 <= i < journal.len()
            && match #[trigger] journal[i] {
                JournalRecord::UnknownRec { request: r, attempt, reason, .. } => {
                    r == request
                        && attempt == evidence.attempt
                        && reason == evidence.reason
                },
                _ => false,
            },
    decreases journal.len(),
{
    assert(journal.len() > 0);
    match journal.last() {
        JournalRecord::UnknownRec { request: r, attempt, reason, .. }
            if r == request => {
            let i = journal.len() as int - 1;
            assert(journal[i] == journal.last());
            assert(attempt == evidence.attempt);
            assert(reason == evidence.reason);
        },
        _ => {
            unknown_projection_has_record(
                journal.drop_last(), request, evidence,
            );
            let i = choose|i: int| 0 <= i < journal.drop_last().len()
                && match #[trigger] journal.drop_last()[i] {
                    JournalRecord::UnknownRec {
                        request: r, attempt, reason, ..
                    } => r == request
                        && attempt == evidence.attempt
                        && reason == evidence.reason,
                    _ => false,
                };
            assert(journal[i] == journal.drop_last()[i]);
        },
    }
}

pub proof fn replay_unknown_terminal_provenance(
    cfg: Config, journal: Seq<JournalRecord>,
)
    requires
        config_wf(cfg),
        journal_legal(cfg, journal),
    ensures
        unknown_terminal_provenance_ok(cfg, journal),
{
    replay_terminal_projections(cfg, journal);
    unknown_records_prefix_valid(cfg, journal);
    assert forall|request: RequestId|
        match #[trigger] replay(cfg, journal).unknown_reason[request] {
            Option::None => true,
            Option::Some(evidence) => exists|i: int| 0 <= i < journal.len()
                && match #[trigger] journal[i] {
                    JournalRecord::UnknownRec {
                        request: r, attempt, reason, evidence_ref, ..
                    } => {
                        r == request
                            && attempt == evidence.attempt
                            && reason == evidence.reason
                            && unknown_enabled(
                                cfg, journal.take(i), r, attempt, reason, evidence_ref,
                            )
                    },
                    _ => false,
                },
        } by {
        match replay(cfg, journal).unknown_reason[request] {
            Option::None => {},
            Option::Some(evidence) => {
                unknown_projection_has_record(journal, request, evidence);
                let i = choose|i: int| 0 <= i < journal.len()
                    && match #[trigger] journal[i] {
                        JournalRecord::UnknownRec {
                            request: r, attempt, reason, ..
                        } => r == request
                            && attempt == evidence.attempt
                            && reason == evidence.reason,
                        _ => false,
                    };
                assert(match journal[i] {
                    JournalRecord::UnknownRec {
                        request: r, attempt, reason, evidence_ref, ..
                    } => unknown_enabled(
                        cfg, journal.take(i), r, attempt, reason, evidence_ref,
                    ),
                    _ => true,
                });
            },
        }
    }
}

pub proof fn replay_started_bound(
    cfg: Config, journal: Seq<JournalRecord>,
)
    requires
        config_wf(cfg),
        journal_legal(cfg, journal),
    ensures
        forall|request: RequestId|
            #[trigger] started_count(journal, request) <= cfg.max_attempts[request],
    decreases journal.len(),
{
    if journal.len() == 0 {
        assert(journal =~= Seq::<JournalRecord>::empty());
    } else {
        let prior = journal.drop_last();
        let record = journal.last();
        assert(prior.push(record) =~= journal);
        journal_legal_drop_last(cfg, journal);
        journal_legal_last(cfg, journal);
        replay_started_bound(cfg, prior);
        assert forall|request: RequestId|
            #[trigger] started_count(journal, request) <= cfg.max_attempts[request] by {
            started_count_push(prior, request, record);
            match record {
                JournalRecord::Start { request: r, .. } if request == r => {
                    assert(started_count(prior, r) + 1 <= cfg.max_attempts[r]);
                },
                _ => {},
            }
        }
    }
}

pub proof fn replay_start_exact(
    cfg: Config, journal: Seq<JournalRecord>,
)
    requires
        config_wf(cfg),
        journal_legal(cfg, journal),
    ensures
        forall|request: RequestId, attempt: AttemptId|
            #[trigger] start_count(journal, request, attempt)
                == if 1 <= attempt && attempt <= started_count(journal, request) {
                    1nat
                } else {
                    0nat
                },
    decreases journal.len(),
{
    if journal.len() == 0 {
        assert(journal =~= Seq::<JournalRecord>::empty());
    } else {
        let prior = journal.drop_last();
        let record = journal.last();
        assert(prior.push(record) =~= journal);
        journal_legal_drop_last(cfg, journal);
        journal_legal_last(cfg, journal);
        replay_start_exact(cfg, prior);
        assert forall|request: RequestId, attempt: AttemptId|
            #[trigger] start_count(journal, request, attempt)
                == if 1 <= attempt && attempt <= started_count(journal, request) {
                    1nat
                } else {
                    0nat
                } by {
            start_count_push(prior, request, attempt, record);
            started_count_push(prior, request, record);
            assert(start_count(prior, request, attempt)
                == if 1 <= attempt && attempt <= started_count(prior, request) {
                    1nat
                } else {
                    0nat
                });
            match record {
                JournalRecord::Start { request: r, attempt: a, .. } => {
                    if request == r {
                        assert(a == started_count(prior, r) + 1);
                    }
                },
                _ => {},
            }
        }
    }
}

pub proof fn replay_outcome_shape(
    cfg: Config, journal: Seq<JournalRecord>,
)
    requires
        config_wf(cfg),
        journal_legal(cfg, journal),
    ensures
        forall|request: RequestId, attempt: AttemptId| {
            let outcomes = #[trigger] outcome_count(journal, request, attempt);
            outcomes <= 1
                && (outcomes == 1 ==> 1 <= attempt
                    && attempt <= started_count(journal, request))
        },
    decreases journal.len(),
{
    if journal.len() == 0 {
        assert(journal =~= Seq::<JournalRecord>::empty());
    } else {
        let prior = journal.drop_last();
        let record = journal.last();
        assert(prior.push(record) =~= journal);
        journal_legal_drop_last(cfg, journal);
        journal_legal_last(cfg, journal);
        replay_outcome_shape(cfg, prior);
        assert forall|request: RequestId, attempt: AttemptId| {
            let outcomes = #[trigger] outcome_count(journal, request, attempt);
            outcomes <= 1
                && (outcomes == 1 ==> 1 <= attempt
                    && attempt <= started_count(journal, request))
        } by {
            outcome_count_push(prior, request, attempt, record);
            started_count_push(prior, request, record);
            assert(outcome_count(prior, request, attempt) <= 1);
            assert(outcome_count(prior, request, attempt) == 1 ==>
                1 <= attempt && attempt <= started_count(prior, request));
            match record {
                JournalRecord::Outcome { request: r, attempt: a, .. } => {
                    if request == r && attempt == a {
                        assert(outcome_count(prior, r, a) == 0);
                        assert(a == started_count(prior, r));
                        assert(a > 0);
                    }
                },
                _ => {},
            }
        }
    }
}

pub proof fn replay_attempt_shape(
    cfg: Config, journal: Seq<JournalRecord>,
)
    requires
        config_wf(cfg),
        journal_legal(cfg, journal),
    ensures
        replay_attempt_shape_ok(cfg, journal),
{
    replay_started_bound(cfg, journal);
    replay_start_exact(cfg, journal);
    replay_outcome_shape(cfg, journal);
    assert forall|request: RequestId| {
        let started = #[trigger] started_count(journal, request);
        started <= cfg.max_attempts[request]
            && forall|attempt: AttemptId| {
                let starts = #[trigger] start_count(journal, request, attempt);
                let outcomes = #[trigger] outcome_count(journal, request, attempt);
                starts == if 1 <= attempt && attempt <= started { 1nat } else { 0nat }
                    && outcomes <= 1
                    && (outcomes == 1 ==> 1 <= attempt && attempt <= started)
            }
    } by {
        assert forall|attempt: AttemptId| {
            let starts = #[trigger] start_count(journal, request, attempt);
            let outcomes = #[trigger] outcome_count(journal, request, attempt);
            starts == if 1 <= attempt
                && attempt <= started_count(journal, request) { 1nat } else { 0nat }
                && outcomes <= 1
                && (outcomes == 1 ==> 1 <= attempt
                    && attempt <= started_count(journal, request))
        } by {}
    }
}

pub proof fn replay_uncontrolled_single_attempt(
    cfg: Config, journal: Seq<JournalRecord>,
)
    requires
        config_wf(cfg),
        journal_legal(cfg, journal),
    ensures
        uncontrolled_single_attempt(cfg, journal),
    decreases journal.len(),
{
    if journal.len() == 0 {
        assert(journal =~= Seq::<JournalRecord>::empty());
    } else {
        let prior = journal.drop_last();
        let record = journal.last();
        assert(prior.push(record) =~= journal);
        journal_legal_drop_last(cfg, journal);
        journal_legal_last(cfg, journal);
        replay_uncontrolled_single_attempt(cfg, prior);
        assert forall|request: RequestId|
            #[trigger] cfg.request_class[request] == RetryClass::Uncontrolled
                implies started_count(journal, request) <= 1 by {
            started_count_push(prior, request, record);
            match record {
                JournalRecord::Start { request: r, .. } if request == r => {
                    assert(started_count(prior, r) == 0);
                },
                _ => {},
            }
        }
    }
}

pub proof fn replay_recorded_success_valid(
    cfg: Config, journal: Seq<JournalRecord>,
)
    requires
        config_wf(cfg),
        journal_legal(cfg, journal),
    ensures
        recorded_success_valid(cfg, journal),
    decreases journal.len(),
{
    if journal.len() == 0 {
        assert(journal =~= Seq::<JournalRecord>::empty());
    } else {
        let prior = journal.drop_last();
        let record = journal.last();
        assert(prior.push(record) =~= journal);
        journal_legal_drop_last(cfg, journal);
        journal_legal_last(cfg, journal);
        replay_recorded_success_valid(cfg, prior);
        assert forall|request: RequestId, attempt: AttemptId, value: Value| #![auto]
            outcome_observation(journal, request, attempt)
                == Option::Some(Observation::Success(value))
                    implies cfg.valid_results.contains((request, value)) by {
            outcome_observation_push(prior, request, attempt, record);
            match record {
                JournalRecord::Outcome {
                    request: r, attempt: a, observation, ..
                } if request == r && attempt == a => {
                    assert(success_is_valid(cfg, r, observation));
                },
                _ => {},
            }
        }
    }
}

pub proof fn commit_count_le_terminal_count(
    journal: Seq<JournalRecord>, request: RequestId,
)
    ensures
        commit_count(journal, request) <= terminal_count(journal, request),
    decreases journal.len(),
{
    if journal.len() > 0 {
        commit_count_le_terminal_count(journal.drop_last(), request);
    }
}

pub proof fn replay_commit_unique(
    cfg: Config, journal: Seq<JournalRecord>,
)
    requires
        config_wf(cfg),
        journal_legal(cfg, journal),
    ensures
        replay_commit_unique_ok(journal),
{
    replay_phase_unique(cfg, journal);
    assert forall|request: RequestId|
        #[trigger] commit_count(journal, request) <= 1 by {
        commit_count_le_terminal_count(journal, request);
    }
}

pub proof fn replay_commit_log_unique(
    cfg: Config, journal: Seq<JournalRecord>,
)
    requires
        config_wf(cfg),
        journal_legal(cfg, journal),
    ensures
        replay_commit_log_unique_ok(cfg, journal),
{
    replay_commit_unique(cfg, journal);
    replay_commit_projection(cfg, journal);
    assert forall|request: RequestId|
        #[trigger] commit_log_request_count(
            replay(cfg, journal).commit_log, request,
        ) <= 1 by {
        commit_projection_count(journal, request);
    }
}

pub proof fn r1_typed_journal_replay_safety(
    cfg: Config, journal: Seq<JournalRecord>,
)
    requires
        config_wf(cfg),
        journal_legal(cfg, journal),
    ensures
        r1_replay_invariant(cfg, journal),
{
    legal_journal_records_well_typed(cfg, journal);
    replay_domains(cfg, journal);
    replay_budget(cfg, journal);
    authorization_phase_count(cfg, journal);
    replay_authorization(cfg, journal);
    authorization_records_are_prefix_valid(cfg, journal);
    replay_scope_confinement(cfg, journal);
    replay_attempt_projection(cfg, journal);
    replay_phase_unique(cfg, journal);
    replay_attempt_shape(cfg, journal);
    start_records_are_prefix_disciplined(cfg, journal);
    replay_uncontrolled_single_attempt(cfg, journal);
    replay_terminal_fields(cfg, journal);
    replay_commit_unique(cfg, journal);
    replay_commit_log_unique(cfg, journal);
    replay_recorded_success_valid(cfg, journal);
    replay_terminal_provenance(cfg, journal);
    unknown_records_prefix_valid(cfg, journal);
    replay_unknown_terminal_provenance(cfg, journal);
}

pub proof fn r1_legal_extension(
    cfg: Config, journal: Seq<JournalRecord>, record: JournalRecord,
)
    requires
        config_wf(cfg),
        journal_legal(cfg, journal),
        structural_enabled(cfg, journal, record),
    ensures
        r1_replay_invariant(cfg, journal.push(record)),
        replay(cfg, journal.push(record))
            == apply_record(replay(cfg, journal), record),
{
    journal_legal_push(cfg, journal, record);
    replay_push(cfg, journal, record);
    r1_typed_journal_replay_safety(cfg, journal.push(record));
}

pub proof fn r1_all_legal_prefixes(
    cfg: Config, journal: Seq<JournalRecord>,
)
    requires
        config_wf(cfg),
        journal_legal(cfg, journal),
    ensures
        forall|length: nat| length <= journal.len() ==>
            #[trigger] r1_replay_invariant(cfg, journal.take(length as int)),
{
    assert forall|length: nat| length <= journal.len() implies
        #[trigger] r1_replay_invariant(cfg, journal.take(length as int)) by {
        journal_legal_take(cfg, journal, length);
        r1_typed_journal_replay_safety(cfg, journal.take(length as int));
    }
}

}
