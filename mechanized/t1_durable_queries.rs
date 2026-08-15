use vstd::prelude::*;

#[path = "t1_replay_append.rs"]
pub mod c1_layer;

verus! {

use c1_layer::replay_layer;

pub open spec fn attempt_log_started(
    log: Seq<replay_layer::AttemptEntry>,
    request: replay_layer::RequestId,
) -> nat
    decreases log.len()
{
    if log.len() == 0 {
        0
    } else {
        attempt_log_started(log.drop_last(), request)
            + match log.last() {
                replay_layer::AttemptEntry {
                    request: r,
                    knowledge: replay_layer::AttemptKnowledge::Started,
                    ..
                } if r == request => 1nat,
                replay_layer::AttemptEntry { .. } => 0nat,
            }
    }
}

pub open spec fn attempt_log_outcome(
    log: Seq<replay_layer::AttemptEntry>,
    request: replay_layer::RequestId,
    attempt: replay_layer::AttemptId,
) -> Option<replay_layer::Observation>
    decreases log.len()
{
    if log.len() == 0 {
        Option::None
    } else {
        match log.last() {
            replay_layer::AttemptEntry {
                request: r,
                attempt: a,
                knowledge: replay_layer::AttemptKnowledge::Recorded(observation),
            } if r == request && a == attempt => Option::Some(observation),
            replay_layer::AttemptEntry { .. } => {
                attempt_log_outcome(log.drop_last(), request, attempt)
            },
        }
    }
}

pub open spec fn d_started(
    durable: replay_layer::DurableBroker,
    request: replay_layer::RequestId,
) -> nat {
    attempt_log_started(durable.attempt_log, request)
}

pub open spec fn d_outcome(
    durable: replay_layer::DurableBroker,
    request: replay_layer::RequestId,
    attempt: replay_layer::AttemptId,
) -> Option<replay_layer::Observation> {
    attempt_log_outcome(durable.attempt_log, request, attempt)
}

pub open spec fn d_latest(
    durable: replay_layer::DurableBroker,
    request: replay_layer::RequestId,
) -> Option<replay_layer::AttemptId> {
    let count = d_started(durable, request);
    if count == 0 { Option::None } else { Option::Some(count) }
}

pub open spec fn d_all_failed(
    durable: replay_layer::DurableBroker,
    request: replay_layer::RequestId,
) -> bool {
    d_started(durable, request) > 0
        && forall|attempt: replay_layer::AttemptId|
            1 <= attempt && attempt <= d_started(durable, request) ==>
                #[trigger] d_outcome(durable, request, attempt)
                    == Option::Some(replay_layer::Observation::Failure)
}

pub open spec fn d_failure_conclusive(
    cfg: replay_layer::Config,
    durable: replay_layer::DurableBroker,
    request: replay_layer::RequestId,
) -> bool {
    let attempt = d_started(durable, request);
    attempt > 0
        && d_outcome(durable, request, attempt)
            == Option::Some(replay_layer::Observation::Failure)
        && (cfg.request_class[request] == replay_layer::RetryClass::Idempotent
            ==> d_all_failed(durable, request))
}

pub open spec fn recorded_success_j(
    journal: Seq<replay_layer::JournalRecord>,
    request: replay_layer::RequestId,
) -> bool {
    let attempt = replay_layer::started_count(journal, request);
    attempt > 0
        && exists|value: replay_layer::Value| #![auto]
            replay_layer::outcome_observation(journal, request, attempt)
                == Option::Some(replay_layer::Observation::Success(value))
}

pub open spec fn recorded_success_d(
    durable: replay_layer::DurableBroker,
    request: replay_layer::RequestId,
) -> bool {
    let attempt = d_started(durable, request);
    attempt > 0
        && exists|value: replay_layer::Value| #![auto]
            d_outcome(durable, request, attempt)
                == Option::Some(replay_layer::Observation::Success(value))
}

pub open spec fn d_uncertain(
    durable: replay_layer::DurableBroker,
    request: replay_layer::RequestId,
) -> bool {
    exists|attempt: replay_layer::AttemptId|
        1 <= attempt && attempt <= d_started(durable, request)
            && match #[trigger] d_outcome(durable, request, attempt) {
                Option::None => true,
                Option::Some(replay_layer::Observation::Failure) => false,
                Option::Some(_) => true,
            }
}

pub open spec fn unsafe_uncontrolled_j(
    cfg: replay_layer::Config,
    journal: Seq<replay_layer::JournalRecord>,
    request: replay_layer::RequestId,
) -> bool {
    replay_layer::replay(cfg, journal).phase[request] == replay_layer::Phase::Armed
        && cfg.request_class[request] == replay_layer::RetryClass::Uncontrolled
        && !replay_layer::failure_conclusive(cfg, journal, request)
        && !recorded_success_j(journal, request)
}

pub open spec fn unsafe_uncontrolled_d(
    cfg: replay_layer::Config,
    durable: replay_layer::DurableBroker,
    request: replay_layer::RequestId,
) -> bool {
    durable.phase[request] == replay_layer::Phase::Armed
        && cfg.request_class[request] == replay_layer::RetryClass::Uncontrolled
        && !d_failure_conclusive(cfg, durable, request)
        && !recorded_success_d(durable, request)
}

pub open spec fn recovery_complete_j(
    cfg: replay_layer::Config,
    journal: Seq<replay_layer::JournalRecord>,
) -> bool {
    forall|request: replay_layer::RequestId|
        !#[trigger] unsafe_uncontrolled_j(cfg, journal, request)
            && !(replay_layer::replay(cfg, journal).phase[request]
                    == replay_layer::Phase::Armed
                && replay_layer::failure_conclusive(cfg, journal, request))
}

pub open spec fn recovery_complete_d(
    cfg: replay_layer::Config,
    durable: replay_layer::DurableBroker,
) -> bool {
    forall|request: replay_layer::RequestId|
        !#[trigger] unsafe_uncontrolled_d(cfg, durable, request)
            && !(durable.phase[request] == replay_layer::Phase::Armed
                && d_failure_conclusive(cfg, durable, request))
}

pub open spec fn d_unknown_enabled(
    cfg: replay_layer::Config,
    durable: replay_layer::DurableBroker,
    request: replay_layer::RequestId,
    attempt: Option<replay_layer::AttemptId>,
    reason: replay_layer::UnknownReason,
) -> bool {
    let started = d_started(durable, request);
    match attempt {
        Option::None => {
            reason == replay_layer::UnknownReason::Recovery
                && started == 0
                && cfg.request_class[request] == replay_layer::RetryClass::Uncontrolled
                && !d_failure_conclusive(cfg, durable, request)
        },
        Option::Some(a) => {
            a == started
                && started > 0
                && match reason {
                    replay_layer::UnknownReason::Exhausted => {
                        started == cfg.max_attempts[request]
                            && d_uncertain(durable, request)
                    },
                    replay_layer::UnknownReason::Recovery => {
                        cfg.request_class[request] == replay_layer::RetryClass::Uncontrolled
                            && !d_failure_conclusive(cfg, durable, request)
                    },
                    replay_layer::UnknownReason::NonConclusiveFailure => {
                        d_outcome(durable, request, a)
                            == Option::Some(replay_layer::Observation::Failure)
                            && !d_failure_conclusive(cfg, durable, request)
                    },
                    replay_layer::UnknownReason::AmbiguousOutcome => {
                        cfg.request_class[request] == replay_layer::RetryClass::Uncontrolled
                            && d_outcome(durable, request, a)
                                == Option::Some(replay_layer::Observation::Ambiguous)
                    },
                    replay_layer::UnknownReason::InvalidResultReason => {
                        cfg.request_class[request] == replay_layer::RetryClass::Uncontrolled
                            && exists|bad: replay_layer::InvalidValue| #![auto]
                                d_outcome(durable, request, a)
                                    == Option::Some(
                                        replay_layer::Observation::InvalidResult(bad),
                                    )
                    },
                }
        },
    }
}

// The durable semantic guard deliberately omits every numerical LSN-reference
// test.  Those tests remain in StructuralEnabled and are discharged against
// the ghost record history at an abstract append call/linearization.
pub open spec fn abstract_record_enabled(
    cfg: replay_layer::Config,
    durable: replay_layer::DurableBroker,
    record: replay_layer::JournalRecord,
) -> bool {
    match record {
        replay_layer::JournalRecord::Authorize { request, capability, digest } => {
            durable.phase[request] == replay_layer::Phase::New
                && capability == cfg.request_capability[request]
                && cfg.matches.contains((request, capability))
                && !durable.revoked.contains(capability)
                && durable.remaining[capability] > 0
                && digest == cfg.request_digest[request]
        },
        replay_layer::JournalRecord::Revoke { capability } => {
            !durable.revoked.contains(capability)
        },
        replay_layer::JournalRecord::Prepare {
            request, class, digest, key, ..
        } => {
            durable.phase[request] == replay_layer::Phase::Authorized
                && class == cfg.request_class[request]
                && replay_layer::request_fields_match(cfg, request, digest, key)
                && durable.witness[request]
                    == Option::Some(cfg.request_capability[request])
        },
        replay_layer::JournalRecord::Arm { request, digest, key, .. } => {
            durable.phase[request] == replay_layer::Phase::Prepared
                && replay_layer::request_fields_match(cfg, request, digest, key)
        },
        replay_layer::JournalRecord::Start {
            request, attempt, digest, key, ..
        } => {
            durable.phase[request] == replay_layer::Phase::Armed
                && replay_layer::request_fields_match(cfg, request, digest, key)
                && attempt == d_started(durable, request) + 1
                && attempt <= cfg.max_attempts[request]
                && !d_failure_conclusive(cfg, durable, request)
                && (cfg.request_class[request] == replay_layer::RetryClass::Uncontrolled
                    ==> d_started(durable, request) == 0)
        },
        replay_layer::JournalRecord::Outcome {
            request, attempt, observation, digest, key, ..
        } => {
            durable.phase[request] == replay_layer::Phase::Armed
                && replay_layer::request_fields_match(cfg, request, digest, key)
                && attempt > 0
                && attempt == d_started(durable, request)
                && d_outcome(durable, request, attempt).is_none()
                && replay_layer::success_is_valid(cfg, request, observation)
        },
        replay_layer::JournalRecord::CommitRec {
            request, attempt, value, digest, key, ..
        } => {
            durable.phase[request] == replay_layer::Phase::Armed
                && replay_layer::request_fields_match(cfg, request, digest, key)
                && attempt > 0
                && attempt == d_started(durable, request)
                && d_outcome(durable, request, attempt)
                    == Option::Some(replay_layer::Observation::Success(value))
        },
        replay_layer::JournalRecord::FailRec {
            request, attempt, digest, key, ..
        } => {
            durable.phase[request] == replay_layer::Phase::Armed
                && replay_layer::request_fields_match(cfg, request, digest, key)
                && attempt > 0
                && attempt == d_started(durable, request)
                && d_failure_conclusive(cfg, durable, request)
        },
        replay_layer::JournalRecord::UnknownRec {
            request, attempt, reason, digest, key, ..
        } => {
            durable.phase[request] == replay_layer::Phase::Armed
                && replay_layer::request_fields_match(cfg, request, digest, key)
                && d_unknown_enabled(cfg, durable, request, attempt, reason)
        },
    }
}

pub proof fn attempt_log_started_push(
    log: Seq<replay_layer::AttemptEntry>,
    request: replay_layer::RequestId,
    entry: replay_layer::AttemptEntry,
)
    ensures
        attempt_log_started(log.push(entry), request)
            == attempt_log_started(log, request)
                + match entry {
                    replay_layer::AttemptEntry {
                        request: r,
                        knowledge: replay_layer::AttemptKnowledge::Started,
                        ..
                    } if r == request => 1nat,
                    replay_layer::AttemptEntry { .. } => 0nat,
                },
{
    assert(log.push(entry).drop_last() =~= log);
    assert(log.push(entry).last() == entry);
}

pub proof fn attempt_log_outcome_push(
    log: Seq<replay_layer::AttemptEntry>,
    request: replay_layer::RequestId,
    attempt: replay_layer::AttemptId,
    entry: replay_layer::AttemptEntry,
)
    ensures
        attempt_log_outcome(log.push(entry), request, attempt)
            == match entry {
                replay_layer::AttemptEntry {
                    request: r,
                    attempt: a,
                    knowledge: replay_layer::AttemptKnowledge::Recorded(observation),
                } if r == request && a == attempt => Option::Some(observation),
                replay_layer::AttemptEntry { .. } => {
                    attempt_log_outcome(log, request, attempt)
                },
            },
{
    assert(log.push(entry).drop_last() =~= log);
    assert(log.push(entry).last() == entry);
}

pub proof fn attempt_projection_started_exact(
    journal: Seq<replay_layer::JournalRecord>,
    request: replay_layer::RequestId,
)
    ensures
        attempt_log_started(replay_layer::attempt_projection(journal), request)
            == replay_layer::started_count(journal, request),
    decreases journal.len(),
{
    if journal.len() > 0 {
        let prior = journal.drop_last();
        let record = journal.last();
        attempt_projection_started_exact(prior, request);
        replay_layer::attempt_projection_push(prior, record);
        match record {
            replay_layer::JournalRecord::Start { request: r, attempt, .. } => {
                attempt_log_started_push(
                    replay_layer::attempt_projection(prior),
                    request,
                    replay_layer::AttemptEntry {
                        request: r,
                        attempt,
                        knowledge: replay_layer::AttemptKnowledge::Started,
                    },
                );
            },
            replay_layer::JournalRecord::Outcome {
                request: r, attempt, observation, ..
            } => {
                attempt_log_started_push(
                    replay_layer::attempt_projection(prior),
                    request,
                    replay_layer::AttemptEntry {
                        request: r,
                        attempt,
                        knowledge: replay_layer::AttemptKnowledge::Recorded(observation),
                    },
                );
            },
            replay_layer::JournalRecord::Authorize { .. }
            | replay_layer::JournalRecord::Revoke { .. }
            | replay_layer::JournalRecord::Prepare { .. }
            | replay_layer::JournalRecord::Arm { .. }
            | replay_layer::JournalRecord::CommitRec { .. }
            | replay_layer::JournalRecord::FailRec { .. }
            | replay_layer::JournalRecord::UnknownRec { .. } => {},
        }
    }
}

pub proof fn attempt_projection_outcome_exact(
    journal: Seq<replay_layer::JournalRecord>,
    request: replay_layer::RequestId,
    attempt: replay_layer::AttemptId,
)
    ensures
        attempt_log_outcome(
            replay_layer::attempt_projection(journal), request, attempt,
        ) == replay_layer::outcome_observation(journal, request, attempt),
    decreases journal.len(),
{
    if journal.len() > 0 {
        let prior = journal.drop_last();
        let record = journal.last();
        attempt_projection_outcome_exact(prior, request, attempt);
        replay_layer::attempt_projection_push(prior, record);
        match record {
            replay_layer::JournalRecord::Start { request: r, attempt: a, .. } => {
                attempt_log_outcome_push(
                    replay_layer::attempt_projection(prior),
                    request,
                    attempt,
                    replay_layer::AttemptEntry {
                        request: r,
                        attempt: a,
                        knowledge: replay_layer::AttemptKnowledge::Started,
                    },
                );
            },
            replay_layer::JournalRecord::Outcome {
                request: r, attempt: a, observation, ..
            } => {
                attempt_log_outcome_push(
                    replay_layer::attempt_projection(prior),
                    request,
                    attempt,
                    replay_layer::AttemptEntry {
                        request: r,
                        attempt: a,
                        knowledge: replay_layer::AttemptKnowledge::Recorded(observation),
                    },
                );
            },
            replay_layer::JournalRecord::Authorize { .. }
            | replay_layer::JournalRecord::Revoke { .. }
            | replay_layer::JournalRecord::Prepare { .. }
            | replay_layer::JournalRecord::Arm { .. }
            | replay_layer::JournalRecord::CommitRec { .. }
            | replay_layer::JournalRecord::FailRec { .. }
            | replay_layer::JournalRecord::UnknownRec { .. } => {},
        }
    }
}

pub proof fn replay_d_started_exact(
    cfg: replay_layer::Config,
    journal: Seq<replay_layer::JournalRecord>,
    request: replay_layer::RequestId,
)
    ensures
        d_started(replay_layer::replay(cfg, journal), request)
            == replay_layer::started_count(journal, request),
{
    replay_layer::replay_attempt_projection(cfg, journal);
    attempt_projection_started_exact(journal, request);
}

pub proof fn replay_d_outcome_exact(
    cfg: replay_layer::Config,
    journal: Seq<replay_layer::JournalRecord>,
    request: replay_layer::RequestId,
    attempt: replay_layer::AttemptId,
)
    ensures
        d_outcome(replay_layer::replay(cfg, journal), request, attempt)
            == replay_layer::outcome_observation(journal, request, attempt),
{
    replay_layer::replay_attempt_projection(cfg, journal);
    attempt_projection_outcome_exact(journal, request, attempt);
}

pub proof fn replay_d_latest_exact(
    cfg: replay_layer::Config,
    journal: Seq<replay_layer::JournalRecord>,
    request: replay_layer::RequestId,
)
    ensures
        d_latest(replay_layer::replay(cfg, journal), request)
            == replay_layer::latest_attempt(journal, request),
{
    replay_d_started_exact(cfg, journal, request);
}

pub proof fn replay_d_all_failed_exact(
    cfg: replay_layer::Config,
    journal: Seq<replay_layer::JournalRecord>,
    request: replay_layer::RequestId,
)
    ensures
        d_all_failed(replay_layer::replay(cfg, journal), request)
            <==> replay_layer::all_attempts_failed(journal, request),
{
    replay_d_started_exact(cfg, journal, request);
    if d_all_failed(replay_layer::replay(cfg, journal), request) {
        assert forall|attempt: replay_layer::AttemptId|
            1 <= attempt && attempt <= replay_layer::started_count(journal, request)
            implies #[trigger] replay_layer::outcome_observation(
                journal, request, attempt,
            ) == Option::Some(replay_layer::Observation::Failure) by {
            replay_d_outcome_exact(cfg, journal, request, attempt);
        }
    }
    if replay_layer::all_attempts_failed(journal, request) {
        assert forall|attempt: replay_layer::AttemptId|
            1 <= attempt
                && attempt <= d_started(replay_layer::replay(cfg, journal), request)
            implies #[trigger] d_outcome(
                replay_layer::replay(cfg, journal), request, attempt,
            ) == Option::Some(replay_layer::Observation::Failure) by {
            replay_d_outcome_exact(cfg, journal, request, attempt);
        }
    }
}

pub proof fn replay_d_failure_conclusive_exact(
    cfg: replay_layer::Config,
    journal: Seq<replay_layer::JournalRecord>,
    request: replay_layer::RequestId,
)
    ensures
        d_failure_conclusive(cfg, replay_layer::replay(cfg, journal), request)
            <==> replay_layer::failure_conclusive(cfg, journal, request),
{
    replay_d_started_exact(cfg, journal, request);
    replay_d_outcome_exact(
        cfg, journal, request, replay_layer::started_count(journal, request),
    );
    replay_d_all_failed_exact(cfg, journal, request);
}

pub proof fn replay_d_uncertain_exact(
    cfg: replay_layer::Config,
    journal: Seq<replay_layer::JournalRecord>,
    request: replay_layer::RequestId,
)
    ensures
        d_uncertain(replay_layer::replay(cfg, journal), request)
            <==> replay_layer::durably_uncertain(journal, request),
{
    replay_d_started_exact(cfg, journal, request);
    assert forall|attempt: replay_layer::AttemptId|
        d_outcome(replay_layer::replay(cfg, journal), request, attempt)
            == #[trigger] replay_layer::outcome_observation(
                journal, request, attempt,
            ) by {
        replay_d_outcome_exact(cfg, journal, request, attempt);
    }
    if d_uncertain(replay_layer::replay(cfg, journal), request) {
        let attempt = choose|attempt: replay_layer::AttemptId|
            1 <= attempt
                && attempt <= d_started(replay_layer::replay(cfg, journal), request)
                && match #[trigger] d_outcome(
                    replay_layer::replay(cfg, journal), request, attempt,
                ) {
                    Option::None => true,
                    Option::Some(replay_layer::Observation::Failure) => false,
                    Option::Some(_) => true,
                };
        assert(1 <= attempt && attempt <= replay_layer::started_count(journal, request));
        assert(match replay_layer::outcome_observation(journal, request, attempt) {
            Option::None => true,
            Option::Some(replay_layer::Observation::Failure) => false,
            Option::Some(_) => true,
        });
    }
    if replay_layer::durably_uncertain(journal, request) {
        let attempt = choose|attempt: replay_layer::AttemptId|
            1 <= attempt && attempt <= replay_layer::started_count(journal, request)
                && match #[trigger] replay_layer::outcome_observation(
                    journal, request, attempt,
                ) {
                    Option::None => true,
                    Option::Some(replay_layer::Observation::Failure) => false,
                    Option::Some(_) => true,
                };
        assert(1 <= attempt
            && attempt <= d_started(replay_layer::replay(cfg, journal), request));
        assert(match d_outcome(
            replay_layer::replay(cfg, journal), request, attempt,
        ) {
            Option::None => true,
            Option::Some(replay_layer::Observation::Failure) => false,
            Option::Some(_) => true,
        });
    }
}

pub proof fn replay_recovery_predicates_exact(
    cfg: replay_layer::Config,
    journal: Seq<replay_layer::JournalRecord>,
)
    requires
        replay_layer::config_wf(cfg),
        replay_layer::journal_legal(cfg, journal),
    ensures
        forall|request: replay_layer::RequestId|
            #[trigger] unsafe_uncontrolled_d(
                cfg, replay_layer::replay(cfg, journal), request,
            ) <==> unsafe_uncontrolled_j(cfg, journal, request),
        recovery_complete_d(cfg, replay_layer::replay(cfg, journal))
            <==> recovery_complete_j(cfg, journal),
{
    assert forall|request: replay_layer::RequestId|
        unsafe_uncontrolled_d(cfg, replay_layer::replay(cfg, journal), request)
            <==> #[trigger] unsafe_uncontrolled_j(cfg, journal, request) by {
        replay_d_started_exact(cfg, journal, request);
        replay_d_outcome_exact(
            cfg,
            journal,
            request,
            replay_layer::started_count(journal, request),
        );
        replay_d_failure_conclusive_exact(cfg, journal, request);
    }
    assert forall|request: replay_layer::RequestId|
        d_failure_conclusive(cfg, replay_layer::replay(cfg, journal), request)
            <==> #[trigger] replay_layer::failure_conclusive(
                cfg, journal, request,
            ) by {
        replay_d_failure_conclusive_exact(cfg, journal, request);
    }
    if recovery_complete_d(cfg, replay_layer::replay(cfg, journal)) {
        assert(recovery_complete_j(cfg, journal)) by {
            assert forall|request: replay_layer::RequestId|
                !#[trigger] unsafe_uncontrolled_j(cfg, journal, request)
                    && !(replay_layer::replay(cfg, journal).phase[request]
                            == replay_layer::Phase::Armed
                        && replay_layer::failure_conclusive(
                            cfg, journal, request,
                        )) by {
                assert(!unsafe_uncontrolled_d(
                    cfg, replay_layer::replay(cfg, journal), request,
                ));
                assert(!(replay_layer::replay(cfg, journal).phase[request]
                        == replay_layer::Phase::Armed
                    && d_failure_conclusive(
                        cfg, replay_layer::replay(cfg, journal), request,
                    )));
                replay_d_failure_conclusive_exact(cfg, journal, request);
            }
        }
    }
    if recovery_complete_j(cfg, journal) {
        assert(recovery_complete_d(cfg, replay_layer::replay(cfg, journal))) by {
            assert forall|request: replay_layer::RequestId|
                !#[trigger] unsafe_uncontrolled_d(
                    cfg, replay_layer::replay(cfg, journal), request,
                ) && !(replay_layer::replay(cfg, journal).phase[request]
                        == replay_layer::Phase::Armed
                    && d_failure_conclusive(
                        cfg, replay_layer::replay(cfg, journal), request,
                    )) by {
                assert(!unsafe_uncontrolled_j(cfg, journal, request));
                assert(!(replay_layer::replay(cfg, journal).phase[request]
                        == replay_layer::Phase::Armed
                    && replay_layer::failure_conclusive(
                        cfg, journal, request,
                    )));
                replay_d_failure_conclusive_exact(cfg, journal, request);
            }
        }
    }
}

pub proof fn outcome_count_zero_implies_no_observation(
    journal: Seq<replay_layer::JournalRecord>,
    request: replay_layer::RequestId,
    attempt: replay_layer::AttemptId,
)
    requires
        replay_layer::outcome_count(journal, request, attempt) == 0,
    ensures
        replay_layer::outcome_observation(journal, request, attempt).is_none(),
    decreases journal.len(),
{
    if journal.len() > 0 {
        let prior = journal.drop_last();
        let record = journal.last();
        match record {
            replay_layer::JournalRecord::Outcome {
                request: r, attempt: a, ..
            } => {
                if r == request && a == attempt {
                    assert(replay_layer::outcome_count(journal, request, attempt) > 0);
                } else {
                    outcome_count_zero_implies_no_observation(prior, request, attempt);
                }
            },
            replay_layer::JournalRecord::Authorize { .. }
            | replay_layer::JournalRecord::Revoke { .. }
            | replay_layer::JournalRecord::Prepare { .. }
            | replay_layer::JournalRecord::Arm { .. }
            | replay_layer::JournalRecord::Start { .. }
            | replay_layer::JournalRecord::CommitRec { .. }
            | replay_layer::JournalRecord::FailRec { .. }
            | replay_layer::JournalRecord::UnknownRec { .. } => {
                outcome_count_zero_implies_no_observation(prior, request, attempt);
            },
        }
    }
}

pub proof fn structural_enabled_implies_abstract_record_enabled(
    cfg: replay_layer::Config,
    journal: Seq<replay_layer::JournalRecord>,
    record: replay_layer::JournalRecord,
)
    requires
        replay_layer::config_wf(cfg),
        replay_layer::journal_legal(cfg, journal),
        replay_layer::structural_enabled(cfg, journal, record),
    ensures
        abstract_record_enabled(cfg, replay_layer::replay(cfg, journal), record),
{
    match record {
        replay_layer::JournalRecord::Authorize { .. }
        | replay_layer::JournalRecord::Revoke { .. }
        | replay_layer::JournalRecord::Prepare { .. }
        | replay_layer::JournalRecord::Arm { .. } => {},
        replay_layer::JournalRecord::Start { request, .. } => {
            replay_d_started_exact(cfg, journal, request);
            replay_d_failure_conclusive_exact(cfg, journal, request);
        },
        replay_layer::JournalRecord::Outcome { request, attempt, .. } => {
            replay_d_started_exact(cfg, journal, request);
            replay_d_outcome_exact(cfg, journal, request, attempt);
            outcome_count_zero_implies_no_observation(journal, request, attempt);
        },
        replay_layer::JournalRecord::CommitRec { request, attempt, .. } => {
            replay_d_started_exact(cfg, journal, request);
            replay_d_outcome_exact(cfg, journal, request, attempt);
        },
        replay_layer::JournalRecord::FailRec { request, .. } => {
            replay_d_started_exact(cfg, journal, request);
            replay_d_failure_conclusive_exact(cfg, journal, request);
        },
        replay_layer::JournalRecord::UnknownRec { request, attempt, reason, .. } => {
            replay_d_started_exact(cfg, journal, request);
            replay_d_failure_conclusive_exact(cfg, journal, request);
            replay_d_uncertain_exact(cfg, journal, request);
            match attempt {
                Option::None => {},
                Option::Some(a) => {
                    replay_d_outcome_exact(cfg, journal, request, a);
                },
            }
            match reason {
                replay_layer::UnknownReason::Exhausted
                | replay_layer::UnknownReason::Recovery
                | replay_layer::UnknownReason::NonConclusiveFailure
                | replay_layer::UnknownReason::AmbiguousOutcome
                | replay_layer::UnknownReason::InvalidResultReason => {},
            }
        },
    }
}

pub proof fn durable_query_bridge(
    cfg: replay_layer::Config,
    journal: Seq<replay_layer::JournalRecord>,
)
    requires
        replay_layer::config_wf(cfg),
        replay_layer::journal_legal(cfg, journal),
    ensures
        forall|request: replay_layer::RequestId|
            #[trigger] d_started(replay_layer::replay(cfg, journal), request)
                == replay_layer::started_count(journal, request),
        forall|request: replay_layer::RequestId, attempt: replay_layer::AttemptId|
            #[trigger] d_outcome(
                replay_layer::replay(cfg, journal), request, attempt,
            ) == replay_layer::outcome_observation(journal, request, attempt),
        forall|request: replay_layer::RequestId|
            #[trigger] d_latest(replay_layer::replay(cfg, journal), request)
                == replay_layer::latest_attempt(journal, request),
        forall|request: replay_layer::RequestId|
            #[trigger] d_all_failed(replay_layer::replay(cfg, journal), request)
                <==> replay_layer::all_attempts_failed(journal, request),
        forall|request: replay_layer::RequestId|
            #[trigger] d_failure_conclusive(
                cfg, replay_layer::replay(cfg, journal), request,
            ) <==> replay_layer::failure_conclusive(cfg, journal, request),
        forall|request: replay_layer::RequestId|
            #[trigger] recorded_success_d(
                replay_layer::replay(cfg, journal), request,
            ) <==> recorded_success_j(journal, request),
        forall|request: replay_layer::RequestId|
            #[trigger] d_uncertain(replay_layer::replay(cfg, journal), request)
                <==> replay_layer::durably_uncertain(journal, request),
        recovery_complete_d(cfg, replay_layer::replay(cfg, journal))
            <==> recovery_complete_j(cfg, journal),
{
    assert forall|request: replay_layer::RequestId|
        d_started(replay_layer::replay(cfg, journal), request)
            == #[trigger] replay_layer::started_count(journal, request) by {
        replay_d_started_exact(cfg, journal, request);
    }
    assert forall|request: replay_layer::RequestId, attempt: replay_layer::AttemptId|
        d_outcome(replay_layer::replay(cfg, journal), request, attempt)
            == #[trigger] replay_layer::outcome_observation(
                journal, request, attempt,
            ) by {
        replay_d_outcome_exact(cfg, journal, request, attempt);
    }
    assert forall|request: replay_layer::RequestId|
        d_latest(replay_layer::replay(cfg, journal), request)
            == #[trigger] replay_layer::latest_attempt(journal, request) by {
        replay_d_latest_exact(cfg, journal, request);
    }
    assert forall|request: replay_layer::RequestId|
        d_all_failed(replay_layer::replay(cfg, journal), request)
            <==> #[trigger] replay_layer::all_attempts_failed(journal, request) by {
        replay_d_all_failed_exact(cfg, journal, request);
    }
    assert forall|request: replay_layer::RequestId|
        d_failure_conclusive(cfg, replay_layer::replay(cfg, journal), request)
            <==> #[trigger] replay_layer::failure_conclusive(
                cfg, journal, request,
            ) by {
        replay_d_failure_conclusive_exact(cfg, journal, request);
    }
    assert forall|request: replay_layer::RequestId|
        recorded_success_d(replay_layer::replay(cfg, journal), request)
            <==> #[trigger] recorded_success_j(journal, request) by {
        replay_d_started_exact(cfg, journal, request);
        replay_d_outcome_exact(
            cfg,
            journal,
            request,
            replay_layer::started_count(journal, request),
        );
    }
    assert forall|request: replay_layer::RequestId|
        d_uncertain(replay_layer::replay(cfg, journal), request)
            <==> #[trigger] replay_layer::durably_uncertain(
                journal, request,
            ) by {
        replay_d_uncertain_exact(cfg, journal, request);
    }
    replay_recovery_predicates_exact(cfg, journal);
}

}
