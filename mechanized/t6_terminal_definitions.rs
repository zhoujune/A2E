use vstd::prelude::*;

#[path = "t5_commit_contextual.rs"]
pub mod t5_c0_layer;

verus! {

use t5_c0_layer::t5_r0_layer;
use t5_r0_layer::t5_e0_layer;
use t5_e0_layer::t5_s0_layer;
use t5_s0_layer::t4_layer;
use t4_layer::t4_c1_layer;
use t4_c1_layer::t4_c0_layer;
use t4_c0_layer::t3_layer;
use t3_layer::representation_layer as t3_representation_layer;
use t3_representation_layer::event_layer as t3_event_layer;
use t3_event_layer::trace_layer as wal_trace_layer;
use wal_trace_layer::runtime_layer as wal_runtime_layer;
use wal_runtime_layer::t2_layer;
use t2_layer::representation_layer as t2_representation_layer;
use t2_representation_layer::event_layer as t2_event_layer;
use t2_event_layer::trace_layer as journal_trace_layer;
use journal_trace_layer::runtime_layer as journal_runtime_layer;
use journal_runtime_layer::t1_layer;
use t1_layer::execution_layer;
use execution_layer::projection_layer;
use projection_layer::global_layer;
use global_layer::bridge_layer;
use bridge_layer::contract_layer;
use contract_layer::p3_layer;
use p3_layer::p2_layer;
use p2_layer::p1_layer;
use p1_layer::p0_layer;
use p0_layer::config_layer;
use config_layer::broker_layer as record_layer;
use record_layer::query_layer;
use query_layer::c1_layer;
use c1_layer::replay_layer;

// T6-D0 freezes the adapter and terminal-evidence vocabulary. It states no
// terminal bridge theorem. Later checkpoints must derive these predicates
// from the completed execution, representation, and provenance layers.

pub struct ExternalRun<X, I> {
    pub pre: X,
    pub post: X,
    pub interference: I,
}

#[verifier::reject_recursive_types(X)]
#[verifier::reject_recursive_types(I)]
pub struct Adapter<X, I> {
    pub env_rely: spec_fn(
        replay_layer::RequestId,
        Seq<p0_layer::PhysicalEvent>,
        ExternalRun<X, I>,
    ) -> bool,
    pub classification_ok: spec_fn(
        replay_layer::RequestId,
        replay_layer::AttemptId,
        replay_layer::Observation,
        ExternalRun<X, I>,
    ) -> bool,
    pub zero_effect: spec_fn(
        replay_layer::RequestId,
        ExternalRun<X, I>,
    ) -> bool,
    pub one_effect: spec_fn(
        replay_layer::RequestId,
        ExternalRun<X, I>,
    ) -> bool,
    pub result_spec: spec_fn(
        replay_layer::RequestId,
        replay_layer::Value,
        ExternalRun<X, I>,
    ) -> bool,
    pub read_preserves: spec_fn(
        replay_layer::RequestId,
        ExternalRun<X, I>,
    ) -> bool,
    pub idempotent_under_rely: spec_fn(
        replay_layer::RequestId,
        ExternalRun<X, I>,
    ) -> bool,
    pub dedup_service_law: spec_fn(
        replay_layer::RequestId,
        replay_layer::AdapterNamespace,
        replay_layer::StableKey,
        Seq<p0_layer::PhysicalEvent>,
        ExternalRun<X, I>,
    ) -> bool,
}

#[allow(inconsistent_fields)]
#[derive(PartialEq, Eq)]
pub enum TerminalOutcome {
    Commit {
        attempt: replay_layer::AttemptId,
        value: replay_layer::Value,
    },
    Fail {
        attempt: replay_layer::AttemptId,
    },
    UnknownOutcome {
        attempt: Option<replay_layer::AttemptId>,
        reason: replay_layer::UnknownReason,
    },
}

#[derive(PartialEq, Eq)]
pub struct IndexedTerminalRecord {
    pub lsn: replay_layer::Lsn,
    pub record: replay_layer::JournalRecord,
}

pub open spec fn event_is_for_request(
    event: p0_layer::PhysicalEvent,
    request: replay_layer::RequestId,
) -> bool {
    match event {
        p0_layer::PhysicalEvent::Invoke { request: event_request, .. }
        | p0_layer::PhysicalEvent::Delivered {
            request: event_request, ..
        } => event_request == request,
    }
}

pub open spec fn request_local_history(
    history: Seq<p0_layer::PhysicalEvent>,
    request: replay_layer::RequestId,
) -> bool {
    forall|index: int| 0 <= index < history.len() ==>
        event_is_for_request(#[trigger] history[index], request)
}

pub open spec fn canonical_invocations(
    cfg: config_layer::FullConfig,
    history: Seq<p0_layer::PhysicalEvent>,
    request: replay_layer::RequestId,
) -> bool {
    forall|index: int| 0 <= index < history.len() ==>
        match #[trigger] history[index] {
            p0_layer::PhysicalEvent::Invoke { call, .. } => {
                call == config_layer::canonical_call(cfg, request)
            },
            p0_layer::PhysicalEvent::Delivered { .. } => true,
        }
}

pub open spec fn positive_attempt_identifiers(
    history: Seq<p0_layer::PhysicalEvent>,
) -> bool {
    forall|index: int| 0 <= index < history.len() ==>
        match #[trigger] history[index] {
            p0_layer::PhysicalEvent::Invoke { attempt, .. }
            | p0_layer::PhysicalEvent::Delivered { attempt, .. } => {
                attempt > 0
            },
        }
}

pub open spec fn latest_delivery_observation(
    history: Seq<p0_layer::PhysicalEvent>,
    request: replay_layer::RequestId,
    attempt: replay_layer::AttemptId,
) -> Option<replay_layer::Observation>
    decreases history.len()
{
    if history.len() == 0 {
        Option::None
    } else {
        match history.last() {
            p0_layer::PhysicalEvent::Delivered {
                request: event_request,
                attempt: event_attempt,
                observation,
                ..
            } if event_request == request && event_attempt == attempt => {
                Option::Some(observation)
            },
            p0_layer::PhysicalEvent::Invoke { .. }
            | p0_layer::PhysicalEvent::Delivered { .. } => {
                latest_delivery_observation(
                    history.drop_last(), request, attempt,
                )
            },
        }
    }
}

pub open spec fn delivery(
    history: Seq<p0_layer::PhysicalEvent>,
    request: replay_layer::RequestId,
    attempt: replay_layer::AttemptId,
) -> Option<replay_layer::Observation> {
    if p1_layer::delivery_count(history, request, attempt) == 1 {
        latest_delivery_observation(history, request, attempt)
    } else {
        Option::None
    }
}

pub open spec fn invoked(
    history: Seq<p0_layer::PhysicalEvent>,
    request: replay_layer::RequestId,
    attempt: replay_layer::AttemptId,
) -> bool {
    p1_layer::invoke_count(history, request, attempt) > 0
}

pub open spec fn only_invoked_attempt(
    history: Seq<p0_layer::PhysicalEvent>,
    request: replay_layer::RequestId,
    attempt: replay_layer::AttemptId,
) -> bool {
    invoked(history, request, attempt)
        && p2_layer::request_invoke_count(history, request) == 1
}

pub open spec fn at_most_one_invoked_attempt(
    history: Seq<p0_layer::PhysicalEvent>,
    request: replay_layer::RequestId,
) -> bool {
    p2_layer::request_invoke_count(history, request) <= 1
}

pub open spec fn all_invocations_failed(
    history: Seq<p0_layer::PhysicalEvent>,
    request: replay_layer::RequestId,
) -> bool {
    forall|attempt: replay_layer::AttemptId|
        #[trigger] invoked(history, request, attempt) ==>
            delivery(history, request, attempt)
                == Option::Some(replay_layer::Observation::Failure)
}

pub open spec fn single_failure(
    history: Seq<p0_layer::PhysicalEvent>,
    request: replay_layer::RequestId,
    attempt: replay_layer::AttemptId,
) -> bool {
    only_invoked_attempt(history, request, attempt)
        && delivery(history, request, attempt)
            == Option::Some(replay_layer::Observation::Failure)
}

pub open spec fn contains_success_or_invalid(
    history: Seq<p0_layer::PhysicalEvent>,
    request: replay_layer::RequestId,
) -> bool {
    exists|index: int| 0 <= index < history.len()
        && match #[trigger] history[index] {
            p0_layer::PhysicalEvent::Delivered {
                request: event_request,
                observation: replay_layer::Observation::Success(_),
                ..
            }
            | p0_layer::PhysicalEvent::Delivered {
                request: event_request,
                observation: replay_layer::Observation::InvalidResult(_),
                ..
            } => event_request == request,
            p0_layer::PhysicalEvent::Invoke { .. }
            | p0_layer::PhysicalEvent::Delivered { .. } => false,
        }
}

pub open spec fn dedup_failure_resolved(
    history: Seq<p0_layer::PhysicalEvent>,
    request: replay_layer::RequestId,
    attempt: replay_layer::AttemptId,
) -> bool {
    delivery(history, request, attempt)
            == Option::Some(replay_layer::Observation::Failure)
        && !contains_success_or_invalid(history, request)
}

pub open spec fn observations_dedup_compatible(
    left: replay_layer::Observation,
    right: replay_layer::Observation,
) -> bool {
    match left {
        replay_layer::Observation::Success(left_value) => match right {
            replay_layer::Observation::Success(right_value) => {
                left_value == right_value
            },
            replay_layer::Observation::Ambiguous => true,
            replay_layer::Observation::Failure
            | replay_layer::Observation::InvalidResult(_) => false,
        },
        replay_layer::Observation::Failure => match right {
            replay_layer::Observation::Failure
            | replay_layer::Observation::Ambiguous => true,
            replay_layer::Observation::Success(_)
            | replay_layer::Observation::InvalidResult(_) => false,
        },
        replay_layer::Observation::Ambiguous => true,
        replay_layer::Observation::InvalidResult(left_value) => match right {
            replay_layer::Observation::InvalidResult(right_value) => {
                left_value == right_value
            },
            replay_layer::Observation::Ambiguous => true,
            replay_layer::Observation::Success(_)
            | replay_layer::Observation::Failure => false,
        },
    }
}

pub open spec fn deduplicated_observations_consistent(
    history: Seq<p0_layer::PhysicalEvent>,
    request: replay_layer::RequestId,
) -> bool {
    forall|left: int, right: int|
        0 <= left < history.len() && 0 <= right < history.len() ==> {
            match (#[trigger] history[left], #[trigger] history[right]) {
                (
                    p0_layer::PhysicalEvent::Delivered {
                        request: left_request,
                        observation: left_observation,
                        ..
                    },
                    p0_layer::PhysicalEvent::Delivered {
                        request: right_request,
                        observation: right_observation,
                        ..
                    },
                ) if left_request == request && right_request == request => {
                    observations_dedup_compatible(
                        left_observation, right_observation,
                    )
                },
                (
                    p0_layer::PhysicalEvent::Invoke { .. },
                    p0_layer::PhysicalEvent::Invoke { .. },
                )
                | (
                    p0_layer::PhysicalEvent::Invoke { .. },
                    p0_layer::PhysicalEvent::Delivered { .. },
                )
                | (
                    p0_layer::PhysicalEvent::Delivered { .. },
                    p0_layer::PhysicalEvent::Invoke { .. },
                )
                | (
                    p0_layer::PhysicalEvent::Delivered { .. },
                    p0_layer::PhysicalEvent::Delivered { .. },
                ) => true,
            }
        }
}

pub open spec fn delivered_observations_classified<X, I>(
    cfg: config_layer::FullConfig,
    adapter: Adapter<X, I>,
    history: Seq<p0_layer::PhysicalEvent>,
    request: replay_layer::RequestId,
    run: ExternalRun<X, I>,
) -> bool {
    forall|index: int| 0 <= index < history.len() ==>
        match #[trigger] history[index] {
            p0_layer::PhysicalEvent::Delivered {
                attempt, observation, ..
            } => {
                &&& (adapter.classification_ok)(
                    request, attempt, observation, run,
                )
                &&& match observation {
                    replay_layer::Observation::Success(value) => {
                        cfg.valid_results.contains((request, value))
                    },
                    replay_layer::Observation::Failure
                    | replay_layer::Observation::Ambiguous
                    | replay_layer::Observation::InvalidResult(_) => true,
                }
            },
            p0_layer::PhysicalEvent::Invoke { .. } => true,
        }
}

pub open spec fn adapter_class_law<X, I>(
    cfg: config_layer::FullConfig,
    adapter: Adapter<X, I>,
    history: Seq<p0_layer::PhysicalEvent>,
    request: replay_layer::RequestId,
    run: ExternalRun<X, I>,
) -> bool {
    match cfg.request[request].retry_class {
        replay_layer::RetryClass::ReadOnly => {
            (adapter.read_preserves)(request, run)
        },
        replay_layer::RetryClass::Idempotent => {
            (adapter.idempotent_under_rely)(request, run)
        },
        replay_layer::RetryClass::Deduplicated => {
            match cfg.request[request].stable_key {
                Option::None => false,
                Option::Some(key) => (adapter.dedup_service_law)(
                    request,
                    cfg.request[request].adapter_namespace,
                    key,
                    history,
                    run,
                ),
            }
        },
        replay_layer::RetryClass::Uncontrolled => true,
    }
}

pub open spec fn adapter_rely_trace<X, I>(
    paper: t1_layer::PaperConfig<Adapter<X, I>>,
    request: replay_layer::RequestId,
    history: Seq<p0_layer::PhysicalEvent>,
    run: ExternalRun<X, I>,
) -> bool {
    let cfg = t1_layer::paper_broker_config(paper);
    let adapter = paper.adapter;
    &&& (adapter.env_rely)(request, history, run)
    &&& request_local_history(history, request)
    &&& canonical_invocations(cfg, history, request)
    &&& positive_attempt_identifiers(history)
    &&& p1_layer::physical_unique(history)
    &&& p1_layer::physical_ordered(history)
    &&& delivered_observations_classified(
        cfg, adapter, history, request, run,
    )
    &&& adapter_class_law(cfg, adapter, history, request, run)
    &&& (cfg.request[request].retry_class
            != replay_layer::RetryClass::Deduplicated
        || deduplicated_observations_consistent(history, request))
}

pub open spec fn adapter_rely<X, I>(
    paper: t1_layer::PaperConfig<Adapter<X, I>>,
    events: Seq<global_layer::GlobalEvent>,
    request: replay_layer::RequestId,
    run: ExternalRun<X, I>,
) -> bool {
    adapter_rely_trace(
        paper,
        request,
        projection_layer::pi_adapter(events, request),
        run,
    )
}

pub open spec fn is_terminal_record_for(
    record: replay_layer::JournalRecord,
    request: replay_layer::RequestId,
) -> bool {
    match record {
        replay_layer::JournalRecord::CommitRec {
            request: record_request, ..
        }
        | replay_layer::JournalRecord::FailRec {
            request: record_request, ..
        }
        | replay_layer::JournalRecord::UnknownRec {
            request: record_request, ..
        } => record_request == request,
        replay_layer::JournalRecord::Authorize { .. }
        | replay_layer::JournalRecord::Revoke { .. }
        | replay_layer::JournalRecord::Prepare { .. }
        | replay_layer::JournalRecord::Arm { .. }
        | replay_layer::JournalRecord::Start { .. }
        | replay_layer::JournalRecord::Outcome { .. } => false,
    }
}

// The selector is total and returns the latest matching terminal record.
// Journal legality later establishes that a request has at most one.
pub open spec fn latest_terminal_record(
    records: Seq<replay_layer::JournalRecord>,
    request: replay_layer::RequestId,
) -> Option<IndexedTerminalRecord>
    decreases records.len()
{
    if records.len() == 0 {
        Option::None
    } else if is_terminal_record_for(records.last(), request) {
        Option::Some(IndexedTerminalRecord {
            lsn: records.len(),
            record: records.last(),
        })
    } else {
        latest_terminal_record(records.drop_last(), request)
    }
}

// The public selector rejects duplicate terminal records. Its one-based LSN
// therefore names the unique request terminal whenever the result is present.
pub open spec fn terminal_record(
    records: Seq<replay_layer::JournalRecord>,
    request: replay_layer::RequestId,
) -> Option<IndexedTerminalRecord> {
    if replay_layer::terminal_count(records, request) == 1 {
        latest_terminal_record(records, request)
    } else {
        Option::None
    }
}

pub open spec fn terminal_outcome_of_record(
    record: replay_layer::JournalRecord,
    request: replay_layer::RequestId,
) -> Option<TerminalOutcome> {
    match record {
        replay_layer::JournalRecord::CommitRec {
            request: record_request, attempt, value, ..
        } if record_request == request => Option::Some(
            TerminalOutcome::Commit { attempt, value },
        ),
        replay_layer::JournalRecord::FailRec {
            request: record_request, attempt, ..
        } if record_request == request => Option::Some(
            TerminalOutcome::Fail { attempt },
        ),
        replay_layer::JournalRecord::UnknownRec {
            request: record_request, attempt, reason, ..
        } if record_request == request => Option::Some(
            TerminalOutcome::UnknownOutcome { attempt, reason },
        ),
        replay_layer::JournalRecord::Authorize { .. }
        | replay_layer::JournalRecord::Revoke { .. }
        | replay_layer::JournalRecord::Prepare { .. }
        | replay_layer::JournalRecord::Arm { .. }
        | replay_layer::JournalRecord::Start { .. }
        | replay_layer::JournalRecord::Outcome { .. }
        | replay_layer::JournalRecord::CommitRec { .. }
        | replay_layer::JournalRecord::FailRec { .. }
        | replay_layer::JournalRecord::UnknownRec { .. } => Option::None,
    }
}

pub open spec fn terminal_from_records(
    records: Seq<replay_layer::JournalRecord>,
    request: replay_layer::RequestId,
) -> Option<TerminalOutcome> {
    match terminal_record(records, request) {
        Option::None => Option::None,
        Option::Some(indexed) => {
            terminal_outcome_of_record(indexed.record, request)
        },
    }
}

pub open spec fn terminal(
    events: Seq<global_layer::GlobalEvent>,
    request: replay_layer::RequestId,
) -> Option<TerminalOutcome> {
    terminal_from_records(projection_layer::pi_journal(events), request)
}

pub open spec fn outcome_record_at(
    records: Seq<replay_layer::JournalRecord>,
    lsn: replay_layer::Lsn,
    request: replay_layer::RequestId,
    attempt: replay_layer::AttemptId,
    observation: replay_layer::Observation,
) -> bool {
    1 <= lsn && lsn <= records.len()
        && match records[(lsn - 1) as int] {
            replay_layer::JournalRecord::Outcome {
                request: record_request,
                attempt: record_attempt,
                observation: record_observation,
                ..
            } => {
                record_request == request
                    && record_attempt == attempt
                    && record_observation == observation
            },
            replay_layer::JournalRecord::Authorize { .. }
            | replay_layer::JournalRecord::Revoke { .. }
            | replay_layer::JournalRecord::Prepare { .. }
            | replay_layer::JournalRecord::Arm { .. }
            | replay_layer::JournalRecord::Start { .. }
            | replay_layer::JournalRecord::CommitRec { .. }
            | replay_layer::JournalRecord::FailRec { .. }
            | replay_layer::JournalRecord::UnknownRec { .. } => false,
        }
}

pub open spec fn unknown_reason_guard(
    cfg: config_layer::FullConfig,
    records: Seq<replay_layer::JournalRecord>,
    request: replay_layer::RequestId,
    attempt: Option<replay_layer::AttemptId>,
    reason: replay_layer::UnknownReason,
) -> bool {
    let erased = config_layer::erase_config(cfg);
    let started = replay_layer::started_count(records, request);
    match attempt {
        Option::None => {
            reason == replay_layer::UnknownReason::Recovery
                && started == 0
                && erased.request_class[request]
                    == replay_layer::RetryClass::Uncontrolled
                && !replay_layer::failure_conclusive(
                    erased, records, request,
                )
                && !replay_layer::has_durable_success(records, request)
        },
        Option::Some(current) => {
            current == started
                && started > 0
                && match reason {
                    replay_layer::UnknownReason::Exhausted => {
                        started == erased.max_attempts[request]
                            && replay_layer::durably_uncertain(
                                records, request,
                            )
                    },
                    replay_layer::UnknownReason::Recovery => {
                        erased.request_class[request]
                                == replay_layer::RetryClass::Uncontrolled
                            && !replay_layer::failure_conclusive(
                                erased, records, request,
                            )
                            && !replay_layer::has_durable_success(records, request)
                    },
                    replay_layer::UnknownReason::NonConclusiveFailure => {
                        replay_layer::outcome_observation(
                            records, request, current,
                        ) == Option::Some(
                            replay_layer::Observation::Failure,
                        )
                            && !replay_layer::failure_conclusive(
                                erased, records, request,
                            )
                    },
                    replay_layer::UnknownReason::AmbiguousOutcome => {
                        erased.request_class[request]
                                == replay_layer::RetryClass::Uncontrolled
                            && replay_layer::outcome_observation(
                                records, request, current,
                            ) == Option::Some(
                                replay_layer::Observation::Ambiguous,
                            )
                    },
                    replay_layer::UnknownReason::InvalidResultReason => {
                        erased.request_class[request]
                                == replay_layer::RetryClass::Uncontrolled
                            && exists|bad: replay_layer::InvalidValue| #![auto]
                                replay_layer::outcome_observation(
                                    records, request, current,
                                ) == Option::Some(
                                    replay_layer::Observation::InvalidResult(bad),
                                )
                    },
                }
        },
    }
}

// This is the reference-ordering half factored out of replay_layer's
// unknown_enabled rule. Keeping it separate lets UnknownCause expose the
// reason semantics while OutcomeEvidence retains the exact durable anchor.
pub open spec fn unknown_evidence_anchor(
    records: Seq<replay_layer::JournalRecord>,
    request: replay_layer::RequestId,
    attempt: Option<replay_layer::AttemptId>,
    reason: replay_layer::UnknownReason,
    evidence_ref: replay_layer::Lsn,
) -> bool {
    match attempt {
        Option::None => replay_layer::ref_is(
            evidence_ref, replay_layer::arm_lsn(records, request),
        ),
        Option::Some(current) => {
            &&& replay_layer::ref_is(
                evidence_ref,
                replay_layer::latest_evidence_lsn(records, request),
            )
            &&& match reason {
                replay_layer::UnknownReason::NonConclusiveFailure
                | replay_layer::UnknownReason::AmbiguousOutcome
                | replay_layer::UnknownReason::InvalidResultReason => {
                    replay_layer::ref_is(
                        evidence_ref,
                        replay_layer::outcome_lsn(
                            records, request, current,
                        ),
                    )
                },
                replay_layer::UnknownReason::Exhausted
                | replay_layer::UnknownReason::Recovery => true,
            }
        },
    }
}

pub open spec fn terminal_record_is_commit(
    indexed: IndexedTerminalRecord,
    request: replay_layer::RequestId,
    attempt: replay_layer::AttemptId,
    value: replay_layer::Value,
    outcome_ref: replay_layer::Lsn,
) -> bool {
    match indexed.record {
        replay_layer::JournalRecord::CommitRec {
            request: record_request,
            attempt: record_attempt,
            value: record_value,
            outcome_ref: record_outcome_ref,
            ..
        } => {
            record_request == request
                && record_attempt == attempt
                && record_value == value
                && record_outcome_ref == outcome_ref
        },
        replay_layer::JournalRecord::Authorize { .. }
        | replay_layer::JournalRecord::Revoke { .. }
        | replay_layer::JournalRecord::Prepare { .. }
        | replay_layer::JournalRecord::Arm { .. }
        | replay_layer::JournalRecord::Start { .. }
        | replay_layer::JournalRecord::Outcome { .. }
        | replay_layer::JournalRecord::FailRec { .. }
        | replay_layer::JournalRecord::UnknownRec { .. } => false,
    }
}

pub open spec fn terminal_record_is_fail(
    indexed: IndexedTerminalRecord,
    request: replay_layer::RequestId,
    attempt: replay_layer::AttemptId,
    outcome_ref: replay_layer::Lsn,
) -> bool {
    match indexed.record {
        replay_layer::JournalRecord::FailRec {
            request: record_request,
            attempt: record_attempt,
            outcome_ref: record_outcome_ref,
            ..
        } => {
            record_request == request
                && record_attempt == attempt
                && record_outcome_ref == outcome_ref
        },
        replay_layer::JournalRecord::Authorize { .. }
        | replay_layer::JournalRecord::Revoke { .. }
        | replay_layer::JournalRecord::Prepare { .. }
        | replay_layer::JournalRecord::Arm { .. }
        | replay_layer::JournalRecord::Start { .. }
        | replay_layer::JournalRecord::Outcome { .. }
        | replay_layer::JournalRecord::CommitRec { .. }
        | replay_layer::JournalRecord::UnknownRec { .. } => false,
    }
}

pub open spec fn terminal_record_is_unknown(
    indexed: IndexedTerminalRecord,
    request: replay_layer::RequestId,
    attempt: Option<replay_layer::AttemptId>,
    reason: replay_layer::UnknownReason,
    evidence_ref: replay_layer::Lsn,
) -> bool {
    match indexed.record {
        replay_layer::JournalRecord::UnknownRec {
            request: record_request,
            attempt: record_attempt,
            reason: record_reason,
            evidence_ref: record_evidence_ref,
            ..
        } => {
            record_request == request
                && record_attempt == attempt
                && record_reason == reason
                && record_evidence_ref == evidence_ref
        },
        replay_layer::JournalRecord::Authorize { .. }
        | replay_layer::JournalRecord::Revoke { .. }
        | replay_layer::JournalRecord::Prepare { .. }
        | replay_layer::JournalRecord::Arm { .. }
        | replay_layer::JournalRecord::Start { .. }
        | replay_layer::JournalRecord::Outcome { .. }
        | replay_layer::JournalRecord::CommitRec { .. }
        | replay_layer::JournalRecord::FailRec { .. } => false,
    }
}

pub open spec fn unknown_cause(
    cfg: config_layer::FullConfig,
    records: Seq<replay_layer::JournalRecord>,
    request: replay_layer::RequestId,
    attempt: Option<replay_layer::AttemptId>,
    reason: replay_layer::UnknownReason,
) -> bool {
    &&& replay_layer::journal_legal(
        config_layer::erase_config(cfg), records,
    )
    &&& exists|indexed: IndexedTerminalRecord,
                  evidence_ref: replay_layer::Lsn| {
        &&& terminal_record(records, request) == Option::Some(indexed)
        &&& terminal_record_is_unknown(
            indexed, request, attempt, reason, evidence_ref,
        )
        &&& unknown_reason_guard(
            cfg,
            records.take((indexed.lsn - 1) as int),
            request,
            attempt,
            reason,
        )
    }
}

pub open spec fn commit_outcome_evidence(
    records: Seq<replay_layer::JournalRecord>,
    request: replay_layer::RequestId,
    history: Seq<p0_layer::PhysicalEvent>,
    attempt: replay_layer::AttemptId,
    value: replay_layer::Value,
) -> bool {
    exists|indexed: IndexedTerminalRecord,
           outcome_ref: replay_layer::Lsn| {
        &&& terminal_record(records, request) == Option::Some(indexed)
        &&& terminal_record_is_commit(
            indexed, request, attempt, value, outcome_ref,
        )
        &&& outcome_record_at(
            records.take((indexed.lsn - 1) as int),
            outcome_ref,
            request,
            attempt,
            replay_layer::Observation::Success(value),
        )
        &&& delivery(history, request, attempt)
            == Option::Some(replay_layer::Observation::Success(value))
    }
}

pub open spec fn fail_outcome_evidence(
    records: Seq<replay_layer::JournalRecord>,
    request: replay_layer::RequestId,
    history: Seq<p0_layer::PhysicalEvent>,
    attempt: replay_layer::AttemptId,
) -> bool {
    exists|indexed: IndexedTerminalRecord,
           outcome_ref: replay_layer::Lsn| {
        &&& terminal_record(records, request) == Option::Some(indexed)
        &&& terminal_record_is_fail(
            indexed, request, attempt, outcome_ref,
        )
        &&& outcome_record_at(
            records.take((indexed.lsn - 1) as int),
            outcome_ref,
            request,
            attempt,
            replay_layer::Observation::Failure,
        )
        &&& delivery(history, request, attempt)
            == Option::Some(replay_layer::Observation::Failure)
    }
}

pub open spec fn unknown_outcome_evidence(
    cfg: config_layer::FullConfig,
    records: Seq<replay_layer::JournalRecord>,
    request: replay_layer::RequestId,
    attempt: Option<replay_layer::AttemptId>,
    reason: replay_layer::UnknownReason,
) -> bool {
    exists|indexed: IndexedTerminalRecord,
           evidence_ref: replay_layer::Lsn| {
        &&& terminal_record(records, request) == Option::Some(indexed)
        &&& terminal_record_is_unknown(
            indexed, request, attempt, reason, evidence_ref,
        )
        &&& replay_layer::structural_enabled(
            config_layer::erase_config(cfg),
            records.take((indexed.lsn - 1) as int),
            indexed.record,
        )
    }
}

pub open spec fn outcome_evidence(
    cfg: config_layer::FullConfig,
    records: Seq<replay_layer::JournalRecord>,
    request: replay_layer::RequestId,
    history: Seq<p0_layer::PhysicalEvent>,
    outcome: TerminalOutcome,
) -> bool {
    match outcome {
        TerminalOutcome::Commit { attempt, value } => {
            commit_outcome_evidence(
                records, request, history, attempt, value,
            )
        },
        TerminalOutcome::Fail { attempt } => {
            fail_outcome_evidence(
                records, request, history, attempt,
            )
        },
        TerminalOutcome::UnknownOutcome { attempt, reason } => {
            unknown_outcome_evidence(
                cfg, records, request, attempt, reason,
            )
        },
    }
}

pub open spec fn commit_outcome_compatible(
    cfg: config_layer::FullConfig,
    request: replay_layer::RequestId,
    history: Seq<p0_layer::PhysicalEvent>,
    attempt: replay_layer::AttemptId,
    value: replay_layer::Value,
) -> bool {
    delivery(history, request, attempt)
            == Option::Some(replay_layer::Observation::Success(value))
        && (cfg.request[request].retry_class
                != replay_layer::RetryClass::Uncontrolled
            || only_invoked_attempt(history, request, attempt))
}

pub open spec fn fail_outcome_compatible(
    cfg: config_layer::FullConfig,
    request: replay_layer::RequestId,
    history: Seq<p0_layer::PhysicalEvent>,
    attempt: replay_layer::AttemptId,
) -> bool {
    delivery(history, request, attempt)
            == Option::Some(replay_layer::Observation::Failure)
        && match cfg.request[request].retry_class {
            replay_layer::RetryClass::ReadOnly => true,
            replay_layer::RetryClass::Idempotent => {
                all_invocations_failed(history, request)
            },
            replay_layer::RetryClass::Deduplicated => {
                dedup_failure_resolved(history, request, attempt)
            },
            replay_layer::RetryClass::Uncontrolled => {
                single_failure(history, request, attempt)
            },
        }
}

pub open spec fn unknown_outcome_compatible(
    cfg: config_layer::FullConfig,
    records: Seq<replay_layer::JournalRecord>,
    request: replay_layer::RequestId,
    history: Seq<p0_layer::PhysicalEvent>,
    attempt: Option<replay_layer::AttemptId>,
    reason: replay_layer::UnknownReason,
) -> bool {
    unknown_cause(cfg, records, request, attempt, reason)
        && (cfg.request[request].retry_class
                != replay_layer::RetryClass::Uncontrolled
            || at_most_one_invoked_attempt(history, request))
}

pub open spec fn broker_outcome_compatible(
    cfg: config_layer::FullConfig,
    records: Seq<replay_layer::JournalRecord>,
    request: replay_layer::RequestId,
    history: Seq<p0_layer::PhysicalEvent>,
    outcome: TerminalOutcome,
) -> bool {
    match outcome {
        TerminalOutcome::Commit { attempt, value } => {
            commit_outcome_compatible(
                cfg, request, history, attempt, value,
            )
        },
        TerminalOutcome::Fail { attempt } => {
            fail_outcome_compatible(cfg, request, history, attempt)
        },
        TerminalOutcome::UnknownOutcome { attempt, reason } => {
            unknown_outcome_compatible(
                cfg, records, request, history, attempt, reason,
            )
        },
    }
}

pub open spec fn refines<X, I>(
    paper: t1_layer::PaperConfig<Adapter<X, I>>,
    request: replay_layer::RequestId,
    history: Seq<p0_layer::PhysicalEvent>,
    run: ExternalRun<X, I>,
    outcome: TerminalOutcome,
) -> bool {
    let cfg = t1_layer::paper_broker_config(paper);
    let adapter = paper.adapter;
    adapter_rely_trace(paper, request, history, run)
        && match outcome {
            TerminalOutcome::Commit { attempt, value } => {
                &&& delivery(history, request, attempt)
                    == Option::Some(
                        replay_layer::Observation::Success(value),
                    )
                &&& (adapter.result_spec)(
                    request, value, run,
                )
                &&& if cfg.request[request].retry_class
                        == replay_layer::RetryClass::ReadOnly {
                    (adapter.zero_effect)(
                        request, run,
                    )
                } else {
                    (adapter.one_effect)(
                        request, run,
                    )
                }
            },
            TerminalOutcome::Fail { attempt } => {
                delivery(history, request, attempt)
                        == Option::Some(replay_layer::Observation::Failure)
                    && (adapter.zero_effect)(
                        request, run,
                    )
            },
            TerminalOutcome::UnknownOutcome { .. } => {
                (adapter.zero_effect)(
                    request, run,
                ) || (adapter.one_effect)(
                    request, run,
                )
            },
        }
}

pub open spec fn adapter_success_sound<X, I>(
    paper: t1_layer::PaperConfig<Adapter<X, I>>,
) -> bool {
    let cfg = t1_layer::paper_broker_config(paper);
    let adapter = paper.adapter;
    forall|request: replay_layer::RequestId,
           history: Seq<p0_layer::PhysicalEvent>,
           run: ExternalRun<X, I>,
           attempt: replay_layer::AttemptId,
           value: replay_layer::Value| {
        &&& adapter_rely_trace(paper, request, history, run)
        &&& commit_outcome_compatible(
            cfg, request, history, attempt, value,
        )
    } ==> {
        &&& (adapter.result_spec)(request, value, run)
        &&& if cfg.request[request].retry_class
                == replay_layer::RetryClass::ReadOnly {
            (adapter.zero_effect)(request, run)
        } else {
            (adapter.one_effect)(request, run)
        }
    }
}

pub open spec fn adapter_resolved_failure_sound<X, I>(
    paper: t1_layer::PaperConfig<Adapter<X, I>>,
) -> bool {
    let cfg = t1_layer::paper_broker_config(paper);
    let adapter = paper.adapter;
    forall|request: replay_layer::RequestId,
           history: Seq<p0_layer::PhysicalEvent>,
           run: ExternalRun<X, I>,
           attempt: replay_layer::AttemptId| {
        &&& adapter_rely_trace(paper, request, history, run)
        &&& fail_outcome_compatible(cfg, request, history, attempt)
    } ==> (adapter.zero_effect)(request, run)
}

pub open spec fn adapter_effect_bounded<X, I>(
    paper: t1_layer::PaperConfig<Adapter<X, I>>,
) -> bool {
    let adapter = paper.adapter;
    forall|request: replay_layer::RequestId,
           history: Seq<p0_layer::PhysicalEvent>,
           run: ExternalRun<X, I>|
        adapter_rely_trace(paper, request, history, run) ==> {
            ||| (adapter.zero_effect)(request, run)
            ||| (adapter.one_effect)(request, run)
        }
}

pub open spec fn primitive_adapter_laws<X, I>(
    paper: t1_layer::PaperConfig<Adapter<X, I>>,
) -> bool {
    adapter_success_sound(paper)
        && adapter_resolved_failure_sound(paper)
        && adapter_effect_bounded(paper)
}

pub proof fn primitive_adapter_laws_imply_verified<X, I>(
    paper: t1_layer::PaperConfig<Adapter<X, I>>,
)
    requires primitive_adapter_laws(paper),
    ensures adapter_verified(paper),
{
    let cfg = t1_layer::paper_broker_config(paper);
    let adapter = paper.adapter;
    assert forall|request: replay_layer::RequestId,
                  records: Seq<replay_layer::JournalRecord>,
                  history: Seq<p0_layer::PhysicalEvent>,
                  run: ExternalRun<X, I>,
                  outcome: TerminalOutcome| {
        &&& replay_layer::journal_legal(
            config_layer::erase_config(cfg), records,
        )
        &&& adapter_rely_trace(paper, request, history, run)
        &&& outcome_evidence(cfg, records, request, history, outcome)
        &&& broker_outcome_compatible(
            cfg, records, request, history, outcome,
        )
    } implies refines(paper, request, history, run, outcome) by {
        match outcome {
            TerminalOutcome::Commit { attempt, value } => {
                assert(adapter_success_sound(paper));
            },
            TerminalOutcome::Fail { attempt } => {
                assert(adapter_resolved_failure_sound(paper));
            },
            TerminalOutcome::UnknownOutcome { .. } => {
                assert(adapter_effect_bounded(paper));
            },
        }
    }
}

pub open spec fn adapter_verified<X, I>(
    paper: t1_layer::PaperConfig<Adapter<X, I>>,
) -> bool {
    let cfg = t1_layer::paper_broker_config(paper);
    forall|request: replay_layer::RequestId,
           records: Seq<replay_layer::JournalRecord>,
           history: Seq<p0_layer::PhysicalEvent>,
           run: ExternalRun<X, I>,
           outcome: TerminalOutcome| {
        &&& replay_layer::journal_legal(
            config_layer::erase_config(cfg), records,
        )
        &&& adapter_rely_trace(
            paper, request, history, run,
        )
        &&& outcome_evidence(
            cfg, records, request, history, outcome,
        )
        &&& broker_outcome_compatible(
            cfg, records, request, history, outcome,
        )
    } ==> refines(
        paper, request, history, run, outcome,
    )
}

pub open spec fn per_request_effect_refinement<X, I>(
    paper: t1_layer::PaperConfig<Adapter<X, I>>,
    events: Seq<global_layer::GlobalEvent>,
    request: replay_layer::RequestId,
    run: ExternalRun<X, I>,
) -> bool {
    match terminal(events, request) {
        Option::None => true,
        Option::Some(outcome) => refines(
            paper,
            request,
            projection_layer::pi_adapter(events, request),
            run,
            outcome,
        ),
    }
}

pub open spec fn terminal_evidence_and_compatibility(
    cfg: config_layer::FullConfig,
    events: Seq<global_layer::GlobalEvent>,
    records: Seq<replay_layer::JournalRecord>,
    request: replay_layer::RequestId,
    outcome: TerminalOutcome,
) -> bool {
    let history = projection_layer::pi_adapter(events, request);
    outcome_evidence(cfg, records, request, history, outcome)
        && broker_outcome_compatible(
            cfg, records, request, history, outcome,
        )
}

pub open spec fn t6_s0_core_statement<X, I>(
    paper: t1_layer::PaperConfig<Adapter<X, I>>,
    events: Seq<global_layer::GlobalEvent>,
    broker: p0_layer::State,
    request: replay_layer::RequestId,
    run: ExternalRun<X, I>,
    outcome: TerminalOutcome,
) -> bool {
    let cfg = t1_layer::paper_broker_config(paper);
    ({
        &&& t1_layer::paper_config_wf(paper)
        &&& contract_layer::broker_contract_invariant(cfg, broker)
        &&& broker.core.evidence.records
            == projection_layer::pi_journal(events)
        &&& broker.physical.physical
            == projection_layer::pi_physical(events)
        &&& adapter_rely(paper, events, request, run)
        &&& terminal(events, request) == Option::Some(outcome)
    }) ==> terminal_evidence_and_compatibility(
        cfg,
        events,
        broker.core.evidence.records,
        request,
        outcome,
    )
}

pub open spec fn journal_t6_s0_statement<X, I>(
    paper: t1_layer::PaperConfig<Adapter<X, I>>,
    execution: journal_runtime_layer::JournalExecution,
    broker: p0_layer::State,
    request: replay_layer::RequestId,
    run: ExternalRun<X, I>,
    outcome: TerminalOutcome,
) -> bool {
    let cfg = t1_layer::paper_broker_config(paper);
    let final_state = execution.configs[execution.events.len() as int];
    ({
        &&& t1_layer::paper_config_wf(paper)
        &&& journal_runtime_layer::exec(cfg, execution)
        &&& journal_trace_layer::admissible_journal_trace(cfg, execution)
        &&& journal_trace_layer::trace_agreement(cfg, execution)
        &&& t2_representation_layer::representation(
            cfg, final_state, broker,
        )
        &&& adapter_rely(
            paper, execution.events, request, run,
        )
        &&& terminal(execution.events, request)
            == Option::Some(outcome)
    }) ==> terminal_evidence_and_compatibility(
        cfg,
        execution.events,
        final_state.evidence.records,
        request,
        outcome,
    )
}

pub open spec fn wal_t6_s0_statement<X, I>(
    paper: t1_layer::PaperConfig<Adapter<X, I>>,
    execution: wal_runtime_layer::WalExecution,
    broker: p0_layer::State,
    request: replay_layer::RequestId,
    run: ExternalRun<X, I>,
    outcome: TerminalOutcome,
) -> bool {
    let cfg = t1_layer::paper_broker_config(paper);
    let final_state = execution.configs[execution.events.len() as int];
    ({
        &&& t1_layer::paper_config_wf(paper)
        &&& wal_runtime_layer::exec(cfg, execution)
        &&& wal_trace_layer::admissible_wal_trace(cfg, execution)
        &&& wal_trace_layer::trace_agreement(cfg, execution)
        &&& t4_c0_layer::wal_broker_representation(
            cfg, final_state, broker,
        )
        &&& adapter_rely(
            paper, execution.events, request, run,
        )
        &&& terminal(execution.events, request)
            == Option::Some(outcome)
    }) ==> terminal_evidence_and_compatibility(
        cfg,
        execution.events,
        final_state.evidence.records,
        request,
        outcome,
    )
}

pub proof fn commit_outcome_evidence_unfolds(
    cfg: config_layer::FullConfig,
    records: Seq<replay_layer::JournalRecord>,
    request: replay_layer::RequestId,
    history: Seq<p0_layer::PhysicalEvent>,
    attempt: replay_layer::AttemptId,
    value: replay_layer::Value,
)
    ensures outcome_evidence(
        cfg,
        records,
        request,
        history,
        TerminalOutcome::Commit { attempt, value },
    ) == commit_outcome_evidence(
        records, request, history, attempt, value,
    ),
{
}

pub proof fn fail_outcome_evidence_unfolds(
    cfg: config_layer::FullConfig,
    records: Seq<replay_layer::JournalRecord>,
    request: replay_layer::RequestId,
    history: Seq<p0_layer::PhysicalEvent>,
    attempt: replay_layer::AttemptId,
)
    ensures outcome_evidence(
        cfg,
        records,
        request,
        history,
        TerminalOutcome::Fail { attempt },
    ) == fail_outcome_evidence(
        records, request, history, attempt,
    ),
{
}

pub proof fn unknown_outcome_evidence_unfolds(
    cfg: config_layer::FullConfig,
    records: Seq<replay_layer::JournalRecord>,
    request: replay_layer::RequestId,
    history: Seq<p0_layer::PhysicalEvent>,
    attempt: Option<replay_layer::AttemptId>,
    reason: replay_layer::UnknownReason,
)
    ensures outcome_evidence(
        cfg,
        records,
        request,
        history,
        TerminalOutcome::UnknownOutcome { attempt, reason },
    ) == unknown_outcome_evidence(
        cfg, records, request, attempt, reason,
    ),
{
}

pub proof fn unknown_enabled_decomposes(
    cfg: config_layer::FullConfig,
    records: Seq<replay_layer::JournalRecord>,
    request: replay_layer::RequestId,
    attempt: Option<replay_layer::AttemptId>,
    reason: replay_layer::UnknownReason,
    evidence_ref: replay_layer::Lsn,
)
    ensures replay_layer::unknown_enabled(
        config_layer::erase_config(cfg),
        records,
        request,
        attempt,
        reason,
        evidence_ref,
    ) == ({
        &&& unknown_reason_guard(
            cfg, records, request, attempt, reason,
        )
        &&& unknown_evidence_anchor(
            records, request, attempt, reason, evidence_ref,
        )
    }),
{
    match attempt {
        Option::None => {},
        Option::Some(_) => {
            match reason {
                replay_layer::UnknownReason::Exhausted => {},
                replay_layer::UnknownReason::Recovery => {},
                replay_layer::UnknownReason::NonConclusiveFailure => {},
                replay_layer::UnknownReason::AmbiguousOutcome => {},
                replay_layer::UnknownReason::InvalidResultReason => {},
            }
        },
    }
}

pub proof fn commit_outcome_compatibility_unfolds(
    cfg: config_layer::FullConfig,
    records: Seq<replay_layer::JournalRecord>,
    request: replay_layer::RequestId,
    history: Seq<p0_layer::PhysicalEvent>,
    attempt: replay_layer::AttemptId,
    value: replay_layer::Value,
)
    ensures broker_outcome_compatible(
        cfg,
        records,
        request,
        history,
        TerminalOutcome::Commit { attempt, value },
    ) == commit_outcome_compatible(
        cfg, request, history, attempt, value,
    ),
{
}

pub proof fn fail_outcome_compatibility_unfolds(
    cfg: config_layer::FullConfig,
    records: Seq<replay_layer::JournalRecord>,
    request: replay_layer::RequestId,
    history: Seq<p0_layer::PhysicalEvent>,
    attempt: replay_layer::AttemptId,
)
    ensures broker_outcome_compatible(
        cfg,
        records,
        request,
        history,
        TerminalOutcome::Fail { attempt },
    ) == fail_outcome_compatible(
        cfg, request, history, attempt,
    ),
{
}

pub proof fn unknown_outcome_compatibility_unfolds(
    cfg: config_layer::FullConfig,
    records: Seq<replay_layer::JournalRecord>,
    request: replay_layer::RequestId,
    history: Seq<p0_layer::PhysicalEvent>,
    attempt: Option<replay_layer::AttemptId>,
    reason: replay_layer::UnknownReason,
)
    ensures broker_outcome_compatible(
        cfg,
        records,
        request,
        history,
        TerminalOutcome::UnknownOutcome { attempt, reason },
    ) == unknown_outcome_compatible(
        cfg, records, request, history, attempt, reason,
    ),
{
}

pub proof fn terminal_record_empty(
    request: replay_layer::RequestId,
)
    ensures terminal_record(Seq::empty(), request).is_none(),
{
}

pub proof fn terminal_record_singleton(
    request: replay_layer::RequestId,
    record: replay_layer::JournalRecord,
)
    requires is_terminal_record_for(record, request),
    ensures terminal_record(Seq::empty().push(record), request)
        == Option::Some(IndexedTerminalRecord { lsn: 1, record }),
{
    match record {
        replay_layer::JournalRecord::CommitRec {
            request: record_request, ..
        } => {
            assert(record_request == request);
        },
        replay_layer::JournalRecord::FailRec {
            request: record_request, ..
        } => {
            assert(record_request == request);
        },
        replay_layer::JournalRecord::UnknownRec {
            request: record_request, ..
        } => {
            assert(record_request == request);
        },
        replay_layer::JournalRecord::Authorize { .. }
        | replay_layer::JournalRecord::Revoke { .. }
        | replay_layer::JournalRecord::Prepare { .. }
        | replay_layer::JournalRecord::Arm { .. }
        | replay_layer::JournalRecord::Start { .. }
        | replay_layer::JournalRecord::Outcome { .. } => {
            assert(false);
        },
    }
    let records = Seq::empty().push(record);
    assert(records.drop_last() =~= Seq::empty());
    assert(records.last() == record);
    replay_layer::terminal_count_push(Seq::empty(), request, record);
    assert(replay_layer::terminal_count(records, request) == 1);
    assert(latest_terminal_record(records, request)
        == Option::Some(IndexedTerminalRecord { lsn: 1, record }));
}

pub proof fn terminal_record_duplicate_rejected(
    request: replay_layer::RequestId,
    first: replay_layer::JournalRecord,
    second: replay_layer::JournalRecord,
)
    requires
        is_terminal_record_for(first, request),
        is_terminal_record_for(second, request),
    ensures terminal_record(
        Seq::empty().push(first).push(second), request,
    ).is_none(),
{
    match first {
        replay_layer::JournalRecord::CommitRec {
            request: record_request, ..
        }
        | replay_layer::JournalRecord::FailRec {
            request: record_request, ..
        }
        | replay_layer::JournalRecord::UnknownRec {
            request: record_request, ..
        } => assert(record_request == request),
        replay_layer::JournalRecord::Authorize { .. }
        | replay_layer::JournalRecord::Revoke { .. }
        | replay_layer::JournalRecord::Prepare { .. }
        | replay_layer::JournalRecord::Arm { .. }
        | replay_layer::JournalRecord::Start { .. }
        | replay_layer::JournalRecord::Outcome { .. } => assert(false),
    }
    match second {
        replay_layer::JournalRecord::CommitRec {
            request: record_request, ..
        }
        | replay_layer::JournalRecord::FailRec {
            request: record_request, ..
        }
        | replay_layer::JournalRecord::UnknownRec {
            request: record_request, ..
        } => assert(record_request == request),
        replay_layer::JournalRecord::Authorize { .. }
        | replay_layer::JournalRecord::Revoke { .. }
        | replay_layer::JournalRecord::Prepare { .. }
        | replay_layer::JournalRecord::Arm { .. }
        | replay_layer::JournalRecord::Start { .. }
        | replay_layer::JournalRecord::Outcome { .. } => assert(false),
    }
    let empty = Seq::empty();
    let prefix = empty.push(first);
    let records = prefix.push(second);
    replay_layer::terminal_count_push(empty, request, first);
    replay_layer::terminal_count_push(prefix, request, second);
    assert(replay_layer::terminal_count(records, request) == 2);
}

pub proof fn invoke_delivery_history_sanity(
    request: replay_layer::RequestId,
    attempt: replay_layer::AttemptId,
    call: config_layer::CallDescriptor,
    observation: replay_layer::Observation,
)
    ensures {
        let history = Seq::empty().push(
            p0_layer::PhysicalEvent::Invoke {
                request,
                attempt,
                call,
                journal_cut: 0,
                ack_cut: 0,
            },
        ).push(p0_layer::PhysicalEvent::Delivered {
            request,
            attempt,
            observation,
            journal_cut: 0,
        });
        invoked(history, request, attempt)
            && delivery(history, request, attempt)
                == Option::Some(observation)
    },
{
    let invoke = p0_layer::PhysicalEvent::Invoke {
        request,
        attempt,
        call,
        journal_cut: 0,
        ack_cut: 0,
    };
    let delivered = p0_layer::PhysicalEvent::Delivered {
        request,
        attempt,
        observation,
        journal_cut: 0,
    };
    let empty = Seq::empty();
    let prefix = empty.push(invoke);
    let history = prefix.push(delivered);
    p1_layer::invoke_count_push(empty, invoke, request, attempt);
    p1_layer::invoke_count_push(prefix, delivered, request, attempt);
    p1_layer::delivery_count_push(empty, invoke, request, attempt);
    p1_layer::delivery_count_push(prefix, delivered, request, attempt);
    assert(history.drop_last() =~= prefix);
    assert(history.last() == delivered);
}

pub proof fn duplicate_delivery_rejected(
    request: replay_layer::RequestId,
    attempt: replay_layer::AttemptId,
    first_observation: replay_layer::Observation,
    second_observation: replay_layer::Observation,
)
    ensures {
        let history = Seq::empty().push(
            p0_layer::PhysicalEvent::Delivered {
                request,
                attempt,
                observation: first_observation,
                journal_cut: 0,
            },
        ).push(p0_layer::PhysicalEvent::Delivered {
            request,
            attempt,
            observation: second_observation,
            journal_cut: 0,
        });
        delivery(history, request, attempt).is_none()
    },
{
    let first = p0_layer::PhysicalEvent::Delivered {
        request,
        attempt,
        observation: first_observation,
        journal_cut: 0,
    };
    let second = p0_layer::PhysicalEvent::Delivered {
        request,
        attempt,
        observation: second_observation,
        journal_cut: 0,
    };
    let empty = Seq::empty();
    let prefix = empty.push(first);
    let history = prefix.push(second);
    p1_layer::delivery_count_push(empty, first, request, attempt);
    p1_layer::delivery_count_push(prefix, second, request, attempt);
    assert(p1_layer::delivery_count(history, request, attempt) == 2);
}

pub proof fn adapter_rely_is_projected_rely<X, I>(
    paper: t1_layer::PaperConfig<Adapter<X, I>>,
    events: Seq<global_layer::GlobalEvent>,
    request: replay_layer::RequestId,
    run: ExternalRun<X, I>,
)
    ensures adapter_rely(paper, events, request, run)
        == adapter_rely_trace(
            paper,
            request,
            projection_layer::pi_adapter(events, request),
            run,
        ),
{
}

pub proof fn adapter_verified_applies<X, I>(
    paper: t1_layer::PaperConfig<Adapter<X, I>>,
    request: replay_layer::RequestId,
    records: Seq<replay_layer::JournalRecord>,
    history: Seq<p0_layer::PhysicalEvent>,
    run: ExternalRun<X, I>,
    outcome: TerminalOutcome,
)
    requires
        adapter_verified(paper),
        replay_layer::journal_legal(
            config_layer::erase_config(
                t1_layer::paper_broker_config(paper),
            ),
            records,
        ),
        adapter_rely_trace(paper, request, history, run),
        outcome_evidence(
            t1_layer::paper_broker_config(paper),
            records,
            request,
            history,
            outcome,
        ),
        broker_outcome_compatible(
            t1_layer::paper_broker_config(paper),
            records,
            request,
            history,
            outcome,
        ),
    ensures refines(paper, request, history, run, outcome),
{
}

} // verus!
