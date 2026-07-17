use vstd::prelude::*;

#[path = "t6_terminal_evidence.rs"]
pub mod t6_e0_layer;

verus! {

use t6_e0_layer::*;
use t6_e0_layer::t6_d0_layer;
use t6_d0_layer::*;
use t6_d0_layer::t5_c0_layer;
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

// T6-C0 proves the compatibility half of the frozen terminal bridge.  It
// consumes the exact terminal evidence established by T6-E0 but deliberately
// leaves adapter-effect refinement to later adapter checkpoints and backend
// wrappers to T6-S0.

pub open spec fn t6_c0_core_statement<X, I>(
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
    }) ==> broker_outcome_compatible(
        cfg,
        broker.core.evidence.records,
        request,
        projection_layer::pi_adapter(events, request),
        outcome,
    )
}

pub proof fn adapter_projection_invoke_count(
    history: Seq<p0_layer::PhysicalEvent>,
    request: replay_layer::RequestId,
    attempt: replay_layer::AttemptId,
)
    ensures p1_layer::invoke_count(
        projection_layer::adapter_from_physical(history, request),
        request,
        attempt,
    ) == p1_layer::invoke_count(history, request, attempt),
    decreases history.len(),
{
    if history.len() > 0 {
        let prefix = history.drop_last();
        let projected = projection_layer::adapter_from_physical(
            prefix, request,
        );
        let event = history.last();
        adapter_projection_invoke_count(prefix, request, attempt);
        assert(prefix.push(event) =~= history);
        p1_layer::invoke_count_push(prefix, event, request, attempt);
        match event {
            event @ p0_layer::PhysicalEvent::Invoke {
                request: event_request, ..
            }
            | event @ p0_layer::PhysicalEvent::Delivered {
                request: event_request, ..
            } => {
                if event_request == request {
                    assert(projection_layer::adapter_from_physical(
                        history, request,
                    ) =~= projected.push(event));
                    p1_layer::invoke_count_push(
                        projected, event, request, attempt,
                    );
                } else {
                    assert(projection_layer::adapter_from_physical(
                        history, request,
                    ) =~= projected);
                }
            },
        }
    }
}

pub proof fn adapter_projection_request_invoke_count(
    history: Seq<p0_layer::PhysicalEvent>,
    request: replay_layer::RequestId,
)
    ensures p2_layer::request_invoke_count(
        projection_layer::adapter_from_physical(history, request),
        request,
    ) == p2_layer::request_invoke_count(history, request),
    decreases history.len(),
{
    if history.len() > 0 {
        let prefix = history.drop_last();
        let projected = projection_layer::adapter_from_physical(
            prefix, request,
        );
        let event = history.last();
        adapter_projection_request_invoke_count(prefix, request);
        assert(prefix.push(event) =~= history);
        p2_layer::request_invoke_count_push(prefix, event, request);
        match event {
            event @ p0_layer::PhysicalEvent::Invoke {
                request: event_request, ..
            }
            | event @ p0_layer::PhysicalEvent::Delivered {
                request: event_request, ..
            } => {
                if event_request == request {
                    assert(projection_layer::adapter_from_physical(
                        history, request,
                    ) =~= projected.push(event));
                    p2_layer::request_invoke_count_push(
                        projected, event, request,
                    );
                } else {
                    assert(projection_layer::adapter_from_physical(
                        history, request,
                    ) =~= projected);
                }
            },
        }
    }
}

pub proof fn attempt_invokes_le_request_invokes(
    history: Seq<p0_layer::PhysicalEvent>,
    request: replay_layer::RequestId,
    attempt: replay_layer::AttemptId,
)
    ensures p1_layer::invoke_count(history, request, attempt)
        <= p2_layer::request_invoke_count(history, request),
    decreases history.len(),
{
    if history.len() > 0 {
        let prefix = history.drop_last();
        let event = history.last();
        attempt_invokes_le_request_invokes(prefix, request, attempt);
        assert(prefix.push(event) =~= history);
        p1_layer::invoke_count_push(prefix, event, request, attempt);
        p2_layer::request_invoke_count_push(prefix, event, request);
        match event {
            p0_layer::PhysicalEvent::Invoke {
                request: event_request,
                attempt: event_attempt,
                ..
            } => {
                if event_request == request && event_attempt == attempt {
                    assert(p1_layer::is_invoke_for(
                        event, request, attempt,
                    ));
                }
            },
            p0_layer::PhysicalEvent::Delivered { .. } => {},
        }
    }
}

pub proof fn selected_delivery_implies_invoked(
    history: Seq<p0_layer::PhysicalEvent>,
    request: replay_layer::RequestId,
    attempt: replay_layer::AttemptId,
    observation: replay_layer::Observation,
)
    requires
        p1_layer::physical_ordered(history),
        delivery(history, request, attempt)
            == Option::Some(observation),
    ensures invoked(history, request, attempt),
{
    if !invoked(history, request, attempt) {
        assert(p1_layer::invoke_count(
            history, request, attempt,
        ) == 0);
        p1_layer::no_delivery_without_invoke(
            history, request, attempt,
        );
        assert(p1_layer::delivery_count(
            history, request, attempt,
        ) == 1);
        assert(false);
    }
}

pub proof fn acknowledged_invocation_refinement_at(
    cfg: config_layer::FullConfig,
    records: Seq<replay_layer::JournalRecord>,
    history: Seq<p0_layer::PhysicalEvent>,
    index: nat,
)
    requires
        p2_layer::acknowledged_invocation_refinement(
            cfg, records, history,
        ),
        index < history.len(),
    ensures p2_layer::invoke_refinement_witness(
        cfg, records, history[index as int],
    ),
    decreases history.len(),
{
    let prefix = history.drop_last();
    if index < prefix.len() {
        assert(prefix[index as int] == history[index as int]);
        acknowledged_invocation_refinement_at(
            cfg, records, prefix, index,
        );
    } else {
        assert(index == history.len() - 1);
        assert(history[index as int] == history.last());
    }
}

pub proof fn selected_delivery_has_witness(
    history: Seq<p0_layer::PhysicalEvent>,
    request: replay_layer::RequestId,
    attempt: replay_layer::AttemptId,
    observation: replay_layer::Observation,
)
    requires
        p1_layer::physical_unique(history),
        delivery(history, request, attempt)
            == Option::Some(observation),
    ensures exists|index: nat, journal_cut: nat| #![auto] {
        &&& index < history.len()
        &&& history[index as int]
            == (p0_layer::PhysicalEvent::Delivered {
                request,
                attempt,
                observation,
                journal_cut,
            })
    },
{
    p1_layer::delivery_index_sound(history, request, attempt);
    match p1_layer::delivery_index(history, request, attempt) {
        Option::None => {
            assert(p1_layer::delivery_count(
                history, request, attempt,
            ) == 1);
            assert(false);
        },
        Option::Some(index) => {
            match history[index as int] {
                p0_layer::PhysicalEvent::Delivered {
                    request: event_request,
                    attempt: event_attempt,
                    observation: event_observation,
                    journal_cut,
                } => {
                    assert(event_request == request);
                    assert(event_attempt == attempt);
                    unique_delivery_observation_is_latest(
                        history,
                        request,
                        attempt,
                        event_observation,
                        index,
                        journal_cut,
                    );
                    assert(event_observation == observation);
                    assert(exists|witness_index: nat, witness_cut: nat| #![auto] {
                        &&& witness_index < history.len()
                        &&& history[witness_index as int]
                            == (p0_layer::PhysicalEvent::Delivered {
                                request,
                                attempt,
                                observation,
                                journal_cut: witness_cut,
                            })
                    }) by {
                        let witness_index = index;
                        let witness_cut = journal_cut;
                    }
                },
                p0_layer::PhysicalEvent::Invoke { .. } => {
                    assert(false);
                },
            }
        },
    }
}

pub proof fn dedup_failure_is_resolved(
    history: Seq<p0_layer::PhysicalEvent>,
    request: replay_layer::RequestId,
    attempt: replay_layer::AttemptId,
)
    requires
        p1_layer::physical_unique(history),
        delivery(history, request, attempt)
            == Option::Some(replay_layer::Observation::Failure),
        deduplicated_observations_consistent(history, request),
    ensures dedup_failure_resolved(history, request, attempt),
{
    selected_delivery_has_witness(
        history,
        request,
        attempt,
        replay_layer::Observation::Failure,
    );
    let failure_index = choose|index: nat|
        exists|journal_cut: nat| {
            &&& index < history.len()
            &&& #[trigger] history[index as int]
                == (p0_layer::PhysicalEvent::Delivered {
                    request,
                    attempt,
                    observation: replay_layer::Observation::Failure,
                    journal_cut,
                })
        };
    let failure_cut = choose|journal_cut: nat| {
        &&& failure_index < history.len()
        &&& #[trigger] history[failure_index as int]
            == (p0_layer::PhysicalEvent::Delivered {
                request,
                attempt,
                observation: replay_layer::Observation::Failure,
                journal_cut,
            })
    };
    // Keep the concrete Failure event explicit so the pairwise consistency
    // quantifier below is anchored at an actual history index.
    assert(history[failure_index as int]
        == (p0_layer::PhysicalEvent::Delivered {
            request,
            attempt,
            observation: replay_layer::Observation::Failure,
            journal_cut: failure_cut,
        }));
    if contains_success_or_invalid(history, request) {
        let conflict = choose|index: int| 0 <= index < history.len()
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
            };
        assert(0 <= conflict < history.len());
        assert(0 <= failure_index < history.len());
        assert(deduplicated_observations_consistent(history, request));
        assert(observations_dedup_compatible(
            replay_layer::Observation::Failure,
            match history[conflict] {
                p0_layer::PhysicalEvent::Delivered {
                    observation, ..
                } => observation,
                p0_layer::PhysicalEvent::Invoke { .. } => {
                    replay_layer::Observation::Failure
                },
            },
        ));
        match history[conflict] {
            p0_layer::PhysicalEvent::Delivered {
                request: event_request,
                observation: replay_layer::Observation::Success(_),
                ..
            }
            | p0_layer::PhysicalEvent::Delivered {
                request: event_request,
                observation: replay_layer::Observation::InvalidResult(_),
                ..
            } => {
                assert(event_request == request);
                assert(false);
            },
            p0_layer::PhysicalEvent::Invoke { .. }
            | p0_layer::PhysicalEvent::Delivered { .. } => {
                assert(false);
            },
        }
    }
}

pub proof fn fail_terminal_sets_failed_projection(
    records: Seq<replay_layer::JournalRecord>,
    request: replay_layer::RequestId,
    indexed: IndexedTerminalRecord,
    attempt: replay_layer::AttemptId,
    outcome_ref: replay_layer::Lsn,
)
    requires
        terminal_record(records, request) == Option::Some(indexed),
        terminal_record_is_fail(
            indexed, request, attempt, outcome_ref,
        ),
    ensures replay_layer::failed_projection(records, request)
        == Option::Some(attempt),
    decreases records.len(),
{
    terminal_record_sound(records, request, indexed);
    let prefix = records.drop_last();
    let record = records.last();
    replay_layer::terminal_count_push(prefix, request, record);
    if is_terminal_record_for(record, request) {
        assert(latest_terminal_record(records, request)
            == Option::Some(IndexedTerminalRecord {
                lsn: records.len(),
                record,
            }));
        assert(indexed == IndexedTerminalRecord {
            lsn: records.len(),
            record,
        });
        match record {
            replay_layer::JournalRecord::FailRec {
                request: event_request,
                attempt: event_attempt,
                ..
            } => {
                assert(event_request == request);
                assert(event_attempt == attempt);
            },
            replay_layer::JournalRecord::Authorize { .. }
            | replay_layer::JournalRecord::Revoke { .. }
            | replay_layer::JournalRecord::Prepare { .. }
            | replay_layer::JournalRecord::Arm { .. }
            | replay_layer::JournalRecord::Start { .. }
            | replay_layer::JournalRecord::Outcome { .. }
            | replay_layer::JournalRecord::CommitRec { .. }
            | replay_layer::JournalRecord::UnknownRec { .. } => {
                assert(false);
            },
        }
    } else {
        assert(replay_layer::terminal_count(prefix, request) == 1);
        assert(latest_terminal_record(records, request)
            == latest_terminal_record(prefix, request));
        assert(terminal_record(prefix, request)
            == Option::Some(indexed));
        fail_terminal_sets_failed_projection(
            prefix, request, indexed, attempt, outcome_ref,
        );
        match record {
            replay_layer::JournalRecord::FailRec {
                request: event_request, ..
            } => {
                assert(event_request != request);
            },
            replay_layer::JournalRecord::Authorize { .. }
            | replay_layer::JournalRecord::Revoke { .. }
            | replay_layer::JournalRecord::Prepare { .. }
            | replay_layer::JournalRecord::Arm { .. }
            | replay_layer::JournalRecord::Start { .. }
            | replay_layer::JournalRecord::Outcome { .. }
            | replay_layer::JournalRecord::CommitRec { .. }
            | replay_layer::JournalRecord::UnknownRec { .. } => {},
        }
    }
}

pub proof fn unknown_evidence_implies_unknown_cause(
    cfg: config_layer::FullConfig,
    records: Seq<replay_layer::JournalRecord>,
    request: replay_layer::RequestId,
    attempt: Option<replay_layer::AttemptId>,
    reason: replay_layer::UnknownReason,
)
    requires
        replay_layer::journal_legal(
            config_layer::erase_config(cfg), records,
        ),
        unknown_outcome_evidence(
            cfg, records, request, attempt, reason,
        ),
    ensures unknown_cause(
        cfg, records, request, attempt, reason,
    ),
{
    match terminal_record(records, request) {
        Option::None => {
            assert(false);
        },
        Option::Some(indexed) => {
            let prefix = records.take((indexed.lsn - 1) as int);
            match indexed.record {
                replay_layer::JournalRecord::UnknownRec {
                    request: event_request,
                    attempt: event_attempt,
                    reason: event_reason,
                    evidence_ref,
                    ..
                } => {
                    assert(event_request == request);
                    assert(event_attempt == attempt);
                    assert(event_reason == reason);
                    assert(terminal_record_is_unknown(
                        indexed,
                        request,
                        attempt,
                        reason,
                        evidence_ref,
                    ));
                    assert(replay_layer::structural_enabled(
                        config_layer::erase_config(cfg),
                        prefix,
                        indexed.record,
                    ));
                    assert(replay_layer::unknown_enabled(
                        config_layer::erase_config(cfg),
                        prefix,
                        request,
                        attempt,
                        reason,
                        evidence_ref,
                    ));
                    unknown_enabled_decomposes(
                        cfg,
                        prefix,
                        request,
                        attempt,
                        reason,
                        evidence_ref,
                    );
                    assert(unknown_reason_guard(
                        cfg, prefix, request, attempt, reason,
                    ));
                    assert(exists|witness: IndexedTerminalRecord,
                                  witness_ref: replay_layer::Lsn| {
                        &&& terminal_record(records, request)
                            == Option::Some(witness)
                        &&& terminal_record_is_unknown(
                            witness,
                            request,
                            attempt,
                            reason,
                            witness_ref,
                        )
                        &&& unknown_reason_guard(
                            cfg,
                            records.take((witness.lsn - 1) as int),
                            request,
                            attempt,
                            reason,
                        )
                    }) by {
                        let witness = indexed;
                        let witness_ref = evidence_ref;
                    }
                },
                replay_layer::JournalRecord::Authorize { .. }
                | replay_layer::JournalRecord::Revoke { .. }
                | replay_layer::JournalRecord::Prepare { .. }
                | replay_layer::JournalRecord::Arm { .. }
                | replay_layer::JournalRecord::Start { .. }
                | replay_layer::JournalRecord::Outcome { .. }
                | replay_layer::JournalRecord::CommitRec { .. }
                | replay_layer::JournalRecord::FailRec { .. } => {
                    assert(false);
                },
            }
        },
    }
}

pub proof fn invoked_attempt_has_durable_range(
    cfg: config_layer::FullConfig,
    records: Seq<replay_layer::JournalRecord>,
    history: Seq<p0_layer::PhysicalEvent>,
    request: replay_layer::RequestId,
    attempt: replay_layer::AttemptId,
)
    requires
        config_layer::full_config_wf(cfg),
        p2_layer::acknowledged_invocation_refinement(
            cfg, records, history,
        ),
        replay_layer::journal_legal(
            config_layer::erase_config(cfg), records,
        ),
        invoked(history, request, attempt),
    ensures
        1 <= attempt,
        attempt <= replay_layer::started_count(records, request),
{
    p1_layer::invoke_index_sound(history, request, attempt);
    match p1_layer::invoke_index(history, request, attempt) {
        Option::None => {
            assert(p1_layer::invoke_count(
                history, request, attempt,
            ) == 0);
            assert(false);
        },
        Option::Some(index) => {
            acknowledged_invocation_refinement_at(
                cfg, records, history, index,
            );
            match history[index as int] {
                p0_layer::PhysicalEvent::Invoke {
                    request: event_request,
                    attempt: event_attempt,
                    ack_cut,
                    ..
                } => {
                    assert(event_request == request);
                    assert(event_attempt == attempt);
                    assert(p2_layer::invoke_refinement_witness(
                        cfg, records, history[index as int],
                    ));
                    assert(ack_cut <= records.len());
                    assert(p2_layer::acknowledged_start_authorized(
                        cfg,
                        records.take(ack_cut as int),
                        request,
                        attempt,
                    ));
                    assert(replay_layer::start_lsn(
                        records.take(ack_cut as int),
                        request,
                        attempt,
                    ).is_some());
                    p1_layer::start_lsn_some_implies_count_positive(
                        records.take(ack_cut as int),
                        request,
                        attempt,
                    );
                    p1_layer::start_count_take_le(
                        records, request, attempt, ack_cut,
                    );
                    assert(replay_layer::start_count(
                        records, request, attempt,
                    ) > 0);
                    config_layer::erasure_is_replay_well_formed(cfg);
                    replay_layer::replay_start_exact(
                        config_layer::erase_config(cfg), records,
                    );
                    assert(replay_layer::start_count(
                        records, request, attempt,
                    ) == if 1 <= attempt
                            && attempt <= replay_layer::started_count(
                                records, request,
                            ) {
                        1nat
                    } else {
                        0nat
                    });
                },
                p0_layer::PhysicalEvent::Delivered { .. } => {
                    assert(false);
                },
            }
        },
    }
}

pub proof fn idempotent_fail_evidence_is_conclusive(
    cfg: config_layer::FullConfig,
    broker: p0_layer::State,
    request: replay_layer::RequestId,
    history: Seq<p0_layer::PhysicalEvent>,
    attempt: replay_layer::AttemptId,
)
    requires
        config_layer::full_config_wf(cfg),
        contract_layer::broker_contract_invariant(cfg, broker),
        cfg.request[request].retry_class
            == replay_layer::RetryClass::Idempotent,
        fail_outcome_evidence(
            broker.core.evidence.records,
            request,
            history,
            attempt,
        ),
    ensures replay_layer::all_attempts_failed(
        broker.core.evidence.records, request,
    ),
{
    let records = broker.core.evidence.records;
    let erased = config_layer::erase_config(cfg);
    match terminal_record(records, request) {
        Option::None => {
            assert(false);
        },
        Option::Some(indexed) => {
            match indexed.record {
                replay_layer::JournalRecord::FailRec {
                    request: event_request,
                    attempt: event_attempt,
                    outcome_ref,
                    ..
                } => {
                    assert(event_request == request);
                    assert(event_attempt == attempt);
                    assert(terminal_record_is_fail(
                        indexed, request, attempt, outcome_ref,
                    ));
                    fail_terminal_sets_failed_projection(
                        records,
                        request,
                        indexed,
                        attempt,
                        outcome_ref,
                    );
                },
                replay_layer::JournalRecord::Authorize { .. }
                | replay_layer::JournalRecord::Revoke { .. }
                | replay_layer::JournalRecord::Prepare { .. }
                | replay_layer::JournalRecord::Arm { .. }
                | replay_layer::JournalRecord::Start { .. }
                | replay_layer::JournalRecord::Outcome { .. }
                | replay_layer::JournalRecord::CommitRec { .. }
                | replay_layer::JournalRecord::UnknownRec { .. } => {
                    assert(false);
                },
            }
        },
    }
    assert(contract_layer::terminal_uniqueness_clause(cfg, broker));
    assert(replay_layer::replay_terminal_fields_ok(erased, records));
    assert(replay_layer::replay(erased, records).failed_attempt[request]
        == Option::Some(attempt));
    assert(contract_layer::value_provenance_clause(cfg, broker));
    assert(replay_layer::replay_terminal_provenance_ok(
        erased, records,
    ));
    assert(replay_layer::failure_conclusive(
        erased, records, request,
    ));
    assert(erased.request_class[request]
        == replay_layer::RetryClass::Idempotent);
}

pub proof fn idempotent_invocation_has_failure_delivery(
    cfg: config_layer::FullConfig,
    broker: p0_layer::State,
    request: replay_layer::RequestId,
    attempt: replay_layer::AttemptId,
)
    requires
        config_layer::full_config_wf(cfg),
        contract_layer::broker_contract_invariant(cfg, broker),
        replay_layer::all_attempts_failed(
            broker.core.evidence.records, request,
        ),
        invoked(broker.physical.physical, request, attempt),
    ensures delivery(
        projection_layer::adapter_from_physical(
            broker.physical.physical, request,
        ),
        request,
        attempt,
    ) == Option::Some(replay_layer::Observation::Failure),
{
    let records = broker.core.evidence.records;
    let history = broker.physical.physical;
    assert(contract_layer::replay_agreement_clause(cfg, broker));
    assert(contract_layer::physical_causality_clause(cfg, broker));
    invoked_attempt_has_durable_range(
        cfg, records, history, request, attempt,
    );
    assert(replay_layer::outcome_observation(
        records, request, attempt,
    ) == Option::Some(replay_layer::Observation::Failure));
    p3_layer::outcome_observation_has_lsn(
        records,
        request,
        attempt,
        replay_layer::Observation::Failure,
    );
    let lsn = choose|lsn: replay_layer::Lsn|
        replay_layer::outcome_lsn(records, request, attempt)
            == Option::Some(lsn);
    p2_layer::outcome_projection_has_delivery(
        records,
        history,
        request,
        attempt,
        replay_layer::Observation::Failure,
        lsn,
    );
    delivery_before_lsn_is_selected(
        history,
        request,
        attempt,
        replay_layer::Observation::Failure,
        lsn,
    );
    delivery_projection(history, request, attempt);
}

pub proof fn idempotent_failure_covers_all_invocations(
    cfg: config_layer::FullConfig,
    broker: p0_layer::State,
    request: replay_layer::RequestId,
    history: Seq<p0_layer::PhysicalEvent>,
    terminal_attempt: replay_layer::AttemptId,
)
    requires
        config_layer::full_config_wf(cfg),
        contract_layer::broker_contract_invariant(cfg, broker),
        history == projection_layer::adapter_from_physical(
            broker.physical.physical, request,
        ),
        cfg.request[request].retry_class
            == replay_layer::RetryClass::Idempotent,
        fail_outcome_evidence(
            broker.core.evidence.records,
            request,
            history,
            terminal_attempt,
        ),
    ensures all_invocations_failed(history, request),
{
    idempotent_fail_evidence_is_conclusive(
        cfg, broker, request, history, terminal_attempt,
    );
    assert forall|attempt: replay_layer::AttemptId|
        #[trigger] invoked(history, request, attempt)
            implies delivery(history, request, attempt)
                == Option::Some(replay_layer::Observation::Failure) by {
        adapter_projection_invoke_count(
            broker.physical.physical, request, attempt,
        );
        assert(invoked(
            broker.physical.physical, request, attempt,
        ));
        idempotent_invocation_has_failure_delivery(
            cfg, broker, request, attempt,
        );
    }
}

pub proof fn uncontrolled_history_has_at_most_one_invocation(
    cfg: config_layer::FullConfig,
    broker: p0_layer::State,
    request: replay_layer::RequestId,
    history: Seq<p0_layer::PhysicalEvent>,
)
    requires
        contract_layer::broker_contract_invariant(cfg, broker),
        history == projection_layer::adapter_from_physical(
            broker.physical.physical, request,
        ),
        cfg.request[request].retry_class
            == replay_layer::RetryClass::Uncontrolled,
    ensures at_most_one_invoked_attempt(history, request),
{
    assert(contract_layer::retry_discipline_clause(cfg, broker));
    assert(p2_layer::aggregate_retry_bounds(cfg, broker));
    assert(config_layer::erase_config(cfg).request_class[request]
        == replay_layer::RetryClass::Uncontrolled);
    adapter_projection_request_invoke_count(
        broker.physical.physical, request,
    );
}

pub proof fn uncontrolled_selected_delivery_is_only_invocation(
    cfg: config_layer::FullConfig,
    broker: p0_layer::State,
    request: replay_layer::RequestId,
    history: Seq<p0_layer::PhysicalEvent>,
    attempt: replay_layer::AttemptId,
    observation: replay_layer::Observation,
)
    requires
        contract_layer::broker_contract_invariant(cfg, broker),
        history == projection_layer::adapter_from_physical(
            broker.physical.physical, request,
        ),
        cfg.request[request].retry_class
            == replay_layer::RetryClass::Uncontrolled,
        p1_layer::physical_ordered(history),
        delivery(history, request, attempt)
            == Option::Some(observation),
    ensures only_invoked_attempt(history, request, attempt),
{
    uncontrolled_history_has_at_most_one_invocation(
        cfg, broker, request, history,
    );
    selected_delivery_implies_invoked(
        history, request, attempt, observation,
    );
    attempt_invokes_le_request_invokes(
        history, request, attempt,
    );
    assert(p2_layer::request_invoke_count(history, request) > 0);
    assert(p2_layer::request_invoke_count(history, request) == 1);
}

pub proof fn event_terminal_outcome_is_compatible<X, I>(
    paper: t1_layer::PaperConfig<Adapter<X, I>>,
    events: Seq<global_layer::GlobalEvent>,
    broker: p0_layer::State,
    request: replay_layer::RequestId,
    run: ExternalRun<X, I>,
    outcome: TerminalOutcome,
)
    requires
        t1_layer::paper_config_wf(paper),
        contract_layer::broker_contract_invariant(
            t1_layer::paper_broker_config(paper), broker,
        ),
        broker.core.evidence.records
            == projection_layer::pi_journal(events),
        broker.physical.physical
            == projection_layer::pi_physical(events),
        adapter_rely(paper, events, request, run),
        terminal(events, request) == Option::Some(outcome),
    ensures broker_outcome_compatible(
        t1_layer::paper_broker_config(paper),
        broker.core.evidence.records,
        request,
        projection_layer::pi_adapter(events, request),
        outcome,
    ),
{
    let cfg = t1_layer::paper_broker_config(paper);
    let records = broker.core.evidence.records;
    let history = projection_layer::pi_adapter(events, request);
    assert(config_layer::full_config_wf(cfg));
    assert(history == projection_layer::adapter_from_physical(
        broker.physical.physical, request,
    ));
    assert(adapter_rely_trace(paper, request, history, run));
    assert(p1_layer::physical_unique(history));
    assert(p1_layer::physical_ordered(history));
    event_terminal_outcome_has_evidence(
        cfg, events, broker, request, outcome,
    );
    match outcome {
        TerminalOutcome::Commit { attempt, value } => {
            assert(commit_outcome_evidence(
                records, request, history, attempt, value,
            ));
            assert(delivery(history, request, attempt)
                == Option::Some(
                    replay_layer::Observation::Success(value),
                ));
            if cfg.request[request].retry_class
                    == replay_layer::RetryClass::Uncontrolled {
                uncontrolled_selected_delivery_is_only_invocation(
                    cfg,
                    broker,
                    request,
                    history,
                    attempt,
                    replay_layer::Observation::Success(value),
                );
            }
            commit_outcome_compatibility_unfolds(
                cfg, records, request, history, attempt, value,
            );
        },
        TerminalOutcome::Fail { attempt } => {
            assert(fail_outcome_evidence(
                records, request, history, attempt,
            ));
            assert(delivery(history, request, attempt)
                == Option::Some(replay_layer::Observation::Failure));
            match cfg.request[request].retry_class {
                replay_layer::RetryClass::ReadOnly => {},
                replay_layer::RetryClass::Idempotent => {
                    idempotent_failure_covers_all_invocations(
                        cfg, broker, request, history, attempt,
                    );
                },
                replay_layer::RetryClass::Deduplicated => {
                    assert(deduplicated_observations_consistent(
                        history, request,
                    ));
                    dedup_failure_is_resolved(
                        history, request, attempt,
                    );
                },
                replay_layer::RetryClass::Uncontrolled => {
                    uncontrolled_selected_delivery_is_only_invocation(
                        cfg,
                        broker,
                        request,
                        history,
                        attempt,
                        replay_layer::Observation::Failure,
                    );
                    assert(single_failure(history, request, attempt));
                },
            }
            fail_outcome_compatibility_unfolds(
                cfg, records, request, history, attempt,
            );
        },
        TerminalOutcome::UnknownOutcome { attempt, reason } => {
            assert(unknown_outcome_evidence(
                cfg, records, request, attempt, reason,
            ));
            assert(contract_layer::replay_agreement_clause(cfg, broker));
            unknown_evidence_implies_unknown_cause(
                cfg, records, request, attempt, reason,
            );
            if cfg.request[request].retry_class
                    == replay_layer::RetryClass::Uncontrolled {
                uncontrolled_history_has_at_most_one_invocation(
                    cfg, broker, request, history,
                );
            }
            unknown_outcome_compatibility_unfolds(
                cfg,
                records,
                request,
                history,
                attempt,
                reason,
            );
        },
    }
}

pub proof fn t6_c0_core<X, I>(
    paper: t1_layer::PaperConfig<Adapter<X, I>>,
    events: Seq<global_layer::GlobalEvent>,
    broker: p0_layer::State,
    request: replay_layer::RequestId,
    run: ExternalRun<X, I>,
    outcome: TerminalOutcome,
)
    ensures t6_c0_core_statement(
        paper, events, broker, request, run, outcome,
    ),
{
    let cfg = t1_layer::paper_broker_config(paper);
    if t1_layer::paper_config_wf(paper)
        && contract_layer::broker_contract_invariant(cfg, broker)
        && broker.core.evidence.records
            == projection_layer::pi_journal(events)
        && broker.physical.physical
            == projection_layer::pi_physical(events)
        && adapter_rely(paper, events, request, run)
        && terminal(events, request) == Option::Some(outcome)
    {
        event_terminal_outcome_is_compatible(
            paper, events, broker, request, run, outcome,
        );
    }
}

} // verus!
