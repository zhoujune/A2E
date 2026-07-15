use vstd::prelude::*;

#[path = "t6_terminal_definitions.rs"]
pub mod t6_d0_layer;

verus! {

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

// T6-E0 proves the evidence half of the frozen terminal bridge.  It is
// intentionally adapter-independent and does not claim outcome compatibility.

pub open spec fn t6_e0_full_history_statement(
    cfg: config_layer::FullConfig,
    records: Seq<replay_layer::JournalRecord>,
    history: Seq<p0_layer::PhysicalEvent>,
    request: replay_layer::RequestId,
    outcome: TerminalOutcome,
) -> bool {
    ({
        &&& replay_layer::journal_legal(
            config_layer::erase_config(cfg), records,
        )
        &&& p1_layer::physical_unique(history)
        &&& p2_layer::durable_outcomes_follow_deliveries(
            records, history,
        )
        &&& terminal_from_records(records, request)
            == Option::Some(outcome)
    }) ==> outcome_evidence(
        cfg, records, request, history, outcome,
    )
}

pub proof fn latest_terminal_record_sound(
    records: Seq<replay_layer::JournalRecord>,
    request: replay_layer::RequestId,
    indexed: IndexedTerminalRecord,
)
    requires latest_terminal_record(records, request)
        == Option::Some(indexed),
    ensures
        1 <= indexed.lsn,
        indexed.lsn <= records.len(),
        records[(indexed.lsn - 1) as int] == indexed.record,
        is_terminal_record_for(indexed.record, request),
    decreases records.len(),
{
    if records.len() > 0 {
        let prefix = records.drop_last();
        if is_terminal_record_for(records.last(), request) {
            assert(indexed.lsn == records.len());
            assert(records[(records.len() - 1) as int] == records.last());
        } else {
            latest_terminal_record_sound(prefix, request, indexed);
            assert(indexed.lsn <= prefix.len());
            assert(prefix[(indexed.lsn - 1) as int]
                == records[(indexed.lsn - 1) as int]);
        }
    }
}

pub proof fn terminal_record_sound(
    records: Seq<replay_layer::JournalRecord>,
    request: replay_layer::RequestId,
    indexed: IndexedTerminalRecord,
)
    requires terminal_record(records, request)
        == Option::Some(indexed),
    ensures
        replay_layer::terminal_count(records, request) == 1,
        1 <= indexed.lsn,
        indexed.lsn <= records.len(),
        records[(indexed.lsn - 1) as int] == indexed.record,
        is_terminal_record_for(indexed.record, request),
{
    latest_terminal_record_sound(records, request, indexed);
}

pub proof fn outcome_projection_is_exact(
    records: Seq<replay_layer::JournalRecord>,
    request: replay_layer::RequestId,
    attempt: replay_layer::AttemptId,
    observation: replay_layer::Observation,
    lsn: replay_layer::Lsn,
)
    requires
        replay_layer::outcome_lsn(records, request, attempt)
            == Option::Some(lsn),
        replay_layer::outcome_observation(records, request, attempt)
            == Option::Some(observation),
    ensures outcome_record_at(
        records, lsn, request, attempt, observation,
    ),
    decreases records.len(),
{
    let prefix = records.drop_last();
    match records.last() {
        replay_layer::JournalRecord::Outcome {
            request: record_request,
            attempt: record_attempt,
            observation: record_observation,
            ..
        } => {
            if record_request == request && record_attempt == attempt {
                assert(lsn == records.len());
                assert(record_observation == observation);
                assert(records[(lsn - 1) as int] == records.last());
            } else {
                outcome_projection_is_exact(
                    prefix, request, attempt, observation, lsn,
                );
                assert(prefix[(lsn - 1) as int]
                    == records[(lsn - 1) as int]);
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
            outcome_projection_is_exact(
                prefix, request, attempt, observation, lsn,
            );
            assert(prefix[(lsn - 1) as int]
                == records[(lsn - 1) as int]);
        },
    }
}

pub proof fn durable_outcomes_follow_deliveries_take(
    records: Seq<replay_layer::JournalRecord>,
    history: Seq<p0_layer::PhysicalEvent>,
    length: nat,
)
    requires
        p2_layer::durable_outcomes_follow_deliveries(records, history),
        length <= records.len(),
    ensures p2_layer::durable_outcomes_follow_deliveries(
        records.take(length as int), history,
    ),
    decreases records.len(),
{
    if length == records.len() {
        assert(records.take(length as int) =~= records);
    } else {
        let prefix = records.drop_last();
        assert(records.len() > 0);
        durable_outcomes_follow_deliveries_take(
            prefix, history, length,
        );
        assert(prefix.take(length as int)
            =~= records.take(length as int));
    }
}

pub proof fn physical_unique_bounds_delivery_count(
    history: Seq<p0_layer::PhysicalEvent>,
    request: replay_layer::RequestId,
    attempt: replay_layer::AttemptId,
)
    requires p1_layer::physical_unique(history),
    ensures p1_layer::delivery_count(history, request, attempt) <= 1,
    decreases history.len(),
{
    if history.len() > 0 {
        let prefix = history.drop_last();
        physical_unique_bounds_delivery_count(prefix, request, attempt);
        match history.last() {
            p0_layer::PhysicalEvent::Delivered {
                request: record_request,
                attempt: record_attempt,
                ..
            } => {
                if record_request == request && record_attempt == attempt {
                    assert(p1_layer::delivery_count(
                        prefix, request, attempt,
                    ) == 0);
                }
            },
            p0_layer::PhysicalEvent::Invoke { .. } => {},
        }
    }
}

pub proof fn unique_delivery_observation_is_latest(
    history: Seq<p0_layer::PhysicalEvent>,
    request: replay_layer::RequestId,
    attempt: replay_layer::AttemptId,
    observation: replay_layer::Observation,
    witness_index: nat,
    witness_cut: nat,
)
    requires
        p1_layer::physical_unique(history),
        witness_index < history.len(),
        history[witness_index as int]
            == (p0_layer::PhysicalEvent::Delivered {
                request,
                attempt,
                observation,
                journal_cut: witness_cut,
            }),
    ensures latest_delivery_observation(
        history, request, attempt,
    ) == Option::Some(observation),
    decreases history.len(),
{
    let prefix = history.drop_last();
    match history.last() {
        p0_layer::PhysicalEvent::Delivered {
            request: last_request,
            attempt: last_attempt,
            observation: last_observation,
            journal_cut: last_cut,
        } if last_request == request && last_attempt == attempt => {
            let last_index = (history.len() - 1) as nat;
            assert(p1_layer::is_delivery_for(
                history[witness_index as int], request, attempt,
            ));
            assert(p1_layer::is_delivery_for(
                history[last_index as int], request, attempt,
            ));
            contract_layer::unique_delivery_indices(
                history, request, attempt, witness_index, last_index,
            );
            assert(witness_index == last_index);
            assert(history[last_index as int] == history.last());
            assert(last_observation == observation);
            assert(last_cut == witness_cut);
        },
        p0_layer::PhysicalEvent::Invoke { .. }
        | p0_layer::PhysicalEvent::Delivered { .. } => {
            assert(witness_index < prefix.len()) by {
                if witness_index == prefix.len() {
                    assert(history[witness_index as int] == history.last());
                    assert(p1_layer::is_delivery_for(
                        history.last(), request, attempt,
                    ));
                }
            }
            assert(prefix[witness_index as int]
                == history[witness_index as int]);
            unique_delivery_observation_is_latest(
                prefix,
                request,
                attempt,
                observation,
                witness_index,
                witness_cut,
            );
        },
    }
}

pub proof fn delivery_before_lsn_is_selected(
    history: Seq<p0_layer::PhysicalEvent>,
    request: replay_layer::RequestId,
    attempt: replay_layer::AttemptId,
    observation: replay_layer::Observation,
    lsn: replay_layer::Lsn,
)
    requires
        p1_layer::physical_unique(history),
        p2_layer::delivery_before_lsn(
            history, request, attempt, observation, lsn,
        ),
    ensures delivery(history, request, attempt)
        == Option::Some(observation),
{
    let witness_index = choose|index: nat|
        exists|journal_cut: nat| {
            &&& index < history.len()
            &&& #[trigger] history[index as int]
                == (p0_layer::PhysicalEvent::Delivered {
                    request,
                    attempt,
                    observation,
                    journal_cut,
                })
            &&& journal_cut < lsn
        };
    let witness_cut = choose|journal_cut: nat| {
        &&& witness_index < history.len()
        &&& #[trigger] history[witness_index as int]
            == (p0_layer::PhysicalEvent::Delivered {
                request,
                attempt,
                observation,
                journal_cut,
            })
        &&& journal_cut < lsn
    };
    assert(p1_layer::is_delivery_for(
        history[witness_index as int], request, attempt,
    ));
    contract_layer::delivery_at_implies_count_positive(
        history, request, attempt, witness_index,
    );
    physical_unique_bounds_delivery_count(history, request, attempt);
    assert(p1_layer::delivery_count(history, request, attempt) == 1);
    unique_delivery_observation_is_latest(
        history,
        request,
        attempt,
        observation,
        witness_index,
        witness_cut,
    );
}

pub proof fn terminal_outcome_has_full_history_evidence(
    cfg: config_layer::FullConfig,
    records: Seq<replay_layer::JournalRecord>,
    history: Seq<p0_layer::PhysicalEvent>,
    request: replay_layer::RequestId,
    outcome: TerminalOutcome,
)
    requires
        replay_layer::journal_legal(
            config_layer::erase_config(cfg), records,
        ),
        p1_layer::physical_unique(history),
        p2_layer::durable_outcomes_follow_deliveries(
            records, history,
        ),
        terminal_from_records(records, request)
            == Option::Some(outcome),
    ensures outcome_evidence(
        cfg, records, request, history, outcome,
    ),
{
    match terminal_record(records, request) {
        Option::None => {},
        Option::Some(indexed) => {
            terminal_record_sound(records, request, indexed);
            let terminal_index = (indexed.lsn - 1) as int;
            let prefix = records.take(terminal_index);
            assert(0 <= terminal_index < records.len());
            assert(records[terminal_index] == indexed.record);
            assert(replay_layer::structural_enabled(
                config_layer::erase_config(cfg),
                prefix,
                indexed.record,
            ));
            match outcome {
                TerminalOutcome::Commit { attempt, value } => {
                    match indexed.record {
                        replay_layer::JournalRecord::CommitRec {
                            request: record_request,
                            attempt: record_attempt,
                            value: record_value,
                            outcome_ref,
                            ..
                        } => {
                            assert(record_request == request);
                            assert(record_attempt == attempt);
                            assert(record_value == value);
                            assert(replay_layer::outcome_lsn(
                                prefix, request, attempt,
                            ) == Option::Some(outcome_ref));
                            assert(replay_layer::outcome_observation(
                                prefix, request, attempt,
                            ) == Option::Some(
                                replay_layer::Observation::Success(value),
                            ));
                            outcome_projection_is_exact(
                                prefix,
                                request,
                                attempt,
                                replay_layer::Observation::Success(value),
                                outcome_ref,
                            );
                            durable_outcomes_follow_deliveries_take(
                                records, history, terminal_index as nat,
                            );
                            p2_layer::outcome_projection_has_delivery(
                                prefix,
                                history,
                                request,
                                attempt,
                                replay_layer::Observation::Success(value),
                                outcome_ref,
                            );
                            delivery_before_lsn_is_selected(
                                history,
                                request,
                                attempt,
                                replay_layer::Observation::Success(value),
                                outcome_ref,
                            );
                            assert(terminal_record_is_commit(
                                indexed,
                                request,
                                attempt,
                                value,
                                outcome_ref,
                            ));
                        },
                        replay_layer::JournalRecord::Authorize { .. }
                        | replay_layer::JournalRecord::Revoke { .. }
                        | replay_layer::JournalRecord::Prepare { .. }
                        | replay_layer::JournalRecord::Arm { .. }
                        | replay_layer::JournalRecord::Start { .. }
                        | replay_layer::JournalRecord::Outcome { .. }
                        | replay_layer::JournalRecord::FailRec { .. }
                        | replay_layer::JournalRecord::UnknownRec { .. } => {
                            assert(false);
                        },
                    }
                },
                TerminalOutcome::Fail { attempt } => {
                    match indexed.record {
                        replay_layer::JournalRecord::FailRec {
                            request: record_request,
                            attempt: record_attempt,
                            outcome_ref,
                            ..
                        } => {
                            assert(record_request == request);
                            assert(record_attempt == attempt);
                            assert(replay_layer::outcome_lsn(
                                prefix, request, attempt,
                            ) == Option::Some(outcome_ref));
                            assert(replay_layer::outcome_observation(
                                prefix, request, attempt,
                            ) == Option::Some(
                                replay_layer::Observation::Failure,
                            ));
                            outcome_projection_is_exact(
                                prefix,
                                request,
                                attempt,
                                replay_layer::Observation::Failure,
                                outcome_ref,
                            );
                            durable_outcomes_follow_deliveries_take(
                                records, history, terminal_index as nat,
                            );
                            p2_layer::outcome_projection_has_delivery(
                                prefix,
                                history,
                                request,
                                attempt,
                                replay_layer::Observation::Failure,
                                outcome_ref,
                            );
                            delivery_before_lsn_is_selected(
                                history,
                                request,
                                attempt,
                                replay_layer::Observation::Failure,
                                outcome_ref,
                            );
                            assert(terminal_record_is_fail(
                                indexed, request, attempt, outcome_ref,
                            ));
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
                TerminalOutcome::UnknownOutcome { attempt, reason } => {
                    match indexed.record {
                        replay_layer::JournalRecord::UnknownRec {
                            request: record_request,
                            attempt: record_attempt,
                            reason: record_reason,
                            evidence_ref,
                            ..
                        } => {
                            assert(record_request == request);
                            assert(record_attempt == attempt);
                            assert(record_reason == reason);
                            assert(terminal_record_is_unknown(
                                indexed,
                                request,
                                attempt,
                                reason,
                                evidence_ref,
                            ));
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
        },
    }
}

pub proof fn adapter_projection_delivery_count(
    history: Seq<p0_layer::PhysicalEvent>,
    request: replay_layer::RequestId,
    attempt: replay_layer::AttemptId,
)
    ensures p1_layer::delivery_count(
        projection_layer::adapter_from_physical(history, request),
        request,
        attempt,
    ) == p1_layer::delivery_count(history, request, attempt),
    decreases history.len(),
{
    if history.len() > 0 {
        let prefix = history.drop_last();
        let projected_prefix = projection_layer::adapter_from_physical(
            prefix, request,
        );
        let event = history.last();
        adapter_projection_delivery_count(prefix, request, attempt);
        assert(prefix.push(event) =~= history);
        p1_layer::delivery_count_push(
            prefix, event, request, attempt,
        );
        match event {
            event @ p0_layer::PhysicalEvent::Invoke {
                request: event_request, ..
            } => {
                if event_request == request {
                    assert(projection_layer::adapter_from_physical(
                        history, request,
                    ) =~= projected_prefix.push(event));
                    p1_layer::delivery_count_push(
                        projected_prefix, event, request, attempt,
                    );
                } else {
                    assert(projection_layer::adapter_from_physical(
                        history, request,
                    ) =~= projected_prefix);
                }
            },
            event @ p0_layer::PhysicalEvent::Delivered {
                request: event_request, ..
            } => {
                if event_request == request {
                    assert(projection_layer::adapter_from_physical(
                        history, request,
                    ) =~= projected_prefix.push(event));
                    p1_layer::delivery_count_push(
                        projected_prefix, event, request, attempt,
                    );
                } else {
                    assert(projection_layer::adapter_from_physical(
                        history, request,
                    ) =~= projected_prefix);
                }
            },
        }
    }
}

pub proof fn latest_delivery_observation_push(
    history: Seq<p0_layer::PhysicalEvent>,
    event: p0_layer::PhysicalEvent,
    request: replay_layer::RequestId,
    attempt: replay_layer::AttemptId,
)
    ensures latest_delivery_observation(
        history.push(event), request, attempt,
    ) == match event {
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
            latest_delivery_observation(history, request, attempt)
        },
    },
{
    assert(history.push(event).drop_last() =~= history);
    assert(history.push(event).last() == event);
}

pub proof fn adapter_projection_latest_delivery(
    history: Seq<p0_layer::PhysicalEvent>,
    request: replay_layer::RequestId,
    attempt: replay_layer::AttemptId,
)
    ensures latest_delivery_observation(
        projection_layer::adapter_from_physical(history, request),
        request,
        attempt,
    ) == latest_delivery_observation(history, request, attempt),
    decreases history.len(),
{
    if history.len() > 0 {
        let prefix = history.drop_last();
        let projected_prefix = projection_layer::adapter_from_physical(
            prefix, request,
        );
        let event = history.last();
        adapter_projection_latest_delivery(prefix, request, attempt);
        assert(prefix.push(event) =~= history);
        latest_delivery_observation_push(
            prefix, event, request, attempt,
        );
        latest_delivery_observation_push(
            projected_prefix, event, request, attempt,
        );
        match event {
            event @ p0_layer::PhysicalEvent::Invoke {
                request: event_request, ..
            } => {
                assert(latest_delivery_observation(
                    history, request, attempt,
                ) == latest_delivery_observation(
                    prefix, request, attempt,
                ));
                if event_request == request {
                    assert(projection_layer::adapter_from_physical(
                        history, request,
                    ) =~= projected_prefix.push(event));
                    assert(latest_delivery_observation(
                        projected_prefix.push(event), request, attempt,
                    ) == latest_delivery_observation(
                        projected_prefix, request, attempt,
                    ));
                } else {
                    assert(projection_layer::adapter_from_physical(
                        history, request,
                    ) =~= projected_prefix);
                }
            },
            event @ p0_layer::PhysicalEvent::Delivered {
                request: event_request,
                attempt: event_attempt,
                observation: event_observation,
                ..
            } => {
                if event_request == request {
                    assert(projection_layer::adapter_from_physical(
                        history, request,
                    ) =~= projected_prefix.push(event));
                } else {
                    assert(event_request != request);
                    assert(projection_layer::adapter_from_physical(
                        history, request,
                    ) =~= projected_prefix);
                }
                if event_request == request && event_attempt == attempt {
                    assert(latest_delivery_observation(
                        history, request, attempt,
                    ) == Option::Some(event_observation));
                    assert(latest_delivery_observation(
                        projected_prefix.push(event), request, attempt,
                    ) == Option::Some(event_observation));
                } else {
                    assert(latest_delivery_observation(
                        history, request, attempt,
                    ) == latest_delivery_observation(
                        prefix, request, attempt,
                    ));
                    if event_request == request {
                        assert(latest_delivery_observation(
                            projected_prefix.push(event), request, attempt,
                        ) == latest_delivery_observation(
                            projected_prefix, request, attempt,
                        ));
                    }
                }
            },
        }
    }
}

pub proof fn delivery_projection(
    history: Seq<p0_layer::PhysicalEvent>,
    request: replay_layer::RequestId,
    attempt: replay_layer::AttemptId,
)
    ensures delivery(
        projection_layer::adapter_from_physical(history, request),
        request,
        attempt,
    ) == delivery(history, request, attempt),
{
    adapter_projection_delivery_count(history, request, attempt);
    adapter_projection_latest_delivery(history, request, attempt);
}

pub proof fn outcome_evidence_projects_to_adapter_history(
    cfg: config_layer::FullConfig,
    records: Seq<replay_layer::JournalRecord>,
    history: Seq<p0_layer::PhysicalEvent>,
    request: replay_layer::RequestId,
    outcome: TerminalOutcome,
)
    requires outcome_evidence(
        cfg, records, request, history, outcome,
    ),
    ensures outcome_evidence(
        cfg,
        records,
        request,
        projection_layer::adapter_from_physical(history, request),
        outcome,
    ),
{
    match outcome {
        TerminalOutcome::Commit { attempt, .. }
        | TerminalOutcome::Fail { attempt } => {
            delivery_projection(history, request, attempt);
        },
        TerminalOutcome::UnknownOutcome { .. } => {},
    }
}

pub proof fn terminal_outcome_has_evidence(
    cfg: config_layer::FullConfig,
    records: Seq<replay_layer::JournalRecord>,
    history: Seq<p0_layer::PhysicalEvent>,
    request: replay_layer::RequestId,
    outcome: TerminalOutcome,
)
    requires
        replay_layer::journal_legal(
            config_layer::erase_config(cfg), records,
        ),
        p1_layer::physical_unique(history),
        p2_layer::durable_outcomes_follow_deliveries(
            records, history,
        ),
        terminal_from_records(records, request)
            == Option::Some(outcome),
    ensures outcome_evidence(
        cfg,
        records,
        request,
        projection_layer::adapter_from_physical(history, request),
        outcome,
    ),
{
    terminal_outcome_has_full_history_evidence(
        cfg, records, history, request, outcome,
    );
    outcome_evidence_projects_to_adapter_history(
        cfg, records, history, request, outcome,
    );
}

pub proof fn broker_terminal_outcome_has_evidence(
    cfg: config_layer::FullConfig,
    broker: p0_layer::State,
    request: replay_layer::RequestId,
    outcome: TerminalOutcome,
)
    requires
        contract_layer::broker_contract_invariant(cfg, broker),
        terminal_from_records(
            broker.core.evidence.records, request,
        ) == Option::Some(outcome),
    ensures outcome_evidence(
        cfg,
        broker.core.evidence.records,
        request,
        projection_layer::adapter_from_physical(
            broker.physical.physical, request,
        ),
        outcome,
    ),
{
    assert(contract_layer::replay_agreement_clause(cfg, broker));
    assert(contract_layer::physical_causality_clause(cfg, broker));
    terminal_outcome_has_evidence(
        cfg,
        broker.core.evidence.records,
        broker.physical.physical,
        request,
        outcome,
    );
}

pub open spec fn t6_e0_core_statement(
    cfg: config_layer::FullConfig,
    events: Seq<global_layer::GlobalEvent>,
    broker: p0_layer::State,
    request: replay_layer::RequestId,
    outcome: TerminalOutcome,
) -> bool {
    ({
        &&& contract_layer::broker_contract_invariant(cfg, broker)
        &&& broker.core.evidence.records
            == projection_layer::pi_journal(events)
        &&& broker.physical.physical
            == projection_layer::pi_physical(events)
        &&& terminal(events, request) == Option::Some(outcome)
    }) ==> outcome_evidence(
        cfg,
        broker.core.evidence.records,
        request,
        projection_layer::pi_adapter(events, request),
        outcome,
    )
}

pub proof fn event_terminal_outcome_has_evidence(
    cfg: config_layer::FullConfig,
    events: Seq<global_layer::GlobalEvent>,
    broker: p0_layer::State,
    request: replay_layer::RequestId,
    outcome: TerminalOutcome,
)
    requires
        contract_layer::broker_contract_invariant(cfg, broker),
        broker.core.evidence.records
            == projection_layer::pi_journal(events),
        broker.physical.physical
            == projection_layer::pi_physical(events),
        terminal(events, request) == Option::Some(outcome),
    ensures outcome_evidence(
        cfg,
        broker.core.evidence.records,
        request,
        projection_layer::pi_adapter(events, request),
        outcome,
    ),
{
    assert(terminal_from_records(
        broker.core.evidence.records, request,
    ) == Option::Some(outcome));
    broker_terminal_outcome_has_evidence(
        cfg, broker, request, outcome,
    );
    assert(projection_layer::adapter_from_physical(
        broker.physical.physical, request,
    ) == projection_layer::pi_adapter(events, request));
}

pub proof fn t6_e0_core(
    cfg: config_layer::FullConfig,
    events: Seq<global_layer::GlobalEvent>,
    broker: p0_layer::State,
    request: replay_layer::RequestId,
    outcome: TerminalOutcome,
)
    ensures t6_e0_core_statement(
        cfg, events, broker, request, outcome,
    ),
{
    if contract_layer::broker_contract_invariant(cfg, broker)
        && broker.core.evidence.records
            == projection_layer::pi_journal(events)
        && broker.physical.physical
            == projection_layer::pi_physical(events)
        && terminal(events, request) == Option::Some(outcome)
    {
        event_terminal_outcome_has_evidence(
            cfg, events, broker, request, outcome,
        );
    }
}

pub proof fn t6_e0_full_history(
    cfg: config_layer::FullConfig,
    records: Seq<replay_layer::JournalRecord>,
    history: Seq<p0_layer::PhysicalEvent>,
    request: replay_layer::RequestId,
    outcome: TerminalOutcome,
)
    ensures t6_e0_full_history_statement(
        cfg, records, history, request, outcome,
    ),
{
    if replay_layer::journal_legal(
            config_layer::erase_config(cfg), records,
        )
        && p1_layer::physical_unique(history)
        && p2_layer::durable_outcomes_follow_deliveries(records, history)
        && terminal_from_records(records, request)
            == Option::Some(outcome)
    {
        terminal_outcome_has_full_history_evidence(
            cfg, records, history, request, outcome,
        );
    }
}

} // verus!
