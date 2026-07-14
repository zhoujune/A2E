use vstd::prelude::*;

#[path = "t1_broker_physical_refinement.rs"]
pub mod p2_layer;

verus! {

use p2_layer::p1_layer;
use p1_layer::p0_layer;
use p0_layer::config_layer;
use config_layer::broker_layer as record_layer;
use record_layer::query_layer;
use record_layer::query_layer::c1_layer::replay_layer;

// B2-P3 closes the terminal-source portion of the physical Broker model.
// Commit sources are the only terminal sources stored in ghost state.  Failed
// and Unknown provenance are instead derived from the durable Journal and P2's
// exact Outcome-to-Delivered refinement; in particular, no failure_source map
// and no claim that a Recovery Unknown lacks physical activity are introduced.

pub open spec fn commit_source_agreement(
    cfg: config_layer::FullConfig,
    state: p0_layer::State,
) -> bool {
    let erased = config_layer::erase_config(cfg);
    forall|request: replay_layer::RequestId| {
        let source = #[trigger] state.physical.commit_source[request];
        match state.core.broker.durable.committed[request] {
            Option::None => source.is_none(),
            Option::Some(committed) => {
                erased.valid_results.contains((request, committed.value))
                    && p1_layer::source_is_delivery(
                        state.physical.physical,
                        source,
                        request,
                        committed.attempt,
                        replay_layer::Observation::Success(committed.value),
                    )
            },
        }
    }
}

pub open spec fn failed_physical_provenance(
    cfg: config_layer::FullConfig,
    state: p0_layer::State,
) -> bool {
    let erased = config_layer::erase_config(cfg);
    let durable = state.core.broker.durable;
    let records = state.core.evidence.records;
    let history = state.physical.physical;
    forall|request: replay_layer::RequestId| {
        match #[trigger] durable.failed_attempt[request] {
            Option::None => true,
            Option::Some(attempt) => {
                query_layer::d_latest(durable, request) == Option::Some(attempt)
                    && query_layer::d_outcome(durable, request, attempt)
                        == Option::Some(replay_layer::Observation::Failure)
                    && query_layer::d_failure_conclusive(
                        erased, durable, request,
                    )
                    && exists|lsn: replay_layer::Lsn| #![auto] {
                        &&& replay_layer::outcome_lsn(
                            records, request, attempt,
                        )
                            == Option::Some(lsn)
                        &&& p2_layer::delivery_before_lsn(
                            history,
                            request,
                            attempt,
                            replay_layer::Observation::Failure,
                            lsn,
                        )
                    }
            },
        }
    }
}

// Unknown provenance intentionally remains a durable statement.  The
// Journal's UnknownRec and its prefix guard are witnessed, but no physical
// absence property is asserted for Recovery Unknown.
pub open spec fn durable_unknown_provenance(
    cfg: config_layer::FullConfig,
    state: p0_layer::State,
) -> bool {
    replay_layer::unknown_terminal_provenance_ok(
        config_layer::erase_config(cfg), state.core.evidence.records,
    )
}

pub open spec fn durable_terminal_provenance(
    cfg: config_layer::FullConfig,
    state: p0_layer::State,
) -> bool {
    let erased = config_layer::erase_config(cfg);
    let records = state.core.evidence.records;
    replay_layer::replay_terminal_fields_ok(erased, records)
        && replay_layer::replay_terminal_provenance_ok(erased, records)
        && replay_layer::unknown_records_are_prefix_valid(erased, records)
        && replay_layer::unknown_terminal_provenance_ok(erased, records)
}

pub open spec fn p3_invariant(
    cfg: config_layer::FullConfig,
    state: p0_layer::State,
) -> bool {
    p2_layer::p2_invariant(cfg, state)
        && commit_source_agreement(cfg, state)
}

pub proof fn source_is_delivery_history_push(
    history: Seq<p0_layer::PhysicalEvent>,
    event: p0_layer::PhysicalEvent,
    source: Option<p0_layer::PhysicalIndex>,
    request: replay_layer::RequestId,
    attempt: replay_layer::AttemptId,
    observation: replay_layer::Observation,
)
    requires p1_layer::source_is_delivery(
        history, source, request, attempt, observation,
    ),
    ensures p1_layer::source_is_delivery(
        history.push(event), source, request, attempt, observation,
    ),
{
    match source {
        Option::Some(index) => {
            assert(index < history.len());
            assert(history.push(event)[index as int] == history[index as int]);
        },
        Option::None => {},
    }
}

pub proof fn initial_commit_source_agreement(cfg: config_layer::FullConfig)
    ensures commit_source_agreement(cfg, p0_layer::initial_state(cfg)),
{
    assert forall|request: replay_layer::RequestId| {
        let source = #[trigger]
            p0_layer::initial_state(cfg).physical.commit_source[request];
        match p0_layer::initial_state(cfg)
            .core.broker.durable.committed[request]
        {
            Option::None => source.is_none(),
            Option::Some(committed) => {
                config_layer::erase_config(cfg).valid_results
                    .contains((request, committed.value))
                    && p1_layer::source_is_delivery(
                        p0_layer::initial_state(cfg).physical.physical,
                        source,
                        request,
                        committed.attempt,
                        replay_layer::Observation::Success(committed.value),
                    )
            },
        }
    } by {}
}

pub proof fn physical_push_preserves_commit_source_agreement(
    cfg: config_layer::FullConfig,
    state: p0_layer::State,
    physical: p0_layer::PhysicalEvent,
)
    requires commit_source_agreement(cfg, state),
    ensures commit_source_agreement(
        cfg,
        p0_layer::State {
            physical: p0_layer::PhysicalEvidence {
                physical: state.physical.physical.push(physical),
                ..state.physical
            },
            ..state
        },
    ),
{
    let after = p0_layer::State {
        physical: p0_layer::PhysicalEvidence {
            physical: state.physical.physical.push(physical),
            ..state.physical
        },
        ..state
    };
    assert forall|request: replay_layer::RequestId| {
        let source = #[trigger] after.physical.commit_source[request];
        match after.core.broker.durable.committed[request] {
            Option::None => source.is_none(),
            Option::Some(committed) => {
                config_layer::erase_config(cfg).valid_results
                    .contains((request, committed.value))
                    && p1_layer::source_is_delivery(
                        after.physical.physical,
                        source,
                        request,
                        committed.attempt,
                        replay_layer::Observation::Success(committed.value),
                    )
            },
        }
    } by {
        match state.core.broker.durable.committed[request] {
            Option::None => {},
            Option::Some(committed) => {
                source_is_delivery_history_push(
                    state.physical.physical,
                    physical,
                    state.physical.commit_source[request],
                    request,
                    committed.attempt,
                    replay_layer::Observation::Success(committed.value),
                );
            },
        }
    }
}

pub proof fn commit_linearize_preserves_source_agreement(
    cfg: config_layer::FullConfig,
    state: p0_layer::State,
    record: replay_layer::JournalRecord,
)
    requires
        p2_layer::p2_invariant(cfg, state),
        commit_source_agreement(cfg, state),
        p0_layer::admissibly_enabled(
            cfg, state, p0_layer::Event::BrokerLinearize { record },
        ),
        record is CommitRec,
    ensures commit_source_agreement(
        cfg,
        p0_layer::apply(
            cfg, state, p0_layer::Event::BrokerLinearize { record },
        ),
    ),
{
    let erased = config_layer::erase_config(cfg);
    let after = p0_layer::apply(
        cfg, state, p0_layer::Event::BrokerLinearize { record },
    );
    match record {
        replay_layer::JournalRecord::CommitRec {
            request: committed_request, attempt, value, ..
        } => {
            assert(state.core.broker.slot
                == (record_layer::ExecSlot::ObservedSuccess {
                    request: committed_request, attempt, value,
                }));
            assert(p1_layer::physical_slot_agreement(state));
            assert(p1_layer::source_is_delivery(
                state.physical.physical,
                state.physical.slot_source,
                committed_request,
                attempt,
                replay_layer::Observation::Success(value),
            ));
            assert(replay_layer::recorded_success_valid(
                erased, state.core.evidence.records,
            ));
            assert(replay_layer::outcome_observation(
                state.core.evidence.records, committed_request, attempt,
            ) == Option::Some(replay_layer::Observation::Success(value)));
            assert(erased.valid_results.contains((committed_request, value)));

            assert forall|request: replay_layer::RequestId| {
                let source = #[trigger] after.physical.commit_source[request];
                match after.core.broker.durable.committed[request] {
                    Option::None => source.is_none(),
                    Option::Some(committed) => {
                        erased.valid_results.contains((request, committed.value))
                            && p1_layer::source_is_delivery(
                                after.physical.physical,
                                source,
                                request,
                                committed.attempt,
                                replay_layer::Observation::Success(
                                    committed.value,
                                ),
                            )
                    },
                }
            } by {
                if request == committed_request {
                    assert(after.physical.commit_source[request]
                        == state.physical.slot_source);
                } else {
                    assert(after.physical.commit_source[request]
                        == state.physical.commit_source[request]);
                    assert(after.core.broker.durable.committed[request]
                        == state.core.broker.durable.committed[request]);
                }
            }
        },
        _ => {},
    }
}

pub proof fn noncommit_step_preserves_source_agreement(
    cfg: config_layer::FullConfig,
    state: p0_layer::State,
    event: p0_layer::Event,
)
    requires
        commit_source_agreement(cfg, state),
        !(event is InvokeEvent),
        !(event is DeliverEvent),
        !(event matches p0_layer::Event::BrokerLinearize {
            record: replay_layer::JournalRecord::CommitRec { .. },
        }),
    ensures commit_source_agreement(cfg, p0_layer::apply(cfg, state, event)),
{
    let after = p0_layer::apply(cfg, state, event);
    match event {
        p0_layer::Event::BrokerLinearize { record } => {
            match record {
                replay_layer::JournalRecord::Authorize { .. }
                | replay_layer::JournalRecord::Revoke { .. }
                | replay_layer::JournalRecord::Prepare { .. }
                | replay_layer::JournalRecord::Arm { .. }
                | replay_layer::JournalRecord::Start { .. }
                | replay_layer::JournalRecord::Outcome { .. }
                | replay_layer::JournalRecord::FailRec { .. }
                | replay_layer::JournalRecord::UnknownRec { .. } => {
                    assert forall|request: replay_layer::RequestId| {
                        let source = #[trigger]
                            after.physical.commit_source[request];
                        match after.core.broker.durable.committed[request] {
                            Option::None => source.is_none(),
                            Option::Some(committed) => {
                                config_layer::erase_config(cfg).valid_results
                                    .contains((request, committed.value))
                                    && p1_layer::source_is_delivery(
                                        after.physical.physical,
                                        source,
                                        request,
                                        committed.attempt,
                                        replay_layer::Observation::Success(
                                            committed.value,
                                        ),
                                    )
                            },
                        }
                    } by {}
                },
                replay_layer::JournalRecord::CommitRec { .. } => {},
            }
        },
        p0_layer::Event::JournalAppendCall { .. }
        | p0_layer::Event::JournalAppendReturn { .. }
        | p0_layer::Event::JournalDiskFull { .. }
        | p0_layer::Event::IgnoreStale { .. }
        | p0_layer::Event::RetryRelease { .. }
        | p0_layer::Event::Crash
        | p0_layer::Event::BeginRecover
        | p0_layer::Event::FinishRecover => {},
        p0_layer::Event::InvokeEvent { .. }
        | p0_layer::Event::DeliverEvent { .. } => {},
    }
}

pub proof fn commit_source_view_preserves_agreement(
    cfg: config_layer::FullConfig,
    before: p0_layer::State,
    after: p0_layer::State,
)
    requires
        commit_source_agreement(cfg, before),
        after.core.broker.durable == before.core.broker.durable,
        after.physical.physical == before.physical.physical,
        after.physical.commit_source == before.physical.commit_source,
    ensures commit_source_agreement(cfg, after),
{
    assert forall|request: replay_layer::RequestId| {
        let source = #[trigger] after.physical.commit_source[request];
        match after.core.broker.durable.committed[request] {
            Option::None => source.is_none(),
            Option::Some(committed) => {
                config_layer::erase_config(cfg).valid_results
                    .contains((request, committed.value))
                    && p1_layer::source_is_delivery(
                        after.physical.physical,
                        source,
                        request,
                        committed.attempt,
                        replay_layer::Observation::Success(committed.value),
                    )
            },
        }
    } by {}
}

pub proof fn step_preserves_commit_source_agreement(
    cfg: config_layer::FullConfig,
    state: p0_layer::State,
    event: p0_layer::Event,
)
    requires
        p2_layer::p2_invariant(cfg, state),
        commit_source_agreement(cfg, state),
        p0_layer::admissibly_enabled(cfg, state, event),
    ensures commit_source_agreement(cfg, p0_layer::apply(cfg, state, event)),
{
    let after = p0_layer::apply(cfg, state, event);
    match event {
        p0_layer::Event::InvokeEvent {
            request, attempt, call, journal_cut, ack_cut,
        } => {
            let physical = p0_layer::PhysicalEvent::Invoke {
                request, attempt, call, journal_cut, ack_cut,
            };
            let extended = p0_layer::State {
                physical: p0_layer::PhysicalEvidence {
                    physical: state.physical.physical.push(physical),
                    ..state.physical
                },
                ..state
            };
            physical_push_preserves_commit_source_agreement(
                cfg, state, physical,
            );
            assert(after.core.broker.durable == extended.core.broker.durable);
            assert(after.physical.physical == extended.physical.physical);
            assert(after.physical.commit_source
                == extended.physical.commit_source);
            commit_source_view_preserves_agreement(cfg, extended, after);
        },
        p0_layer::Event::DeliverEvent {
            request, attempt, observation, journal_cut,
        } => {
            let physical = p0_layer::PhysicalEvent::Delivered {
                request, attempt, observation, journal_cut,
            };
            let extended = p0_layer::State {
                physical: p0_layer::PhysicalEvidence {
                    physical: state.physical.physical.push(physical),
                    ..state.physical
                },
                ..state
            };
            physical_push_preserves_commit_source_agreement(
                cfg, state, physical,
            );
            assert(after.core.broker.durable == extended.core.broker.durable);
            assert(after.physical.physical == extended.physical.physical);
            assert(after.physical.commit_source
                == extended.physical.commit_source);
            commit_source_view_preserves_agreement(cfg, extended, after);
        },
        p0_layer::Event::BrokerLinearize { record } => match record {
            replay_layer::JournalRecord::CommitRec { .. } => {
                commit_linearize_preserves_source_agreement(
                    cfg, state, record,
                );
            },
            replay_layer::JournalRecord::Authorize { .. }
            | replay_layer::JournalRecord::Revoke { .. }
            | replay_layer::JournalRecord::Prepare { .. }
            | replay_layer::JournalRecord::Arm { .. }
            | replay_layer::JournalRecord::Start { .. }
            | replay_layer::JournalRecord::Outcome { .. }
            | replay_layer::JournalRecord::FailRec { .. }
            | replay_layer::JournalRecord::UnknownRec { .. } => {
                noncommit_step_preserves_source_agreement(cfg, state, event);
            },
        },
        p0_layer::Event::JournalAppendCall { .. }
        | p0_layer::Event::JournalAppendReturn { .. }
        | p0_layer::Event::JournalDiskFull { .. }
        | p0_layer::Event::IgnoreStale { .. }
        | p0_layer::Event::RetryRelease { .. }
        | p0_layer::Event::Crash
        | p0_layer::Event::BeginRecover
        | p0_layer::Event::FinishRecover => {
            noncommit_step_preserves_source_agreement(cfg, state, event);
        },
    }
}

pub proof fn outcome_observation_has_lsn(
    records: Seq<replay_layer::JournalRecord>,
    request: replay_layer::RequestId,
    attempt: replay_layer::AttemptId,
    observation: replay_layer::Observation,
)
    requires replay_layer::outcome_observation(records, request, attempt)
        == Option::Some(observation),
    ensures exists|lsn: replay_layer::Lsn| #![auto]
        replay_layer::outcome_lsn(records, request, attempt)
            == Option::Some(lsn),
    decreases records.len(),
{
    assert(records.len() > 0);
    let prefix = records.drop_last();
    match records.last() {
        replay_layer::JournalRecord::Outcome {
            request: r, attempt: a, observation: o, ..
        } => {
            if r == request && a == attempt {
                let lsn = records.len();
                assert(o == observation);
            } else {
                outcome_observation_has_lsn(
                    prefix, request, attempt, observation,
                );
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
            outcome_observation_has_lsn(
                prefix, request, attempt, observation,
            );
        },
    }
}

pub proof fn p2_implies_failed_physical_provenance(
    cfg: config_layer::FullConfig,
    state: p0_layer::State,
)
    requires
        config_layer::full_config_wf(cfg),
        p2_layer::p2_invariant(cfg, state),
    ensures failed_physical_provenance(cfg, state),
{
    let erased = config_layer::erase_config(cfg);
    let durable = state.core.broker.durable;
    let records = state.core.evidence.records;
    let history = state.physical.physical;
    config_layer::erasure_is_replay_well_formed(cfg);
    assert(durable == replay_layer::replay(erased, records));
    assert(replay_layer::r1_replay_invariant(erased, records));
    assert(replay_layer::replay_terminal_provenance_ok(erased, records));
    assert forall|request: replay_layer::RequestId| {
        match #[trigger] durable.failed_attempt[request] {
            Option::None => true,
            Option::Some(attempt) => {
                query_layer::d_latest(durable, request)
                        == Option::Some(attempt)
                    && query_layer::d_outcome(durable, request, attempt)
                        == Option::Some(replay_layer::Observation::Failure)
                    && query_layer::d_failure_conclusive(
                        erased, durable, request,
                    )
                    && exists|lsn: replay_layer::Lsn| #![auto] {
                        &&& replay_layer::outcome_lsn(
                            records, request, attempt,
                        ) == Option::Some(lsn)
                        &&& p2_layer::delivery_before_lsn(
                            history,
                            request,
                            attempt,
                            replay_layer::Observation::Failure,
                            lsn,
                        )
                    }
            },
        }
    } by {
        match durable.failed_attempt[request] {
            Option::None => {},
            Option::Some(attempt) => {
                assert(replay_layer::outcome_observation(
                    records, request, attempt,
                ) == Option::Some(replay_layer::Observation::Failure));
                assert(attempt
                    == replay_layer::started_count(records, request));
                assert(replay_layer::failure_conclusive(
                    erased, records, request,
                ));
                query_layer::replay_d_latest_exact(
                    erased, records, request,
                );
                query_layer::replay_d_outcome_exact(
                    erased, records, request, attempt,
                );
                query_layer::replay_d_failure_conclusive_exact(
                    erased, records, request,
                );
                assert(replay_layer::started_count(records, request) > 0);
                assert(replay_layer::latest_attempt(records, request)
                    == Option::Some(attempt));
                outcome_observation_has_lsn(
                    records,
                    request,
                    attempt,
                    replay_layer::Observation::Failure,
                );
                let lsn = choose|lsn: replay_layer::Lsn|
                    replay_layer::outcome_lsn(
                        records, request, attempt,
                    ) == Option::Some(lsn);
                p2_layer::outcome_projection_has_delivery(
                    records,
                    history,
                    request,
                    attempt,
                    replay_layer::Observation::Failure,
                    lsn,
                );
            },
        }
    }
}

pub proof fn p2_implies_durable_terminal_provenance(
    cfg: config_layer::FullConfig,
    state: p0_layer::State,
)
    requires p2_layer::p2_invariant(cfg, state),
    ensures
        durable_terminal_provenance(cfg, state),
        durable_unknown_provenance(cfg, state),
{
    let erased = config_layer::erase_config(cfg);
    let records = state.core.evidence.records;
    assert(replay_layer::r1_replay_invariant(erased, records));
}

pub open spec fn recovery_repair_record(
    cfg: config_layer::FullConfig,
    durable: replay_layer::DurableBroker,
    record: replay_layer::JournalRecord,
) -> bool {
    match record {
        replay_layer::JournalRecord::FailRec { request, .. } => {
            query_layer::d_failure_conclusive(
                config_layer::erase_config(cfg), durable, request,
            )
        },
        replay_layer::JournalRecord::UnknownRec { request, reason, .. } => {
            reason == replay_layer::UnknownReason::Recovery
                && query_layer::unsafe_uncontrolled_d(
                    config_layer::erase_config(cfg), durable, request,
                )
        },
        replay_layer::JournalRecord::Authorize { .. }
        | replay_layer::JournalRecord::Revoke { .. }
        | replay_layer::JournalRecord::Prepare { .. }
        | replay_layer::JournalRecord::Arm { .. }
        | replay_layer::JournalRecord::Start { .. }
        | replay_layer::JournalRecord::Outcome { .. }
        | replay_layer::JournalRecord::CommitRec { .. } => false,
    }
}

pub proof fn recovering_linearize_is_source_preserving_repair(
    cfg: config_layer::FullConfig,
    state: p0_layer::State,
    record: replay_layer::JournalRecord,
)
    requires
        p2_layer::p2_invariant(cfg, state),
        state.core.broker.mode == record_layer::Mode::Recovering,
        p0_layer::admissibly_enabled(
            cfg, state, p0_layer::Event::BrokerLinearize { record },
        ),
    ensures
        recovery_repair_record(cfg, state.core.broker.durable, record),
        p0_layer::apply(
            cfg, state, p0_layer::Event::BrokerLinearize { record },
        ).physical.commit_source == state.physical.commit_source,
{
    let erased = config_layer::erase_config(cfg);
    assert(record_layer::abstract_enabled(
        erased, state.core.broker, record,
    ));
    assert(record_layer::durable_slot_update(
        erased,
        state.core.broker.durable,
        state.core.broker.mode,
        state.core.broker.slot,
        record,
    ).is_some());
    match record {
        replay_layer::JournalRecord::FailRec { .. } => {},
        replay_layer::JournalRecord::UnknownRec { request, reason, .. } => {
            assert(reason == replay_layer::UnknownReason::Recovery);
            assert(query_layer::unsafe_uncontrolled_d(
                erased, state.core.broker.durable, request,
            ));
        },
        replay_layer::JournalRecord::Authorize { .. }
        | replay_layer::JournalRecord::Revoke { .. }
        | replay_layer::JournalRecord::Prepare { .. }
        | replay_layer::JournalRecord::Arm { .. }
        | replay_layer::JournalRecord::Start { .. }
        | replay_layer::JournalRecord::Outcome { .. }
        | replay_layer::JournalRecord::CommitRec { .. } => {
            assert(false);
        },
    }
}

pub proof fn crash_preserves_commit_sources(
    cfg: config_layer::FullConfig,
    state: p0_layer::State,
)
    ensures p0_layer::apply(cfg, state, p0_layer::Event::Crash)
        .physical.commit_source == state.physical.commit_source,
{
}

pub proof fn step_preserves_p3_invariant(
    cfg: config_layer::FullConfig,
    state: p0_layer::State,
    event: p0_layer::Event,
)
    requires
        config_layer::full_config_wf(cfg),
        p3_invariant(cfg, state),
        p0_layer::admissibly_enabled(cfg, state, event),
    ensures p3_invariant(cfg, p0_layer::apply(cfg, state, event)),
{
    step_preserves_commit_source_agreement(cfg, state, event);
    p2_layer::step_preserves_p2_invariant(cfg, state, event);
}

pub proof fn initial_p3_invariant(cfg: config_layer::FullConfig)
    requires config_layer::full_config_wf(cfg),
    ensures p3_invariant(cfg, p0_layer::initial_state(cfg)),
{
    p2_layer::initial_p2_invariant(cfg);
    initial_commit_source_agreement(cfg);
}

pub proof fn executable_run_p3_invariant(
    cfg: config_layer::FullConfig,
    events: Seq<p0_layer::Event>,
)
    requires
        config_layer::full_config_wf(cfg),
        p0_layer::admissibly_executable(cfg, events),
    ensures p3_invariant(cfg, p0_layer::run(cfg, events)),
    decreases events.len(),
{
    if events.len() == 0 {
        initial_p3_invariant(cfg);
    } else {
        let prefix = events.drop_last();
        executable_run_p3_invariant(cfg, prefix);
        step_preserves_p3_invariant(
            cfg, p0_layer::run(cfg, prefix), events.last(),
        );
    }
}

pub open spec fn p3_checkpoint(
    cfg: config_layer::FullConfig,
    events: Seq<p0_layer::Event>,
) -> bool {
    let state = p0_layer::run(cfg, events);
    p2_layer::p2_checkpoint(cfg, events)
        && p3_invariant(cfg, state)
        && durable_terminal_provenance(cfg, state)
        && failed_physical_provenance(cfg, state)
        && durable_unknown_provenance(cfg, state)
}

pub proof fn b2_p3_terminal_provenance_safety(
    cfg: config_layer::FullConfig,
    events: Seq<p0_layer::Event>,
)
    requires
        config_layer::full_config_wf(cfg),
        p0_layer::admissibly_executable(cfg, events),
    ensures
        p3_checkpoint(cfg, events),
        forall|length: nat| length <= events.len() ==>
            #[trigger] p3_checkpoint(cfg, events.take(length as int)),
{
    p2_layer::b2_p2_physical_refinement_safety(cfg, events);
    executable_run_p3_invariant(cfg, events);
    p2_implies_durable_terminal_provenance(
        cfg, p0_layer::run(cfg, events),
    );
    p2_implies_failed_physical_provenance(
        cfg, p0_layer::run(cfg, events),
    );
    assert forall|length: nat| length <= events.len() implies
        #[trigger] p3_checkpoint(cfg, events.take(length as int)) by {
        p0_layer::executable_prefix(cfg, events, length);
        p2_layer::b2_p2_physical_refinement_safety(
            cfg, events.take(length as int),
        );
        executable_run_p3_invariant(cfg, events.take(length as int));
        p2_implies_durable_terminal_provenance(
            cfg, p0_layer::run(cfg, events.take(length as int)),
        );
        p2_implies_failed_physical_provenance(
            cfg, p0_layer::run(cfg, events.take(length as int)),
        );
    }
}

} // verus!
