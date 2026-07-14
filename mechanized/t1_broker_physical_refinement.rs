use vstd::prelude::*;

#[path = "t1_broker_physical_causality.rs"]
pub mod p1_layer;

verus! {

use p1_layer::p0_layer;
use p0_layer::config_layer;
use config_layer::broker_layer as record_layer;
use record_layer::query_layer;
use record_layer::query_layer::c1_layer::replay_layer;
use record_layer::query_layer::c1_layer::append_layer;

// B2-P2 strengthens B2-P1 with three physical/Journaling refinement facts:
// aggregate retry bounds, acknowledged authorization ancestry for every
// invocation, and an earlier exact delivery for every durable Outcome.  It
// deliberately leaves terminal Commit/Fail provenance and adapter effects to
// later checkpoints.

pub open spec fn request_invoke_count(
    history: Seq<p0_layer::PhysicalEvent>,
    request: replay_layer::RequestId,
) -> nat
    decreases history.len()
{
    if history.len() == 0 {
        0
    } else {
        request_invoke_count(history.drop_last(), request)
            + match history.last() {
                p0_layer::PhysicalEvent::Invoke { request: r, .. }
                    if r == request => 1nat,
                _ => 0nat,
            }
    }
}

// A Ready slot owns the one durable Start that has not yet been consumed by
// an Invoke.  This credit formulation makes Start and Invoke preserve the same
// accounting equation without a physical-attempt counter in runtime state.
pub open spec fn ready_credit(
    slot: record_layer::ExecSlot,
    request: replay_layer::RequestId,
) -> nat {
    match slot {
        record_layer::ExecSlot::Ready { request: r, .. } if r == request => 1nat,
        _ => 0nat,
    }
}

pub open spec fn invocation_accounting(state: p0_layer::State) -> bool {
    forall|request: replay_layer::RequestId|
        #[trigger] request_invoke_count(state.physical.physical, request)
            + ready_credit(state.core.broker.slot, request)
            <= replay_layer::started_count(state.core.evidence.records, request)
}

pub open spec fn aggregate_retry_bounds(
    cfg: config_layer::FullConfig,
    state: p0_layer::State,
) -> bool {
    let erased = config_layer::erase_config(cfg);
    forall|request: replay_layer::RequestId| {
        let invokes = #[trigger] request_invoke_count(
            state.physical.physical, request,
        );
        invokes <= erased.max_attempts[request]
            && (erased.request_class[request]
                    == replay_layer::RetryClass::Uncontrolled
                ==> invokes <= 1)
    }
}

pub open spec fn valid_authorize_at(
    cfg: config_layer::FullConfig,
    records: Seq<replay_layer::JournalRecord>,
    lsn: replay_layer::Lsn,
    request: replay_layer::RequestId,
) -> bool {
    replay_layer::authorize_at(records, lsn, request)
        && match records[(lsn - 1) as int] {
            replay_layer::JournalRecord::Authorize {
                request: r, capability, digest,
            } => {
                let erased = config_layer::erase_config(cfg);
                r == request
                    && capability == erased.request_capability[request]
                    && erased.matches.contains((request, capability))
                    && digest == erased.request_digest[request]
                    && replay_layer::replay(
                        erased, records.take((lsn - 1) as int),
                    ).phase[request] == replay_layer::Phase::New
                    && !replay_layer::replay(
                        erased, records.take((lsn - 1) as int),
                    ).revoked.contains(capability)
                    && replay_layer::replay(
                        erased, records.take((lsn - 1) as int),
                    ).remaining[capability] > 0
            },
            _ => false,
        }
}

pub open spec fn acknowledged_start_authorized(
    cfg: config_layer::FullConfig,
    records: Seq<replay_layer::JournalRecord>,
    request: replay_layer::RequestId,
    attempt: replay_layer::AttemptId,
) -> bool {
    exists|start: replay_layer::Lsn, auth: replay_layer::Lsn| {
        &&& replay_layer::start_lsn(records, request, attempt)
            == Option::Some(start)
        &&& valid_authorize_at(cfg, records, auth, request)
        &&& auth < start
        &&& attempt <= config_layer::erase_config(cfg).max_attempts[request]
        &&& (config_layer::erase_config(cfg).request_class[request]
                == replay_layer::RetryClass::Uncontrolled
            ==> attempt == 1)
        &&& !replay_layer::failure_conclusive(
            config_layer::erase_config(cfg),
            records.take((start - 1) as int),
            request,
        )
    }
}

pub open spec fn invoke_refinement_witness(
    cfg: config_layer::FullConfig,
    records: Seq<replay_layer::JournalRecord>,
    event: p0_layer::PhysicalEvent,
) -> bool {
    match event {
        p0_layer::PhysicalEvent::Invoke {
            request, attempt, journal_cut, ack_cut, ..
        } => {
            let acknowledged = records.take(ack_cut as int);
            ack_cut <= records.len()
                && journal_cut <= records.len()
                && acknowledged_start_authorized(
                    cfg, acknowledged, request, attempt,
                )
                && !replay_layer::failure_conclusive(
                    config_layer::erase_config(cfg),
                    records.take(journal_cut as int),
                    request,
                )
        },
        p0_layer::PhysicalEvent::Delivered { .. } => true,
    }
}

pub open spec fn acknowledged_invocation_refinement(
    cfg: config_layer::FullConfig,
    records: Seq<replay_layer::JournalRecord>,
    history: Seq<p0_layer::PhysicalEvent>,
) -> bool
    decreases history.len()
{
    history.len() == 0 || {
        let prefix = history.drop_last();
        acknowledged_invocation_refinement(cfg, records, prefix)
            && invoke_refinement_witness(cfg, records, history.last())
    }
}

pub open spec fn delivery_before_lsn(
    history: Seq<p0_layer::PhysicalEvent>,
    request: replay_layer::RequestId,
    attempt: replay_layer::AttemptId,
    observation: replay_layer::Observation,
    outcome_lsn: replay_layer::Lsn,
) -> bool {
    exists|index: nat, delivery_cut: nat| {
        &&& index < history.len()
        &&& history[index as int]
            == (p0_layer::PhysicalEvent::Delivered {
                request,
                attempt,
                observation,
                journal_cut: delivery_cut,
            })
        &&& delivery_cut < outcome_lsn
    }
}

// This recursive predicate makes each record's one-based LSN explicit.  The
// observation in the witness is equal, not merely classification-compatible.
pub open spec fn durable_outcomes_follow_deliveries(
    records: Seq<replay_layer::JournalRecord>,
    history: Seq<p0_layer::PhysicalEvent>,
) -> bool
    decreases records.len()
{
    records.len() == 0 || {
        let prefix = records.drop_last();
        durable_outcomes_follow_deliveries(prefix, history)
            && match records.last() {
                replay_layer::JournalRecord::Outcome {
                    request, attempt, observation, ..
                } => delivery_before_lsn(
                    history, request, attempt, observation, records.len(),
                ),
                _ => true,
            }
    }
}

pub open spec fn p2_invariant(
    cfg: config_layer::FullConfig,
    state: p0_layer::State,
) -> bool {
    p1_layer::p1_invariant(cfg, state)
        && invocation_accounting(state)
        && acknowledged_invocation_refinement(
            cfg, state.core.evidence.records, state.physical.physical,
        )
        && durable_outcomes_follow_deliveries(
            state.core.evidence.records, state.physical.physical,
        )
}

pub proof fn request_invoke_count_push(
    history: Seq<p0_layer::PhysicalEvent>,
    event: p0_layer::PhysicalEvent,
    request: replay_layer::RequestId,
)
    ensures request_invoke_count(history.push(event), request)
        == request_invoke_count(history, request)
            + match event {
                p0_layer::PhysicalEvent::Invoke { request: r, .. }
                    if r == request => 1nat,
                _ => 0nat,
            },
{
    assert(history.push(event).drop_last() =~= history);
    assert(history.push(event).last() == event);
}

pub proof fn authorize_count_positive_has_lsn(
    records: Seq<replay_layer::JournalRecord>,
    request: replay_layer::RequestId,
)
    requires replay_layer::authorize_count_for_request(records, request) > 0,
    ensures replay_layer::authorize_lsn(records, request).is_some(),
    decreases records.len(),
{
    if records.len() == 0 {
        assert(replay_layer::authorize_count_for_request(records, request) == 0);
    } else {
        let prefix = records.drop_last();
        match records.last() {
            replay_layer::JournalRecord::Authorize { request: r, .. } => {
                if r != request {
                    replay_layer::authorize_request_count_push(
                        prefix, request, records.last(),
                    );
                    authorize_count_positive_has_lsn(prefix, request);
                }
            },
            _ => {
                replay_layer::authorize_request_count_push(
                    prefix, request, records.last(),
                );
                authorize_count_positive_has_lsn(prefix, request);
            },
        }
    }
}

pub proof fn start_has_acknowledged_authorization(
    cfg: config_layer::FullConfig,
    records: Seq<replay_layer::JournalRecord>,
    request: replay_layer::RequestId,
    attempt: replay_layer::AttemptId,
)
    requires
        config_layer::full_config_wf(cfg),
        replay_layer::journal_legal(config_layer::erase_config(cfg), records),
        replay_layer::start_lsn(records, request, attempt).is_some(),
    ensures acknowledged_start_authorized(cfg, records, request, attempt),
{
    let erased = config_layer::erase_config(cfg);
    config_layer::erasure_is_replay_well_formed(cfg);
    replay_layer::start_lsn_is_in_bounds(records, request, attempt);
    match replay_layer::start_lsn(records, request, attempt) {
        Option::Some(start) => {
            assert(1 <= start && start <= records.len());
            assert(replay_layer::start_at(
                records, start, request, attempt,
            ));
            let before = records.take((start - 1) as int);
            let record = records[(start - 1) as int];
            assert(replay_layer::structural_enabled(erased, before, record));
            match record {
                replay_layer::JournalRecord::Start {
                    request: r, attempt: a, ..
                } => {
                    assert(r == request && a == attempt);
                    assert(replay_layer::replay(erased, before).phase[request]
                        == replay_layer::Phase::Armed);
                    assert(attempt
                        == replay_layer::started_count(before, request) + 1);
                    assert(attempt <= erased.max_attempts[request]);
                    assert(!replay_layer::failure_conclusive(
                        erased, before, request,
                    ));
                    if erased.request_class[request]
                        == replay_layer::RetryClass::Uncontrolled
                    {
                        assert(replay_layer::started_count(before, request) == 0);
                        assert(attempt == 1);
                    }
                },
                _ => {},
            }
            replay_layer::journal_legal_take(
                erased, records, (start - 1) as nat,
            );
            replay_layer::authorization_phase_count(erased, before);
            assert(replay_layer::authorize_count_for_request(
                before, request,
            ) > 0);
            authorize_count_positive_has_lsn(before, request);
            match replay_layer::authorize_lsn(before, request) {
                Option::Some(auth) => {
                    replay_layer::authorize_lsn_is_in_bounds(before, request);
                    assert(replay_layer::authorize_at(before, auth, request));
                    assert(1 <= auth && auth <= before.len());
                    assert(before.len() == start - 1);
                    assert(auth < start);
                    assert(records[auth as int - 1] == before[auth as int - 1]);
                    assert(replay_layer::authorize_at(records, auth, request));
                    replay_layer::authorization_records_are_prefix_valid(
                        erased, records,
                    );
                    assert(valid_authorize_at(cfg, records, auth, request));
                },
                Option::None => {},
            }
        },
        Option::None => {},
    }
}

pub proof fn invoke_refinement_record_push(
    cfg: config_layer::FullConfig,
    records: Seq<replay_layer::JournalRecord>,
    history: Seq<p0_layer::PhysicalEvent>,
    record: replay_layer::JournalRecord,
)
    requires acknowledged_invocation_refinement(cfg, records, history),
    ensures acknowledged_invocation_refinement(
        cfg, records.push(record), history,
    ),
    decreases history.len(),
{
    if history.len() > 0 {
        let prefix = history.drop_last();
        invoke_refinement_record_push(cfg, records, prefix, record);
        match history.last() {
            p0_layer::PhysicalEvent::Invoke {
                ack_cut, journal_cut, ..
            } => {
                assert(ack_cut <= records.len());
                assert(journal_cut <= records.len());
                append_layer::take_push_stable(records, record, ack_cut);
                append_layer::take_push_stable(records, record, journal_cut);
            },
            p0_layer::PhysicalEvent::Delivered { .. } => {},
        }
    }
}

pub proof fn invoke_refinement_push(
    cfg: config_layer::FullConfig,
    records: Seq<replay_layer::JournalRecord>,
    history: Seq<p0_layer::PhysicalEvent>,
    event: p0_layer::PhysicalEvent,
)
    requires
        acknowledged_invocation_refinement(cfg, records, history),
        invoke_refinement_witness(cfg, records, event),
    ensures acknowledged_invocation_refinement(
        cfg, records, history.push(event),
    ),
{
    assert(history.push(event).drop_last() =~= history);
    assert(history.push(event).last() == event);
}

pub proof fn delivery_before_lsn_history_push(
    history: Seq<p0_layer::PhysicalEvent>,
    event: p0_layer::PhysicalEvent,
    request: replay_layer::RequestId,
    attempt: replay_layer::AttemptId,
    observation: replay_layer::Observation,
    outcome_lsn: replay_layer::Lsn,
)
    requires delivery_before_lsn(
        history, request, attempt, observation, outcome_lsn,
    ),
    ensures delivery_before_lsn(
        history.push(event), request, attempt, observation, outcome_lsn,
    ),
{
    let index = choose|index: nat| exists|delivery_cut: nat| {
        &&& index < history.len()
        &&& #[trigger] history[index as int]
            == (p0_layer::PhysicalEvent::Delivered {
                request, attempt, observation, journal_cut: delivery_cut,
            })
        &&& delivery_cut < outcome_lsn
    };
    let delivery_cut = choose|delivery_cut: nat| {
        &&& index < history.len()
        &&& #[trigger] history[index as int]
            == (p0_layer::PhysicalEvent::Delivered {
                request, attempt, observation, journal_cut: delivery_cut,
            })
        &&& delivery_cut < outcome_lsn
    };
    assert(history.push(event)[index as int] == history[index as int]);
}

pub proof fn outcomes_refinement_history_push(
    records: Seq<replay_layer::JournalRecord>,
    history: Seq<p0_layer::PhysicalEvent>,
    event: p0_layer::PhysicalEvent,
)
    requires durable_outcomes_follow_deliveries(records, history),
    ensures durable_outcomes_follow_deliveries(
        records, history.push(event),
    ),
    decreases records.len(),
{
    if records.len() > 0 {
        let prefix = records.drop_last();
        outcomes_refinement_history_push(prefix, history, event);
        match records.last() {
            replay_layer::JournalRecord::Outcome {
                request, attempt, observation, ..
            } => {
                delivery_before_lsn_history_push(
                    history, event, request, attempt, observation,
                    records.len(),
                );
            },
            _ => {},
        }
    }
}

pub proof fn outcomes_refinement_record_push(
    records: Seq<replay_layer::JournalRecord>,
    history: Seq<p0_layer::PhysicalEvent>,
    record: replay_layer::JournalRecord,
)
    requires
        durable_outcomes_follow_deliveries(records, history),
        match record {
            replay_layer::JournalRecord::Outcome {
                request, attempt, observation, ..
            } => delivery_before_lsn(
                history, request, attempt, observation, records.len() + 1,
            ),
            _ => true,
        },
    ensures durable_outcomes_follow_deliveries(
        records.push(record), history,
    ),
{
    assert(records.push(record).drop_last() =~= records);
    assert(records.push(record).last() == record);
    assert(records.push(record).len() == records.len() + 1);
}

pub proof fn delivery_cut_bounded_at(
    cfg: config_layer::FullConfig,
    records: Seq<replay_layer::JournalRecord>,
    ack_cuts: Seq<nat>,
    history: Seq<p0_layer::PhysicalEvent>,
    index: nat,
)
    requires
        p1_layer::physical_cuts_valid(cfg, records, ack_cuts, history),
        index < history.len(),
        history[index as int] is Delivered,
    ensures match history[index as int] {
        p0_layer::PhysicalEvent::Delivered { journal_cut, .. } => {
            journal_cut <= records.len()
        },
        p0_layer::PhysicalEvent::Invoke { .. } => false,
    },
    decreases history.len(),
{
    let prefix = history.drop_last();
    if index < prefix.len() {
        assert(prefix[index as int] == history[index as int]);
        delivery_cut_bounded_at(cfg, records, ack_cuts, prefix, index);
    } else {
        assert(index == history.len() - 1);
        assert(history[index as int] == history.last());
    }
}

pub proof fn slot_source_yields_delivery_before_next_lsn(
    cfg: config_layer::FullConfig,
    state: p0_layer::State,
    request: replay_layer::RequestId,
    attempt: replay_layer::AttemptId,
    observation: replay_layer::Observation,
)
    requires
        p1_layer::physical_cuts_valid(
            cfg,
            state.core.evidence.records,
            state.core.evidence.ack_cuts,
            state.physical.physical,
        ),
        p1_layer::source_is_delivery(
            state.physical.physical,
            state.physical.slot_source,
            request,
            attempt,
            observation,
        ),
    ensures delivery_before_lsn(
        state.physical.physical,
        request,
        attempt,
        observation,
        state.core.evidence.records.len() + 1,
    ),
{
    match state.physical.slot_source {
        Option::Some(index) => {
            assert(index < state.physical.physical.len());
            match state.physical.physical[index as int] {
                p0_layer::PhysicalEvent::Delivered {
                    request: r,
                    attempt: a,
                    observation: o,
                    journal_cut,
                } => {
                    assert(r == request && a == attempt && o == observation);
                    delivery_cut_bounded_at(
                        cfg,
                        state.core.evidence.records,
                        state.core.evidence.ack_cuts,
                        state.physical.physical,
                        index,
                    );
                    assert(journal_cut < state.core.evidence.records.len() + 1);
                    assert(delivery_before_lsn(
                        state.physical.physical,
                        request,
                        attempt,
                        observation,
                        state.core.evidence.records.len() + 1,
                    )) by {
                        assert(exists|witness_index: nat, delivery_cut: nat| {
                            &&& witness_index < state.physical.physical.len()
                            &&& state.physical.physical[witness_index as int]
                                == (p0_layer::PhysicalEvent::Delivered {
                                    request,
                                    attempt,
                                    observation,
                                    journal_cut: delivery_cut,
                                })
                            &&& delivery_cut
                                < state.core.evidence.records.len() + 1
                        }) by {
                            assert(index < state.physical.physical.len());
                            assert(state.physical.physical[index as int]
                                == (p0_layer::PhysicalEvent::Delivered {
                                    request,
                                    attempt,
                                    observation,
                                    journal_cut,
                                }));
                        }
                    }
                },
                p0_layer::PhysicalEvent::Invoke { .. } => {},
            }
        },
        Option::None => {},
    }
}

pub proof fn nonstart_linearize_credit_nonincreasing(
    cfg: config_layer::FullConfig,
    state: p0_layer::State,
    record: replay_layer::JournalRecord,
)
    requires
        p0_layer::admissibly_enabled(
            cfg, state, p0_layer::Event::BrokerLinearize { record },
        ),
        !(record is Start),
    ensures forall|request: replay_layer::RequestId|
        #[trigger] ready_credit(
            p0_layer::apply(
                cfg, state, p0_layer::Event::BrokerLinearize { record },
            ).core.broker.slot,
            request,
        ) <= ready_credit(state.core.broker.slot, request),
{
    assert forall|request: replay_layer::RequestId|
        #[trigger] ready_credit(
            p0_layer::apply(
                cfg, state, p0_layer::Event::BrokerLinearize { record },
            ).core.broker.slot,
            request,
        ) <= ready_credit(state.core.broker.slot, request) by {
        match record {
            replay_layer::JournalRecord::Authorize { .. }
            | replay_layer::JournalRecord::Revoke { .. }
            | replay_layer::JournalRecord::Prepare { .. }
            | replay_layer::JournalRecord::Arm { .. } => {},
            replay_layer::JournalRecord::Outcome { .. }
            | replay_layer::JournalRecord::CommitRec { .. }
            | replay_layer::JournalRecord::FailRec { .. }
            | replay_layer::JournalRecord::UnknownRec { .. } => {
                match state.core.broker.slot {
                    record_layer::ExecSlot::Idle
                    | record_layer::ExecSlot::Ready { .. }
                    | record_layer::ExecSlot::InFlight { .. }
                    | record_layer::ExecSlot::Received { .. }
                    | record_layer::ExecSlot::ObservedSuccess { .. }
                    | record_layer::ExecSlot::ObservedFailure { .. }
                    | record_layer::ExecSlot::ObservedUnknown { .. } => {},
                }
            },
            replay_layer::JournalRecord::Start { .. } => {},
        }
    }
}

pub proof fn nonphysical_nonstart_credit_nonincreasing(
    cfg: config_layer::FullConfig,
    state: p0_layer::State,
    event: p0_layer::Event,
)
    requires
        p0_layer::admissibly_enabled(cfg, state, event),
        !(event is InvokeEvent),
        !(event is DeliverEvent),
        !(event is BrokerLinearize),
    ensures forall|request: replay_layer::RequestId|
        #[trigger] ready_credit(
            p0_layer::apply(cfg, state, event).core.broker.slot, request,
        ) <= ready_credit(state.core.broker.slot, request),
{
    assert forall|request: replay_layer::RequestId|
        #[trigger] ready_credit(
            p0_layer::apply(cfg, state, event).core.broker.slot, request,
        ) <= ready_credit(state.core.broker.slot, request) by {
        match event {
            p0_layer::Event::JournalAppendCall { .. }
            | p0_layer::Event::JournalAppendReturn { .. }
            | p0_layer::Event::JournalDiskFull { .. }
            | p0_layer::Event::IgnoreStale { .. }
            | p0_layer::Event::BeginRecover
            | p0_layer::Event::FinishRecover => {},
            p0_layer::Event::RetryRelease { .. }
            | p0_layer::Event::Crash => {
                match state.core.broker.slot {
                    record_layer::ExecSlot::Idle
                    | record_layer::ExecSlot::Ready { .. }
                    | record_layer::ExecSlot::InFlight { .. }
                    | record_layer::ExecSlot::Received { .. }
                    | record_layer::ExecSlot::ObservedSuccess { .. }
                    | record_layer::ExecSlot::ObservedFailure { .. }
                    | record_layer::ExecSlot::ObservedUnknown { .. } => {},
                }
            },
            p0_layer::Event::BrokerLinearize { .. }
            | p0_layer::Event::InvokeEvent { .. }
            | p0_layer::Event::DeliverEvent { .. } => {},
        }
    }
}

pub proof fn step_preserves_invocation_accounting(
    cfg: config_layer::FullConfig,
    state: p0_layer::State,
    event: p0_layer::Event,
)
    requires
        invocation_accounting(state),
        p0_layer::admissibly_enabled(cfg, state, event),
    ensures invocation_accounting(p0_layer::apply(cfg, state, event)),
{
    let after = p0_layer::apply(cfg, state, event);
    match event {
        p0_layer::Event::InvokeEvent {
            request: invoked, attempt, call, journal_cut, ack_cut,
        } => {
            let physical = p0_layer::PhysicalEvent::Invoke {
                request: invoked, attempt, call, journal_cut, ack_cut,
            };
            assert(state.core.broker.slot
                == (record_layer::ExecSlot::Ready {
                    request: invoked, attempt,
                }));
            assert forall|request: replay_layer::RequestId|
                #[trigger] request_invoke_count(
                    after.physical.physical, request,
                ) + ready_credit(after.core.broker.slot, request)
                    <= replay_layer::started_count(
                        after.core.evidence.records, request,
                    ) by {
                request_invoke_count_push(
                    state.physical.physical, physical, request,
                );
                if request == invoked {
                    assert(ready_credit(state.core.broker.slot, request) == 1);
                    assert(ready_credit(after.core.broker.slot, request) == 0);
                } else {
                    assert(ready_credit(state.core.broker.slot, request) == 0);
                    assert(ready_credit(after.core.broker.slot, request) == 0);
                }
            }
        },
        p0_layer::Event::DeliverEvent {
            request: delivered,
            attempt,
            observation,
            journal_cut,
        } => {
            let physical = p0_layer::PhysicalEvent::Delivered {
                request: delivered, attempt, observation, journal_cut,
            };
            assert(state.core.broker.slot
                == (record_layer::ExecSlot::InFlight {
                    request: delivered, attempt,
                }));
            assert forall|request: replay_layer::RequestId|
                #[trigger] request_invoke_count(
                    after.physical.physical, request,
                ) + ready_credit(after.core.broker.slot, request)
                    <= replay_layer::started_count(
                        after.core.evidence.records, request,
                    ) by {
                request_invoke_count_push(
                    state.physical.physical, physical, request,
                );
                assert(ready_credit(state.core.broker.slot, request) == 0);
                assert(ready_credit(after.core.broker.slot, request) == 0);
            }
        },
        p0_layer::Event::BrokerLinearize { record } => {
            match record {
                replay_layer::JournalRecord::Start {
                    request: started, attempt, ..
                } => {
                    assert(state.core.broker.slot == record_layer::ExecSlot::Idle);
                    assert(after.core.broker.slot
                        == (record_layer::ExecSlot::Ready {
                            request: started, attempt,
                        }));
                    assert forall|request: replay_layer::RequestId|
                        #[trigger] request_invoke_count(
                            after.physical.physical, request,
                        ) + ready_credit(after.core.broker.slot, request)
                            <= replay_layer::started_count(
                                after.core.evidence.records, request,
                            ) by {
                        replay_layer::started_count_push(
                            state.core.evidence.records, request, record,
                        );
                        if request == started {
                            assert(ready_credit(
                                state.core.broker.slot, request,
                            ) == 0);
                            assert(ready_credit(
                                after.core.broker.slot, request,
                            ) == 1);
                        } else {
                            assert(ready_credit(
                                state.core.broker.slot, request,
                            ) == 0);
                            assert(ready_credit(
                                after.core.broker.slot, request,
                            ) == 0);
                        }
                    }
                },
                _ => {
                    nonstart_linearize_credit_nonincreasing(cfg, state, record);
                    assert forall|request: replay_layer::RequestId|
                        #[trigger] request_invoke_count(
                            after.physical.physical, request,
                        ) + ready_credit(after.core.broker.slot, request)
                            <= replay_layer::started_count(
                                after.core.evidence.records, request,
                            ) by {
                        replay_layer::started_count_push(
                            state.core.evidence.records, request, record,
                        );
                    }
                },
            }
        },
        p0_layer::Event::JournalAppendCall { .. }
        | p0_layer::Event::JournalAppendReturn { .. }
        | p0_layer::Event::JournalDiskFull { .. }
        | p0_layer::Event::IgnoreStale { .. }
        | p0_layer::Event::RetryRelease { .. }
        | p0_layer::Event::Crash
        | p0_layer::Event::BeginRecover
        | p0_layer::Event::FinishRecover => {
            nonphysical_nonstart_credit_nonincreasing(cfg, state, event);
            assert forall|request: replay_layer::RequestId|
                #[trigger] request_invoke_count(
                    after.physical.physical, request,
                ) + ready_credit(after.core.broker.slot, request)
                    <= replay_layer::started_count(
                        after.core.evidence.records, request,
                    ) by {}
        },
    }
}

pub proof fn accounting_implies_aggregate_retry_bounds(
    cfg: config_layer::FullConfig,
    state: p0_layer::State,
)
    requires
        config_layer::full_config_wf(cfg),
        p1_layer::p1_invariant(cfg, state),
        invocation_accounting(state),
    ensures aggregate_retry_bounds(cfg, state),
{
    let erased = config_layer::erase_config(cfg);
    config_layer::erasure_is_replay_well_formed(cfg);
    replay_layer::replay_started_bound(
        erased, state.core.evidence.records,
    );
    replay_layer::replay_uncontrolled_single_attempt(
        erased, state.core.evidence.records,
    );
    assert forall|request: replay_layer::RequestId| {
        let invokes = #[trigger] request_invoke_count(
            state.physical.physical, request,
        );
        invokes <= erased.max_attempts[request]
            && (erased.request_class[request]
                    == replay_layer::RetryClass::Uncontrolled
                ==> invokes <= 1)
    } by {
        assert(request_invoke_count(state.physical.physical, request)
            <= replay_layer::started_count(
                state.core.evidence.records, request,
            ));
    }
}

pub proof fn invoke_event_has_refinement_witness(
    cfg: config_layer::FullConfig,
    state: p0_layer::State,
    event: p0_layer::Event,
)
    requires
        config_layer::full_config_wf(cfg),
        p1_layer::p1_invariant(cfg, state),
        p0_layer::admissibly_enabled(cfg, state, event),
        event is InvokeEvent,
    ensures match p0_layer::event_physical(event) {
        Option::Some(physical) => invoke_refinement_witness(
            cfg, state.core.evidence.records, physical,
        ),
        Option::None => false,
    },
{
    let erased = config_layer::erase_config(cfg);
    config_layer::erasure_is_replay_well_formed(cfg);
    match event {
        p0_layer::Event::InvokeEvent {
            request,
            attempt,
            call,
            journal_cut,
            ack_cut,
        } => {
            let records = state.core.evidence.records;
            let acknowledged = records.take(ack_cut as int);
            assert(journal_cut == records.len());
            assert(ack_cut == state.core.evidence.acknowledged_prefix.len());
            assert(ack_cut <= records.len());
            match replay_layer::start_lsn(records, request, attempt) {
                Option::Some(start) => {
                    assert(1 <= start && start <= ack_cut);
                    p1_layer::start_lsn_take_cover(
                        records, request, attempt, ack_cut, start,
                    );
                },
                Option::None => {},
            }
            replay_layer::journal_legal_take(erased, records, ack_cut);
            start_has_acknowledged_authorization(
                cfg, acknowledged, request, attempt,
            );

            assert(state.core.broker.slot
                == (record_layer::ExecSlot::Ready { request, attempt }));
            assert(record_layer::durable_slot_agreement(
                erased,
                state.core.broker.durable,
                state.core.broker.slot,
            ));
            assert(state.core.broker.durable
                == replay_layer::replay(erased, records));
            assert(query_layer::d_latest(
                state.core.broker.durable, request,
            ) == Option::Some(attempt));
            assert(query_layer::d_outcome(
                state.core.broker.durable, request, attempt,
            ).is_none());
            assert(!query_layer::d_failure_conclusive(
                erased, state.core.broker.durable, request,
            ));
            query_layer::replay_d_failure_conclusive_exact(
                erased, records, request,
            );
            assert(!replay_layer::failure_conclusive(
                erased, records, request,
            ));
            assert(records.take(journal_cut as int) =~= records);
            let physical = p0_layer::PhysicalEvent::Invoke {
                request, attempt, call, journal_cut, ack_cut,
            };
            assert(invoke_refinement_witness(cfg, records, physical)) by {
                assert(acknowledged_start_authorized(
                    cfg, acknowledged, request, attempt,
                ));
            }
        },
        _ => {},
    }
}

pub proof fn step_preserves_acknowledged_invocation_refinement(
    cfg: config_layer::FullConfig,
    state: p0_layer::State,
    event: p0_layer::Event,
)
    requires
        config_layer::full_config_wf(cfg),
        p2_invariant(cfg, state),
        p0_layer::admissibly_enabled(cfg, state, event),
    ensures acknowledged_invocation_refinement(
        cfg,
        p0_layer::apply(cfg, state, event).core.evidence.records,
        p0_layer::apply(cfg, state, event).physical.physical,
    ),
{
    let records = state.core.evidence.records;
    let history = state.physical.physical;
    match event {
        p0_layer::Event::InvokeEvent { .. } => {
            invoke_event_has_refinement_witness(cfg, state, event);
            match p0_layer::event_physical(event) {
                Option::Some(physical) => {
                    invoke_refinement_push(cfg, records, history, physical);
                },
                Option::None => {},
            }
        },
        p0_layer::Event::DeliverEvent {
            request, attempt, observation, journal_cut,
        } => {
            let physical = p0_layer::PhysicalEvent::Delivered {
                request, attempt, observation, journal_cut,
            };
            invoke_refinement_push(cfg, records, history, physical);
        },
        p0_layer::Event::BrokerLinearize { record } => {
            invoke_refinement_record_push(cfg, records, history, record);
        },
        p0_layer::Event::JournalAppendCall { .. }
        | p0_layer::Event::JournalAppendReturn { .. }
        | p0_layer::Event::JournalDiskFull { .. }
        | p0_layer::Event::IgnoreStale { .. }
        | p0_layer::Event::RetryRelease { .. }
        | p0_layer::Event::Crash
        | p0_layer::Event::BeginRecover
        | p0_layer::Event::FinishRecover => {},
    }
}

pub proof fn step_preserves_durable_outcome_refinement(
    cfg: config_layer::FullConfig,
    state: p0_layer::State,
    event: p0_layer::Event,
)
    requires
        p2_invariant(cfg, state),
        p0_layer::admissibly_enabled(cfg, state, event),
    ensures durable_outcomes_follow_deliveries(
        p0_layer::apply(cfg, state, event).core.evidence.records,
        p0_layer::apply(cfg, state, event).physical.physical,
    ),
{
    let records = state.core.evidence.records;
    let history = state.physical.physical;
    match event {
        p0_layer::Event::InvokeEvent {
            request, attempt, call, journal_cut, ack_cut,
        } => {
            outcomes_refinement_history_push(
                records,
                history,
                p0_layer::PhysicalEvent::Invoke {
                    request, attempt, call, journal_cut, ack_cut,
                },
            );
        },
        p0_layer::Event::DeliverEvent {
            request, attempt, observation, journal_cut,
        } => {
            outcomes_refinement_history_push(
                records,
                history,
                p0_layer::PhysicalEvent::Delivered {
                    request, attempt, observation, journal_cut,
                },
            );
        },
        p0_layer::Event::BrokerLinearize { record } => {
            match record {
                replay_layer::JournalRecord::Outcome {
                    request, attempt, observation, ..
                } => {
                    assert(state.core.broker.slot
                        == (record_layer::ExecSlot::Received {
                            request, attempt, observation,
                        }));
                    assert(p1_layer::source_is_delivery(
                        history,
                        state.physical.slot_source,
                        request,
                        attempt,
                        observation,
                    ));
                    slot_source_yields_delivery_before_next_lsn(
                        cfg, state, request, attempt, observation,
                    );
                    outcomes_refinement_record_push(records, history, record);
                },
                _ => {
                    outcomes_refinement_record_push(records, history, record);
                },
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
    }
}

pub proof fn outcome_projection_has_delivery(
    records: Seq<replay_layer::JournalRecord>,
    history: Seq<p0_layer::PhysicalEvent>,
    request: replay_layer::RequestId,
    attempt: replay_layer::AttemptId,
    observation: replay_layer::Observation,
    lsn: replay_layer::Lsn,
)
    requires
        durable_outcomes_follow_deliveries(records, history),
        replay_layer::outcome_lsn(records, request, attempt)
            == Option::Some(lsn),
        replay_layer::outcome_observation(records, request, attempt)
            == Option::Some(observation),
    ensures delivery_before_lsn(
        history, request, attempt, observation, lsn,
    ),
    decreases records.len(),
{
    if records.len() > 0 {
        let prefix = records.drop_last();
        match records.last() {
            replay_layer::JournalRecord::Outcome {
                request: r,
                attempt: a,
                observation: o,
                ..
            } => {
                if r == request && a == attempt {
                    assert(lsn == records.len());
                    assert(o == observation);
                } else {
                    outcome_projection_has_delivery(
                        prefix,
                        history,
                        request,
                        attempt,
                        observation,
                        lsn,
                    );
                }
            },
            _ => {
                outcome_projection_has_delivery(
                    prefix,
                    history,
                    request,
                    attempt,
                    observation,
                    lsn,
                );
            },
        }
    }
}

pub proof fn step_preserves_p2_invariant(
    cfg: config_layer::FullConfig,
    state: p0_layer::State,
    event: p0_layer::Event,
)
    requires
        config_layer::full_config_wf(cfg),
        p2_invariant(cfg, state),
        p0_layer::admissibly_enabled(cfg, state, event),
    ensures p2_invariant(cfg, p0_layer::apply(cfg, state, event)),
{
    step_preserves_invocation_accounting(cfg, state, event);
    step_preserves_acknowledged_invocation_refinement(cfg, state, event);
    step_preserves_durable_outcome_refinement(cfg, state, event);
    p1_layer::step_preserves_p1_invariant(cfg, state, event);
}

pub proof fn initial_p2_invariant(cfg: config_layer::FullConfig)
    requires config_layer::full_config_wf(cfg),
    ensures p2_invariant(cfg, p0_layer::initial_state(cfg)),
{
    p1_layer::initial_p1_invariant(cfg);
}

pub proof fn executable_run_p2_invariant(
    cfg: config_layer::FullConfig,
    events: Seq<p0_layer::Event>,
)
    requires
        config_layer::full_config_wf(cfg),
        p0_layer::admissibly_executable(cfg, events),
    ensures p2_invariant(cfg, p0_layer::run(cfg, events)),
    decreases events.len(),
{
    if events.len() == 0 {
        initial_p2_invariant(cfg);
    } else {
        let prefix = events.drop_last();
        executable_run_p2_invariant(cfg, prefix);
        step_preserves_p2_invariant(
            cfg, p0_layer::run(cfg, prefix), events.last(),
        );
    }
}

pub open spec fn p2_checkpoint(
    cfg: config_layer::FullConfig,
    events: Seq<p0_layer::Event>,
) -> bool {
    let state = p0_layer::run(cfg, events);
    p2_invariant(cfg, state)
        && aggregate_retry_bounds(cfg, state)
        && p0_layer::p0_history_agreement(cfg, state, events)
        && p1_layer::ack_nonretroactive(events)
}

pub proof fn b2_p2_physical_refinement_safety(
    cfg: config_layer::FullConfig,
    events: Seq<p0_layer::Event>,
)
    requires
        config_layer::full_config_wf(cfg),
        p0_layer::admissibly_executable(cfg, events),
    ensures
        p2_checkpoint(cfg, events),
        forall|length: nat| length <= events.len() ==>
            #[trigger] p2_checkpoint(cfg, events.take(length as int)),
{
    executable_run_p2_invariant(cfg, events);
    accounting_implies_aggregate_retry_bounds(
        cfg, p0_layer::run(cfg, events),
    );
    p0_layer::run_history_agreement(cfg, events);
    p1_layer::executable_ack_nonretroactive(cfg, events);
    assert forall|length: nat| length <= events.len() implies
        #[trigger] p2_checkpoint(cfg, events.take(length as int)) by {
        p0_layer::executable_prefix(cfg, events, length);
        executable_run_p2_invariant(cfg, events.take(length as int));
        accounting_implies_aggregate_retry_bounds(
            cfg, p0_layer::run(cfg, events.take(length as int)),
        );
        p0_layer::run_history_agreement(cfg, events.take(length as int));
        p1_layer::executable_ack_nonretroactive(
            cfg, events.take(length as int),
        );
    }
}

} // verus!
