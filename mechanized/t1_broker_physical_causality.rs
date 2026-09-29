use vstd::prelude::*;

#[path = "t1_broker_physical.rs"]
pub mod p0_layer;

verus! {

use p0_layer::config_layer;
use config_layer::broker_layer as record_layer;
use record_layer::query_layer::c1_layer::replay_layer;
use record_layer::query_layer::c1_layer::append_layer;

// B2-P1 adds physical-history order, per-attempt uniqueness, immutable-call
// and cut evidence, and executor/source agreement to B2-P0.  It deliberately
// does not yet claim terminal provenance, aggregate retry bounds, adapter
// refinement, or the complete T1 BrokerInvariant.

pub open spec fn is_invoke_for(
    event: p0_layer::PhysicalEvent,
    request: replay_layer::RequestId,
    attempt: replay_layer::AttemptId,
) -> bool {
    match event {
        p0_layer::PhysicalEvent::Invoke {
            request: r, attempt: a, ..
        } => r == request && a == attempt,
        p0_layer::PhysicalEvent::Delivered { .. } => false,
    }
}

pub open spec fn is_delivery_for(
    event: p0_layer::PhysicalEvent,
    request: replay_layer::RequestId,
    attempt: replay_layer::AttemptId,
) -> bool {
    match event {
        p0_layer::PhysicalEvent::Delivered {
            request: r, attempt: a, ..
        } => r == request && a == attempt,
        p0_layer::PhysicalEvent::Invoke { .. } => false,
    }
}

pub open spec fn invoke_count(
    history: Seq<p0_layer::PhysicalEvent>,
    request: replay_layer::RequestId,
    attempt: replay_layer::AttemptId,
) -> nat
    decreases history.len()
{
    if history.len() == 0 {
        0
    } else {
        invoke_count(history.drop_last(), request, attempt)
            + if is_invoke_for(history.last(), request, attempt) { 1nat } else { 0nat }
    }
}

pub open spec fn delivery_count(
    history: Seq<p0_layer::PhysicalEvent>,
    request: replay_layer::RequestId,
    attempt: replay_layer::AttemptId,
) -> nat
    decreases history.len()
{
    if history.len() == 0 {
        0
    } else {
        delivery_count(history.drop_last(), request, attempt)
            + if is_delivery_for(history.last(), request, attempt) { 1nat } else { 0nat }
    }
}

pub open spec fn invoke_index(
    history: Seq<p0_layer::PhysicalEvent>,
    request: replay_layer::RequestId,
    attempt: replay_layer::AttemptId,
) -> Option<nat>
    decreases history.len()
{
    if history.len() == 0 {
        Option::None
    } else if is_invoke_for(history.last(), request, attempt) {
        Option::Some((history.len() - 1) as nat)
    } else {
        invoke_index(history.drop_last(), request, attempt)
    }
}

pub open spec fn delivery_index(
    history: Seq<p0_layer::PhysicalEvent>,
    request: replay_layer::RequestId,
    attempt: replay_layer::AttemptId,
) -> Option<nat>
    decreases history.len()
{
    if history.len() == 0 {
        Option::None
    } else if is_delivery_for(history.last(), request, attempt) {
        Option::Some((history.len() - 1) as nat)
    } else {
        delivery_index(history.drop_last(), request, attempt)
    }
}

pub open spec fn nat_occurs(values: Seq<nat>, value: nat) -> bool
    decreases values.len()
{
    values.len() > 0
        && (values.last() == value || nat_occurs(values.drop_last(), value))
}

// Recursive uniqueness records the exact fact needed when a physical event is
// appended: its request/attempt pair has not previously carried that kind.
pub open spec fn physical_unique(history: Seq<p0_layer::PhysicalEvent>) -> bool
    decreases history.len()
{
    history.len() == 0 || {
        let prefix = history.drop_last();
        physical_unique(prefix)
            && match history.last() {
                p0_layer::PhysicalEvent::Invoke { request, attempt, .. } => {
                    invoke_count(prefix, request, attempt) == 0
                },
                p0_layer::PhysicalEvent::Delivered { request, attempt, .. } => {
                    delivery_count(prefix, request, attempt) == 0
                },
            }
    }
}

// Every accepted delivery follows exactly one invocation in its strict
// physical-history prefix.
pub open spec fn physical_ordered(history: Seq<p0_layer::PhysicalEvent>) -> bool
    decreases history.len()
{
    history.len() == 0 || {
        let prefix = history.drop_last();
        physical_ordered(prefix)
            && match history.last() {
                p0_layer::PhysicalEvent::Delivered { request, attempt, .. } => {
                    invoke_count(prefix, request, attempt) == 1
                },
                p0_layer::PhysicalEvent::Invoke { .. } => true,
            }
    }
}

// Invoke cuts name a canonical call and an already acknowledged Start.  The
// recursive predicate is interpreted against the current append-only Journal
// and acknowledgment histories, so later record/ack extensions are monotone.
pub open spec fn physical_cuts_valid(
    cfg: config_layer::FullConfig,
    records: Seq<replay_layer::JournalRecord>,
    ack_cuts: Seq<nat>,
    history: Seq<p0_layer::PhysicalEvent>,
) -> bool
    decreases history.len()
{
    history.len() == 0 || {
        let prefix = history.drop_last();
        physical_cuts_valid(cfg, records, ack_cuts, prefix)
            && match history.last() {
                p0_layer::PhysicalEvent::Invoke {
                    request, attempt, call, journal_cut, ack_cut,
                } => {
                    call == config_layer::canonical_call(cfg, request)
                        && 1 <= ack_cut
                        && ack_cut <= journal_cut
                        && journal_cut <= records.len()
                        && nat_occurs(ack_cuts, ack_cut)
                        && replay_layer::start_lsn(
                            records.take(ack_cut as int), request, attempt,
                        ).is_some()
                },
                p0_layer::PhysicalEvent::Delivered { journal_cut, .. } => {
                    journal_cut <= records.len()
                },
            }
    }
}

pub open spec fn source_is_delivery(
    history: Seq<p0_layer::PhysicalEvent>,
    source: Option<p0_layer::PhysicalIndex>,
    request: replay_layer::RequestId,
    attempt: replay_layer::AttemptId,
    observation: replay_layer::Observation,
) -> bool {
    match source {
        Option::None => false,
        Option::Some(index) => index < history.len()
            && match history[index as int] {
                p0_layer::PhysicalEvent::Delivered {
                    request: r, attempt: a, observation: o, ..
                } => r == request && a == attempt && o == observation,
                p0_layer::PhysicalEvent::Invoke { .. } => false,
            },
    }
}

pub open spec fn physical_slot_agreement(state: p0_layer::State) -> bool {
    let history = state.physical.physical;
    match state.core.broker.slot {
        record_layer::ExecSlot::Idle => state.physical.slot_source.is_none(),
        record_layer::ExecSlot::Ready { request, attempt } => {
            state.physical.slot_source.is_none()
                && invoke_count(history, request, attempt) == 0
                && delivery_count(history, request, attempt) == 0
        },
        record_layer::ExecSlot::InFlight { request, attempt } => {
            state.physical.slot_source.is_none()
                && invoke_count(history, request, attempt) == 1
                && delivery_count(history, request, attempt) == 0
        },
        record_layer::ExecSlot::Received {
            request, attempt, observation,
        } => {
            invoke_count(history, request, attempt) == 1
                && delivery_count(history, request, attempt) == 1
                && source_is_delivery(
                    history, state.physical.slot_source,
                    request, attempt, observation,
                )
        },
        record_layer::ExecSlot::ObservedSuccess {
            request, attempt, value,
        } => source_is_delivery(
            history, state.physical.slot_source, request, attempt,
            replay_layer::Observation::Success(value),
        ),
        record_layer::ExecSlot::ObservedFailure { request, attempt } => {
            source_is_delivery(
                history, state.physical.slot_source, request, attempt,
                replay_layer::Observation::Failure,
            )
        },
        record_layer::ExecSlot::ObservedUnknown {
            request, attempt, reason,
        } => match reason {
            replay_layer::UnknownReason::AmbiguousOutcome => source_is_delivery(
                history, state.physical.slot_source, request, attempt,
                replay_layer::Observation::Ambiguous,
            ),
            replay_layer::UnknownReason::InvalidResultReason => {
                exists|bad: replay_layer::InvalidValue| #![auto]
                    source_is_delivery(
                        history, state.physical.slot_source, request, attempt,
                        replay_layer::Observation::InvalidResult(bad),
                    )
            },
            replay_layer::UnknownReason::Exhausted
            | replay_layer::UnknownReason::Recovery
            | replay_layer::UnknownReason::NonConclusiveFailure => false,
        },
    }
}

pub open spec fn p1_invariant(
    cfg: config_layer::FullConfig,
    state: p0_layer::State,
) -> bool {
    p0_layer::p0_invariant(cfg, state)
        && physical_unique(state.physical.physical)
        && physical_ordered(state.physical.physical)
        && physical_cuts_valid(
            cfg,
            state.core.evidence.records,
            state.core.evidence.ack_cuts,
            state.physical.physical,
        )
        && physical_slot_agreement(state)
}

pub proof fn invoke_count_push(
    history: Seq<p0_layer::PhysicalEvent>,
    event: p0_layer::PhysicalEvent,
    request: replay_layer::RequestId,
    attempt: replay_layer::AttemptId,
)
    ensures invoke_count(history.push(event), request, attempt)
        == invoke_count(history, request, attempt)
            + if is_invoke_for(event, request, attempt) { 1nat } else { 0nat },
{
    assert(history.push(event).drop_last() =~= history);
    assert(history.push(event).last() == event);
}

pub proof fn delivery_count_push(
    history: Seq<p0_layer::PhysicalEvent>,
    event: p0_layer::PhysicalEvent,
    request: replay_layer::RequestId,
    attempt: replay_layer::AttemptId,
)
    ensures delivery_count(history.push(event), request, attempt)
        == delivery_count(history, request, attempt)
            + if is_delivery_for(event, request, attempt) { 1nat } else { 0nat },
{
    assert(history.push(event).drop_last() =~= history);
    assert(history.push(event).last() == event);
}

pub proof fn nat_occurs_push(values: Seq<nat>, value: nat, added: nat)
    requires nat_occurs(values, value),
    ensures nat_occurs(values.push(added), value),
{
    assert(values.push(added).drop_last() =~= values);
    assert(values.push(added).last() == added);
}

pub proof fn acknowledged_cut_occurs(state: p0_layer::State)
    requires
        append_layer::b1_invariant(record_layer::append_view(state.core)),
        state.core.evidence.acknowledged_prefix.len() > 0,
    ensures nat_occurs(
        state.core.evidence.ack_cuts,
        state.core.evidence.acknowledged_prefix.len(),
    ),
{
    assert(state.core.evidence.acknowledged_prefix.len()
        == append_layer::last_or_zero(state.core.evidence.ack_cuts));
    assert(state.core.evidence.ack_cuts.len() > 0) by {
        if state.core.evidence.ack_cuts.len() == 0 {
            assert(append_layer::last_or_zero(state.core.evidence.ack_cuts) == 0);
        }
    }
    assert(state.core.evidence.ack_cuts.last()
        == state.core.evidence.acknowledged_prefix.len());
}

pub proof fn cuts_valid_record_push(
    cfg: config_layer::FullConfig,
    records: Seq<replay_layer::JournalRecord>,
    ack_cuts: Seq<nat>,
    history: Seq<p0_layer::PhysicalEvent>,
    record: replay_layer::JournalRecord,
)
    requires physical_cuts_valid(cfg, records, ack_cuts, history),
    ensures physical_cuts_valid(
        cfg, records.push(record), ack_cuts, history,
    ),
    decreases history.len(),
{
    if history.len() > 0 {
        let prefix = history.drop_last();
        cuts_valid_record_push(cfg, records, ack_cuts, prefix, record);
        match history.last() {
            p0_layer::PhysicalEvent::Invoke { ack_cut, journal_cut, .. } => {
                assert(ack_cut <= journal_cut);
                assert(journal_cut <= records.len());
                append_layer::take_push_stable(records, record, ack_cut);
            },
            p0_layer::PhysicalEvent::Delivered { .. } => {},
        }
    }
}

pub proof fn cuts_valid_ack_push(
    cfg: config_layer::FullConfig,
    records: Seq<replay_layer::JournalRecord>,
    ack_cuts: Seq<nat>,
    history: Seq<p0_layer::PhysicalEvent>,
    cut: nat,
)
    requires physical_cuts_valid(cfg, records, ack_cuts, history),
    ensures physical_cuts_valid(
        cfg, records, ack_cuts.push(cut), history,
    ),
    decreases history.len(),
{
    if history.len() > 0 {
        let prefix = history.drop_last();
        cuts_valid_ack_push(cfg, records, ack_cuts, prefix, cut);
        match history.last() {
            p0_layer::PhysicalEvent::Invoke { ack_cut, .. } => {
                nat_occurs_push(ack_cuts, ack_cut, cut);
            },
            p0_layer::PhysicalEvent::Delivered { .. } => {},
        }
    }
}

pub proof fn cuts_valid_push_invoke(
    cfg: config_layer::FullConfig,
    records: Seq<replay_layer::JournalRecord>,
    ack_cuts: Seq<nat>,
    history: Seq<p0_layer::PhysicalEvent>,
    event: p0_layer::PhysicalEvent,
)
    requires
        physical_cuts_valid(cfg, records, ack_cuts, history),
        match event {
            p0_layer::PhysicalEvent::Invoke {
                request, attempt, call, journal_cut, ack_cut,
            } => call == config_layer::canonical_call(cfg, request)
                && 1 <= ack_cut
                && ack_cut <= journal_cut
                && journal_cut <= records.len()
                && nat_occurs(ack_cuts, ack_cut)
                && replay_layer::start_lsn(
                    records.take(ack_cut as int), request, attempt,
                ).is_some(),
            p0_layer::PhysicalEvent::Delivered { .. } => false,
        },
    ensures physical_cuts_valid(
        cfg, records, ack_cuts, history.push(event),
    ),
{
    assert(history.push(event).drop_last() =~= history);
    assert(history.push(event).last() == event);
}

pub proof fn cuts_valid_push_delivery(
    cfg: config_layer::FullConfig,
    records: Seq<replay_layer::JournalRecord>,
    ack_cuts: Seq<nat>,
    history: Seq<p0_layer::PhysicalEvent>,
    event: p0_layer::PhysicalEvent,
)
    requires
        physical_cuts_valid(cfg, records, ack_cuts, history),
        match event {
            p0_layer::PhysicalEvent::Delivered { journal_cut, .. } => {
                journal_cut <= records.len()
            },
            p0_layer::PhysicalEvent::Invoke { .. } => false,
        },
    ensures physical_cuts_valid(
        cfg, records, ack_cuts, history.push(event),
    ),
{
    assert(history.push(event).drop_last() =~= history);
    assert(history.push(event).last() == event);
}

pub proof fn unique_push_invoke(
    history: Seq<p0_layer::PhysicalEvent>,
    event: p0_layer::PhysicalEvent,
    request: replay_layer::RequestId,
    attempt: replay_layer::AttemptId,
)
    requires
        physical_unique(history),
        event is Invoke,
        is_invoke_for(event, request, attempt),
        invoke_count(history, request, attempt) == 0,
    ensures physical_unique(history.push(event)),
{
    assert(history.push(event).drop_last() =~= history);
    assert(history.push(event).last() == event);
    match event {
        p0_layer::PhysicalEvent::Invoke {
            request: r, attempt: a, ..
        } => {
            assert(r == request && a == attempt);
        },
        p0_layer::PhysicalEvent::Delivered { .. } => {},
    }
}

pub proof fn unique_push_delivery(
    history: Seq<p0_layer::PhysicalEvent>,
    event: p0_layer::PhysicalEvent,
    request: replay_layer::RequestId,
    attempt: replay_layer::AttemptId,
)
    requires
        physical_unique(history),
        event is Delivered,
        is_delivery_for(event, request, attempt),
        delivery_count(history, request, attempt) == 0,
    ensures physical_unique(history.push(event)),
{
    assert(history.push(event).drop_last() =~= history);
    assert(history.push(event).last() == event);
    match event {
        p0_layer::PhysicalEvent::Delivered {
            request: r, attempt: a, ..
        } => {
            assert(r == request && a == attempt);
        },
        p0_layer::PhysicalEvent::Invoke { .. } => {},
    }
}

pub proof fn ordered_push_invoke(
    history: Seq<p0_layer::PhysicalEvent>,
    event: p0_layer::PhysicalEvent,
)
    requires physical_ordered(history), event is Invoke,
    ensures physical_ordered(history.push(event)),
{
    assert(history.push(event).drop_last() =~= history);
    assert(history.push(event).last() == event);
}

pub proof fn ordered_push_delivery(
    history: Seq<p0_layer::PhysicalEvent>,
    event: p0_layer::PhysicalEvent,
    request: replay_layer::RequestId,
    attempt: replay_layer::AttemptId,
)
    requires
        physical_ordered(history),
        event is Delivered,
        is_delivery_for(event, request, attempt),
        invoke_count(history, request, attempt) == 1,
    ensures physical_ordered(history.push(event)),
{
    assert(history.push(event).drop_last() =~= history);
    assert(history.push(event).last() == event);
    match event {
        p0_layer::PhysicalEvent::Delivered {
            request: r, attempt: a, ..
        } => assert(r == request && a == attempt),
        p0_layer::PhysicalEvent::Invoke { .. } => {},
    }
}

pub proof fn source_is_new_delivery(
    history: Seq<p0_layer::PhysicalEvent>,
    request: replay_layer::RequestId,
    attempt: replay_layer::AttemptId,
    observation: replay_layer::Observation,
    journal_cut: nat,
)
    ensures source_is_delivery(
        history.push(p0_layer::PhysicalEvent::Delivered {
            request, attempt, observation, journal_cut,
        }),
        Option::Some(history.len()),
        request,
        attempt,
        observation,
    ),
{
    let event = p0_layer::PhysicalEvent::Delivered {
        request, attempt, observation, journal_cut,
    };
    assert(history.push(event).len() == history.len() + 1);
    assert(history.push(event)[history.len() as int] == event);
}

pub proof fn invalid_delivery_has_witness(
    history: Seq<p0_layer::PhysicalEvent>,
    source: Option<p0_layer::PhysicalIndex>,
    request: replay_layer::RequestId,
    attempt: replay_layer::AttemptId,
    bad: replay_layer::InvalidValue,
)
    requires source_is_delivery(
        history, source, request, attempt,
        replay_layer::Observation::InvalidResult(bad),
    ),
    ensures exists|witness: replay_layer::InvalidValue| #![auto]
        source_is_delivery(
            history, source, request, attempt,
            replay_layer::Observation::InvalidResult(witness),
        ),
{
    let witness = bad;
}

pub proof fn observed_invalid_source_is_slot_agreement(
    state: p0_layer::State,
    request: replay_layer::RequestId,
    attempt: replay_layer::AttemptId,
)
    requires
        state.core.broker.slot
            == (record_layer::ExecSlot::ObservedUnknown {
                request,
                attempt,
                reason: replay_layer::UnknownReason::InvalidResultReason,
            }),
        exists|bad: replay_layer::InvalidValue| #![auto]
            source_is_delivery(
                state.physical.physical,
                state.physical.slot_source,
                request,
                attempt,
                replay_layer::Observation::InvalidResult(bad),
            ),
    ensures physical_slot_agreement(state),
{
    match state.core.broker.slot {
        record_layer::ExecSlot::ObservedUnknown {
            request: r, attempt: a, reason,
        } => {
            assert(r == request && a == attempt);
            assert(reason == replay_layer::UnknownReason::InvalidResultReason);
            match reason {
                replay_layer::UnknownReason::InvalidResultReason => {},
                replay_layer::UnknownReason::Exhausted
                | replay_layer::UnknownReason::Recovery
                | replay_layer::UnknownReason::NonConclusiveFailure
                | replay_layer::UnknownReason::AmbiguousOutcome => {},
            }
        },
        record_layer::ExecSlot::Idle
        | record_layer::ExecSlot::Ready { .. }
        | record_layer::ExecSlot::InFlight { .. }
        | record_layer::ExecSlot::Received { .. }
        | record_layer::ExecSlot::ObservedSuccess { .. }
        | record_layer::ExecSlot::ObservedFailure { .. } => {},
    }
}

pub proof fn start_lsn_take_cover(
    records: Seq<replay_layer::JournalRecord>,
    request: replay_layer::RequestId,
    attempt: replay_layer::AttemptId,
    cut: nat,
    start: replay_layer::Lsn,
)
    requires
        replay_layer::start_lsn(records, request, attempt)
            == Option::Some(start),
        start <= cut,
        cut <= records.len(),
    ensures
        replay_layer::start_lsn(
            records.take(cut as int), request, attempt,
        ) == Option::Some(start),
    decreases records.len(),
{
    if cut == records.len() {
        assert(records.take(cut as int) =~= records);
    } else {
        assert(records.len() > 0);
        assert(cut < records.len());
        let prefix = records.drop_last();
        match records.last() {
            replay_layer::JournalRecord::Start {
                request: r, attempt: a, ..
            } => {
                if r == request && a == attempt {
                    assert(start == records.len());
                    assert(false);
                } else {
                    assert(replay_layer::start_lsn(prefix, request, attempt)
                        == Option::Some(start));
                    start_lsn_take_cover(
                        prefix, request, attempt, cut, start,
                    );
                    assert(records.take(cut as int) =~= prefix.take(cut as int));
                }
            },
            replay_layer::JournalRecord::Authorize { .. }
            | replay_layer::JournalRecord::Revoke { .. }
            | replay_layer::JournalRecord::Prepare { .. }
            | replay_layer::JournalRecord::Arm { .. }
            | replay_layer::JournalRecord::Outcome { .. }
            | replay_layer::JournalRecord::CommitRec { .. }
            | replay_layer::JournalRecord::FailRec { .. }
            | replay_layer::JournalRecord::UnknownRec { .. } => {
                assert(replay_layer::start_lsn(prefix, request, attempt)
                    == Option::Some(start));
                start_lsn_take_cover(prefix, request, attempt, cut, start);
                assert(records.take(cut as int) =~= prefix.take(cut as int));
            },
        }
    }
}

pub proof fn invoke_preserves_unique_order(
    cfg: config_layer::FullConfig,
    state: p0_layer::State,
    event: p0_layer::Event,
)
    requires
        p1_invariant(cfg, state),
        p0_layer::admissibly_enabled(cfg, state, event),
        event is InvokeEvent,
    ensures
        physical_unique(p0_layer::apply(cfg, state, event).physical.physical),
        physical_ordered(p0_layer::apply(cfg, state, event).physical.physical),
{
    match event {
        p0_layer::Event::InvokeEvent {
            request, attempt, call, journal_cut, ack_cut,
        } => {
            let history = state.physical.physical;
            let physical = p0_layer::PhysicalEvent::Invoke {
                request, attempt, call, journal_cut, ack_cut,
            };
            assert(state.core.broker.slot
                == (record_layer::ExecSlot::Ready { request, attempt }));
            assert(invoke_count(history, request, attempt) == 0);
            assert(delivery_count(history, request, attempt) == 0);
            unique_push_invoke(history, physical, request, attempt);
            ordered_push_invoke(history, physical);
        },
        p0_layer::Event::JournalAppendCall { .. }
        | p0_layer::Event::BrokerLinearize { .. }
        | p0_layer::Event::JournalAppendReturn { .. }
        | p0_layer::Event::JournalDiskFull { .. }
        | p0_layer::Event::DeliverEvent { .. }
        | p0_layer::Event::IgnoreStale { .. }
        | p0_layer::Event::RetryRelease { .. }
        | p0_layer::Event::Crash
        | p0_layer::Event::BeginRecover
        | p0_layer::Event::FinishRecover => {},
    }
}

pub proof fn invoke_preserves_cuts(
    cfg: config_layer::FullConfig,
    state: p0_layer::State,
    event: p0_layer::Event,
)
    requires
        p1_invariant(cfg, state),
        p0_layer::admissibly_enabled(cfg, state, event),
        event is InvokeEvent,
    ensures physical_cuts_valid(
        cfg,
        p0_layer::apply(cfg, state, event).core.evidence.records,
        p0_layer::apply(cfg, state, event).core.evidence.ack_cuts,
        p0_layer::apply(cfg, state, event).physical.physical,
    ),
{
    match event {
        p0_layer::Event::InvokeEvent {
            request, attempt, call, journal_cut, ack_cut,
        } => {
            let history = state.physical.physical;
            let physical = p0_layer::PhysicalEvent::Invoke {
                request, attempt, call, journal_cut, ack_cut,
            };
            assert(journal_cut == state.core.evidence.records.len());
            assert(ack_cut == state.core.evidence.acknowledged_prefix.len());
            assert(call == config_layer::canonical_call(cfg, request));
            assert(append_layer::b1_invariant(
                record_layer::append_view(state.core),
            ));
            assert(append_layer::is_prefix(
                state.core.evidence.acknowledged_prefix,
                state.core.evidence.records,
            ));
            assert(ack_cut <= journal_cut);
            match replay_layer::start_lsn(
                state.core.evidence.records, request, attempt,
            ) {
                Option::Some(start) => {
                    assert(1 <= start && start <= ack_cut);
                    acknowledged_cut_occurs(state);
                    start_lsn_take_cover(
                        state.core.evidence.records,
                        request,
                        attempt,
                        ack_cut,
                        start,
                    );
                },
                Option::None => {},
            }
            cuts_valid_push_invoke(
                cfg,
                state.core.evidence.records,
                state.core.evidence.ack_cuts,
                history,
                physical,
            );
        },
        p0_layer::Event::JournalAppendCall { .. }
        | p0_layer::Event::BrokerLinearize { .. }
        | p0_layer::Event::JournalAppendReturn { .. }
        | p0_layer::Event::JournalDiskFull { .. }
        | p0_layer::Event::DeliverEvent { .. }
        | p0_layer::Event::IgnoreStale { .. }
        | p0_layer::Event::RetryRelease { .. }
        | p0_layer::Event::Crash
        | p0_layer::Event::BeginRecover
        | p0_layer::Event::FinishRecover => {},
    }
}

pub proof fn invoke_preserves_slot_agreement(
    cfg: config_layer::FullConfig,
    state: p0_layer::State,
    event: p0_layer::Event,
)
    requires
        p1_invariant(cfg, state),
        p0_layer::admissibly_enabled(cfg, state, event),
        event is InvokeEvent,
    ensures physical_slot_agreement(p0_layer::apply(cfg, state, event)),
{
    match event {
        p0_layer::Event::InvokeEvent {
            request, attempt, call, journal_cut, ack_cut,
        } => {
            let history = state.physical.physical;
            let physical = p0_layer::PhysicalEvent::Invoke {
                request, attempt, call, journal_cut, ack_cut,
            };
            assert(state.core.broker.slot
                == (record_layer::ExecSlot::Ready { request, attempt }));
            assert(invoke_count(history, request, attempt) == 0);
            assert(delivery_count(history, request, attempt) == 0);
            invoke_count_push(history, physical, request, attempt);
            delivery_count_push(history, physical, request, attempt);
        },
        p0_layer::Event::JournalAppendCall { .. }
        | p0_layer::Event::BrokerLinearize { .. }
        | p0_layer::Event::JournalAppendReturn { .. }
        | p0_layer::Event::JournalDiskFull { .. }
        | p0_layer::Event::DeliverEvent { .. }
        | p0_layer::Event::IgnoreStale { .. }
        | p0_layer::Event::RetryRelease { .. }
        | p0_layer::Event::Crash
        | p0_layer::Event::BeginRecover
        | p0_layer::Event::FinishRecover => {},
    }
}

pub proof fn invoke_preserves_physical_facts(
    cfg: config_layer::FullConfig,
    state: p0_layer::State,
    event: p0_layer::Event,
)
    requires
        p1_invariant(cfg, state),
        p0_layer::admissibly_enabled(cfg, state, event),
        event is InvokeEvent,
    ensures
        physical_unique(p0_layer::apply(cfg, state, event).physical.physical),
        physical_ordered(p0_layer::apply(cfg, state, event).physical.physical),
        physical_cuts_valid(
            cfg,
            p0_layer::apply(cfg, state, event).core.evidence.records,
            p0_layer::apply(cfg, state, event).core.evidence.ack_cuts,
            p0_layer::apply(cfg, state, event).physical.physical,
        ),
        physical_slot_agreement(p0_layer::apply(cfg, state, event)),
{
    invoke_preserves_unique_order(cfg, state, event);
    invoke_preserves_cuts(cfg, state, event);
    invoke_preserves_slot_agreement(cfg, state, event);
}

pub proof fn deliver_preserves_physical_facts(
    cfg: config_layer::FullConfig,
    state: p0_layer::State,
    event: p0_layer::Event,
)
    requires
        p1_invariant(cfg, state),
        p0_layer::admissibly_enabled(cfg, state, event),
        event is DeliverEvent,
    ensures
        physical_unique(p0_layer::apply(cfg, state, event).physical.physical),
        physical_ordered(p0_layer::apply(cfg, state, event).physical.physical),
        physical_cuts_valid(
            cfg,
            p0_layer::apply(cfg, state, event).core.evidence.records,
            p0_layer::apply(cfg, state, event).core.evidence.ack_cuts,
            p0_layer::apply(cfg, state, event).physical.physical,
        ),
        physical_slot_agreement(p0_layer::apply(cfg, state, event)),
{
    match event {
        p0_layer::Event::DeliverEvent {
            request, attempt, observation, journal_cut,
        } => {
            let history = state.physical.physical;
            let physical = p0_layer::PhysicalEvent::Delivered {
                request, attempt, observation, journal_cut,
            };
            assert(state.core.broker.slot
                == (record_layer::ExecSlot::InFlight { request, attempt }));
            assert(invoke_count(history, request, attempt) == 1);
            assert(delivery_count(history, request, attempt) == 0);
            unique_push_delivery(history, physical, request, attempt);
            ordered_push_delivery(history, physical, request, attempt);
            invoke_count_push(history, physical, request, attempt);
            delivery_count_push(history, physical, request, attempt);
            assert(journal_cut == state.core.evidence.records.len());
            cuts_valid_push_delivery(
                cfg,
                state.core.evidence.records,
                state.core.evidence.ack_cuts,
                history,
                physical,
            );
            source_is_new_delivery(
                history, request, attempt, observation, journal_cut,
            );
        },
        p0_layer::Event::JournalAppendCall { .. }
        | p0_layer::Event::BrokerLinearize { .. }
        | p0_layer::Event::JournalAppendReturn { .. }
        | p0_layer::Event::JournalDiskFull { .. }
        | p0_layer::Event::InvokeEvent { .. }
        | p0_layer::Event::IgnoreStale { .. }
        | p0_layer::Event::RetryRelease { .. }
        | p0_layer::Event::Crash
        | p0_layer::Event::BeginRecover
        | p0_layer::Event::FinishRecover => {},
    }
}

pub proof fn start_lsn_some_implies_count_positive(
    records: Seq<replay_layer::JournalRecord>,
    request: replay_layer::RequestId,
    attempt: replay_layer::AttemptId,
)
    requires replay_layer::start_lsn(records, request, attempt).is_some(),
    ensures replay_layer::start_count(records, request, attempt) > 0,
    decreases records.len(),
{
    if records.len() > 0 {
        let prefix = records.drop_last();
        match records.last() {
            replay_layer::JournalRecord::Start {
                request: r, attempt: a, ..
            } => {
                if r == request && a == attempt {
                    assert(replay_layer::start_count(records, request, attempt)
                        == replay_layer::start_count(prefix, request, attempt) + 1);
                } else {
                    start_lsn_some_implies_count_positive(
                        prefix, request, attempt,
                    );
                }
            },
            replay_layer::JournalRecord::Authorize { .. }
            | replay_layer::JournalRecord::Revoke { .. }
            | replay_layer::JournalRecord::Prepare { .. }
            | replay_layer::JournalRecord::Arm { .. }
            | replay_layer::JournalRecord::Outcome { .. }
            | replay_layer::JournalRecord::CommitRec { .. }
            | replay_layer::JournalRecord::FailRec { .. }
            | replay_layer::JournalRecord::UnknownRec { .. } => {
                start_lsn_some_implies_count_positive(
                    prefix, request, attempt,
                );
            },
        }
    }
}

pub proof fn start_count_take_le(
    records: Seq<replay_layer::JournalRecord>,
    request: replay_layer::RequestId,
    attempt: replay_layer::AttemptId,
    cut: nat,
)
    requires cut <= records.len(),
    ensures replay_layer::start_count(
        records.take(cut as int), request, attempt,
    ) <= replay_layer::start_count(records, request, attempt),
    decreases records.len() - cut,
{
    if cut == records.len() {
        assert(records.take(cut as int) =~= records);
    } else {
        assert(records.len() > 0);
        let prefix = records.drop_last();
        assert(cut <= prefix.len());
        start_count_take_le(prefix, request, attempt, cut);
        assert(records.take(cut as int) =~= prefix.take(cut as int));
        match records.last() {
            replay_layer::JournalRecord::Start { .. }
            | replay_layer::JournalRecord::Authorize { .. }
            | replay_layer::JournalRecord::Revoke { .. }
            | replay_layer::JournalRecord::Prepare { .. }
            | replay_layer::JournalRecord::Arm { .. }
            | replay_layer::JournalRecord::Outcome { .. }
            | replay_layer::JournalRecord::CommitRec { .. }
            | replay_layer::JournalRecord::FailRec { .. }
            | replay_layer::JournalRecord::UnknownRec { .. } => {},
        }
    }
}

pub proof fn no_invoke_without_start(
    cfg: config_layer::FullConfig,
    records: Seq<replay_layer::JournalRecord>,
    ack_cuts: Seq<nat>,
    history: Seq<p0_layer::PhysicalEvent>,
    request: replay_layer::RequestId,
    attempt: replay_layer::AttemptId,
)
    requires
        physical_cuts_valid(cfg, records, ack_cuts, history),
        replay_layer::start_count(records, request, attempt) == 0,
    ensures invoke_count(history, request, attempt) == 0,
    decreases history.len(),
{
    if history.len() > 0 {
        let prefix = history.drop_last();
        no_invoke_without_start(
            cfg, records, ack_cuts, prefix, request, attempt,
        );
        match history.last() {
            p0_layer::PhysicalEvent::Invoke {
                request: r, attempt: a, ack_cut, journal_cut, ..
            } => {
                if r == request && a == attempt {
                    assert(ack_cut <= journal_cut);
                    assert(journal_cut <= records.len());
                    assert(replay_layer::start_lsn(
                        records.take(ack_cut as int), request, attempt,
                    ).is_some());
                    start_lsn_some_implies_count_positive(
                        records.take(ack_cut as int), request, attempt,
                    );
                    start_count_take_le(records, request, attempt, ack_cut);
                    assert(false);
                }
            },
            p0_layer::PhysicalEvent::Delivered { .. } => {},
        }
    }
}

pub proof fn no_delivery_without_invoke(
    history: Seq<p0_layer::PhysicalEvent>,
    request: replay_layer::RequestId,
    attempt: replay_layer::AttemptId,
)
    requires
        physical_ordered(history),
        invoke_count(history, request, attempt) == 0,
    ensures delivery_count(history, request, attempt) == 0,
    decreases history.len(),
{
    if history.len() > 0 {
        let prefix = history.drop_last();
        match history.last() {
            p0_layer::PhysicalEvent::Invoke { .. } => {
                assert(invoke_count(prefix, request, attempt) == 0);
                no_delivery_without_invoke(prefix, request, attempt);
            },
            p0_layer::PhysicalEvent::Delivered {
                request: r, attempt: a, ..
            } => {
                assert(invoke_count(prefix, request, attempt) == 0);
                if r == request && a == attempt {
                    assert(invoke_count(prefix, request, attempt) == 1);
                    assert(false);
                } else {
                    no_delivery_without_invoke(prefix, request, attempt);
                }
            },
        }
    }
}

pub proof fn record_event_preserves_physical_history(
    cfg: config_layer::FullConfig,
    state: p0_layer::State,
    event: p0_layer::Event,
)
    requires
        p1_invariant(cfg, state),
        p0_layer::admissibly_enabled(cfg, state, event),
        !(event is InvokeEvent),
        !(event is DeliverEvent),
    ensures
        physical_unique(p0_layer::apply(cfg, state, event).physical.physical),
        physical_ordered(p0_layer::apply(cfg, state, event).physical.physical),
        physical_cuts_valid(
            cfg,
            p0_layer::apply(cfg, state, event).core.evidence.records,
            p0_layer::apply(cfg, state, event).core.evidence.ack_cuts,
            p0_layer::apply(cfg, state, event).physical.physical,
        ),
{
    match event {
        p0_layer::Event::BrokerLinearize { record } => {
            cuts_valid_record_push(
                cfg,
                state.core.evidence.records,
                state.core.evidence.ack_cuts,
                state.physical.physical,
                record,
            );
        },
        p0_layer::Event::JournalAppendReturn { cut } => {
            cuts_valid_ack_push(
                cfg,
                state.core.evidence.records,
                state.core.evidence.ack_cuts,
                state.physical.physical,
                cut,
            );
        },
        p0_layer::Event::JournalAppendCall { .. }
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

pub proof fn start_linearize_preserves_physical_slot(
    cfg: config_layer::FullConfig,
    state: p0_layer::State,
    record: replay_layer::JournalRecord,
)
    requires
        config_layer::full_config_wf(cfg),
        p1_invariant(cfg, state),
        record is Start,
        p0_layer::admissibly_enabled(
            cfg, state, p0_layer::Event::BrokerLinearize { record },
        ),
    ensures physical_slot_agreement(p0_layer::apply(
        cfg, state, p0_layer::Event::BrokerLinearize { record },
    )),
{
    config_layer::erasure_is_replay_well_formed(cfg);
    match record {
        replay_layer::JournalRecord::Start { request, attempt, .. } => {
            let erased = config_layer::erase_config(cfg);
            let history = state.physical.physical;
            assert(replay_layer::structural_enabled(
                erased, state.core.evidence.records, record,
            ));
            assert(attempt == replay_layer::started_count(
                state.core.evidence.records, request,
            ) + 1);
            replay_layer::replay_start_exact(
                erased, state.core.evidence.records,
            );
            assert(replay_layer::start_count(
                state.core.evidence.records, request, attempt,
            ) == 0);
            no_invoke_without_start(
                cfg,
                state.core.evidence.records,
                state.core.evidence.ack_cuts,
                history,
                request,
                attempt,
            );
            no_delivery_without_invoke(history, request, attempt);
            assert(state.core.broker.slot == record_layer::ExecSlot::Idle);
            assert(state.physical.slot_source.is_none());
        },
        replay_layer::JournalRecord::Authorize { .. }
        | replay_layer::JournalRecord::Revoke { .. }
        | replay_layer::JournalRecord::Prepare { .. }
        | replay_layer::JournalRecord::Arm { .. }
        | replay_layer::JournalRecord::Outcome { .. }
        | replay_layer::JournalRecord::CommitRec { .. }
        | replay_layer::JournalRecord::FailRec { .. }
        | replay_layer::JournalRecord::UnknownRec { .. } => {},
    }
}

pub proof fn equal_physical_slot_view_preserves_agreement(
    before: p0_layer::State,
    after: p0_layer::State,
)
    requires
        physical_slot_agreement(before),
        after.core.broker.slot == before.core.broker.slot,
        after.physical.physical == before.physical.physical,
        after.physical.slot_source == before.physical.slot_source,
    ensures physical_slot_agreement(after),
{
    match before.core.broker.slot {
        record_layer::ExecSlot::Idle
        | record_layer::ExecSlot::Ready { .. }
        | record_layer::ExecSlot::InFlight { .. }
        | record_layer::ExecSlot::Received { .. }
        | record_layer::ExecSlot::ObservedSuccess { .. }
        | record_layer::ExecSlot::ObservedFailure { .. }
        | record_layer::ExecSlot::ObservedUnknown { .. } => {},
    }
}

pub proof fn admin_linearize_preserves_physical_slot(
    cfg: config_layer::FullConfig,
    state: p0_layer::State,
    record: replay_layer::JournalRecord,
)
    requires
        p1_invariant(cfg, state),
        record is Authorize || record is Revoke || record is Prepare || record is Arm,
        p0_layer::admissibly_enabled(
            cfg, state, p0_layer::Event::BrokerLinearize { record },
        ),
    ensures physical_slot_agreement(p0_layer::apply(
        cfg, state, p0_layer::Event::BrokerLinearize { record },
    )),
{
    match record {
        replay_layer::JournalRecord::Authorize { .. }
        | replay_layer::JournalRecord::Revoke { .. }
        | replay_layer::JournalRecord::Prepare { .. }
        | replay_layer::JournalRecord::Arm { .. } => {
            let after = p0_layer::apply(
                cfg, state, p0_layer::Event::BrokerLinearize { record },
            );
            match state.core.broker.slot {
                record_layer::ExecSlot::Idle
                | record_layer::ExecSlot::Ready { .. }
                | record_layer::ExecSlot::InFlight { .. }
                | record_layer::ExecSlot::Received { .. }
                | record_layer::ExecSlot::ObservedSuccess { .. }
                | record_layer::ExecSlot::ObservedFailure { .. }
                | record_layer::ExecSlot::ObservedUnknown { .. } => {},
            }
            assert(after.core.broker.slot == state.core.broker.slot);
            assert(after.physical.physical == state.physical.physical);
            assert(after.physical.slot_source == state.physical.slot_source);
            equal_physical_slot_view_preserves_agreement(state, after);
        },
        replay_layer::JournalRecord::Start { .. }
        | replay_layer::JournalRecord::Outcome { .. }
        | replay_layer::JournalRecord::CommitRec { .. }
        | replay_layer::JournalRecord::FailRec { .. }
        | replay_layer::JournalRecord::UnknownRec { .. } => {},
    }
}

pub proof fn success_outcome_preserves_physical_slot(
    cfg: config_layer::FullConfig,
    state: p0_layer::State,
    record: replay_layer::JournalRecord,
)
    requires
        p1_invariant(cfg, state),
        match record {
            replay_layer::JournalRecord::Outcome {
                observation: replay_layer::Observation::Success(_), ..
            } => true,
            _ => false,
        },
        p0_layer::admissibly_enabled(
            cfg, state, p0_layer::Event::BrokerLinearize { record },
        ),
    ensures physical_slot_agreement(p0_layer::apply(
        cfg, state, p0_layer::Event::BrokerLinearize { record },
    )),
{
    match record {
        replay_layer::JournalRecord::Outcome {
            request, attempt, observation, ..
        } => {
            match observation {
                replay_layer::Observation::Success(value) => {
                    assert(state.core.broker.slot
                        == (record_layer::ExecSlot::Received {
                            request, attempt, observation,
                        }));
                    assert(source_is_delivery(
                        state.physical.physical,
                        state.physical.slot_source,
                        request,
                        attempt,
                        observation,
                    ));
                    assert(p0_layer::apply(
                        cfg, state,
                        p0_layer::Event::BrokerLinearize { record },
                    ).core.broker.slot
                        == (record_layer::ExecSlot::ObservedSuccess {
                            request, attempt, value,
                        }));
                    assert(p0_layer::apply(
                        cfg, state,
                        p0_layer::Event::BrokerLinearize { record },
                    ).physical.slot_source == state.physical.slot_source);
                },
                replay_layer::Observation::Failure
                | replay_layer::Observation::Ambiguous
                | replay_layer::Observation::InvalidResult(_) => {},
            }
        },
        replay_layer::JournalRecord::Authorize { .. }
        | replay_layer::JournalRecord::Revoke { .. }
        | replay_layer::JournalRecord::Prepare { .. }
        | replay_layer::JournalRecord::Arm { .. }
        | replay_layer::JournalRecord::Start { .. }
        | replay_layer::JournalRecord::CommitRec { .. }
        | replay_layer::JournalRecord::FailRec { .. }
        | replay_layer::JournalRecord::UnknownRec { .. } => {},
    }
}

pub proof fn failure_outcome_preserves_physical_slot(
    cfg: config_layer::FullConfig,
    state: p0_layer::State,
    record: replay_layer::JournalRecord,
)
    requires
        p1_invariant(cfg, state),
        match record {
            replay_layer::JournalRecord::Outcome {
                observation: replay_layer::Observation::Failure, ..
            } => true,
            _ => false,
        },
        p0_layer::admissibly_enabled(
            cfg, state, p0_layer::Event::BrokerLinearize { record },
        ),
    ensures physical_slot_agreement(p0_layer::apply(
        cfg, state, p0_layer::Event::BrokerLinearize { record },
    )),
{
    match record {
        replay_layer::JournalRecord::Outcome {
            request, attempt, observation, ..
        } => match observation {
            replay_layer::Observation::Failure => {
                    assert(state.core.broker.slot
                        == (record_layer::ExecSlot::Received {
                            request, attempt, observation,
                        }));
                    assert(source_is_delivery(
                        state.physical.physical,
                        state.physical.slot_source,
                        request,
                        attempt,
                        observation,
                    ));
                    assert(p0_layer::apply(
                        cfg, state,
                        p0_layer::Event::BrokerLinearize { record },
                    ).core.broker.slot
                        == (record_layer::ExecSlot::ObservedFailure {
                            request, attempt,
                        }));
                    assert(p0_layer::apply(
                        cfg, state,
                        p0_layer::Event::BrokerLinearize { record },
                    ).physical.slot_source == state.physical.slot_source);
                },
            replay_layer::Observation::Success(_)
            | replay_layer::Observation::Ambiguous
            | replay_layer::Observation::InvalidResult(_) => {},
        },
        replay_layer::JournalRecord::Authorize { .. }
        | replay_layer::JournalRecord::Revoke { .. }
        | replay_layer::JournalRecord::Prepare { .. }
        | replay_layer::JournalRecord::Arm { .. }
        | replay_layer::JournalRecord::Start { .. }
        | replay_layer::JournalRecord::CommitRec { .. }
        | replay_layer::JournalRecord::FailRec { .. }
        | replay_layer::JournalRecord::UnknownRec { .. } => {},
    }
}

pub proof fn ambiguous_outcome_preserves_physical_slot(
    cfg: config_layer::FullConfig,
    state: p0_layer::State,
    record: replay_layer::JournalRecord,
)
    requires
        p1_invariant(cfg, state),
        match record {
            replay_layer::JournalRecord::Outcome {
                observation: replay_layer::Observation::Ambiguous, ..
            } => true,
            _ => false,
        },
        p0_layer::admissibly_enabled(
            cfg, state, p0_layer::Event::BrokerLinearize { record },
        ),
    ensures physical_slot_agreement(p0_layer::apply(
        cfg, state, p0_layer::Event::BrokerLinearize { record },
    )),
{
    match record {
        replay_layer::JournalRecord::Outcome {
            request, attempt, observation, ..
        } => match observation {
            replay_layer::Observation::Ambiguous => {
                    assert(state.core.broker.slot
                        == (record_layer::ExecSlot::Received {
                            request, attempt, observation,
                        }));
                    assert(source_is_delivery(
                        state.physical.physical,
                        state.physical.slot_source,
                        request,
                        attempt,
                        observation,
                    ));
                    if config_layer::erase_config(cfg).request_class[request]
                        == replay_layer::RetryClass::Uncontrolled
                    {
                        assert(p0_layer::apply(
                            cfg, state,
                            p0_layer::Event::BrokerLinearize { record },
                        ).core.broker.slot
                            == (record_layer::ExecSlot::ObservedUnknown {
                                request,
                                attempt,
                                reason: replay_layer::UnknownReason::AmbiguousOutcome,
                            }));
                        assert(p0_layer::apply(
                            cfg, state,
                            p0_layer::Event::BrokerLinearize { record },
                        ).physical.slot_source == state.physical.slot_source);
                    } else {
                        assert(p0_layer::apply(
                            cfg, state,
                            p0_layer::Event::BrokerLinearize { record },
                        ).core.broker.slot == record_layer::ExecSlot::Idle);
                        assert(p0_layer::apply(
                            cfg, state,
                            p0_layer::Event::BrokerLinearize { record },
                        ).physical.slot_source.is_none());
                    }
                },
            replay_layer::Observation::Success(_)
            | replay_layer::Observation::Failure
            | replay_layer::Observation::InvalidResult(_) => {},
        },
        replay_layer::JournalRecord::Authorize { .. }
        | replay_layer::JournalRecord::Revoke { .. }
        | replay_layer::JournalRecord::Prepare { .. }
        | replay_layer::JournalRecord::Arm { .. }
        | replay_layer::JournalRecord::Start { .. }
        | replay_layer::JournalRecord::CommitRec { .. }
        | replay_layer::JournalRecord::FailRec { .. }
        | replay_layer::JournalRecord::UnknownRec { .. } => {},
    }
}

pub proof fn uncontrolled_invalid_outcome_preserves_physical_slot(
    cfg: config_layer::FullConfig,
    state: p0_layer::State,
    record: replay_layer::JournalRecord,
)
    requires
        p1_invariant(cfg, state),
        match record {
            replay_layer::JournalRecord::Outcome {
                request,
                observation: replay_layer::Observation::InvalidResult(_), ..
            } => config_layer::erase_config(cfg).request_class[request]
                == replay_layer::RetryClass::Uncontrolled,
            _ => false,
        },
        p0_layer::admissibly_enabled(
            cfg, state, p0_layer::Event::BrokerLinearize { record },
        ),
    ensures physical_slot_agreement(p0_layer::apply(
        cfg, state, p0_layer::Event::BrokerLinearize { record },
    )),
{
    match record {
        replay_layer::JournalRecord::Outcome {
            request, attempt, observation, ..
        } => match observation {
            replay_layer::Observation::InvalidResult(bad) => {
                    assert(state.core.broker.slot
                        == (record_layer::ExecSlot::Received {
                            request, attempt, observation,
                        }));
                    assert(source_is_delivery(
                        state.physical.physical,
                        state.physical.slot_source,
                        request,
                        attempt,
                        observation,
                    ));
                    assert(config_layer::erase_config(cfg).request_class[request]
                        == replay_layer::RetryClass::Uncontrolled);
                    assert(p0_layer::apply(
                        cfg, state,
                        p0_layer::Event::BrokerLinearize { record },
                    ).core.broker.slot
                        == (record_layer::ExecSlot::ObservedUnknown {
                            request,
                            attempt,
                            reason: replay_layer::UnknownReason::InvalidResultReason,
                        }));
                    assert(p0_layer::apply(
                        cfg, state,
                        p0_layer::Event::BrokerLinearize { record },
                    ).physical.slot_source == state.physical.slot_source);
                    assert(p0_layer::apply(
                        cfg, state,
                        p0_layer::Event::BrokerLinearize { record },
                    ).physical.physical == state.physical.physical);
                    invalid_delivery_has_witness(
                        state.physical.physical,
                        state.physical.slot_source,
                        request,
                        attempt,
                        bad,
                    );
                    assert(exists|witness: replay_layer::InvalidValue| #![auto]
                        source_is_delivery(
                            p0_layer::apply(
                                cfg, state,
                                p0_layer::Event::BrokerLinearize { record },
                            ).physical.physical,
                            p0_layer::apply(
                                cfg, state,
                                p0_layer::Event::BrokerLinearize { record },
                            ).physical.slot_source,
                            request,
                            attempt,
                            replay_layer::Observation::InvalidResult(witness),
                        ));
                    observed_invalid_source_is_slot_agreement(
                        p0_layer::apply(
                            cfg, state,
                            p0_layer::Event::BrokerLinearize { record },
                        ),
                        request,
                        attempt,
                    );
                },
            replay_layer::Observation::Success(_)
            | replay_layer::Observation::Failure
            | replay_layer::Observation::Ambiguous => {},
        },
        replay_layer::JournalRecord::Authorize { .. }
        | replay_layer::JournalRecord::Revoke { .. }
        | replay_layer::JournalRecord::Prepare { .. }
        | replay_layer::JournalRecord::Arm { .. }
        | replay_layer::JournalRecord::Start { .. }
        | replay_layer::JournalRecord::CommitRec { .. }
        | replay_layer::JournalRecord::FailRec { .. }
        | replay_layer::JournalRecord::UnknownRec { .. } => {},
    }
}

pub proof fn retry_safe_invalid_outcome_preserves_physical_slot(
    cfg: config_layer::FullConfig,
    state: p0_layer::State,
    record: replay_layer::JournalRecord,
)
    requires
        p1_invariant(cfg, state),
        match record {
            replay_layer::JournalRecord::Outcome {
                request,
                observation: replay_layer::Observation::InvalidResult(_), ..
            } => config_layer::erase_config(cfg).request_class[request]
                != replay_layer::RetryClass::Uncontrolled,
            _ => false,
        },
        p0_layer::admissibly_enabled(
            cfg, state, p0_layer::Event::BrokerLinearize { record },
        ),
    ensures physical_slot_agreement(p0_layer::apply(
        cfg, state, p0_layer::Event::BrokerLinearize { record },
    )),
{
    match record {
        replay_layer::JournalRecord::Outcome {
            request, attempt, observation, ..
        } => match observation {
            replay_layer::Observation::InvalidResult(_) => {
                assert(state.core.broker.slot
                    == (record_layer::ExecSlot::Received {
                        request, attempt, observation,
                    }));
                assert(p0_layer::apply(
                    cfg, state,
                    p0_layer::Event::BrokerLinearize { record },
                ).core.broker.slot == record_layer::ExecSlot::Idle);
                assert(p0_layer::apply(
                    cfg, state,
                    p0_layer::Event::BrokerLinearize { record },
                ).physical.slot_source.is_none());
            },
            replay_layer::Observation::Success(_)
            | replay_layer::Observation::Failure
            | replay_layer::Observation::Ambiguous => {},
        },
        replay_layer::JournalRecord::Authorize { .. }
        | replay_layer::JournalRecord::Revoke { .. }
        | replay_layer::JournalRecord::Prepare { .. }
        | replay_layer::JournalRecord::Arm { .. }
        | replay_layer::JournalRecord::Start { .. }
        | replay_layer::JournalRecord::CommitRec { .. }
        | replay_layer::JournalRecord::FailRec { .. }
        | replay_layer::JournalRecord::UnknownRec { .. } => {},
    }
}

pub proof fn invalid_outcome_preserves_physical_slot(
    cfg: config_layer::FullConfig,
    state: p0_layer::State,
    record: replay_layer::JournalRecord,
)
    requires
        p1_invariant(cfg, state),
        match record {
            replay_layer::JournalRecord::Outcome {
                observation: replay_layer::Observation::InvalidResult(_), ..
            } => true,
            _ => false,
        },
        p0_layer::admissibly_enabled(
            cfg, state, p0_layer::Event::BrokerLinearize { record },
        ),
    ensures physical_slot_agreement(p0_layer::apply(
        cfg, state, p0_layer::Event::BrokerLinearize { record },
    )),
{
    match record {
        replay_layer::JournalRecord::Outcome {
            request,
            observation: replay_layer::Observation::InvalidResult(_), ..
        } => {
            if config_layer::erase_config(cfg).request_class[request]
                == replay_layer::RetryClass::Uncontrolled
            {
                uncontrolled_invalid_outcome_preserves_physical_slot(
                    cfg, state, record,
                );
            } else {
                retry_safe_invalid_outcome_preserves_physical_slot(
                    cfg, state, record,
                );
            }
        },
        replay_layer::JournalRecord::Authorize { .. }
        | replay_layer::JournalRecord::Revoke { .. }
        | replay_layer::JournalRecord::Prepare { .. }
        | replay_layer::JournalRecord::Arm { .. }
        | replay_layer::JournalRecord::Start { .. }
        | replay_layer::JournalRecord::Outcome {
            observation: replay_layer::Observation::Success(_), ..
        }
        | replay_layer::JournalRecord::Outcome {
            observation: replay_layer::Observation::Failure, ..
        }
        | replay_layer::JournalRecord::Outcome {
            observation: replay_layer::Observation::Ambiguous, ..
        }
        | replay_layer::JournalRecord::CommitRec { .. }
        | replay_layer::JournalRecord::FailRec { .. }
        | replay_layer::JournalRecord::UnknownRec { .. } => {},
    }
}

pub proof fn outcome_linearize_preserves_physical_slot(
    cfg: config_layer::FullConfig,
    state: p0_layer::State,
    record: replay_layer::JournalRecord,
)
    requires
        p1_invariant(cfg, state),
        record is Outcome,
        p0_layer::admissibly_enabled(
            cfg, state, p0_layer::Event::BrokerLinearize { record },
        ),
    ensures physical_slot_agreement(p0_layer::apply(
        cfg, state, p0_layer::Event::BrokerLinearize { record },
    )),
{
    match record {
        replay_layer::JournalRecord::Outcome { observation, .. } => {
            match observation {
                replay_layer::Observation::Success(_) => {
                    success_outcome_preserves_physical_slot(cfg, state, record);
                },
                replay_layer::Observation::Failure => {
                    failure_outcome_preserves_physical_slot(cfg, state, record);
                },
                replay_layer::Observation::Ambiguous => {
                    ambiguous_outcome_preserves_physical_slot(cfg, state, record);
                },
                replay_layer::Observation::InvalidResult(_) => {
                    invalid_outcome_preserves_physical_slot(cfg, state, record);
                },
            }
        },
        replay_layer::JournalRecord::Authorize { .. }
        | replay_layer::JournalRecord::Revoke { .. }
        | replay_layer::JournalRecord::Prepare { .. }
        | replay_layer::JournalRecord::Arm { .. }
        | replay_layer::JournalRecord::Start { .. }
        | replay_layer::JournalRecord::CommitRec { .. }
        | replay_layer::JournalRecord::FailRec { .. }
        | replay_layer::JournalRecord::UnknownRec { .. } => {},
    }
}

pub proof fn terminal_linearize_preserves_physical_slot(
    cfg: config_layer::FullConfig,
    state: p0_layer::State,
    record: replay_layer::JournalRecord,
)
    requires
        p1_invariant(cfg, state),
        record is CommitRec || record is FailRec || record is UnknownRec,
        p0_layer::admissibly_enabled(
            cfg, state, p0_layer::Event::BrokerLinearize { record },
        ),
    ensures physical_slot_agreement(p0_layer::apply(
        cfg, state, p0_layer::Event::BrokerLinearize { record },
    )),
{
    match record {
        replay_layer::JournalRecord::CommitRec { .. }
        | replay_layer::JournalRecord::FailRec { .. }
        | replay_layer::JournalRecord::UnknownRec { .. } => {},
        replay_layer::JournalRecord::Authorize { .. }
        | replay_layer::JournalRecord::Revoke { .. }
        | replay_layer::JournalRecord::Prepare { .. }
        | replay_layer::JournalRecord::Arm { .. }
        | replay_layer::JournalRecord::Start { .. }
        | replay_layer::JournalRecord::Outcome { .. } => {},
    }
}

pub proof fn linearize_preserves_physical_slot(
    cfg: config_layer::FullConfig,
    state: p0_layer::State,
    record: replay_layer::JournalRecord,
)
    requires
        config_layer::full_config_wf(cfg),
        p1_invariant(cfg, state),
        p0_layer::admissibly_enabled(
            cfg, state, p0_layer::Event::BrokerLinearize { record },
        ),
    ensures physical_slot_agreement(p0_layer::apply(
        cfg, state, p0_layer::Event::BrokerLinearize { record },
    )),
{
    match record {
        replay_layer::JournalRecord::Start { .. } => {
            start_linearize_preserves_physical_slot(cfg, state, record);
        },
        replay_layer::JournalRecord::Outcome { .. } => {
            outcome_linearize_preserves_physical_slot(cfg, state, record);
        },
        replay_layer::JournalRecord::CommitRec { .. }
        | replay_layer::JournalRecord::FailRec { .. }
        | replay_layer::JournalRecord::UnknownRec { .. } => {
            terminal_linearize_preserves_physical_slot(cfg, state, record);
        },
        replay_layer::JournalRecord::Authorize { .. }
        | replay_layer::JournalRecord::Revoke { .. }
        | replay_layer::JournalRecord::Prepare { .. }
        | replay_layer::JournalRecord::Arm { .. } => {
            admin_linearize_preserves_physical_slot(cfg, state, record);
        },
    }
}

pub proof fn stuttering_control_preserves_physical_slot(
    cfg: config_layer::FullConfig,
    state: p0_layer::State,
    event: p0_layer::Event,
)
    requires
        p1_invariant(cfg, state),
        p0_layer::admissibly_enabled(cfg, state, event),
        event is JournalAppendCall
            || event is JournalAppendReturn
            || event is JournalDiskFull
            || event is IgnoreStale
            || event is BeginRecover
            || event is FinishRecover,
    ensures physical_slot_agreement(p0_layer::apply(cfg, state, event)),
{
    let after = p0_layer::apply(cfg, state, event);
    match event {
        p0_layer::Event::JournalAppendCall { .. }
        | p0_layer::Event::JournalAppendReturn { .. }
        | p0_layer::Event::JournalDiskFull { .. }
        | p0_layer::Event::IgnoreStale { .. }
        | p0_layer::Event::BeginRecover
        | p0_layer::Event::FinishRecover => {
            assert(after.core.broker.slot == state.core.broker.slot);
            assert(after.physical.physical == state.physical.physical);
            assert(after.physical.slot_source == state.physical.slot_source);
            equal_physical_slot_view_preserves_agreement(state, after);
        },
        p0_layer::Event::BrokerLinearize { .. }
        | p0_layer::Event::InvokeEvent { .. }
        | p0_layer::Event::DeliverEvent { .. }
        | p0_layer::Event::RetryRelease { .. }
        | p0_layer::Event::Crash => {},
    }
}

pub proof fn retry_release_clears_physical_slot(
    cfg: config_layer::FullConfig,
    state: p0_layer::State,
    request: replay_layer::RequestId,
)
    ensures physical_slot_agreement(p0_layer::apply(
        cfg, state, p0_layer::Event::RetryRelease { request },
    )),
{
}

pub proof fn crash_clears_physical_slot(
    cfg: config_layer::FullConfig,
    state: p0_layer::State,
)
    ensures physical_slot_agreement(p0_layer::apply(
        cfg, state, p0_layer::Event::Crash,
    )),
{
}

pub proof fn clearing_control_preserves_physical_slot(
    cfg: config_layer::FullConfig,
    state: p0_layer::State,
    event: p0_layer::Event,
)
    requires
        p1_invariant(cfg, state),
        p0_layer::admissibly_enabled(cfg, state, event),
        event is RetryRelease || event is Crash,
    ensures physical_slot_agreement(p0_layer::apply(cfg, state, event)),
{
    match event {
        p0_layer::Event::RetryRelease { request } => {
            retry_release_clears_physical_slot(cfg, state, request);
        },
        p0_layer::Event::Crash => {
            crash_clears_physical_slot(cfg, state);
        },
        p0_layer::Event::JournalAppendCall { .. }
        | p0_layer::Event::BrokerLinearize { .. }
        | p0_layer::Event::JournalAppendReturn { .. }
        | p0_layer::Event::JournalDiskFull { .. }
        | p0_layer::Event::InvokeEvent { .. }
        | p0_layer::Event::DeliverEvent { .. }
        | p0_layer::Event::IgnoreStale { .. }
        | p0_layer::Event::BeginRecover
        | p0_layer::Event::FinishRecover => {},
    }
}

pub proof fn record_event_preserves_physical_slot(
    cfg: config_layer::FullConfig,
    state: p0_layer::State,
    event: p0_layer::Event,
)
    requires
        config_layer::full_config_wf(cfg),
        p1_invariant(cfg, state),
        p0_layer::admissibly_enabled(cfg, state, event),
        !(event is InvokeEvent),
        !(event is DeliverEvent),
    ensures physical_slot_agreement(p0_layer::apply(cfg, state, event)),
{
    match event {
        p0_layer::Event::BrokerLinearize { record } => {
            linearize_preserves_physical_slot(cfg, state, record);
        },
        p0_layer::Event::RetryRelease { .. }
        | p0_layer::Event::Crash => {
            clearing_control_preserves_physical_slot(cfg, state, event);
        },
        p0_layer::Event::JournalAppendCall { .. }
        | p0_layer::Event::JournalAppendReturn { .. }
        | p0_layer::Event::JournalDiskFull { .. }
        | p0_layer::Event::IgnoreStale { .. }
        | p0_layer::Event::BeginRecover
        | p0_layer::Event::FinishRecover => {
            stuttering_control_preserves_physical_slot(cfg, state, event);
        },
        p0_layer::Event::InvokeEvent { .. }
        | p0_layer::Event::DeliverEvent { .. } => {},
    }
}

pub proof fn step_preserves_p1_invariant(
    cfg: config_layer::FullConfig,
    state: p0_layer::State,
    event: p0_layer::Event,
)
    requires
        config_layer::full_config_wf(cfg),
        p1_invariant(cfg, state),
        p0_layer::admissibly_enabled(cfg, state, event),
    ensures p1_invariant(cfg, p0_layer::apply(cfg, state, event)),
{
    p0_layer::step_preserves_p0_invariant(cfg, state, event);
    match event {
        p0_layer::Event::InvokeEvent { .. } => {
            invoke_preserves_physical_facts(cfg, state, event);
        },
        p0_layer::Event::DeliverEvent { .. } => {
            deliver_preserves_physical_facts(cfg, state, event);
        },
        p0_layer::Event::JournalAppendCall { .. }
        | p0_layer::Event::BrokerLinearize { .. }
        | p0_layer::Event::JournalAppendReturn { .. }
        | p0_layer::Event::JournalDiskFull { .. }
        | p0_layer::Event::IgnoreStale { .. }
        | p0_layer::Event::RetryRelease { .. }
        | p0_layer::Event::Crash
        | p0_layer::Event::BeginRecover
        | p0_layer::Event::FinishRecover => {
            record_event_preserves_physical_history(cfg, state, event);
            record_event_preserves_physical_slot(cfg, state, event);
        },
    }
}

pub proof fn invoke_index_sound(
    history: Seq<p0_layer::PhysicalEvent>,
    request: replay_layer::RequestId,
    attempt: replay_layer::AttemptId,
)
    ensures match invoke_index(history, request, attempt) {
        Option::None => invoke_count(history, request, attempt) == 0,
        Option::Some(index) => index < history.len()
            && is_invoke_for(history[index as int], request, attempt),
    },
    decreases history.len(),
{
    if history.len() > 0 {
        let prefix = history.drop_last();
        if is_invoke_for(history.last(), request, attempt) {
            assert(history[(history.len() - 1) as int] == history.last());
        } else {
            invoke_index_sound(prefix, request, attempt);
        }
    }
}

pub proof fn delivery_index_sound(
    history: Seq<p0_layer::PhysicalEvent>,
    request: replay_layer::RequestId,
    attempt: replay_layer::AttemptId,
)
    ensures match delivery_index(history, request, attempt) {
        Option::None => delivery_count(history, request, attempt) == 0,
        Option::Some(index) => index < history.len()
            && is_delivery_for(history[index as int], request, attempt),
    },
    decreases history.len(),
{
    if history.len() > 0 {
        let prefix = history.drop_last();
        if is_delivery_for(history.last(), request, attempt) {
            assert(history[(history.len() - 1) as int] == history.last());
        } else {
            delivery_index_sound(prefix, request, attempt);
        }
    }
}

pub open spec fn ack_nonretroactive(events: Seq<p0_layer::Event>) -> bool
    decreases events.len()
{
    events.len() == 0 || {
        let prefix = events.drop_last();
        ack_nonretroactive(prefix)
            && match events.last() {
                p0_layer::Event::InvokeEvent { ack_cut, .. } => {
                    nat_occurs(p0_layer::pi_ack(prefix), ack_cut)
                },
                p0_layer::Event::JournalAppendCall { .. }
                | p0_layer::Event::BrokerLinearize { .. }
                | p0_layer::Event::JournalAppendReturn { .. }
                | p0_layer::Event::JournalDiskFull { .. }
                | p0_layer::Event::DeliverEvent { .. }
                | p0_layer::Event::IgnoreStale { .. }
                | p0_layer::Event::RetryRelease { .. }
                | p0_layer::Event::Crash
                | p0_layer::Event::BeginRecover
                | p0_layer::Event::FinishRecover => true,
            }
    }
}

pub proof fn ack_nonretroactive_push(
    cfg: config_layer::FullConfig,
    state: p0_layer::State,
    events: Seq<p0_layer::Event>,
    event: p0_layer::Event,
)
    requires
        p0_layer::p0_invariant(cfg, state),
        p0_layer::p0_history_agreement(cfg, state, events),
        p0_layer::admissibly_enabled(cfg, state, event),
        ack_nonretroactive(events),
    ensures ack_nonretroactive(events.push(event)),
{
    assert(events.push(event).drop_last() =~= events);
    assert(events.push(event).last() == event);
    match event {
        p0_layer::Event::InvokeEvent { request, attempt, ack_cut, .. } => {
            assert(ack_cut
                == state.core.evidence.acknowledged_prefix.len());
            match replay_layer::start_lsn(
                state.core.evidence.records, request, attempt,
            ) {
                Option::Some(start) => {
                    assert(1 <= start && start <= ack_cut);
                    assert(append_layer::b1_invariant(
                        record_layer::append_view(state.core),
                    ));
                    acknowledged_cut_occurs(state);
                    assert(state.core.evidence.ack_cuts == p0_layer::pi_ack(events));
                },
                Option::None => {},
            }
        },
        p0_layer::Event::JournalAppendCall { .. }
        | p0_layer::Event::BrokerLinearize { .. }
        | p0_layer::Event::JournalAppendReturn { .. }
        | p0_layer::Event::JournalDiskFull { .. }
        | p0_layer::Event::DeliverEvent { .. }
        | p0_layer::Event::IgnoreStale { .. }
        | p0_layer::Event::RetryRelease { .. }
        | p0_layer::Event::Crash
        | p0_layer::Event::BeginRecover
        | p0_layer::Event::FinishRecover => {},
    }
}

pub proof fn executable_run_p1_invariant(
    cfg: config_layer::FullConfig,
    events: Seq<p0_layer::Event>,
)
    requires
        config_layer::full_config_wf(cfg),
        p0_layer::admissibly_executable(cfg, events),
    ensures p1_invariant(cfg, p0_layer::run(cfg, events)),
    decreases events.len(),
{
    if events.len() == 0 {
        initial_p1_invariant(cfg);
    } else {
        let prefix = events.drop_last();
        executable_run_p1_invariant(cfg, prefix);
        step_preserves_p1_invariant(
            cfg, p0_layer::run(cfg, prefix), events.last(),
        );
    }
}

pub proof fn executable_ack_nonretroactive(
    cfg: config_layer::FullConfig,
    events: Seq<p0_layer::Event>,
)
    requires
        config_layer::full_config_wf(cfg),
        p0_layer::admissibly_executable(cfg, events),
    ensures ack_nonretroactive(events),
    decreases events.len(),
{
    if events.len() > 0 {
        let prefix = events.drop_last();
        assert(p0_layer::admissibly_executable(cfg, prefix));
        executable_ack_nonretroactive(cfg, prefix);
        p0_layer::executable_run_invariant(cfg, prefix);
        p0_layer::run_history_agreement(cfg, prefix);
        ack_nonretroactive_push(
            cfg,
            p0_layer::run(cfg, prefix),
            prefix,
            events.last(),
        );
        assert(prefix.push(events.last()) =~= events);
    }
}

pub open spec fn p1_checkpoint(
    cfg: config_layer::FullConfig,
    events: Seq<p0_layer::Event>,
) -> bool {
    let state = p0_layer::run(cfg, events);
    p1_invariant(cfg, state)
        && p0_layer::p0_history_agreement(cfg, state, events)
        && state.physical.physical == p0_layer::pi_physical(events)
        && ack_nonretroactive(events)
}

pub proof fn b2_p1_physical_causality_safety(
    cfg: config_layer::FullConfig,
    events: Seq<p0_layer::Event>,
)
    requires
        config_layer::full_config_wf(cfg),
        p0_layer::admissibly_executable(cfg, events),
    ensures
        p1_checkpoint(cfg, events),
        forall|length: nat| length <= events.len() ==>
            #[trigger] p1_checkpoint(
                cfg, events.take(length as int),
            ),
{
    executable_run_p1_invariant(cfg, events);
    executable_ack_nonretroactive(cfg, events);
    p0_layer::run_history_agreement(cfg, events);
    assert forall|length: nat| length <= events.len() implies
        #[trigger] p1_checkpoint(cfg, events.take(length as int)) by {
        p0_layer::executable_prefix(cfg, events, length);
        executable_run_p1_invariant(cfg, events.take(length as int));
        executable_ack_nonretroactive(cfg, events.take(length as int));
        p0_layer::run_history_agreement(cfg, events.take(length as int));
    }
}

pub proof fn initial_p1_invariant(cfg: config_layer::FullConfig)
    requires config_layer::full_config_wf(cfg),
    ensures p1_invariant(cfg, p0_layer::initial_state(cfg)),
{
    p0_layer::initial_p0_invariant(cfg);
}

} // verus!
