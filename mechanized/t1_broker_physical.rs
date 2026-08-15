use vstd::prelude::*;

#[path = "t1_full_config.rs"]
pub mod config_layer;

verus! {

use config_layer::broker_layer as record_layer;
use record_layer::query_layer::c1_layer::replay_layer;
use record_layer::query_layer::c1_layer::append_layer;

// B2-P0 is the physical-transition and trace-projection substrate.  It uses
// the rich configuration and the B2-R state without redeclaring either type.
// The stronger physical-causality, retry-count, and terminal-provenance
// invariants are deliberately not claimed by this checkpoint.

pub type PhysicalIndex = nat;

#[derive(PartialEq, Eq)]
pub enum PhysicalEvent {
    Invoke {
        request: replay_layer::RequestId,
        attempt: replay_layer::AttemptId,
        call: config_layer::CallDescriptor,
        journal_cut: nat,
        ack_cut: nat,
    },
    Delivered {
        request: replay_layer::RequestId,
        attempt: replay_layer::AttemptId,
        observation: replay_layer::Observation,
        journal_cut: nat,
    },
}

pub open spec fn delivery_source(
    history: Seq<PhysicalEvent>,
    request: replay_layer::RequestId,
    attempt: replay_layer::AttemptId,
    observation: replay_layer::Observation,
) -> Option<PhysicalIndex>
    decreases history.len()
{
    if history.len() == 0 {
        Option::None
    } else {
        match history.last() {
            PhysicalEvent::Delivered {
                request: r, attempt: a, observation: o, ..
            } if r == request && a == attempt && o == observation => {
                Option::Some((history.len() - 1) as nat)
            },
            PhysicalEvent::Invoke { .. }
            | PhysicalEvent::Delivered { .. } => {
                delivery_source(history.drop_last(), request, attempt, observation)
            },
        }
    }
}

pub struct PhysicalEvidence {
    pub physical: Seq<PhysicalEvent>,
    pub slot_source: Option<PhysicalIndex>,
    pub commit_source: IMap<replay_layer::RequestId, Option<PhysicalIndex>>,
}

pub struct State {
    pub core: record_layer::State,
    pub physical: PhysicalEvidence,
}

pub enum Event {
    JournalAppendCall { record: replay_layer::JournalRecord },
    BrokerLinearize { record: replay_layer::JournalRecord },
    JournalAppendReturn { cut: nat },
    JournalDiskFull { record: replay_layer::JournalRecord, cut: nat },
    InvokeEvent {
        request: replay_layer::RequestId,
        attempt: replay_layer::AttemptId,
        call: config_layer::CallDescriptor,
        journal_cut: nat,
        ack_cut: nat,
    },
    DeliverEvent {
        request: replay_layer::RequestId,
        attempt: replay_layer::AttemptId,
        observation: replay_layer::Observation,
        journal_cut: nat,
    },
    IgnoreStale {
        request: replay_layer::RequestId,
        attempt: replay_layer::AttemptId,
    },
    RetryRelease { request: replay_layer::RequestId },
    Crash,
    BeginRecover,
    FinishRecover,
}

pub open spec fn as_record_event(event: Event) -> Option<record_layer::Event> {
    match event {
        Event::JournalAppendCall { record } => Option::Some(
            record_layer::Event::JournalAppendCall { record },
        ),
        Event::BrokerLinearize { record } => Option::Some(
            record_layer::Event::BrokerLinearize { record },
        ),
        Event::JournalAppendReturn { cut } => Option::Some(
            record_layer::Event::JournalAppendReturn { cut },
        ),
        Event::JournalDiskFull { record, cut } => Option::Some(
            record_layer::Event::JournalDiskFull { record, cut },
        ),
        Event::IgnoreStale { request, attempt } => Option::Some(
            record_layer::Event::IgnoreStale { request, attempt },
        ),
        Event::RetryRelease { request } => Option::Some(
            record_layer::Event::RetryRelease { request },
        ),
        Event::Crash => Option::Some(record_layer::Event::Crash),
        Event::BeginRecover => Option::Some(record_layer::Event::BeginRecover),
        Event::FinishRecover => Option::Some(record_layer::Event::FinishRecover),
        Event::InvokeEvent { .. } | Event::DeliverEvent { .. } => Option::None,
    }
}

pub open spec fn event_physical(event: Event) -> Option<PhysicalEvent> {
    match event {
        Event::InvokeEvent {
            request, attempt, call, journal_cut, ack_cut,
        } => Option::Some(PhysicalEvent::Invoke {
            request, attempt, call, journal_cut, ack_cut,
        }),
        Event::DeliverEvent {
            request, attempt, observation, journal_cut,
        } => Option::Some(PhysicalEvent::Delivered {
            request, attempt, observation, journal_cut,
        }),
        Event::JournalAppendCall { .. }
        | Event::BrokerLinearize { .. }
        | Event::JournalAppendReturn { .. }
        | Event::JournalDiskFull { .. }
        | Event::IgnoreStale { .. }
        | Event::RetryRelease { .. }
        | Event::Crash
        | Event::BeginRecover
        | Event::FinishRecover => Option::None,
    }
}

pub open spec fn initial_state(cfg: config_layer::FullConfig) -> State {
    State {
        core: record_layer::initial_state(config_layer::erase_config(cfg)),
        physical: PhysicalEvidence {
            physical: Seq::empty(),
            slot_source: Option::None,
            commit_source: IMap::new(
                |_request: replay_layer::RequestId| true,
                |_request: replay_layer::RequestId| Option::None,
            ),
        },
    }
}

// Runtime control reads only immutable configuration and the Broker state.
pub open spec fn control_enabled(
    cfg: config_layer::FullConfig,
    state: State,
    event: Event,
) -> bool {
    match event {
        Event::InvokeEvent { request, attempt, call, .. } => {
            state.core.broker.mode == record_layer::Mode::Online
                && state.core.broker.append is Idle
                && state.core.broker.slot
                    == (record_layer::ExecSlot::Ready { request, attempt })
                && call == config_layer::canonical_call(cfg, request)
        },
        Event::DeliverEvent { request, attempt, .. } => {
            state.core.broker.mode == record_layer::Mode::Online
                && state.core.broker.append is Idle
                && state.core.broker.slot
                    == (record_layer::ExecSlot::InFlight { request, attempt })
        },
        Event::JournalAppendCall { .. }
        | Event::BrokerLinearize { .. }
        | Event::JournalAppendReturn { .. }
        | Event::JournalDiskFull { .. }
        | Event::IgnoreStale { .. }
        | Event::RetryRelease { .. }
        | Event::Crash
        | Event::BeginRecover
        | Event::FinishRecover => {
            match as_record_event(event) {
                Option::Some(record_event) => record_layer::control_enabled(
                    config_layer::erase_config(cfg), state.core, record_event,
                ),
                Option::None => false,
            }
        },
    }
}

// Cuts and exact Journal references are proof evidence, not runtime guards.
pub open spec fn evidence_admissible(
    cfg: config_layer::FullConfig,
    state: State,
    event: Event,
) -> bool {
    match event {
        Event::InvokeEvent {
            request, attempt, journal_cut, ack_cut, ..
        } => {
            journal_cut == state.core.evidence.records.len()
                && ack_cut == state.core.evidence.acknowledged_prefix.len()
                && match replay_layer::start_lsn(
                    state.core.evidence.records, request, attempt,
                ) {
                    Option::None => false,
                    Option::Some(start) => 1 <= start && start <= ack_cut,
                }
        },
        Event::DeliverEvent { journal_cut, .. } => {
            journal_cut == state.core.evidence.records.len()
        },
        Event::JournalAppendCall { .. }
        | Event::BrokerLinearize { .. }
        | Event::JournalAppendReturn { .. }
        | Event::JournalDiskFull { .. }
        | Event::IgnoreStale { .. }
        | Event::RetryRelease { .. }
        | Event::Crash
        | Event::BeginRecover
        | Event::FinishRecover => {
            match as_record_event(event) {
                Option::Some(record_event) => record_layer::evidence_admissible(
                    config_layer::erase_config(cfg), state.core, record_event,
                ),
                Option::None => false,
            }
        },
    }
}

pub open spec fn admissibly_enabled(
    cfg: config_layer::FullConfig,
    state: State,
    event: Event,
) -> bool {
    control_enabled(cfg, state, event) && evidence_admissible(cfg, state, event)
}

pub open spec fn slot_carries_source(slot: record_layer::ExecSlot) -> bool {
    match slot {
        record_layer::ExecSlot::Received { .. }
        | record_layer::ExecSlot::ObservedSuccess { .. }
        | record_layer::ExecSlot::ObservedFailure { .. }
        | record_layer::ExecSlot::ObservedUnknown { .. } => true,
        record_layer::ExecSlot::Idle
        | record_layer::ExecSlot::Ready { .. }
        | record_layer::ExecSlot::InFlight { .. } => false,
    }
}

pub open spec fn source_after_record(
    cfg: config_layer::FullConfig,
    state: State,
    event: record_layer::Event,
) -> Option<PhysicalIndex> {
    match event {
        record_layer::Event::Crash | record_layer::Event::RetryRelease { .. } => {
            Option::None
        },
        record_layer::Event::BrokerLinearize { record } => {
            let after = record_layer::apply(
                config_layer::erase_config(cfg), state.core, event,
            );
            if slot_carries_source(after.broker.slot) {
                state.physical.slot_source
            } else {
                Option::None
            }
        },
        record_layer::Event::JournalAppendCall { .. }
        | record_layer::Event::JournalAppendReturn { .. }
        | record_layer::Event::JournalDiskFull { .. }
        | record_layer::Event::IgnoreStale { .. }
        | record_layer::Event::BeginRecover
        | record_layer::Event::FinishRecover => state.physical.slot_source,
    }
}

pub open spec fn commit_source_after_record(
    state: State,
    event: record_layer::Event,
) -> IMap<replay_layer::RequestId, Option<PhysicalIndex>> {
    match event {
        record_layer::Event::BrokerLinearize {
            record: replay_layer::JournalRecord::CommitRec {
                request, attempt, value, ..
            },
        } => state.physical.commit_source.insert(
            request,
            delivery_source(
                state.physical.physical,
                request,
                attempt,
                replay_layer::Observation::Success(value),
            ),
        ),
        record_layer::Event::JournalAppendCall { .. }
        | record_layer::Event::BrokerLinearize { .. }
        | record_layer::Event::JournalAppendReturn { .. }
        | record_layer::Event::JournalDiskFull { .. }
        | record_layer::Event::IgnoreStale { .. }
        | record_layer::Event::RetryRelease { .. }
        | record_layer::Event::Crash
        | record_layer::Event::BeginRecover
        | record_layer::Event::FinishRecover => state.physical.commit_source,
    }
}

pub open spec fn apply(
    cfg: config_layer::FullConfig,
    state: State,
    event: Event,
) -> State {
    match event {
        Event::InvokeEvent {
            request, attempt, call, journal_cut, ack_cut,
        } => State {
            core: record_layer::State {
                broker: record_layer::BrokerState {
                    slot: record_layer::ExecSlot::InFlight { request, attempt },
                    ..state.core.broker
                },
                ..state.core
            },
            physical: PhysicalEvidence {
                physical: state.physical.physical.push(PhysicalEvent::Invoke {
                    request, attempt, call, journal_cut, ack_cut,
                }),
                slot_source: Option::None,
                ..state.physical
            },
        },
        Event::DeliverEvent {
            request, attempt, observation, journal_cut,
        } => State {
            core: record_layer::State {
                broker: record_layer::BrokerState {
                    slot: record_layer::ExecSlot::Received {
                        request, attempt, observation,
                    },
                    ..state.core.broker
                },
                ..state.core
            },
            physical: PhysicalEvidence {
                physical: state.physical.physical.push(PhysicalEvent::Delivered {
                    request, attempt, observation, journal_cut,
                }),
                slot_source: Option::Some(state.physical.physical.len()),
                ..state.physical
            },
        },
        Event::JournalAppendCall { .. }
        | Event::BrokerLinearize { .. }
        | Event::JournalAppendReturn { .. }
        | Event::JournalDiskFull { .. }
        | Event::IgnoreStale { .. }
        | Event::RetryRelease { .. }
        | Event::Crash
        | Event::BeginRecover
        | Event::FinishRecover => {
            match as_record_event(event) {
                Option::Some(record_event) => State {
                    core: record_layer::apply(
                        config_layer::erase_config(cfg), state.core, record_event,
                    ),
                    physical: PhysicalEvidence {
                        slot_source: source_after_record(cfg, state, record_event),
                        commit_source: commit_source_after_record(state, record_event),
                        ..state.physical
                    },
                },
                Option::None => state,
            }
        },
    }
}

pub open spec fn physical_step(
    cfg: config_layer::FullConfig,
    before: State,
    event: Event,
    after: State,
) -> bool {
    admissibly_enabled(cfg, before, event) && after == apply(cfg, before, event)
}

pub open spec fn pi_physical(events: Seq<Event>) -> Seq<PhysicalEvent>
    decreases events.len()
{
    if events.len() == 0 {
        Seq::empty()
    } else {
        let prefix = pi_physical(events.drop_last());
        match event_physical(events.last()) {
            Option::None => prefix,
            Option::Some(event) => prefix.push(event),
        }
    }
}

pub open spec fn pi_journal(events: Seq<Event>)
    -> Seq<replay_layer::JournalRecord>
    decreases events.len()
{
    if events.len() == 0 {
        Seq::empty()
    } else {
        let prefix = pi_journal(events.drop_last());
        match events.last() {
            Event::BrokerLinearize { record } => prefix.push(record),
            Event::JournalAppendCall { .. }
            | Event::JournalAppendReturn { .. }
            | Event::JournalDiskFull { .. }
            | Event::InvokeEvent { .. }
            | Event::DeliverEvent { .. }
            | Event::IgnoreStale { .. }
            | Event::RetryRelease { .. }
            | Event::Crash
            | Event::BeginRecover
            | Event::FinishRecover => prefix,
        }
    }
}

pub open spec fn pi_ack(events: Seq<Event>) -> Seq<nat>
    decreases events.len()
{
    if events.len() == 0 {
        Seq::empty()
    } else {
        let prefix = pi_ack(events.drop_last());
        match events.last() {
            Event::JournalAppendReturn { cut } => prefix.push(cut),
            Event::JournalAppendCall { .. }
            | Event::BrokerLinearize { .. }
            | Event::JournalDiskFull { .. }
            | Event::InvokeEvent { .. }
            | Event::DeliverEvent { .. }
            | Event::IgnoreStale { .. }
            | Event::RetryRelease { .. }
            | Event::Crash
            | Event::BeginRecover
            | Event::FinishRecover => prefix,
        }
    }
}

pub open spec fn run(
    cfg: config_layer::FullConfig,
    events: Seq<Event>,
) -> State
    decreases events.len()
{
    if events.len() == 0 {
        initial_state(cfg)
    } else {
        apply(cfg, run(cfg, events.drop_last()), events.last())
    }
}

pub open spec fn admissibly_executable(
    cfg: config_layer::FullConfig,
    events: Seq<Event>,
) -> bool
    decreases events.len()
{
    events.len() == 0 || {
        let prefix = events.drop_last();
        admissibly_executable(cfg, prefix)
            && admissibly_enabled(cfg, run(cfg, prefix), events.last())
    }
}

pub open spec fn p0_history_agreement(
    cfg: config_layer::FullConfig,
    state: State,
    events: Seq<Event>,
) -> bool {
    state.core.evidence.records == pi_journal(events)
        && state.core.evidence.ack_cuts == pi_ack(events)
        && state.core.evidence.acknowledged_prefix
            == append_layer::acknowledged_prefix_for(
                pi_journal(events), pi_ack(events),
            )
        && state.physical.physical == pi_physical(events)
        && state.core.broker.durable
            == replay_layer::replay(config_layer::erase_config(cfg), pi_journal(events))
}

pub open spec fn p0_invariant(
    cfg: config_layer::FullConfig,
    state: State,
) -> bool {
    record_layer::b2_record_invariant(config_layer::erase_config(cfg), state.core)
        && state.physical.commit_source.dom()
            == ISet::<replay_layer::RequestId>::full()
        && (state.core.broker.mode != record_layer::Mode::Online
            ==> state.physical.slot_source.is_none())
}

pub proof fn initial_p0_invariant(cfg: config_layer::FullConfig)
    requires config_layer::full_config_wf(cfg),
    ensures p0_invariant(cfg, initial_state(cfg)),
{
    config_layer::erasure_is_replay_well_formed(cfg);
    record_layer::initial_invariant(config_layer::erase_config(cfg));
    assert(initial_state(cfg).physical.commit_source.dom()
        == ISet::<replay_layer::RequestId>::full());
}

pub proof fn initial_history_agreement(cfg: config_layer::FullConfig)
    ensures p0_history_agreement(cfg, initial_state(cfg), Seq::empty()),
{
    let records = Seq::<replay_layer::JournalRecord>::empty();
    let cuts = Seq::<nat>::empty();
    assert(append_layer::last_or_zero(cuts) == 0);
    assert(records.take(0) =~= records);
    assert(append_layer::acknowledged_prefix_for(records, cuts) == records);
}

pub proof fn invoke_preserves_record_invariant(
    cfg: config_layer::FullConfig,
    state: State,
    event: Event,
)
    requires
        record_layer::b2_record_invariant(
            config_layer::erase_config(cfg), state.core,
        ),
        control_enabled(cfg, state, event),
        event is InvokeEvent,
    ensures
        record_layer::b2_record_invariant(
            config_layer::erase_config(cfg), apply(cfg, state, event).core,
        ),
{
    let erased = config_layer::erase_config(cfg);
    match event {
        Event::InvokeEvent { request, attempt, .. } => {
            assert(state.core.broker.mode == record_layer::Mode::Online);
            assert(state.core.broker.append is Idle);
            assert(state.core.broker.slot
                == (record_layer::ExecSlot::Ready { request, attempt }));
            assert(record_layer::durable_slot_agreement(
                erased,
                state.core.broker.durable,
                record_layer::ExecSlot::Ready { request, attempt },
            ));
            assert(record_layer::durable_slot_agreement(
                erased,
                state.core.broker.durable,
                record_layer::ExecSlot::InFlight { request, attempt },
            ));
            assert(record_layer::called_shape(erased, apply(cfg, state, event).core));
            assert(record_layer::linearized_shape(
                erased, apply(cfg, state, event).core,
            ));
            assert(record_layer::ready_release_agreement(
                apply(cfg, state, event).core,
            ));
        },
        Event::JournalAppendCall { .. }
        | Event::BrokerLinearize { .. }
        | Event::JournalAppendReturn { .. }
        | Event::JournalDiskFull { .. }
        | Event::DeliverEvent { .. }
        | Event::IgnoreStale { .. }
        | Event::RetryRelease { .. }
        | Event::Crash
        | Event::BeginRecover
        | Event::FinishRecover => {},
    }
}

pub proof fn deliver_preserves_record_invariant(
    cfg: config_layer::FullConfig,
    state: State,
    event: Event,
)
    requires
        record_layer::b2_record_invariant(
            config_layer::erase_config(cfg), state.core,
        ),
        control_enabled(cfg, state, event),
        event is DeliverEvent,
    ensures
        record_layer::b2_record_invariant(
            config_layer::erase_config(cfg), apply(cfg, state, event).core,
        ),
{
    let erased = config_layer::erase_config(cfg);
    match event {
        Event::DeliverEvent { request, attempt, observation, .. } => {
            assert(state.core.broker.mode == record_layer::Mode::Online);
            assert(state.core.broker.append is Idle);
            assert(state.core.broker.slot
                == (record_layer::ExecSlot::InFlight { request, attempt }));
            assert(record_layer::durable_slot_agreement(
                erased,
                state.core.broker.durable,
                record_layer::ExecSlot::InFlight { request, attempt },
            ));
            assert(record_layer::durable_slot_agreement(
                erased,
                state.core.broker.durable,
                record_layer::ExecSlot::Received {
                    request, attempt, observation,
                },
            ));
            assert(record_layer::called_shape(erased, apply(cfg, state, event).core));
            assert(record_layer::linearized_shape(
                erased, apply(cfg, state, event).core,
            ));
            assert(record_layer::ready_release_agreement(
                apply(cfg, state, event).core,
            ));
        },
        Event::JournalAppendCall { .. }
        | Event::BrokerLinearize { .. }
        | Event::JournalAppendReturn { .. }
        | Event::JournalDiskFull { .. }
        | Event::InvokeEvent { .. }
        | Event::IgnoreStale { .. }
        | Event::RetryRelease { .. }
        | Event::Crash
        | Event::BeginRecover
        | Event::FinishRecover => {},
    }
}

pub proof fn step_preserves_p0_invariant(
    cfg: config_layer::FullConfig,
    state: State,
    event: Event,
)
    requires
        config_layer::full_config_wf(cfg),
        p0_invariant(cfg, state),
        admissibly_enabled(cfg, state, event),
    ensures p0_invariant(cfg, apply(cfg, state, event)),
{
    config_layer::erasure_is_replay_well_formed(cfg);
    match event {
        Event::InvokeEvent { .. } => {
            invoke_preserves_record_invariant(cfg, state, event);
        },
        Event::DeliverEvent { .. } => {
            deliver_preserves_record_invariant(cfg, state, event);
        },
        Event::JournalAppendCall { .. }
        | Event::BrokerLinearize { .. }
        | Event::JournalAppendReturn { .. }
        | Event::JournalDiskFull { .. }
        | Event::IgnoreStale { .. }
        | Event::RetryRelease { .. }
        | Event::Crash
        | Event::BeginRecover
        | Event::FinishRecover => {
            match as_record_event(event) {
                Option::Some(record_event) => {
                    assert(record_layer::admissibly_enabled(
                        config_layer::erase_config(cfg), state.core, record_event,
                    ));
                    record_layer::step_preserves_invariant(
                        config_layer::erase_config(cfg), state.core, record_event,
                    );
                    match record_event {
                        record_layer::Event::JournalAppendCall { .. }
                        | record_layer::Event::BrokerLinearize { .. }
                        | record_layer::Event::JournalAppendReturn { .. }
                        | record_layer::Event::JournalDiskFull { .. }
                        | record_layer::Event::IgnoreStale { .. }
                        | record_layer::Event::RetryRelease { .. }
                        | record_layer::Event::Crash
                        | record_layer::Event::BeginRecover
                        | record_layer::Event::FinishRecover => {},
                    }
                },
                Option::None => {},
            }
        },
    }
}

pub proof fn pi_physical_push(events: Seq<Event>, event: Event)
    ensures
        pi_physical(events.push(event))
            == match event_physical(event) {
                Option::None => pi_physical(events),
                Option::Some(physical) => pi_physical(events).push(physical),
            },
{
    assert(events.push(event).drop_last() =~= events);
    assert(events.push(event).last() == event);
}

pub proof fn pi_journal_push(events: Seq<Event>, event: Event)
    ensures
        pi_journal(events.push(event))
            == match event {
                Event::BrokerLinearize { record } => pi_journal(events).push(record),
                Event::JournalAppendCall { .. }
                | Event::JournalAppendReturn { .. }
                | Event::JournalDiskFull { .. }
                | Event::InvokeEvent { .. }
                | Event::DeliverEvent { .. }
                | Event::IgnoreStale { .. }
                | Event::RetryRelease { .. }
                | Event::Crash
                | Event::BeginRecover
                | Event::FinishRecover => pi_journal(events),
            },
{
    assert(events.push(event).drop_last() =~= events);
    assert(events.push(event).last() == event);
}

pub proof fn pi_ack_push(events: Seq<Event>, event: Event)
    ensures
        pi_ack(events.push(event))
            == match event {
                Event::JournalAppendReturn { cut } => pi_ack(events).push(cut),
                Event::JournalAppendCall { .. }
                | Event::BrokerLinearize { .. }
                | Event::JournalDiskFull { .. }
                | Event::InvokeEvent { .. }
                | Event::DeliverEvent { .. }
                | Event::IgnoreStale { .. }
                | Event::RetryRelease { .. }
                | Event::Crash
                | Event::BeginRecover
                | Event::FinishRecover => pi_ack(events),
            },
{
    assert(events.push(event).drop_last() =~= events);
    assert(events.push(event).last() == event);
}

pub proof fn step_preserves_p0_history(
    cfg: config_layer::FullConfig,
    state: State,
    events: Seq<Event>,
    event: Event,
)
    requires
        p0_invariant(cfg, state),
        p0_history_agreement(cfg, state, events),
        admissibly_enabled(cfg, state, event),
    ensures
        p0_history_agreement(
            cfg, apply(cfg, state, event), events.push(event),
        ),
{
    pi_physical_push(events, event);
    pi_journal_push(events, event);
    pi_ack_push(events, event);
    match event {
        Event::BrokerLinearize { record } => {
            assert(append_layer::b1_invariant(
                record_layer::append_view(state.core),
            ));
            assert(append_layer::cuts_bounded(
                state.core.evidence.ack_cuts,
                state.core.evidence.records.len(),
            ));
            append_layer::acknowledged_prefix_survives_record_push(
                state.core.evidence.records,
                state.core.evidence.ack_cuts,
                record,
            );
            replay_layer::replay_push(
                config_layer::erase_config(cfg), pi_journal(events), record,
            );
        },
        Event::JournalAppendReturn { cut } => {
            assert(cut == state.core.evidence.records.len());
            assert(state.core.evidence.ack_cuts.push(cut).len() > 0);
            assert(state.core.evidence.ack_cuts.push(cut).last() == cut);
            assert(append_layer::last_or_zero(
                state.core.evidence.ack_cuts.push(cut),
            ) == cut);
            append_layer::take_full(state.core.evidence.records);
        },
        Event::JournalAppendCall { .. }
        | Event::JournalDiskFull { .. }
        | Event::InvokeEvent { .. }
        | Event::DeliverEvent { .. }
        | Event::IgnoreStale { .. }
        | Event::RetryRelease { .. }
        | Event::Crash
        | Event::BeginRecover
        | Event::FinishRecover => {},
    }
}

pub proof fn run_history_agreement(
    cfg: config_layer::FullConfig,
    events: Seq<Event>,
)
    requires
        config_layer::full_config_wf(cfg),
        admissibly_executable(cfg, events),
    ensures p0_history_agreement(cfg, run(cfg, events), events),
    decreases events.len(),
{
    if events.len() == 0 {
        initial_history_agreement(cfg);
    } else {
        let prefix = events.drop_last();
        let event = events.last();
        assert(admissibly_executable(cfg, prefix));
        run_history_agreement(cfg, prefix);
        executable_run_invariant(cfg, prefix);
        step_preserves_p0_history(
            cfg, run(cfg, prefix), prefix, event,
        );
        assert(prefix.push(event) =~= events);
    }
}

pub proof fn executable_run_invariant(
    cfg: config_layer::FullConfig,
    events: Seq<Event>,
)
    requires
        config_layer::full_config_wf(cfg),
        admissibly_executable(cfg, events),
    ensures p0_invariant(cfg, run(cfg, events)),
    decreases events.len(),
{
    if events.len() == 0 {
        initial_p0_invariant(cfg);
    } else {
        let prefix = events.drop_last();
        executable_run_invariant(cfg, prefix);
        step_preserves_p0_invariant(cfg, run(cfg, prefix), events.last());
    }
}

pub proof fn executable_prefix(
    cfg: config_layer::FullConfig,
    events: Seq<Event>,
    length: nat,
)
    requires
        admissibly_executable(cfg, events),
        length <= events.len(),
    ensures admissibly_executable(cfg, events.take(length as int)),
    decreases events.len() - length,
{
    if length == events.len() {
        assert(events.take(length as int) =~= events);
    } else {
        assert(length < events.len());
        assert(admissibly_executable(cfg, events.drop_last()));
        executable_prefix(cfg, events.drop_last(), length);
        assert(events.drop_last().take(length as int) =~= events.take(length as int));
    }
}

pub proof fn b2_p0_physical_trace_safety(
    cfg: config_layer::FullConfig,
    events: Seq<Event>,
)
    requires
        config_layer::full_config_wf(cfg),
        admissibly_executable(cfg, events),
    ensures
        p0_invariant(cfg, run(cfg, events)),
        p0_history_agreement(cfg, run(cfg, events), events),
        forall|length: nat| length <= events.len() ==>
            #[trigger] p0_invariant(
                cfg, run(cfg, events.take(length as int)),
            )
            && p0_history_agreement(
                cfg,
                run(cfg, events.take(length as int)),
                events.take(length as int),
            ),
{
    executable_run_invariant(cfg, events);
    run_history_agreement(cfg, events);
    assert forall|length: nat| length <= events.len() implies
        #[trigger] p0_invariant(
            cfg, run(cfg, events.take(length as int)),
        )
        && p0_history_agreement(
            cfg,
            run(cfg, events.take(length as int)),
            events.take(length as int),
        ) by {
        executable_prefix(cfg, events, length);
        executable_run_invariant(cfg, events.take(length as int));
        run_history_agreement(cfg, events.take(length as int));
    }
}

} // verus!
