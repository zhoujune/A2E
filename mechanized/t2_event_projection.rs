use vstd::prelude::*;

#[path = "t2_atomic_trace.rs"]
pub mod trace_layer;

verus! {

use trace_layer::runtime_layer;
use runtime_layer::t1_layer;
use t1_layer::execution_layer;
use execution_layer::projection_layer;
use projection_layer::global_layer;
use global_layer::bridge_layer;
use bridge_layer::contract_layer;
use contract_layer::p3_layer::p2_layer::p1_layer::p0_layer;
use p0_layer::config_layer;
use config_layer::broker_layer as record_layer;
use record_layer::query_layer::c1_layer::replay_layer;
use record_layer::query_layer::c1_layer::append_layer;

// T2-E is the event-level refinement between the independent atomic Journal
// and the Broker.  Atomic append linearization is the only renamed label.
// Every other accepted Journal label is carried to the identical global label.
pub open spec fn journal_to_broker_event(
    event: global_layer::GlobalEvent,
) -> global_layer::GlobalEvent {
    match event {
        global_layer::GlobalEvent::BrokerLinearize { record } => {
            global_layer::GlobalEvent::BrokerLinearize { record }
        },
        global_layer::GlobalEvent::JournalAppendCall { record } => {
            global_layer::GlobalEvent::JournalAppendCall { record }
        },
        global_layer::GlobalEvent::JournalAppendLinearize { record } => {
            global_layer::GlobalEvent::BrokerLinearize { record }
        },
        global_layer::GlobalEvent::JournalAppendReturn { cut } => {
            global_layer::GlobalEvent::JournalAppendReturn { cut }
        },
        global_layer::GlobalEvent::JournalDiskFull { record, cut } => {
            global_layer::GlobalEvent::JournalDiskFull { record, cut }
        },
        global_layer::GlobalEvent::WalStage { record } => {
            global_layer::GlobalEvent::WalStage { record }
        },
        global_layer::GlobalEvent::WalWriteFull { record } => {
            global_layer::GlobalEvent::WalWriteFull { record }
        },
        global_layer::GlobalEvent::WalWriteTorn { record } => {
            global_layer::GlobalEvent::WalWriteTorn { record }
        },
        global_layer::GlobalEvent::WalFinishTorn { record } => {
            global_layer::GlobalEvent::WalFinishTorn { record }
        },
        global_layer::GlobalEvent::WalFlushAck { cut } => {
            global_layer::GlobalEvent::WalFlushAck { cut }
        },
        global_layer::GlobalEvent::WalDiskFull { record, cut } => {
            global_layer::GlobalEvent::WalDiskFull { record, cut }
        },
        global_layer::GlobalEvent::InvokeEvent {
            request, attempt, call, journal_cut, ack_cut,
        } => global_layer::GlobalEvent::InvokeEvent {
            request, attempt, call, journal_cut, ack_cut,
        },
        global_layer::GlobalEvent::DeliverEvent {
            request, attempt, observation, journal_cut,
        } => global_layer::GlobalEvent::DeliverEvent {
            request, attempt, observation, journal_cut,
        },
        global_layer::GlobalEvent::IgnoreStale { request, attempt } => {
            global_layer::GlobalEvent::IgnoreStale { request, attempt }
        },
        global_layer::GlobalEvent::RetryRelease { request } => {
            global_layer::GlobalEvent::RetryRelease { request }
        },
        global_layer::GlobalEvent::Crash => global_layer::GlobalEvent::Crash,
        global_layer::GlobalEvent::BeginScan => {
            global_layer::GlobalEvent::BeginScan
        },
        global_layer::GlobalEvent::FinishScan => {
            global_layer::GlobalEvent::FinishScan
        },
        global_layer::GlobalEvent::TruncateTail => {
            global_layer::GlobalEvent::TruncateTail
        },
        global_layer::GlobalEvent::AbortScan => {
            global_layer::GlobalEvent::AbortScan
        },
        global_layer::GlobalEvent::BeginRecover => {
            global_layer::GlobalEvent::BeginRecover
        },
        global_layer::GlobalEvent::FinishRecover => {
            global_layer::GlobalEvent::FinishRecover
        },
    }
}

pub open spec fn journal_local_to_broker(
    event: runtime_layer::JournalEvent,
) -> p0_layer::Event {
    match event {
        runtime_layer::JournalEvent::JournalAppendCall { record } => {
            p0_layer::Event::JournalAppendCall { record }
        },
        runtime_layer::JournalEvent::JournalAppendLinearize { record } => {
            p0_layer::Event::BrokerLinearize { record }
        },
        runtime_layer::JournalEvent::JournalAppendReturn { cut } => {
            p0_layer::Event::JournalAppendReturn { cut }
        },
        runtime_layer::JournalEvent::JournalDiskFull { record, cut } => {
            p0_layer::Event::JournalDiskFull { record, cut }
        },
        runtime_layer::JournalEvent::InvokeEvent {
            request, attempt, call, journal_cut, ack_cut,
        } => p0_layer::Event::InvokeEvent {
            request, attempt, call, journal_cut, ack_cut,
        },
        runtime_layer::JournalEvent::DeliverEvent {
            request, attempt, observation, journal_cut,
        } => p0_layer::Event::DeliverEvent {
            request, attempt, observation, journal_cut,
        },
        runtime_layer::JournalEvent::IgnoreStale { request, attempt } => {
            p0_layer::Event::IgnoreStale { request, attempt }
        },
        runtime_layer::JournalEvent::RetryRelease { request } => {
            p0_layer::Event::RetryRelease { request }
        },
        runtime_layer::JournalEvent::Crash => p0_layer::Event::Crash,
        runtime_layer::JournalEvent::BeginRecover => p0_layer::Event::BeginRecover,
        runtime_layer::JournalEvent::FinishRecover => p0_layer::Event::FinishRecover,
    }
}

pub open spec fn event_match(
    source: global_layer::GlobalEvent,
    target: global_layer::GlobalEvent,
) -> bool {
    target == journal_to_broker_event(source)
}

pub proof fn translated_encoded_event_decodes(
    event: runtime_layer::JournalEvent,
)
    ensures global_layer::broker_decode(journal_to_broker_event(
        runtime_layer::journal_encode(event),
    )) == Option::Some(journal_local_to_broker(event)),
{
    match event {
        runtime_layer::JournalEvent::JournalAppendCall { .. }
        | runtime_layer::JournalEvent::JournalAppendLinearize { .. }
        | runtime_layer::JournalEvent::JournalAppendReturn { .. }
        | runtime_layer::JournalEvent::JournalDiskFull { .. }
        | runtime_layer::JournalEvent::InvokeEvent { .. }
        | runtime_layer::JournalEvent::DeliverEvent { .. }
        | runtime_layer::JournalEvent::IgnoreStale { .. }
        | runtime_layer::JournalEvent::RetryRelease { .. }
        | runtime_layer::JournalEvent::Crash
        | runtime_layer::JournalEvent::BeginRecover
        | runtime_layer::JournalEvent::FinishRecover => {},
    }
}

pub proof fn translated_decoded_event_is_broker_event(
    source: global_layer::GlobalEvent,
    local: runtime_layer::JournalEvent,
)
    requires runtime_layer::journal_decode(source) == Option::Some(local),
    ensures global_layer::broker_decode(journal_to_broker_event(source))
        == Option::Some(journal_local_to_broker(local)),
{
    match source {
        global_layer::GlobalEvent::BrokerLinearize { .. }
        | global_layer::GlobalEvent::JournalAppendCall { .. }
        | global_layer::GlobalEvent::JournalAppendLinearize { .. }
        | global_layer::GlobalEvent::JournalAppendReturn { .. }
        | global_layer::GlobalEvent::JournalDiskFull { .. }
        | global_layer::GlobalEvent::WalStage { .. }
        | global_layer::GlobalEvent::WalWriteFull { .. }
        | global_layer::GlobalEvent::WalWriteTorn { .. }
        | global_layer::GlobalEvent::WalFinishTorn { .. }
        | global_layer::GlobalEvent::WalFlushAck { .. }
        | global_layer::GlobalEvent::WalDiskFull { .. }
        | global_layer::GlobalEvent::InvokeEvent { .. }
        | global_layer::GlobalEvent::DeliverEvent { .. }
        | global_layer::GlobalEvent::IgnoreStale { .. }
        | global_layer::GlobalEvent::RetryRelease { .. }
        | global_layer::GlobalEvent::Crash
        | global_layer::GlobalEvent::BeginScan
        | global_layer::GlobalEvent::FinishScan
        | global_layer::GlobalEvent::TruncateTail
        | global_layer::GlobalEvent::AbortScan
        | global_layer::GlobalEvent::BeginRecover
        | global_layer::GlobalEvent::FinishRecover => {},
    }
}

pub open spec fn singleton(
    event: global_layer::GlobalEvent,
) -> Seq<global_layer::GlobalEvent> {
    Seq::empty().push(event)
}

// The weak-simulation infrastructure permits zero target steps only for a
// source label absent from every T2-observed projection.  No accepted atomic
// Journal label has that property.
pub open spec fn t2_projection_silent(
    event: global_layer::GlobalEvent,
) -> bool {
    let events = singleton(event);
    projection_layer::pi_append(events).len() == 0
        && projection_layer::pi_auth(events).len() == 0
        && projection_layer::pi_journal(events).len() == 0
        && projection_layer::pi_physical(events).len() == 0
        && projection_layer::pi_ack(events).len() == 0
        && projection_layer::pi_append_io(events).len() == 0
        && projection_layer::pi_control(events).len() == 0
        && projection_layer::pi_logical(events).len() == 0
        && forall|request: replay_layer::RequestId|
            #[trigger] projection_layer::pi_adapter(events, request).len() == 0
}

pub proof fn accepted_journal_event_is_not_silent(
    event: global_layer::GlobalEvent,
)
    requires runtime_layer::journal_constructor(event),
    ensures !t2_projection_silent(event),
{
    match event {
        global_layer::GlobalEvent::BrokerLinearize { .. }
        | global_layer::GlobalEvent::JournalAppendCall { .. }
        | global_layer::GlobalEvent::JournalAppendLinearize { .. }
        | global_layer::GlobalEvent::JournalAppendReturn { .. }
        | global_layer::GlobalEvent::JournalDiskFull { .. }
        | global_layer::GlobalEvent::WalStage { .. }
        | global_layer::GlobalEvent::WalWriteFull { .. }
        | global_layer::GlobalEvent::WalWriteTorn { .. }
        | global_layer::GlobalEvent::WalFinishTorn { .. }
        | global_layer::GlobalEvent::WalFlushAck { .. }
        | global_layer::GlobalEvent::WalDiskFull { .. }
        | global_layer::GlobalEvent::InvokeEvent { .. }
        | global_layer::GlobalEvent::DeliverEvent { .. }
        | global_layer::GlobalEvent::IgnoreStale { .. }
        | global_layer::GlobalEvent::RetryRelease { .. }
        | global_layer::GlobalEvent::Crash
        | global_layer::GlobalEvent::BeginScan
        | global_layer::GlobalEvent::FinishScan
        | global_layer::GlobalEvent::TruncateTail
        | global_layer::GlobalEvent::AbortScan
        | global_layer::GlobalEvent::BeginRecover
        | global_layer::GlobalEvent::FinishRecover => {},
    }
}

pub open spec fn translate_trace(
    events: Seq<global_layer::GlobalEvent>,
) -> Seq<global_layer::GlobalEvent>
    decreases events.len()
{
    if events.len() == 0 {
        Seq::empty()
    } else {
        translate_trace(events.drop_last()).push(
            journal_to_broker_event(events.last()),
        )
    }
}

pub proof fn translate_trace_push(
    events: Seq<global_layer::GlobalEvent>,
    event: global_layer::GlobalEvent,
)
    ensures translate_trace(events.push(event))
        == translate_trace(events).push(journal_to_broker_event(event)),
{
    assert(events.push(event).drop_last() =~= events);
    assert(events.push(event).last() == event);
}

pub proof fn translate_trace_len(events: Seq<global_layer::GlobalEvent>)
    ensures translate_trace(events).len() == events.len(),
    decreases events.len(),
{
    if events.len() > 0 {
        translate_trace_len(events.drop_last());
    }
}

pub proof fn translate_trace_index(
    events: Seq<global_layer::GlobalEvent>,
    index: nat,
)
    requires index < events.len(),
    ensures translate_trace(events)[index as int]
        == journal_to_broker_event(events[index as int]),
    decreases events.len(),
{
    let prefix = events.drop_last();
    translate_trace_len(prefix);
    if index < prefix.len() {
        translate_trace_index(prefix, index);
        assert(events[index as int] == prefix[index as int]);
    } else {
        assert(index == prefix.len());
        assert(events[index as int] == events.last());
    }
}

pub proof fn translate_trace_take(
    events: Seq<global_layer::GlobalEvent>,
    length: nat,
)
    requires length <= events.len(),
    ensures translate_trace(events.take(length as int))
        == translate_trace(events).take(length as int),
{
    translate_trace_len(events);
    translate_trace_len(events.take(length as int));
    assert(translate_trace(events.take(length as int)).len() == length);
    assert(translate_trace(events).take(length as int).len() == length);
    assert forall|index: int| 0 <= index < length implies
        translate_trace(events.take(length as int))[index]
            == translate_trace(events).take(length as int)[index] by {
        let n: nat = index as nat;
        translate_trace_index(events.take(length as int), n);
        translate_trace_index(events, n);
        assert(events.take(length as int)[index] == events[index]);
        assert(translate_trace(events).take(length as int)[index]
            == translate_trace(events)[index]);
    }
    assert(translate_trace(events.take(length as int)) =~=
        translate_trace(events).take(length as int));
}

pub proof fn translated_linearized_record(
    event: global_layer::GlobalEvent,
)
    ensures projection_layer::linearized_record(
        journal_to_broker_event(event),
    ) == projection_layer::linearized_record(event),
{
    match event {
        global_layer::GlobalEvent::BrokerLinearize { .. }
        | global_layer::GlobalEvent::JournalAppendCall { .. }
        | global_layer::GlobalEvent::JournalAppendLinearize { .. }
        | global_layer::GlobalEvent::JournalAppendReturn { .. }
        | global_layer::GlobalEvent::JournalDiskFull { .. }
        | global_layer::GlobalEvent::WalStage { .. }
        | global_layer::GlobalEvent::WalWriteFull { .. }
        | global_layer::GlobalEvent::WalWriteTorn { .. }
        | global_layer::GlobalEvent::WalFinishTorn { .. }
        | global_layer::GlobalEvent::WalFlushAck { .. }
        | global_layer::GlobalEvent::WalDiskFull { .. }
        | global_layer::GlobalEvent::InvokeEvent { .. }
        | global_layer::GlobalEvent::DeliverEvent { .. }
        | global_layer::GlobalEvent::IgnoreStale { .. }
        | global_layer::GlobalEvent::RetryRelease { .. }
        | global_layer::GlobalEvent::Crash
        | global_layer::GlobalEvent::BeginScan
        | global_layer::GlobalEvent::FinishScan
        | global_layer::GlobalEvent::TruncateTail
        | global_layer::GlobalEvent::AbortScan
        | global_layer::GlobalEvent::BeginRecover
        | global_layer::GlobalEvent::FinishRecover => {},
    }
}

pub proof fn translated_append_after(
    output: Seq<append_layer::AppendEvent<replay_layer::JournalRecord>>,
    event: global_layer::GlobalEvent,
)
    ensures projection_layer::append_after(
        output, journal_to_broker_event(event),
    ) == projection_layer::append_after(output, event),
{
    match event {
        global_layer::GlobalEvent::BrokerLinearize { .. }
        | global_layer::GlobalEvent::JournalAppendCall { .. }
        | global_layer::GlobalEvent::JournalAppendLinearize { .. }
        | global_layer::GlobalEvent::JournalAppendReturn { .. }
        | global_layer::GlobalEvent::JournalDiskFull { .. }
        | global_layer::GlobalEvent::WalStage { .. }
        | global_layer::GlobalEvent::WalWriteFull { .. }
        | global_layer::GlobalEvent::WalWriteTorn { .. }
        | global_layer::GlobalEvent::WalFinishTorn { .. }
        | global_layer::GlobalEvent::WalFlushAck { .. }
        | global_layer::GlobalEvent::WalDiskFull { .. }
        | global_layer::GlobalEvent::InvokeEvent { .. }
        | global_layer::GlobalEvent::DeliverEvent { .. }
        | global_layer::GlobalEvent::IgnoreStale { .. }
        | global_layer::GlobalEvent::RetryRelease { .. }
        | global_layer::GlobalEvent::Crash
        | global_layer::GlobalEvent::BeginScan
        | global_layer::GlobalEvent::FinishScan
        | global_layer::GlobalEvent::TruncateTail
        | global_layer::GlobalEvent::AbortScan
        | global_layer::GlobalEvent::BeginRecover
        | global_layer::GlobalEvent::FinishRecover => {},
    }
}

pub proof fn translated_physical_event(event: global_layer::GlobalEvent)
    ensures projection_layer::physical_event(journal_to_broker_event(event))
        == projection_layer::physical_event(event),
{
    match event {
        global_layer::GlobalEvent::BrokerLinearize { .. }
        | global_layer::GlobalEvent::JournalAppendCall { .. }
        | global_layer::GlobalEvent::JournalAppendLinearize { .. }
        | global_layer::GlobalEvent::JournalAppendReturn { .. }
        | global_layer::GlobalEvent::JournalDiskFull { .. }
        | global_layer::GlobalEvent::WalStage { .. }
        | global_layer::GlobalEvent::WalWriteFull { .. }
        | global_layer::GlobalEvent::WalWriteTorn { .. }
        | global_layer::GlobalEvent::WalFinishTorn { .. }
        | global_layer::GlobalEvent::WalFlushAck { .. }
        | global_layer::GlobalEvent::WalDiskFull { .. }
        | global_layer::GlobalEvent::InvokeEvent { .. }
        | global_layer::GlobalEvent::DeliverEvent { .. }
        | global_layer::GlobalEvent::IgnoreStale { .. }
        | global_layer::GlobalEvent::RetryRelease { .. }
        | global_layer::GlobalEvent::Crash
        | global_layer::GlobalEvent::BeginScan
        | global_layer::GlobalEvent::FinishScan
        | global_layer::GlobalEvent::TruncateTail
        | global_layer::GlobalEvent::AbortScan
        | global_layer::GlobalEvent::BeginRecover
        | global_layer::GlobalEvent::FinishRecover => {},
    }
}

pub proof fn translated_append_io_after(
    output: Seq<append_layer::AppendEvent<replay_layer::JournalRecord>>,
    event: global_layer::GlobalEvent,
)
    ensures projection_layer::append_io_after(
        output, journal_to_broker_event(event),
    ) == projection_layer::append_io_after(output, event),
{
    match event {
        global_layer::GlobalEvent::BrokerLinearize { .. }
        | global_layer::GlobalEvent::JournalAppendCall { .. }
        | global_layer::GlobalEvent::JournalAppendLinearize { .. }
        | global_layer::GlobalEvent::JournalAppendReturn { .. }
        | global_layer::GlobalEvent::JournalDiskFull { .. }
        | global_layer::GlobalEvent::WalStage { .. }
        | global_layer::GlobalEvent::WalWriteFull { .. }
        | global_layer::GlobalEvent::WalWriteTorn { .. }
        | global_layer::GlobalEvent::WalFinishTorn { .. }
        | global_layer::GlobalEvent::WalFlushAck { .. }
        | global_layer::GlobalEvent::WalDiskFull { .. }
        | global_layer::GlobalEvent::InvokeEvent { .. }
        | global_layer::GlobalEvent::DeliverEvent { .. }
        | global_layer::GlobalEvent::IgnoreStale { .. }
        | global_layer::GlobalEvent::RetryRelease { .. }
        | global_layer::GlobalEvent::Crash
        | global_layer::GlobalEvent::BeginScan
        | global_layer::GlobalEvent::FinishScan
        | global_layer::GlobalEvent::TruncateTail
        | global_layer::GlobalEvent::AbortScan
        | global_layer::GlobalEvent::BeginRecover
        | global_layer::GlobalEvent::FinishRecover => {},
    }
}

pub proof fn translated_pi_append(events: Seq<global_layer::GlobalEvent>)
    ensures projection_layer::pi_append(translate_trace(events))
        == projection_layer::pi_append(events),
    decreases events.len(),
{
    if events.len() > 0 {
        let prefix = events.drop_last();
        let event = events.last();
        assert(prefix.push(event) =~= events);
        translated_pi_append(prefix);
        translate_trace_push(prefix, event);
        projection_layer::pi_append_push(prefix, event);
        projection_layer::pi_append_push(
            translate_trace(prefix), journal_to_broker_event(event),
        );
        translated_append_after(
            projection_layer::pi_append(prefix), event,
        );
    }
}

pub proof fn translated_pi_journal(events: Seq<global_layer::GlobalEvent>)
    ensures projection_layer::pi_journal(translate_trace(events))
        == projection_layer::pi_journal(events),
    decreases events.len(),
{
    if events.len() > 0 {
        let prefix = events.drop_last();
        let event = events.last();
        assert(prefix.push(event) =~= events);
        translated_pi_journal(prefix);
        translate_trace_push(prefix, event);
        projection_layer::pi_journal_push(prefix, event);
        projection_layer::pi_journal_push(
            translate_trace(prefix), journal_to_broker_event(event),
        );
        translated_linearized_record(event);
    }
}

pub proof fn translated_pi_physical(events: Seq<global_layer::GlobalEvent>)
    ensures projection_layer::pi_physical(translate_trace(events))
        == projection_layer::pi_physical(events),
    decreases events.len(),
{
    if events.len() > 0 {
        let prefix = events.drop_last();
        let event = events.last();
        assert(prefix.push(event) =~= events);
        translated_pi_physical(prefix);
        translate_trace_push(prefix, event);
        projection_layer::pi_physical_push(prefix, event);
        projection_layer::pi_physical_push(
            translate_trace(prefix), journal_to_broker_event(event),
        );
        translated_physical_event(event);
    }
}

pub proof fn translated_pi_ack(events: Seq<global_layer::GlobalEvent>)
    ensures projection_layer::pi_ack(translate_trace(events))
        == projection_layer::pi_ack(events),
    decreases events.len(),
{
    if events.len() > 0 {
        let prefix = events.drop_last();
        let event = events.last();
        assert(prefix.push(event) =~= events);
        translated_pi_ack(prefix);
        translate_trace_push(prefix, event);
        projection_layer::pi_ack_push(prefix, event);
        projection_layer::pi_ack_push(
            translate_trace(prefix), journal_to_broker_event(event),
        );
        match event {
            global_layer::GlobalEvent::BrokerLinearize { .. }
            | global_layer::GlobalEvent::JournalAppendCall { .. }
            | global_layer::GlobalEvent::JournalAppendLinearize { .. }
            | global_layer::GlobalEvent::JournalAppendReturn { .. }
            | global_layer::GlobalEvent::JournalDiskFull { .. }
            | global_layer::GlobalEvent::WalStage { .. }
            | global_layer::GlobalEvent::WalWriteFull { .. }
            | global_layer::GlobalEvent::WalWriteTorn { .. }
            | global_layer::GlobalEvent::WalFinishTorn { .. }
            | global_layer::GlobalEvent::WalFlushAck { .. }
            | global_layer::GlobalEvent::WalDiskFull { .. }
            | global_layer::GlobalEvent::InvokeEvent { .. }
            | global_layer::GlobalEvent::DeliverEvent { .. }
            | global_layer::GlobalEvent::IgnoreStale { .. }
            | global_layer::GlobalEvent::RetryRelease { .. }
            | global_layer::GlobalEvent::Crash
            | global_layer::GlobalEvent::BeginScan
            | global_layer::GlobalEvent::FinishScan
            | global_layer::GlobalEvent::TruncateTail
            | global_layer::GlobalEvent::AbortScan
            | global_layer::GlobalEvent::BeginRecover
            | global_layer::GlobalEvent::FinishRecover => {},
        }
    }
}

pub proof fn translated_pi_append_io(events: Seq<global_layer::GlobalEvent>)
    ensures projection_layer::pi_append_io(translate_trace(events))
        == projection_layer::pi_append_io(events),
    decreases events.len(),
{
    if events.len() > 0 {
        let prefix = events.drop_last();
        let event = events.last();
        assert(prefix.push(event) =~= events);
        translated_pi_append_io(prefix);
        translate_trace_push(prefix, event);
        projection_layer::pi_append_io_push(prefix, event);
        projection_layer::pi_append_io_push(
            translate_trace(prefix), journal_to_broker_event(event),
        );
        translated_append_io_after(
            projection_layer::pi_append_io(prefix), event,
        );
    }
}

pub proof fn translated_pi_control(events: Seq<global_layer::GlobalEvent>)
    ensures projection_layer::pi_control(translate_trace(events))
        == projection_layer::pi_control(events),
    decreases events.len(),
{
    if events.len() > 0 {
        let prefix = events.drop_last();
        let event = events.last();
        assert(prefix.push(event) =~= events);
        translated_pi_control(prefix);
        translate_trace_push(prefix, event);
        projection_layer::pi_control_push(prefix, event);
        projection_layer::pi_control_push(
            translate_trace(prefix), journal_to_broker_event(event),
        );
        match event {
            global_layer::GlobalEvent::BrokerLinearize { .. }
            | global_layer::GlobalEvent::JournalAppendCall { .. }
            | global_layer::GlobalEvent::JournalAppendLinearize { .. }
            | global_layer::GlobalEvent::JournalAppendReturn { .. }
            | global_layer::GlobalEvent::JournalDiskFull { .. }
            | global_layer::GlobalEvent::WalStage { .. }
            | global_layer::GlobalEvent::WalWriteFull { .. }
            | global_layer::GlobalEvent::WalWriteTorn { .. }
            | global_layer::GlobalEvent::WalFinishTorn { .. }
            | global_layer::GlobalEvent::WalFlushAck { .. }
            | global_layer::GlobalEvent::WalDiskFull { .. }
            | global_layer::GlobalEvent::InvokeEvent { .. }
            | global_layer::GlobalEvent::DeliverEvent { .. }
            | global_layer::GlobalEvent::IgnoreStale { .. }
            | global_layer::GlobalEvent::RetryRelease { .. }
            | global_layer::GlobalEvent::Crash
            | global_layer::GlobalEvent::BeginScan
            | global_layer::GlobalEvent::FinishScan
            | global_layer::GlobalEvent::TruncateTail
            | global_layer::GlobalEvent::AbortScan
            | global_layer::GlobalEvent::BeginRecover
            | global_layer::GlobalEvent::FinishRecover => {},
        }
    }
}

pub proof fn translated_pi_logical(events: Seq<global_layer::GlobalEvent>)
    ensures projection_layer::pi_logical(translate_trace(events))
        == projection_layer::pi_logical(events),
    decreases events.len(),
{
    if events.len() > 0 {
        let prefix = events.drop_last();
        let event = events.last();
        assert(prefix.push(event) =~= events);
        translated_pi_logical(prefix);
        translate_trace_push(prefix, event);
        projection_layer::pi_logical_push(prefix, event);
        projection_layer::pi_logical_push(
            translate_trace(prefix), journal_to_broker_event(event),
        );
        translated_linearized_record(event);
    }
}

pub proof fn translated_pi_auth(events: Seq<global_layer::GlobalEvent>)
    ensures projection_layer::pi_auth(translate_trace(events))
        == projection_layer::pi_auth(events),
{
    translated_pi_journal(events);
}

pub proof fn translated_pi_adapter(
    events: Seq<global_layer::GlobalEvent>,
    request: replay_layer::RequestId,
)
    ensures projection_layer::pi_adapter(translate_trace(events), request)
        == projection_layer::pi_adapter(events, request),
{
    translated_pi_physical(events);
}

pub open spec fn t2_projection_agreement(
    source: Seq<global_layer::GlobalEvent>,
    target: Seq<global_layer::GlobalEvent>,
) -> bool {
    projection_layer::pi_append(source) == projection_layer::pi_append(target)
        && projection_layer::pi_auth(source) == projection_layer::pi_auth(target)
        && projection_layer::pi_journal(source) == projection_layer::pi_journal(target)
        && projection_layer::pi_physical(source)
            == projection_layer::pi_physical(target)
        && projection_layer::pi_control(source) == projection_layer::pi_control(target)
        && projection_layer::pi_logical(source) == projection_layer::pi_logical(target)
        && projection_layer::pi_ack(source) == projection_layer::pi_ack(target)
        && projection_layer::pi_append_io(source)
            == projection_layer::pi_append_io(target)
        && forall|request: replay_layer::RequestId|
            #[trigger] projection_layer::pi_adapter(source, request)
                == projection_layer::pi_adapter(target, request)
}

pub proof fn translated_trace_projection_agreement(
    events: Seq<global_layer::GlobalEvent>,
)
    ensures t2_projection_agreement(events, translate_trace(events)),
{
    translated_pi_append(events);
    translated_pi_auth(events);
    translated_pi_journal(events);
    translated_pi_physical(events);
    translated_pi_control(events);
    translated_pi_logical(events);
    translated_pi_ack(events);
    translated_pi_append_io(events);
    assert forall|request: replay_layer::RequestId|
        #[trigger] projection_layer::pi_adapter(events, request)
            == projection_layer::pi_adapter(translate_trace(events), request) by {
        translated_pi_adapter(events, request);
    }
}

} // verus!
