use vstd::prelude::*;

#[path = "t3_wal_trace.rs"]
pub mod trace_layer;

verus! {

use trace_layer::runtime_layer;
use runtime_layer::t2_layer::representation_layer::event_layer::trace_layer
    as journal_trace_layer;
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
use record_layer::query_layer::c1_layer;
use c1_layer::replay_layer;
use c1_layer::append_layer;

// T3-W1 compresses a typed-WAL trace to the atomic-Journal trace that it
// implements.  Twelve WAL constructors match Journal steps.  The remaining
// five constructors are private recovery or torn-write steps and are erased.
pub open spec fn wal_local_to_journal(
    event: runtime_layer::WalEvent,
) -> Option<journal_runtime_layer::JournalEvent> {
    match event {
        runtime_layer::WalEvent::WalStage { record } => Option::Some(
            journal_runtime_layer::JournalEvent::JournalAppendCall { record },
        ),
        runtime_layer::WalEvent::WalWriteFull { record }
        | runtime_layer::WalEvent::WalFinishTorn { record } => Option::Some(
            journal_runtime_layer::JournalEvent::JournalAppendLinearize { record },
        ),
        runtime_layer::WalEvent::WalWriteTorn { .. }
        | runtime_layer::WalEvent::BeginScan
        | runtime_layer::WalEvent::FinishScan
        | runtime_layer::WalEvent::TruncateTail
        | runtime_layer::WalEvent::AbortScan => Option::None,
        runtime_layer::WalEvent::WalFlushAck { cut } => Option::Some(
            journal_runtime_layer::JournalEvent::JournalAppendReturn { cut },
        ),
        runtime_layer::WalEvent::WalDiskFull { record, cut } => Option::Some(
            journal_runtime_layer::JournalEvent::JournalDiskFull { record, cut },
        ),
        runtime_layer::WalEvent::InvokeEvent {
            request, attempt, call, journal_cut, ack_cut,
        } => Option::Some(journal_runtime_layer::JournalEvent::InvokeEvent {
            request, attempt, call, journal_cut, ack_cut,
        }),
        runtime_layer::WalEvent::DeliverEvent {
            request, attempt, observation, journal_cut,
        } => Option::Some(journal_runtime_layer::JournalEvent::DeliverEvent {
            request, attempt, observation, journal_cut,
        }),
        runtime_layer::WalEvent::IgnoreStale { request, attempt } => Option::Some(
            journal_runtime_layer::JournalEvent::IgnoreStale { request, attempt },
        ),
        runtime_layer::WalEvent::RetryRelease { request } => Option::Some(
            journal_runtime_layer::JournalEvent::RetryRelease { request },
        ),
        runtime_layer::WalEvent::Crash => Option::Some(
            journal_runtime_layer::JournalEvent::Crash,
        ),
        runtime_layer::WalEvent::BeginRecover => Option::Some(
            journal_runtime_layer::JournalEvent::BeginRecover,
        ),
        runtime_layer::WalEvent::FinishRecover => Option::Some(
            journal_runtime_layer::JournalEvent::FinishRecover,
        ),
    }
}

pub open spec fn wal_local_internal(event: runtime_layer::WalEvent) -> bool {
    match event {
        runtime_layer::WalEvent::WalWriteTorn { .. }
        | runtime_layer::WalEvent::BeginScan
        | runtime_layer::WalEvent::FinishScan
        | runtime_layer::WalEvent::TruncateTail
        | runtime_layer::WalEvent::AbortScan => true,
        runtime_layer::WalEvent::WalStage { .. }
        | runtime_layer::WalEvent::WalWriteFull { .. }
        | runtime_layer::WalEvent::WalFinishTorn { .. }
        | runtime_layer::WalEvent::WalFlushAck { .. }
        | runtime_layer::WalEvent::WalDiskFull { .. }
        | runtime_layer::WalEvent::InvokeEvent { .. }
        | runtime_layer::WalEvent::DeliverEvent { .. }
        | runtime_layer::WalEvent::IgnoreStale { .. }
        | runtime_layer::WalEvent::RetryRelease { .. }
        | runtime_layer::WalEvent::Crash
        | runtime_layer::WalEvent::BeginRecover
        | runtime_layer::WalEvent::FinishRecover => false,
    }
}

pub proof fn local_translation_classifier_exact(event: runtime_layer::WalEvent)
    ensures
        wal_local_to_journal(event).is_none() <==> wal_local_internal(event),
        wal_local_to_journal(event).is_some() <==> !wal_local_internal(event),
{
    match event {
        runtime_layer::WalEvent::WalStage { .. }
        | runtime_layer::WalEvent::WalWriteFull { .. }
        | runtime_layer::WalEvent::WalWriteTorn { .. }
        | runtime_layer::WalEvent::WalFinishTorn { .. }
        | runtime_layer::WalEvent::WalFlushAck { .. }
        | runtime_layer::WalEvent::WalDiskFull { .. }
        | runtime_layer::WalEvent::InvokeEvent { .. }
        | runtime_layer::WalEvent::DeliverEvent { .. }
        | runtime_layer::WalEvent::IgnoreStale { .. }
        | runtime_layer::WalEvent::RetryRelease { .. }
        | runtime_layer::WalEvent::Crash
        | runtime_layer::WalEvent::BeginScan
        | runtime_layer::WalEvent::FinishScan
        | runtime_layer::WalEvent::TruncateTail
        | runtime_layer::WalEvent::AbortScan
        | runtime_layer::WalEvent::BeginRecover
        | runtime_layer::WalEvent::FinishRecover => {},
    }
}

// Partial translation over the complete global alphabet.  Non-WAL labels are
// rejected rather than silently treated as WAL stutters.
pub open spec fn translate_event(
    event: global_layer::GlobalEvent,
) -> Option<global_layer::GlobalEvent> {
    match event {
        global_layer::GlobalEvent::BrokerLinearize { .. }
        | global_layer::GlobalEvent::JournalAppendCall { .. }
        | global_layer::GlobalEvent::JournalAppendLinearize { .. }
        | global_layer::GlobalEvent::JournalAppendReturn { .. }
        | global_layer::GlobalEvent::JournalDiskFull { .. } => Option::None,
        global_layer::GlobalEvent::WalStage { record } => Option::Some(
            global_layer::GlobalEvent::JournalAppendCall { record },
        ),
        global_layer::GlobalEvent::WalWriteFull { record }
        | global_layer::GlobalEvent::WalFinishTorn { record } => Option::Some(
            global_layer::GlobalEvent::JournalAppendLinearize { record },
        ),
        global_layer::GlobalEvent::WalWriteTorn { .. }
        | global_layer::GlobalEvent::BeginScan
        | global_layer::GlobalEvent::FinishScan
        | global_layer::GlobalEvent::TruncateTail
        | global_layer::GlobalEvent::AbortScan => Option::None,
        global_layer::GlobalEvent::WalFlushAck { cut } => Option::Some(
            global_layer::GlobalEvent::JournalAppendReturn { cut },
        ),
        global_layer::GlobalEvent::WalDiskFull { record, cut } => Option::Some(
            global_layer::GlobalEvent::JournalDiskFull { record, cut },
        ),
        global_layer::GlobalEvent::InvokeEvent {
            request, attempt, call, journal_cut, ack_cut,
        } => Option::Some(global_layer::GlobalEvent::InvokeEvent {
            request, attempt, call, journal_cut, ack_cut,
        }),
        global_layer::GlobalEvent::DeliverEvent {
            request, attempt, observation, journal_cut,
        } => Option::Some(global_layer::GlobalEvent::DeliverEvent {
            request, attempt, observation, journal_cut,
        }),
        global_layer::GlobalEvent::IgnoreStale { request, attempt } => Option::Some(
            global_layer::GlobalEvent::IgnoreStale { request, attempt },
        ),
        global_layer::GlobalEvent::RetryRelease { request } => Option::Some(
            global_layer::GlobalEvent::RetryRelease { request },
        ),
        global_layer::GlobalEvent::Crash => Option::Some(
            global_layer::GlobalEvent::Crash,
        ),
        global_layer::GlobalEvent::BeginRecover => Option::Some(
            global_layer::GlobalEvent::BeginRecover,
        ),
        global_layer::GlobalEvent::FinishRecover => Option::Some(
            global_layer::GlobalEvent::FinishRecover,
        ),
    }
}

pub open spec fn wal_internal_event(event: global_layer::GlobalEvent) -> bool {
    match event {
        global_layer::GlobalEvent::WalWriteTorn { .. }
        | global_layer::GlobalEvent::BeginScan
        | global_layer::GlobalEvent::FinishScan
        | global_layer::GlobalEvent::TruncateTail
        | global_layer::GlobalEvent::AbortScan => true,
        global_layer::GlobalEvent::BrokerLinearize { .. }
        | global_layer::GlobalEvent::JournalAppendCall { .. }
        | global_layer::GlobalEvent::JournalAppendLinearize { .. }
        | global_layer::GlobalEvent::JournalAppendReturn { .. }
        | global_layer::GlobalEvent::JournalDiskFull { .. }
        | global_layer::GlobalEvent::WalStage { .. }
        | global_layer::GlobalEvent::WalWriteFull { .. }
        | global_layer::GlobalEvent::WalFinishTorn { .. }
        | global_layer::GlobalEvent::WalFlushAck { .. }
        | global_layer::GlobalEvent::WalDiskFull { .. }
        | global_layer::GlobalEvent::InvokeEvent { .. }
        | global_layer::GlobalEvent::DeliverEvent { .. }
        | global_layer::GlobalEvent::IgnoreStale { .. }
        | global_layer::GlobalEvent::RetryRelease { .. }
        | global_layer::GlobalEvent::Crash
        | global_layer::GlobalEvent::BeginRecover
        | global_layer::GlobalEvent::FinishRecover => false,
    }
}

pub open spec fn matched_wal_event(event: global_layer::GlobalEvent) -> bool {
    runtime_layer::wal_constructor(event) && translate_event(event).is_some()
}

pub proof fn wal_translation_classifier_exact(event: global_layer::GlobalEvent)
    requires runtime_layer::wal_constructor(event),
    ensures
        translate_event(event).is_none() <==> wal_internal_event(event),
        translate_event(event).is_some() <==> matched_wal_event(event),
        matched_wal_event(event) <==> !wal_internal_event(event),
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

pub proof fn translated_encoded_event(event: runtime_layer::WalEvent)
    ensures translate_event(runtime_layer::wal_encode(event)) ==
        match wal_local_to_journal(event) {
            Option::Some(target) => Option::Some(
                journal_runtime_layer::journal_encode(target),
            ),
            Option::None => Option::None,
        },
{
    match event {
        runtime_layer::WalEvent::WalStage { .. }
        | runtime_layer::WalEvent::WalWriteFull { .. }
        | runtime_layer::WalEvent::WalWriteTorn { .. }
        | runtime_layer::WalEvent::WalFinishTorn { .. }
        | runtime_layer::WalEvent::WalFlushAck { .. }
        | runtime_layer::WalEvent::WalDiskFull { .. }
        | runtime_layer::WalEvent::InvokeEvent { .. }
        | runtime_layer::WalEvent::DeliverEvent { .. }
        | runtime_layer::WalEvent::IgnoreStale { .. }
        | runtime_layer::WalEvent::RetryRelease { .. }
        | runtime_layer::WalEvent::Crash
        | runtime_layer::WalEvent::BeginScan
        | runtime_layer::WalEvent::FinishScan
        | runtime_layer::WalEvent::TruncateTail
        | runtime_layer::WalEvent::AbortScan
        | runtime_layer::WalEvent::BeginRecover
        | runtime_layer::WalEvent::FinishRecover => {},
    }
}

pub proof fn translated_decoded_event(
    source: global_layer::GlobalEvent,
    local: runtime_layer::WalEvent,
)
    requires runtime_layer::wal_decode(source) == Option::Some(local),
    ensures translate_event(source) == match wal_local_to_journal(local) {
        Option::Some(target) => Option::Some(
            journal_runtime_layer::journal_encode(target),
        ),
        Option::None => Option::None,
    },
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

pub proof fn translated_encoded_event_decodes(
    source: runtime_layer::WalEvent,
    target: journal_runtime_layer::JournalEvent,
)
    requires wal_local_to_journal(source) == Option::Some(target),
    ensures
        translate_event(runtime_layer::wal_encode(source)) == Option::Some(
            journal_runtime_layer::journal_encode(target),
        ),
        journal_runtime_layer::journal_decode(
            journal_runtime_layer::journal_encode(target),
        ) == Option::Some(target),
{
    translated_encoded_event(source);
    journal_runtime_layer::journal_decode_encode(target);
}

pub proof fn translated_target_is_journal_event(
    source: global_layer::GlobalEvent,
    target: global_layer::GlobalEvent,
)
    requires
        runtime_layer::wal_constructor(source),
        translate_event(source) == Option::Some(target),
    ensures journal_runtime_layer::journal_constructor(target),
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

pub open spec fn event_match(
    source: global_layer::GlobalEvent,
    target: global_layer::GlobalEvent,
) -> bool {
    translate_event(source) == Option::Some(target)
}

pub open spec fn singleton(
    event: global_layer::GlobalEvent,
) -> Seq<global_layer::GlobalEvent> {
    Seq::empty().push(event)
}

// This predicate names precisely the observations used across the T3 backend
// boundary.  pi_wal is intentionally absent: it exposes the implementation.
pub open spec fn t3_projection_silent(event: global_layer::GlobalEvent) -> bool {
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

pub proof fn internal_event_is_silent(event: global_layer::GlobalEvent)
    requires wal_internal_event(event),
    ensures t3_projection_silent(event),
{
    let empty = Seq::empty();
    let events = singleton(event);
    assert(events =~= empty.push(event));
    projection_layer::pi_append_push(empty, event);
    projection_layer::pi_journal_push(empty, event);
    projection_layer::pi_physical_push(empty, event);
    projection_layer::pi_ack_push(empty, event);
    projection_layer::pi_append_io_push(empty, event);
    projection_layer::pi_control_push(empty, event);
    projection_layer::pi_logical_push(empty, event);
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
    assert(projection_layer::pi_physical(events) =~= Seq::empty());
    assert forall|request: replay_layer::RequestId|
        #[trigger] projection_layer::pi_adapter(events, request).len() == 0 by {
    }
}

pub proof fn matched_wal_event_is_visible(event: global_layer::GlobalEvent)
    requires
        runtime_layer::wal_constructor(event),
        !wal_internal_event(event),
    ensures !t3_projection_silent(event),
{
    let empty = Seq::empty();
    let events = singleton(event);
    assert(events =~= empty.push(event));
    projection_layer::pi_append_push(empty, event);
    projection_layer::pi_journal_push(empty, event);
    projection_layer::pi_physical_push(empty, event);
    projection_layer::pi_control_push(empty, event);
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

pub proof fn internal_event_classifier_exact(event: global_layer::GlobalEvent)
    requires runtime_layer::wal_constructor(event),
    ensures t3_projection_silent(event) <==> wal_internal_event(event),
{
    if wal_internal_event(event) {
        internal_event_is_silent(event);
    } else {
        matched_wal_event_is_visible(event);
    }
}

pub proof fn translation_silence_classifier_exact(
    event: global_layer::GlobalEvent,
)
    requires runtime_layer::wal_constructor(event),
    ensures translate_event(event).is_none() <==> t3_projection_silent(event),
{
    wal_translation_classifier_exact(event);
    internal_event_classifier_exact(event);
}

pub open spec fn translate_trace(
    events: Seq<global_layer::GlobalEvent>,
) -> Seq<global_layer::GlobalEvent>
    decreases events.len()
{
    if events.len() == 0 {
        Seq::empty()
    } else {
        let prefix = translate_trace(events.drop_last());
        match translate_event(events.last()) {
            Option::Some(event) => prefix.push(event),
            Option::None => prefix,
        }
    }
}

pub open spec fn matched_count(events: Seq<global_layer::GlobalEvent>) -> nat
    decreases events.len()
{
    if events.len() == 0 {
        0
    } else {
        matched_count(events.drop_last()) + match translate_event(events.last()) {
            Option::Some(_) => 1nat,
            Option::None => 0nat,
        }
    }
}

pub proof fn translate_trace_push(
    events: Seq<global_layer::GlobalEvent>,
    event: global_layer::GlobalEvent,
)
    ensures translate_trace(events.push(event)) == match translate_event(event) {
        Option::Some(target) => translate_trace(events).push(target),
        Option::None => translate_trace(events),
    },
{
    assert(events.push(event).drop_last() =~= events);
    assert(events.push(event).last() == event);
}

pub proof fn matched_count_push(
    events: Seq<global_layer::GlobalEvent>,
    event: global_layer::GlobalEvent,
)
    ensures matched_count(events.push(event)) == matched_count(events)
        + match translate_event(event) {
            Option::Some(_) => 1nat,
            Option::None => 0nat,
        },
{
    assert(events.push(event).drop_last() =~= events);
    assert(events.push(event).last() == event);
}

pub proof fn translate_trace_len(events: Seq<global_layer::GlobalEvent>)
    ensures translate_trace(events).len() == matched_count(events),
    decreases events.len(),
{
    if events.len() > 0 {
        let prefix = events.drop_last();
        let event = events.last();
        assert(prefix.push(event) =~= events);
        translate_trace_len(prefix);
        translate_trace_push(prefix, event);
        matched_count_push(prefix, event);
    }
}

pub proof fn matched_count_le(events: Seq<global_layer::GlobalEvent>)
    ensures matched_count(events) <= events.len(),
    decreases events.len(),
{
    if events.len() > 0 {
        let prefix = events.drop_last();
        let event = events.last();
        assert(prefix.push(event) =~= events);
        matched_count_le(prefix);
        matched_count_push(prefix, event);
    }
}

pub proof fn translate_trace_len_bounded(events: Seq<global_layer::GlobalEvent>)
    ensures translate_trace(events).len() <= events.len(),
{
    translate_trace_len(events);
    matched_count_le(events);
}

pub proof fn matched_count_take_le(
    events: Seq<global_layer::GlobalEvent>,
    length: nat,
)
    requires length <= events.len(),
    ensures matched_count(events.take(length as int)) <= matched_count(events),
    decreases events.len(),
{
    if events.len() > 0 {
        let prefix = events.drop_last();
        let event = events.last();
        assert(prefix.push(event) =~= events);
        if length < events.len() {
            assert(length <= prefix.len());
            assert(events.take(length as int) =~= prefix.take(length as int));
            matched_count_take_le(prefix, length);
            matched_count_push(prefix, event);
        } else {
            assert(length == events.len());
            assert(events.take(length as int) =~= events);
        }
    } else {
        assert(length == 0);
    }
}

// A source prefix maps to a target prefix whose length is the number of
// matched source labels in that prefix.
pub proof fn translate_trace_take(
    events: Seq<global_layer::GlobalEvent>,
    length: nat,
)
    requires length <= events.len(),
    ensures translate_trace(events.take(length as int))
        == translate_trace(events).take(
            matched_count(events.take(length as int)) as int,
        ),
    decreases events.len(),
{
    if events.len() == 0 {
        assert(length == 0);
    } else {
        let prefix = events.drop_last();
        let event = events.last();
        assert(prefix.push(event) =~= events);
        if length < events.len() {
            assert(length <= prefix.len());
            assert(events.take(length as int) =~= prefix.take(length as int));
            translate_trace_take(prefix, length);
            matched_count_take_le(prefix, length);
            translate_trace_len(prefix);
            translate_trace_push(prefix, event);
            let count = matched_count(prefix.take(length as int));
            assert(count <= translate_trace(prefix).len());
            match translate_event(event) {
                Option::Some(target) => {
                    assert(translate_trace(events)
                        == translate_trace(prefix).push(target));
                    assert(translate_trace(events).take(count as int) =~=
                        translate_trace(prefix).take(count as int));
                },
                Option::None => {},
            }
        } else {
            assert(length == events.len());
            assert(events.take(length as int) =~= events);
            translate_trace_len(events);
            assert(translate_trace(events).take(
                matched_count(events) as int,
            ) =~= translate_trace(events));
        }
    }
}

pub proof fn translate_trace_take_prefix(
    events: Seq<global_layer::GlobalEvent>,
    length: nat,
)
    requires length <= events.len(),
    ensures translate_trace(events.take(length as int))
        == translate_trace(events).take(
            matched_count(events.take(length as int)) as int,
        ),
{
    translate_trace_take(events, length);
}

// A matched source event occurs at the target index equal to the number of
// earlier matched source events.
pub proof fn translate_trace_index(
    events: Seq<global_layer::GlobalEvent>,
    index: nat,
    target: global_layer::GlobalEvent,
)
    requires
        index < events.len(),
        translate_event(events[index as int]) == Option::Some(target),
    ensures
        matched_count(events.take(index as int)) < translate_trace(events).len(),
        translate_trace(events)[
            matched_count(events.take(index as int)) as int
        ] == target,
    decreases events.len(),
{
    let prefix = events.drop_last();
    let event = events.last();
    assert(prefix.push(event) =~= events);
    translate_trace_push(prefix, event);
    translate_trace_len(prefix);
    if index < prefix.len() {
        assert(events[index as int] == prefix[index as int]);
        assert(events.take(index as int) =~= prefix.take(index as int));
        translate_trace_index(prefix, index, target);
        match translate_event(event) {
            Option::Some(last_target) => {
                assert(translate_trace(events)
                    == translate_trace(prefix).push(last_target));
            },
            Option::None => {},
        }
    } else {
        assert(index == prefix.len());
        assert(events[index as int] == event);
        assert(events.take(index as int) =~= prefix);
        assert(translate_event(event) == Option::Some(target));
        assert(translate_trace(events) == translate_trace(prefix).push(target));
    }
}

pub proof fn wal_closed_last(events: Seq<global_layer::GlobalEvent>)
    requires runtime_layer::wal_trace_closed(events), events.len() > 0,
    ensures
        runtime_layer::wal_trace_closed(events.drop_last()),
        runtime_layer::wal_constructor(events.last()),
{
}

pub proof fn journal_closed_push(
    events: Seq<global_layer::GlobalEvent>,
    event: global_layer::GlobalEvent,
)
    requires
        journal_runtime_layer::journal_trace_closed(events),
        journal_runtime_layer::journal_constructor(event),
    ensures journal_runtime_layer::journal_trace_closed(events.push(event)),
{
    assert(events.push(event).drop_last() =~= events);
    assert(events.push(event).last() == event);
}

pub proof fn translated_trace_is_journal_closed(
    events: Seq<global_layer::GlobalEvent>,
)
    requires runtime_layer::wal_trace_closed(events),
    ensures journal_runtime_layer::journal_trace_closed(translate_trace(events)),
    decreases events.len(),
{
    if events.len() > 0 {
        let prefix = events.drop_last();
        let event = events.last();
        wal_closed_last(events);
        translated_trace_is_journal_closed(prefix);
        translate_trace_push(prefix, event);
        match translate_event(event) {
            Option::Some(target) => {
                translated_target_is_journal_event(event, target);
                journal_closed_push(translate_trace(prefix), target);
            },
            Option::None => {},
        }
    }
}

pub proof fn translated_linearized_record(event: global_layer::GlobalEvent)
    requires runtime_layer::wal_constructor(event),
    ensures match translate_event(event) {
        Option::Some(target) => projection_layer::linearized_record(target)
            == projection_layer::linearized_record(event),
        Option::None => projection_layer::linearized_record(event).is_none(),
    },
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
    requires runtime_layer::wal_constructor(event),
    ensures match translate_event(event) {
        Option::Some(target) => projection_layer::append_after(output, target)
            == projection_layer::append_after(output, event),
        Option::None => projection_layer::append_after(output, event) == output,
    },
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
    requires runtime_layer::wal_constructor(event),
    ensures match translate_event(event) {
        Option::Some(target) => projection_layer::physical_event(target)
            == projection_layer::physical_event(event),
        Option::None => projection_layer::physical_event(event).is_none(),
    },
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
    requires runtime_layer::wal_constructor(event),
    ensures match translate_event(event) {
        Option::Some(target) => projection_layer::append_io_after(output, target)
            == projection_layer::append_io_after(output, event),
        Option::None => projection_layer::append_io_after(output, event) == output,
    },
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
    requires runtime_layer::wal_trace_closed(events),
    ensures projection_layer::pi_append(translate_trace(events))
        == projection_layer::pi_append(events),
    decreases events.len(),
{
    if events.len() > 0 {
        let prefix = events.drop_last();
        let event = events.last();
        wal_closed_last(events);
        translated_pi_append(prefix);
        translate_trace_push(prefix, event);
        projection_layer::pi_append_push(prefix, event);
        translated_append_after(projection_layer::pi_append(prefix), event);
        match translate_event(event) {
            Option::Some(target) => {
                projection_layer::pi_append_push(translate_trace(prefix), target);
            },
            Option::None => {},
        }
    }
}

pub proof fn translated_pi_journal(events: Seq<global_layer::GlobalEvent>)
    requires runtime_layer::wal_trace_closed(events),
    ensures projection_layer::pi_journal(translate_trace(events))
        == projection_layer::pi_journal(events),
    decreases events.len(),
{
    if events.len() > 0 {
        let prefix = events.drop_last();
        let event = events.last();
        wal_closed_last(events);
        translated_pi_journal(prefix);
        translate_trace_push(prefix, event);
        projection_layer::pi_journal_push(prefix, event);
        translated_linearized_record(event);
        match translate_event(event) {
            Option::Some(target) => {
                projection_layer::pi_journal_push(translate_trace(prefix), target);
            },
            Option::None => {},
        }
    }
}

pub proof fn translated_pi_physical(events: Seq<global_layer::GlobalEvent>)
    requires runtime_layer::wal_trace_closed(events),
    ensures projection_layer::pi_physical(translate_trace(events))
        == projection_layer::pi_physical(events),
    decreases events.len(),
{
    if events.len() > 0 {
        let prefix = events.drop_last();
        let event = events.last();
        wal_closed_last(events);
        translated_pi_physical(prefix);
        translate_trace_push(prefix, event);
        projection_layer::pi_physical_push(prefix, event);
        translated_physical_event(event);
        match translate_event(event) {
            Option::Some(target) => {
                projection_layer::pi_physical_push(translate_trace(prefix), target);
            },
            Option::None => {},
        }
    }
}

pub proof fn translated_pi_ack(events: Seq<global_layer::GlobalEvent>)
    requires runtime_layer::wal_trace_closed(events),
    ensures projection_layer::pi_ack(translate_trace(events))
        == projection_layer::pi_ack(events),
    decreases events.len(),
{
    if events.len() > 0 {
        let prefix = events.drop_last();
        let event = events.last();
        wal_closed_last(events);
        translated_pi_ack(prefix);
        translate_trace_push(prefix, event);
        projection_layer::pi_ack_push(prefix, event);
        match translate_event(event) {
            Option::Some(target) => {
                projection_layer::pi_ack_push(translate_trace(prefix), target);
            },
            Option::None => {},
        }
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
    requires runtime_layer::wal_trace_closed(events),
    ensures projection_layer::pi_append_io(translate_trace(events))
        == projection_layer::pi_append_io(events),
    decreases events.len(),
{
    if events.len() > 0 {
        let prefix = events.drop_last();
        let event = events.last();
        wal_closed_last(events);
        translated_pi_append_io(prefix);
        translate_trace_push(prefix, event);
        projection_layer::pi_append_io_push(prefix, event);
        translated_append_io_after(projection_layer::pi_append_io(prefix), event);
        match translate_event(event) {
            Option::Some(target) => {
                projection_layer::pi_append_io_push(
                    translate_trace(prefix), target,
                );
            },
            Option::None => {},
        }
    }
}

pub proof fn translated_pi_control(events: Seq<global_layer::GlobalEvent>)
    requires runtime_layer::wal_trace_closed(events),
    ensures projection_layer::pi_control(translate_trace(events))
        == projection_layer::pi_control(events),
    decreases events.len(),
{
    if events.len() > 0 {
        let prefix = events.drop_last();
        let event = events.last();
        wal_closed_last(events);
        translated_pi_control(prefix);
        translate_trace_push(prefix, event);
        projection_layer::pi_control_push(prefix, event);
        match translate_event(event) {
            Option::Some(target) => {
                projection_layer::pi_control_push(translate_trace(prefix), target);
            },
            Option::None => {},
        }
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
    requires runtime_layer::wal_trace_closed(events),
    ensures projection_layer::pi_logical(translate_trace(events))
        == projection_layer::pi_logical(events),
    decreases events.len(),
{
    if events.len() > 0 {
        let prefix = events.drop_last();
        let event = events.last();
        wal_closed_last(events);
        translated_pi_logical(prefix);
        translate_trace_push(prefix, event);
        projection_layer::pi_logical_push(prefix, event);
        translated_linearized_record(event);
        match translate_event(event) {
            Option::Some(target) => {
                projection_layer::pi_logical_push(translate_trace(prefix), target);
            },
            Option::None => {},
        }
    }
}

pub proof fn translated_pi_auth(events: Seq<global_layer::GlobalEvent>)
    requires runtime_layer::wal_trace_closed(events),
    ensures projection_layer::pi_auth(translate_trace(events))
        == projection_layer::pi_auth(events),
{
    translated_pi_journal(events);
}

pub proof fn translated_pi_adapter(
    events: Seq<global_layer::GlobalEvent>,
    request: replay_layer::RequestId,
)
    requires runtime_layer::wal_trace_closed(events),
    ensures projection_layer::pi_adapter(translate_trace(events), request)
        == projection_layer::pi_adapter(events, request),
{
    translated_pi_physical(events);
}

pub open spec fn t3_projection_agreement(
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
    requires runtime_layer::wal_trace_closed(events),
    ensures t3_projection_agreement(events, translate_trace(events)),
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
