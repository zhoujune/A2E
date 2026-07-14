use vstd::prelude::*;

#[path = "t1_global_event.rs"]
pub mod global_layer;

verus! {

use global_layer::bridge_layer;
use bridge_layer::contract_layer::p3_layer::p2_layer::p1_layer::p0_layer;
use p0_layer::config_layer;
use config_layer::broker_layer as record_layer;
use record_layer::query_layer::c1_layer;
use c1_layer::replay_layer;
use c1_layer::append_layer;

// G1-P defines the paper's projections once, over the complete global event
// alphabet.  A Broker trace is embedded without filtering.  Conversely, the
// decoder is partial and rejects a trace as soon as any backend-only label is
// present, so no theorem silently changes event-prefix indices.

#[allow(inconsistent_fields)]
#[derive(PartialEq, Eq)]
pub enum LogicalEvent {
    Commit {
        request: replay_layer::RequestId,
        attempt: replay_layer::AttemptId,
        value: replay_layer::Value,
    },
    Fail {
        request: replay_layer::RequestId,
        attempt: replay_layer::AttemptId,
    },
    UnknownOutcome {
        request: replay_layer::RequestId,
        attempt: Option<replay_layer::AttemptId>,
        reason: replay_layer::UnknownReason,
    },
}

pub open spec fn linearized_record(
    event: global_layer::GlobalEvent,
) -> Option<replay_layer::JournalRecord> {
    match event {
        global_layer::GlobalEvent::BrokerLinearize { record } => {
            Option::Some(record)
        },
        global_layer::GlobalEvent::JournalAppendCall { record: _ } => {
            Option::None
        },
        global_layer::GlobalEvent::JournalAppendLinearize { record } => {
            Option::Some(record)
        },
        global_layer::GlobalEvent::JournalAppendReturn { cut: _ } => {
            Option::None
        },
        global_layer::GlobalEvent::JournalDiskFull { record: _, cut: _ } => {
            Option::None
        },
        global_layer::GlobalEvent::WalStage { record: _ } => Option::None,
        global_layer::GlobalEvent::WalWriteFull { record } => {
            Option::Some(record)
        },
        global_layer::GlobalEvent::WalWriteTorn { record: _ } => Option::None,
        global_layer::GlobalEvent::WalFinishTorn { record } => {
            Option::Some(record)
        },
        global_layer::GlobalEvent::WalFlushAck { cut: _ } => Option::None,
        global_layer::GlobalEvent::WalDiskFull { record: _, cut: _ } => {
            Option::None
        },
        global_layer::GlobalEvent::InvokeEvent { .. } => Option::None,
        global_layer::GlobalEvent::DeliverEvent { .. } => Option::None,
        global_layer::GlobalEvent::IgnoreStale { .. } => Option::None,
        global_layer::GlobalEvent::RetryRelease { .. } => Option::None,
        global_layer::GlobalEvent::Crash => Option::None,
        global_layer::GlobalEvent::BeginScan => Option::None,
        global_layer::GlobalEvent::FinishScan => Option::None,
        global_layer::GlobalEvent::TruncateTail => Option::None,
        global_layer::GlobalEvent::AbortScan => Option::None,
        global_layer::GlobalEvent::BeginRecover => Option::None,
        global_layer::GlobalEvent::FinishRecover => Option::None,
    }
}

pub open spec fn append_after(
    output: Seq<append_layer::AppendEvent<replay_layer::JournalRecord>>,
    event: global_layer::GlobalEvent,
) -> Seq<append_layer::AppendEvent<replay_layer::JournalRecord>> {
    match event {
        global_layer::GlobalEvent::JournalAppendCall { record }
        | global_layer::GlobalEvent::WalStage { record } => {
            output.push(append_layer::AppendEvent::Call { record })
        },
        global_layer::GlobalEvent::BrokerLinearize { record }
        | global_layer::GlobalEvent::JournalAppendLinearize { record }
        | global_layer::GlobalEvent::WalWriteFull { record }
        | global_layer::GlobalEvent::WalFinishTorn { record } => {
            output.push(append_layer::AppendEvent::Linearize { record })
        },
        global_layer::GlobalEvent::JournalAppendReturn { cut }
        | global_layer::GlobalEvent::WalFlushAck { cut } => {
            output.push(append_layer::AppendEvent::Return {
                result: append_layer::AppendResult::Ok,
                cut,
            })
        },
        global_layer::GlobalEvent::JournalDiskFull { record, cut }
        | global_layer::GlobalEvent::WalDiskFull { record, cut } => {
            output.push(append_layer::AppendEvent::Call { record }).push(
                append_layer::AppendEvent::Return {
                    result: append_layer::AppendResult::Full,
                    cut,
                },
            )
        },
        global_layer::GlobalEvent::WalWriteTorn { .. }
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
        | global_layer::GlobalEvent::FinishRecover => output,
    }
}

pub open spec fn pi_append(
    events: Seq<global_layer::GlobalEvent>,
) -> Seq<append_layer::AppendEvent<replay_layer::JournalRecord>>
    decreases events.len()
{
    if events.len() == 0 {
        Seq::empty()
    } else {
        append_after(pi_append(events.drop_last()), events.last())
    }
}

// Total raw append-control projection.  Unlike pi_append, this emits exactly
// one B1 control label per global label, preserving global prefix indices.
// The six Broker stutter kinds agree definitionally with B2-A; backend-only
// stutters use disjoint additional tags.
pub open spec fn global_append_event(
    event: global_layer::GlobalEvent,
) -> append_layer::Event<replay_layer::JournalRecord> {
    match event {
        global_layer::GlobalEvent::JournalAppendCall { record }
        | global_layer::GlobalEvent::WalStage { record } => {
            append_layer::Event::Call { record }
        },
        global_layer::GlobalEvent::BrokerLinearize { record }
        | global_layer::GlobalEvent::JournalAppendLinearize { record }
        | global_layer::GlobalEvent::WalWriteFull { record }
        | global_layer::GlobalEvent::WalFinishTorn { record } => {
            append_layer::Event::Linearize { record }
        },
        global_layer::GlobalEvent::JournalAppendReturn { cut }
        | global_layer::GlobalEvent::WalFlushAck { cut } => {
            append_layer::Event::ReturnOk { cut }
        },
        global_layer::GlobalEvent::JournalDiskFull { record, cut }
        | global_layer::GlobalEvent::WalDiskFull { record, cut } => {
            append_layer::Event::DiskFull { record, cut }
        },
        global_layer::GlobalEvent::Crash => append_layer::Event::Crash,
        global_layer::GlobalEvent::IgnoreStale { .. } => {
            append_layer::Event::Stutter { kind: 0 }
        },
        global_layer::GlobalEvent::RetryRelease { .. } => {
            append_layer::Event::Stutter { kind: 1 }
        },
        global_layer::GlobalEvent::BeginRecover => {
            append_layer::Event::Stutter { kind: 2 }
        },
        global_layer::GlobalEvent::FinishRecover => {
            append_layer::Event::Stutter { kind: 3 }
        },
        global_layer::GlobalEvent::InvokeEvent { .. } => {
            append_layer::Event::Stutter { kind: 4 }
        },
        global_layer::GlobalEvent::DeliverEvent { .. } => {
            append_layer::Event::Stutter { kind: 5 }
        },
        global_layer::GlobalEvent::WalWriteTorn { .. } => {
            append_layer::Event::Stutter { kind: 6 }
        },
        global_layer::GlobalEvent::BeginScan => {
            append_layer::Event::Stutter { kind: 7 }
        },
        global_layer::GlobalEvent::FinishScan => {
            append_layer::Event::Stutter { kind: 8 }
        },
        global_layer::GlobalEvent::TruncateTail => {
            append_layer::Event::Stutter { kind: 9 }
        },
        global_layer::GlobalEvent::AbortScan => {
            append_layer::Event::Stutter { kind: 10 }
        },
    }
}

pub open spec fn global_append_project(
    events: Seq<global_layer::GlobalEvent>,
) -> Seq<append_layer::Event<replay_layer::JournalRecord>>
    decreases events.len()
{
    if events.len() == 0 {
        Seq::empty()
    } else {
        global_append_project(events.drop_last()).push(
            global_append_event(events.last()),
        )
    }
}

pub open spec fn global_append_protocol_prefix(
    events: Seq<global_layer::GlobalEvent>,
) -> bool {
    append_layer::append_protocol_prefix(global_append_project(events))
}

pub open spec fn pi_journal(
    events: Seq<global_layer::GlobalEvent>,
) -> Seq<replay_layer::JournalRecord>
    decreases events.len()
{
    if events.len() == 0 {
        Seq::empty()
    } else {
        let prefix = pi_journal(events.drop_last());
        match linearized_record(events.last()) {
            Option::Some(record) => prefix.push(record),
            Option::None => prefix,
        }
    }
}

pub open spec fn physical_event(
    event: global_layer::GlobalEvent,
) -> Option<p0_layer::PhysicalEvent> {
    match event {
        global_layer::GlobalEvent::InvokeEvent {
            request, attempt, call, journal_cut, ack_cut,
        } => Option::Some(p0_layer::PhysicalEvent::Invoke {
            request, attempt, call, journal_cut, ack_cut,
        }),
        global_layer::GlobalEvent::DeliverEvent {
            request, attempt, observation, journal_cut,
        } => Option::Some(p0_layer::PhysicalEvent::Delivered {
            request, attempt, observation, journal_cut,
        }),
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
        | global_layer::GlobalEvent::IgnoreStale { .. }
        | global_layer::GlobalEvent::RetryRelease { .. }
        | global_layer::GlobalEvent::Crash
        | global_layer::GlobalEvent::BeginScan
        | global_layer::GlobalEvent::FinishScan
        | global_layer::GlobalEvent::TruncateTail
        | global_layer::GlobalEvent::AbortScan
        | global_layer::GlobalEvent::BeginRecover
        | global_layer::GlobalEvent::FinishRecover => Option::None,
    }
}

pub open spec fn pi_physical(
    events: Seq<global_layer::GlobalEvent>,
) -> Seq<p0_layer::PhysicalEvent>
    decreases events.len()
{
    if events.len() == 0 {
        Seq::empty()
    } else {
        let prefix = pi_physical(events.drop_last());
        match physical_event(events.last()) {
            Option::Some(event) => prefix.push(event),
            Option::None => prefix,
        }
    }
}

pub open spec fn pi_ack(
    events: Seq<global_layer::GlobalEvent>,
) -> Seq<nat>
    decreases events.len()
{
    if events.len() == 0 {
        Seq::empty()
    } else {
        let prefix = pi_ack(events.drop_last());
        match events.last() {
            global_layer::GlobalEvent::JournalAppendReturn { cut }
            | global_layer::GlobalEvent::WalFlushAck { cut } => prefix.push(cut),
            global_layer::GlobalEvent::BrokerLinearize { .. }
            | global_layer::GlobalEvent::JournalAppendCall { .. }
            | global_layer::GlobalEvent::JournalAppendLinearize { .. }
            | global_layer::GlobalEvent::JournalDiskFull { .. }
            | global_layer::GlobalEvent::WalStage { .. }
            | global_layer::GlobalEvent::WalWriteFull { .. }
            | global_layer::GlobalEvent::WalWriteTorn { .. }
            | global_layer::GlobalEvent::WalFinishTorn { .. }
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
            | global_layer::GlobalEvent::FinishRecover => prefix,
        }
    }
}

pub open spec fn append_io_after(
    output: Seq<append_layer::AppendEvent<replay_layer::JournalRecord>>,
    event: global_layer::GlobalEvent,
) -> Seq<append_layer::AppendEvent<replay_layer::JournalRecord>> {
    match event {
        global_layer::GlobalEvent::JournalAppendCall { record }
        | global_layer::GlobalEvent::WalStage { record } => {
            output.push(append_layer::AppendEvent::Call { record })
        },
        global_layer::GlobalEvent::JournalAppendReturn { cut }
        | global_layer::GlobalEvent::WalFlushAck { cut } => {
            output.push(append_layer::AppendEvent::Return {
                result: append_layer::AppendResult::Ok,
                cut,
            })
        },
        global_layer::GlobalEvent::JournalDiskFull { record, cut }
        | global_layer::GlobalEvent::WalDiskFull { record, cut } => {
            output.push(append_layer::AppendEvent::Call { record }).push(
                append_layer::AppendEvent::Return {
                    result: append_layer::AppendResult::Full,
                    cut,
                },
            )
        },
        global_layer::GlobalEvent::BrokerLinearize { .. }
        | global_layer::GlobalEvent::JournalAppendLinearize { .. }
        | global_layer::GlobalEvent::WalWriteFull { .. }
        | global_layer::GlobalEvent::WalWriteTorn { .. }
        | global_layer::GlobalEvent::WalFinishTorn { .. }
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
        | global_layer::GlobalEvent::FinishRecover => output,
    }
}

pub open spec fn pi_append_io(
    events: Seq<global_layer::GlobalEvent>,
) -> Seq<append_layer::AppendEvent<replay_layer::JournalRecord>>
    decreases events.len()
{
    if events.len() == 0 {
        Seq::empty()
    } else {
        append_io_after(pi_append_io(events.drop_last()), events.last())
    }
}

pub open spec fn pi_control(
    events: Seq<global_layer::GlobalEvent>,
) -> Seq<global_layer::GlobalEvent>
    decreases events.len()
{
    if events.len() == 0 {
        Seq::empty()
    } else {
        let prefix = pi_control(events.drop_last());
        match events.last() {
            event @ global_layer::GlobalEvent::IgnoreStale { .. }
            | event @ global_layer::GlobalEvent::RetryRelease { .. }
            | event @ global_layer::GlobalEvent::Crash
            | event @ global_layer::GlobalEvent::BeginRecover
            | event @ global_layer::GlobalEvent::FinishRecover => {
                prefix.push(event)
            },
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
            | global_layer::GlobalEvent::BeginScan
            | global_layer::GlobalEvent::FinishScan
            | global_layer::GlobalEvent::TruncateTail
            | global_layer::GlobalEvent::AbortScan => prefix,
        }
    }
}

pub open spec fn logical_record(
    record: replay_layer::JournalRecord,
) -> Option<LogicalEvent> {
    match record {
        replay_layer::JournalRecord::CommitRec {
            request, attempt, value, ..
        } => Option::Some(LogicalEvent::Commit { request, attempt, value }),
        replay_layer::JournalRecord::FailRec { request, attempt, .. } => {
            Option::Some(LogicalEvent::Fail { request, attempt })
        },
        replay_layer::JournalRecord::UnknownRec {
            request, attempt, reason, ..
        } => Option::Some(LogicalEvent::UnknownOutcome {
            request, attempt, reason,
        }),
        replay_layer::JournalRecord::Authorize { .. }
        | replay_layer::JournalRecord::Revoke { .. }
        | replay_layer::JournalRecord::Prepare { .. }
        | replay_layer::JournalRecord::Arm { .. }
        | replay_layer::JournalRecord::Start { .. }
        | replay_layer::JournalRecord::Outcome { .. } => Option::None,
    }
}

pub open spec fn logical_after(
    output: Seq<LogicalEvent>,
    event: global_layer::GlobalEvent,
) -> Seq<LogicalEvent> {
    match linearized_record(event) {
        Option::None => output,
        Option::Some(record) => match logical_record(record) {
            Option::None => output,
            Option::Some(logical) => output.push(logical),
        },
    }
}

pub open spec fn pi_logical(
    events: Seq<global_layer::GlobalEvent>,
) -> Seq<LogicalEvent>
    decreases events.len()
{
    if events.len() == 0 {
        Seq::empty()
    } else {
        logical_after(pi_logical(events.drop_last()), events.last())
    }
}

pub open spec fn pi_wal(
    events: Seq<global_layer::GlobalEvent>,
) -> Seq<global_layer::GlobalEvent>
    decreases events.len()
{
    if events.len() == 0 {
        Seq::empty()
    } else {
        let prefix = pi_wal(events.drop_last());
        match events.last() {
            event @ global_layer::GlobalEvent::WalStage { .. }
            | event @ global_layer::GlobalEvent::WalWriteFull { .. }
            | event @ global_layer::GlobalEvent::WalWriteTorn { .. }
            | event @ global_layer::GlobalEvent::WalFinishTorn { .. }
            | event @ global_layer::GlobalEvent::WalFlushAck { .. }
            | event @ global_layer::GlobalEvent::WalDiskFull { .. }
            | event @ global_layer::GlobalEvent::Crash
            | event @ global_layer::GlobalEvent::BeginScan
            | event @ global_layer::GlobalEvent::FinishScan
            | event @ global_layer::GlobalEvent::TruncateTail
            | event @ global_layer::GlobalEvent::AbortScan
            | event @ global_layer::GlobalEvent::BeginRecover
            | event @ global_layer::GlobalEvent::FinishRecover => {
                prefix.push(event)
            },
            global_layer::GlobalEvent::BrokerLinearize { .. }
            | global_layer::GlobalEvent::JournalAppendCall { .. }
            | global_layer::GlobalEvent::JournalAppendLinearize { .. }
            | global_layer::GlobalEvent::JournalAppendReturn { .. }
            | global_layer::GlobalEvent::JournalDiskFull { .. }
            | global_layer::GlobalEvent::InvokeEvent { .. }
            | global_layer::GlobalEvent::DeliverEvent { .. }
            | global_layer::GlobalEvent::IgnoreStale { .. }
            | global_layer::GlobalEvent::RetryRelease { .. } => prefix,
        }
    }
}

// Eventwise embedding/decoding.  broker_encode_trace is length-preserving;
// broker_decode_trace never filters and instead returns None at the first
// backend-only constructor.
pub open spec fn broker_encode_trace(
    events: Seq<p0_layer::Event>,
) -> Seq<global_layer::GlobalEvent>
    decreases events.len()
{
    if events.len() == 0 {
        Seq::empty()
    } else {
        broker_encode_trace(events.drop_last()).push(
            global_layer::broker_encode(events.last()),
        )
    }
}

pub open spec fn broker_decode_trace(
    events: Seq<global_layer::GlobalEvent>,
) -> Option<Seq<p0_layer::Event>>
    decreases events.len()
{
    if events.len() == 0 {
        Option::Some(Seq::empty())
    } else {
        match broker_decode_trace(events.drop_last()) {
            Option::None => Option::None,
            Option::Some(prefix) => match global_layer::broker_decode(events.last()) {
                Option::None => Option::None,
                Option::Some(event) => Option::Some(prefix.push(event)),
            },
        }
    }
}

pub open spec fn broker_trace_closed(
    events: Seq<global_layer::GlobalEvent>,
) -> bool
    decreases events.len()
{
    events.len() == 0
        || (broker_trace_closed(events.drop_last())
            && global_layer::broker_constructor(events.last()))
}

pub open spec fn broker_trace_decodable(
    events: Seq<global_layer::GlobalEvent>,
) -> bool {
    match broker_decode_trace(events) {
        Option::Some(_) => true,
        Option::None => false,
    }
}

// Append events since the most recent Crash.  Unlike pi_append, this resets
// the word at Crash and therefore states the per-epoch language used by T1.
pub open spec fn global_epoch_io_after(
    output: Seq<append_layer::AppendEvent<replay_layer::JournalRecord>>,
    event: global_layer::GlobalEvent,
) -> Seq<append_layer::AppendEvent<replay_layer::JournalRecord>> {
    match event {
        global_layer::GlobalEvent::JournalAppendCall { record }
        | global_layer::GlobalEvent::WalStage { record } => {
            output.push(append_layer::AppendEvent::Call { record })
        },
        global_layer::GlobalEvent::BrokerLinearize { record }
        | global_layer::GlobalEvent::JournalAppendLinearize { record }
        | global_layer::GlobalEvent::WalWriteFull { record }
        | global_layer::GlobalEvent::WalFinishTorn { record } => {
            output.push(append_layer::AppendEvent::Linearize { record })
        },
        global_layer::GlobalEvent::JournalAppendReturn { cut }
        | global_layer::GlobalEvent::WalFlushAck { cut } => {
            output.push(append_layer::AppendEvent::Return {
                result: append_layer::AppendResult::Ok,
                cut,
            })
        },
        global_layer::GlobalEvent::JournalDiskFull { record, cut }
        | global_layer::GlobalEvent::WalDiskFull { record, cut } => {
            output.push(append_layer::AppendEvent::Call { record }).push(
                append_layer::AppendEvent::Return {
                    result: append_layer::AppendResult::Full,
                    cut,
                },
            )
        },
        global_layer::GlobalEvent::Crash => Seq::empty(),
        global_layer::GlobalEvent::WalWriteTorn { .. }
        | global_layer::GlobalEvent::InvokeEvent { .. }
        | global_layer::GlobalEvent::DeliverEvent { .. }
        | global_layer::GlobalEvent::IgnoreStale { .. }
        | global_layer::GlobalEvent::RetryRelease { .. }
        | global_layer::GlobalEvent::BeginScan
        | global_layer::GlobalEvent::FinishScan
        | global_layer::GlobalEvent::TruncateTail
        | global_layer::GlobalEvent::AbortScan
        | global_layer::GlobalEvent::BeginRecover
        | global_layer::GlobalEvent::FinishRecover => output,
    }
}

pub open spec fn global_current_epoch_io(
    events: Seq<global_layer::GlobalEvent>,
) -> Seq<append_layer::AppendEvent<replay_layer::JournalRecord>>
    decreases events.len()
{
    if events.len() == 0 {
        Seq::empty()
    } else {
        global_epoch_io_after(
            global_current_epoch_io(events.drop_last()),
            events.last(),
        )
    }
}

pub open spec fn global_crash_free(
    events: Seq<global_layer::GlobalEvent>,
) -> bool
    decreases events.len()
{
    if events.len() == 0 {
        true
    } else {
        global_crash_free(events.drop_last())
            && match events.last() {
                global_layer::GlobalEvent::Crash => false,
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
                | global_layer::GlobalEvent::BeginScan
                | global_layer::GlobalEvent::FinishScan
                | global_layer::GlobalEvent::TruncateTail
                | global_layer::GlobalEvent::AbortScan
                | global_layer::GlobalEvent::BeginRecover
                | global_layer::GlobalEvent::FinishRecover => true,
            }
    }
}

pub open spec fn logical_records(
    records: Seq<replay_layer::JournalRecord>,
) -> Seq<LogicalEvent>
    decreases records.len()
{
    if records.len() == 0 {
        Seq::empty()
    } else {
        let prefix = logical_records(records.drop_last());
        match logical_record(records.last()) {
            Option::Some(event) => prefix.push(event),
            Option::None => prefix,
        }
    }
}

// These two local views are used only to state exact correspondence for the
// control and WAL-boundary projections, which did not previously have named
// B2-A functions.
pub open spec fn broker_pi_control(
    events: Seq<p0_layer::Event>,
) -> Seq<global_layer::GlobalEvent>
    decreases events.len()
{
    if events.len() == 0 {
        Seq::empty()
    } else {
        let prefix = broker_pi_control(events.drop_last());
        match events.last() {
            event @ p0_layer::Event::IgnoreStale { .. }
            | event @ p0_layer::Event::RetryRelease { .. }
            | event @ p0_layer::Event::Crash
            | event @ p0_layer::Event::BeginRecover
            | event @ p0_layer::Event::FinishRecover => {
                prefix.push(global_layer::broker_encode(event))
            },
            p0_layer::Event::JournalAppendCall { .. }
            | p0_layer::Event::BrokerLinearize { .. }
            | p0_layer::Event::JournalAppendReturn { .. }
            | p0_layer::Event::JournalDiskFull { .. }
            | p0_layer::Event::InvokeEvent { .. }
            | p0_layer::Event::DeliverEvent { .. } => prefix,
        }
    }
}

pub open spec fn broker_pi_wal_boundary(
    events: Seq<p0_layer::Event>,
) -> Seq<global_layer::GlobalEvent>
    decreases events.len()
{
    if events.len() == 0 {
        Seq::empty()
    } else {
        let prefix = broker_pi_wal_boundary(events.drop_last());
        match events.last() {
            event @ p0_layer::Event::Crash
            | event @ p0_layer::Event::BeginRecover
            | event @ p0_layer::Event::FinishRecover => {
                prefix.push(global_layer::broker_encode(event))
            },
            p0_layer::Event::JournalAppendCall { .. }
            | p0_layer::Event::BrokerLinearize { .. }
            | p0_layer::Event::JournalAppendReturn { .. }
            | p0_layer::Event::JournalDiskFull { .. }
            | p0_layer::Event::InvokeEvent { .. }
            | p0_layer::Event::DeliverEvent { .. }
            | p0_layer::Event::IgnoreStale { .. }
            | p0_layer::Event::RetryRelease { .. } => prefix,
        }
    }
}

// Definitional push lemmas for all recursively defined global projections.
pub proof fn pi_append_push(
    events: Seq<global_layer::GlobalEvent>,
    event: global_layer::GlobalEvent,
)
    ensures pi_append(events.push(event)) == append_after(pi_append(events), event),
{
    assert(events.push(event).drop_last() =~= events);
    assert(events.push(event).last() == event);
}

pub proof fn pi_journal_push(
    events: Seq<global_layer::GlobalEvent>,
    event: global_layer::GlobalEvent,
)
    ensures pi_journal(events.push(event)) == match linearized_record(event) {
        Option::Some(record) => pi_journal(events).push(record),
        Option::None => pi_journal(events),
    },
{
    assert(events.push(event).drop_last() =~= events);
    assert(events.push(event).last() == event);
}

pub proof fn pi_physical_push(
    events: Seq<global_layer::GlobalEvent>,
    event: global_layer::GlobalEvent,
)
    ensures pi_physical(events.push(event)) == match physical_event(event) {
        Option::Some(physical) => pi_physical(events).push(physical),
        Option::None => pi_physical(events),
    },
{
    assert(events.push(event).drop_last() =~= events);
    assert(events.push(event).last() == event);
}

pub proof fn pi_ack_push(
    events: Seq<global_layer::GlobalEvent>,
    event: global_layer::GlobalEvent,
)
    ensures pi_ack(events.push(event)) == match event {
        global_layer::GlobalEvent::JournalAppendReturn { cut }
        | global_layer::GlobalEvent::WalFlushAck { cut } => {
            pi_ack(events).push(cut)
        },
        global_layer::GlobalEvent::BrokerLinearize { .. }
        | global_layer::GlobalEvent::JournalAppendCall { .. }
        | global_layer::GlobalEvent::JournalAppendLinearize { .. }
        | global_layer::GlobalEvent::JournalDiskFull { .. }
        | global_layer::GlobalEvent::WalStage { .. }
        | global_layer::GlobalEvent::WalWriteFull { .. }
        | global_layer::GlobalEvent::WalWriteTorn { .. }
        | global_layer::GlobalEvent::WalFinishTorn { .. }
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
        | global_layer::GlobalEvent::FinishRecover => pi_ack(events),
    },
{
    assert(events.push(event).drop_last() =~= events);
    assert(events.push(event).last() == event);
}

pub proof fn pi_append_io_push(
    events: Seq<global_layer::GlobalEvent>,
    event: global_layer::GlobalEvent,
)
    ensures pi_append_io(events.push(event))
        == append_io_after(pi_append_io(events), event),
{
    assert(events.push(event).drop_last() =~= events);
    assert(events.push(event).last() == event);
}

pub proof fn pi_control_push(
    events: Seq<global_layer::GlobalEvent>,
    event: global_layer::GlobalEvent,
)
    ensures pi_control(events.push(event)) == match event {
        selected @ global_layer::GlobalEvent::IgnoreStale { .. }
        | selected @ global_layer::GlobalEvent::RetryRelease { .. }
        | selected @ global_layer::GlobalEvent::Crash
        | selected @ global_layer::GlobalEvent::BeginRecover
        | selected @ global_layer::GlobalEvent::FinishRecover => {
            pi_control(events).push(selected)
        },
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
        | global_layer::GlobalEvent::BeginScan
        | global_layer::GlobalEvent::FinishScan
        | global_layer::GlobalEvent::TruncateTail
        | global_layer::GlobalEvent::AbortScan => pi_control(events),
    },
{
    assert(events.push(event).drop_last() =~= events);
    assert(events.push(event).last() == event);
}

pub proof fn pi_logical_push(
    events: Seq<global_layer::GlobalEvent>,
    event: global_layer::GlobalEvent,
)
    ensures pi_logical(events.push(event)) == logical_after(pi_logical(events), event),
{
    assert(events.push(event).drop_last() =~= events);
    assert(events.push(event).last() == event);
}

pub proof fn pi_wal_push(
    events: Seq<global_layer::GlobalEvent>,
    event: global_layer::GlobalEvent,
)
    ensures pi_wal(events.push(event)) == match event {
        selected @ global_layer::GlobalEvent::WalStage { .. }
        | selected @ global_layer::GlobalEvent::WalWriteFull { .. }
        | selected @ global_layer::GlobalEvent::WalWriteTorn { .. }
        | selected @ global_layer::GlobalEvent::WalFinishTorn { .. }
        | selected @ global_layer::GlobalEvent::WalFlushAck { .. }
        | selected @ global_layer::GlobalEvent::WalDiskFull { .. }
        | selected @ global_layer::GlobalEvent::Crash
        | selected @ global_layer::GlobalEvent::BeginScan
        | selected @ global_layer::GlobalEvent::FinishScan
        | selected @ global_layer::GlobalEvent::TruncateTail
        | selected @ global_layer::GlobalEvent::AbortScan
        | selected @ global_layer::GlobalEvent::BeginRecover
        | selected @ global_layer::GlobalEvent::FinishRecover => {
            pi_wal(events).push(selected)
        },
        global_layer::GlobalEvent::BrokerLinearize { .. }
        | global_layer::GlobalEvent::JournalAppendCall { .. }
        | global_layer::GlobalEvent::JournalAppendLinearize { .. }
        | global_layer::GlobalEvent::JournalAppendReturn { .. }
        | global_layer::GlobalEvent::JournalDiskFull { .. }
        | global_layer::GlobalEvent::InvokeEvent { .. }
        | global_layer::GlobalEvent::DeliverEvent { .. }
        | global_layer::GlobalEvent::IgnoreStale { .. }
        | global_layer::GlobalEvent::RetryRelease { .. } => pi_wal(events),
    },
{
    assert(events.push(event).drop_last() =~= events);
    assert(events.push(event).last() == event);
}

pub proof fn broker_encode_trace_push(
    events: Seq<p0_layer::Event>,
    event: p0_layer::Event,
)
    ensures broker_encode_trace(events.push(event))
        == broker_encode_trace(events).push(global_layer::broker_encode(event)),
{
    assert(events.push(event).drop_last() =~= events);
    assert(events.push(event).last() == event);
}

pub proof fn broker_encode_trace_len(events: Seq<p0_layer::Event>)
    ensures broker_encode_trace(events).len() == events.len(),
    decreases events.len(),
{
    if events.len() > 0 {
        broker_encode_trace_len(events.drop_last());
    }
}

pub proof fn broker_encode_trace_take(
    events: Seq<p0_layer::Event>,
    length: nat,
)
    requires length <= events.len(),
    ensures broker_encode_trace(events.take(length as int))
        == broker_encode_trace(events).take(length as int),
    decreases events.len() - length,
{
    if length == events.len() {
        assert(events.take(length as int) =~= events);
        broker_encode_trace_len(events);
        assert(broker_encode_trace(events).take(length as int)
            =~= broker_encode_trace(events));
    } else {
        assert(length < events.len());
        broker_encode_trace_take(events.drop_last(), length);
        broker_encode_trace_len(events.drop_last());
        assert(events.drop_last().take(length as int)
            =~= events.take(length as int));
        assert(broker_encode_trace(events).drop_last()
            =~= broker_encode_trace(events.drop_last()));
        assert(broker_encode_trace(events).take(length as int)
            =~= broker_encode_trace(events.drop_last()).take(length as int));
    }
}

pub proof fn global_append_project_push(
    events: Seq<global_layer::GlobalEvent>,
    event: global_layer::GlobalEvent,
)
    ensures global_append_project(events.push(event))
        == global_append_project(events).push(global_append_event(event)),
{
    assert(events.push(event).drop_last() =~= events);
    assert(events.push(event).last() == event);
}

pub proof fn global_append_project_len(
    events: Seq<global_layer::GlobalEvent>,
)
    ensures global_append_project(events).len() == events.len(),
    decreases events.len(),
{
    if events.len() > 0 {
        global_append_project_len(events.drop_last());
    }
}

pub proof fn global_append_project_take(
    events: Seq<global_layer::GlobalEvent>,
    length: nat,
)
    requires length <= events.len(),
    ensures global_append_project(events.take(length as int))
        == global_append_project(events).take(length as int),
    decreases events.len() - length,
{
    if length == events.len() {
        assert(events.take(length as int) =~= events);
        global_append_project_len(events);
        assert(global_append_project(events).take(length as int)
            =~= global_append_project(events));
    } else {
        assert(length < events.len());
        global_append_project_take(events.drop_last(), length);
        global_append_project_len(events.drop_last());
        assert(events.drop_last().take(length as int)
            =~= events.take(length as int));
        assert(global_append_project(events).drop_last()
            =~= global_append_project(events.drop_last()));
        assert(global_append_project(events).take(length as int)
            =~= global_append_project(events.drop_last()).take(length as int));
    }
}

pub proof fn encoded_global_append_event(event: p0_layer::Event)
    ensures global_append_event(global_layer::broker_encode(event))
        == bridge_layer::append_event(event),
{
    match event {
        p0_layer::Event::JournalAppendCall { .. }
        | p0_layer::Event::BrokerLinearize { .. }
        | p0_layer::Event::JournalAppendReturn { .. }
        | p0_layer::Event::JournalDiskFull { .. }
        | p0_layer::Event::InvokeEvent { .. }
        | p0_layer::Event::DeliverEvent { .. }
        | p0_layer::Event::IgnoreStale { .. }
        | p0_layer::Event::RetryRelease { .. }
        | p0_layer::Event::Crash
        | p0_layer::Event::BeginRecover
        | p0_layer::Event::FinishRecover => {},
    }
}

pub proof fn encoded_global_append_project(events: Seq<p0_layer::Event>)
    ensures global_append_project(broker_encode_trace(events))
        == bridge_layer::append_project(events),
    decreases events.len(),
{
    if events.len() > 0 {
        let prefix = events.drop_last();
        let event = events.last();
        encoded_global_append_project(prefix);
        broker_encode_trace_push(prefix, event);
        global_append_project_push(
            broker_encode_trace(prefix), global_layer::broker_encode(event),
        );
        bridge_layer::append_project_push(prefix, event);
        encoded_global_append_event(event);
        assert(prefix.push(event) =~= events);
    }
}

pub proof fn broker_decode_trace_push(
    events: Seq<global_layer::GlobalEvent>,
    event: global_layer::GlobalEvent,
)
    ensures broker_decode_trace(events.push(event))
        == match broker_decode_trace(events) {
            Option::None => Option::None,
            Option::Some(prefix) => match global_layer::broker_decode(event) {
                Option::None => Option::None,
                Option::Some(decoded) => Option::Some(prefix.push(decoded)),
            },
        },
{
    assert(events.push(event).drop_last() =~= events);
    assert(events.push(event).last() == event);
}

pub proof fn broker_decode_encode_trace_round_trip(
    events: Seq<p0_layer::Event>,
)
    ensures broker_decode_trace(broker_encode_trace(events))
        == Option::Some(events),
    decreases events.len(),
{
    if events.len() > 0 {
        let prefix = events.drop_last();
        let event = events.last();
        broker_decode_encode_trace_round_trip(prefix);
        broker_encode_trace_push(prefix, event);
        broker_decode_trace_push(
            broker_encode_trace(prefix),
            global_layer::broker_encode(event),
        );
        global_layer::broker_decode_encode_round_trip(event);
        assert(prefix.push(event) =~= events);
    }
}

pub proof fn broker_decode_trace_shape(
    events: Seq<global_layer::GlobalEvent>,
)
    ensures match broker_decode_trace(events) {
        Option::None => true,
        Option::Some(decoded) => {
            broker_encode_trace(decoded) == events
                && decoded.len() == events.len()
        },
    },
    decreases events.len(),
{
    if events.len() > 0 {
        let prefix = events.drop_last();
        let event = events.last();
        broker_decode_trace_shape(prefix);
        broker_decode_trace_push(prefix, event);
        match broker_decode_trace(prefix) {
            Option::None => {},
            Option::Some(decoded_prefix) => {
                match global_layer::broker_decode(event) {
                    Option::None => {},
                    Option::Some(decoded_event) => {
                        global_layer::broker_encode_decode_inverse(
                            event, decoded_event,
                        );
                        broker_encode_trace_push(decoded_prefix, decoded_event);
                        broker_encode_trace_len(decoded_prefix);
                        assert(prefix.push(event) =~= events);
                    },
                }
            },
        }
    }
}

pub proof fn broker_decode_trace_inverse(
    globals: Seq<global_layer::GlobalEvent>,
    locals: Seq<p0_layer::Event>,
)
    requires broker_decode_trace(globals) == Option::Some(locals),
    ensures
        broker_encode_trace(locals) == globals,
        locals.len() == globals.len(),
{
    broker_decode_trace_shape(globals);
}

pub proof fn broker_encode_trace_injective(
    left: Seq<p0_layer::Event>,
    right: Seq<p0_layer::Event>,
)
    requires broker_encode_trace(left) == broker_encode_trace(right),
    ensures left == right,
{
    broker_decode_encode_trace_round_trip(left);
    broker_decode_encode_trace_round_trip(right);
    assert(broker_decode_trace(broker_encode_trace(left))
        == broker_decode_trace(broker_encode_trace(right)));
}

pub proof fn broker_decode_trace_take(
    globals: Seq<global_layer::GlobalEvent>,
    locals: Seq<p0_layer::Event>,
    length: nat,
)
    requires
        broker_decode_trace(globals) == Option::Some(locals),
        length <= globals.len(),
    ensures broker_decode_trace(globals.take(length as int))
        == Option::Some(locals.take(length as int)),
{
    broker_decode_trace_inverse(globals, locals);
    assert(length <= locals.len());
    broker_encode_trace_take(locals, length);
    broker_decode_encode_trace_round_trip(locals.take(length as int));
}

pub proof fn broker_decode_trace_accepts_exactly(
    events: Seq<global_layer::GlobalEvent>,
)
    ensures broker_trace_decodable(events) <==> broker_trace_closed(events),
    decreases events.len(),
{
    if events.len() > 0 {
        let prefix = events.drop_last();
        let event = events.last();
        broker_decode_trace_accepts_exactly(prefix);
        broker_decode_trace_push(prefix, event);
        global_layer::broker_decode_accepts_exactly(event);
    }
}

pub proof fn broker_decode_trace_rejects_backend_push(
    events: Seq<global_layer::GlobalEvent>,
    event: global_layer::GlobalEvent,
)
    requires global_layer::backend_only_constructor(event),
    ensures broker_decode_trace(events.push(event)) == Option::None,
{
    global_layer::broker_decode_rejects_backend_only(event);
    broker_decode_trace_push(events, event);
}

// Projection correspondence for length-preserving embedded Broker traces.
pub proof fn encoded_pi_journal(events: Seq<p0_layer::Event>)
    ensures pi_journal(broker_encode_trace(events))
        == p0_layer::pi_journal(events),
    decreases events.len(),
{
    if events.len() > 0 {
        let prefix = events.drop_last();
        let event = events.last();
        encoded_pi_journal(prefix);
        broker_encode_trace_push(prefix, event);
        pi_journal_push(
            broker_encode_trace(prefix), global_layer::broker_encode(event),
        );
        p0_layer::pi_journal_push(prefix, event);
        assert(prefix.push(event) =~= events);
        match event {
            p0_layer::Event::JournalAppendCall { .. }
            | p0_layer::Event::BrokerLinearize { .. }
            | p0_layer::Event::JournalAppendReturn { .. }
            | p0_layer::Event::JournalDiskFull { .. }
            | p0_layer::Event::InvokeEvent { .. }
            | p0_layer::Event::DeliverEvent { .. }
            | p0_layer::Event::IgnoreStale { .. }
            | p0_layer::Event::RetryRelease { .. }
            | p0_layer::Event::Crash
            | p0_layer::Event::BeginRecover
            | p0_layer::Event::FinishRecover => {},
        }
    }
}

pub proof fn encoded_pi_physical(events: Seq<p0_layer::Event>)
    ensures pi_physical(broker_encode_trace(events))
        == p0_layer::pi_physical(events),
    decreases events.len(),
{
    if events.len() > 0 {
        let prefix = events.drop_last();
        let event = events.last();
        encoded_pi_physical(prefix);
        broker_encode_trace_push(prefix, event);
        pi_physical_push(
            broker_encode_trace(prefix), global_layer::broker_encode(event),
        );
        p0_layer::pi_physical_push(prefix, event);
        assert(prefix.push(event) =~= events);
        match event {
            p0_layer::Event::JournalAppendCall { .. }
            | p0_layer::Event::BrokerLinearize { .. }
            | p0_layer::Event::JournalAppendReturn { .. }
            | p0_layer::Event::JournalDiskFull { .. }
            | p0_layer::Event::InvokeEvent { .. }
            | p0_layer::Event::DeliverEvent { .. }
            | p0_layer::Event::IgnoreStale { .. }
            | p0_layer::Event::RetryRelease { .. }
            | p0_layer::Event::Crash
            | p0_layer::Event::BeginRecover
            | p0_layer::Event::FinishRecover => {},
        }
    }
}

pub proof fn encoded_pi_ack(events: Seq<p0_layer::Event>)
    ensures pi_ack(broker_encode_trace(events)) == p0_layer::pi_ack(events),
    decreases events.len(),
{
    if events.len() > 0 {
        let prefix = events.drop_last();
        let event = events.last();
        encoded_pi_ack(prefix);
        broker_encode_trace_push(prefix, event);
        pi_ack_push(
            broker_encode_trace(prefix), global_layer::broker_encode(event),
        );
        p0_layer::pi_ack_push(prefix, event);
        assert(prefix.push(event) =~= events);
        match event {
            p0_layer::Event::JournalAppendCall { .. }
            | p0_layer::Event::BrokerLinearize { .. }
            | p0_layer::Event::JournalAppendReturn { .. }
            | p0_layer::Event::JournalDiskFull { .. }
            | p0_layer::Event::InvokeEvent { .. }
            | p0_layer::Event::DeliverEvent { .. }
            | p0_layer::Event::IgnoreStale { .. }
            | p0_layer::Event::RetryRelease { .. }
            | p0_layer::Event::Crash
            | p0_layer::Event::BeginRecover
            | p0_layer::Event::FinishRecover => {},
        }
    }
}

pub proof fn encoded_pi_append(events: Seq<p0_layer::Event>)
    ensures pi_append(broker_encode_trace(events))
        == bridge_layer::broker_pi_append(events),
    decreases events.len(),
{
    if events.len() > 0 {
        let prefix = events.drop_last();
        let event = events.last();
        encoded_pi_append(prefix);
        broker_encode_trace_push(prefix, event);
        pi_append_push(
            broker_encode_trace(prefix), global_layer::broker_encode(event),
        );
        bridge_layer::append_project_push(prefix, event);
        append_layer::pi_append_push(
            bridge_layer::append_project(prefix),
            bridge_layer::append_event(event),
        );
        assert(prefix.push(event) =~= events);
        match event {
            p0_layer::Event::JournalAppendCall { .. }
            | p0_layer::Event::BrokerLinearize { .. }
            | p0_layer::Event::JournalAppendReturn { .. }
            | p0_layer::Event::JournalDiskFull { .. }
            | p0_layer::Event::InvokeEvent { .. }
            | p0_layer::Event::DeliverEvent { .. }
            | p0_layer::Event::IgnoreStale { .. }
            | p0_layer::Event::RetryRelease { .. }
            | p0_layer::Event::Crash
            | p0_layer::Event::BeginRecover
            | p0_layer::Event::FinishRecover => {},
        }
    }
}

pub open spec fn erase_append_linearize(
    events: Seq<append_layer::AppendEvent<replay_layer::JournalRecord>>,
) -> Seq<append_layer::AppendEvent<replay_layer::JournalRecord>>
    decreases events.len()
{
    if events.len() == 0 {
        Seq::empty()
    } else {
        let prefix = erase_append_linearize(events.drop_last());
        match events.last() {
            append_layer::AppendEvent::Call { record } => {
                prefix.push(append_layer::AppendEvent::Call { record })
            },
            append_layer::AppendEvent::Linearize { .. } => prefix,
            append_layer::AppendEvent::Return { result, cut } => {
                prefix.push(append_layer::AppendEvent::Return { result, cut })
            },
        }
    }
}

pub proof fn erase_append_linearize_push(
    events: Seq<append_layer::AppendEvent<replay_layer::JournalRecord>>,
    event: append_layer::AppendEvent<replay_layer::JournalRecord>,
)
    ensures erase_append_linearize(events.push(event)) == match event {
        append_layer::AppendEvent::Call { record } => {
            erase_append_linearize(events).push(
                append_layer::AppendEvent::Call { record },
            )
        },
        append_layer::AppendEvent::Linearize { .. } => {
            erase_append_linearize(events)
        },
        append_layer::AppendEvent::Return { result, cut } => {
            erase_append_linearize(events).push(
                append_layer::AppendEvent::Return { result, cut },
            )
        },
    },
{
    assert(events.push(event).drop_last() =~= events);
    assert(events.push(event).last() == event);
}

pub proof fn pi_append_io_is_erased_append(
    events: Seq<global_layer::GlobalEvent>,
)
    ensures pi_append_io(events) == erase_append_linearize(pi_append(events)),
    decreases events.len(),
{
    if events.len() > 0 {
        let prefix = events.drop_last();
        let event = events.last();
        pi_append_io_is_erased_append(prefix);
        pi_append_push(prefix, event);
        pi_append_io_push(prefix, event);
        assert(prefix.push(event) =~= events);
        match event {
            global_layer::GlobalEvent::JournalAppendCall { record }
            | global_layer::GlobalEvent::WalStage { record } => {
                erase_append_linearize_push(
                    pi_append(prefix),
                    append_layer::AppendEvent::Call { record },
                );
            },
            global_layer::GlobalEvent::BrokerLinearize { record }
            | global_layer::GlobalEvent::JournalAppendLinearize { record }
            | global_layer::GlobalEvent::WalWriteFull { record }
            | global_layer::GlobalEvent::WalFinishTorn { record } => {
                erase_append_linearize_push(
                    pi_append(prefix),
                    append_layer::AppendEvent::Linearize { record },
                );
            },
            global_layer::GlobalEvent::JournalAppendReturn { cut }
            | global_layer::GlobalEvent::WalFlushAck { cut } => {
                erase_append_linearize_push(
                    pi_append(prefix),
                    append_layer::AppendEvent::Return {
                        result: append_layer::AppendResult::Ok, cut,
                    },
                );
            },
            global_layer::GlobalEvent::JournalDiskFull { record, cut }
            | global_layer::GlobalEvent::WalDiskFull { record, cut } => {
                let called = pi_append(prefix).push(
                    append_layer::AppendEvent::Call { record },
                );
                erase_append_linearize_push(
                    pi_append(prefix),
                    append_layer::AppendEvent::Call { record },
                );
                erase_append_linearize_push(
                    called,
                    append_layer::AppendEvent::Return {
                        result: append_layer::AppendResult::Full, cut,
                    },
                );
            },
            global_layer::GlobalEvent::WalWriteTorn { .. }
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

pub proof fn encoded_pi_append_io(events: Seq<p0_layer::Event>)
    ensures pi_append_io(broker_encode_trace(events))
        == erase_append_linearize(bridge_layer::broker_pi_append(events)),
{
    pi_append_io_is_erased_append(broker_encode_trace(events));
    encoded_pi_append(events);
}

pub proof fn logical_records_push(
    records: Seq<replay_layer::JournalRecord>,
    record: replay_layer::JournalRecord,
)
    ensures logical_records(records.push(record)) == match logical_record(record) {
        Option::Some(event) => logical_records(records).push(event),
        Option::None => logical_records(records),
    },
{
    assert(records.push(record).drop_last() =~= records);
    assert(records.push(record).last() == record);
}

pub proof fn pi_logical_is_journal_projection(
    events: Seq<global_layer::GlobalEvent>,
)
    ensures pi_logical(events) == logical_records(pi_journal(events)),
    decreases events.len(),
{
    if events.len() > 0 {
        let prefix = events.drop_last();
        let event = events.last();
        pi_logical_is_journal_projection(prefix);
        pi_logical_push(prefix, event);
        pi_journal_push(prefix, event);
        assert(prefix.push(event) =~= events);
        match event {
            global_layer::GlobalEvent::BrokerLinearize { record }
            | global_layer::GlobalEvent::JournalAppendLinearize { record }
            | global_layer::GlobalEvent::WalWriteFull { record }
            | global_layer::GlobalEvent::WalFinishTorn { record } => {
                logical_records_push(pi_journal(prefix), record);
            },
            global_layer::GlobalEvent::JournalAppendCall { .. }
            | global_layer::GlobalEvent::JournalAppendReturn { .. }
            | global_layer::GlobalEvent::JournalDiskFull { .. }
            | global_layer::GlobalEvent::WalStage { .. }
            | global_layer::GlobalEvent::WalWriteTorn { .. }
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

pub proof fn encoded_pi_logical(events: Seq<p0_layer::Event>)
    ensures pi_logical(broker_encode_trace(events))
        == logical_records(p0_layer::pi_journal(events)),
{
    pi_logical_is_journal_projection(broker_encode_trace(events));
    encoded_pi_journal(events);
}

pub proof fn encoded_pi_control(events: Seq<p0_layer::Event>)
    ensures pi_control(broker_encode_trace(events)) == broker_pi_control(events),
    decreases events.len(),
{
    if events.len() > 0 {
        let prefix = events.drop_last();
        let event = events.last();
        encoded_pi_control(prefix);
        broker_encode_trace_push(prefix, event);
        pi_control_push(
            broker_encode_trace(prefix), global_layer::broker_encode(event),
        );
        assert(prefix.push(event) =~= events);
        match event {
            p0_layer::Event::JournalAppendCall { .. }
            | p0_layer::Event::BrokerLinearize { .. }
            | p0_layer::Event::JournalAppendReturn { .. }
            | p0_layer::Event::JournalDiskFull { .. }
            | p0_layer::Event::InvokeEvent { .. }
            | p0_layer::Event::DeliverEvent { .. }
            | p0_layer::Event::IgnoreStale { .. }
            | p0_layer::Event::RetryRelease { .. }
            | p0_layer::Event::Crash
            | p0_layer::Event::BeginRecover
            | p0_layer::Event::FinishRecover => {},
        }
    }
}

pub proof fn encoded_pi_wal(events: Seq<p0_layer::Event>)
    ensures pi_wal(broker_encode_trace(events)) == broker_pi_wal_boundary(events),
    decreases events.len(),
{
    if events.len() > 0 {
        let prefix = events.drop_last();
        let event = events.last();
        encoded_pi_wal(prefix);
        broker_encode_trace_push(prefix, event);
        pi_wal_push(
            broker_encode_trace(prefix), global_layer::broker_encode(event),
        );
        assert(prefix.push(event) =~= events);
        match event {
            p0_layer::Event::JournalAppendCall { .. }
            | p0_layer::Event::BrokerLinearize { .. }
            | p0_layer::Event::JournalAppendReturn { .. }
            | p0_layer::Event::JournalDiskFull { .. }
            | p0_layer::Event::InvokeEvent { .. }
            | p0_layer::Event::DeliverEvent { .. }
            | p0_layer::Event::IgnoreStale { .. }
            | p0_layer::Event::RetryRelease { .. }
            | p0_layer::Event::Crash
            | p0_layer::Event::BeginRecover
            | p0_layer::Event::FinishRecover => {},
        }
    }
}

pub proof fn global_current_epoch_io_push(
    events: Seq<global_layer::GlobalEvent>,
    event: global_layer::GlobalEvent,
)
    ensures global_current_epoch_io(events.push(event))
        == global_epoch_io_after(global_current_epoch_io(events), event),
{
    assert(events.push(event).drop_last() =~= events);
    assert(events.push(event).last() == event);
}

pub proof fn broker_current_epoch_io_push(
    events: Seq<p0_layer::Event>,
    event: p0_layer::Event,
)
    ensures bridge_layer::current_epoch_io(events.push(event))
        == bridge_layer::epoch_io_after(
            bridge_layer::current_epoch_io(events),
            bridge_layer::append_event(event),
        ),
{
    assert(events.push(event).drop_last() =~= events);
    assert(events.push(event).last() == event);
}

pub proof fn global_crash_free_push(
    events: Seq<global_layer::GlobalEvent>,
    event: global_layer::GlobalEvent,
)
    ensures global_crash_free(events.push(event))
        == (global_crash_free(events)
            && match event {
                global_layer::GlobalEvent::Crash => false,
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
                | global_layer::GlobalEvent::BeginScan
                | global_layer::GlobalEvent::FinishScan
                | global_layer::GlobalEvent::TruncateTail
                | global_layer::GlobalEvent::AbortScan
                | global_layer::GlobalEvent::BeginRecover
                | global_layer::GlobalEvent::FinishRecover => true,
            }),
{
    assert(events.push(event).drop_last() =~= events);
    assert(events.push(event).last() == event);
}

pub proof fn broker_crash_free_push(
    events: Seq<p0_layer::Event>,
    event: p0_layer::Event,
)
    ensures bridge_layer::crash_free(events.push(event))
        == (bridge_layer::crash_free(events)
            && match event {
                p0_layer::Event::Crash => false,
                p0_layer::Event::JournalAppendCall { .. }
                | p0_layer::Event::BrokerLinearize { .. }
                | p0_layer::Event::JournalAppendReturn { .. }
                | p0_layer::Event::JournalDiskFull { .. }
                | p0_layer::Event::InvokeEvent { .. }
                | p0_layer::Event::DeliverEvent { .. }
                | p0_layer::Event::IgnoreStale { .. }
                | p0_layer::Event::RetryRelease { .. }
                | p0_layer::Event::BeginRecover
                | p0_layer::Event::FinishRecover => true,
            }),
{
    assert(events.push(event).drop_last() =~= events);
    assert(events.push(event).last() == event);
}

pub proof fn encoded_current_epoch_io(events: Seq<p0_layer::Event>)
    ensures global_current_epoch_io(broker_encode_trace(events))
        == bridge_layer::current_epoch_io(events),
    decreases events.len(),
{
    if events.len() > 0 {
        let prefix = events.drop_last();
        let event = events.last();
        encoded_current_epoch_io(prefix);
        broker_encode_trace_push(prefix, event);
        global_current_epoch_io_push(
            broker_encode_trace(prefix), global_layer::broker_encode(event),
        );
        broker_current_epoch_io_push(prefix, event);
        assert(prefix.push(event) =~= events);
        match event {
            p0_layer::Event::JournalAppendCall { .. }
            | p0_layer::Event::BrokerLinearize { .. }
            | p0_layer::Event::JournalAppendReturn { .. }
            | p0_layer::Event::JournalDiskFull { .. }
            | p0_layer::Event::InvokeEvent { .. }
            | p0_layer::Event::DeliverEvent { .. }
            | p0_layer::Event::IgnoreStale { .. }
            | p0_layer::Event::RetryRelease { .. }
            | p0_layer::Event::Crash
            | p0_layer::Event::BeginRecover
            | p0_layer::Event::FinishRecover => {},
        }
    }
}

pub proof fn encoded_crash_free(events: Seq<p0_layer::Event>)
    ensures global_crash_free(broker_encode_trace(events))
        == bridge_layer::crash_free(events),
    decreases events.len(),
{
    if events.len() > 0 {
        let prefix = events.drop_last();
        let event = events.last();
        encoded_crash_free(prefix);
        broker_encode_trace_push(prefix, event);
        global_crash_free_push(
            broker_encode_trace(prefix), global_layer::broker_encode(event),
        );
        broker_crash_free_push(prefix, event);
        assert(prefix.push(event) =~= events);
        match event {
            p0_layer::Event::JournalAppendCall { .. }
            | p0_layer::Event::BrokerLinearize { .. }
            | p0_layer::Event::JournalAppendReturn { .. }
            | p0_layer::Event::JournalDiskFull { .. }
            | p0_layer::Event::InvokeEvent { .. }
            | p0_layer::Event::DeliverEvent { .. }
            | p0_layer::Event::IgnoreStale { .. }
            | p0_layer::Event::RetryRelease { .. }
            | p0_layer::Event::Crash
            | p0_layer::Event::BeginRecover
            | p0_layer::Event::FinishRecover => {},
        }
    }
}

// A successful decode supplies the exact local trace and therefore all local
// projection correspondences without a filter-map or a separate prefix map.
pub proof fn decoded_broker_projection_agreement(
    globals: Seq<global_layer::GlobalEvent>,
    locals: Seq<p0_layer::Event>,
)
    requires broker_decode_trace(globals) == Option::Some(locals),
    ensures
        globals == broker_encode_trace(locals),
        globals.len() == locals.len(),
        pi_append(globals) == bridge_layer::broker_pi_append(locals),
        pi_journal(globals) == p0_layer::pi_journal(locals),
        pi_physical(globals) == p0_layer::pi_physical(locals),
        pi_ack(globals) == p0_layer::pi_ack(locals),
        pi_append_io(globals)
            == erase_append_linearize(bridge_layer::broker_pi_append(locals)),
        pi_control(globals) == broker_pi_control(locals),
        pi_logical(globals) == logical_records(p0_layer::pi_journal(locals)),
        pi_wal(globals) == broker_pi_wal_boundary(locals),
        pi_auth(globals) == auth_records(p0_layer::pi_journal(locals)),
        pi_invocations(globals)
            == invocations_from_physical(p0_layer::pi_physical(locals)),
        forall|request: replay_layer::RequestId|
            #[trigger] pi_adapter(globals, request)
                == adapter_from_physical(
                    p0_layer::pi_physical(locals), request,
                ),
        global_current_epoch_io(globals)
            == bridge_layer::current_epoch_io(locals),
        global_crash_free(globals) == bridge_layer::crash_free(locals),
{
    broker_decode_trace_inverse(globals, locals);
    encoded_pi_append(locals);
    encoded_pi_journal(locals);
    encoded_pi_physical(locals);
    encoded_pi_ack(locals);
    encoded_pi_append_io(locals);
    encoded_pi_control(locals);
    encoded_pi_logical(locals);
    encoded_pi_wal(locals);
    encoded_pi_auth(locals);
    encoded_pi_invocations(locals);
    assert forall|request: replay_layer::RequestId|
        #[trigger] pi_adapter(globals, request)
            == adapter_from_physical(p0_layer::pi_physical(locals), request) by {
        encoded_pi_adapter(locals, request);
    }
    encoded_current_epoch_io(locals);
    encoded_crash_free(locals);
}

// Additional Section 6 derived projections.  They are expressed through the
// already verified journal/physical projections, keeping one source of event
// ordering while exposing the exact interfaces needed by later refinement
// theorems.

#[derive(PartialEq, Eq)]
pub enum AuthEvent {
    Authorize {
        request: replay_layer::RequestId,
        capability: replay_layer::CapabilityId,
    },
    Revoke {
        capability: replay_layer::CapabilityId,
    },
}

#[derive(PartialEq, Eq)]
pub struct ProtectedInvocation {
    pub request: replay_layer::RequestId,
    pub attempt: replay_layer::AttemptId,
    pub call: config_layer::CallDescriptor,
}

pub open spec fn auth_record(
    record: replay_layer::JournalRecord,
) -> Option<AuthEvent> {
    match record {
        replay_layer::JournalRecord::Authorize {
            request, capability, ..
        } => Option::Some(AuthEvent::Authorize { request, capability }),
        replay_layer::JournalRecord::Revoke { capability } => {
            Option::Some(AuthEvent::Revoke { capability })
        },
        replay_layer::JournalRecord::Prepare { .. }
        | replay_layer::JournalRecord::Arm { .. }
        | replay_layer::JournalRecord::Start { .. }
        | replay_layer::JournalRecord::Outcome { .. }
        | replay_layer::JournalRecord::CommitRec { .. }
        | replay_layer::JournalRecord::FailRec { .. }
        | replay_layer::JournalRecord::UnknownRec { .. } => Option::None,
    }
}

pub open spec fn auth_records(
    records: Seq<replay_layer::JournalRecord>,
) -> Seq<AuthEvent>
    decreases records.len()
{
    if records.len() == 0 {
        Seq::empty()
    } else {
        let prefix = auth_records(records.drop_last());
        match auth_record(records.last()) {
            Option::Some(event) => prefix.push(event),
            Option::None => prefix,
        }
    }
}

pub open spec fn pi_auth(
    events: Seq<global_layer::GlobalEvent>,
) -> Seq<AuthEvent> {
    auth_records(pi_journal(events))
}

pub open spec fn invocations_from_physical(
    events: Seq<p0_layer::PhysicalEvent>,
) -> Seq<ProtectedInvocation>
    decreases events.len()
{
    if events.len() == 0 {
        Seq::empty()
    } else {
        let prefix = invocations_from_physical(events.drop_last());
        match events.last() {
            p0_layer::PhysicalEvent::Invoke {
                request, attempt, call, ..
            } => prefix.push(ProtectedInvocation { request, attempt, call }),
            p0_layer::PhysicalEvent::Delivered { .. } => prefix,
        }
    }
}

pub open spec fn adapter_from_physical(
    events: Seq<p0_layer::PhysicalEvent>,
    request: replay_layer::RequestId,
) -> Seq<p0_layer::PhysicalEvent>
    decreases events.len()
{
    if events.len() == 0 {
        Seq::empty()
    } else {
        let prefix = adapter_from_physical(events.drop_last(), request);
        match events.last() {
            event @ p0_layer::PhysicalEvent::Invoke {
                request: event_request, ..
            } => {
                if event_request == request { prefix.push(event) } else { prefix }
            },
            event @ p0_layer::PhysicalEvent::Delivered {
                request: event_request, ..
            } => {
                if event_request == request { prefix.push(event) } else { prefix }
            },
        }
    }
}

pub open spec fn pi_invocations(
    events: Seq<global_layer::GlobalEvent>,
) -> Seq<ProtectedInvocation> {
    invocations_from_physical(pi_physical(events))
}

pub open spec fn pi_adapter(
    events: Seq<global_layer::GlobalEvent>,
    request: replay_layer::RequestId,
) -> Seq<p0_layer::PhysicalEvent> {
    adapter_from_physical(pi_physical(events), request)
}

pub open spec fn complete_mediation(
    events: Seq<global_layer::GlobalEvent>,
    protected: Seq<ProtectedInvocation>,
) -> bool {
    protected == pi_invocations(events)
}

pub proof fn encoded_pi_auth(events: Seq<p0_layer::Event>)
    ensures pi_auth(broker_encode_trace(events))
        == auth_records(p0_layer::pi_journal(events)),
{
    encoded_pi_journal(events);
}

pub proof fn encoded_pi_invocations(events: Seq<p0_layer::Event>)
    ensures pi_invocations(broker_encode_trace(events))
        == invocations_from_physical(p0_layer::pi_physical(events)),
{
    encoded_pi_physical(events);
}

pub proof fn encoded_pi_adapter(
    events: Seq<p0_layer::Event>,
    request: replay_layer::RequestId,
)
    ensures pi_adapter(broker_encode_trace(events), request)
        == adapter_from_physical(p0_layer::pi_physical(events), request),
{
    encoded_pi_physical(events);
}

pub open spec fn successful_return_cut(
    event: global_layer::GlobalEvent,
) -> Option<nat> {
    match event {
        global_layer::GlobalEvent::JournalAppendReturn { cut }
        | global_layer::GlobalEvent::WalFlushAck { cut } => Option::Some(cut),
        global_layer::GlobalEvent::BrokerLinearize { .. }
        | global_layer::GlobalEvent::JournalAppendCall { .. }
        | global_layer::GlobalEvent::JournalAppendLinearize { .. }
        | global_layer::GlobalEvent::JournalDiskFull { .. }
        | global_layer::GlobalEvent::WalStage { .. }
        | global_layer::GlobalEvent::WalWriteFull { .. }
        | global_layer::GlobalEvent::WalWriteTorn { .. }
        | global_layer::GlobalEvent::WalFinishTorn { .. }
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
        | global_layer::GlobalEvent::FinishRecover => Option::None,
    }
}

// Every projected acknowledgment has an actual successful-return source in
// the original trace.  Applying this lemma to the prefix before an Invoke
// supplies the temporal "prior return" witness used by ack_cut reasoning.
pub proof fn pi_ack_has_successful_return_source(
    events: Seq<global_layer::GlobalEvent>,
    ack_index: int,
)
    requires 0 <= ack_index < pi_ack(events).len(),
    ensures exists|event_index: int|
        0 <= event_index < events.len()
            && #[trigger] successful_return_cut(events[event_index])
                == Option::Some(pi_ack(events)[ack_index]),
    decreases events.len(),
{
    assert(events.len() > 0);
    let prefix = events.drop_last();
    let event = events.last();
    pi_ack_push(prefix, event);
    assert(prefix.push(event) =~= events);
    match event {
        global_layer::GlobalEvent::JournalAppendReturn { cut }
        | global_layer::GlobalEvent::WalFlushAck { cut } => {
            if ack_index < pi_ack(prefix).len() {
                pi_ack_has_successful_return_source(prefix, ack_index);
                let source = choose|source: int|
                    0 <= source < prefix.len()
                        && #[trigger] successful_return_cut(prefix[source])
                            == Option::Some(pi_ack(prefix)[ack_index]);
                assert(prefix[source] == events[source]);
                assert(pi_ack(events)[ack_index] == pi_ack(prefix)[ack_index]);
                assert(exists|event_index: int|
                    0 <= event_index < events.len()
                        && #[trigger] successful_return_cut(events[event_index])
                            == Option::Some(pi_ack(events)[ack_index])) by {
                    assert(0 <= source < events.len());
                    assert(successful_return_cut(events[source])
                        == Option::Some(pi_ack(events)[ack_index]));
                }
            } else {
                assert(ack_index == pi_ack(prefix).len());
                let source = events.len() as int - 1;
                assert(0 <= source < events.len());
                assert(events[source] == event);
                assert(pi_ack(events)[ack_index] == cut);
                assert(exists|event_index: int|
                    0 <= event_index < events.len()
                        && #[trigger] successful_return_cut(events[event_index])
                            == Option::Some(pi_ack(events)[ack_index])) by {
                    assert(successful_return_cut(events[source])
                        == Option::Some(pi_ack(events)[ack_index]));
                }
            }
        },
        global_layer::GlobalEvent::BrokerLinearize { .. }
        | global_layer::GlobalEvent::JournalAppendCall { .. }
        | global_layer::GlobalEvent::JournalAppendLinearize { .. }
        | global_layer::GlobalEvent::JournalDiskFull { .. }
        | global_layer::GlobalEvent::WalStage { .. }
        | global_layer::GlobalEvent::WalWriteFull { .. }
        | global_layer::GlobalEvent::WalWriteTorn { .. }
        | global_layer::GlobalEvent::WalFinishTorn { .. }
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
        | global_layer::GlobalEvent::FinishRecover => {
            pi_ack_has_successful_return_source(prefix, ack_index);
            let source = choose|source: int|
                0 <= source < prefix.len()
                    && #[trigger] successful_return_cut(prefix[source])
                        == Option::Some(pi_ack(prefix)[ack_index]);
            assert(prefix[source] == events[source]);
            assert(pi_ack(events) == pi_ack(prefix));
            assert(exists|event_index: int|
                0 <= event_index < events.len()
                    && #[trigger] successful_return_cut(events[event_index])
                        == Option::Some(pi_ack(events)[ack_index])) by {
                assert(0 <= source < events.len());
                assert(successful_return_cut(events[source])
                    == Option::Some(pi_ack(events)[ack_index]));
            }
        },
    }
}

} // verus!
