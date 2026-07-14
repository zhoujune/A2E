use vstd::prelude::*;

#[path = "t1_broker_append_bridge.rs"]
pub mod bridge_layer;

verus! {

use bridge_layer::contract_layer::p3_layer::p2_layer::p1_layer::p0_layer;
use p0_layer::config_layer;
use config_layer::broker_layer as record_layer;
use record_layer::query_layer::c1_layer;
use c1_layer::replay_layer;

// G0 closes the local Broker proof over the paper's single, normative event
// alphabet.  This datatype deliberately contains the Broker labels, the
// atomic-Journal-only linearization label, and all WAL/scan backend labels.
// The exhaustive decoder below is therefore also the machine-checked closure
// boundary for BrokerStep.

#[allow(inconsistent_fields)]
#[derive(PartialEq, Eq)]
pub enum GlobalEvent {
    BrokerLinearize {
        record: replay_layer::JournalRecord,
    },
    JournalAppendCall {
        record: replay_layer::JournalRecord,
    },
    JournalAppendLinearize {
        record: replay_layer::JournalRecord,
    },
    JournalAppendReturn {
        cut: nat,
    },
    JournalDiskFull {
        record: replay_layer::JournalRecord,
        cut: nat,
    },
    WalStage {
        record: replay_layer::JournalRecord,
    },
    WalWriteFull {
        record: replay_layer::JournalRecord,
    },
    WalWriteTorn {
        record: replay_layer::JournalRecord,
    },
    WalFinishTorn {
        record: replay_layer::JournalRecord,
    },
    WalFlushAck {
        cut: nat,
    },
    WalDiskFull {
        record: replay_layer::JournalRecord,
        cut: nat,
    },
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
    RetryRelease {
        request: replay_layer::RequestId,
    },
    Crash,
    BeginScan,
    FinishScan,
    TruncateTail,
    AbortScan,
    BeginRecover,
    FinishRecover,
}

// Keep the paper's short name available without creating a second datatype.
pub type Event = GlobalEvent;

// Exactly the eleven constructors in the Broker row of the event-closure
// table decode to local Broker events.  Each backend-only constructor has its
// own explicit rejecting arm; there is intentionally no catch-all pattern.
pub open spec fn broker_decode(event: GlobalEvent) -> Option<p0_layer::Event> {
    match event {
        GlobalEvent::BrokerLinearize { record } => Option::Some(
            p0_layer::Event::BrokerLinearize { record },
        ),
        GlobalEvent::JournalAppendCall { record } => Option::Some(
            p0_layer::Event::JournalAppendCall { record },
        ),
        GlobalEvent::JournalAppendLinearize { record: _ } => Option::None,
        GlobalEvent::JournalAppendReturn { cut } => Option::Some(
            p0_layer::Event::JournalAppendReturn { cut },
        ),
        GlobalEvent::JournalDiskFull { record, cut } => Option::Some(
            p0_layer::Event::JournalDiskFull { record, cut },
        ),
        GlobalEvent::WalStage { record: _ } => Option::None,
        GlobalEvent::WalWriteFull { record: _ } => Option::None,
        GlobalEvent::WalWriteTorn { record: _ } => Option::None,
        GlobalEvent::WalFinishTorn { record: _ } => Option::None,
        GlobalEvent::WalFlushAck { cut: _ } => Option::None,
        GlobalEvent::WalDiskFull { record: _, cut: _ } => Option::None,
        GlobalEvent::InvokeEvent {
            request, attempt, call, journal_cut, ack_cut,
        } => Option::Some(p0_layer::Event::InvokeEvent {
            request, attempt, call, journal_cut, ack_cut,
        }),
        GlobalEvent::DeliverEvent {
            request, attempt, observation, journal_cut,
        } => Option::Some(p0_layer::Event::DeliverEvent {
            request, attempt, observation, journal_cut,
        }),
        GlobalEvent::IgnoreStale { request, attempt } => Option::Some(
            p0_layer::Event::IgnoreStale { request, attempt },
        ),
        GlobalEvent::RetryRelease { request } => Option::Some(
            p0_layer::Event::RetryRelease { request },
        ),
        GlobalEvent::Crash => Option::Some(p0_layer::Event::Crash),
        GlobalEvent::BeginScan => Option::None,
        GlobalEvent::FinishScan => Option::None,
        GlobalEvent::TruncateTail => Option::None,
        GlobalEvent::AbortScan => Option::None,
        GlobalEvent::BeginRecover => Option::Some(p0_layer::Event::BeginRecover),
        GlobalEvent::FinishRecover => Option::Some(p0_layer::Event::FinishRecover),
    }
}

// The total embedding is the inverse of broker_decode on the accepted image.
pub open spec fn broker_encode(event: p0_layer::Event) -> GlobalEvent {
    match event {
        p0_layer::Event::JournalAppendCall { record } => {
            GlobalEvent::JournalAppendCall { record }
        },
        p0_layer::Event::BrokerLinearize { record } => {
            GlobalEvent::BrokerLinearize { record }
        },
        p0_layer::Event::JournalAppendReturn { cut } => {
            GlobalEvent::JournalAppendReturn { cut }
        },
        p0_layer::Event::JournalDiskFull { record, cut } => {
            GlobalEvent::JournalDiskFull { record, cut }
        },
        p0_layer::Event::InvokeEvent {
            request, attempt, call, journal_cut, ack_cut,
        } => GlobalEvent::InvokeEvent {
            request, attempt, call, journal_cut, ack_cut,
        },
        p0_layer::Event::DeliverEvent {
            request, attempt, observation, journal_cut,
        } => GlobalEvent::DeliverEvent {
            request, attempt, observation, journal_cut,
        },
        p0_layer::Event::IgnoreStale { request, attempt } => {
            GlobalEvent::IgnoreStale { request, attempt }
        },
        p0_layer::Event::RetryRelease { request } => {
            GlobalEvent::RetryRelease { request }
        },
        p0_layer::Event::Crash => GlobalEvent::Crash,
        p0_layer::Event::BeginRecover => GlobalEvent::BeginRecover,
        p0_layer::Event::FinishRecover => GlobalEvent::FinishRecover,
    }
}

// Syntactic classifiers are kept independent of broker_decode.  Their exact
// correspondence below prevents a future constructor from being accepted (or
// rejected) merely because a permissive decoder pattern happened to match it.
pub open spec fn broker_constructor(event: GlobalEvent) -> bool {
    match event {
        GlobalEvent::BrokerLinearize { record: _ } => true,
        GlobalEvent::JournalAppendCall { record: _ } => true,
        GlobalEvent::JournalAppendLinearize { record: _ } => false,
        GlobalEvent::JournalAppendReturn { cut: _ } => true,
        GlobalEvent::JournalDiskFull { record: _, cut: _ } => true,
        GlobalEvent::WalStage { record: _ } => false,
        GlobalEvent::WalWriteFull { record: _ } => false,
        GlobalEvent::WalWriteTorn { record: _ } => false,
        GlobalEvent::WalFinishTorn { record: _ } => false,
        GlobalEvent::WalFlushAck { cut: _ } => false,
        GlobalEvent::WalDiskFull { record: _, cut: _ } => false,
        GlobalEvent::InvokeEvent {
            request: _, attempt: _, call: _, journal_cut: _, ack_cut: _,
        } => true,
        GlobalEvent::DeliverEvent {
            request: _, attempt: _, observation: _, journal_cut: _,
        } => true,
        GlobalEvent::IgnoreStale { request: _, attempt: _ } => true,
        GlobalEvent::RetryRelease { request: _ } => true,
        GlobalEvent::Crash => true,
        GlobalEvent::BeginScan => false,
        GlobalEvent::FinishScan => false,
        GlobalEvent::TruncateTail => false,
        GlobalEvent::AbortScan => false,
        GlobalEvent::BeginRecover => true,
        GlobalEvent::FinishRecover => true,
    }
}

pub open spec fn backend_only_constructor(event: GlobalEvent) -> bool {
    match event {
        GlobalEvent::BrokerLinearize { record: _ } => false,
        GlobalEvent::JournalAppendCall { record: _ } => false,
        GlobalEvent::JournalAppendLinearize { record: _ } => true,
        GlobalEvent::JournalAppendReturn { cut: _ } => false,
        GlobalEvent::JournalDiskFull { record: _, cut: _ } => false,
        GlobalEvent::WalStage { record: _ } => true,
        GlobalEvent::WalWriteFull { record: _ } => true,
        GlobalEvent::WalWriteTorn { record: _ } => true,
        GlobalEvent::WalFinishTorn { record: _ } => true,
        GlobalEvent::WalFlushAck { cut: _ } => true,
        GlobalEvent::WalDiskFull { record: _, cut: _ } => true,
        GlobalEvent::InvokeEvent {
            request: _, attempt: _, call: _, journal_cut: _, ack_cut: _,
        } => false,
        GlobalEvent::DeliverEvent {
            request: _, attempt: _, observation: _, journal_cut: _,
        } => false,
        GlobalEvent::IgnoreStale { request: _, attempt: _ } => false,
        GlobalEvent::RetryRelease { request: _ } => false,
        GlobalEvent::Crash => false,
        GlobalEvent::BeginScan => true,
        GlobalEvent::FinishScan => true,
        GlobalEvent::TruncateTail => true,
        GlobalEvent::AbortScan => true,
        GlobalEvent::BeginRecover => false,
        GlobalEvent::FinishRecover => false,
    }
}

pub open spec fn broker_decodable(event: GlobalEvent) -> bool {
    match broker_decode(event) {
        Option::Some(_) => true,
        Option::None => false,
    }
}

pub proof fn broker_constructor_partition(event: GlobalEvent)
    ensures
        broker_constructor(event) <==> !backend_only_constructor(event),
{
    match event {
        GlobalEvent::BrokerLinearize { .. }
        | GlobalEvent::JournalAppendCall { .. }
        | GlobalEvent::JournalAppendLinearize { .. }
        | GlobalEvent::JournalAppendReturn { .. }
        | GlobalEvent::JournalDiskFull { .. }
        | GlobalEvent::WalStage { .. }
        | GlobalEvent::WalWriteFull { .. }
        | GlobalEvent::WalWriteTorn { .. }
        | GlobalEvent::WalFinishTorn { .. }
        | GlobalEvent::WalFlushAck { .. }
        | GlobalEvent::WalDiskFull { .. }
        | GlobalEvent::InvokeEvent { .. }
        | GlobalEvent::DeliverEvent { .. }
        | GlobalEvent::IgnoreStale { .. }
        | GlobalEvent::RetryRelease { .. }
        | GlobalEvent::Crash
        | GlobalEvent::BeginScan
        | GlobalEvent::FinishScan
        | GlobalEvent::TruncateTail
        | GlobalEvent::AbortScan
        | GlobalEvent::BeginRecover
        | GlobalEvent::FinishRecover => {},
    }
}

pub proof fn broker_decode_accepts_exactly(event: GlobalEvent)
    ensures
        broker_decodable(event) <==> broker_constructor(event),
{
    match event {
        GlobalEvent::BrokerLinearize { .. }
        | GlobalEvent::JournalAppendCall { .. }
        | GlobalEvent::JournalAppendLinearize { .. }
        | GlobalEvent::JournalAppendReturn { .. }
        | GlobalEvent::JournalDiskFull { .. }
        | GlobalEvent::WalStage { .. }
        | GlobalEvent::WalWriteFull { .. }
        | GlobalEvent::WalWriteTorn { .. }
        | GlobalEvent::WalFinishTorn { .. }
        | GlobalEvent::WalFlushAck { .. }
        | GlobalEvent::WalDiskFull { .. }
        | GlobalEvent::InvokeEvent { .. }
        | GlobalEvent::DeliverEvent { .. }
        | GlobalEvent::IgnoreStale { .. }
        | GlobalEvent::RetryRelease { .. }
        | GlobalEvent::Crash
        | GlobalEvent::BeginScan
        | GlobalEvent::FinishScan
        | GlobalEvent::TruncateTail
        | GlobalEvent::AbortScan
        | GlobalEvent::BeginRecover
        | GlobalEvent::FinishRecover => {},
    }
}

pub proof fn broker_decode_rejects_backend_only(event: GlobalEvent)
    requires
        backend_only_constructor(event),
    ensures
        broker_decode(event) == Option::None,
{
    match event {
        GlobalEvent::BrokerLinearize { .. }
        | GlobalEvent::JournalAppendCall { .. }
        | GlobalEvent::JournalAppendLinearize { .. }
        | GlobalEvent::JournalAppendReturn { .. }
        | GlobalEvent::JournalDiskFull { .. }
        | GlobalEvent::WalStage { .. }
        | GlobalEvent::WalWriteFull { .. }
        | GlobalEvent::WalWriteTorn { .. }
        | GlobalEvent::WalFinishTorn { .. }
        | GlobalEvent::WalFlushAck { .. }
        | GlobalEvent::WalDiskFull { .. }
        | GlobalEvent::InvokeEvent { .. }
        | GlobalEvent::DeliverEvent { .. }
        | GlobalEvent::IgnoreStale { .. }
        | GlobalEvent::RetryRelease { .. }
        | GlobalEvent::Crash
        | GlobalEvent::BeginScan
        | GlobalEvent::FinishScan
        | GlobalEvent::TruncateTail
        | GlobalEvent::AbortScan
        | GlobalEvent::BeginRecover
        | GlobalEvent::FinishRecover => {},
    }
}

pub proof fn broker_decode_encode_round_trip(event: p0_layer::Event)
    ensures
        broker_decode(broker_encode(event)) == Option::Some(event),
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

pub proof fn broker_encode_decode_inverse(
    global: GlobalEvent,
    local: p0_layer::Event,
)
    requires
        broker_decode(global) == Option::Some(local),
    ensures
        broker_encode(local) == global,
{
    match global {
        GlobalEvent::BrokerLinearize { .. }
        | GlobalEvent::JournalAppendCall { .. }
        | GlobalEvent::JournalAppendLinearize { .. }
        | GlobalEvent::JournalAppendReturn { .. }
        | GlobalEvent::JournalDiskFull { .. }
        | GlobalEvent::WalStage { .. }
        | GlobalEvent::WalWriteFull { .. }
        | GlobalEvent::WalWriteTorn { .. }
        | GlobalEvent::WalFinishTorn { .. }
        | GlobalEvent::WalFlushAck { .. }
        | GlobalEvent::WalDiskFull { .. }
        | GlobalEvent::InvokeEvent { .. }
        | GlobalEvent::DeliverEvent { .. }
        | GlobalEvent::IgnoreStale { .. }
        | GlobalEvent::RetryRelease { .. }
        | GlobalEvent::Crash
        | GlobalEvent::BeginScan
        | GlobalEvent::FinishScan
        | GlobalEvent::TruncateTail
        | GlobalEvent::AbortScan
        | GlobalEvent::BeginRecover
        | GlobalEvent::FinishRecover => {},
    }
}

pub proof fn broker_encode_injective(
    left: p0_layer::Event,
    right: p0_layer::Event,
)
    requires
        broker_encode(left) == broker_encode(right),
    ensures
        left == right,
{
    broker_decode_encode_round_trip(left);
    broker_decode_encode_round_trip(right);
    assert(broker_decode(broker_encode(left))
        == broker_decode(broker_encode(right)));
}

pub proof fn encoded_events_are_exactly_broker_events(event: p0_layer::Event)
    ensures
        broker_constructor(broker_encode(event)),
        !backend_only_constructor(broker_encode(event)),
        broker_decodable(broker_encode(event)),
{
    broker_decode_encode_round_trip(event);
    broker_decode_accepts_exactly(broker_encode(event));
    broker_constructor_partition(broker_encode(event));
}

} // verus!
