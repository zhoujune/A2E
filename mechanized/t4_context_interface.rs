use vstd::prelude::*;

#[path = "t4_closed_composition.rs"]
pub mod t4_c0_layer;

verus! {

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
use contract_layer::p3_layer::p2_layer::p1_layer::p0_layer;
use p0_layer::config_layer;
use config_layer::broker_layer as record_layer;
use record_layer::query_layer::c1_layer::replay_layer;
use record_layer::query_layer::c1_layer::append_layer;

// T4-C1 fixes the sole interface through which a program context may observe
// the storage-backed runtime. It defines plugging and erasure, but deliberately
// does not construct a target plugged execution; that contextual lift is C2.

pub enum ContextEvent {
    AppendCall {
        record: replay_layer::JournalRecord,
    },
    AppendReturn {
        result: append_layer::AppendResult,
        cut: nat,
    },
    Invoke {
        request: replay_layer::RequestId,
        attempt: replay_layer::AttemptId,
        call: config_layer::CallDescriptor,
    },
    Deliver {
        request: replay_layer::RequestId,
        attempt: replay_layer::AttemptId,
        observation: replay_layer::Observation,
    },
    IgnoreStale {
        request: replay_layer::RequestId,
        attempt: replay_layer::AttemptId,
    },
    RetryRelease {
        request: replay_layer::RequestId,
    },
    Crash,
    BeginRecover,
    FinishRecover,
}

pub enum ContextRuntimeView {
    Quiescent {
        mode: record_layer::Mode,
        slot: record_layer::ExecSlot,
    },
    AppendPending {
        mode: record_layer::Mode,
        record: replay_layer::JournalRecord,
    },
}

pub struct ContextView {
    pub requests: IMap<replay_layer::RequestId, config_layer::Request>,
    pub history: Seq<ContextEvent>,
    pub runtime: ContextRuntimeView,
}

pub open spec fn context_history_after(
    history: Seq<ContextEvent>,
    event: global_layer::GlobalEvent,
) -> Seq<ContextEvent> {
    match event {
        global_layer::GlobalEvent::JournalAppendCall { record }
        | global_layer::GlobalEvent::WalStage { record } => {
            history.push(ContextEvent::AppendCall { record })
        },
        global_layer::GlobalEvent::JournalAppendReturn { cut }
        | global_layer::GlobalEvent::WalFlushAck { cut } => {
            history.push(ContextEvent::AppendReturn {
                result: append_layer::AppendResult::Ok,
                cut,
            })
        },
        global_layer::GlobalEvent::JournalDiskFull { record, cut }
        | global_layer::GlobalEvent::WalDiskFull { record, cut } => {
            history.push(ContextEvent::AppendCall { record }).push(
                ContextEvent::AppendReturn {
                    result: append_layer::AppendResult::Full,
                    cut,
                },
            )
        },
        global_layer::GlobalEvent::InvokeEvent {
            request, attempt, call, ..
        } => history.push(ContextEvent::Invoke { request, attempt, call }),
        global_layer::GlobalEvent::DeliverEvent {
            request, attempt, observation, ..
        } => history.push(ContextEvent::Deliver {
            request, attempt, observation,
        }),
        global_layer::GlobalEvent::IgnoreStale { request, attempt } => {
            history.push(ContextEvent::IgnoreStale { request, attempt })
        },
        global_layer::GlobalEvent::RetryRelease { request } => {
            history.push(ContextEvent::RetryRelease { request })
        },
        global_layer::GlobalEvent::Crash => history.push(ContextEvent::Crash),
        global_layer::GlobalEvent::BeginRecover => {
            history.push(ContextEvent::BeginRecover)
        },
        global_layer::GlobalEvent::FinishRecover => {
            history.push(ContextEvent::FinishRecover)
        },
        global_layer::GlobalEvent::BrokerLinearize { .. }
        | global_layer::GlobalEvent::JournalAppendLinearize { .. }
        | global_layer::GlobalEvent::WalWriteFull { .. }
        | global_layer::GlobalEvent::WalWriteTorn { .. }
        | global_layer::GlobalEvent::WalFinishTorn { .. }
        | global_layer::GlobalEvent::BeginScan
        | global_layer::GlobalEvent::FinishScan
        | global_layer::GlobalEvent::TruncateTail
        | global_layer::GlobalEvent::AbortScan => history,
    }
}

pub open spec fn context_delta(
    event: global_layer::GlobalEvent,
) -> Seq<ContextEvent> {
    context_history_after(Seq::empty(), event)
}

pub open spec fn context_hidden_event(
    event: global_layer::GlobalEvent,
) -> bool {
    match event {
        global_layer::GlobalEvent::BrokerLinearize { .. }
        | global_layer::GlobalEvent::JournalAppendLinearize { .. }
        | global_layer::GlobalEvent::WalWriteFull { .. }
        | global_layer::GlobalEvent::WalWriteTorn { .. }
        | global_layer::GlobalEvent::WalFinishTorn { .. }
        | global_layer::GlobalEvent::BeginScan
        | global_layer::GlobalEvent::FinishScan
        | global_layer::GlobalEvent::TruncateTail
        | global_layer::GlobalEvent::AbortScan => true,
        global_layer::GlobalEvent::JournalAppendCall { .. }
        | global_layer::GlobalEvent::JournalAppendReturn { .. }
        | global_layer::GlobalEvent::JournalDiskFull { .. }
        | global_layer::GlobalEvent::WalStage { .. }
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

pub proof fn context_delta_classification(
    event: global_layer::GlobalEvent,
)
    ensures
        context_delta(event).len() <= 2,
        context_delta(event).len() == 0 <==> context_hidden_event(event),
        context_delta(event).len() > 0 <==> !context_hidden_event(event),
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

pub open spec fn context_history(
    events: Seq<global_layer::GlobalEvent>,
) -> Seq<ContextEvent>
    decreases events.len()
{
    if events.len() == 0 {
        Seq::empty()
    } else {
        context_history_after(context_history(events.drop_last()), events.last())
    }
}

pub proof fn context_history_push(
    events: Seq<global_layer::GlobalEvent>,
    event: global_layer::GlobalEvent,
)
    ensures context_history(events.push(event))
        == context_history_after(context_history(events), event),
{
    assert(events.push(event).drop_last() =~= events);
    assert(events.push(event).last() == event);
}

pub proof fn context_history_after_is_delta_append(
    history: Seq<ContextEvent>,
    event: global_layer::GlobalEvent,
)
    ensures context_history_after(history, event)
        == history.add(context_delta(event)),
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
        | global_layer::GlobalEvent::FinishRecover => {
            assert(context_history_after(history, event)
                =~= history.add(context_delta(event)));
        },
    }
}

pub proof fn context_history_push_delta(
    events: Seq<global_layer::GlobalEvent>,
    event: global_layer::GlobalEvent,
)
    ensures context_history(events.push(event))
        == context_history(events).add(context_delta(event)),
{
    context_history_push(events, event);
    context_history_after_is_delta_append(context_history(events), event);
}

pub proof fn equal_context_deltas_extend_history_equally(
    history: Seq<ContextEvent>,
    left: global_layer::GlobalEvent,
    right: global_layer::GlobalEvent,
)
    requires context_delta(left) == context_delta(right),
    ensures context_history_after(history, left)
        == context_history_after(history, right),
{
    context_history_after_is_delta_append(history, left);
    context_history_after_is_delta_append(history, right);
}

pub open spec fn context_append_io_after(
    output: Seq<append_layer::AppendEvent<replay_layer::JournalRecord>>,
    event: ContextEvent,
) -> Seq<append_layer::AppendEvent<replay_layer::JournalRecord>> {
    match event {
        ContextEvent::AppendCall { record } => {
            output.push(append_layer::AppendEvent::Call { record })
        },
        ContextEvent::AppendReturn { result, cut } => {
            output.push(append_layer::AppendEvent::Return { result, cut })
        },
        ContextEvent::Invoke { .. }
        | ContextEvent::Deliver { .. }
        | ContextEvent::IgnoreStale { .. }
        | ContextEvent::RetryRelease { .. }
        | ContextEvent::Crash
        | ContextEvent::BeginRecover
        | ContextEvent::FinishRecover => output,
    }
}

pub open spec fn context_append_io(
    history: Seq<ContextEvent>,
) -> Seq<append_layer::AppendEvent<replay_layer::JournalRecord>>
    decreases history.len()
{
    if history.len() == 0 {
        Seq::empty()
    } else {
        context_append_io_after(
            context_append_io(history.drop_last()), history.last(),
        )
    }
}

pub proof fn context_append_io_push(
    history: Seq<ContextEvent>,
    event: ContextEvent,
)
    ensures context_append_io(history.push(event))
        == context_append_io_after(context_append_io(history), event),
{
    assert(history.push(event).drop_last() =~= history);
    assert(history.push(event).last() == event);
}

pub proof fn context_append_io_after_global(
    history: Seq<ContextEvent>,
    event: global_layer::GlobalEvent,
)
    ensures context_append_io(context_history_after(history, event))
        == projection_layer::append_io_after(context_append_io(history), event),
{
    match event {
        global_layer::GlobalEvent::JournalAppendCall { record }
        | global_layer::GlobalEvent::WalStage { record } => {
            context_append_io_push(
                history, ContextEvent::AppendCall { record },
            );
        },
        global_layer::GlobalEvent::JournalAppendReturn { cut }
        | global_layer::GlobalEvent::WalFlushAck { cut } => {
            context_append_io_push(history, ContextEvent::AppendReturn {
                result: append_layer::AppendResult::Ok,
                cut,
            });
        },
        global_layer::GlobalEvent::JournalDiskFull { record, cut }
        | global_layer::GlobalEvent::WalDiskFull { record, cut } => {
            let called = history.push(ContextEvent::AppendCall { record });
            context_append_io_push(
                history, ContextEvent::AppendCall { record },
            );
            context_append_io_push(called, ContextEvent::AppendReturn {
                result: append_layer::AppendResult::Full,
                cut,
            });
        },
        global_layer::GlobalEvent::InvokeEvent {
            request, attempt, call, ..
        } => {
            context_append_io_push(
                history, ContextEvent::Invoke { request, attempt, call },
            );
        },
        global_layer::GlobalEvent::DeliverEvent {
            request, attempt, observation, ..
        } => {
            context_append_io_push(history, ContextEvent::Deliver {
                request, attempt, observation,
            });
        },
        global_layer::GlobalEvent::IgnoreStale { request, attempt } => {
            context_append_io_push(
                history, ContextEvent::IgnoreStale { request, attempt },
            );
        },
        global_layer::GlobalEvent::RetryRelease { request } => {
            context_append_io_push(
                history, ContextEvent::RetryRelease { request },
            );
        },
        global_layer::GlobalEvent::Crash => {
            context_append_io_push(history, ContextEvent::Crash);
        },
        global_layer::GlobalEvent::BeginRecover => {
            context_append_io_push(history, ContextEvent::BeginRecover);
        },
        global_layer::GlobalEvent::FinishRecover => {
            context_append_io_push(history, ContextEvent::FinishRecover);
        },
        global_layer::GlobalEvent::BrokerLinearize { .. }
        | global_layer::GlobalEvent::JournalAppendLinearize { .. }
        | global_layer::GlobalEvent::WalWriteFull { .. }
        | global_layer::GlobalEvent::WalWriteTorn { .. }
        | global_layer::GlobalEvent::WalFinishTorn { .. }
        | global_layer::GlobalEvent::BeginScan
        | global_layer::GlobalEvent::FinishScan
        | global_layer::GlobalEvent::TruncateTail
        | global_layer::GlobalEvent::AbortScan => {},
    }
}

pub proof fn context_history_projects_append_io(
    events: Seq<global_layer::GlobalEvent>,
)
    ensures context_append_io(context_history(events))
        == projection_layer::pi_append_io(events),
    decreases events.len(),
{
    if events.len() > 0 {
        context_history_projects_append_io(events.drop_last());
        context_append_io_after_global(
            context_history(events.drop_last()), events.last(),
        );
    }
}

pub open spec fn masked_runtime_view(
    mode: record_layer::Mode,
    slot: record_layer::ExecSlot,
    append: append_layer::AppendControl<replay_layer::JournalRecord>,
) -> ContextRuntimeView {
    match append {
        append_layer::AppendControl::Idle => {
            ContextRuntimeView::Quiescent { mode, slot }
        },
        append_layer::AppendControl::Called { record }
        | append_layer::AppendControl::Linearized { record } => {
            ContextRuntimeView::AppendPending { mode, record }
        },
    }
}

pub open spec fn wal_runtime_view(
    state: wal_runtime_layer::WalConfiguration,
) -> ContextRuntimeView {
    masked_runtime_view(
        state.runtime.mode, state.runtime.slot, state.runtime.append,
    )
}

pub open spec fn journal_runtime_view(
    state: journal_runtime_layer::JournalConfiguration,
) -> ContextRuntimeView {
    masked_runtime_view(
        state.runtime.mode, state.runtime.slot, state.runtime.append,
    )
}

pub open spec fn broker_runtime_view(
    state: p0_layer::State,
) -> ContextRuntimeView {
    masked_runtime_view(
        state.core.broker.mode,
        state.core.broker.slot,
        state.core.broker.append,
    )
}

pub open spec fn initial_context_view(
    cfg: config_layer::FullConfig,
) -> ContextView {
    ContextView {
        requests: cfg.request,
        history: Seq::empty(),
        runtime: ContextRuntimeView::Quiescent {
            mode: record_layer::Mode::Online,
            slot: record_layer::ExecSlot::Idle,
        },
    }
}

pub proof fn initial_runtime_views_agree(
    cfg: config_layer::FullConfig,
)
    ensures
        wal_runtime_view(wal_runtime_layer::initial_configuration(cfg))
            == initial_context_view(cfg).runtime,
        journal_runtime_view(journal_runtime_layer::initial_configuration(cfg))
            == initial_context_view(cfg).runtime,
        broker_runtime_view(p0_layer::initial_state(cfg))
            == initial_context_view(cfg).runtime,
{
}

pub proof fn t3_representation_preserves_runtime_view(
    wal: wal_runtime_layer::WalConfiguration,
    journal: journal_runtime_layer::JournalConfiguration,
)
    requires t3_representation_layer::representation(wal, journal),
    ensures wal_runtime_view(wal) == journal_runtime_view(journal),
{
}

pub proof fn t2_representation_preserves_runtime_view(
    cfg: config_layer::FullConfig,
    journal: journal_runtime_layer::JournalConfiguration,
    broker: p0_layer::State,
)
    requires t2_representation_layer::representation(cfg, journal, broker),
    ensures journal_runtime_view(journal) == broker_runtime_view(broker),
{
}

pub proof fn t4_representation_preserves_runtime_view(
    cfg: config_layer::FullConfig,
    wal: wal_runtime_layer::WalConfiguration,
    broker: p0_layer::State,
)
    requires t4_c0_layer::wal_broker_representation(cfg, wal, broker),
    ensures wal_runtime_view(wal) == broker_runtime_view(broker),
{
}

pub proof fn t3_matched_events_have_equal_context_delta(
    source: global_layer::GlobalEvent,
    target: global_layer::GlobalEvent,
)
    requires t3_event_layer::event_match(source, target),
    ensures context_delta(source) == context_delta(target),
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

pub proof fn t3_internal_events_have_empty_context_delta(
    event: global_layer::GlobalEvent,
)
    requires t3_event_layer::wal_internal_event(event),
    ensures context_delta(event).len() == 0,
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

pub proof fn t3_silent_event_has_empty_context_delta(
    event: global_layer::GlobalEvent,
)
    requires
        wal_runtime_layer::wal_constructor(event),
        t3_event_layer::t3_projection_silent(event),
    ensures context_delta(event).len() == 0,
{
    t3_event_layer::internal_event_classifier_exact(event);
    t3_internal_events_have_empty_context_delta(event);
}

pub proof fn t4_silent_event_has_empty_context_delta(
    event: global_layer::GlobalEvent,
)
    requires
        wal_runtime_layer::wal_constructor(event),
        t4_c0_layer::composed_projection_silent(event),
    ensures context_delta(event).len() == 0,
{
    t3_silent_event_has_empty_context_delta(event);
}

pub proof fn t2_renaming_preserves_context_delta(
    event: global_layer::GlobalEvent,
)
    ensures context_delta(event) == context_delta(
        t2_event_layer::journal_to_broker_event(event),
    ),
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

pub proof fn t2_matched_events_have_equal_context_delta(
    source: global_layer::GlobalEvent,
    target: global_layer::GlobalEvent,
)
    requires t2_event_layer::event_match(source, target),
    ensures context_delta(source) == context_delta(target),
{
    t2_renaming_preserves_context_delta(source);
}

pub proof fn t4_matched_events_have_equal_context_delta(
    source: global_layer::GlobalEvent,
    target: global_layer::GlobalEvent,
)
    requires t4_c0_layer::composed_event_match(source, target),
    ensures context_delta(source) == context_delta(target),
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

pub proof fn t3_translation_preserves_context_history(
    events: Seq<global_layer::GlobalEvent>,
)
    requires wal_runtime_layer::wal_trace_closed(events),
    ensures context_history(t3_event_layer::translate_trace(events))
        == context_history(events),
    decreases events.len(),
{
    if events.len() > 0 {
        let prefix = events.drop_last();
        let event = events.last();
        t3_event_layer::wal_closed_last(events);
        t3_translation_preserves_context_history(prefix);
        t3_event_layer::translate_trace_push(prefix, event);
        context_history_push_delta(prefix, event);
        match t3_event_layer::translate_event(event) {
            Option::Some(target) => {
                context_history_push_delta(
                    t3_event_layer::translate_trace(prefix), target,
                );
                t3_matched_events_have_equal_context_delta(event, target);
            },
            Option::None => {
                t3_event_layer::wal_translation_classifier_exact(event);
                t3_internal_events_have_empty_context_delta(event);
                assert(context_delta(event) =~= Seq::empty());
            },
        }
    }
}

pub proof fn t2_translation_preserves_context_history(
    events: Seq<global_layer::GlobalEvent>,
)
    ensures context_history(t2_event_layer::translate_trace(events))
        == context_history(events),
    decreases events.len(),
{
    if events.len() > 0 {
        let prefix = events.drop_last();
        let event = events.last();
        t2_translation_preserves_context_history(prefix);
        t2_event_layer::translate_trace_push(prefix, event);
        context_history_push_delta(prefix, event);
        context_history_push_delta(
            t2_event_layer::translate_trace(prefix),
            t2_event_layer::journal_to_broker_event(event),
        );
        t2_renaming_preserves_context_delta(event);
    }
}

pub struct ContextInitial<S> {
    pub view: ContextView,
    pub state: S,
}

// Context reactions are synchronized to visible machine events and may inspect
// both masked endpoint views. Autonomous reactions between machine events are
// outside this finite-trace safety interface.
pub struct ContextTransition<S> {
    pub before: S,
    pub view: ContextView,
    pub delta: Seq<ContextEvent>,
    pub after_view: ContextView,
    pub after: S,
}

#[verifier::reject_recursive_types(S)]
pub struct ProgramContext<S> {
    pub initial: ISet<ContextInitial<S>>,
    pub transitions: ISet<ContextTransition<S>>,
}

pub open spec fn valid_context_delta(delta: Seq<ContextEvent>) -> bool {
    delta.len() > 0
        && exists|event: global_layer::GlobalEvent|
            context_delta(event) == delta
}

pub open spec fn storage_parametric_context<S>(
    cfg: config_layer::FullConfig,
    context: ProgramContext<S>,
) -> bool {
    &&& exists|state: S| context.initial.contains(ContextInitial {
        view: initial_context_view(cfg),
        state,
    })
    &&& forall|admitted: ContextInitial<S>|
        #[trigger] context.initial.contains(admitted) ==>
            admitted.view == initial_context_view(cfg)
    &&& forall|transition: ContextTransition<S>|
        #[trigger] context.transitions.contains(transition) ==> {
            &&& transition.view.requests == cfg.request
            &&& transition.after_view.requests == cfg.request
            &&& valid_context_delta(transition.delta)
        }
}

pub open spec fn context_accepts_step<S>(
    context: ProgramContext<S>,
    before: S,
    view: ContextView,
    event: global_layer::GlobalEvent,
    after_view: ContextView,
    after: S,
) -> bool {
    let delta = context_delta(event);
    if delta.len() == 0 {
        after_view == view && after == before
    } else {
        context.transitions.contains(ContextTransition {
            before,
            view,
            delta,
            after_view,
            after,
        })
    }
}

pub proof fn equal_view_transition_transfer<S>(
    context: ProgramContext<S>,
    state: S,
    left_view: ContextView,
    right_view: ContextView,
    delta: Seq<ContextEvent>,
    left_after_view: ContextView,
    right_after_view: ContextView,
    next: S,
)
    requires
        left_view == right_view,
        left_after_view == right_after_view,
    ensures context.transitions.contains(ContextTransition {
        before: state,
        view: left_view,
        delta,
        after_view: left_after_view,
        after: next,
    }) <==> context.transitions.contains(ContextTransition {
        before: state,
        view: right_view,
        delta,
        after_view: right_after_view,
        after: next,
    }),
{
}

pub proof fn context_acceptance_transfers<S>(
    context: ProgramContext<S>,
    state: S,
    left_view: ContextView,
    right_view: ContextView,
    left_event: global_layer::GlobalEvent,
    right_event: global_layer::GlobalEvent,
    left_after_view: ContextView,
    right_after_view: ContextView,
    next: S,
)
    requires
        left_view == right_view,
        left_after_view == right_after_view,
        context_delta(left_event) == context_delta(right_event),
    ensures context_accepts_step(
        context, state, left_view, left_event, left_after_view, next,
    ) <==> context_accepts_step(
        context, state, right_view, right_event, right_after_view, next,
    ),
{
}

pub open spec fn wal_context_view_at(
    cfg: config_layer::FullConfig,
    execution: wal_runtime_layer::WalExecution,
    index: nat,
) -> ContextView {
    ContextView {
        requests: cfg.request,
        history: context_history(execution.events.take(index as int)),
        runtime: wal_runtime_view(execution.configs[index as int]),
    }
}

pub open spec fn journal_context_view_at(
    cfg: config_layer::FullConfig,
    execution: journal_runtime_layer::JournalExecution,
    index: nat,
) -> ContextView {
    ContextView {
        requests: cfg.request,
        history: context_history(execution.events.take(index as int)),
        runtime: journal_runtime_view(execution.configs[index as int]),
    }
}

pub open spec fn broker_context_view_at(
    cfg: config_layer::FullConfig,
    execution: execution_layer::BrokerExecution,
    index: nat,
) -> ContextView {
    ContextView {
        requests: cfg.request,
        history: context_history(execution.events.take(index as int)),
        runtime: broker_runtime_view(execution.configs[index as int]),
    }
}

pub proof fn initialized_wal_has_initial_context_view(
    cfg: config_layer::FullConfig,
    execution: wal_runtime_layer::WalExecution,
)
    requires
        execution.configs.len() > 0,
        execution.configs[0] == wal_runtime_layer::initial_configuration(cfg),
    ensures wal_context_view_at(cfg, execution, 0) == initial_context_view(cfg),
{
    initial_runtime_views_agree(cfg);
}

pub proof fn initialized_journal_has_initial_context_view(
    cfg: config_layer::FullConfig,
    execution: journal_runtime_layer::JournalExecution,
)
    requires
        execution.configs.len() > 0,
        execution.configs[0]
            == journal_runtime_layer::initial_configuration(cfg),
    ensures journal_context_view_at(cfg, execution, 0)
        == initial_context_view(cfg),
{
    initial_runtime_views_agree(cfg);
}

pub proof fn initialized_broker_has_initial_context_view(
    cfg: config_layer::FullConfig,
    execution: execution_layer::BrokerExecution,
)
    requires
        execution.configs.len() > 0,
        execution.configs[0] == p0_layer::initial_state(cfg),
    ensures broker_context_view_at(cfg, execution, 0)
        == initial_context_view(cfg),
{
    initial_runtime_views_agree(cfg);
}

pub struct PluggedWalExecution<S> {
    pub machine: wal_runtime_layer::WalExecution,
    pub contexts: Seq<S>,
}

pub struct PluggedJournalExecution<S> {
    pub machine: journal_runtime_layer::JournalExecution,
    pub contexts: Seq<S>,
}

pub struct PluggedBrokerExecution<S> {
    pub machine: execution_layer::BrokerExecution,
    pub contexts: Seq<S>,
}

pub open spec fn plugged_wal_exec<S>(
    cfg: config_layer::FullConfig,
    context: ProgramContext<S>,
    execution: PluggedWalExecution<S>,
) -> bool {
    &&& execution.machine.configs.len() == execution.machine.events.len() + 1
    &&& execution.contexts.len() == execution.machine.events.len() + 1
    &&& execution.machine.configs[0]
        == wal_runtime_layer::initial_configuration(cfg)
    &&& context.initial.contains(ContextInitial {
        view: wal_context_view_at(cfg, execution.machine, 0),
        state: execution.contexts[0],
    })
    &&& forall|index: nat| index < execution.machine.events.len() ==> {
        &&& #[trigger] wal_runtime_layer::wal_runtime_step(
            cfg,
            execution.machine.configs[index as int],
            execution.machine.events[index as int],
            execution.machine.configs[(index + 1) as int],
        )
        &&& context_accepts_step(
            context,
            execution.contexts[index as int],
            wal_context_view_at(cfg, execution.machine, index),
            execution.machine.events[index as int],
            wal_context_view_at(cfg, execution.machine, index + 1),
            execution.contexts[(index + 1) as int],
        )
    }
}

pub open spec fn plugged_journal_exec<S>(
    cfg: config_layer::FullConfig,
    context: ProgramContext<S>,
    execution: PluggedJournalExecution<S>,
) -> bool {
    &&& execution.machine.configs.len() == execution.machine.events.len() + 1
    &&& execution.contexts.len() == execution.machine.events.len() + 1
    &&& execution.machine.configs[0]
        == journal_runtime_layer::initial_configuration(cfg)
    &&& context.initial.contains(ContextInitial {
        view: journal_context_view_at(cfg, execution.machine, 0),
        state: execution.contexts[0],
    })
    &&& forall|index: nat| index < execution.machine.events.len() ==> {
        &&& #[trigger] journal_runtime_layer::journal_runtime_step(
            cfg,
            execution.machine.configs[index as int],
            execution.machine.events[index as int],
            execution.machine.configs[(index + 1) as int],
        )
        &&& context_accepts_step(
            context,
            execution.contexts[index as int],
            journal_context_view_at(cfg, execution.machine, index),
            execution.machine.events[index as int],
            journal_context_view_at(cfg, execution.machine, index + 1),
            execution.contexts[(index + 1) as int],
        )
    }
}

pub open spec fn plugged_broker_exec<S>(
    cfg: config_layer::FullConfig,
    context: ProgramContext<S>,
    execution: PluggedBrokerExecution<S>,
) -> bool {
    &&& execution.machine.configs.len() == execution.machine.events.len() + 1
    &&& execution.contexts.len() == execution.machine.events.len() + 1
    &&& execution.machine.configs[0] == p0_layer::initial_state(cfg)
    &&& context.initial.contains(ContextInitial {
        view: broker_context_view_at(cfg, execution.machine, 0),
        state: execution.contexts[0],
    })
    &&& forall|index: nat| index < execution.machine.events.len() ==> {
        &&& #[trigger] execution_layer::broker_step(
            cfg,
            execution.machine.configs[index as int],
            execution.machine.events[index as int],
            execution.machine.configs[(index + 1) as int],
        )
        &&& context_accepts_step(
            context,
            execution.contexts[index as int],
            broker_context_view_at(cfg, execution.machine, index),
            execution.machine.events[index as int],
            broker_context_view_at(cfg, execution.machine, index + 1),
            execution.contexts[(index + 1) as int],
        )
    }
}

pub proof fn plugged_wal_embeds<S>(
    cfg: config_layer::FullConfig,
    context: ProgramContext<S>,
    execution: PluggedWalExecution<S>,
)
    requires plugged_wal_exec(cfg, context, execution),
    ensures wal_runtime_layer::exec(cfg, execution.machine),
{
}

pub proof fn plugged_journal_embeds<S>(
    cfg: config_layer::FullConfig,
    context: ProgramContext<S>,
    execution: PluggedJournalExecution<S>,
)
    requires plugged_journal_exec(cfg, context, execution),
    ensures journal_runtime_layer::exec(cfg, execution.machine),
{
}

pub proof fn plugged_broker_embeds<S>(
    cfg: config_layer::FullConfig,
    context: ProgramContext<S>,
    execution: PluggedBrokerExecution<S>,
)
    requires plugged_broker_exec(cfg, context, execution),
    ensures execution_layer::exec(cfg, execution.machine),
{
}

pub proof fn wal_hidden_step_preserves_runtime_view(
    cfg: config_layer::FullConfig,
    before: wal_runtime_layer::WalConfiguration,
    event: global_layer::GlobalEvent,
    after: wal_runtime_layer::WalConfiguration,
)
    requires
        wal_runtime_layer::wal_runtime_step(cfg, before, event, after),
        context_delta(event).len() == 0,
    ensures wal_runtime_view(before) == wal_runtime_view(after),
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

pub proof fn journal_hidden_step_preserves_runtime_view(
    cfg: config_layer::FullConfig,
    before: journal_runtime_layer::JournalConfiguration,
    event: global_layer::GlobalEvent,
    after: journal_runtime_layer::JournalConfiguration,
)
    requires
        journal_runtime_layer::journal_runtime_step(cfg, before, event, after),
        context_delta(event).len() == 0,
    ensures journal_runtime_view(before) == journal_runtime_view(after),
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

pub proof fn broker_hidden_step_preserves_runtime_view(
    cfg: config_layer::FullConfig,
    before: p0_layer::State,
    event: global_layer::GlobalEvent,
    after: p0_layer::State,
)
    requires
        execution_layer::broker_step(cfg, before, event, after),
        context_delta(event).len() == 0,
    ensures broker_runtime_view(before) == broker_runtime_view(after),
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

pub proof fn wal_hidden_step_preserves_context_view(
    cfg: config_layer::FullConfig,
    history: Seq<ContextEvent>,
    before: wal_runtime_layer::WalConfiguration,
    event: global_layer::GlobalEvent,
    after: wal_runtime_layer::WalConfiguration,
)
    requires
        wal_runtime_layer::wal_runtime_step(cfg, before, event, after),
        context_delta(event).len() == 0,
    ensures (ContextView {
        requests: cfg.request,
        history,
        runtime: wal_runtime_view(before),
    }) == (ContextView {
        requests: cfg.request,
        history: context_history_after(history, event),
        runtime: wal_runtime_view(after),
    }),
{
    context_delta_classification(event);
    wal_hidden_step_preserves_runtime_view(cfg, before, event, after);
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

pub proof fn journal_hidden_step_preserves_context_view(
    cfg: config_layer::FullConfig,
    history: Seq<ContextEvent>,
    before: journal_runtime_layer::JournalConfiguration,
    event: global_layer::GlobalEvent,
    after: journal_runtime_layer::JournalConfiguration,
)
    requires
        journal_runtime_layer::journal_runtime_step(cfg, before, event, after),
        context_delta(event).len() == 0,
    ensures (ContextView {
        requests: cfg.request,
        history,
        runtime: journal_runtime_view(before),
    }) == (ContextView {
        requests: cfg.request,
        history: context_history_after(history, event),
        runtime: journal_runtime_view(after),
    }),
{
    context_delta_classification(event);
    journal_hidden_step_preserves_runtime_view(cfg, before, event, after);
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

pub proof fn broker_hidden_step_preserves_context_view(
    cfg: config_layer::FullConfig,
    history: Seq<ContextEvent>,
    before: p0_layer::State,
    event: global_layer::GlobalEvent,
    after: p0_layer::State,
)
    requires
        execution_layer::broker_step(cfg, before, event, after),
        context_delta(event).len() == 0,
    ensures (ContextView {
        requests: cfg.request,
        history,
        runtime: broker_runtime_view(before),
    }) == (ContextView {
        requests: cfg.request,
        history: context_history_after(history, event),
        runtime: broker_runtime_view(after),
    }),
{
    context_delta_classification(event);
    broker_hidden_step_preserves_runtime_view(cfg, before, event, after);
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

pub open spec fn plugged_wal_prefix<S>(
    execution: PluggedWalExecution<S>,
    length: nat,
) -> PluggedWalExecution<S> {
    PluggedWalExecution {
        machine: wal_runtime_layer::execution_prefix(execution.machine, length),
        contexts: execution.contexts.take((length + 1) as int),
    }
}

pub open spec fn plugged_journal_prefix<S>(
    execution: PluggedJournalExecution<S>,
    length: nat,
) -> PluggedJournalExecution<S> {
    PluggedJournalExecution {
        machine: journal_runtime_layer::execution_prefix(execution.machine, length),
        contexts: execution.contexts.take((length + 1) as int),
    }
}

pub open spec fn plugged_broker_prefix<S>(
    execution: PluggedBrokerExecution<S>,
    length: nat,
) -> PluggedBrokerExecution<S> {
    PluggedBrokerExecution {
        machine: execution_layer::execution_prefix(execution.machine, length),
        contexts: execution.contexts.take((length + 1) as int),
    }
}

pub proof fn plugged_wal_prefix_closed<S>(
    cfg: config_layer::FullConfig,
    context: ProgramContext<S>,
    execution: PluggedWalExecution<S>,
    length: nat,
)
    requires
        plugged_wal_exec(cfg, context, execution),
        length <= execution.machine.events.len(),
    ensures plugged_wal_exec(
        cfg, context, plugged_wal_prefix(execution, length),
    ),
{
    let prefix = plugged_wal_prefix(execution, length);
    assert(prefix.machine.events.len() == length);
    assert(prefix.machine.configs.len() == length + 1);
    assert(prefix.contexts.len() == length + 1);
    assert(prefix.machine.configs[0] == execution.machine.configs[0]);
    assert(prefix.contexts[0] == execution.contexts[0]);
    assert(prefix.machine.events.take(0) =~= execution.machine.events.take(0));
    assert(wal_context_view_at(cfg, prefix.machine, 0)
        == wal_context_view_at(cfg, execution.machine, 0));
    assert forall|index: nat| index < prefix.machine.events.len() implies {
        &&& #[trigger] wal_runtime_layer::wal_runtime_step(
            cfg,
            prefix.machine.configs[index as int],
            prefix.machine.events[index as int],
            prefix.machine.configs[(index + 1) as int],
        )
        &&& context_accepts_step(
            context,
            prefix.contexts[index as int],
            wal_context_view_at(cfg, prefix.machine, index),
            prefix.machine.events[index as int],
            wal_context_view_at(cfg, prefix.machine, index + 1),
            prefix.contexts[(index + 1) as int],
        )
    } by {
        assert(index < execution.machine.events.len());
        assert(prefix.machine.events[index as int]
            == execution.machine.events[index as int]);
        assert(prefix.machine.configs[index as int]
            == execution.machine.configs[index as int]);
        assert(prefix.machine.configs[(index + 1) as int]
            == execution.machine.configs[(index + 1) as int]);
        assert(prefix.contexts[index as int] == execution.contexts[index as int]);
        assert(prefix.contexts[(index + 1) as int]
            == execution.contexts[(index + 1) as int]);
        assert(prefix.machine.events.take(index as int)
            =~= execution.machine.events.take(index as int));
        assert(prefix.machine.events.take((index + 1) as int)
            =~= execution.machine.events.take((index + 1) as int));
        assert(wal_context_view_at(cfg, prefix.machine, index)
            == wal_context_view_at(cfg, execution.machine, index));
        assert(wal_context_view_at(cfg, prefix.machine, index + 1)
            == wal_context_view_at(cfg, execution.machine, index + 1));
    }
}

pub proof fn plugged_journal_prefix_closed<S>(
    cfg: config_layer::FullConfig,
    context: ProgramContext<S>,
    execution: PluggedJournalExecution<S>,
    length: nat,
)
    requires
        plugged_journal_exec(cfg, context, execution),
        length <= execution.machine.events.len(),
    ensures plugged_journal_exec(
        cfg, context, plugged_journal_prefix(execution, length),
    ),
{
    let prefix = plugged_journal_prefix(execution, length);
    assert(prefix.machine.events.len() == length);
    assert(prefix.machine.configs.len() == length + 1);
    assert(prefix.contexts.len() == length + 1);
    assert(prefix.machine.configs[0] == execution.machine.configs[0]);
    assert(prefix.contexts[0] == execution.contexts[0]);
    assert(prefix.machine.events.take(0) =~= execution.machine.events.take(0));
    assert(journal_context_view_at(cfg, prefix.machine, 0)
        == journal_context_view_at(cfg, execution.machine, 0));
    assert forall|index: nat| index < prefix.machine.events.len() implies {
        &&& #[trigger] journal_runtime_layer::journal_runtime_step(
            cfg,
            prefix.machine.configs[index as int],
            prefix.machine.events[index as int],
            prefix.machine.configs[(index + 1) as int],
        )
        &&& context_accepts_step(
            context,
            prefix.contexts[index as int],
            journal_context_view_at(cfg, prefix.machine, index),
            prefix.machine.events[index as int],
            journal_context_view_at(cfg, prefix.machine, index + 1),
            prefix.contexts[(index + 1) as int],
        )
    } by {
        assert(index < execution.machine.events.len());
        assert(prefix.machine.events[index as int]
            == execution.machine.events[index as int]);
        assert(prefix.machine.configs[index as int]
            == execution.machine.configs[index as int]);
        assert(prefix.machine.configs[(index + 1) as int]
            == execution.machine.configs[(index + 1) as int]);
        assert(prefix.contexts[index as int] == execution.contexts[index as int]);
        assert(prefix.contexts[(index + 1) as int]
            == execution.contexts[(index + 1) as int]);
        assert(prefix.machine.events.take(index as int)
            =~= execution.machine.events.take(index as int));
        assert(prefix.machine.events.take((index + 1) as int)
            =~= execution.machine.events.take((index + 1) as int));
        assert(journal_context_view_at(cfg, prefix.machine, index)
            == journal_context_view_at(cfg, execution.machine, index));
        assert(journal_context_view_at(cfg, prefix.machine, index + 1)
            == journal_context_view_at(cfg, execution.machine, index + 1));
    }
}

pub proof fn plugged_broker_prefix_closed<S>(
    cfg: config_layer::FullConfig,
    context: ProgramContext<S>,
    execution: PluggedBrokerExecution<S>,
    length: nat,
)
    requires
        plugged_broker_exec(cfg, context, execution),
        length <= execution.machine.events.len(),
    ensures plugged_broker_exec(
        cfg, context, plugged_broker_prefix(execution, length),
    ),
{
    let prefix = plugged_broker_prefix(execution, length);
    assert(prefix.machine.events.len() == length);
    assert(prefix.machine.configs.len() == length + 1);
    assert(prefix.contexts.len() == length + 1);
    assert(prefix.machine.configs[0] == execution.machine.configs[0]);
    assert(prefix.contexts[0] == execution.contexts[0]);
    assert(prefix.machine.events.take(0) =~= execution.machine.events.take(0));
    assert(broker_context_view_at(cfg, prefix.machine, 0)
        == broker_context_view_at(cfg, execution.machine, 0));
    assert forall|index: nat| index < prefix.machine.events.len() implies {
        &&& #[trigger] execution_layer::broker_step(
            cfg,
            prefix.machine.configs[index as int],
            prefix.machine.events[index as int],
            prefix.machine.configs[(index + 1) as int],
        )
        &&& context_accepts_step(
            context,
            prefix.contexts[index as int],
            broker_context_view_at(cfg, prefix.machine, index),
            prefix.machine.events[index as int],
            broker_context_view_at(cfg, prefix.machine, index + 1),
            prefix.contexts[(index + 1) as int],
        )
    } by {
        assert(index < execution.machine.events.len());
        assert(prefix.machine.events[index as int]
            == execution.machine.events[index as int]);
        assert(prefix.machine.configs[index as int]
            == execution.machine.configs[index as int]);
        assert(prefix.machine.configs[(index + 1) as int]
            == execution.machine.configs[(index + 1) as int]);
        assert(prefix.contexts[index as int] == execution.contexts[index as int]);
        assert(prefix.contexts[(index + 1) as int]
            == execution.contexts[(index + 1) as int]);
        assert(prefix.machine.events.take(index as int)
            =~= execution.machine.events.take(index as int));
        assert(prefix.machine.events.take((index + 1) as int)
            =~= execution.machine.events.take((index + 1) as int));
        assert(broker_context_view_at(cfg, prefix.machine, index)
            == broker_context_view_at(cfg, execution.machine, index));
        assert(broker_context_view_at(cfg, prefix.machine, index + 1)
            == broker_context_view_at(cfg, execution.machine, index + 1));
    }
}

pub open spec fn inert_context<S>(
    cfg: config_layer::FullConfig,
    state: S,
) -> ProgramContext<S> {
    ProgramContext {
        initial: ISet::new(|entry: ContextInitial<S>| entry.view
                == initial_context_view(cfg)
            && entry.state == state),
        transitions: ISet::new(|transition: ContextTransition<S>| {
            &&& transition.before == state
            &&& transition.after == state
            &&& transition.view.requests == cfg.request
            &&& transition.after_view.requests == cfg.request
            &&& valid_context_delta(transition.delta)
        }),
    }
}

pub proof fn inert_context_is_storage_parametric<S>(
    cfg: config_layer::FullConfig,
    state: S,
)
    ensures storage_parametric_context(cfg, inert_context(cfg, state)),
{
    let admitted = ContextInitial {
        view: initial_context_view(cfg),
        state,
    };
    assert(inert_context(cfg, state).initial.contains(admitted));
    assert(exists|witness: S| inert_context(cfg, state).initial.contains(
        ContextInitial { view: initial_context_view(cfg), state: witness },
    )) by {
        let witness = state;
    }
    assert forall|transition: ContextTransition<S>|
        #[trigger] inert_context(cfg, state).transitions.contains(transition)
            implies {
                &&& transition.view.requests == cfg.request
                &&& transition.after_view.requests == cfg.request
                &&& valid_context_delta(transition.delta)
            } by {
    }
}

pub open spec fn zero_wal_execution(
    cfg: config_layer::FullConfig,
) -> wal_runtime_layer::WalExecution {
    wal_runtime_layer::WalExecution {
        configs: Seq::empty().push(wal_runtime_layer::initial_configuration(cfg)),
        events: Seq::empty(),
    }
}

pub open spec fn zero_journal_execution(
    cfg: config_layer::FullConfig,
) -> journal_runtime_layer::JournalExecution {
    journal_runtime_layer::JournalExecution {
        configs: Seq::empty().push(
            journal_runtime_layer::initial_configuration(cfg),
        ),
        events: Seq::empty(),
    }
}

pub open spec fn zero_broker_execution(
    cfg: config_layer::FullConfig,
) -> execution_layer::BrokerExecution {
    execution_layer::BrokerExecution {
        configs: Seq::empty().push(p0_layer::initial_state(cfg)),
        events: Seq::empty(),
    }
}

pub open spec fn crash_wal_execution(
    cfg: config_layer::FullConfig,
) -> wal_runtime_layer::WalExecution {
    let initial = wal_runtime_layer::initial_configuration(cfg);
    wal_runtime_layer::WalExecution {
        configs: Seq::empty().push(initial).push(wal_runtime_layer::apply(
            cfg, initial, wal_runtime_layer::WalEvent::Crash,
        )),
        events: Seq::empty().push(global_layer::GlobalEvent::Crash),
    }
}

pub open spec fn crash_journal_execution(
    cfg: config_layer::FullConfig,
) -> journal_runtime_layer::JournalExecution {
    let initial = journal_runtime_layer::initial_configuration(cfg);
    journal_runtime_layer::JournalExecution {
        configs: Seq::empty().push(initial).push(journal_runtime_layer::apply(
            cfg, initial, journal_runtime_layer::JournalEvent::Crash,
        )),
        events: Seq::empty().push(global_layer::GlobalEvent::Crash),
    }
}

pub open spec fn crash_broker_execution(
    cfg: config_layer::FullConfig,
) -> execution_layer::BrokerExecution {
    let initial = p0_layer::initial_state(cfg);
    execution_layer::BrokerExecution {
        configs: Seq::empty().push(initial).push(p0_layer::apply(
            cfg, initial, p0_layer::Event::Crash,
        )),
        events: Seq::empty().push(global_layer::GlobalEvent::Crash),
    }
}

pub proof fn initial_context_views_are_identical(
    cfg: config_layer::FullConfig,
)
    ensures
        wal_context_view_at(cfg, zero_wal_execution(cfg), 0)
            == initial_context_view(cfg),
        journal_context_view_at(cfg, zero_journal_execution(cfg), 0)
            == initial_context_view(cfg),
        broker_context_view_at(cfg, zero_broker_execution(cfg), 0)
            == initial_context_view(cfg),
{
    initial_runtime_views_agree(cfg);
}

pub proof fn storage_parametric_context_has_shared_zero_execution<S>(
    cfg: config_layer::FullConfig,
    context: ProgramContext<S>,
)
    requires storage_parametric_context(cfg, context),
    ensures exists|state: S| {
        &&& plugged_wal_exec(cfg, context, PluggedWalExecution {
            machine: zero_wal_execution(cfg),
            contexts: Seq::empty().push(state),
        })
        &&& plugged_journal_exec(cfg, context, PluggedJournalExecution {
            machine: zero_journal_execution(cfg),
            contexts: Seq::empty().push(state),
        })
        &&& plugged_broker_exec(cfg, context, PluggedBrokerExecution {
            machine: zero_broker_execution(cfg),
            contexts: Seq::empty().push(state),
        })
    },
{
    assert(exists|candidate: S| context.initial.contains(ContextInitial {
        view: initial_context_view(cfg),
        state: candidate,
    }));
    let state = choose|state: S| context.initial.contains(ContextInitial {
        view: initial_context_view(cfg),
        state,
    });
    assert(context.initial.contains(ContextInitial {
        view: initial_context_view(cfg),
        state,
    }));
    initial_context_views_are_identical(cfg);
    assert(plugged_wal_exec(cfg, context, PluggedWalExecution {
        machine: zero_wal_execution(cfg),
        contexts: Seq::empty().push(state),
    }));
    assert(plugged_journal_exec(cfg, context, PluggedJournalExecution {
        machine: zero_journal_execution(cfg),
        contexts: Seq::empty().push(state),
    }));
    assert(plugged_broker_exec(cfg, context, PluggedBrokerExecution {
        machine: zero_broker_execution(cfg),
        contexts: Seq::empty().push(state),
    }));
    assert(exists|witness: S| {
        &&& plugged_wal_exec(cfg, context, PluggedWalExecution {
            machine: zero_wal_execution(cfg),
            contexts: Seq::empty().push(witness),
        })
        &&& plugged_journal_exec(cfg, context, PluggedJournalExecution {
            machine: zero_journal_execution(cfg),
            contexts: Seq::empty().push(witness),
        })
        &&& plugged_broker_exec(cfg, context, PluggedBrokerExecution {
            machine: zero_broker_execution(cfg),
            contexts: Seq::empty().push(witness),
        })
    }) by {
        let witness = state;
    }
}

pub proof fn inert_context_has_shared_visible_execution<S>(
    cfg: config_layer::FullConfig,
    state: S,
)
    ensures
        plugged_wal_exec(cfg, inert_context(cfg, state), PluggedWalExecution {
            machine: crash_wal_execution(cfg),
            contexts: Seq::empty().push(state).push(state),
        }),
        plugged_journal_exec(
            cfg, inert_context(cfg, state), PluggedJournalExecution {
                machine: crash_journal_execution(cfg),
                contexts: Seq::empty().push(state).push(state),
            },
        ),
        plugged_broker_exec(
            cfg, inert_context(cfg, state), PluggedBrokerExecution {
                machine: crash_broker_execution(cfg),
                contexts: Seq::empty().push(state).push(state),
            },
        ),
{
    let delta = context_delta(global_layer::GlobalEvent::Crash);
    assert(valid_context_delta(delta)) by {
        assert(exists|event: global_layer::GlobalEvent|
            context_delta(event) == delta) by {
            let event = global_layer::GlobalEvent::Crash;
        }
    }
    initial_context_views_are_identical(cfg);
    assert(wal_runtime_layer::wal_runtime_step(
        cfg,
        crash_wal_execution(cfg).configs[0],
        crash_wal_execution(cfg).events[0],
        crash_wal_execution(cfg).configs[1],
    ));
    assert(journal_runtime_layer::journal_runtime_step(
        cfg,
        crash_journal_execution(cfg).configs[0],
        crash_journal_execution(cfg).events[0],
        crash_journal_execution(cfg).configs[1],
    ));
    assert(execution_layer::broker_step(
        cfg,
        crash_broker_execution(cfg).configs[0],
        crash_broker_execution(cfg).events[0],
        crash_broker_execution(cfg).configs[1],
    ));
}

}
