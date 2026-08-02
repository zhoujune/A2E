use vstd::prelude::*;

#[path = "t6_deduplicated_witness.rs"]
pub mod t6_dd2_layer;

verus! {

use t6_dd2_layer::*;
use t6_dd2_layer::t6_dd1_layer;
use t6_dd1_layer::*;
use t6_dd1_layer::t6_dd0_layer;
use t6_dd0_layer::*;
use t6_dd0_layer::t6_ro0_layer;
use t6_ro0_layer::t6_x0_layer;
use t6_x0_layer::*;
use t6_x0_layer::t6_p0_layer;
use t6_p0_layer::t6_m0_layer;
use t6_m0_layer::*;
use t6_m0_layer::t6_a1_layer;
use t6_a1_layer::t6_a0_layer;
use t6_a0_layer::*;
use t6_a0_layer::t6_s0_layer;
use t6_s0_layer::t6_c0_layer;
use t6_c0_layer::t6_e0_layer;
use t6_e0_layer::t6_d0_layer;
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

// T6-DD3 gives DD2 an independently executed keyed protected service. A key
// can acquire one decision. Any later call for the same key can return only
// the memoized decision, without another protected mutation.

#[derive(PartialEq, Eq)]
pub struct DD3ProtectedCall {
    pub request: replay_layer::RequestId,
    pub attempt: replay_layer::AttemptId,
    pub stable_key: replay_layer::StableKey,
    pub call: config_layer::CallDescriptor,
    pub journal_cut: nat,
    pub ack_cut: nat,
    pub source_index: nat,
}

#[derive(PartialEq, Eq)]
pub struct DD3ProtectedDecision {
    pub stable_key: replay_layer::StableKey,
    pub call_ref: nat,
    pub decision: DDDecision,
}

#[allow(inconsistent_fields)]
#[derive(PartialEq, Eq)]
pub enum DD3ProtectedEvent {
    BrokerInvoke { call: DD3ProtectedCall },
    ServiceDecide { call_ref: nat, decision: DDDecision },
    ServiceReturn {
        call_ref: nat,
        observation: replay_layer::Observation,
    },
    Stutter,
}

pub struct DD3ProtectedState {
    pub request: replay_layer::RequestId,
    pub stable_key: replay_layer::StableKey,
    pub initial_slot: Option<replay_layer::Value>,
    pub slot: Option<replay_layer::Value>,
    pub calls: Seq<DD3ProtectedCall>,
    pub decisions: Seq<DD3ProtectedDecision>,
    pub completed_refs: ISet<nat>,
}

pub struct DD3ProtectedExecution {
    pub configs: Seq<DD3ProtectedState>,
    pub events: Seq<DD3ProtectedEvent>,
}

pub open spec fn dd3_call_invocation(
    call: DD3ProtectedCall,
) -> projection_layer::ProtectedInvocation {
    projection_layer::ProtectedInvocation {
        request: call.request,
        attempt: call.attempt,
        call: call.call,
    }
}

pub open spec fn dd3_call_global_event(
    call: DD3ProtectedCall,
) -> global_layer::GlobalEvent {
    global_layer::GlobalEvent::InvokeEvent {
        request: call.request,
        attempt: call.attempt,
        call: call.call,
        journal_cut: call.journal_cut,
        ack_cut: call.ack_cut,
    }
}

pub open spec fn dd3_m0_call(call: DD3ProtectedCall) -> M0ProtectedCall {
    M0ProtectedCall {
        request: call.request,
        attempt: call.attempt,
        call: call.call,
        journal_cut: call.journal_cut,
        ack_cut: call.ack_cut,
        source_index: call.source_index,
    }
}

pub open spec fn dd3_erase_calls(
    calls: Seq<DD3ProtectedCall>,
) -> Seq<projection_layer::ProtectedInvocation>
    decreases calls.len()
{
    if calls.len() == 0 {
        Seq::empty()
    } else {
        dd3_erase_calls(calls.drop_last()).push(
            dd3_call_invocation(calls.last()),
        )
    }
}

pub open spec fn dd3_protected_calls(
    events: Seq<DD3ProtectedEvent>,
) -> Seq<DD3ProtectedCall>
    decreases events.len()
{
    if events.len() == 0 {
        Seq::empty()
    } else {
        let prefix = dd3_protected_calls(events.drop_last());
        match events.last() {
            DD3ProtectedEvent::BrokerInvoke { call } => prefix.push(call),
            DD3ProtectedEvent::ServiceDecide { .. }
            | DD3ProtectedEvent::ServiceReturn { .. }
            | DD3ProtectedEvent::Stutter => prefix,
        }
    }
}

pub open spec fn dd3_protected_trace(
    events: Seq<DD3ProtectedEvent>,
) -> Seq<projection_layer::ProtectedInvocation> {
    dd3_erase_calls(dd3_protected_calls(events))
}

pub open spec fn dd3_initial_protected_state(
    request: replay_layer::RequestId,
    stable_key: replay_layer::StableKey,
    initial_slot: Option<replay_layer::Value>,
) -> DD3ProtectedState {
    DD3ProtectedState {
        request,
        stable_key,
        initial_slot,
        slot: initial_slot,
        calls: Seq::empty(),
        decisions: Seq::empty(),
        completed_refs: ISet::empty(),
    }
}

pub open spec fn dd3_call_key_fresh(
    calls: Seq<DD3ProtectedCall>,
    request: replay_layer::RequestId,
    attempt: replay_layer::AttemptId,
) -> bool {
    forall|call_ref: nat| call_ref < calls.len() ==>
        #[trigger] calls[call_ref as int].request != request
            || calls[call_ref as int].attempt != attempt
}

pub open spec fn dd3_key_is_undecided(
    decisions: Seq<DD3ProtectedDecision>,
    key: replay_layer::StableKey,
) -> bool {
    forall|decision_ref: nat| decision_ref < decisions.len() ==>
        #[trigger] decisions[decision_ref as int].stable_key != key
}

pub open spec fn dd3_observation_matches_memo(
    decisions: Seq<DD3ProtectedDecision>,
    key: replay_layer::StableKey,
    observation: replay_layer::Observation,
) -> bool {
    exists|decision_ref: nat| {
        &&& decision_ref < decisions.len()
        &&& #[trigger] decisions[decision_ref as int].stable_key == key
        &&& match (
            decisions[decision_ref as int].decision,
            observation,
        ) {
            (
                DDDecision::Applied { value: decided },
                replay_layer::Observation::Success(observed),
            ) => decided == observed,
            (
                DDDecision::Rejected,
                replay_layer::Observation::Failure,
            ) => true,
            (DDDecision::Applied { .. }, _)
            | (DDDecision::Rejected, _) => false,
        }
    }
}

pub open spec fn dd3_protected_enabled(
    state: DD3ProtectedState,
    event: DD3ProtectedEvent,
) -> bool {
    match event {
        DD3ProtectedEvent::BrokerInvoke { call } => {
            &&& call.request == state.request
            &&& call.stable_key == state.stable_key
            &&& dd3_call_key_fresh(
                state.calls, call.request, call.attempt,
            )
        },
        DD3ProtectedEvent::ServiceDecide { call_ref, decision } => {
            &&& call_ref < state.calls.len()
            &&& state.calls[call_ref as int].request == state.request
            &&& state.calls[call_ref as int].stable_key == state.stable_key
            &&& !state.completed_refs.contains(call_ref)
            &&& dd3_key_is_undecided(state.decisions, state.stable_key)
            &&& match decision {
                DDDecision::Applied { value } => value.id == 1,
                DDDecision::Rejected => true,
            }
        },
        DD3ProtectedEvent::ServiceReturn { call_ref, observation } => {
            &&& call_ref < state.calls.len()
            &&& !state.completed_refs.contains(call_ref)
            &&& dd3_observation_matches_memo(
                state.decisions,
                state.calls[call_ref as int].stable_key,
                observation,
            )
        },
        DD3ProtectedEvent::Stutter => true,
    }
}

pub open spec fn dd3_protected_apply(
    state: DD3ProtectedState,
    event: DD3ProtectedEvent,
) -> DD3ProtectedState {
    match event {
        DD3ProtectedEvent::BrokerInvoke { call } => DD3ProtectedState {
            calls: state.calls.push(call),
            ..state
        },
        DD3ProtectedEvent::ServiceDecide { call_ref, decision } => {
            DD3ProtectedState {
                slot: match decision {
                    DDDecision::Applied { value } => Option::Some(value),
                    DDDecision::Rejected => state.slot,
                },
                decisions: state.decisions.push(DD3ProtectedDecision {
                    stable_key: state.stable_key,
                    call_ref,
                    decision,
                }),
                ..state
            }
        },
        DD3ProtectedEvent::ServiceReturn { call_ref, .. } => {
            DD3ProtectedState {
                completed_refs: state.completed_refs.insert(call_ref),
                ..state
            }
        },
        DD3ProtectedEvent::Stutter => state,
    }
}

pub open spec fn dd3_protected_step(
    before: DD3ProtectedState,
    event: DD3ProtectedEvent,
    after: DD3ProtectedState,
) -> bool {
    dd3_protected_enabled(before, event)
        && after == dd3_protected_apply(before, event)
}

pub open spec fn dd3_protected_exec(
    request: replay_layer::RequestId,
    stable_key: replay_layer::StableKey,
    initial_slot: Option<replay_layer::Value>,
    execution: DD3ProtectedExecution,
) -> bool {
    execution.configs.len() == execution.events.len() + 1
        && execution.configs[0]
            == dd3_initial_protected_state(request, stable_key, initial_slot)
        && forall|index: nat| index < execution.events.len() ==>
            #[trigger] dd3_protected_step(
                execution.configs[index as int],
                execution.events[index as int],
                execution.configs[(index + 1) as int],
            )
}

pub open spec fn dd3_protected_execution_prefix(
    execution: DD3ProtectedExecution,
    length: nat,
) -> DD3ProtectedExecution {
    DD3ProtectedExecution {
        configs: execution.configs.take((length + 1) as int),
        events: execution.events.take(length as int),
    }
}

pub open spec fn dd3_slot_changed(
    before: DD3ProtectedState,
    after: DD3ProtectedState,
) -> bool {
    before.slot != after.slot
}

pub proof fn dd3_slot_change_requires_decision(
    before: DD3ProtectedState,
    event: DD3ProtectedEvent,
    after: DD3ProtectedState,
)
    requires dd3_protected_step(before, event, after),
    ensures dd3_slot_changed(before, after) ==> match event {
        DD3ProtectedEvent::ServiceDecide {
            call_ref,
            decision: DDDecision::Applied { value },
        } => {
            &&& call_ref < before.calls.len()
            &&& before.calls[call_ref as int].stable_key == before.stable_key
            &&& dd3_key_is_undecided(before.decisions, before.stable_key)
            &&& after.slot == Option::Some(value)
        },
        DD3ProtectedEvent::BrokerInvoke { .. }
        | DD3ProtectedEvent::ServiceDecide {
            decision: DDDecision::Rejected, ..
        }
        | DD3ProtectedEvent::ServiceReturn { .. }
        | DD3ProtectedEvent::Stutter => false,
    },
{
    match event {
        DD3ProtectedEvent::BrokerInvoke { .. }
        | DD3ProtectedEvent::ServiceReturn { .. }
        | DD3ProtectedEvent::Stutter => {},
        DD3ProtectedEvent::ServiceDecide { decision, .. } => {
            match decision {
                DDDecision::Applied { .. } => {},
                DDDecision::Rejected => {},
            }
        },
    }
}

pub open spec fn dd3_event_coupled(
    adapter_before: DDAdapterState,
    adapter_event: DDAdapterEvent,
    protected_before: DD3ProtectedState,
    protected_event: DD3ProtectedEvent,
) -> bool {
    match adapter_event {
        DDAdapterEvent::Observe {
            event: global_layer::GlobalEvent::InvokeEvent {
                request, attempt, call, journal_cut, ack_cut,
            },
        } => protected_event == DD3ProtectedEvent::BrokerInvoke {
            call: DD3ProtectedCall {
                request,
                attempt,
                stable_key: protected_before.stable_key,
                call,
                journal_cut,
                ack_cut,
                source_index: adapter_before.globals.len(),
            },
        },
        DDAdapterEvent::Observe {
            event: global_layer::GlobalEvent::DeliverEvent {
                request, attempt, observation, ..
            },
        } => exists|call_ref: nat| {
            &&& call_ref < protected_before.calls.len()
            &&& protected_before.calls[call_ref as int].request == request
            &&& protected_before.calls[call_ref as int].attempt == attempt
            &&& protected_event == DD3ProtectedEvent::ServiceReturn {
                call_ref,
                observation,
            }
        },
        DDAdapterEvent::ServiceDecide { decision } => {
            exists|call_ref: nat| {
                &&& call_ref < protected_before.calls.len()
                &&& protected_before.calls[call_ref as int].request
                    == adapter_before.request
                &&& adapter_before.active.is_some()
                &&& protected_before.calls[call_ref as int].attempt
                    == adapter_before.active.unwrap()
                &&& protected_event == DD3ProtectedEvent::ServiceDecide {
                    call_ref,
                    decision,
                }
            }
        },
        DDAdapterEvent::Observe {
            event: global_layer::GlobalEvent::BrokerLinearize { .. },
        }
        | DDAdapterEvent::Observe {
            event: global_layer::GlobalEvent::JournalAppendCall { .. },
        }
        | DDAdapterEvent::Observe {
            event: global_layer::GlobalEvent::JournalAppendLinearize { .. },
        }
        | DDAdapterEvent::Observe {
            event: global_layer::GlobalEvent::JournalAppendReturn { .. },
        }
        | DDAdapterEvent::Observe {
            event: global_layer::GlobalEvent::JournalDiskFull { .. },
        }
        | DDAdapterEvent::Observe {
            event: global_layer::GlobalEvent::WalStage { .. },
        }
        | DDAdapterEvent::Observe {
            event: global_layer::GlobalEvent::WalWriteFull { .. },
        }
        | DDAdapterEvent::Observe {
            event: global_layer::GlobalEvent::WalWriteTorn { .. },
        }
        | DDAdapterEvent::Observe {
            event: global_layer::GlobalEvent::WalFinishTorn { .. },
        }
        | DDAdapterEvent::Observe {
            event: global_layer::GlobalEvent::WalFlushAck { .. },
        }
        | DDAdapterEvent::Observe {
            event: global_layer::GlobalEvent::WalDiskFull { .. },
        }
        | DDAdapterEvent::Observe {
            event: global_layer::GlobalEvent::IgnoreStale { .. },
        }
        | DDAdapterEvent::Observe {
            event: global_layer::GlobalEvent::RetryRelease { .. },
        }
        | DDAdapterEvent::Observe {
            event: global_layer::GlobalEvent::Crash,
        }
        | DDAdapterEvent::Observe {
            event: global_layer::GlobalEvent::BeginScan,
        }
        | DDAdapterEvent::Observe {
            event: global_layer::GlobalEvent::FinishScan,
        }
        | DDAdapterEvent::Observe {
            event: global_layer::GlobalEvent::TruncateTail,
        }
        | DDAdapterEvent::Observe {
            event: global_layer::GlobalEvent::AbortScan,
        }
        | DDAdapterEvent::Observe {
            event: global_layer::GlobalEvent::BeginRecover,
        }
        | DDAdapterEvent::Observe {
            event: global_layer::GlobalEvent::FinishRecover,
        } => protected_event == DD3ProtectedEvent::Stutter,
    }
}

pub open spec fn dd3_coupled_exec(
    request: replay_layer::RequestId,
    stable_key: replay_layer::StableKey,
    initial_slot: Option<replay_layer::Value>,
    adapter: DDAdapterExecution,
    protected: DD3ProtectedExecution,
) -> bool {
    &&& dd_exec(request, initial_slot, adapter)
    &&& dd3_protected_exec(request, stable_key, initial_slot, protected)
    &&& adapter.events.len() == protected.events.len()
    &&& forall|index: nat| index < adapter.events.len() ==>
        #[trigger] dd3_event_coupled(
            adapter.configs[index as int],
            adapter.events[index as int],
            protected.configs[index as int],
            protected.events[index as int],
        )
}

pub open spec fn dd3_event_trace_match(
    adapter_event: DDAdapterEvent,
    protected_event: DD3ProtectedEvent,
) -> bool {
    match adapter_event {
        DDAdapterEvent::Observe {
            event: global_layer::GlobalEvent::InvokeEvent {
                request, attempt, call, ..
            },
        } => match protected_event {
            DD3ProtectedEvent::BrokerInvoke { call: protected_call } => {
                &&& protected_call.request == request
                &&& protected_call.attempt == attempt
                &&& protected_call.call == call
            },
            DD3ProtectedEvent::ServiceDecide { .. }
            | DD3ProtectedEvent::ServiceReturn { .. }
            | DD3ProtectedEvent::Stutter => false,
        },
        DDAdapterEvent::Observe {
            event: global_layer::GlobalEvent::BrokerLinearize { .. },
        }
        | DDAdapterEvent::Observe {
            event: global_layer::GlobalEvent::JournalAppendCall { .. },
        }
        | DDAdapterEvent::Observe {
            event: global_layer::GlobalEvent::JournalAppendLinearize { .. },
        }
        | DDAdapterEvent::Observe {
            event: global_layer::GlobalEvent::JournalAppendReturn { .. },
        }
        | DDAdapterEvent::Observe {
            event: global_layer::GlobalEvent::JournalDiskFull { .. },
        }
        | DDAdapterEvent::Observe {
            event: global_layer::GlobalEvent::WalStage { .. },
        }
        | DDAdapterEvent::Observe {
            event: global_layer::GlobalEvent::WalWriteFull { .. },
        }
        | DDAdapterEvent::Observe {
            event: global_layer::GlobalEvent::WalWriteTorn { .. },
        }
        | DDAdapterEvent::Observe {
            event: global_layer::GlobalEvent::WalFinishTorn { .. },
        }
        | DDAdapterEvent::Observe {
            event: global_layer::GlobalEvent::WalFlushAck { .. },
        }
        | DDAdapterEvent::Observe {
            event: global_layer::GlobalEvent::WalDiskFull { .. },
        }
        | DDAdapterEvent::Observe {
            event: global_layer::GlobalEvent::DeliverEvent { .. },
        }
        | DDAdapterEvent::Observe {
            event: global_layer::GlobalEvent::IgnoreStale { .. },
        }
        | DDAdapterEvent::Observe {
            event: global_layer::GlobalEvent::RetryRelease { .. },
        }
        | DDAdapterEvent::Observe {
            event: global_layer::GlobalEvent::Crash,
        }
        | DDAdapterEvent::Observe {
            event: global_layer::GlobalEvent::BeginScan,
        }
        | DDAdapterEvent::Observe {
            event: global_layer::GlobalEvent::FinishScan,
        }
        | DDAdapterEvent::Observe {
            event: global_layer::GlobalEvent::TruncateTail,
        }
        | DDAdapterEvent::Observe {
            event: global_layer::GlobalEvent::AbortScan,
        }
        | DDAdapterEvent::Observe {
            event: global_layer::GlobalEvent::BeginRecover,
        }
        | DDAdapterEvent::Observe {
            event: global_layer::GlobalEvent::FinishRecover,
        }
        | DDAdapterEvent::ServiceDecide { .. } => match protected_event {
            DD3ProtectedEvent::BrokerInvoke { .. } => false,
            DD3ProtectedEvent::ServiceDecide { .. }
            | DD3ProtectedEvent::ServiceReturn { .. }
            | DD3ProtectedEvent::Stutter => true,
        },
    }
}

pub proof fn dd3_event_coupling_implies_trace_match(
    adapter_before: DDAdapterState,
    adapter_event: DDAdapterEvent,
    protected_before: DD3ProtectedState,
    protected_event: DD3ProtectedEvent,
)
    requires dd3_event_coupled(
        adapter_before, adapter_event, protected_before, protected_event,
    ),
    ensures dd3_event_trace_match(adapter_event, protected_event),
{
    match adapter_event {
        DDAdapterEvent::Observe {
            event: global_layer::GlobalEvent::InvokeEvent { .. },
        } => {},
        DDAdapterEvent::Observe { .. }
        | DDAdapterEvent::ServiceDecide { .. } => {},
    }
}

proof fn dd3_erase_calls_push(
    calls: Seq<DD3ProtectedCall>,
    call: DD3ProtectedCall,
)
    ensures dd3_erase_calls(calls.push(call))
        == dd3_erase_calls(calls).push(dd3_call_invocation(call)),
{
    assert(calls.push(call).drop_last() =~= calls);
}

proof fn dd3_protected_calls_push(
    events: Seq<DD3ProtectedEvent>,
    event: DD3ProtectedEvent,
)
    ensures dd3_protected_calls(events.push(event)) == match event {
        DD3ProtectedEvent::BrokerInvoke { call } => {
            dd3_protected_calls(events).push(call)
        },
        DD3ProtectedEvent::ServiceDecide { .. }
        | DD3ProtectedEvent::ServiceReturn { .. }
        | DD3ProtectedEvent::Stutter => dd3_protected_calls(events),
    },
{
    assert(events.push(event).drop_last() =~= events);
}

proof fn dd3_global_trace_push(
    events: Seq<DDAdapterEvent>,
    event: DDAdapterEvent,
)
    ensures dd_global_trace(events.push(event)) == match event {
        DDAdapterEvent::Observe { event: global } => {
            dd_global_trace(events).push(global)
        },
        DDAdapterEvent::ServiceDecide { .. } => dd_global_trace(events),
    },
{
    assert(events.push(event).drop_last() =~= events);
}

pub proof fn dd3_trace_coupling_derives_mediation(
    adapter_events: Seq<DDAdapterEvent>,
    protected_events: Seq<DD3ProtectedEvent>,
)
    requires
        adapter_events.len() == protected_events.len(),
        forall|index: nat| index < adapter_events.len() ==>
            #[trigger] dd3_event_trace_match(
                adapter_events[index as int],
                protected_events[index as int],
            ),
    ensures dd3_protected_trace(protected_events)
        == projection_layer::pi_invocations(dd_global_trace(adapter_events)),
    decreases adapter_events.len(),
{
    if adapter_events.len() == 0 {
        assert(protected_events.len() == 0);
    } else {
        let adapter_prefix = adapter_events.drop_last();
        let protected_prefix = protected_events.drop_last();
        assert(adapter_prefix.len() == protected_prefix.len());
        assert forall|index: nat| index < adapter_prefix.len() implies
            #[trigger] dd3_event_trace_match(
                adapter_prefix[index as int],
                protected_prefix[index as int],
            ) by {
            assert(index < adapter_events.len());
            assert(adapter_prefix[index as int]
                == adapter_events[index as int]);
            assert(protected_prefix[index as int]
                == protected_events[index as int]);
        }
        dd3_trace_coupling_derives_mediation(
            adapter_prefix, protected_prefix,
        );
        let adapter_last = adapter_events.last();
        let protected_last = protected_events.last();
        assert(dd3_event_trace_match(adapter_last, protected_last));
        assert(adapter_events =~= adapter_prefix.push(adapter_last));
        assert(protected_events =~= protected_prefix.push(protected_last));
        dd3_global_trace_push(adapter_prefix, adapter_last);
        dd3_protected_calls_push(protected_prefix, protected_last);
        match adapter_last {
            DDAdapterEvent::Observe {
                event: global @ global_layer::GlobalEvent::InvokeEvent { .. },
            } => {
                m0_pi_invocations_push(dd_global_trace(adapter_prefix), global);
                match protected_last {
                    DD3ProtectedEvent::BrokerInvoke { call } => {
                        dd3_erase_calls_push(
                            dd3_protected_calls(protected_prefix), call,
                        );
                    },
                    DD3ProtectedEvent::ServiceDecide { .. }
                    | DD3ProtectedEvent::ServiceReturn { .. }
                    | DD3ProtectedEvent::Stutter => {},
                }
            },
            DDAdapterEvent::Observe { event: global } => {
                m0_pi_invocations_push(dd_global_trace(adapter_prefix), global);
            },
            DDAdapterEvent::ServiceDecide { .. } => {},
        }
    }
}

pub proof fn dd3_protected_exec_prefix(
    request: replay_layer::RequestId,
    stable_key: replay_layer::StableKey,
    initial_slot: Option<replay_layer::Value>,
    execution: DD3ProtectedExecution,
    length: nat,
)
    requires
        dd3_protected_exec(request, stable_key, initial_slot, execution),
        length <= execution.events.len(),
    ensures dd3_protected_exec(
        request,
        stable_key,
        initial_slot,
        dd3_protected_execution_prefix(execution, length),
    ),
{
    let prefix = dd3_protected_execution_prefix(execution, length);
    assert(prefix.events.len() == length);
    assert(prefix.configs.len() == length + 1);
    assert(prefix.configs[0] == execution.configs[0]);
    assert forall|index: nat| index < prefix.events.len() implies
        #[trigger] dd3_protected_step(
            prefix.configs[index as int],
            prefix.events[index as int],
            prefix.configs[(index + 1) as int],
        ) by {
        assert(index < execution.events.len());
        assert(prefix.events[index as int]
            == execution.events[index as int]);
        assert(prefix.configs[index as int]
            == execution.configs[index as int]);
        assert(prefix.configs[(index + 1) as int]
            == execution.configs[(index + 1) as int]);
    }
}

pub proof fn dd3_protected_exec_final_calls_are_generated(
    request: replay_layer::RequestId,
    stable_key: replay_layer::StableKey,
    initial_slot: Option<replay_layer::Value>,
    execution: DD3ProtectedExecution,
)
    requires dd3_protected_exec(
        request, stable_key, initial_slot, execution,
    ),
    ensures execution.configs[execution.events.len() as int].calls
        == dd3_protected_calls(execution.events),
    decreases execution.events.len(),
{
    if execution.events.len() == 0 {
        assert(execution.configs[0]
            == dd3_initial_protected_state(
                request, stable_key, initial_slot,
            ));
    } else {
        let last_index: nat = (execution.events.len() - 1) as nat;
        let prefix = dd3_protected_execution_prefix(execution, last_index);
        dd3_protected_exec_prefix(
            request, stable_key, initial_slot, execution, last_index,
        );
        dd3_protected_exec_final_calls_are_generated(
            request, stable_key, initial_slot, prefix,
        );
        let before = execution.configs[last_index as int];
        let event = execution.events[last_index as int];
        let after = execution.configs[(last_index + 1) as int];
        assert(prefix.events =~= execution.events.drop_last());
        assert(dd3_protected_step(before, event, after));
        dd3_protected_calls_push(prefix.events, event);
        assert(execution.events =~= prefix.events.push(event));
    }
}

pub proof fn dd3_coupled_exec_derives_complete_mediation(
    request: replay_layer::RequestId,
    stable_key: replay_layer::StableKey,
    initial_slot: Option<replay_layer::Value>,
    adapter: DDAdapterExecution,
    protected: DD3ProtectedExecution,
)
    requires dd3_coupled_exec(
        request, stable_key, initial_slot, adapter, protected,
    ),
    ensures
        protected.configs[protected.events.len() as int].calls
            == dd3_protected_calls(protected.events),
        dd3_erase_calls(
            protected.configs[protected.events.len() as int].calls,
        ) == projection_layer::pi_invocations(
            dd_global_trace(adapter.events),
        ),
        projection_layer::complete_mediation(
            dd_global_trace(adapter.events),
            dd3_erase_calls(
                protected.configs[protected.events.len() as int].calls,
            ),
        ),
{
    assert forall|index: nat| index < adapter.events.len() implies
        #[trigger] dd3_event_trace_match(
            adapter.events[index as int],
            protected.events[index as int],
        ) by {
        dd3_event_coupling_implies_trace_match(
            adapter.configs[index as int],
            adapter.events[index as int],
            protected.configs[index as int],
            protected.events[index as int],
        );
    }
    dd3_trace_coupling_derives_mediation(
        adapter.events, protected.events,
    );
    dd3_protected_exec_final_calls_are_generated(
        request, stable_key, initial_slot, protected,
    );
}

pub open spec fn dd3_call_one() -> DD3ProtectedCall {
    let cfg = dd_full_config();
    let request = dd_request_zero();
    DD3ProtectedCall {
        request,
        attempt: 1,
        stable_key: dd2_key(),
        call: config_layer::canonical_call(cfg, request),
        journal_cut: 4,
        ack_cut: 4,
        source_index: 12,
    }
}

pub open spec fn dd3_call_two() -> DD3ProtectedCall {
    let cfg = dd_full_config();
    let request = dd_request_zero();
    DD3ProtectedCall {
        request,
        attempt: 2,
        stable_key: dd2_key(),
        call: config_layer::canonical_call(cfg, request),
        journal_cut: 5,
        ack_cut: 5,
        source_index: 22,
    }
}

pub open spec fn dd3_zero_protected_execution(
    request: replay_layer::RequestId,
    stable_key: replay_layer::StableKey,
    initial_slot: Option<replay_layer::Value>,
) -> DD3ProtectedExecution {
    DD3ProtectedExecution {
        configs: Seq::empty().push(dd3_initial_protected_state(
            request, stable_key, initial_slot,
        )),
        events: Seq::empty(),
    }
}

pub proof fn dd3_zero_protected_execution_exec(
    request: replay_layer::RequestId,
    stable_key: replay_layer::StableKey,
    initial_slot: Option<replay_layer::Value>,
)
    ensures dd3_protected_exec(
        request,
        stable_key,
        initial_slot,
        dd3_zero_protected_execution(request, stable_key, initial_slot),
    ),
{
}

pub open spec fn dd3_extend_protected_execution(
    execution: DD3ProtectedExecution,
    event: DD3ProtectedEvent,
) -> DD3ProtectedExecution {
    DD3ProtectedExecution {
        configs: execution.configs.push(dd3_protected_apply(
            execution.configs.last(), event,
        )),
        events: execution.events.push(event),
    }
}

pub proof fn dd3_extend_protected_execution_exec(
    request: replay_layer::RequestId,
    stable_key: replay_layer::StableKey,
    initial_slot: Option<replay_layer::Value>,
    execution: DD3ProtectedExecution,
    event: DD3ProtectedEvent,
)
    requires
        dd3_protected_exec(
            request, stable_key, initial_slot, execution,
        ),
        dd3_protected_enabled(execution.configs.last(), event),
    ensures dd3_protected_exec(
        request,
        stable_key,
        initial_slot,
        dd3_extend_protected_execution(execution, event),
    ),
{
    let extended = dd3_extend_protected_execution(execution, event);
    let old_len = execution.events.len();
    assert(extended.configs.len() == extended.events.len() + 1);
    assert(extended.configs[0] == execution.configs[0]);
    assert forall|index: nat| index < extended.events.len() implies
        #[trigger] dd3_protected_step(
            extended.configs[index as int],
            extended.events[index as int],
            extended.configs[(index + 1) as int],
        ) by {
        if index < old_len {
            assert(extended.events[index as int]
                == execution.events[index as int]);
            assert(extended.configs[index as int]
                == execution.configs[index as int]);
            assert(extended.configs[(index + 1) as int]
                == execution.configs[(index + 1) as int]);
        } else {
            assert(index == old_len);
            assert(extended.events[index as int] == event);
            assert(extended.configs[index as int]
                == execution.configs.last());
            assert(extended.configs[(index + 1) as int]
                == dd3_protected_apply(execution.configs.last(), event));
        }
    }
}

pub open spec fn dd3_append_stutters(
    execution: DD3ProtectedExecution,
    count: nat,
) -> DD3ProtectedExecution
    decreases count
{
    if count == 0 {
        execution
    } else {
        dd3_append_stutters(
            dd3_extend_protected_execution(
                execution, DD3ProtectedEvent::Stutter,
            ),
            (count - 1) as nat,
        )
    }
}

pub proof fn dd3_append_stutters_exec(
    request: replay_layer::RequestId,
    stable_key: replay_layer::StableKey,
    initial_slot: Option<replay_layer::Value>,
    execution: DD3ProtectedExecution,
    count: nat,
)
    requires dd3_protected_exec(
        request, stable_key, initial_slot, execution,
    ),
    ensures
        dd3_protected_exec(
            request,
            stable_key,
            initial_slot,
            dd3_append_stutters(execution, count),
        ),
        dd3_append_stutters(execution, count).events.len()
            == execution.events.len() + count,
        dd3_append_stutters(execution, count).configs.last().calls
            == execution.configs.last().calls,
        dd3_append_stutters(execution, count).configs.last().decisions
            == execution.configs.last().decisions,
        dd3_append_stutters(execution, count).configs.last().slot
            == execution.configs.last().slot,
        dd3_append_stutters(execution, count).configs.last().completed_refs
            == execution.configs.last().completed_refs,
        dd3_append_stutters(execution, count).configs.last().request
            == execution.configs.last().request,
        dd3_append_stutters(execution, count).configs.last().stable_key
            == execution.configs.last().stable_key,
        dd3_append_stutters(execution, count).configs.last().initial_slot
            == execution.configs.last().initial_slot,
    decreases count,
{
    if count > 0 {
        let extended = dd3_extend_protected_execution(
            execution, DD3ProtectedEvent::Stutter,
        );
        dd3_extend_protected_execution_exec(
            request,
            stable_key,
            initial_slot,
            execution,
            DD3ProtectedEvent::Stutter,
        );
        dd3_append_stutters_exec(
            request,
            stable_key,
            initial_slot,
            extended,
            (count - 1) as nat,
        );
    }
}

pub open spec fn dd3_protected_execution() -> DD3ProtectedExecution {
    let request = dd_request_zero();
    let key = dd2_key();
    let initial = Option::<replay_layer::Value>::None;
    let p0 = dd3_zero_protected_execution(request, key, initial);
    let p1 = dd3_append_stutters(p0, 12);
    let p2 = dd3_extend_protected_execution(
        p1,
        DD3ProtectedEvent::BrokerInvoke { call: dd3_call_one() },
    );
    let p3 = dd3_extend_protected_execution(
        p2,
        DD3ProtectedEvent::ServiceDecide {
            call_ref: 0,
            decision: DDDecision::Applied { value: dd2_value() },
        },
    );
    let p4 = dd3_append_stutters(p3, 9);
    let p5 = dd3_extend_protected_execution(
        p4,
        DD3ProtectedEvent::BrokerInvoke { call: dd3_call_two() },
    );
    let p6 = dd3_extend_protected_execution(
        p5,
        DD3ProtectedEvent::ServiceReturn {
            call_ref: 1,
            observation: replay_layer::Observation::Success(dd2_value()),
        },
    );
    dd3_append_stutters(p6, 6)
}

pub proof fn dd3_protected_execution_exec()
    ensures
        dd3_protected_exec(
            dd_request_zero(),
            dd2_key(),
            Option::None,
            dd3_protected_execution(),
        ),
        dd3_protected_execution().events.len() == 31,
        dd3_protected_execution().configs.last().calls
            == Seq::empty().push(dd3_call_one()).push(dd3_call_two()),
        dd3_protected_execution().configs.last().decisions
            == Seq::empty().push(DD3ProtectedDecision {
                stable_key: dd2_key(),
                call_ref: 0,
                decision: DDDecision::Applied { value: dd2_value() },
            }),
        dd3_protected_execution().configs.last().slot
            == Option::Some(dd2_value()),
        dd3_protected_execution().configs.last().completed_refs.contains(1),
        !dd3_protected_execution().configs.last().completed_refs.contains(0),
{
    let request = dd_request_zero();
    let key = dd2_key();
    let initial = Option::<replay_layer::Value>::None;
    let p0 = dd3_zero_protected_execution(request, key, initial);
    dd3_zero_protected_execution_exec(request, key, initial);
    let p1 = dd3_append_stutters(p0, 12);
    dd3_append_stutters_exec(request, key, initial, p0, 12);
    let invoke1 = DD3ProtectedEvent::BrokerInvoke {
        call: dd3_call_one(),
    };
    assert(p1.configs.last().request == request);
    assert(p1.configs.last().stable_key == key);
    assert(dd3_call_one().request == request);
    assert(dd3_call_one().stable_key == key);
    assert(dd3_call_key_fresh(
        p1.configs.last().calls,
        dd3_call_one().request,
        dd3_call_one().attempt,
    )) by {
        assert forall|call_ref: nat|
            call_ref < p1.configs.last().calls.len() implies
            p1.configs.last().calls[call_ref as int].request
                != dd3_call_one().request
                || p1.configs.last().calls[call_ref as int].attempt
                    != dd3_call_one().attempt by {
        }
    }
    assert(dd3_protected_enabled(p1.configs.last(), invoke1));
    let p2 = dd3_extend_protected_execution(p1, invoke1);
    dd3_extend_protected_execution_exec(
        request, key, initial, p1, invoke1,
    );
    assert(p2.configs.last().calls
        == Seq::empty().push(dd3_call_one()));
    let decide1 = DD3ProtectedEvent::ServiceDecide {
        call_ref: 0,
        decision: DDDecision::Applied { value: dd2_value() },
    };
    assert(dd3_protected_enabled(p2.configs.last(), decide1));
    let p3 = dd3_extend_protected_execution(p2, decide1);
    dd3_extend_protected_execution_exec(
        request, key, initial, p2, decide1,
    );
    assert(p3.configs.last().decisions
        == Seq::empty().push(DD3ProtectedDecision {
            stable_key: key,
            call_ref: 0,
            decision: DDDecision::Applied { value: dd2_value() },
        }));
    assert(p3.configs.last().slot == Option::Some(dd2_value()));
    let p4 = dd3_append_stutters(p3, 9);
    dd3_append_stutters_exec(request, key, initial, p3, 9);
    let invoke2 = DD3ProtectedEvent::BrokerInvoke {
        call: dd3_call_two(),
    };
    assert(p4.configs.last().request == request);
    assert(p4.configs.last().stable_key == key);
    assert(dd3_call_two().request == request);
    assert(dd3_call_two().stable_key == key);
    assert(dd3_call_key_fresh(
        p4.configs.last().calls,
        dd3_call_two().request,
        dd3_call_two().attempt,
    )) by {
        assert forall|call_ref: nat|
            call_ref < p4.configs.last().calls.len() implies
            p4.configs.last().calls[call_ref as int].request
                != dd3_call_two().request
                || p4.configs.last().calls[call_ref as int].attempt
                    != dd3_call_two().attempt by {
            assert(call_ref == 0);
            assert(p4.configs.last().calls[call_ref as int]
                == dd3_call_one());
            assert(dd3_call_one().attempt != dd3_call_two().attempt);
        }
    }
    assert(dd3_protected_enabled(p4.configs.last(), invoke2));
    let p5 = dd3_extend_protected_execution(p4, invoke2);
    dd3_extend_protected_execution_exec(
        request, key, initial, p4, invoke2,
    );
    assert(p5.configs.last().calls
        == Seq::empty().push(dd3_call_one()).push(dd3_call_two()));
    assert(p5.configs.last().decisions
        == Seq::empty().push(DD3ProtectedDecision {
            stable_key: key,
            call_ref: 0,
            decision: DDDecision::Applied { value: dd2_value() },
        }));
    assert(p5.configs.last().calls[1].stable_key == key);
    assert(p5.configs.last().decisions[0].stable_key == key);
    assert(p5.configs.last().decisions[0].decision
        == DDDecision::Applied { value: dd2_value() });
    assert(dd3_observation_matches_memo(
        p5.configs.last().decisions,
        p5.configs.last().calls[1].stable_key,
        replay_layer::Observation::Success(dd2_value()),
    )) by {
        let decision_ref: nat = 0;
    }
    let return2 = DD3ProtectedEvent::ServiceReturn {
        call_ref: 1,
        observation: replay_layer::Observation::Success(dd2_value()),
    };
    assert(dd3_protected_enabled(p5.configs.last(), return2));
    let p6 = dd3_extend_protected_execution(p5, return2);
    dd3_extend_protected_execution_exec(
        request, key, initial, p5, return2,
    );
    dd3_append_stutters_exec(request, key, initial, p6, 6);
}

pub open spec fn dd3_protected_event_shape(
    events: Seq<DD3ProtectedEvent>,
) -> bool {
    &&& events.len() == 31
    &&& forall|index: nat| index < 12 ==>
        events[index as int] == DD3ProtectedEvent::Stutter
    &&& events[12] == DD3ProtectedEvent::BrokerInvoke {
        call: dd3_call_one(),
    }
    &&& events[13] == DD3ProtectedEvent::ServiceDecide {
        call_ref: 0,
        decision: DDDecision::Applied { value: dd2_value() },
    }
    &&& forall|index: nat| 14 <= index && index < 23 ==>
        events[index as int] == DD3ProtectedEvent::Stutter
    &&& events[23] == DD3ProtectedEvent::BrokerInvoke {
        call: dd3_call_two(),
    }
    &&& events[24] == DD3ProtectedEvent::ServiceReturn {
        call_ref: 1,
        observation: replay_layer::Observation::Success(dd2_value()),
    }
    &&& forall|index: nat| 25 <= index && index < 31 ==>
        events[index as int] == DD3ProtectedEvent::Stutter
}

pub proof fn dd3_protected_execution_has_shape()
    ensures dd3_protected_event_shape(dd3_protected_execution().events),
{
    reveal_with_fuel(dd3_append_stutters, 40);
    assert forall|index: nat| index < 12 implies
        dd3_protected_execution().events[index as int]
            == DD3ProtectedEvent::Stutter by {
    }
    assert forall|index: nat| 14 <= index && index < 23 implies
        dd3_protected_execution().events[index as int]
            == DD3ProtectedEvent::Stutter by {
    }
    assert forall|index: nat| 25 <= index && index < 31 implies
        dd3_protected_execution().events[index as int]
            == DD3ProtectedEvent::Stutter by {
    }
}

proof fn dd3_protected_coupling_state_shape()
    ensures
        dd3_protected_execution().configs[12].stable_key == dd2_key(),
        dd3_protected_execution().configs[23].stable_key == dd2_key(),
        dd3_protected_execution().configs[13].calls
            == Seq::empty().push(dd3_call_one()),
        dd3_protected_execution().configs[14].calls
            == Seq::empty().push(dd3_call_one()),
        dd3_protected_execution().configs[24].calls
            == Seq::empty().push(dd3_call_one()).push(dd3_call_two()),
        dd3_protected_execution().configs[24].decisions
            == Seq::empty().push(DD3ProtectedDecision {
                stable_key: dd2_key(),
                call_ref: 0,
                decision: DDDecision::Applied { value: dd2_value() },
            }),
        dd3_protected_execution().configs[24].slot
            == Option::Some(dd2_value()),
{
    reveal_with_fuel(dd3_append_stutters, 40);
}

pub open spec fn dd3_adapter_event_is_stutter(
    event: DDAdapterEvent,
) -> bool {
    match event {
        DDAdapterEvent::Observe { event: global } => {
            !(global is InvokeEvent) && !(global is DeliverEvent)
        },
        DDAdapterEvent::ServiceDecide { .. } => false,
    }
}

proof fn dd3_adapter_stutter_is_coupled(
    adapter_before: DDAdapterState,
    adapter_event: DDAdapterEvent,
    protected_before: DD3ProtectedState,
)
    requires dd3_adapter_event_is_stutter(adapter_event),
    ensures dd3_event_coupled(
        adapter_before,
        adapter_event,
        protected_before,
        DD3ProtectedEvent::Stutter,
    ),
{
    match adapter_event {
        DDAdapterEvent::Observe { event } => {
            match event {
                global_layer::GlobalEvent::InvokeEvent { .. }
                | global_layer::GlobalEvent::DeliverEvent { .. } => {},
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
                | global_layer::GlobalEvent::FinishRecover => {},
            }
        },
        DDAdapterEvent::ServiceDecide { .. } => {},
    }
}

pub open spec fn dd3_adapter_event_shape(
    execution: DDAdapterExecution,
) -> bool {
    &&& execution.events.len() == 31
    &&& forall|index: nat| index < 12 ==>
        dd3_adapter_event_is_stutter(execution.events[index as int])
    &&& execution.events[12] == DDAdapterEvent::Observe {
        event: dd3_call_global_event(dd3_call_one()),
    }
    &&& execution.configs[12].globals.len() == 12
    &&& execution.events[13] == DDAdapterEvent::ServiceDecide {
        decision: DDDecision::Applied { value: dd2_value() },
    }
    &&& execution.configs[13].active == Option::Some(1)
    &&& forall|index: nat| 14 <= index && index < 23 ==>
        dd3_adapter_event_is_stutter(execution.events[index as int])
    &&& execution.events[23] == DDAdapterEvent::Observe {
        event: dd3_call_global_event(dd3_call_two()),
    }
    &&& execution.configs[23].globals.len() == 22
    &&& execution.events[24] == DDAdapterEvent::Observe {
        event: global_layer::GlobalEvent::DeliverEvent {
            request: dd_request_zero(),
            attempt: 2,
            observation: replay_layer::Observation::Success(dd2_value()),
            journal_cut: 5,
        },
    }
    &&& forall|index: nat| 25 <= index && index < 31 ==>
        dd3_adapter_event_is_stutter(execution.events[index as int])
}

proof fn dd3_adapter_extension_preserves_prefix(
    execution: DDAdapterExecution,
    event: DDAdapterEvent,
)
    ensures
        forall|index: nat| index < execution.events.len() ==>
            #[trigger] dd2_extend_adapter_execution(
                execution, event,
            ).events[index as int] == execution.events[index as int],
        forall|index: nat| index < execution.configs.len() ==>
            #[trigger] dd2_extend_adapter_execution(
                execution, event,
            ).configs[index as int] == execution.configs[index as int],
{
}

proof fn dd3_adapter_full_append_preserves_prefix(
    execution: DDAdapterExecution,
    record: replay_layer::JournalRecord,
    cut: nat,
)
    ensures
        forall|index: nat| index < execution.events.len() ==>
            #[trigger] dd2_observe_full_append(
                execution, record, cut,
            ).events[index as int] == execution.events[index as int],
        forall|index: nat| index < execution.configs.len() ==>
            #[trigger] dd2_observe_full_append(
                execution, record, cut,
            ).configs[index as int] == execution.configs[index as int],
{
    let staged = dd2_extend_adapter_execution(
        execution,
        DDAdapterEvent::Observe {
            event: global_layer::GlobalEvent::WalStage { record },
        },
    );
    let written = dd2_extend_adapter_execution(
        staged,
        DDAdapterEvent::Observe {
            event: global_layer::GlobalEvent::WalWriteFull { record },
        },
    );
    dd3_adapter_extension_preserves_prefix(
        execution,
        DDAdapterEvent::Observe {
            event: global_layer::GlobalEvent::WalStage { record },
        },
    );
    dd3_adapter_extension_preserves_prefix(
        staged,
        DDAdapterEvent::Observe {
            event: global_layer::GlobalEvent::WalWriteFull { record },
        },
    );
    dd3_adapter_extension_preserves_prefix(
        written,
        DDAdapterEvent::Observe {
            event: global_layer::GlobalEvent::WalFlushAck { cut },
        },
    );
}

proof fn dd3_adapter_recovery_preserves_prefix(
    execution: DDAdapterExecution,
)
    ensures
        forall|index: nat| index < execution.events.len() ==>
            #[trigger] dd2_observe_recovery(
                execution,
            ).events[index as int] == execution.events[index as int],
        forall|index: nat| index < execution.configs.len() ==>
            #[trigger] dd2_observe_recovery(
                execution,
            ).configs[index as int] == execution.configs[index as int],
{
}

proof fn dd3_adapter_initial_segment_shape()
    ensures
        forall|index: nat| index < 12 ==>
            dd3_adapter_event_is_stutter(
                dd2_adapter_pre_crash_execution().events[index as int],
            ),
        dd2_adapter_pre_crash_execution().events[12]
            == (DDAdapterEvent::Observe {
            event: dd3_call_global_event(dd3_call_one()),
        }),
        dd2_adapter_pre_crash_execution().configs[12].globals.len() == 12,
        dd2_adapter_pre_crash_execution().events[13]
            == (DDAdapterEvent::ServiceDecide {
                decision: DDDecision::Applied { value: dd2_value() },
            }),
        dd2_adapter_pre_crash_execution().configs[13].active
            == Option::Some(1),
{
    dd2_adapter_pre_crash_execution_exec();
    assert forall|index: nat| index < 12 implies
        dd3_adapter_event_is_stutter(
            dd2_adapter_pre_crash_execution().events[index as int],
        ) by {
        if index < 3 {
        } else if index < 6 {
        } else if index < 9 {
        } else {
            assert(index < 12);
        }
    }
}

proof fn dd3_adapter_recovery_segment_shape()
    ensures
        forall|index: nat| 14 <= index && index < 20 ==>
            dd3_adapter_event_is_stutter(
                dd2_adapter_recovered_execution().events[index as int],
            ),
{
    dd2_adapter_pre_crash_execution_exec();
    assert forall|index: nat| 14 <= index && index < 20 implies
        dd3_adapter_event_is_stutter(
            dd2_adapter_recovered_execution().events[index as int],
        ) by {
        if index == 14 {
        } else if index == 15 {
        } else if index == 16 {
        } else if index == 17 {
        } else if index == 18 {
        } else {
            assert(index == 19);
        }
    }
}

proof fn dd3_adapter_retry_segment_shape()
    ensures
        forall|index: nat| 20 <= index && index < 23 ==>
            dd3_adapter_event_is_stutter(
                dd2_adapter_retry_observed_execution().events[index as int],
            ),
        dd2_adapter_retry_observed_execution().events[23]
            == (DDAdapterEvent::Observe {
            event: dd3_call_global_event(dd3_call_two()),
        }),
        dd2_adapter_retry_observed_execution().configs[23].globals.len()
            == 22,
        dd2_adapter_retry_observed_execution().events[24]
            == (DDAdapterEvent::Observe {
            event: global_layer::GlobalEvent::DeliverEvent {
                request: dd_request_zero(),
                attempt: 2,
                observation: replay_layer::Observation::Success(dd2_value()),
                journal_cut: 5,
            },
        }),
{
    let request = dd_request_zero();
    let initial = Option::<replay_layer::Value>::None;
    let recovered = dd2_adapter_recovered_execution();
    let wal = dd2_wal_recovered_execution();
    dd2_adapter_recovered_execution_exec();
    dd2_wal_recovered_execution_exec();
    let cut = wal_runtime_layer::journal_view(
        wal.configs.last(),
    ).len() + 1;
    let started = dd2_observe_full_append(
        recovered, dd2_start_two_record(), cut,
    );
    dd2_observe_full_append_exec(
        request, initial, recovered, dd2_start_two_record(), cut,
    );
    dd1_exec_final_globals_are_projected(request, initial, started);
    assert(started.configs.last().globals.len() == 22);
    assert forall|index: nat| 20 <= index && index < 23 implies
        dd3_adapter_event_is_stutter(
            dd2_adapter_retry_observed_execution().events[index as int],
        ) by {
        if index == 20 {
        } else if index == 21 {
        } else {
            assert(index == 22);
        }
    }
}

proof fn dd3_adapter_terminal_segment_shape()
    ensures forall|index: nat| 25 <= index && index < 31 ==>
        dd3_adapter_event_is_stutter(
            dd2_adapter_execution().events[index as int],
        ),
{
    dd2_adapter_retry_observed_execution_exec();
    assert forall|index: nat| 25 <= index && index < 31 implies
        dd3_adapter_event_is_stutter(
            dd2_adapter_execution().events[index as int],
        ) by {
        if index < 28 {
        } else {
            assert(index < 31);
        }
    }
}

proof fn dd3_adapter_execution_segment_prefixes()
    ensures
        forall|index: nat| index < 14 ==>
            #[trigger] dd2_adapter_execution().events[index as int]
                == dd2_adapter_pre_crash_execution().events[index as int],
        forall|index: nat| index <= 14 ==>
            #[trigger] dd2_adapter_execution().configs[index as int]
                == dd2_adapter_pre_crash_execution().configs[index as int],
        forall|index: nat| 14 <= index && index < 20 ==>
            #[trigger] dd2_adapter_execution().events[index as int]
                == dd2_adapter_recovered_execution().events[index as int],
        forall|index: nat| 20 <= index && index < 25 ==>
            #[trigger] dd2_adapter_execution().events[index as int]
                == dd2_adapter_retry_observed_execution().events[index as int],
        dd2_adapter_execution().configs[23]
            == dd2_adapter_retry_observed_execution().configs[23],
{
    let pre = dd2_adapter_pre_crash_execution();
    let recovered = dd2_adapter_recovered_execution();
    let retry = dd2_adapter_retry_observed_execution();
    let wal_recovered = dd2_wal_recovered_execution();
    let cut5 = wal_runtime_layer::journal_view(
        wal_recovered.configs.last(),
    ).len() + 1;
    let started = dd2_observe_full_append(
        recovered, dd2_start_two_record(), cut5,
    );
    let invoked = dd2_observe_wal_event(started, dd2_invoke_two_wal_event());
    let success = dd2_adapter_success_outcome_execution();
    let final_execution = dd2_adapter_execution();
    dd2_adapter_pre_crash_execution_exec();
    dd2_adapter_recovered_execution_exec();
    dd2_adapter_retry_observed_execution_exec();
    dd3_adapter_recovery_preserves_prefix(pre);
    dd3_adapter_full_append_preserves_prefix(
        recovered, dd2_start_two_record(), cut5,
    );
    dd3_adapter_extension_preserves_prefix(
        started,
        DDAdapterEvent::Observe {
            event: wal_runtime_layer::wal_encode(dd2_invoke_two_wal_event()),
        },
    );
    dd3_adapter_extension_preserves_prefix(
        invoked,
        DDAdapterEvent::Observe {
            event: wal_runtime_layer::wal_encode(dd2_success_two_wal_event()),
        },
    );
    let cut6 = wal_runtime_layer::journal_view(
        dd2_wal_retry_observed_execution().configs.last(),
    ).len() + 1;
    dd3_adapter_full_append_preserves_prefix(
        retry, dd2_success_outcome_record(), cut6,
    );
    let cut7 = wal_runtime_layer::journal_view(
        dd2_wal_success_outcome_execution().configs.last(),
    ).len() + 1;
    dd3_adapter_full_append_preserves_prefix(
        success, dd2_commit_record(), cut7,
    );
    assert forall|index: nat| index < 14 implies
        final_execution.events[index as int] == pre.events[index as int] by {
        assert(recovered.events[index as int] == pre.events[index as int]);
        assert(retry.events[index as int] == recovered.events[index as int]);
        assert(success.events[index as int] == retry.events[index as int]);
        assert(final_execution.events[index as int]
            == success.events[index as int]);
    }
    assert forall|index: nat| index <= 14 implies
        final_execution.configs[index as int] == pre.configs[index as int] by {
        assert(index < pre.configs.len());
        assert(recovered.configs[index as int] == pre.configs[index as int]);
        assert(retry.configs[index as int] == recovered.configs[index as int]);
        assert(success.configs[index as int] == retry.configs[index as int]);
        assert(final_execution.configs[index as int]
            == success.configs[index as int]);
    }
    assert forall|index: nat| 14 <= index && index < 20 implies
        final_execution.events[index as int]
            == recovered.events[index as int] by {
        assert(retry.events[index as int] == recovered.events[index as int]);
        assert(success.events[index as int] == retry.events[index as int]);
        assert(final_execution.events[index as int]
            == success.events[index as int]);
    }
    assert forall|index: nat| 20 <= index && index < 25 implies
        final_execution.events[index as int] == retry.events[index as int] by {
        assert(success.events[index as int] == retry.events[index as int]);
        assert(final_execution.events[index as int]
            == success.events[index as int]);
    }
    assert(final_execution.configs[23] == success.configs[23]);
    assert(success.configs[23] == retry.configs[23]);
}

pub proof fn dd3_adapter_execution_has_shape()
    ensures dd3_adapter_event_shape(dd2_adapter_execution()),
{
    dd2_adapter_execution_exec();
    dd3_adapter_initial_segment_shape();
    dd3_adapter_recovery_segment_shape();
    dd3_adapter_retry_segment_shape();
    dd3_adapter_terminal_segment_shape();
    dd3_adapter_execution_segment_prefixes();
    assert forall|index: nat| index < 12 implies
        dd3_adapter_event_is_stutter(
            dd2_adapter_execution().events[index as int],
        ) by {
    }
    assert forall|index: nat| 14 <= index && index < 23 implies
        dd3_adapter_event_is_stutter(
            dd2_adapter_execution().events[index as int],
        ) by {
        if index < 20 {
        } else {
            assert(index < 23);
        }
    }
}

pub proof fn dd3_adapter_and_service_are_coupled()
    ensures dd3_coupled_exec(
        dd_request_zero(),
        dd2_key(),
        Option::None,
        dd2_adapter_execution(),
        dd3_protected_execution(),
    ),
{
    let request = dd_request_zero();
    let key = dd2_key();
    let initial = Option::<replay_layer::Value>::None;
    let adapter = dd2_adapter_execution();
    let protected = dd3_protected_execution();
    dd2_adapter_execution_exec();
    dd3_protected_execution_exec();
    dd3_protected_execution_has_shape();
    dd3_protected_coupling_state_shape();
    dd3_adapter_execution_has_shape();
    assert(adapter.events.len() == 31);
    assert(protected.events.len() == 31);
    assert forall|index: nat| index < adapter.events.len() implies
        #[trigger] dd3_event_coupled(
            adapter.configs[index as int],
            adapter.events[index as int],
            protected.configs[index as int],
            protected.events[index as int],
        ) by {
        if index < 12 {
            assert(protected.events[index as int]
                == DD3ProtectedEvent::Stutter);
            dd3_adapter_stutter_is_coupled(
                adapter.configs[index as int],
                adapter.events[index as int],
                protected.configs[index as int],
            );
        } else if index == 12 {
            assert(protected.events[index as int]
                == DD3ProtectedEvent::BrokerInvoke {
                    call: dd3_call_one(),
                });
            assert(adapter.configs[index as int].globals.len() == 12);
            assert(protected.configs[index as int].stable_key == key);
        } else if index == 13 {
            assert(protected.events[index as int]
                == DD3ProtectedEvent::ServiceDecide {
                    call_ref: 0,
                    decision: DDDecision::Applied { value: dd2_value() },
                });
            assert(protected.configs[index as int].calls[0]
                == dd3_call_one());
            assert(adapter.configs[index as int].request == request);
            assert(adapter.configs[index as int].active == Option::Some(1));
            assert(exists|call_ref: nat| {
                &&& call_ref < protected.configs[index as int].calls.len()
                &&& protected.configs[index as int].calls[
                    call_ref as int
                ].request == adapter.configs[index as int].request
                &&& adapter.configs[index as int].active.is_some()
                &&& protected.configs[index as int].calls[
                    call_ref as int
                ].attempt == adapter.configs[index as int].active.unwrap()
                &&& protected.events[index as int]
                    == DD3ProtectedEvent::ServiceDecide {
                        call_ref,
                        decision: DDDecision::Applied { value: dd2_value() },
                    }
            }) by {
                let call_ref: nat = 0;
            }
        } else if index < 23 {
            assert(14 <= index);
            assert(protected.events[index as int]
                == DD3ProtectedEvent::Stutter);
            dd3_adapter_stutter_is_coupled(
                adapter.configs[index as int],
                adapter.events[index as int],
                protected.configs[index as int],
            );
        } else if index == 23 {
            assert(protected.events[index as int]
                == DD3ProtectedEvent::BrokerInvoke {
                    call: dd3_call_two(),
                });
            assert(adapter.configs[index as int].globals.len() == 22);
            assert(protected.configs[index as int].stable_key == key);
        } else if index == 24 {
            assert(protected.events[index as int]
                == DD3ProtectedEvent::ServiceReturn {
                    call_ref: 1,
                    observation: replay_layer::Observation::Success(
                        dd2_value(),
                    ),
                });
            assert(protected.configs[index as int].calls[1]
                == dd3_call_two());
            assert(exists|call_ref: nat| {
                &&& call_ref < protected.configs[index as int].calls.len()
                &&& protected.configs[index as int].calls[
                    call_ref as int
                ].request == request
                &&& protected.configs[index as int].calls[
                    call_ref as int
                ].attempt == 2
                &&& protected.events[index as int]
                    == DD3ProtectedEvent::ServiceReturn {
                        call_ref,
                        observation: replay_layer::Observation::Success(
                            dd2_value(),
                        ),
                    }
            }) by {
                let call_ref: nat = 1;
            }
        } else {
            assert(25 <= index && index < 31);
            assert(protected.events[index as int]
                == DD3ProtectedEvent::Stutter);
            dd3_adapter_stutter_is_coupled(
                adapter.configs[index as int],
                adapter.events[index as int],
                protected.configs[index as int],
            );
        }
        assert(dd3_event_coupled(
            adapter.configs[index as int],
            adapter.events[index as int],
            protected.configs[index as int],
            protected.events[index as int],
        ));
    }
}

pub open spec fn dd3_decision_count(
    events: Seq<DD3ProtectedEvent>,
) -> nat
    decreases events.len()
{
    if events.len() == 0 {
        0
    } else {
        dd3_decision_count(events.drop_last()) + match events.last() {
            DD3ProtectedEvent::ServiceDecide { .. } => 1nat,
            DD3ProtectedEvent::BrokerInvoke { .. }
            | DD3ProtectedEvent::ServiceReturn { .. }
            | DD3ProtectedEvent::Stutter => 0nat,
        }
    }
}

pub open spec fn dd3_decision_provenance(
    execution: DD3ProtectedExecution,
) -> bool {
    forall|index: nat| index < execution.events.len() ==> match
        #[trigger] execution.events[index as int]
    {
        DD3ProtectedEvent::ServiceDecide { call_ref, decision } => {
            &&& call_ref < execution.configs[index as int].calls.len()
            &&& execution.configs[index as int].calls[
                call_ref as int
            ].stable_key == execution.configs[index as int].stable_key
            &&& dd3_key_is_undecided(
                execution.configs[index as int].decisions,
                execution.configs[index as int].stable_key,
            )
            &&& execution.configs[(index + 1) as int].decisions
                == execution.configs[index as int].decisions.push(
                    DD3ProtectedDecision {
                        stable_key: execution.configs[index as int].stable_key,
                        call_ref,
                        decision,
                    },
                )
            &&& match decision {
                DDDecision::Applied { value } => {
                    execution.configs[(index + 1) as int].slot
                        == Option::Some(value)
                },
                DDDecision::Rejected => {
                    execution.configs[(index + 1) as int].slot
                        == execution.configs[index as int].slot
                },
            }
        },
        DD3ProtectedEvent::BrokerInvoke { .. }
        | DD3ProtectedEvent::ServiceReturn { .. }
        | DD3ProtectedEvent::Stutter => {
            !dd3_slot_changed(
                execution.configs[index as int],
                execution.configs[(index + 1) as int],
            )
        },
    }
}

pub proof fn dd3_protected_exec_derives_decision_provenance(
    request: replay_layer::RequestId,
    stable_key: replay_layer::StableKey,
    initial_slot: Option<replay_layer::Value>,
    execution: DD3ProtectedExecution,
)
    requires dd3_protected_exec(
        request, stable_key, initial_slot, execution,
    ),
    ensures dd3_decision_provenance(execution),
{
    assert forall|index: nat| index < execution.events.len() implies match
        #[trigger] execution.events[index as int]
    {
        DD3ProtectedEvent::ServiceDecide { call_ref, decision } => {
            &&& call_ref < execution.configs[index as int].calls.len()
            &&& execution.configs[index as int].calls[
                call_ref as int
            ].stable_key == execution.configs[index as int].stable_key
            &&& dd3_key_is_undecided(
                execution.configs[index as int].decisions,
                execution.configs[index as int].stable_key,
            )
            &&& execution.configs[(index + 1) as int].decisions
                == execution.configs[index as int].decisions.push(
                    DD3ProtectedDecision {
                        stable_key: execution.configs[index as int].stable_key,
                        call_ref,
                        decision,
                    },
                )
            &&& match decision {
                DDDecision::Applied { value } => {
                    execution.configs[(index + 1) as int].slot
                        == Option::Some(value)
                },
                DDDecision::Rejected => {
                    execution.configs[(index + 1) as int].slot
                        == execution.configs[index as int].slot
                },
            }
        },
        DD3ProtectedEvent::BrokerInvoke { .. }
        | DD3ProtectedEvent::ServiceReturn { .. }
        | DD3ProtectedEvent::Stutter => {
            !dd3_slot_changed(
                execution.configs[index as int],
                execution.configs[(index + 1) as int],
            )
        },
    } by {
        let before = execution.configs[index as int];
        let event = execution.events[index as int];
        let after = execution.configs[(index + 1) as int];
        assert(dd3_protected_step(before, event, after));
        match event {
            DD3ProtectedEvent::ServiceDecide { .. } => {
                dd3_slot_change_requires_decision(before, event, after);
            },
            DD3ProtectedEvent::BrokerInvoke { .. }
            | DD3ProtectedEvent::ServiceReturn { .. }
            | DD3ProtectedEvent::Stutter => {},
        }
    }
}

pub proof fn dd3_retry_has_one_keyed_decision()
    ensures
        dd3_decision_count(dd3_protected_execution().events) == 1,
        dd3_decision_provenance(dd3_protected_execution()),
        dd3_protected_execution().configs.last().decisions
            == Seq::empty().push(DD3ProtectedDecision {
                stable_key: dd2_key(),
                call_ref: 0,
                decision: DDDecision::Applied { value: dd2_value() },
            }),
        dd3_observation_matches_memo(
            dd3_protected_execution().configs[24].decisions,
            dd3_call_two().stable_key,
            replay_layer::Observation::Success(dd2_value()),
        ),
{
    dd3_protected_execution_exec();
    dd3_protected_execution_has_shape();
    dd3_protected_coupling_state_shape();
    dd3_protected_exec_derives_decision_provenance(
        dd_request_zero(),
        dd2_key(),
        Option::None,
        dd3_protected_execution(),
    );
    reveal_with_fuel(dd3_decision_count, 40);
    assert(dd3_protected_execution().configs[24].decisions
        == Seq::empty().push(DD3ProtectedDecision {
            stable_key: dd2_key(),
            call_ref: 0,
            decision: DDDecision::Applied { value: dd2_value() },
        }));
    assert(dd3_call_two().stable_key == dd2_key());
    assert(dd3_protected_execution().configs[24].decisions[0].stable_key
        == dd3_call_two().stable_key);
    assert(dd3_protected_execution().configs[24].decisions[0].decision
        == DDDecision::Applied { value: dd2_value() });
    assert(dd3_observation_matches_memo(
        dd3_protected_execution().configs[24].decisions,
        dd3_call_two().stable_key,
        replay_layer::Observation::Success(dd2_value()),
    )) by {
        let decision_ref: nat = 0;
    }
}

proof fn dd3_first_call_has_exact_wal_origin()
    ensures
        dd2_wal_execution().events[
            dd3_call_one().source_index as int
        ] == dd3_call_global_event(dd3_call_one()),
{
    dd2_wal_trace_shape();
    assert(dd3_call_one().source_index == 12);
    assert(dd3_call_global_event(dd3_call_one())
        == wal_runtime_layer::wal_encode(dd2_invoke_one_wal_event()));
}

proof fn dd3_second_call_has_exact_wal_origin()
    ensures
        dd2_wal_execution().events[
            dd3_call_two().source_index as int
        ] == dd3_call_global_event(dd3_call_two()),
{
    dd2_wal_trace_shape();
    assert(dd3_call_two().source_index == 22);
    assert(dd3_call_global_event(dd3_call_two())
        == wal_runtime_layer::wal_encode(dd2_invoke_two_wal_event()));
}

pub proof fn dd3_calls_have_exact_wal_origins()
    ensures
        dd2_wal_execution().events[
            dd3_call_one().source_index as int
        ] == dd3_call_global_event(dd3_call_one()),
        dd2_wal_execution().events[
            dd3_call_two().source_index as int
        ] == dd3_call_global_event(dd3_call_two()),
{
    dd3_first_call_has_exact_wal_origin();
    dd3_second_call_has_exact_wal_origin();
}

pub proof fn dd3_calls_are_durably_authorized()
    ensures
        m0_durably_authorized_call(
            dd_full_config(),
            dd2_wal_execution(),
            dd3_m0_call(dd3_call_one()),
        ),
        m0_durably_authorized_call(
            dd_full_config(),
            dd2_wal_execution(),
            dd3_m0_call(dd3_call_two()),
        ),
{
    let cfg = dd_full_config();
    let wal = dd2_wal_execution();
    dd_full_config_is_well_formed();
    dd2_wal_execution_exec();
    dd3_calls_have_exact_wal_origins();
    assert(dd3_m0_call(dd3_call_one()).source_index < wal.events.len());
    assert(dd3_m0_call(dd3_call_two()).source_index < wal.events.len());
    m0_exact_wal_invoke_is_durably_authorized(
        cfg, wal, dd3_m0_call(dd3_call_one()),
    );
    m0_exact_wal_invoke_is_durably_authorized(
        cfg, wal, dd3_m0_call(dd3_call_two()),
    );
}

pub open spec fn dd3_every_decision_durably_authorized(
    cfg: config_layer::FullConfig,
    wal: wal_runtime_layer::WalExecution,
    protected: DD3ProtectedExecution,
) -> bool {
    forall|index: nat| index < protected.events.len() ==> match
        #[trigger] protected.events[index as int]
    {
        DD3ProtectedEvent::ServiceDecide { call_ref, .. } => {
            &&& call_ref < protected.configs[index as int].calls.len()
            &&& m0_durably_authorized_call(
                cfg,
                wal,
                dd3_m0_call(
                    protected.configs[index as int].calls[call_ref as int],
                ),
            )
        },
        DD3ProtectedEvent::BrokerInvoke { .. }
        | DD3ProtectedEvent::ServiceReturn { .. }
        | DD3ProtectedEvent::Stutter => true,
    }
}

pub proof fn dd3_retry_every_decision_is_durably_authorized()
    ensures dd3_every_decision_durably_authorized(
        dd_full_config(),
        dd2_wal_execution(),
        dd3_protected_execution(),
    ),
{
    let protected = dd3_protected_execution();
    dd3_protected_execution_exec();
    dd3_protected_execution_has_shape();
    dd3_protected_coupling_state_shape();
    dd3_calls_are_durably_authorized();
    assert forall|index: nat| index < protected.events.len() implies match
        #[trigger] protected.events[index as int]
    {
        DD3ProtectedEvent::ServiceDecide { call_ref, .. } => {
            &&& call_ref < protected.configs[index as int].calls.len()
            &&& m0_durably_authorized_call(
                dd_full_config(),
                dd2_wal_execution(),
                dd3_m0_call(
                    protected.configs[index as int].calls[call_ref as int],
                ),
            )
        },
        DD3ProtectedEvent::BrokerInvoke { .. }
        | DD3ProtectedEvent::ServiceReturn { .. }
        | DD3ProtectedEvent::Stutter => true,
    } by {
        if index < 12 {
            assert(protected.events[index as int]
                == DD3ProtectedEvent::Stutter);
        } else if index == 12 {
            assert(protected.events[index as int]
                == DD3ProtectedEvent::BrokerInvoke {
                    call: dd3_call_one(),
                });
        } else if index == 13 {
            assert(protected.events[index as int]
                == DD3ProtectedEvent::ServiceDecide {
                    call_ref: 0,
                    decision: DDDecision::Applied { value: dd2_value() },
                });
            assert(protected.configs[index as int].calls[0]
                == dd3_call_one());
            assert(m0_durably_authorized_call(
                dd_full_config(),
                dd2_wal_execution(),
                dd3_m0_call(protected.configs[index as int].calls[0]),
            ));
        } else if index < 23 {
            assert(protected.events[index as int]
                == DD3ProtectedEvent::Stutter);
        } else if index == 23 {
            assert(protected.events[index as int]
                == DD3ProtectedEvent::BrokerInvoke {
                    call: dd3_call_two(),
                });
        } else if index == 24 {
            assert(protected.events[index as int]
                == DD3ProtectedEvent::ServiceReturn {
                    call_ref: 1,
                    observation: replay_layer::Observation::Success(
                        dd2_value(),
                    ),
                });
        } else {
            assert(protected.events[index as int]
                == DD3ProtectedEvent::Stutter);
        }
    }
}

pub closed spec fn dd3_mediation_package(
    adapter: DDAdapterExecution,
    protected: DD3ProtectedExecution,
    wal: wal_runtime_layer::WalExecution,
    plugged: t4_c1_layer::PluggedWalExecution<M0ProtectedHandleState>,
) -> bool {
    let cfg = dd_full_config();
    let final_protected = protected.configs[protected.events.len() as int];
    let final_context = plugged.contexts[plugged.machine.events.len() as int];
    &&& adapter == dd2_adapter_execution()
    &&& protected == dd3_protected_execution()
    &&& wal == dd2_wal_execution()
    &&& plugged == m0_plugged_wal_execution(wal)
    &&& dd3_coupled_exec(
        dd_request_zero(), dd2_key(), Option::None, adapter, protected,
    )
    &&& wal_runtime_layer::exec(cfg, wal)
    &&& dd_global_trace(adapter.events) == wal.events
    &&& t4_c1_layer::storage_parametric_context(
        cfg, m0_exclusive_handle_context(cfg),
    )
    &&& t4_c1_layer::plugged_wal_exec(
        cfg, m0_exclusive_handle_context(cfg), plugged,
    )
    &&& final_protected.calls
        == Seq::empty().push(dd3_call_one()).push(dd3_call_two())
    &&& final_protected.decisions
        == Seq::empty().push(DD3ProtectedDecision {
            stable_key: dd2_key(),
            call_ref: 0,
            decision: DDDecision::Applied { value: dd2_value() },
        })
    &&& final_protected.slot == Option::Some(dd2_value())
    &&& final_protected.completed_refs.contains(1)
    &&& !final_protected.completed_refs.contains(0)
    &&& dd3_erase_calls(final_protected.calls)
        == final_context.invocations
    &&& projection_layer::complete_mediation(
        wal.events, dd3_erase_calls(final_protected.calls),
    )
    &&& projection_layer::complete_mediation(
        wal.events, final_context.invocations,
    )
    &&& dd3_decision_count(protected.events) == 1
    &&& dd3_decision_provenance(protected)
    &&& dd3_observation_matches_memo(
        protected.configs[24].decisions,
        dd3_call_two().stable_key,
        replay_layer::Observation::Success(dd2_value()),
    )
    &&& m0_durably_authorized_call(
        cfg, wal, dd3_m0_call(dd3_call_one()),
    )
    &&& m0_durably_authorized_call(
        cfg, wal, dd3_m0_call(dd3_call_two()),
    )
    &&& dd3_every_decision_durably_authorized(cfg, wal, protected)
    &&& dd2_executable_crash_retry_package()
}

pub proof fn t6_dd3_deduplicated_mediation()
    ensures dd3_mediation_package(
        dd2_adapter_execution(),
        dd3_protected_execution(),
        dd2_wal_execution(),
        m0_plugged_wal_execution(dd2_wal_execution()),
    ),
{
    let cfg = dd_full_config();
    let adapter = dd2_adapter_execution();
    let protected = dd3_protected_execution();
    let wal = dd2_wal_execution();
    let plugged = m0_plugged_wal_execution(wal);
    dd_full_config_is_well_formed();
    t6_dd2_executable_crash_retry_nonvacuity();
    dd2_adapter_execution_exec();
    dd2_wal_execution_exec();
    dd3_protected_execution_exec();
    dd3_adapter_and_service_are_coupled();
    assert(dd_global_trace(adapter.events) == wal.events);
    dd3_coupled_exec_derives_complete_mediation(
        dd_request_zero(),
        dd2_key(),
        Option::None,
        adapter,
        protected,
    );
    assert(projection_layer::complete_mediation(
        wal.events,
        dd3_erase_calls(
            protected.configs[protected.events.len() as int].calls,
        ),
    ));
    m0_exclusive_context_is_storage_parametric(cfg);
    m0_wal_exec_has_exclusive_handle_context(cfg, wal);
    m0_exclusive_context_derives_complete_mediation(cfg, plugged);
    assert(plugged.contexts[wal.events.len() as int].invocations
        == projection_layer::pi_invocations(wal.events));
    assert(dd3_erase_calls(
        protected.configs[protected.events.len() as int].calls,
    ) == plugged.contexts[wal.events.len() as int].invocations);
    dd3_retry_has_one_keyed_decision();
    dd3_calls_are_durably_authorized();
    dd3_retry_every_decision_is_durably_authorized();
    reveal(dd3_mediation_package);
}

pub proof fn t6_dd3_mediation_nonvacuity()
    ensures exists|
        adapter: DDAdapterExecution,
        protected: DD3ProtectedExecution,
        wal: wal_runtime_layer::WalExecution,
        plugged: t4_c1_layer::PluggedWalExecution<
            M0ProtectedHandleState,
        >| #![auto] {
            &&& adapter == dd2_adapter_execution()
            &&& protected == dd3_protected_execution()
            &&& wal == dd2_wal_execution()
            &&& plugged == m0_plugged_wal_execution(wal)
            &&& dd3_mediation_package(adapter, protected, wal, plugged)
        },
{
    t6_dd3_deduplicated_mediation();
    assert(exists|
        adapter: DDAdapterExecution,
        protected: DD3ProtectedExecution,
        wal: wal_runtime_layer::WalExecution,
        plugged: t4_c1_layer::PluggedWalExecution<
            M0ProtectedHandleState,
        >| #![auto] {
            &&& adapter == dd2_adapter_execution()
            &&& protected == dd3_protected_execution()
            &&& wal == dd2_wal_execution()
            &&& plugged == m0_plugged_wal_execution(wal)
            &&& dd3_mediation_package(adapter, protected, wal, plugged)
        }) by {
        let adapter = dd2_adapter_execution();
        let protected = dd3_protected_execution();
        let wal = dd2_wal_execution();
        let plugged = m0_plugged_wal_execution(wal);
    }
}

} // verus!
