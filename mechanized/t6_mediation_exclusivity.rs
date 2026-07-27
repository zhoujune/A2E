use vstd::prelude::*;

#[path = "t6_adapter_executable_refinement.rs"]
pub mod t6_a1_layer;

verus! {

use t6_a1_layer::*;
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
use c1_layer::append_layer;

// T6-M0 makes the protected boundary operational.  Calls retain their exact
// durable cuts, and target effects name a unique previously accepted call by
// sequence index.  The event alphabet deliberately has no raw/context-owned
// protected invocation or target-mutation constructor.

#[derive(PartialEq, Eq)]
pub struct M0ProtectedCall {
    pub request: replay_layer::RequestId,
    pub attempt: replay_layer::AttemptId,
    pub call: config_layer::CallDescriptor,
    pub journal_cut: nat,
    pub ack_cut: nat,
    pub source_index: nat,
}

#[allow(inconsistent_fields)]
#[derive(PartialEq, Eq)]
pub enum M0ProtectedEvent {
    BrokerInvoke { call: M0ProtectedCall },
    ServiceLinearize { call_ref: nat },
    ServiceReturn {
        call_ref: nat,
        observation: replay_layer::Observation,
    },
    EnvironmentAdd { resource: config_layer::Resource },
    Stutter,
}

pub struct M0ProtectedState {
    pub request: replay_layer::RequestId,
    pub initial_members: ISet<config_layer::Resource>,
    pub members: ISet<config_layer::Resource>,
    pub calls: Seq<M0ProtectedCall>,
    pub linearized_refs: ISet<nat>,
    pub completed_refs: ISet<nat>,
    pub environment_additions: ISet<config_layer::Resource>,
}

pub struct M0ProtectedExecution {
    pub configs: Seq<M0ProtectedState>,
    pub events: Seq<M0ProtectedEvent>,
}

pub open spec fn m0_call_invocation(
    call: M0ProtectedCall,
) -> projection_layer::ProtectedInvocation {
    projection_layer::ProtectedInvocation {
        request: call.request,
        attempt: call.attempt,
        call: call.call,
    }
}

pub open spec fn m0_call_global_event(
    call: M0ProtectedCall,
) -> global_layer::GlobalEvent {
    global_layer::GlobalEvent::InvokeEvent {
        request: call.request,
        attempt: call.attempt,
        call: call.call,
        journal_cut: call.journal_cut,
        ack_cut: call.ack_cut,
    }
}

pub open spec fn m0_erase_calls(
    calls: Seq<M0ProtectedCall>,
) -> Seq<projection_layer::ProtectedInvocation>
    decreases calls.len()
{
    if calls.len() == 0 {
        Seq::empty()
    } else {
        m0_erase_calls(calls.drop_last()).push(
            m0_call_invocation(calls.last()),
        )
    }
}

pub open spec fn m0_protected_calls(
    events: Seq<M0ProtectedEvent>,
) -> Seq<M0ProtectedCall>
    decreases events.len()
{
    if events.len() == 0 {
        Seq::empty()
    } else {
        let prefix = m0_protected_calls(events.drop_last());
        match events.last() {
            M0ProtectedEvent::BrokerInvoke { call } => prefix.push(call),
            M0ProtectedEvent::ServiceLinearize { .. }
            | M0ProtectedEvent::ServiceReturn { .. }
            | M0ProtectedEvent::EnvironmentAdd { .. }
            | M0ProtectedEvent::Stutter => prefix,
        }
    }
}

pub open spec fn m0_protected_trace(
    events: Seq<M0ProtectedEvent>,
) -> Seq<projection_layer::ProtectedInvocation> {
    m0_erase_calls(m0_protected_calls(events))
}

pub open spec fn m0_initial_protected_state(
    request: replay_layer::RequestId,
    members: ISet<config_layer::Resource>,
) -> M0ProtectedState {
    M0ProtectedState {
        request,
        initial_members: members,
        members,
        calls: Seq::empty(),
        linearized_refs: ISet::empty(),
        completed_refs: ISet::empty(),
        environment_additions: ISet::empty(),
    }
}

pub open spec fn m0_call_key_fresh(
    calls: Seq<M0ProtectedCall>,
    request: replay_layer::RequestId,
    attempt: replay_layer::AttemptId,
) -> bool {
    forall|call_ref: nat| call_ref < calls.len() ==>
        #[trigger] calls[call_ref as int].request != request
            || calls[call_ref as int].attempt != attempt
}

pub open spec fn m0_protected_enabled(
    state: M0ProtectedState,
    event: M0ProtectedEvent,
) -> bool {
    match event {
        M0ProtectedEvent::BrokerInvoke { call } => {
            &&& call.request == state.request
            &&& m0_call_key_fresh(
                state.calls, call.request, call.attempt,
            )
        },
        M0ProtectedEvent::ServiceLinearize { call_ref } => {
            &&& call_ref < state.calls.len()
            &&& state.calls[call_ref as int].request == state.request
            &&& !state.linearized_refs.contains(call_ref)
            &&& !state.completed_refs.contains(call_ref)
        },
        M0ProtectedEvent::ServiceReturn { call_ref, observation } => {
            &&& call_ref < state.calls.len()
            &&& !state.completed_refs.contains(call_ref)
            &&& match observation {
                replay_layer::Observation::Success(_) => {
                    state.linearized_refs.contains(call_ref)
                },
                replay_layer::Observation::Failure => {
                    !state.linearized_refs.contains(call_ref)
                },
                replay_layer::Observation::Ambiguous
                | replay_layer::Observation::InvalidResult(_) => true,
            }
        },
        M0ProtectedEvent::EnvironmentAdd { resource } => {
            resource != ensure_member_target(state.request)
        },
        M0ProtectedEvent::Stutter => true,
    }
}

pub open spec fn m0_protected_apply(
    state: M0ProtectedState,
    event: M0ProtectedEvent,
) -> M0ProtectedState {
    match event {
        M0ProtectedEvent::BrokerInvoke { call } => M0ProtectedState {
            calls: state.calls.push(call),
            ..state
        },
        M0ProtectedEvent::ServiceLinearize { call_ref } => M0ProtectedState {
            members: state.members.insert(
                ensure_member_target(state.request),
            ),
            linearized_refs: state.linearized_refs.insert(call_ref),
            ..state
        },
        M0ProtectedEvent::ServiceReturn { call_ref, .. } => M0ProtectedState {
            completed_refs: state.completed_refs.insert(call_ref),
            ..state
        },
        M0ProtectedEvent::EnvironmentAdd { resource } => M0ProtectedState {
            members: state.members.insert(resource),
            environment_additions: state.environment_additions.insert(resource),
            ..state
        },
        M0ProtectedEvent::Stutter => state,
    }
}

pub open spec fn m0_protected_step(
    before: M0ProtectedState,
    event: M0ProtectedEvent,
    after: M0ProtectedState,
) -> bool {
    m0_protected_enabled(before, event)
        && after == m0_protected_apply(before, event)
}

pub open spec fn m0_protected_exec(
    request: replay_layer::RequestId,
    initial_members: ISet<config_layer::Resource>,
    execution: M0ProtectedExecution,
) -> bool {
    execution.configs.len() == execution.events.len() + 1
        && execution.configs[0]
            == m0_initial_protected_state(request, initial_members)
        && forall|index: nat| index < execution.events.len() ==>
            #[trigger] m0_protected_step(
                execution.configs[index as int],
                execution.events[index as int],
                execution.configs[(index + 1) as int],
            )
}

pub open spec fn m0_protected_execution_prefix(
    execution: M0ProtectedExecution,
    length: nat,
) -> M0ProtectedExecution {
    M0ProtectedExecution {
        configs: execution.configs.take((length + 1) as int),
        events: execution.events.take(length as int),
    }
}

pub open spec fn m0_target_membership_changed(
    before: M0ProtectedState,
    after: M0ProtectedState,
) -> bool {
    before.members.contains(ensure_member_target(before.request))
        != after.members.contains(ensure_member_target(before.request))
}

pub proof fn m0_context_has_no_protected_transition_constructor(
    before: M0ProtectedState,
    after: M0ProtectedState,
)
    requires before == after,
    ensures !m0_target_membership_changed(before, after),
{
}

pub proof fn m0_target_change_requires_linearization(
    before: M0ProtectedState,
    event: M0ProtectedEvent,
    after: M0ProtectedState,
)
    requires m0_protected_step(before, event, after),
    ensures
        m0_target_membership_changed(before, after) ==> match event {
            M0ProtectedEvent::ServiceLinearize { call_ref } => {
                &&& call_ref < before.calls.len()
                &&& before.calls[call_ref as int].request == before.request
                &&& !before.linearized_refs.contains(call_ref)
                &&& !before.completed_refs.contains(call_ref)
                &&& after.linearized_refs.contains(call_ref)
            },
            M0ProtectedEvent::BrokerInvoke { .. }
            | M0ProtectedEvent::ServiceReturn { .. }
            | M0ProtectedEvent::EnvironmentAdd { .. }
            | M0ProtectedEvent::Stutter => false,
        },
{
    match event {
        M0ProtectedEvent::BrokerInvoke { .. }
        | M0ProtectedEvent::ServiceReturn { .. }
        | M0ProtectedEvent::Stutter => {},
        M0ProtectedEvent::ServiceLinearize { .. } => {},
        M0ProtectedEvent::EnvironmentAdd { resource } => {
            assert(resource != ensure_member_target(before.request));
        },
    }
}

pub proof fn m0_environment_cannot_add_target(
    before: M0ProtectedState,
    resource: config_layer::Resource,
    after: M0ProtectedState,
)
    requires m0_protected_step(
        before,
        M0ProtectedEvent::EnvironmentAdd { resource },
        after,
    ),
    ensures
        resource != ensure_member_target(before.request),
        !m0_target_membership_changed(before, after),
{
}

pub proof fn m0_broker_invoke_step_is_local_and_fresh(
    before: M0ProtectedState,
    call: M0ProtectedCall,
    after: M0ProtectedState,
)
    requires m0_protected_step(
        before,
        M0ProtectedEvent::BrokerInvoke { call },
        after,
    ),
    ensures
        call.request == before.request,
        m0_call_key_fresh(before.calls, call.request, call.attempt),
        after.calls == before.calls.push(call),
{
}

// Eventwise coupling is the only route from an adapter event into the
// protected-service alphabet.  Final trace equality is intentionally not a
// conjunct: it is derived below by prefix induction.
pub open spec fn m0_event_coupled(
    adapter_before: A1AdapterState,
    adapter_event: A1AdapterEvent,
    protected_before: M0ProtectedState,
    protected_event: M0ProtectedEvent,
) -> bool {
    match adapter_event {
        A1AdapterEvent::Observe {
            event: global_layer::GlobalEvent::InvokeEvent {
                request, attempt, call, journal_cut, ack_cut,
            },
        } => protected_event == M0ProtectedEvent::BrokerInvoke {
            call: M0ProtectedCall {
                request,
                attempt,
                call,
                journal_cut,
                ack_cut,
                source_index: adapter_before.globals.len(),
            },
        },
        A1AdapterEvent::Observe {
            event: global_layer::GlobalEvent::DeliverEvent {
                request, attempt, observation, ..
            },
        } => exists|call_ref: nat| {
            &&& call_ref < protected_before.calls.len()
            &&& protected_before.calls[call_ref as int].request == request
            &&& protected_before.calls[call_ref as int].attempt == attempt
            &&& protected_event == M0ProtectedEvent::ServiceReturn {
                call_ref,
                observation,
            }
        },
        A1AdapterEvent::ServiceLinearize { attempt } => {
            exists|call_ref: nat| {
                &&& call_ref < protected_before.calls.len()
                &&& protected_before.calls[call_ref as int].request
                    == adapter_before.request
                &&& protected_before.calls[call_ref as int].attempt == attempt
                &&& protected_event
                    == M0ProtectedEvent::ServiceLinearize { call_ref }
            }
        },
        A1AdapterEvent::EnvironmentAdd { resource } => {
            protected_event == M0ProtectedEvent::EnvironmentAdd { resource }
        },
        A1AdapterEvent::Observe {
            event: global_layer::GlobalEvent::BrokerLinearize { .. },
        }
        | A1AdapterEvent::Observe {
            event: global_layer::GlobalEvent::JournalAppendCall { .. },
        }
        | A1AdapterEvent::Observe {
            event: global_layer::GlobalEvent::JournalAppendLinearize { .. },
        }
        | A1AdapterEvent::Observe {
            event: global_layer::GlobalEvent::JournalAppendReturn { .. },
        }
        | A1AdapterEvent::Observe {
            event: global_layer::GlobalEvent::JournalDiskFull { .. },
        }
        | A1AdapterEvent::Observe {
            event: global_layer::GlobalEvent::WalStage { .. },
        }
        | A1AdapterEvent::Observe {
            event: global_layer::GlobalEvent::WalWriteFull { .. },
        }
        | A1AdapterEvent::Observe {
            event: global_layer::GlobalEvent::WalWriteTorn { .. },
        }
        | A1AdapterEvent::Observe {
            event: global_layer::GlobalEvent::WalFinishTorn { .. },
        }
        | A1AdapterEvent::Observe {
            event: global_layer::GlobalEvent::WalFlushAck { .. },
        }
        | A1AdapterEvent::Observe {
            event: global_layer::GlobalEvent::WalDiskFull { .. },
        }
        | A1AdapterEvent::Observe {
            event: global_layer::GlobalEvent::IgnoreStale { .. },
        }
        | A1AdapterEvent::Observe {
            event: global_layer::GlobalEvent::RetryRelease { .. },
        }
        | A1AdapterEvent::Observe {
            event: global_layer::GlobalEvent::Crash,
        }
        | A1AdapterEvent::Observe {
            event: global_layer::GlobalEvent::BeginScan,
        }
        | A1AdapterEvent::Observe {
            event: global_layer::GlobalEvent::FinishScan,
        }
        | A1AdapterEvent::Observe {
            event: global_layer::GlobalEvent::TruncateTail,
        }
        | A1AdapterEvent::Observe {
            event: global_layer::GlobalEvent::AbortScan,
        }
        | A1AdapterEvent::Observe {
            event: global_layer::GlobalEvent::BeginRecover,
        }
        | A1AdapterEvent::Observe {
            event: global_layer::GlobalEvent::FinishRecover,
        } => protected_event == M0ProtectedEvent::Stutter,
    }
}

pub open spec fn m0_coupled_exec(
    request: replay_layer::RequestId,
    initial_members: ISet<config_layer::Resource>,
    adapter: A1AdapterExecution,
    protected: M0ProtectedExecution,
) -> bool {
    &&& a1_exec(request, initial_members, adapter)
    &&& m0_protected_exec(request, initial_members, protected)
    &&& adapter.events.len() == protected.events.len()
    &&& forall|index: nat| index < adapter.events.len() ==>
        #[trigger] m0_event_coupled(
            adapter.configs[index as int],
            adapter.events[index as int],
            protected.configs[index as int],
            protected.events[index as int],
        )
}

pub open spec fn m0_event_trace_match(
    adapter_event: A1AdapterEvent,
    protected_event: M0ProtectedEvent,
) -> bool {
    match adapter_event {
        A1AdapterEvent::Observe {
            event: global_layer::GlobalEvent::InvokeEvent {
                request, attempt, call, journal_cut, ack_cut,
            },
        } => match protected_event {
            M0ProtectedEvent::BrokerInvoke { call: protected_call } => {
                &&& protected_call.request == request
                &&& protected_call.attempt == attempt
                &&& protected_call.call == call
                &&& protected_call.journal_cut == journal_cut
                &&& protected_call.ack_cut == ack_cut
            },
            M0ProtectedEvent::ServiceLinearize { .. }
            | M0ProtectedEvent::ServiceReturn { .. }
            | M0ProtectedEvent::EnvironmentAdd { .. }
            | M0ProtectedEvent::Stutter => false,
        },
        A1AdapterEvent::Observe {
            event: global_layer::GlobalEvent::BrokerLinearize { .. },
        }
        | A1AdapterEvent::Observe {
            event: global_layer::GlobalEvent::JournalAppendCall { .. },
        }
        | A1AdapterEvent::Observe {
            event: global_layer::GlobalEvent::JournalAppendLinearize { .. },
        }
        | A1AdapterEvent::Observe {
            event: global_layer::GlobalEvent::JournalAppendReturn { .. },
        }
        | A1AdapterEvent::Observe {
            event: global_layer::GlobalEvent::JournalDiskFull { .. },
        }
        | A1AdapterEvent::Observe {
            event: global_layer::GlobalEvent::WalStage { .. },
        }
        | A1AdapterEvent::Observe {
            event: global_layer::GlobalEvent::WalWriteFull { .. },
        }
        | A1AdapterEvent::Observe {
            event: global_layer::GlobalEvent::WalWriteTorn { .. },
        }
        | A1AdapterEvent::Observe {
            event: global_layer::GlobalEvent::WalFinishTorn { .. },
        }
        | A1AdapterEvent::Observe {
            event: global_layer::GlobalEvent::WalFlushAck { .. },
        }
        | A1AdapterEvent::Observe {
            event: global_layer::GlobalEvent::WalDiskFull { .. },
        }
        | A1AdapterEvent::Observe {
            event: global_layer::GlobalEvent::DeliverEvent { .. },
        }
        | A1AdapterEvent::Observe {
            event: global_layer::GlobalEvent::IgnoreStale { .. },
        }
        | A1AdapterEvent::Observe {
            event: global_layer::GlobalEvent::RetryRelease { .. },
        }
        | A1AdapterEvent::Observe {
            event: global_layer::GlobalEvent::Crash,
        }
        | A1AdapterEvent::Observe {
            event: global_layer::GlobalEvent::BeginScan,
        }
        | A1AdapterEvent::Observe {
            event: global_layer::GlobalEvent::FinishScan,
        }
        | A1AdapterEvent::Observe {
            event: global_layer::GlobalEvent::TruncateTail,
        }
        | A1AdapterEvent::Observe {
            event: global_layer::GlobalEvent::AbortScan,
        }
        | A1AdapterEvent::Observe {
            event: global_layer::GlobalEvent::BeginRecover,
        }
        | A1AdapterEvent::Observe {
            event: global_layer::GlobalEvent::FinishRecover,
        }
        | A1AdapterEvent::ServiceLinearize { .. }
        | A1AdapterEvent::EnvironmentAdd { .. } => {
            !(protected_event is BrokerInvoke)
        },
    }
}

pub proof fn m0_event_coupling_implies_trace_match(
    adapter_before: A1AdapterState,
    adapter_event: A1AdapterEvent,
    protected_before: M0ProtectedState,
    protected_event: M0ProtectedEvent,
)
    requires m0_event_coupled(
        adapter_before, adapter_event, protected_before, protected_event,
    ),
    ensures m0_event_trace_match(adapter_event, protected_event),
{
    match adapter_event {
        A1AdapterEvent::Observe {
            event: global_layer::GlobalEvent::BrokerLinearize { .. },
        }
        | A1AdapterEvent::Observe {
            event: global_layer::GlobalEvent::JournalAppendCall { .. },
        }
        | A1AdapterEvent::Observe {
            event: global_layer::GlobalEvent::JournalAppendLinearize { .. },
        }
        | A1AdapterEvent::Observe {
            event: global_layer::GlobalEvent::JournalAppendReturn { .. },
        }
        | A1AdapterEvent::Observe {
            event: global_layer::GlobalEvent::JournalDiskFull { .. },
        }
        | A1AdapterEvent::Observe {
            event: global_layer::GlobalEvent::WalStage { .. },
        }
        | A1AdapterEvent::Observe {
            event: global_layer::GlobalEvent::WalWriteFull { .. },
        }
        | A1AdapterEvent::Observe {
            event: global_layer::GlobalEvent::WalWriteTorn { .. },
        }
        | A1AdapterEvent::Observe {
            event: global_layer::GlobalEvent::WalFinishTorn { .. },
        }
        | A1AdapterEvent::Observe {
            event: global_layer::GlobalEvent::WalFlushAck { .. },
        }
        | A1AdapterEvent::Observe {
            event: global_layer::GlobalEvent::WalDiskFull { .. },
        }
        | A1AdapterEvent::Observe {
            event: global_layer::GlobalEvent::InvokeEvent { .. },
        }
        | A1AdapterEvent::Observe {
            event: global_layer::GlobalEvent::DeliverEvent { .. },
        }
        | A1AdapterEvent::Observe {
            event: global_layer::GlobalEvent::IgnoreStale { .. },
        }
        | A1AdapterEvent::Observe {
            event: global_layer::GlobalEvent::RetryRelease { .. },
        }
        | A1AdapterEvent::Observe {
            event: global_layer::GlobalEvent::Crash,
        }
        | A1AdapterEvent::Observe {
            event: global_layer::GlobalEvent::BeginScan,
        }
        | A1AdapterEvent::Observe {
            event: global_layer::GlobalEvent::FinishScan,
        }
        | A1AdapterEvent::Observe {
            event: global_layer::GlobalEvent::TruncateTail,
        }
        | A1AdapterEvent::Observe {
            event: global_layer::GlobalEvent::AbortScan,
        }
        | A1AdapterEvent::Observe {
            event: global_layer::GlobalEvent::BeginRecover,
        }
        | A1AdapterEvent::Observe {
            event: global_layer::GlobalEvent::FinishRecover,
        }
        | A1AdapterEvent::ServiceLinearize { .. }
        | A1AdapterEvent::EnvironmentAdd { .. } => {},
    }
}

proof fn m0_erase_calls_push(
    calls: Seq<M0ProtectedCall>,
    call: M0ProtectedCall,
)
    ensures m0_erase_calls(calls.push(call))
        == m0_erase_calls(calls).push(m0_call_invocation(call)),
{
    assert(calls.push(call).drop_last() =~= calls);
    assert(calls.push(call).last() == call);
}

proof fn m0_protected_calls_push(
    events: Seq<M0ProtectedEvent>,
    event: M0ProtectedEvent,
)
    ensures m0_protected_calls(events.push(event)) == match event {
        M0ProtectedEvent::BrokerInvoke { call } => {
            m0_protected_calls(events).push(call)
        },
        M0ProtectedEvent::ServiceLinearize { .. }
        | M0ProtectedEvent::ServiceReturn { .. }
        | M0ProtectedEvent::EnvironmentAdd { .. }
        | M0ProtectedEvent::Stutter => m0_protected_calls(events),
    },
{
    assert(events.push(event).drop_last() =~= events);
    assert(events.push(event).last() == event);
}

proof fn m0_invocations_from_physical_push(
    events: Seq<p0_layer::PhysicalEvent>,
    event: p0_layer::PhysicalEvent,
)
    ensures projection_layer::invocations_from_physical(
        events.push(event),
    ) == match event {
        p0_layer::PhysicalEvent::Invoke { request, attempt, call, .. } => {
            projection_layer::invocations_from_physical(events).push(
                projection_layer::ProtectedInvocation {
                    request,
                    attempt,
                    call,
                },
            )
        },
        p0_layer::PhysicalEvent::Delivered { .. } => {
            projection_layer::invocations_from_physical(events)
        },
    },
{
    assert(events.push(event).drop_last() =~= events);
    assert(events.push(event).last() == event);
}

pub proof fn m0_pi_invocations_push(
    events: Seq<global_layer::GlobalEvent>,
    event: global_layer::GlobalEvent,
)
    ensures projection_layer::pi_invocations(events.push(event))
        == match event {
            global_layer::GlobalEvent::InvokeEvent {
                request, attempt, call, ..
            } => projection_layer::pi_invocations(events).push(
                projection_layer::ProtectedInvocation {
                    request,
                    attempt,
                    call,
                },
            ),
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
                projection_layer::pi_invocations(events)
            },
        },
{
    projection_layer::pi_physical_push(events, event);
    match event {
        global_layer::GlobalEvent::InvokeEvent {
            request, attempt, call, journal_cut, ack_cut,
        } => {
            let physical = p0_layer::PhysicalEvent::Invoke {
                request,
                attempt,
                call,
                journal_cut,
                ack_cut,
            };
            m0_invocations_from_physical_push(
                projection_layer::pi_physical(events), physical,
            );
        },
        global_layer::GlobalEvent::DeliverEvent {
            request, attempt, observation, journal_cut,
        } => {
            let physical = p0_layer::PhysicalEvent::Delivered {
                request,
                attempt,
                observation,
                journal_cut,
            };
            m0_invocations_from_physical_push(
                projection_layer::pi_physical(events), physical,
            );
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

proof fn m0_a1_global_trace_push(
    events: Seq<A1AdapterEvent>,
    event: A1AdapterEvent,
)
    ensures a1_global_trace(events.push(event)) == match event {
        A1AdapterEvent::Observe { event: global } => {
            a1_global_trace(events).push(global)
        },
        A1AdapterEvent::ServiceLinearize { .. }
        | A1AdapterEvent::EnvironmentAdd { .. } => a1_global_trace(events),
    },
{
    assert(events.push(event).drop_last() =~= events);
    assert(events.push(event).last() == event);
}

pub proof fn m0_trace_coupling_derives_mediation(
    adapter_events: Seq<A1AdapterEvent>,
    protected_events: Seq<M0ProtectedEvent>,
)
    requires
        adapter_events.len() == protected_events.len(),
        forall|index: nat| index < adapter_events.len() ==>
            #[trigger] m0_event_trace_match(
                adapter_events[index as int],
                protected_events[index as int],
            ),
    ensures m0_protected_trace(protected_events)
        == projection_layer::pi_invocations(
            a1_global_trace(adapter_events),
        ),
    decreases adapter_events.len(),
{
    if adapter_events.len() == 0 {
        assert(protected_events.len() == 0);
    } else {
        let adapter_prefix = adapter_events.drop_last();
        let protected_prefix = protected_events.drop_last();
        assert(adapter_prefix.len() == protected_prefix.len());
        assert forall|index: nat| index < adapter_prefix.len() implies
            #[trigger] m0_event_trace_match(
                adapter_prefix[index as int],
                protected_prefix[index as int],
            ) by {
            assert(index < adapter_events.len());
            assert(adapter_prefix[index as int]
                == adapter_events[index as int]);
            assert(protected_prefix[index as int]
                == protected_events[index as int]);
        }
        m0_trace_coupling_derives_mediation(
            adapter_prefix, protected_prefix,
        );
        let adapter_last = adapter_events.last();
        let protected_last = protected_events.last();
        assert(m0_event_trace_match(adapter_last, protected_last));
        assert(adapter_events =~= adapter_prefix.push(adapter_last));
        assert(protected_events =~= protected_prefix.push(protected_last));
        m0_a1_global_trace_push(adapter_prefix, adapter_last);
        m0_protected_calls_push(protected_prefix, protected_last);
        match adapter_last {
            A1AdapterEvent::Observe {
                event: global @ global_layer::GlobalEvent::InvokeEvent { .. },
            } => {
                m0_pi_invocations_push(
                    a1_global_trace(adapter_prefix), global,
                );
                match protected_last {
                    M0ProtectedEvent::BrokerInvoke { call } => {
                        m0_erase_calls_push(
                            m0_protected_calls(protected_prefix), call,
                        );
                    },
                    M0ProtectedEvent::ServiceLinearize { .. }
                    | M0ProtectedEvent::ServiceReturn { .. }
                    | M0ProtectedEvent::EnvironmentAdd { .. }
                    | M0ProtectedEvent::Stutter => {},
                }
            },
            A1AdapterEvent::Observe { event: global } => {
                m0_pi_invocations_push(
                    a1_global_trace(adapter_prefix), global,
                );
            },
            A1AdapterEvent::ServiceLinearize { .. }
            | A1AdapterEvent::EnvironmentAdd { .. } => {},
        }
    }
}

pub proof fn m0_protected_exec_prefix(
    request: replay_layer::RequestId,
    initial_members: ISet<config_layer::Resource>,
    execution: M0ProtectedExecution,
    length: nat,
)
    requires
        m0_protected_exec(request, initial_members, execution),
        length <= execution.events.len(),
    ensures m0_protected_exec(
        request,
        initial_members,
        m0_protected_execution_prefix(execution, length),
    ),
{
    let prefix = m0_protected_execution_prefix(execution, length);
    assert(prefix.events.len() == length);
    assert(prefix.configs.len() == length + 1);
    assert(prefix.configs[0] == execution.configs[0]);
    assert forall|index: nat| index < prefix.events.len() implies
        #[trigger] m0_protected_step(
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

pub proof fn m0_protected_exec_final_calls_are_generated(
    request: replay_layer::RequestId,
    initial_members: ISet<config_layer::Resource>,
    execution: M0ProtectedExecution,
)
    requires m0_protected_exec(request, initial_members, execution),
    ensures execution.configs[execution.events.len() as int].calls
        == m0_protected_calls(execution.events),
    decreases execution.events.len(),
{
    if execution.events.len() == 0 {
        assert(execution.configs[0]
            == m0_initial_protected_state(request, initial_members));
    } else {
        let last_index: nat = (execution.events.len() - 1) as nat;
        let prefix = m0_protected_execution_prefix(execution, last_index);
        m0_protected_exec_prefix(
            request, initial_members, execution, last_index,
        );
        m0_protected_exec_final_calls_are_generated(
            request, initial_members, prefix,
        );
        let before = execution.configs[last_index as int];
        let event = execution.events[last_index as int];
        let after = execution.configs[(last_index + 1) as int];
        assert(prefix.events =~= execution.events.drop_last());
        assert(prefix.configs[last_index as int] == before);
        assert(m0_protected_step(before, event, after));
        assert(after == m0_protected_apply(before, event));
        m0_protected_calls_push(prefix.events, event);
        assert(execution.events =~= prefix.events.push(event));
    }
}

pub proof fn m0_coupled_exec_derives_complete_mediation(
    request: replay_layer::RequestId,
    initial_members: ISet<config_layer::Resource>,
    adapter: A1AdapterExecution,
    protected: M0ProtectedExecution,
)
    requires m0_coupled_exec(
        request, initial_members, adapter, protected,
    ),
    ensures
        protected.configs[protected.events.len() as int].calls
            == m0_protected_calls(protected.events),
        m0_erase_calls(
            protected.configs[protected.events.len() as int].calls,
        ) == projection_layer::pi_invocations(
            a1_global_trace(adapter.events),
        ),
        projection_layer::complete_mediation(
            a1_global_trace(adapter.events),
            m0_erase_calls(
                protected.configs[protected.events.len() as int].calls,
            ),
        ),
{
    assert forall|index: nat| index < adapter.events.len() implies
        #[trigger] m0_event_trace_match(
            adapter.events[index as int],
            protected.events[index as int],
        ) by {
        m0_event_coupling_implies_trace_match(
            adapter.configs[index as int],
            adapter.events[index as int],
            protected.configs[index as int],
            protected.events[index as int],
        );
    }
    m0_trace_coupling_derives_mediation(
        adapter.events, protected.events,
    );
    m0_protected_exec_final_calls_are_generated(
        request, initial_members, protected,
    );
}

// The program context receives only the masked T4-C1 view.  Its state is an
// audit of visible broker invocations; neither its state nor its transition
// type contains a protected-service handle or a target-mutation operation.

pub struct M0ProtectedHandleState {
    pub invocations: Seq<projection_layer::ProtectedInvocation>,
}

pub open spec fn m0_context_invocations(
    history: Seq<t4_c1_layer::ContextEvent>,
) -> Seq<projection_layer::ProtectedInvocation>
    decreases history.len()
{
    if history.len() == 0 {
        Seq::empty()
    } else {
        let prefix = m0_context_invocations(history.drop_last());
        match history.last() {
            t4_c1_layer::ContextEvent::Invoke {
                request, attempt, call,
            } => prefix.push(projection_layer::ProtectedInvocation {
                request,
                attempt,
                call,
            }),
            t4_c1_layer::ContextEvent::AppendCall { .. }
            | t4_c1_layer::ContextEvent::AppendReturn { .. }
            | t4_c1_layer::ContextEvent::Deliver { .. }
            | t4_c1_layer::ContextEvent::IgnoreStale { .. }
            | t4_c1_layer::ContextEvent::RetryRelease { .. }
            | t4_c1_layer::ContextEvent::Crash
            | t4_c1_layer::ContextEvent::BeginRecover
            | t4_c1_layer::ContextEvent::FinishRecover => prefix,
        }
    }
}

pub open spec fn m0_exclusive_handle_context(
    cfg: config_layer::FullConfig,
) -> t4_c1_layer::ProgramContext<M0ProtectedHandleState> {
    t4_c1_layer::ProgramContext {
        initial: ISet::new(|entry: t4_c1_layer::ContextInitial<
            M0ProtectedHandleState,
        >| {
            &&& entry.view == t4_c1_layer::initial_context_view(cfg)
            &&& entry.state.invocations == Seq::empty()
        }),
        transitions: ISet::new(|transition: t4_c1_layer::ContextTransition<
            M0ProtectedHandleState,
        >| {
            &&& transition.view.requests == cfg.request
            &&& transition.after_view.requests == cfg.request
            &&& t4_c1_layer::valid_context_delta(transition.delta)
            &&& transition.after_view.history
                == transition.view.history.add(transition.delta)
            &&& transition.before.invocations
                == m0_context_invocations(transition.view.history)
            &&& transition.after.invocations
                == m0_context_invocations(transition.after_view.history)
        }),
    }
}

proof fn m0_context_invocations_push(
    history: Seq<t4_c1_layer::ContextEvent>,
    event: t4_c1_layer::ContextEvent,
)
    ensures m0_context_invocations(history.push(event)) == match event {
        t4_c1_layer::ContextEvent::Invoke {
            request, attempt, call,
        } => m0_context_invocations(history).push(
            projection_layer::ProtectedInvocation {
                request,
                attempt,
                call,
            },
        ),
        t4_c1_layer::ContextEvent::AppendCall { .. }
        | t4_c1_layer::ContextEvent::AppendReturn { .. }
        | t4_c1_layer::ContextEvent::Deliver { .. }
        | t4_c1_layer::ContextEvent::IgnoreStale { .. }
        | t4_c1_layer::ContextEvent::RetryRelease { .. }
        | t4_c1_layer::ContextEvent::Crash
        | t4_c1_layer::ContextEvent::BeginRecover
        | t4_c1_layer::ContextEvent::FinishRecover => {
            m0_context_invocations(history)
        },
    },
{
    assert(history.push(event).drop_last() =~= history);
    assert(history.push(event).last() == event);
}

proof fn m0_context_invocations_add(
    left: Seq<t4_c1_layer::ContextEvent>,
    right: Seq<t4_c1_layer::ContextEvent>,
)
    ensures m0_context_invocations(left.add(right))
        == m0_context_invocations(left).add(
            m0_context_invocations(right),
        ),
    decreases right.len(),
{
    if right.len() == 0 {
        assert(left.add(right) =~= left);
    } else {
        let prefix = right.drop_last();
        let event = right.last();
        m0_context_invocations_add(left, prefix);
        assert(right =~= prefix.push(event));
        assert(left.add(right) =~= left.add(prefix).push(event));
        m0_context_invocations_push(left.add(prefix), event);
        m0_context_invocations_push(prefix, event);
        match event {
            t4_c1_layer::ContextEvent::AppendCall { .. }
            | t4_c1_layer::ContextEvent::AppendReturn { .. }
            | t4_c1_layer::ContextEvent::Invoke { .. }
            | t4_c1_layer::ContextEvent::Deliver { .. }
            | t4_c1_layer::ContextEvent::IgnoreStale { .. }
            | t4_c1_layer::ContextEvent::RetryRelease { .. }
            | t4_c1_layer::ContextEvent::Crash
            | t4_c1_layer::ContextEvent::BeginRecover
            | t4_c1_layer::ContextEvent::FinishRecover => {},
        }
    }
}

pub proof fn m0_exclusive_context_is_storage_parametric(
    cfg: config_layer::FullConfig,
)
    ensures t4_c1_layer::storage_parametric_context(
        cfg, m0_exclusive_handle_context(cfg),
    ),
{
    let state = M0ProtectedHandleState {
        invocations: Seq::empty(),
    };
    let admitted = t4_c1_layer::ContextInitial {
        view: t4_c1_layer::initial_context_view(cfg),
        state,
    };
    assert(m0_exclusive_handle_context(cfg).initial.contains(admitted));
    assert(exists|witness: M0ProtectedHandleState|
        m0_exclusive_handle_context(cfg).initial.contains(
            t4_c1_layer::ContextInitial {
                view: t4_c1_layer::initial_context_view(cfg),
                state: witness,
            },
        )) by {
        let witness = state;
    }
    assert forall|transition: t4_c1_layer::ContextTransition<
        M0ProtectedHandleState,
    >| m0_exclusive_handle_context(cfg).transitions.contains(transition)
        implies {
            &&& transition.view.requests == cfg.request
            &&& transition.after_view.requests == cfg.request
            &&& t4_c1_layer::valid_context_delta(transition.delta)
        } by {
    }
}

pub proof fn m0_exclusive_context_transition_is_invoke_only(
    cfg: config_layer::FullConfig,
    transition: t4_c1_layer::ContextTransition<M0ProtectedHandleState>,
)
    requires m0_exclusive_handle_context(cfg).transitions.contains(transition),
    ensures
        transition.after.invocations
            == transition.before.invocations.add(
                m0_context_invocations(transition.delta),
            ),
        m0_context_invocations(transition.delta).len() == 0 ==>
            transition.after.invocations == transition.before.invocations,
{
    m0_context_invocations_add(
        transition.view.history, transition.delta,
    );
}

pub open spec fn m0_handle_contexts(
    events: Seq<global_layer::GlobalEvent>,
) -> Seq<M0ProtectedHandleState> {
    Seq::new((events.len() + 1) as nat, |index: int|
        M0ProtectedHandleState {
            invocations: m0_context_invocations(
                t4_c1_layer::context_history(events.take(index)),
            ),
        },
    )
}

pub open spec fn m0_plugged_wal_execution(
    execution: wal_runtime_layer::WalExecution,
) -> t4_c1_layer::PluggedWalExecution<M0ProtectedHandleState> {
    t4_c1_layer::PluggedWalExecution {
        machine: execution,
        contexts: m0_handle_contexts(execution.events),
    }
}

pub proof fn m0_wal_exec_has_exclusive_handle_context(
    cfg: config_layer::FullConfig,
    execution: wal_runtime_layer::WalExecution,
)
    requires wal_runtime_layer::exec(cfg, execution),
    ensures t4_c1_layer::plugged_wal_exec(
        cfg,
        m0_exclusive_handle_context(cfg),
        m0_plugged_wal_execution(execution),
    ),
{
    let plugged = m0_plugged_wal_execution(execution);
    let context = m0_exclusive_handle_context(cfg);
    assert(plugged.contexts.len() == execution.events.len() + 1);
    assert(plugged.contexts[0].invocations == Seq::empty());
    t4_c1_layer::initialized_wal_has_initial_context_view(cfg, execution);
    assert(context.initial.contains(t4_c1_layer::ContextInitial {
        view: t4_c1_layer::wal_context_view_at(cfg, execution, 0),
        state: plugged.contexts[0],
    }));
    assert forall|index: nat| index < execution.events.len() implies {
        &&& #[trigger] wal_runtime_layer::wal_runtime_step(
            cfg,
            execution.configs[index as int],
            execution.events[index as int],
            execution.configs[(index + 1) as int],
        )
        &&& t4_c1_layer::context_accepts_step(
            context,
            plugged.contexts[index as int],
            t4_c1_layer::wal_context_view_at(cfg, execution, index),
            execution.events[index as int],
            t4_c1_layer::wal_context_view_at(cfg, execution, index + 1),
            plugged.contexts[(index + 1) as int],
        )
    } by {
        let event = execution.events[index as int];
        let before_view = t4_c1_layer::wal_context_view_at(
            cfg, execution, index,
        );
        let after_view = t4_c1_layer::wal_context_view_at(
            cfg, execution, index + 1,
        );
        let before_state = plugged.contexts[index as int];
        let after_state = plugged.contexts[(index + 1) as int];
        assert(index + 1 <= execution.events.len());
        assert(execution.events.take((index + 1) as int) =~=
            execution.events.take(index as int).push(event));
        t4_c1_layer::context_history_push_delta(
            execution.events.take(index as int), event,
        );
        t4_c1_layer::context_history_push(
            execution.events.take(index as int), event,
        );
        if t4_c1_layer::context_delta(event).len() == 0 {
            t4_c1_layer::wal_hidden_step_preserves_context_view(
                cfg,
                t4_c1_layer::context_history(
                    execution.events.take(index as int),
                ),
                execution.configs[index as int],
                event,
                execution.configs[(index + 1) as int],
            );
            assert(before_view.history == t4_c1_layer::context_history(
                execution.events.take(index as int),
            ));
            assert(after_view.history == t4_c1_layer::context_history_after(
                t4_c1_layer::context_history(
                    execution.events.take(index as int),
                ),
                event,
            ));
            assert(before_view == after_view);
            assert(before_state.invocations == after_state.invocations);
            assert(before_state == after_state);
        } else {
            let delta = t4_c1_layer::context_delta(event);
            assert(t4_c1_layer::valid_context_delta(delta)) by {
                assert(exists|source: global_layer::GlobalEvent|
                    t4_c1_layer::context_delta(source) == delta) by {
                    let source = event;
                }
            }
            assert(after_view.history == before_view.history.add(delta));
            assert(before_state.invocations
                == m0_context_invocations(before_view.history));
            assert(after_state.invocations
                == m0_context_invocations(after_view.history));
            assert(context.transitions.contains(
                t4_c1_layer::ContextTransition {
                    before: before_state,
                    view: before_view,
                    delta,
                    after_view,
                    after: after_state,
                },
            ));
        }
    }
}

proof fn m0_context_invocations_after_global(
    history: Seq<t4_c1_layer::ContextEvent>,
    event: global_layer::GlobalEvent,
)
    ensures m0_context_invocations(
        t4_c1_layer::context_history_after(history, event),
    ) == match event {
        global_layer::GlobalEvent::InvokeEvent {
            request, attempt, call, ..
        } => m0_context_invocations(history).push(
            projection_layer::ProtectedInvocation {
                request,
                attempt,
                call,
            },
        ),
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
            m0_context_invocations(history)
        },
    },
{
    match event {
        global_layer::GlobalEvent::JournalDiskFull { record, cut }
        | global_layer::GlobalEvent::WalDiskFull { record, cut } => {
            let first = t4_c1_layer::ContextEvent::AppendCall { record };
            let second = t4_c1_layer::ContextEvent::AppendReturn {
                result: c1_layer::append_layer::AppendResult::Full,
                cut,
            };
            m0_context_invocations_push(history, first);
            m0_context_invocations_push(history.push(first), second);
        },
        global_layer::GlobalEvent::JournalAppendCall { record }
        | global_layer::GlobalEvent::WalStage { record } => {
            m0_context_invocations_push(
                history,
                t4_c1_layer::ContextEvent::AppendCall { record },
            );
        },
        global_layer::GlobalEvent::JournalAppendReturn { cut }
        | global_layer::GlobalEvent::WalFlushAck { cut } => {
            m0_context_invocations_push(
                history,
                t4_c1_layer::ContextEvent::AppendReturn {
                    result: c1_layer::append_layer::AppendResult::Ok,
                    cut,
                },
            );
        },
        global_layer::GlobalEvent::InvokeEvent {
            request, attempt, call, ..
        } => {
            m0_context_invocations_push(
                history,
                t4_c1_layer::ContextEvent::Invoke {
                    request,
                    attempt,
                    call,
                },
            );
        },
        global_layer::GlobalEvent::DeliverEvent {
            request, attempt, observation, ..
        } => {
            m0_context_invocations_push(
                history,
                t4_c1_layer::ContextEvent::Deliver {
                    request,
                    attempt,
                    observation,
                },
            );
        },
        global_layer::GlobalEvent::IgnoreStale { request, attempt } => {
            m0_context_invocations_push(
                history,
                t4_c1_layer::ContextEvent::IgnoreStale { request, attempt },
            );
        },
        global_layer::GlobalEvent::RetryRelease { request } => {
            m0_context_invocations_push(
                history,
                t4_c1_layer::ContextEvent::RetryRelease { request },
            );
        },
        global_layer::GlobalEvent::Crash => {
            m0_context_invocations_push(
                history, t4_c1_layer::ContextEvent::Crash,
            );
        },
        global_layer::GlobalEvent::BeginRecover => {
            m0_context_invocations_push(
                history, t4_c1_layer::ContextEvent::BeginRecover,
            );
        },
        global_layer::GlobalEvent::FinishRecover => {
            m0_context_invocations_push(
                history, t4_c1_layer::ContextEvent::FinishRecover,
            );
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

pub proof fn m0_context_trace_equals_pi_invocations(
    events: Seq<global_layer::GlobalEvent>,
)
    ensures m0_context_invocations(t4_c1_layer::context_history(events))
        == projection_layer::pi_invocations(events),
    decreases events.len(),
{
    if events.len() > 0 {
        let prefix = events.drop_last();
        let event = events.last();
        m0_context_trace_equals_pi_invocations(prefix);
        t4_c1_layer::context_history_push(prefix, event);
        m0_context_invocations_after_global(
            t4_c1_layer::context_history(prefix), event,
        );
        m0_pi_invocations_push(prefix, event);
        assert(events =~= prefix.push(event));
    }
}

proof fn m0_exclusive_context_final_state_tracks_invocations(
    cfg: config_layer::FullConfig,
    execution: t4_c1_layer::PluggedWalExecution<M0ProtectedHandleState>,
)
    requires t4_c1_layer::plugged_wal_exec(
        cfg, m0_exclusive_handle_context(cfg), execution,
    ),
    ensures execution.contexts[execution.machine.events.len() as int].invocations
        == m0_context_invocations(t4_c1_layer::context_history(
            execution.machine.events,
        )),
    decreases execution.machine.events.len(),
{
    let context = m0_exclusive_handle_context(cfg);
    if execution.machine.events.len() == 0 {
        assert(context.initial.contains(t4_c1_layer::ContextInitial {
            view: t4_c1_layer::wal_context_view_at(
                cfg, execution.machine, 0,
            ),
            state: execution.contexts[0],
        }));
        assert(execution.contexts[0].invocations == Seq::empty());
    } else {
        let prior: nat = (execution.machine.events.len() - 1) as nat;
        let prefix = t4_c1_layer::plugged_wal_prefix(execution, prior);
        t4_c1_layer::plugged_wal_prefix_closed(
            cfg, context, execution, prior,
        );
        m0_exclusive_context_final_state_tracks_invocations(cfg, prefix);
        assert(prefix.machine.events =~= execution.machine.events.drop_last());
        assert(prefix.contexts =~= execution.contexts.drop_last());
        let event = execution.machine.events.last();
        let before_view = t4_c1_layer::wal_context_view_at(
            cfg, execution.machine, prior,
        );
        let after_view = t4_c1_layer::wal_context_view_at(
            cfg, execution.machine, prior + 1,
        );
        let before_state = execution.contexts[prior as int];
        let after_state = execution.contexts[(prior + 1) as int];
        assert(prior < execution.machine.events.len());
        assert(wal_runtime_layer::wal_runtime_step(
            cfg,
            execution.machine.configs[prior as int],
            event,
            execution.machine.configs[(prior + 1) as int],
        ));
        assert(t4_c1_layer::context_accepts_step(
            context,
            before_state,
            before_view,
            event,
            after_view,
            after_state,
        ));
        assert(execution.machine.events =~=
            prefix.machine.events.push(event));
        t4_c1_layer::context_history_push_delta(
            prefix.machine.events, event,
        );
        assert(before_state.invocations == m0_context_invocations(
            t4_c1_layer::context_history(prefix.machine.events),
        ));
        if t4_c1_layer::context_delta(event).len() == 0 {
            assert(after_state == before_state);
        } else {
            assert(context.transitions.contains(
                t4_c1_layer::ContextTransition {
                    before: before_state,
                    view: before_view,
                    delta: t4_c1_layer::context_delta(event),
                    after_view,
                    after: after_state,
                },
            ));
            assert(after_state.invocations
                == m0_context_invocations(after_view.history));
        }
    }
}

pub proof fn m0_exclusive_context_state_tracks_invocations(
    cfg: config_layer::FullConfig,
    execution: t4_c1_layer::PluggedWalExecution<M0ProtectedHandleState>,
    index: nat,
)
    requires
        t4_c1_layer::plugged_wal_exec(
            cfg, m0_exclusive_handle_context(cfg), execution,
        ),
        index <= execution.machine.events.len(),
    ensures execution.contexts[index as int].invocations
        == m0_context_invocations(t4_c1_layer::context_history(
            execution.machine.events.take(index as int),
        )),
{
    let context = m0_exclusive_handle_context(cfg);
    let prefix = t4_c1_layer::plugged_wal_prefix(execution, index);
    t4_c1_layer::plugged_wal_prefix_closed(
        cfg, context, execution, index,
    );
    m0_exclusive_context_final_state_tracks_invocations(cfg, prefix);
    assert(prefix.machine.events
        =~= execution.machine.events.take(index as int));
    assert(prefix.contexts[index as int]
        == execution.contexts[index as int]);
}

pub proof fn m0_exclusive_context_derives_complete_mediation(
    cfg: config_layer::FullConfig,
    execution: t4_c1_layer::PluggedWalExecution<M0ProtectedHandleState>,
)
    requires t4_c1_layer::plugged_wal_exec(
        cfg, m0_exclusive_handle_context(cfg), execution,
    ),
    ensures
        execution.contexts[execution.machine.events.len() as int].invocations
            == projection_layer::pi_invocations(execution.machine.events),
        projection_layer::complete_mediation(
            execution.machine.events,
            execution.contexts[
                execution.machine.events.len() as int
            ].invocations,
        ),
{
    let length = execution.machine.events.len();
    m0_exclusive_context_state_tracks_invocations(
        cfg, execution, length,
    );
    assert(execution.machine.events.take(length as int)
        =~= execution.machine.events);
    m0_context_trace_equals_pi_invocations(execution.machine.events);
    assert(execution.contexts[length as int].invocations
        == projection_layer::pi_invocations(execution.machine.events));
}

// A protected call is durably authorized when its exact WAL Invoke survives
// the canonical T4 compression and the corresponding Broker label satisfies
// T1's temporal authorization theorem.  The latter includes the acknowledged
// Start/Authorize ancestry and a strict prior successful append return.
pub open spec fn m0_durably_authorized_call(
    cfg: config_layer::FullConfig,
    execution: wal_runtime_layer::WalExecution,
    call: M0ProtectedCall,
) -> bool {
    let target = t4_c0_layer::canonical_target_execution(cfg, execution);
    let map = t4_c0_layer::canonical_composed_map(execution);
    let broker_index = map.points[call.source_index as int];
    &&& call.source_index < execution.events.len()
    &&& execution.events[call.source_index as int]
        == m0_call_global_event(call)
    &&& broker_index < target.events.len()
    &&& target.events[broker_index as int] == m0_call_global_event(call)
    &&& t1_layer::invoke_temporal_at(cfg, target, broker_index)
}

proof fn m0_invoke_survives_canonical_mapping(
    cfg: config_layer::FullConfig,
    execution: wal_runtime_layer::WalExecution,
    target: execution_layer::BrokerExecution,
    map: t2_layer::WeakIndexMap,
    call: M0ProtectedCall,
)
    requires
        t4_c0_layer::step_correspondence(execution, target, map),
        call.source_index < execution.events.len(),
        execution.events[call.source_index as int]
            == m0_call_global_event(call),
    ensures
        map.points[call.source_index as int] < target.events.len(),
        target.events[map.points[call.source_index as int] as int]
            == m0_call_global_event(call),
{
    let source_index = call.source_index;
    let left = map.points[source_index as int];
    let right = map.points[(source_index + 1) as int];
    assert(!t4_c0_layer::composed_projection_silent(
        m0_call_global_event(call),
    ));
    assert(left != right);
    assert(right == left + 1);
    assert(left < target.events.len());
    assert(t4_c0_layer::composed_event_match(
        m0_call_global_event(call), target.events[left as int],
    ));
    assert(t4_c0_layer::wal_to_broker_event(
        m0_call_global_event(call),
    ) == Option::Some(m0_call_global_event(call)));
}

proof fn m0_t1_safety_authorizes_exact_invoke(
    cfg: config_layer::FullConfig,
    target: execution_layer::BrokerExecution,
    call: M0ProtectedCall,
    broker_index: nat,
)
    requires
        t1_layer::t1_parameterized_safety_statement(cfg, target),
        broker_index < target.events.len(),
        target.events[broker_index as int] == m0_call_global_event(call),
    ensures t1_layer::invoke_temporal_at(cfg, target, broker_index),
{
    assert(t1_layer::t1_global_corollaries(cfg, target));
    assert(t1_layer::invoke_temporal_safety(cfg, target));
}

proof fn m0_authorization_components_close(
    cfg: config_layer::FullConfig,
    execution: wal_runtime_layer::WalExecution,
    call: M0ProtectedCall,
)
    requires
        call.source_index < execution.events.len(),
        execution.events[call.source_index as int]
            == m0_call_global_event(call),
        {
            let target = t4_c0_layer::canonical_target_execution(
                cfg, execution,
            );
            let map = t4_c0_layer::canonical_composed_map(execution);
            let broker_index = map.points[call.source_index as int];
            &&& broker_index < target.events.len()
            &&& target.events[broker_index as int]
                == m0_call_global_event(call)
            &&& t1_layer::invoke_temporal_at(cfg, target, broker_index)
        },
    ensures m0_durably_authorized_call(cfg, execution, call),
{
}

pub proof fn m0_exact_wal_invoke_is_durably_authorized(
    cfg: config_layer::FullConfig,
    execution: wal_runtime_layer::WalExecution,
    call: M0ProtectedCall,
)
    requires
        config_layer::full_config_wf(cfg),
        wal_runtime_layer::exec(cfg, execution),
        call.source_index < execution.events.len(),
        execution.events[call.source_index as int]
            == m0_call_global_event(call),
    ensures m0_durably_authorized_call(cfg, execution, call),
{
    let target = t4_c0_layer::canonical_target_execution(cfg, execution);
    let map = t4_c0_layer::canonical_composed_map(execution);
    let source_index = call.source_index;
    let left = map.points[source_index as int];
    t4_c0_layer::canonical_closed_wal_broker_composition(cfg, execution);
    m0_invoke_survives_canonical_mapping(
        cfg, execution, target, map, call,
    );
    m0_t1_safety_authorizes_exact_invoke(
        cfg, target, call, left,
    );
    m0_authorization_components_close(cfg, execution, call);
}

pub proof fn m0_durable_authorization_exposes_t1_ancestry(
    cfg: config_layer::FullConfig,
    execution: wal_runtime_layer::WalExecution,
    call: M0ProtectedCall,
)
    requires m0_durably_authorized_call(cfg, execution, call),
    ensures {
        let target = t4_c0_layer::canonical_target_execution(cfg, execution);
        let map = t4_c0_layer::canonical_composed_map(execution);
        let broker_index = map.points[call.source_index as int];
        let records = projection_layer::pi_journal(
            target.events.take(broker_index as int),
        );
        &&& call.call == config_layer::canonical_call(cfg, call.request)
        &&& 1 <= call.ack_cut
        &&& call.ack_cut <= call.journal_cut
        &&& p2_layer::acknowledged_start_authorized(
            cfg,
            records.take(call.ack_cut as int),
            call.request,
            call.attempt,
        )
        &&& replay_layer::authorize_count_for_request(
            records.take(call.ack_cut as int), call.request,
        ) == 1
        &&& replay_layer::start_count(
            records.take(call.ack_cut as int),
            call.request,
            call.attempt,
        ) == 1
        &&& exists|return_index: nat| {
            &&& return_index < broker_index
            &&& target.events[return_index as int]
                == global_layer::GlobalEvent::JournalAppendReturn {
                    cut: call.ack_cut,
                }
        }
    },
{
}

pub open spec fn m0_retry_call_one() -> M0ProtectedCall {
    let cfg = ensure_member_full_config();
    let request = ensure_member_request_zero();
    M0ProtectedCall {
        request,
        attempt: 1,
        call: config_layer::canonical_call(cfg, request),
        journal_cut: 4,
        ack_cut: 4,
        source_index: 12,
    }
}

pub open spec fn m0_retry_call_two() -> M0ProtectedCall {
    let cfg = ensure_member_full_config();
    let request = ensure_member_request_zero();
    M0ProtectedCall {
        request,
        attempt: 2,
        call: config_layer::canonical_call(cfg, request),
        journal_cut: 5,
        ack_cut: 5,
        source_index: 23,
    }
}

pub open spec fn m0_zero_protected_execution(
    request: replay_layer::RequestId,
    initial_members: ISet<config_layer::Resource>,
) -> M0ProtectedExecution {
    M0ProtectedExecution {
        configs: Seq::empty().push(
            m0_initial_protected_state(request, initial_members),
        ),
        events: Seq::empty(),
    }
}

pub open spec fn m0_extend_protected_execution(
    execution: M0ProtectedExecution,
    event: M0ProtectedEvent,
) -> M0ProtectedExecution {
    M0ProtectedExecution {
        configs: execution.configs.push(
            m0_protected_apply(execution.configs.last(), event),
        ),
        events: execution.events.push(event),
    }
}

pub proof fn m0_zero_protected_execution_exec(
    request: replay_layer::RequestId,
    initial_members: ISet<config_layer::Resource>,
)
    ensures m0_protected_exec(
        request,
        initial_members,
        m0_zero_protected_execution(request, initial_members),
    ),
{
}

pub proof fn m0_extend_protected_execution_exec(
    request: replay_layer::RequestId,
    initial_members: ISet<config_layer::Resource>,
    execution: M0ProtectedExecution,
    event: M0ProtectedEvent,
)
    requires
        m0_protected_exec(request, initial_members, execution),
        m0_protected_enabled(execution.configs.last(), event),
    ensures
        m0_protected_exec(
            request,
            initial_members,
            m0_extend_protected_execution(execution, event),
        ),
        m0_extend_protected_execution(execution, event).events
            == execution.events.push(event),
        m0_extend_protected_execution(execution, event).configs.last()
            == m0_protected_apply(execution.configs.last(), event),
{
    let extended = m0_extend_protected_execution(execution, event);
    let old_len = execution.events.len();
    assert(execution.configs.len() == old_len + 1);
    assert(execution.configs.last()
        == execution.configs[old_len as int]);
    assert forall|index: nat| index < extended.events.len() implies
        #[trigger] m0_protected_step(
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
                == m0_protected_apply(execution.configs.last(), event));
        }
    }
}

pub open spec fn m0_append_stutters(
    execution: M0ProtectedExecution,
    count: nat,
) -> M0ProtectedExecution
    decreases count
{
    if count == 0 {
        execution
    } else {
        m0_append_stutters(
            m0_extend_protected_execution(
                execution, M0ProtectedEvent::Stutter,
            ),
            (count - 1) as nat,
        )
    }
}

pub proof fn m0_append_stutters_exec(
    request: replay_layer::RequestId,
    initial_members: ISet<config_layer::Resource>,
    execution: M0ProtectedExecution,
    count: nat,
)
    requires m0_protected_exec(request, initial_members, execution),
    ensures
        m0_protected_exec(
            request,
            initial_members,
            m0_append_stutters(execution, count),
        ),
        m0_append_stutters(execution, count).events.len()
            == execution.events.len() + count,
        m0_append_stutters(execution, count).configs.last()
            == execution.configs.last(),
        m0_protected_calls(
            m0_append_stutters(execution, count).events,
        ) == m0_protected_calls(execution.events),
    decreases count,
{
    if count > 0 {
        let extended = m0_extend_protected_execution(
            execution, M0ProtectedEvent::Stutter,
        );
        assert(m0_protected_enabled(
            execution.configs.last(), M0ProtectedEvent::Stutter,
        ));
        m0_extend_protected_execution_exec(
            request,
            initial_members,
            execution,
            M0ProtectedEvent::Stutter,
        );
        m0_append_stutters_exec(
            request,
            initial_members,
            extended,
            (count - 1) as nat,
        );
        m0_protected_calls_push(
            execution.events, M0ProtectedEvent::Stutter,
        );
    }
}

pub open spec fn m0_retry_protected_execution()
    -> M0ProtectedExecution
{
    let request = ensure_member_request_zero();
    let initial = ISet::<config_layer::Resource>::empty();
    let p0 = m0_zero_protected_execution(request, initial);
    let p1 = m0_append_stutters(p0, 12);
    let p2 = m0_extend_protected_execution(
        p1,
        M0ProtectedEvent::BrokerInvoke { call: m0_retry_call_one() },
    );
    let p3 = m0_extend_protected_execution(
        p2,
        M0ProtectedEvent::ServiceLinearize { call_ref: 0 },
    );
    let p4 = m0_extend_protected_execution(
        p3,
        M0ProtectedEvent::ServiceReturn {
            call_ref: 0,
            observation: replay_layer::Observation::Success(
                ensure_member_success_value(),
            ),
        },
    );
    let p5 = m0_append_stutters(p4, 9);
    let p6 = m0_extend_protected_execution(
        p5,
        M0ProtectedEvent::BrokerInvoke { call: m0_retry_call_two() },
    );
    let p7 = m0_extend_protected_execution(
        p6,
        M0ProtectedEvent::ServiceReturn {
            call_ref: 1,
            observation: replay_layer::Observation::Failure,
        },
    );
    m0_append_stutters(p7, 6)
}

pub proof fn m0_retry_protected_execution_exec()
    ensures
        m0_protected_exec(
            ensure_member_request_zero(),
            ISet::<config_layer::Resource>::empty(),
            m0_retry_protected_execution(),
        ),
        m0_retry_protected_execution().events.len() == 32,
        m0_retry_protected_execution().configs.last().calls
            == Seq::empty()
                .push(m0_retry_call_one())
                .push(m0_retry_call_two()),
        m0_retry_protected_execution().configs.last()
            .linearized_refs.contains(0),
        !m0_retry_protected_execution().configs.last()
            .linearized_refs.contains(1),
        m0_retry_protected_execution().configs.last()
            .completed_refs.contains(0),
        m0_retry_protected_execution().configs.last()
            .completed_refs.contains(1),
        m0_retry_protected_execution().configs.last()
            .environment_additions == ISet::empty(),
        m0_retry_protected_execution().configs.last().members.contains(
            ensure_member_target(ensure_member_request_zero()),
        ),
{
    let request = ensure_member_request_zero();
    let initial = ISet::<config_layer::Resource>::empty();
    let p0 = m0_zero_protected_execution(request, initial);
    m0_zero_protected_execution_exec(request, initial);
    let p1 = m0_append_stutters(p0, 12);
    m0_append_stutters_exec(request, initial, p0, 12);
    let invoke1 = M0ProtectedEvent::BrokerInvoke {
        call: m0_retry_call_one(),
    };
    assert(m0_protected_enabled(p1.configs.last(), invoke1));
    let p2 = m0_extend_protected_execution(p1, invoke1);
    m0_extend_protected_execution_exec(
        request, initial, p1, invoke1,
    );
    assert(p2.configs.last().calls
        == Seq::empty().push(m0_retry_call_one()));
    let linearize1 = M0ProtectedEvent::ServiceLinearize { call_ref: 0 };
    assert(m0_protected_enabled(p2.configs.last(), linearize1));
    let p3 = m0_extend_protected_execution(p2, linearize1);
    m0_extend_protected_execution_exec(
        request, initial, p2, linearize1,
    );
    assert(p3.configs.last().linearized_refs.contains(0));
    let return1 = M0ProtectedEvent::ServiceReturn {
        call_ref: 0,
        observation: replay_layer::Observation::Success(
            ensure_member_success_value(),
        ),
    };
    assert(m0_protected_enabled(p3.configs.last(), return1));
    let p4 = m0_extend_protected_execution(p3, return1);
    m0_extend_protected_execution_exec(
        request, initial, p3, return1,
    );
    let p5 = m0_append_stutters(p4, 9);
    m0_append_stutters_exec(request, initial, p4, 9);
    let invoke2 = M0ProtectedEvent::BrokerInvoke {
        call: m0_retry_call_two(),
    };
    assert(m0_protected_enabled(p5.configs.last(), invoke2));
    let p6 = m0_extend_protected_execution(p5, invoke2);
    m0_extend_protected_execution_exec(
        request, initial, p5, invoke2,
    );
    assert(p6.configs.last().calls
        == Seq::empty()
            .push(m0_retry_call_one())
            .push(m0_retry_call_two()));
    let return2 = M0ProtectedEvent::ServiceReturn {
        call_ref: 1,
        observation: replay_layer::Observation::Failure,
    };
    assert(m0_protected_enabled(p6.configs.last(), return2));
    let p7 = m0_extend_protected_execution(p6, return2);
    m0_extend_protected_execution_exec(
        request, initial, p6, return2,
    );
    m0_append_stutters_exec(request, initial, p7, 6);
}

pub open spec fn m0_retry_protected_event_shape(
    events: Seq<M0ProtectedEvent>,
) -> bool {
    &&& events.len() == 32
    &&& forall|index: nat| index < 12 ==>
        events[index as int] == M0ProtectedEvent::Stutter
    &&& events[12] == M0ProtectedEvent::BrokerInvoke {
        call: m0_retry_call_one(),
    }
    &&& events[13] == M0ProtectedEvent::ServiceLinearize { call_ref: 0 }
    &&& events[14] == M0ProtectedEvent::ServiceReturn {
        call_ref: 0,
        observation: replay_layer::Observation::Success(
            ensure_member_success_value(),
        ),
    }
    &&& forall|index: nat| 15 <= index && index < 24 ==>
        events[index as int] == M0ProtectedEvent::Stutter
    &&& events[24] == M0ProtectedEvent::BrokerInvoke {
        call: m0_retry_call_two(),
    }
    &&& events[25] == M0ProtectedEvent::ServiceReturn {
        call_ref: 1,
        observation: replay_layer::Observation::Failure,
    }
    &&& forall|index: nat| 26 <= index && index < 32 ==>
        events[index as int] == M0ProtectedEvent::Stutter
}

pub proof fn m0_retry_protected_execution_has_shape()
    ensures m0_retry_protected_event_shape(
        m0_retry_protected_execution().events,
    ),
{
    reveal_with_fuel(m0_append_stutters, 40);
    assert forall|index: nat| index < 12 implies
        m0_retry_protected_execution().events[index as int]
            == M0ProtectedEvent::Stutter by {
    }
    assert forall|index: nat| 15 <= index && index < 24 implies
        m0_retry_protected_execution().events[index as int]
            == M0ProtectedEvent::Stutter by {
    }
    assert forall|index: nat| 26 <= index && index < 32 implies
        m0_retry_protected_execution().events[index as int]
            == M0ProtectedEvent::Stutter by {
    }
}

proof fn m0_retry_protected_coupling_state_shape()
    ensures
        m0_retry_protected_execution().configs[13].calls
            == Seq::empty().push(m0_retry_call_one()),
        m0_retry_protected_execution().configs[14].calls
            == Seq::empty().push(m0_retry_call_one()),
        m0_retry_protected_execution().configs[25].calls
            == Seq::empty()
                .push(m0_retry_call_one())
                .push(m0_retry_call_two()),
{
    reveal_with_fuel(m0_append_stutters, 40);
}

pub open spec fn m0_adapter_event_is_service_stutter(
    event: A1AdapterEvent,
) -> bool {
    match event {
        A1AdapterEvent::Observe { event: global } => {
            !(global is InvokeEvent) && !(global is DeliverEvent)
        },
        A1AdapterEvent::ServiceLinearize { .. }
        | A1AdapterEvent::EnvironmentAdd { .. } => false,
    }
}

pub open spec fn m0_retry_adapter_event_shape(
    execution: A1AdapterExecution,
) -> bool {
    &&& execution.events.len() == 32
    &&& forall|index: nat| index < 12 ==>
        m0_adapter_event_is_service_stutter(execution.events[index as int])
    &&& execution.events[12] == A1AdapterEvent::Observe {
        event: m0_call_global_event(m0_retry_call_one()),
    }
    &&& execution.configs[12].globals.len() == 12
    &&& execution.events[13]
        == A1AdapterEvent::ServiceLinearize { attempt: 1 }
    &&& execution.events[14] == A1AdapterEvent::Observe {
        event: global_layer::GlobalEvent::DeliverEvent {
            request: ensure_member_request_zero(),
            attempt: 1,
            observation: replay_layer::Observation::Success(
                ensure_member_success_value(),
            ),
            journal_cut: 4,
        },
    }
    &&& forall|index: nat| 15 <= index && index < 24 ==>
        m0_adapter_event_is_service_stutter(execution.events[index as int])
    &&& execution.events[24] == A1AdapterEvent::Observe {
        event: m0_call_global_event(m0_retry_call_two()),
    }
    &&& execution.configs[24].globals.len() == 23
    &&& execution.events[25] == A1AdapterEvent::Observe {
        event: global_layer::GlobalEvent::DeliverEvent {
            request: ensure_member_request_zero(),
            attempt: 2,
            observation: replay_layer::Observation::Failure,
            journal_cut: 5,
        },
    }
    &&& forall|index: nat| 26 <= index && index < 32 ==>
        m0_adapter_event_is_service_stutter(execution.events[index as int])
}

proof fn m0_retry_adapter_initial_segment_shape()
    ensures
        forall|index: nat| index < 12 ==>
            m0_adapter_event_is_service_stutter(
                a1_retry_adapter_execution().events[index as int],
            ),
        a1_retry_adapter_execution().events[12]
            == (A1AdapterEvent::Observe {
                event: m0_call_global_event(m0_retry_call_one()),
            }),
        a1_retry_adapter_execution().configs[12].globals.len() == 12,
        a1_retry_adapter_execution().events[13]
            == (A1AdapterEvent::ServiceLinearize { attempt: 1 }),
        a1_retry_adapter_execution().events[14]
            == (A1AdapterEvent::Observe {
                event: global_layer::GlobalEvent::DeliverEvent {
                    request: ensure_member_request_zero(),
                    attempt: 1,
                    observation: replay_layer::Observation::Success(
                        ensure_member_success_value(),
                    ),
                    journal_cut: 4,
                },
            }),
{
    assert forall|index: nat| index < 12 implies
        m0_adapter_event_is_service_stutter(
            a1_retry_adapter_execution().events[index as int],
        ) by {
        if index < 3 {
        } else if index < 6 {
        } else if index < 9 {
        } else {
            assert(index < 12);
        }
    }
}

proof fn m0_retry_adapter_retry_segment_shape()
    ensures
        forall|index: nat| 15 <= index && index < 24 ==>
            m0_adapter_event_is_service_stutter(
                a1_retry_adapter_execution().events[index as int],
            ),
        a1_retry_adapter_execution().events[24]
            == (A1AdapterEvent::Observe {
                event: m0_call_global_event(m0_retry_call_two()),
            }),
        a1_retry_adapter_execution().configs[24].globals.len() == 23,
        a1_retry_adapter_execution().events[25]
            == (A1AdapterEvent::Observe {
                event: global_layer::GlobalEvent::DeliverEvent {
                    request: ensure_member_request_zero(),
                    attempt: 2,
                    observation: replay_layer::Observation::Failure,
                    journal_cut: 5,
                },
            }),
{
    assert forall|index: nat| 15 <= index && index < 24 implies
        m0_adapter_event_is_service_stutter(
            a1_retry_adapter_execution().events[index as int],
        ) by {
        if index < 21 {
        } else {
            assert(index < 24);
        }
    }
}

proof fn m0_retry_adapter_terminal_segment_shape()
    ensures forall|index: nat| 26 <= index && index < 32 ==>
        m0_adapter_event_is_service_stutter(
            a1_retry_adapter_execution().events[index as int],
        ),
{
    assert forall|index: nat| 26 <= index && index < 32 implies
        m0_adapter_event_is_service_stutter(
            a1_retry_adapter_execution().events[index as int],
        ) by {
        if index < 29 {
        } else {
            assert(index < 32);
        }
    }
}

pub proof fn m0_retry_adapter_execution_has_shape()
    ensures m0_retry_adapter_event_shape(a1_retry_adapter_execution()),
{
    a1_retry_adapter_execution_exec();
    m0_retry_adapter_initial_segment_shape();
    m0_retry_adapter_retry_segment_shape();
    m0_retry_adapter_terminal_segment_shape();
}

pub proof fn m0_retry_adapter_and_service_are_coupled()
    ensures m0_coupled_exec(
        ensure_member_request_zero(),
        ISet::<config_layer::Resource>::empty(),
        a1_retry_adapter_execution(),
        m0_retry_protected_execution(),
    ),
{
    let request = ensure_member_request_zero();
    let initial = ISet::<config_layer::Resource>::empty();
    let adapter = a1_retry_adapter_execution();
    let protected = m0_retry_protected_execution();
    a1_retry_adapter_execution_exec();
    m0_retry_protected_execution_exec();
    m0_retry_protected_execution_has_shape();
    m0_retry_protected_coupling_state_shape();
    m0_retry_adapter_execution_has_shape();
    a1_every_exec_configuration_satisfies_invariant(
        request, initial, adapter,
    );
    assert(adapter.events.len() == 32);
    assert(protected.events.len() == 32);
    assert forall|index: nat| index < adapter.events.len() implies
        #[trigger] m0_event_coupled(
            adapter.configs[index as int],
            adapter.events[index as int],
            protected.configs[index as int],
            protected.events[index as int],
        ) by {
        if index < 12 {
            assert(protected.events[index as int]
                == M0ProtectedEvent::Stutter);
            assert(m0_event_coupled(
                adapter.configs[index as int],
                adapter.events[index as int],
                protected.configs[index as int],
                protected.events[index as int],
            ));
        } else if index == 12 {
            assert(protected.events[index as int]
                == M0ProtectedEvent::BrokerInvoke {
                    call: m0_retry_call_one(),
                });
            assert(m0_event_coupled(
                adapter.configs[index as int],
                adapter.events[index as int],
                protected.configs[index as int],
                protected.events[index as int],
            ));
        } else if index == 13 {
            assert(protected.events[index as int]
                == M0ProtectedEvent::ServiceLinearize { call_ref: 0 });
            assert(adapter.configs[index as int].request == request);
            assert(protected.configs[index as int].calls[0]
                == m0_retry_call_one());
            assert(exists|call_ref: nat| {
                &&& call_ref < protected.configs[index as int].calls.len()
                &&& protected.configs[index as int].calls[
                    call_ref as int
                ].request == adapter.configs[index as int].request
                &&& protected.configs[index as int].calls[
                    call_ref as int
                ].attempt == 1
                &&& protected.events[index as int]
                    == M0ProtectedEvent::ServiceLinearize { call_ref }
            }) by {
                let call_ref: nat = 0;
            }
            assert(m0_event_coupled(
                adapter.configs[index as int],
                adapter.events[index as int],
                protected.configs[index as int],
                protected.events[index as int],
            ));
        } else if index == 14 {
            assert(protected.events[index as int]
                == M0ProtectedEvent::ServiceReturn {
                    call_ref: 0,
                    observation: replay_layer::Observation::Success(
                        ensure_member_success_value(),
                    ),
                });
            assert(protected.configs[index as int].calls[0]
                == m0_retry_call_one());
            assert(exists|call_ref: nat| {
                &&& call_ref < protected.configs[index as int].calls.len()
                &&& protected.configs[index as int].calls[
                    call_ref as int
                ].request == request
                &&& protected.configs[index as int].calls[
                    call_ref as int
                ].attempt == 1
                &&& protected.events[index as int]
                    == M0ProtectedEvent::ServiceReturn {
                        call_ref,
                        observation: replay_layer::Observation::Success(
                            ensure_member_success_value(),
                        ),
                    }
            }) by {
                let call_ref: nat = 0;
            }
            assert(m0_event_coupled(
                adapter.configs[index as int],
                adapter.events[index as int],
                protected.configs[index as int],
                protected.events[index as int],
            ));
        } else if index < 24 {
            assert(15 <= index);
            assert(protected.events[index as int]
                == M0ProtectedEvent::Stutter);
            assert(m0_event_coupled(
                adapter.configs[index as int],
                adapter.events[index as int],
                protected.configs[index as int],
                protected.events[index as int],
            ));
        } else if index == 24 {
            assert(protected.events[index as int]
                == M0ProtectedEvent::BrokerInvoke {
                    call: m0_retry_call_two(),
                });
            assert(m0_event_coupled(
                adapter.configs[index as int],
                adapter.events[index as int],
                protected.configs[index as int],
                protected.events[index as int],
            ));
        } else if index == 25 {
            assert(protected.events[index as int]
                == M0ProtectedEvent::ServiceReturn {
                    call_ref: 1,
                    observation: replay_layer::Observation::Failure,
                });
            assert(protected.configs[index as int].calls[1]
                == m0_retry_call_two());
            assert(exists|call_ref: nat| {
                &&& call_ref < protected.configs[index as int].calls.len()
                &&& protected.configs[index as int].calls[
                    call_ref as int
                ].request == request
                &&& protected.configs[index as int].calls[
                    call_ref as int
                ].attempt == 2
                &&& protected.events[index as int]
                    == M0ProtectedEvent::ServiceReturn {
                        call_ref,
                        observation: replay_layer::Observation::Failure,
                    }
            }) by {
                let call_ref: nat = 1;
            }
            assert(m0_event_coupled(
                adapter.configs[index as int],
                adapter.events[index as int],
                protected.configs[index as int],
                protected.events[index as int],
            ));
        } else {
            assert(26 <= index && index < 32);
            assert(protected.events[index as int]
                == M0ProtectedEvent::Stutter);
            assert(m0_event_coupled(
                adapter.configs[index as int],
                adapter.events[index as int],
                protected.configs[index as int],
                protected.events[index as int],
            ));
        }
    }
}

pub open spec fn m0_linearization_count(
    events: Seq<M0ProtectedEvent>,
) -> nat
    decreases events.len()
{
    if events.len() == 0 {
        0
    } else {
        m0_linearization_count(events.drop_last()) + match events.last() {
            M0ProtectedEvent::ServiceLinearize { .. } => 1nat,
            M0ProtectedEvent::BrokerInvoke { .. }
            | M0ProtectedEvent::ServiceReturn { .. }
            | M0ProtectedEvent::EnvironmentAdd { .. }
            | M0ProtectedEvent::Stutter => 0nat,
        }
    }
}

pub open spec fn m0_target_action_provenance(
    execution: M0ProtectedExecution,
) -> bool {
    forall|index: nat| index < execution.events.len() ==> match
        #[trigger] execution.events[index as int]
    {
        M0ProtectedEvent::ServiceLinearize { call_ref } => {
            &&& call_ref < execution.configs[index as int].calls.len()
            &&& execution.configs[index as int].calls[
                call_ref as int
            ].request == execution.configs[index as int].request
            &&& !execution.configs[index as int]
                .completed_refs.contains(call_ref)
            &&& execution.configs[(index + 1) as int]
                .linearized_refs.contains(call_ref)
            &&& execution.configs[(index + 1) as int].members.contains(
                ensure_member_target(
                    execution.configs[index as int].request,
                ),
            )
        },
        M0ProtectedEvent::BrokerInvoke { .. }
        | M0ProtectedEvent::ServiceReturn { .. }
        | M0ProtectedEvent::EnvironmentAdd { .. }
        | M0ProtectedEvent::Stutter => {
            !m0_target_membership_changed(
                execution.configs[index as int],
                execution.configs[(index + 1) as int],
            )
        },
    }
}

pub proof fn m0_protected_exec_derives_target_action_provenance(
    request: replay_layer::RequestId,
    initial_members: ISet<config_layer::Resource>,
    execution: M0ProtectedExecution,
)
    requires m0_protected_exec(request, initial_members, execution),
    ensures m0_target_action_provenance(execution),
{
    assert forall|index: nat| index < execution.events.len() implies match
        #[trigger] execution.events[index as int]
    {
        M0ProtectedEvent::ServiceLinearize { call_ref } => {
            &&& call_ref < execution.configs[index as int].calls.len()
            &&& execution.configs[index as int].calls[
                call_ref as int
            ].request == execution.configs[index as int].request
            &&& !execution.configs[index as int]
                .completed_refs.contains(call_ref)
            &&& execution.configs[(index + 1) as int]
                .linearized_refs.contains(call_ref)
            &&& execution.configs[(index + 1) as int].members.contains(
                ensure_member_target(
                    execution.configs[index as int].request,
                ),
            )
        },
        M0ProtectedEvent::BrokerInvoke { .. }
        | M0ProtectedEvent::ServiceReturn { .. }
        | M0ProtectedEvent::EnvironmentAdd { .. }
        | M0ProtectedEvent::Stutter => {
            !m0_target_membership_changed(
                execution.configs[index as int],
                execution.configs[(index + 1) as int],
            )
        },
    } by {
        let before = execution.configs[index as int];
        let event = execution.events[index as int];
        let after = execution.configs[(index + 1) as int];
        assert(m0_protected_step(before, event, after));
        match event {
            M0ProtectedEvent::ServiceLinearize { .. } => {
                m0_target_change_requires_linearization(
                    before, event, after,
                );
            },
            M0ProtectedEvent::EnvironmentAdd { resource } => {
                m0_environment_cannot_add_target(
                    before, resource, after,
                );
            },
            M0ProtectedEvent::BrokerInvoke { .. }
            | M0ProtectedEvent::ServiceReturn { .. }
            | M0ProtectedEvent::Stutter => {},
        }
    }
}

pub proof fn m0_retry_has_one_target_action()
    ensures
        m0_linearization_count(
            m0_retry_protected_execution().events,
        ) == 1,
        m0_target_action_provenance(m0_retry_protected_execution()),
{
    m0_retry_protected_execution_exec();
    m0_retry_protected_execution_has_shape();
    m0_protected_exec_derives_target_action_provenance(
        ensure_member_request_zero(),
        ISet::<config_layer::Resource>::empty(),
        m0_retry_protected_execution(),
    );
    reveal_with_fuel(m0_linearization_count, 40);
}

pub proof fn m0_retry_calls_have_exact_wal_origins()
    ensures
        a1_retry_wal_execution().events[
            m0_retry_call_one().source_index as int
        ] == m0_call_global_event(m0_retry_call_one()),
        a1_retry_wal_execution().events[
            m0_retry_call_two().source_index as int
        ] == m0_call_global_event(m0_retry_call_two()),
{
    a1_retry_wal_execution_exec();
    a1_retry_has_explicit_crash_recovery_shape();
}

pub proof fn m0_retry_calls_are_durably_authorized()
    ensures
        m0_durably_authorized_call(
            ensure_member_full_config(),
            a1_retry_wal_execution(),
            m0_retry_call_one(),
        ),
        m0_durably_authorized_call(
            ensure_member_full_config(),
            a1_retry_wal_execution(),
            m0_retry_call_two(),
        ),
{
    let cfg = ensure_member_full_config();
    let execution = a1_retry_wal_execution();
    ensure_member_full_config_is_well_formed();
    a1_retry_wal_execution_exec();
    m0_retry_calls_have_exact_wal_origins();
    assert(m0_retry_call_one().source_index < execution.events.len());
    assert(m0_retry_call_two().source_index < execution.events.len());
    m0_exact_wal_invoke_is_durably_authorized(
        cfg, execution, m0_retry_call_one(),
    );
    m0_exact_wal_invoke_is_durably_authorized(
        cfg, execution, m0_retry_call_two(),
    );
}

pub open spec fn m0_calls_have_origins(
    globals: Seq<global_layer::GlobalEvent>,
    calls: Seq<M0ProtectedCall>,
) -> bool {
    forall|call_ref: nat| call_ref < calls.len() ==> {
        let call = #[trigger] calls[call_ref as int];
        &&& call.source_index < globals.len()
        &&& globals[call.source_index as int] == m0_call_global_event(call)
    }
}

pub proof fn m0_coupled_exec_prefix(
    request: replay_layer::RequestId,
    initial_members: ISet<config_layer::Resource>,
    adapter: A1AdapterExecution,
    protected: M0ProtectedExecution,
    length: nat,
)
    requires
        m0_coupled_exec(
            request, initial_members, adapter, protected,
        ),
        length <= adapter.events.len(),
    ensures m0_coupled_exec(
        request,
        initial_members,
        a1_execution_prefix(adapter, length),
        m0_protected_execution_prefix(protected, length),
    ),
{
    let adapter_prefix = a1_execution_prefix(adapter, length);
    let protected_prefix = m0_protected_execution_prefix(protected, length);
    a1_exec_prefix(request, initial_members, adapter, length);
    m0_protected_exec_prefix(
        request, initial_members, protected, length,
    );
    assert(adapter_prefix.events.len() == length);
    assert(protected_prefix.events.len() == length);
    assert forall|index: nat| index < length implies
        #[trigger] m0_event_coupled(
            adapter_prefix.configs[index as int],
            adapter_prefix.events[index as int],
            protected_prefix.configs[index as int],
            protected_prefix.events[index as int],
        ) by {
        assert(index < adapter.events.len());
        assert(adapter_prefix.configs[index as int]
            == adapter.configs[index as int]);
        assert(adapter_prefix.events[index as int]
            == adapter.events[index as int]);
        assert(protected_prefix.configs[index as int]
            == protected.configs[index as int]);
        assert(protected_prefix.events[index as int]
            == protected.events[index as int]);
    }
}

proof fn m0_prior_origins_survive_push(
    globals: Seq<global_layer::GlobalEvent>,
    event: global_layer::GlobalEvent,
    calls: Seq<M0ProtectedCall>,
)
    requires m0_calls_have_origins(globals, calls),
    ensures m0_calls_have_origins(globals.push(event), calls),
{
    assert forall|call_ref: nat| call_ref < calls.len() implies {
        let call = #[trigger] calls[call_ref as int];
        &&& call.source_index < globals.push(event).len()
        &&& globals.push(event)[call.source_index as int]
            == m0_call_global_event(call)
    } by {
        let call = calls[call_ref as int];
        assert(call.source_index < globals.len());
        assert(globals.push(event)[call.source_index as int]
            == globals[call.source_index as int]);
    }
}

proof fn m0_append_new_origin(
    globals: Seq<global_layer::GlobalEvent>,
    calls: Seq<M0ProtectedCall>,
    call: M0ProtectedCall,
)
    requires
        m0_calls_have_origins(globals, calls),
        call.source_index == globals.len(),
    ensures m0_calls_have_origins(
        globals.push(m0_call_global_event(call)), calls.push(call),
    ),
{
    assert forall|call_ref: nat| call_ref < calls.push(call).len() implies {
        let selected = #[trigger] calls.push(call)[call_ref as int];
        &&& selected.source_index
            < globals.push(m0_call_global_event(call)).len()
        &&& globals.push(m0_call_global_event(call))[
            selected.source_index as int
        ] == m0_call_global_event(selected)
    } by {
        if call_ref < calls.len() {
            let selected = calls[call_ref as int];
            assert(calls.push(call)[call_ref as int] == selected);
            assert(selected.source_index < globals.len());
        } else {
            assert(call_ref == calls.len());
            assert(calls.push(call)[call_ref as int] == call);
        }
    }
}

pub proof fn m0_coupled_final_calls_have_exact_origins(
    request: replay_layer::RequestId,
    initial_members: ISet<config_layer::Resource>,
    adapter: A1AdapterExecution,
    protected: M0ProtectedExecution,
)
    requires m0_coupled_exec(
        request, initial_members, adapter, protected,
    ),
    ensures m0_calls_have_origins(
        a1_global_trace(adapter.events),
        protected.configs[protected.events.len() as int].calls,
    ),
    decreases adapter.events.len(),
{
    if adapter.events.len() == 0 {
        assert(protected.events.len() == 0);
        assert(protected.configs[0]
            == m0_initial_protected_state(request, initial_members));
    } else {
        let last_index: nat = (adapter.events.len() - 1) as nat;
        let adapter_prefix = a1_execution_prefix(adapter, last_index);
        let protected_prefix = m0_protected_execution_prefix(
            protected, last_index,
        );
        m0_coupled_exec_prefix(
            request,
            initial_members,
            adapter,
            protected,
            last_index,
        );
        m0_coupled_final_calls_have_exact_origins(
            request,
            initial_members,
            adapter_prefix,
            protected_prefix,
        );
        a1_exec_final_globals_are_projected(
            request, initial_members, adapter_prefix,
        );
        let adapter_before = adapter.configs[last_index as int];
        let adapter_event = adapter.events[last_index as int];
        let protected_before = protected.configs[last_index as int];
        let protected_event = protected.events[last_index as int];
        let protected_after = protected.configs[(last_index + 1) as int];
        assert(adapter_prefix.configs[last_index as int] == adapter_before);
        assert(protected_prefix.configs[last_index as int]
            == protected_before);
        assert(m0_event_coupled(
            adapter_before,
            adapter_event,
            protected_before,
            protected_event,
        ));
        assert(m0_protected_step(
            protected_before, protected_event, protected_after,
        ));
        assert(protected_after
            == m0_protected_apply(protected_before, protected_event));
        assert(adapter.events =~= adapter_prefix.events.push(adapter_event));
        m0_a1_global_trace_push(adapter_prefix.events, adapter_event);
        match adapter_event {
            A1AdapterEvent::Observe {
                event: global @ global_layer::GlobalEvent::InvokeEvent { .. },
            } => {
                match protected_event {
                    M0ProtectedEvent::BrokerInvoke { call } => {
                        assert(call.source_index
                            == adapter_before.globals.len());
                        assert(adapter_before.globals
                            == a1_global_trace(adapter_prefix.events));
                        assert(global == m0_call_global_event(call));
                        m0_append_new_origin(
                            a1_global_trace(adapter_prefix.events),
                            protected_before.calls,
                            call,
                        );
                    },
                    M0ProtectedEvent::ServiceLinearize { .. }
                    | M0ProtectedEvent::ServiceReturn { .. }
                    | M0ProtectedEvent::EnvironmentAdd { .. }
                    | M0ProtectedEvent::Stutter => {},
                }
            },
            A1AdapterEvent::Observe { event: global } => {
                assert(!(protected_event is BrokerInvoke));
                assert(protected_after.calls == protected_before.calls);
                m0_prior_origins_survive_push(
                    a1_global_trace(adapter_prefix.events),
                    global,
                    protected_before.calls,
                );
            },
            A1AdapterEvent::ServiceLinearize { .. }
            | A1AdapterEvent::EnvironmentAdd { .. } => {
                assert(!(protected_event is BrokerInvoke));
                assert(protected_after.calls == protected_before.calls);
            },
        }
    }
}

pub proof fn m0_coupled_every_configuration_has_call_origins(
    request: replay_layer::RequestId,
    initial_members: ISet<config_layer::Resource>,
    adapter: A1AdapterExecution,
    protected: M0ProtectedExecution,
)
    requires m0_coupled_exec(
        request, initial_members, adapter, protected,
    ),
    ensures forall|index: nat| index <= adapter.events.len() ==>
        #[trigger] m0_calls_have_origins(
            a1_global_trace(adapter.events.take(index as int)),
            protected.configs[index as int].calls,
        ),
{
    assert forall|index: nat| index <= adapter.events.len() implies
        #[trigger] m0_calls_have_origins(
            a1_global_trace(adapter.events.take(index as int)),
            protected.configs[index as int].calls,
        ) by {
        let adapter_prefix = a1_execution_prefix(adapter, index);
        let protected_prefix = m0_protected_execution_prefix(
            protected, index,
        );
        m0_coupled_exec_prefix(
            request,
            initial_members,
            adapter,
            protected,
            index,
        );
        m0_coupled_final_calls_have_exact_origins(
            request,
            initial_members,
            adapter_prefix,
            protected_prefix,
        );
        assert(adapter_prefix.events
            =~= adapter.events.take(index as int));
        assert(protected_prefix.configs[index as int]
            == protected.configs[index as int]);
    }
}

proof fn m0_seq_prefix_reflexive<A>(sequence: Seq<A>)
    ensures append_layer::is_prefix(sequence, sequence),
{
    assert(sequence.take(sequence.len() as int) =~= sequence);
}

proof fn m0_seq_prefix_survives_push<A>(
    prefix: Seq<A>,
    whole: Seq<A>,
    value: A,
)
    requires append_layer::is_prefix(prefix, whole),
    ensures append_layer::is_prefix(prefix, whole.push(value)),
{
    assert(prefix.len() <= whole.len());
    assert(whole.push(value).take(prefix.len() as int)
        =~= whole.take(prefix.len() as int));
}

pub proof fn m0_a1_global_trace_prefix(
    events: Seq<A1AdapterEvent>,
    length: nat,
)
    requires length <= events.len(),
    ensures append_layer::is_prefix(
        a1_global_trace(events.take(length as int)),
        a1_global_trace(events),
    ),
    decreases events.len(),
{
    if length == events.len() {
        assert(events.take(length as int) =~= events);
        m0_seq_prefix_reflexive(a1_global_trace(events));
    } else {
        let prefix = events.drop_last();
        let event = events.last();
        assert(length <= prefix.len());
        assert(events.take(length as int) =~= prefix.take(length as int));
        m0_a1_global_trace_prefix(prefix, length);
        m0_a1_global_trace_push(prefix, event);
        assert(events =~= prefix.push(event));
        match event {
            A1AdapterEvent::Observe { event: global } => {
                m0_seq_prefix_survives_push(
                    a1_global_trace(prefix.take(length as int)),
                    a1_global_trace(prefix),
                    global,
                );
            },
            A1AdapterEvent::ServiceLinearize { .. }
            | A1AdapterEvent::EnvironmentAdd { .. } => {},
        }
    }
}

pub proof fn m0_coupled_linearization_is_durably_authorized(
    cfg: config_layer::FullConfig,
    request: replay_layer::RequestId,
    initial_members: ISet<config_layer::Resource>,
    adapter: A1AdapterExecution,
    protected: M0ProtectedExecution,
    wal: wal_runtime_layer::WalExecution,
    index: nat,
    call_ref: nat,
)
    requires
        config_layer::full_config_wf(cfg),
        m0_coupled_exec(
            request, initial_members, adapter, protected,
        ),
        a1_global_trace(adapter.events) == wal.events,
        wal_runtime_layer::exec(cfg, wal),
        index < protected.events.len(),
        protected.events[index as int]
            == (M0ProtectedEvent::ServiceLinearize { call_ref }),
    ensures
        call_ref < protected.configs[index as int].calls.len(),
        protected.configs[index as int].calls[
            call_ref as int
        ].request == protected.configs[index as int].request,
        m0_durably_authorized_call(
            cfg,
            wal,
            protected.configs[index as int].calls[call_ref as int],
        ),
{
    let call = protected.configs[index as int].calls[call_ref as int];
    m0_protected_exec_derives_target_action_provenance(
        request, initial_members, protected,
    );
    assert(call_ref < protected.configs[index as int].calls.len());
    m0_coupled_every_configuration_has_call_origins(
        request, initial_members, adapter, protected,
    );
    assert(m0_calls_have_origins(
        a1_global_trace(adapter.events.take(index as int)),
        protected.configs[index as int].calls,
    ));
    assert(call.source_index
        < a1_global_trace(adapter.events.take(index as int)).len());
    assert(a1_global_trace(adapter.events.take(index as int))[
        call.source_index as int
    ] == m0_call_global_event(call));
    m0_a1_global_trace_prefix(adapter.events, index);
    assert(append_layer::is_prefix(
        a1_global_trace(adapter.events.take(index as int)),
        a1_global_trace(adapter.events),
    ));
    assert(a1_global_trace(adapter.events)[call.source_index as int]
        == m0_call_global_event(call));
    assert(call.source_index < wal.events.len());
    assert(wal.events[call.source_index as int]
        == m0_call_global_event(call));
    m0_exact_wal_invoke_is_durably_authorized(cfg, wal, call);
}

// This is the reusable closed-interface deployment boundary for M0.  It
// packages the independently checked component executions and their two
// cross-component relations.  It deliberately does not claim that production
// processes, descriptors, credentials, or network endpoints enforce the same
// boundary; those require a later implementation/deployment refinement.
pub open spec fn m0_deployment_exec(
    cfg: config_layer::FullConfig,
    request: replay_layer::RequestId,
    initial_members: ISet<config_layer::Resource>,
    adapter: A1AdapterExecution,
    protected: M0ProtectedExecution,
    wal: wal_runtime_layer::WalExecution,
) -> bool {
    &&& config_layer::full_config_wf(cfg)
    &&& m0_coupled_exec(
        request, initial_members, adapter, protected,
    )
    &&& wal_runtime_layer::exec(cfg, wal)
    &&& a1_global_trace(adapter.events) == wal.events
}

pub open spec fn m0_every_linearization_durably_authorized(
    cfg: config_layer::FullConfig,
    wal: wal_runtime_layer::WalExecution,
    protected: M0ProtectedExecution,
) -> bool {
    forall|index: nat| index < protected.events.len() ==> match
        #[trigger] protected.events[index as int]
    {
        M0ProtectedEvent::ServiceLinearize { call_ref } => {
            &&& call_ref < protected.configs[index as int].calls.len()
            &&& m0_durably_authorized_call(
                cfg,
                wal,
                protected.configs[index as int].calls[call_ref as int],
            )
        },
        M0ProtectedEvent::BrokerInvoke { .. }
        | M0ProtectedEvent::ServiceReturn { .. }
        | M0ProtectedEvent::EnvironmentAdd { .. }
        | M0ProtectedEvent::Stutter => true,
    }
}

pub proof fn m0_deployment_derives_authorized_linearizations(
    cfg: config_layer::FullConfig,
    request: replay_layer::RequestId,
    initial_members: ISet<config_layer::Resource>,
    adapter: A1AdapterExecution,
    protected: M0ProtectedExecution,
    wal: wal_runtime_layer::WalExecution,
)
    requires m0_deployment_exec(
        cfg, request, initial_members, adapter, protected, wal,
    ),
    ensures m0_every_linearization_durably_authorized(
        cfg, wal, protected,
    ),
{
    assert forall|index: nat| index < protected.events.len() implies match
        #[trigger] protected.events[index as int]
    {
        M0ProtectedEvent::ServiceLinearize { call_ref } => {
            &&& call_ref < protected.configs[index as int].calls.len()
            &&& m0_durably_authorized_call(
                cfg,
                wal,
                protected.configs[index as int].calls[call_ref as int],
            )
        },
        M0ProtectedEvent::BrokerInvoke { .. }
        | M0ProtectedEvent::ServiceReturn { .. }
        | M0ProtectedEvent::EnvironmentAdd { .. }
        | M0ProtectedEvent::Stutter => true,
    } by {
        match protected.events[index as int] {
            M0ProtectedEvent::ServiceLinearize { call_ref } => {
                m0_coupled_linearization_is_durably_authorized(
                    cfg,
                    request,
                    initial_members,
                    adapter,
                    protected,
                    wal,
                    index,
                    call_ref,
                );
            },
            M0ProtectedEvent::BrokerInvoke { .. }
            | M0ProtectedEvent::ServiceReturn { .. }
            | M0ProtectedEvent::EnvironmentAdd { .. }
            | M0ProtectedEvent::Stutter => {},
        }
    }
}

pub open spec fn m0_retry_mediation_package(
    adapter: A1AdapterExecution,
    protected: M0ProtectedExecution,
    wal: wal_runtime_layer::WalExecution,
    plugged: t4_c1_layer::PluggedWalExecution<M0ProtectedHandleState>,
) -> bool {
    let cfg = ensure_member_full_config();
    let request = ensure_member_request_zero();
    let final_protected = protected.configs[protected.events.len() as int];
    let final_context = plugged.contexts[plugged.machine.events.len() as int];
    &&& adapter == a1_retry_adapter_execution()
    &&& protected == m0_retry_protected_execution()
    &&& wal == a1_retry_wal_execution()
    &&& plugged == m0_plugged_wal_execution(wal)
    &&& m0_deployment_exec(
        cfg,
        request,
        ISet::<config_layer::Resource>::empty(),
        adapter,
        protected,
        wal,
    )
    &&& t4_c1_layer::storage_parametric_context(
        cfg, m0_exclusive_handle_context(cfg),
    )
    &&& t4_c1_layer::plugged_wal_exec(
        cfg, m0_exclusive_handle_context(cfg), plugged,
    )
    &&& final_protected.calls
        == Seq::empty()
            .push(m0_retry_call_one())
            .push(m0_retry_call_two())
    &&& m0_erase_calls(final_protected.calls)
        == final_context.invocations
    &&& projection_layer::complete_mediation(
        wal.events, m0_erase_calls(final_protected.calls),
    )
    &&& projection_layer::complete_mediation(
        wal.events, final_context.invocations,
    )
    &&& m0_linearization_count(protected.events) == 1
    &&& m0_target_action_provenance(protected)
    &&& final_protected.linearized_refs.contains(0)
    &&& !final_protected.linearized_refs.contains(1)
    &&& final_protected.environment_additions == ISet::empty()
    &&& final_protected.members.contains(ensure_member_target(request))
    &&& m0_durably_authorized_call(cfg, wal, m0_retry_call_one())
    &&& m0_durably_authorized_call(cfg, wal, m0_retry_call_two())
    &&& m0_every_linearization_durably_authorized(
        cfg, wal, protected,
    )
    &&& a1_executable_retry_package(
        adapter,
        wal,
        request,
        a1_retry_run(),
        a1_retry_outcome(),
    )
}

pub proof fn t6_m0_executable_crash_retry_mediation()
    ensures m0_retry_mediation_package(
        a1_retry_adapter_execution(),
        m0_retry_protected_execution(),
        a1_retry_wal_execution(),
        m0_plugged_wal_execution(a1_retry_wal_execution()),
    ),
{
    let cfg = ensure_member_full_config();
    let request = ensure_member_request_zero();
    let initial = ISet::<config_layer::Resource>::empty();
    let adapter = a1_retry_adapter_execution();
    let protected = m0_retry_protected_execution();
    let wal = a1_retry_wal_execution();
    let plugged = m0_plugged_wal_execution(wal);
    ensure_member_full_config_is_well_formed();
    a1_concrete_executable_retry_package();
    a1_retry_adapter_execution_exec();
    a1_retry_wal_execution_exec();
    m0_retry_protected_execution_exec();
    m0_retry_adapter_and_service_are_coupled();
    assert(a1_global_trace(adapter.events) == wal.events);
    assert(m0_deployment_exec(
        cfg, request, initial, adapter, protected, wal,
    ));
    m0_deployment_derives_authorized_linearizations(
        cfg, request, initial, adapter, protected, wal,
    );
    m0_coupled_exec_derives_complete_mediation(
        request, initial, adapter, protected,
    );
    assert(protected.configs[protected.events.len() as int].calls
        == Seq::empty()
            .push(m0_retry_call_one())
            .push(m0_retry_call_two()));
    assert(projection_layer::complete_mediation(
        wal.events,
        m0_erase_calls(
            protected.configs[protected.events.len() as int].calls,
        ),
    ));
    m0_exclusive_context_is_storage_parametric(cfg);
    m0_wal_exec_has_exclusive_handle_context(cfg, wal);
    m0_exclusive_context_derives_complete_mediation(cfg, plugged);
    assert(plugged.contexts[wal.events.len() as int].invocations
        == projection_layer::pi_invocations(wal.events));
    assert(m0_erase_calls(
        protected.configs[protected.events.len() as int].calls,
    ) == plugged.contexts[wal.events.len() as int].invocations);
    m0_retry_has_one_target_action();
    m0_retry_calls_are_durably_authorized();
    m0_retry_protected_execution_has_shape();
    m0_coupled_linearization_is_durably_authorized(
        cfg,
        request,
        initial,
        adapter,
        protected,
        wal,
        13,
        0,
    );
}

pub proof fn t6_m0_mediation_nonvacuity()
    ensures exists|
        adapter: A1AdapterExecution,
        protected: M0ProtectedExecution,
        wal: wal_runtime_layer::WalExecution,
        plugged: t4_c1_layer::PluggedWalExecution<
            M0ProtectedHandleState,
        >| #![auto] {
            &&& adapter == a1_retry_adapter_execution()
            &&& protected == m0_retry_protected_execution()
            &&& wal == a1_retry_wal_execution()
            &&& plugged == m0_plugged_wal_execution(wal)
            &&& m0_retry_mediation_package(
                adapter, protected, wal, plugged,
            )
        },
{
    t6_m0_executable_crash_retry_mediation();
    assert(exists|
        adapter: A1AdapterExecution,
        protected: M0ProtectedExecution,
        wal: wal_runtime_layer::WalExecution,
        plugged: t4_c1_layer::PluggedWalExecution<
            M0ProtectedHandleState,
        >| #![auto] {
            &&& adapter == a1_retry_adapter_execution()
            &&& protected == m0_retry_protected_execution()
            &&& wal == a1_retry_wal_execution()
            &&& plugged == m0_plugged_wal_execution(wal)
            &&& m0_retry_mediation_package(
                adapter, protected, wal, plugged,
            )
        }) by {
        let adapter = a1_retry_adapter_execution();
        let protected = m0_retry_protected_execution();
        let wal = a1_retry_wal_execution();
        let plugged = m0_plugged_wal_execution(wal);
    }
}

} // verus!
