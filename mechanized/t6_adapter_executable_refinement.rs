use vstd::prelude::*;

#[path = "t6_adapter_semantic_closure.rs"]
pub mod t6_a0_layer;

verus! {

use t6_a0_layer::*;
use t6_a0_layer::t6_s0_layer;
use t6_s0_layer::t6_c0_layer;
use t6_c0_layer::t6_e0_layer;
use t6_e0_layer::t6_d0_layer;
use t6_d0_layer::*;
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

// T6-A1 gives the A0 EnsureMember interpretation an explicit operational
// model. AdapterRely is a theorem of this transition system, not an enabledness
// premise. This remains a model of an adapter/service protocol rather than a
// verification of production network or service code.

#[derive(PartialEq, Eq)]
pub enum A1AdapterMode {
    Online,
    Crashed,
    Recovering,
}

#[allow(inconsistent_fields)]
#[derive(PartialEq, Eq)]
pub enum A1AdapterEvent {
    Observe { event: global_layer::GlobalEvent },
    ServiceLinearize { attempt: replay_layer::AttemptId },
    EnvironmentAdd { resource: config_layer::Resource },
}

pub struct A1AdapterState {
    pub request: replay_layer::RequestId,
    pub initial_members: ISet<config_layer::Resource>,
    pub members: ISet<config_layer::Resource>,
    pub environment_additions: ISet<config_layer::Resource>,
    pub linearized_attempts: ISet<replay_layer::AttemptId>,
    pub failed_attempts: ISet<replay_layer::AttemptId>,
    pub globals: Seq<global_layer::GlobalEvent>,
    pub history: Seq<p0_layer::PhysicalEvent>,
    pub mode: A1AdapterMode,
    pub active: Option<replay_layer::AttemptId>,
}

pub struct A1AdapterExecution {
    pub configs: Seq<A1AdapterState>,
    pub events: Seq<A1AdapterEvent>,
}

pub open spec fn a1_physical_for_request(
    event: global_layer::GlobalEvent,
    request: replay_layer::RequestId,
) -> Option<p0_layer::PhysicalEvent> {
    match event {
        global_layer::GlobalEvent::InvokeEvent {
            request: event_request,
            attempt,
            call,
            journal_cut,
            ack_cut,
        } if event_request == request => Option::Some(
            p0_layer::PhysicalEvent::Invoke {
                request: event_request,
                attempt,
                call,
                journal_cut,
                ack_cut,
            },
        ),
        global_layer::GlobalEvent::DeliverEvent {
            request: event_request,
            attempt,
            observation,
            journal_cut,
        } if event_request == request => Option::Some(
            p0_layer::PhysicalEvent::Delivered {
                request: event_request,
                attempt,
                observation,
                journal_cut,
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

pub open spec fn a1_history_after_global(
    history: Seq<p0_layer::PhysicalEvent>,
    event: global_layer::GlobalEvent,
    request: replay_layer::RequestId,
) -> Seq<p0_layer::PhysicalEvent> {
    match a1_physical_for_request(event, request) {
        Option::Some(physical) => history.push(physical),
        Option::None => history,
    }
}

pub open spec fn a1_global_trace(
    events: Seq<A1AdapterEvent>,
) -> Seq<global_layer::GlobalEvent>
    decreases events.len()
{
    if events.len() == 0 {
        Seq::empty()
    } else {
        let prefix = a1_global_trace(events.drop_last());
        match events.last() {
            A1AdapterEvent::Observe { event } => prefix.push(event),
            A1AdapterEvent::ServiceLinearize { .. }
            | A1AdapterEvent::EnvironmentAdd { .. } => prefix,
        }
    }
}

pub open spec fn a1_initial_state(
    request: replay_layer::RequestId,
    members: ISet<config_layer::Resource>,
) -> A1AdapterState {
    A1AdapterState {
        request,
        initial_members: members,
        members,
        environment_additions: ISet::empty(),
        linearized_attempts: ISet::empty(),
        failed_attempts: ISet::empty(),
        globals: Seq::empty(),
        history: Seq::empty(),
        mode: A1AdapterMode::Online,
        active: Option::None,
    }
}

pub open spec fn a1_external_run(
    state: A1AdapterState,
) -> ExternalRun<ISet<config_layer::Resource>, EnsureMemberWitness> {
    ExternalRun {
        pre: state.initial_members,
        post: state.members,
        interference: EnsureMemberWitness {
            environment_additions: state.environment_additions,
            linearized_attempts: state.linearized_attempts,
        },
    }
}

pub open spec fn a1_observe_enabled(
    state: A1AdapterState,
    event: global_layer::GlobalEvent,
) -> bool {
    let cfg = ensure_member_full_config();
    let request = state.request;
    match event {
        global_layer::GlobalEvent::InvokeEvent {
            request: event_request,
            attempt,
            call,
            ..
        } if event_request == request => {
            &&& state.mode == A1AdapterMode::Online
            &&& state.active.is_none()
            &&& attempt > 0
            &&& attempt <= cfg.request[request].max_attempts
            &&& call == config_layer::canonical_call(cfg, request)
            &&& p1_layer::invoke_count(state.history, request, attempt) == 0
            &&& p1_layer::delivery_count(state.history, request, attempt) == 0
        },
        global_layer::GlobalEvent::DeliverEvent {
            request: event_request,
            attempt,
            observation,
            ..
        } if event_request == request => {
            &&& state.mode == A1AdapterMode::Online
            &&& state.active == Option::Some(attempt)
            &&& attempt > 0
            &&& p1_layer::delivery_count(state.history, request, attempt) == 0
            &&& match observation {
                replay_layer::Observation::Success(value) => {
                    value.id == 1
                        && state.linearized_attempts.contains(attempt)
                },
                replay_layer::Observation::Failure => {
                    !state.linearized_attempts.contains(attempt)
                },
                replay_layer::Observation::Ambiguous
                | replay_layer::Observation::InvalidResult(_) => false,
            }
        },
        global_layer::GlobalEvent::Crash => {
            state.mode != A1AdapterMode::Crashed
        },
        global_layer::GlobalEvent::BeginRecover => {
            state.mode == A1AdapterMode::Crashed
        },
        global_layer::GlobalEvent::FinishRecover => {
            state.mode == A1AdapterMode::Recovering
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
        | global_layer::GlobalEvent::IgnoreStale { .. }
        | global_layer::GlobalEvent::RetryRelease { .. }
        | global_layer::GlobalEvent::BeginScan
        | global_layer::GlobalEvent::FinishScan
        | global_layer::GlobalEvent::TruncateTail
        | global_layer::GlobalEvent::AbortScan => true,
    }
}

// This is a remote-service pending window, not the local adapter's active
// slot. An invoked request may remain able to linearize after the local
// adapter crashes and clears `active`.
pub open spec fn a1_remote_attempt_pending(
    state: A1AdapterState,
    attempt: replay_layer::AttemptId,
) -> bool {
    invoked(state.history, state.request, attempt)
        && p1_layer::delivery_count(
            state.history, state.request, attempt,
        ) == 0
        && !state.linearized_attempts.contains(attempt)
        && !state.failed_attempts.contains(attempt)
}

pub open spec fn a1_enabled(
    state: A1AdapterState,
    event: A1AdapterEvent,
) -> bool {
    match event {
        A1AdapterEvent::Observe { event } => {
            a1_observe_enabled(state, event)
        },
        A1AdapterEvent::ServiceLinearize { attempt } => {
            &&& invoked(state.history, state.request, attempt)
            &&& p1_layer::delivery_count(
                state.history, state.request, attempt,
            ) == 0
            &&& !state.linearized_attempts.contains(attempt)
            &&& !state.failed_attempts.contains(attempt)
        },
        A1AdapterEvent::EnvironmentAdd { resource } => {
            resource != ensure_member_target(state.request)
        },
    }
}

pub open spec fn a1_apply_observe(
    state: A1AdapterState,
    event: global_layer::GlobalEvent,
) -> A1AdapterState {
    let request = state.request;
    let globals = state.globals.push(event);
    let history = a1_history_after_global(state.history, event, request);
    match event {
        global_layer::GlobalEvent::InvokeEvent {
            request: event_request, attempt, ..
        } if event_request == request => A1AdapterState {
            globals,
            history,
            active: Option::Some(attempt),
            ..state
        },
        global_layer::GlobalEvent::DeliverEvent {
            request: event_request,
            attempt,
            observation: replay_layer::Observation::Failure,
            ..
        } if event_request == request => A1AdapterState {
            failed_attempts: state.failed_attempts.insert(attempt),
            globals,
            history,
            active: Option::None,
            ..state
        },
        global_layer::GlobalEvent::DeliverEvent {
            request: event_request, ..
        } if event_request == request => A1AdapterState {
            globals,
            history,
            active: Option::None,
            ..state
        },
        global_layer::GlobalEvent::Crash => A1AdapterState {
            globals,
            mode: A1AdapterMode::Crashed,
            active: Option::None,
            ..state
        },
        global_layer::GlobalEvent::BeginRecover => A1AdapterState {
            globals,
            mode: A1AdapterMode::Recovering,
            ..state
        },
        global_layer::GlobalEvent::FinishRecover => A1AdapterState {
            globals,
            mode: A1AdapterMode::Online,
            ..state
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
        | global_layer::GlobalEvent::IgnoreStale { .. }
        | global_layer::GlobalEvent::RetryRelease { .. }
        | global_layer::GlobalEvent::BeginScan
        | global_layer::GlobalEvent::FinishScan
        | global_layer::GlobalEvent::TruncateTail
        | global_layer::GlobalEvent::AbortScan => A1AdapterState {
            globals,
            ..state
        },
    }
}

pub open spec fn a1_apply(
    state: A1AdapterState,
    event: A1AdapterEvent,
) -> A1AdapterState {
    match event {
        A1AdapterEvent::Observe { event } => a1_apply_observe(state, event),
        A1AdapterEvent::ServiceLinearize { attempt } => A1AdapterState {
            members: state.members.insert(
                ensure_member_target(state.request),
            ),
            linearized_attempts: state.linearized_attempts.insert(attempt),
            ..state
        },
        A1AdapterEvent::EnvironmentAdd { resource } => A1AdapterState {
            members: state.members.insert(resource),
            environment_additions: state.environment_additions.insert(resource),
            ..state
        },
    }
}

pub open spec fn a1_step(
    before: A1AdapterState,
    event: A1AdapterEvent,
    after: A1AdapterState,
) -> bool {
    a1_enabled(before, event) && after == a1_apply(before, event)
}

pub proof fn a1_service_linearize_step_has_remote_provenance(
    before: A1AdapterState,
    attempt: replay_layer::AttemptId,
    after: A1AdapterState,
)
    requires a1_step(
        before,
        A1AdapterEvent::ServiceLinearize { attempt },
        after,
    ),
    ensures
        a1_remote_attempt_pending(before, attempt),
        after.linearized_attempts.contains(attempt),
        after.members.contains(ensure_member_target(before.request)),
        after.history == before.history,
        after.globals == before.globals,
{
}

pub open spec fn a1_exec(
    request: replay_layer::RequestId,
    initial_members: ISet<config_layer::Resource>,
    execution: A1AdapterExecution,
) -> bool {
    execution.configs.len() == execution.events.len() + 1
        && execution.configs[0]
            == a1_initial_state(request, initial_members)
        && forall|index: nat| index < execution.events.len() ==>
            #[trigger] a1_step(
                execution.configs[index as int],
                execution.events[index as int],
                execution.configs[(index + 1) as int],
            )
}

pub open spec fn a1_execution_prefix(
    execution: A1AdapterExecution,
    length: nat,
) -> A1AdapterExecution {
    A1AdapterExecution {
        configs: execution.configs.take((length + 1) as int),
        events: execution.events.take(length as int),
    }
}

pub open spec fn a1_has_linearization(state: A1AdapterState) -> bool {
    exists|attempt: replay_layer::AttemptId|
        state.linearized_attempts.contains(attempt)
}

pub open spec fn a1_members_match_effect(state: A1AdapterState) -> bool {
    forall|resource: config_layer::Resource|
        #[trigger] state.members.contains(resource) <==>
            state.initial_members.contains(resource)
                || state.environment_additions.contains(resource)
                || (a1_has_linearization(state)
                    && resource == ensure_member_target(state.request))
}

pub open spec fn a1_history_classified(state: A1AdapterState) -> bool {
    forall|index: int| 0 <= index < state.history.len() ==>
        match #[trigger] state.history[index] {
            p0_layer::PhysicalEvent::Invoke { .. } => true,
            p0_layer::PhysicalEvent::Delivered {
                attempt,
                observation: replay_layer::Observation::Success(value),
                ..
            } => state.linearized_attempts.contains(attempt)
                && value.id == 1,
            p0_layer::PhysicalEvent::Delivered {
                attempt,
                observation: replay_layer::Observation::Failure,
                ..
            } => state.failed_attempts.contains(attempt)
                && !state.linearized_attempts.contains(attempt),
            p0_layer::PhysicalEvent::Delivered {
                observation: replay_layer::Observation::Ambiguous, ..
            }
            | p0_layer::PhysicalEvent::Delivered {
                observation: replay_layer::Observation::InvalidResult(_), ..
            } => false,
        }
}

pub open spec fn a1_machine_invariant(state: A1AdapterState) -> bool {
    let cfg = ensure_member_full_config();
    &&& state.history
        == projection_layer::pi_adapter(state.globals, state.request)
    &&& request_local_history(state.history, state.request)
    &&& canonical_invocations(cfg, state.history, state.request)
    &&& positive_attempt_identifiers(state.history)
    &&& p1_layer::physical_unique(state.history)
    &&& p1_layer::physical_ordered(state.history)
    &&& a1_history_classified(state)
    &&& a1_members_match_effect(state)
    &&& !state.environment_additions.contains(
        ensure_member_target(state.request),
    )
    &&& forall|attempt: replay_layer::AttemptId|
        #[trigger] state.linearized_attempts.contains(attempt)
            ==> invoked(state.history, state.request, attempt)
    &&& forall|attempt: replay_layer::AttemptId|
        #[trigger] state.failed_attempts.contains(attempt)
            ==> !state.linearized_attempts.contains(attempt)
    &&& match state.active {
        Option::None => true,
        Option::Some(attempt) => {
            p1_layer::invoke_count(
                state.history, state.request, attempt,
            ) == 1
                && p1_layer::delivery_count(
                    state.history, state.request, attempt,
                ) == 0
        },
    }
}

pub open spec fn a1_execution_invariant(
    request: replay_layer::RequestId,
    initial_members: ISet<config_layer::Resource>,
    state: A1AdapterState,
) -> bool {
    state.request == request
        && state.initial_members == initial_members
        && a1_machine_invariant(state)
}

proof fn a1_adapter_from_physical_push(
    history: Seq<p0_layer::PhysicalEvent>,
    physical: p0_layer::PhysicalEvent,
    request: replay_layer::RequestId,
)
    ensures projection_layer::adapter_from_physical(
        history.push(physical), request,
    ) == if event_is_for_request(physical, request) {
        projection_layer::adapter_from_physical(history, request).push(physical)
    } else {
        projection_layer::adapter_from_physical(history, request)
    },
{
    assert(history.push(physical).drop_last() =~= history);
    assert(history.push(physical).last() == physical);
}

pub proof fn a1_pi_adapter_push(
    globals: Seq<global_layer::GlobalEvent>,
    event: global_layer::GlobalEvent,
    request: replay_layer::RequestId,
)
    ensures projection_layer::pi_adapter(
        globals.push(event), request,
    ) == a1_history_after_global(
        projection_layer::pi_adapter(globals, request), event, request,
    ),
{
    projection_layer::pi_physical_push(globals, event);
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
        | global_layer::GlobalEvent::IgnoreStale { .. }
        | global_layer::GlobalEvent::RetryRelease { .. }
        | global_layer::GlobalEvent::Crash
        | global_layer::GlobalEvent::BeginScan
        | global_layer::GlobalEvent::FinishScan
        | global_layer::GlobalEvent::TruncateTail
        | global_layer::GlobalEvent::AbortScan
        | global_layer::GlobalEvent::BeginRecover
        | global_layer::GlobalEvent::FinishRecover => {
            assert(projection_layer::physical_event(event) == Option::None);
            assert(projection_layer::pi_physical(globals.push(event))
                == projection_layer::pi_physical(globals));
            assert(a1_physical_for_request(event, request) == Option::None);
        },
        global_layer::GlobalEvent::InvokeEvent {
            request: event_request,
            attempt,
            call,
            journal_cut,
            ack_cut,
        } => {
            let physical = p0_layer::PhysicalEvent::Invoke {
                request: event_request,
                attempt,
                call,
                journal_cut,
                ack_cut,
            };
            a1_adapter_from_physical_push(
                projection_layer::pi_physical(globals), physical, request,
            );
            if event_request == request {
                assert(a1_physical_for_request(event, request)
                    == Option::Some(physical));
            } else {
                assert(a1_physical_for_request(event, request)
                    == Option::None);
            }
        },
        global_layer::GlobalEvent::DeliverEvent {
            request: event_request,
            attempt,
            observation,
            journal_cut,
        } => {
            let physical = p0_layer::PhysicalEvent::Delivered {
                request: event_request,
                attempt,
                observation,
                journal_cut,
            };
            a1_adapter_from_physical_push(
                projection_layer::pi_physical(globals), physical, request,
            );
            if event_request == request {
                assert(a1_physical_for_request(event, request)
                    == Option::Some(physical));
            } else {
                assert(a1_physical_for_request(event, request)
                    == Option::None);
            }
        },
    }
}

proof fn a1_equal_linearizations_have_equal_presence(
    left: A1AdapterState,
    right: A1AdapterState,
)
    requires left.linearized_attempts == right.linearized_attempts,
    ensures a1_has_linearization(left) == a1_has_linearization(right),
{
    if a1_has_linearization(left) {
        let attempt = choose|attempt: replay_layer::AttemptId|
            left.linearized_attempts.contains(attempt);
        assert(right.linearized_attempts.contains(attempt));
        assert(a1_has_linearization(right));
    }
    if a1_has_linearization(right) {
        let attempt = choose|attempt: replay_layer::AttemptId|
            right.linearized_attempts.contains(attempt);
        assert(left.linearized_attempts.contains(attempt));
        assert(a1_has_linearization(left));
    }
}

proof fn a1_append_history_shape(
    state: A1AdapterState,
    physical: p0_layer::PhysicalEvent,
)
    requires
        request_local_history(state.history, state.request),
        canonical_invocations(
            ensure_member_full_config(), state.history, state.request,
        ),
        positive_attempt_identifiers(state.history),
        event_is_for_request(physical, state.request),
        match physical {
            p0_layer::PhysicalEvent::Invoke { call, attempt, .. } => {
                call == config_layer::canonical_call(
                    ensure_member_full_config(), state.request,
                ) && attempt > 0
            },
            p0_layer::PhysicalEvent::Delivered { attempt, .. } => attempt > 0,
        },
    ensures
        request_local_history(state.history.push(physical), state.request),
        canonical_invocations(
            ensure_member_full_config(),
            state.history.push(physical),
            state.request,
        ),
        positive_attempt_identifiers(state.history.push(physical)),
{
    assert forall|index: int| 0 <= index < state.history.push(physical).len()
        implies event_is_for_request(
            #[trigger] state.history.push(physical)[index], state.request,
        ) by {
        if index < state.history.len() {
            assert(state.history.push(physical)[index] == state.history[index]);
        } else {
            assert(index == state.history.len());
            assert(state.history.push(physical)[index] == physical);
        }
    }
    assert forall|index: int| 0 <= index < state.history.push(physical).len()
        implies match #[trigger] state.history.push(physical)[index] {
            p0_layer::PhysicalEvent::Invoke { call, .. } => {
                call == config_layer::canonical_call(
                    ensure_member_full_config(), state.request,
                )
            },
            p0_layer::PhysicalEvent::Delivered { .. } => true,
        } by {
        if index < state.history.len() {
            assert(state.history.push(physical)[index] == state.history[index]);
        } else {
            assert(index == state.history.len());
            assert(state.history.push(physical)[index] == physical);
        }
    }
    assert forall|index: int| 0 <= index < state.history.push(physical).len()
        implies match #[trigger] state.history.push(physical)[index] {
            p0_layer::PhysicalEvent::Invoke { attempt, .. }
            | p0_layer::PhysicalEvent::Delivered { attempt, .. } => attempt > 0,
        } by {
        if index < state.history.len() {
            assert(state.history.push(physical)[index] == state.history[index]);
        } else {
            assert(index == state.history.len());
            assert(state.history.push(physical)[index] == physical);
        }
    }
}

pub proof fn a1_initial_state_satisfies_invariant(
    request: replay_layer::RequestId,
    initial_members: ISet<config_layer::Resource>,
)
    ensures a1_execution_invariant(
        request,
        initial_members,
        a1_initial_state(request, initial_members),
    ),
{
    let state = a1_initial_state(request, initial_members);
    reveal_with_fuel(projection_layer::adapter_from_physical, 1);
    reveal_with_fuel(projection_layer::pi_physical, 1);
    reveal_with_fuel(p1_layer::physical_unique, 1);
    reveal_with_fuel(p1_layer::physical_ordered, 1);
    assert forall|resource: config_layer::Resource|
        #[trigger] state.members.contains(resource) <==>
            state.initial_members.contains(resource)
                || state.environment_additions.contains(resource)
                || (a1_has_linearization(state)
                    && resource == ensure_member_target(request)) by {
    }
}

proof fn a1_observe_preserves_invariant(
    before: A1AdapterState,
    event: global_layer::GlobalEvent,
)
    requires
        a1_machine_invariant(before),
        a1_observe_enabled(before, event),
    ensures a1_machine_invariant(a1_apply_observe(before, event)),
{
    let after = a1_apply_observe(before, event);
    let request = before.request;
    let cfg = ensure_member_full_config();
    a1_pi_adapter_push(before.globals, event, request);

    match event {
        global_layer::GlobalEvent::InvokeEvent {
            request: event_request,
            attempt,
            call,
            journal_cut,
            ack_cut,
        } if event_request == request => {
            let physical = p0_layer::PhysicalEvent::Invoke {
                request: event_request,
                attempt,
                call,
                journal_cut,
                ack_cut,
            };
            assert(after.history == before.history.push(physical));
            a1_append_history_shape(before, physical);
            p1_layer::unique_push_invoke(
                before.history, physical, request, attempt,
            );
            p1_layer::ordered_push_invoke(before.history, physical);
            p1_layer::invoke_count_push(
                before.history, physical, request, attempt,
            );
            p1_layer::delivery_count_push(
                before.history, physical, request, attempt,
            );
            assert(p1_layer::invoke_count(after.history, request, attempt) == 1);
            assert(p1_layer::delivery_count(
                after.history, request, attempt,
            ) == 0);
            assert forall|index: int| 0 <= index < after.history.len()
                implies match #[trigger] after.history[index] {
                    p0_layer::PhysicalEvent::Invoke { .. } => true,
                    p0_layer::PhysicalEvent::Delivered {
                        attempt: observed_attempt,
                        observation: replay_layer::Observation::Success(value),
                        ..
                    } => after.linearized_attempts.contains(observed_attempt)
                        && value.id == 1,
                    p0_layer::PhysicalEvent::Delivered {
                        attempt: observed_attempt,
                        observation: replay_layer::Observation::Failure,
                        ..
                    } => after.failed_attempts.contains(observed_attempt)
                        && !after.linearized_attempts.contains(observed_attempt),
                    p0_layer::PhysicalEvent::Delivered {
                        observation: replay_layer::Observation::Ambiguous, ..
                    }
                    | p0_layer::PhysicalEvent::Delivered {
                        observation: replay_layer::Observation::InvalidResult(_), ..
                    } => false,
                } by {
                if index < before.history.len() {
                    assert(after.history[index] == before.history[index]);
                } else {
                    assert(index == before.history.len());
                    assert(after.history[index] == physical);
                }
            }
            assert(after.history
                == projection_layer::pi_adapter(after.globals, request));
            assert(request_local_history(after.history, request));
            assert(canonical_invocations(cfg, after.history, request));
            assert(positive_attempt_identifiers(after.history));
            assert(p1_layer::physical_unique(after.history));
            assert(p1_layer::physical_ordered(after.history));
            assert(a1_history_classified(after));
            assert(after.members == before.members);
            assert(after.initial_members == before.initial_members);
            assert(after.environment_additions
                == before.environment_additions);
            assert(after.linearized_attempts
                == before.linearized_attempts);
            a1_equal_linearizations_have_equal_presence(after, before);
            assert forall|resource: config_layer::Resource|
                #[trigger] after.members.contains(resource) <==>
                    after.initial_members.contains(resource)
                        || after.environment_additions.contains(resource)
                        || (a1_has_linearization(after)
                            && resource
                                == ensure_member_target(after.request)) by {
            }
            assert(a1_members_match_effect(after));
            assert(!after.environment_additions.contains(
                ensure_member_target(request),
            ));
            assert forall|linearized: replay_layer::AttemptId|
                #[trigger] after.linearized_attempts.contains(linearized)
                    implies invoked(after.history, request, linearized) by {
                assert(before.linearized_attempts.contains(linearized));
                assert(invoked(before.history, request, linearized));
                if linearized == attempt {
                    assert(p1_layer::invoke_count(
                        after.history, request, linearized,
                    ) == 1);
                } else {
                    p1_layer::invoke_count_push(
                        before.history, physical, request, linearized,
                    );
                }
            }
            assert forall|failed: replay_layer::AttemptId|
                #[trigger] after.failed_attempts.contains(failed)
                    implies !after.linearized_attempts.contains(failed) by {
            }
            assert(after.active == Option::Some(attempt));
            assert(p1_layer::invoke_count(
                after.history, request, attempt,
            ) == 1);
            assert(p1_layer::delivery_count(
                after.history, request, attempt,
            ) == 0);
            assert(a1_machine_invariant(after));
        },
        global_layer::GlobalEvent::DeliverEvent {
            request: event_request,
            attempt,
            observation,
            journal_cut,
        } if event_request == request => {
            let physical = p0_layer::PhysicalEvent::Delivered {
                request: event_request,
                attempt,
                observation,
                journal_cut,
            };
            assert(after.history == before.history.push(physical));
            a1_append_history_shape(before, physical);
            assert(p1_layer::invoke_count(before.history, request, attempt) == 1);
            p1_layer::unique_push_delivery(
                before.history, physical, request, attempt,
            );
            p1_layer::ordered_push_delivery(
                before.history, physical, request, attempt,
            );
            assert forall|index: int| 0 <= index < after.history.len()
                implies match #[trigger] after.history[index] {
                    p0_layer::PhysicalEvent::Invoke { .. } => true,
                    p0_layer::PhysicalEvent::Delivered {
                        attempt: observed_attempt,
                        observation: replay_layer::Observation::Success(value),
                        ..
                    } => after.linearized_attempts.contains(observed_attempt)
                        && value.id == 1,
                    p0_layer::PhysicalEvent::Delivered {
                        attempt: observed_attempt,
                        observation: replay_layer::Observation::Failure,
                        ..
                    } => after.failed_attempts.contains(observed_attempt)
                        && !after.linearized_attempts.contains(observed_attempt),
                    p0_layer::PhysicalEvent::Delivered {
                        observation: replay_layer::Observation::Ambiguous, ..
                    }
                    | p0_layer::PhysicalEvent::Delivered {
                        observation: replay_layer::Observation::InvalidResult(_), ..
                    } => false,
                } by {
                if index < before.history.len() {
                    assert(after.history[index] == before.history[index]);
                } else {
                    assert(index == before.history.len());
                    assert(after.history[index] == physical);
                    match observation {
                        replay_layer::Observation::Success(value) => {},
                        replay_layer::Observation::Failure => {},
                        replay_layer::Observation::Ambiguous
                        | replay_layer::Observation::InvalidResult(_) => {},
                    }
                }
            }
            assert(after.history
                == projection_layer::pi_adapter(after.globals, request));
            assert(after.members == before.members);
            assert(after.initial_members == before.initial_members);
            assert(after.environment_additions
                == before.environment_additions);
            assert(after.linearized_attempts
                == before.linearized_attempts);
            a1_equal_linearizations_have_equal_presence(after, before);
            assert(a1_members_match_effect(after));
            assert(request_local_history(after.history, request));
            assert(canonical_invocations(cfg, after.history, request));
            assert(positive_attempt_identifiers(after.history));
            assert(p1_layer::physical_unique(after.history));
            assert(p1_layer::physical_ordered(after.history));
            assert(a1_history_classified(after));
            assert(!after.environment_additions.contains(
                ensure_member_target(request),
            ));
            assert forall|linearized: replay_layer::AttemptId|
                #[trigger] after.linearized_attempts.contains(linearized)
                    implies invoked(after.history, request, linearized) by {
                assert(invoked(before.history, request, linearized));
                p1_layer::invoke_count_push(
                    before.history, physical, request, linearized,
                );
            }
            assert forall|failed: replay_layer::AttemptId|
                #[trigger] after.failed_attempts.contains(failed)
                    implies !after.linearized_attempts.contains(failed) by {
                if failed == attempt {
                    match observation {
                        replay_layer::Observation::Failure => {
                            assert(!before.linearized_attempts.contains(attempt));
                        },
                        replay_layer::Observation::Success(_) => {
                            assert(after.failed_attempts
                                == before.failed_attempts);
                        },
                        replay_layer::Observation::Ambiguous
                        | replay_layer::Observation::InvalidResult(_) => {},
                    }
                }
            }
            assert(after.active == Option::None);
            assert(a1_machine_invariant(after));
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
        | global_layer::GlobalEvent::IgnoreStale { .. }
        | global_layer::GlobalEvent::RetryRelease { .. }
        | global_layer::GlobalEvent::Crash
        | global_layer::GlobalEvent::BeginScan
        | global_layer::GlobalEvent::FinishScan
        | global_layer::GlobalEvent::TruncateTail
        | global_layer::GlobalEvent::AbortScan
        | global_layer::GlobalEvent::BeginRecover
        | global_layer::GlobalEvent::FinishRecover => {
            assert(a1_physical_for_request(event, request) == Option::None);
            assert(after.history == before.history);
            assert(after.history
                == projection_layer::pi_adapter(after.globals, request));
            assert(after.members == before.members);
            assert(after.initial_members == before.initial_members);
            assert(after.environment_additions
                == before.environment_additions);
            assert(after.linearized_attempts
                == before.linearized_attempts);
            assert(after.failed_attempts == before.failed_attempts);
            a1_equal_linearizations_have_equal_presence(after, before);
            assert(a1_members_match_effect(after));
            match after.active {
                Option::None => {},
                Option::Some(active) => {
                    assert(before.active == Option::Some(active));
                },
            }
            assert(a1_machine_invariant(after));
        },
    }
}

proof fn a1_linearize_preserves_invariant(
    before: A1AdapterState,
    attempt: replay_layer::AttemptId,
)
    requires
        a1_machine_invariant(before),
        a1_enabled(before, A1AdapterEvent::ServiceLinearize { attempt }),
    ensures a1_machine_invariant(a1_apply(
        before, A1AdapterEvent::ServiceLinearize { attempt },
    )),
{
    let after = a1_apply(
        before, A1AdapterEvent::ServiceLinearize { attempt },
    );
    let target = ensure_member_target(before.request);
    assert(a1_has_linearization(after)) by {
        assert(after.linearized_attempts.contains(attempt));
    }
    assert forall|resource: config_layer::Resource|
        #[trigger] after.members.contains(resource) <==>
            after.initial_members.contains(resource)
                || after.environment_additions.contains(resource)
                || (a1_has_linearization(after)
                    && resource == ensure_member_target(after.request)) by {
        if resource != target {
            assert(after.members.contains(resource)
                == before.members.contains(resource));
        }
    }
    assert forall|index: int| 0 <= index < after.history.len()
        implies match #[trigger] after.history[index] {
            p0_layer::PhysicalEvent::Invoke { .. } => true,
            p0_layer::PhysicalEvent::Delivered {
                attempt: observed_attempt,
                observation: replay_layer::Observation::Success(value),
                ..
            } => after.linearized_attempts.contains(observed_attempt)
                && value.id == 1,
            p0_layer::PhysicalEvent::Delivered {
                attempt: observed_attempt,
                observation: replay_layer::Observation::Failure,
                ..
            } => after.failed_attempts.contains(observed_attempt)
                && !after.linearized_attempts.contains(observed_attempt),
            p0_layer::PhysicalEvent::Delivered {
                observation: replay_layer::Observation::Ambiguous, ..
            }
            | p0_layer::PhysicalEvent::Delivered {
                observation: replay_layer::Observation::InvalidResult(_), ..
            } => false,
        } by {
        match after.history[index] {
            p0_layer::PhysicalEvent::Delivered {
                attempt: observed_attempt,
                observation: replay_layer::Observation::Failure,
                ..
            } => {
                assert(before.failed_attempts.contains(observed_attempt));
                if observed_attempt == attempt {
                    assert(before.failed_attempts.contains(attempt));
                    assert(false);
                }
            },
            p0_layer::PhysicalEvent::Invoke { .. }
            | p0_layer::PhysicalEvent::Delivered { .. } => {},
        }
    }
    assert forall|failed: replay_layer::AttemptId|
        #[trigger] after.failed_attempts.contains(failed)
            implies !after.linearized_attempts.contains(failed) by {
        if failed == attempt {
            assert(!before.failed_attempts.contains(attempt));
        }
    }
    assert forall|linearized: replay_layer::AttemptId|
        #[trigger] after.linearized_attempts.contains(linearized)
            implies invoked(after.history, after.request, linearized) by {
        if linearized == attempt {
            assert(invoked(before.history, before.request, attempt));
        }
    }
}

proof fn a1_environment_add_preserves_invariant(
    before: A1AdapterState,
    resource: config_layer::Resource,
)
    requires
        a1_machine_invariant(before),
        a1_enabled(before, A1AdapterEvent::EnvironmentAdd { resource }),
    ensures a1_machine_invariant(a1_apply(
        before, A1AdapterEvent::EnvironmentAdd { resource },
    )),
{
    let after = a1_apply(
        before, A1AdapterEvent::EnvironmentAdd { resource },
    );
    assert(after.linearized_attempts == before.linearized_attempts);
    a1_equal_linearizations_have_equal_presence(after, before);
    assert forall|candidate: config_layer::Resource|
        #[trigger] after.members.contains(candidate) <==>
            after.initial_members.contains(candidate)
                || after.environment_additions.contains(candidate)
                || (a1_has_linearization(after)
                    && candidate == ensure_member_target(after.request)) by {
        if candidate != resource {
            assert(after.members.contains(candidate)
                == before.members.contains(candidate));
            assert(after.environment_additions.contains(candidate)
                == before.environment_additions.contains(candidate));
        } else {
            assert(after.members.contains(candidate));
            assert(after.environment_additions.contains(candidate));
        }
    }
}

pub proof fn a1_step_preserves_invariant(
    request: replay_layer::RequestId,
    initial_members: ISet<config_layer::Resource>,
    before: A1AdapterState,
    event: A1AdapterEvent,
)
    requires
        a1_execution_invariant(request, initial_members, before),
        a1_enabled(before, event),
    ensures a1_execution_invariant(
        request, initial_members, a1_apply(before, event),
    ),
{
    match event {
        A1AdapterEvent::Observe { event } => {
            a1_observe_preserves_invariant(before, event);
        },
        A1AdapterEvent::ServiceLinearize { attempt } => {
            a1_linearize_preserves_invariant(before, attempt);
        },
        A1AdapterEvent::EnvironmentAdd { resource } => {
            a1_environment_add_preserves_invariant(before, resource);
        },
    }
}

pub proof fn a1_exec_prefix(
    request: replay_layer::RequestId,
    initial_members: ISet<config_layer::Resource>,
    execution: A1AdapterExecution,
    length: nat,
)
    requires
        a1_exec(request, initial_members, execution),
        length <= execution.events.len(),
    ensures a1_exec(
        request,
        initial_members,
        a1_execution_prefix(execution, length),
    ),
{
    let prefix = a1_execution_prefix(execution, length);
    assert(prefix.events.len() == length);
    assert(prefix.configs.len() == length + 1);
    assert(prefix.configs[0] == execution.configs[0]);
    assert forall|index: nat| index < prefix.events.len() implies
        #[trigger] a1_step(
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

pub proof fn a1_every_exec_configuration_satisfies_invariant(
    request: replay_layer::RequestId,
    initial_members: ISet<config_layer::Resource>,
    execution: A1AdapterExecution,
)
    requires a1_exec(request, initial_members, execution),
    ensures forall|index: nat| index < execution.configs.len() ==>
        #[trigger] a1_execution_invariant(
            request,
            initial_members,
            execution.configs[index as int],
        ),
    decreases execution.events.len(),
{
    if execution.events.len() == 0 {
        a1_initial_state_satisfies_invariant(request, initial_members);
    } else {
        let last_index: nat = (execution.events.len() - 1) as nat;
        let prefix = a1_execution_prefix(execution, last_index);
        a1_exec_prefix(request, initial_members, execution, last_index);
        a1_every_exec_configuration_satisfies_invariant(
            request, initial_members, prefix,
        );
        assert(prefix.configs.len() == execution.events.len());
        assert forall|index: nat| index < execution.events.len() implies
            #[trigger] a1_execution_invariant(
                request,
                initial_members,
                execution.configs[index as int],
            ) by {
            assert(index < prefix.configs.len());
            assert(prefix.configs[index as int]
                == execution.configs[index as int]);
        }
        let before = execution.configs[last_index as int];
        let event = execution.events[last_index as int];
        let after = execution.configs[(last_index + 1) as int];
        assert(a1_execution_invariant(
            request, initial_members, before,
        ));
        assert(a1_step(before, event, after));
        a1_step_preserves_invariant(
            request, initial_members, before, event,
        );
        assert(after == a1_apply(before, event));
        assert(a1_execution_invariant(
            request, initial_members, after,
        ));
        assert forall|index: nat| index < execution.configs.len() implies
            #[trigger] a1_execution_invariant(
                request,
                initial_members,
                execution.configs[index as int],
            ) by {
            if index < execution.events.len() {
                assert(index < prefix.configs.len());
            } else {
                assert(index == execution.events.len());
                assert(index == last_index + 1);
            }
        }
    }
}

proof fn a1_global_trace_push(
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

pub proof fn a1_exec_final_globals_are_projected(
    request: replay_layer::RequestId,
    initial_members: ISet<config_layer::Resource>,
    execution: A1AdapterExecution,
)
    requires a1_exec(request, initial_members, execution),
    ensures execution.configs[execution.events.len() as int].globals
        == a1_global_trace(execution.events),
    decreases execution.events.len(),
{
    if execution.events.len() == 0 {
        assert(execution.configs[0]
            == a1_initial_state(request, initial_members));
    } else {
        let last_index: nat = (execution.events.len() - 1) as nat;
        let prefix = a1_execution_prefix(execution, last_index);
        a1_exec_prefix(request, initial_members, execution, last_index);
        a1_exec_final_globals_are_projected(
            request, initial_members, prefix,
        );
        assert(prefix.events =~= execution.events.drop_last());
        assert(prefix.configs.len() == execution.events.len());
        assert(prefix.configs[last_index as int]
            == execution.configs[last_index as int]);
        let before = execution.configs[last_index as int];
        let event = execution.events[last_index as int];
        let after = execution.configs[(last_index + 1) as int];
        assert(a1_step(before, event, after));
        assert(after == a1_apply(before, event));
        a1_global_trace_push(prefix.events, event);
        assert(execution.events =~= prefix.events.push(event));
        match event {
            A1AdapterEvent::Observe { event: global } => {
                assert(after.globals == before.globals.push(global));
            },
            A1AdapterEvent::ServiceLinearize { .. }
            | A1AdapterEvent::EnvironmentAdd { .. } => {
                assert(after.globals == before.globals);
            },
        }
    }
}

pub proof fn a1_invariant_implies_adapter_rely_trace(
    state: A1AdapterState,
)
    requires a1_machine_invariant(state),
    ensures adapter_rely_trace(
        ensure_member_paper(),
        state.request,
        state.history,
        a1_external_run(state),
    ),
{
    let cfg = ensure_member_full_config();
    let paper = ensure_member_paper();
    let request = state.request;
    let run = a1_external_run(state);
    t1_layer::paper_broker_config_is_broker(paper);
    assert(t1_layer::paper_broker_config(paper) == cfg);

    assert(ensure_member_env_rely(request, state.history, run)) by {
        assert(!run.interference.environment_additions.contains(
            ensure_member_target(request),
        ));
        assert(run.interference.linearized_attempts
            == state.linearized_attempts);
        assert(ensure_member_has_linearized_attempt(run)
            == a1_has_linearization(state)) by {
            if ensure_member_has_linearized_attempt(run) {
                let attempt = choose|attempt: replay_layer::AttemptId|
                    run.interference.linearized_attempts.contains(attempt);
                assert(state.linearized_attempts.contains(attempt));
                assert(a1_has_linearization(state));
            }
            if a1_has_linearization(state) {
                let attempt = choose|attempt: replay_layer::AttemptId|
                    state.linearized_attempts.contains(attempt);
                assert(run.interference.linearized_attempts.contains(attempt));
                assert(ensure_member_has_linearized_attempt(run));
            }
        }
        assert forall|attempt: replay_layer::AttemptId|
            #[trigger] run.interference.linearized_attempts.contains(attempt)
                implies invoked(state.history, request, attempt) by {
        }
        if ensure_member_has_linearized_attempt(run) {
            assert(a1_has_linearization(state));
            assert forall|resource: config_layer::Resource|
                #[trigger] run.post.contains(resource) <==>
                    ensure_member_baseline_contains(run, resource)
                        || resource == ensure_member_target(request) by {
            }
            assert(ensure_member_one_effect(request, run));
        } else {
            assert(!a1_has_linearization(state));
            assert forall|resource: config_layer::Resource|
                #[trigger] run.post.contains(resource) <==>
                    ensure_member_baseline_contains(run, resource) by {
            }
            assert(ensure_member_zero_effect(request, run));
        }
    }

    assert forall|index: int| 0 <= index < state.history.len() implies
        match #[trigger] state.history[index] {
            p0_layer::PhysicalEvent::Delivered {
                attempt, observation, ..
            } => {
                &&& ensure_member_classification_ok(
                    request, attempt, observation, run,
                )
                &&& match observation {
                    replay_layer::Observation::Success(value) => {
                        cfg.valid_results.contains((request, value))
                    },
                    replay_layer::Observation::Failure
                    | replay_layer::Observation::Ambiguous
                    | replay_layer::Observation::InvalidResult(_) => true,
                }
            },
            p0_layer::PhysicalEvent::Invoke { .. } => true,
        } by {
        match state.history[index] {
            p0_layer::PhysicalEvent::Delivered {
                attempt,
                observation: replay_layer::Observation::Success(value),
                ..
            } => {
                assert(state.linearized_attempts.contains(attempt));
                assert(value.id == 1);
                assert(cfg.valid_results.contains((request, value)));
            },
            p0_layer::PhysicalEvent::Delivered {
                attempt,
                observation: replay_layer::Observation::Failure,
                ..
            } => {
                assert(!state.linearized_attempts.contains(attempt));
            },
            p0_layer::PhysicalEvent::Invoke { .. }
            | p0_layer::PhysicalEvent::Delivered { .. } => {},
        }
    }
    assert(delivered_observations_classified(
        cfg,
        ensure_member_adapter(),
        state.history,
        request,
        run,
    ));
    assert(cfg.request[request].retry_class
        == replay_layer::RetryClass::Idempotent);
    assert(ensure_member_zero_effect(request, run)
        || ensure_member_one_effect(request, run));
    assert(ensure_member_idempotent_under_rely(request, run));
    assert(adapter_class_law(
        cfg,
        ensure_member_adapter(),
        state.history,
        request,
        run,
    ));
}

pub proof fn ensure_member_exec_derives_adapter_rely(
    request: replay_layer::RequestId,
    initial_members: ISet<config_layer::Resource>,
    execution: A1AdapterExecution,
)
    requires a1_exec(request, initial_members, execution),
    ensures adapter_rely(
        ensure_member_paper(),
        a1_global_trace(execution.events),
        request,
        a1_external_run(
            execution.configs[execution.events.len() as int],
        ),
    ),
{
    let final_state = execution.configs[execution.events.len() as int];
    a1_every_exec_configuration_satisfies_invariant(
        request, initial_members, execution,
    );
    assert(a1_execution_invariant(
        request, initial_members, final_state,
    ));
    a1_exec_final_globals_are_projected(
        request, initial_members, execution,
    );
    a1_invariant_implies_adapter_rely_trace(final_state);
    assert(final_state.request == request);
    assert(final_state.globals == a1_global_trace(execution.events));
    assert(final_state.history
        == projection_layer::pi_adapter(final_state.globals, request));
    adapter_rely_is_projected_rely(
        ensure_member_paper(),
        a1_global_trace(execution.events),
        request,
        a1_external_run(final_state),
    );
}

pub proof fn ensure_member_executable_wal_terminal_refines(
    request: replay_layer::RequestId,
    initial_members: ISet<config_layer::Resource>,
    adapter_execution: A1AdapterExecution,
    wal_execution: wal_runtime_layer::WalExecution,
    outcome: TerminalOutcome,
)
    requires
        a1_exec(request, initial_members, adapter_execution),
        a1_global_trace(adapter_execution.events) == wal_execution.events,
        wal_runtime_layer::exec(
            ensure_member_full_config(), wal_execution,
        ),
        terminal(wal_execution.events, request) == Option::Some(outcome),
    ensures
        adapter_rely(
            ensure_member_paper(),
            wal_execution.events,
            request,
            a1_external_run(
                adapter_execution.configs[
                    adapter_execution.events.len() as int
                ],
            ),
        ),
        refines(
            ensure_member_paper(),
            request,
            projection_layer::pi_adapter(wal_execution.events, request),
            a1_external_run(
                adapter_execution.configs[
                    adapter_execution.events.len() as int
                ],
            ),
            outcome,
        ),
        per_request_effect_refinement(
            ensure_member_paper(),
            wal_execution.events,
            request,
            a1_external_run(
                adapter_execution.configs[
                    adapter_execution.events.len() as int
                ],
            ),
        ),
{
    let paper = ensure_member_paper();
    let cfg = ensure_member_full_config();
    let final_adapter = adapter_execution.configs[
        adapter_execution.events.len() as int
    ];
    let final_wal = wal_execution.configs[wal_execution.events.len() as int];
    let target = t4_c0_layer::canonical_target_execution(cfg, wal_execution);
    let map = t4_c0_layer::canonical_composed_map(wal_execution);
    let broker = target.configs[target.events.len() as int];

    ensure_member_exec_derives_adapter_rely(
        request, initial_members, adapter_execution,
    );
    assert(adapter_rely(
        paper,
        wal_execution.events,
        request,
        a1_external_run(final_adapter),
    ));
    ensure_member_full_config_is_well_formed();
    t1_layer::paper_broker_config_is_broker(paper);
    assert(t1_layer::paper_broker_config(paper) == cfg);
    ensure_member_adapter_is_verified();
    wal_trace_layer::exec_implies_admissible_wal_trace(cfg, wal_execution);
    wal_trace_layer::trace_agreement_for_exec(cfg, wal_execution);
    config_layer::erasure_is_replay_well_formed(cfg);
    t4_c0_layer::canonical_closed_wal_broker_composition(
        cfg, wal_execution,
    );
    assert(t4_c0_layer::weak_simulation_index_map(
        cfg, wal_execution, target, map,
    ));
    assert(t2_layer::weak_index_shape(
        wal_execution.events.len(), target.events.len(), map,
    ));
    assert(map.points[wal_execution.events.len() as int]
        == target.events.len());
    assert(t4_c0_layer::related_prefixes(
        cfg, wal_execution, target, map,
    ));
    assert(t4_c0_layer::wal_broker_representation(
        cfg, final_wal, broker,
    ));
    wal_terminal_outcome_refines(
        paper,
        wal_execution,
        broker,
        request,
        a1_external_run(final_adapter),
        outcome,
    );
}

pub open spec fn a1_zero_adapter_execution(
    request: replay_layer::RequestId,
    initial_members: ISet<config_layer::Resource>,
) -> A1AdapterExecution {
    A1AdapterExecution {
        configs: Seq::empty().push(
            a1_initial_state(request, initial_members),
        ),
        events: Seq::empty(),
    }
}

pub open spec fn a1_extend_adapter_execution(
    execution: A1AdapterExecution,
    event: A1AdapterEvent,
) -> A1AdapterExecution {
    let before = execution.configs.last();
    A1AdapterExecution {
        configs: execution.configs.push(a1_apply(before, event)),
        events: execution.events.push(event),
    }
}

pub proof fn a1_zero_adapter_execution_exec(
    request: replay_layer::RequestId,
    initial_members: ISet<config_layer::Resource>,
)
    ensures a1_exec(
        request,
        initial_members,
        a1_zero_adapter_execution(request, initial_members),
    ),
{
}

pub proof fn a1_extend_adapter_execution_exec(
    request: replay_layer::RequestId,
    initial_members: ISet<config_layer::Resource>,
    execution: A1AdapterExecution,
    event: A1AdapterEvent,
)
    requires
        a1_exec(request, initial_members, execution),
        a1_enabled(execution.configs.last(), event),
    ensures a1_exec(
        request,
        initial_members,
        a1_extend_adapter_execution(execution, event),
    ),
    a1_extend_adapter_execution(execution, event).events.len()
        == execution.events.len() + 1,
    a1_global_trace(
        a1_extend_adapter_execution(execution, event).events,
    ) == match event {
        A1AdapterEvent::Observe { event: global } => {
            a1_global_trace(execution.events).push(global)
        },
        A1AdapterEvent::ServiceLinearize { .. }
        | A1AdapterEvent::EnvironmentAdd { .. } => {
            a1_global_trace(execution.events)
        },
    },
{
    let extended = a1_extend_adapter_execution(execution, event);
    let old_len = execution.events.len();
    assert(execution.configs.len() == old_len + 1);
    assert(execution.configs.last()
        == execution.configs[old_len as int]);
    assert forall|index: nat| index < extended.events.len() implies
        #[trigger] a1_step(
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
                == a1_apply(execution.configs.last(), event));
        }
    }
    a1_global_trace_push(execution.events, event);
}

pub open spec fn a1_observe_full_append(
    execution: A1AdapterExecution,
    record: replay_layer::JournalRecord,
    cut: nat,
) -> A1AdapterExecution {
    let staged = a1_extend_adapter_execution(
        execution,
        A1AdapterEvent::Observe {
            event: global_layer::GlobalEvent::WalStage { record },
        },
    );
    let written = a1_extend_adapter_execution(
        staged,
        A1AdapterEvent::Observe {
            event: global_layer::GlobalEvent::WalWriteFull { record },
        },
    );
    a1_extend_adapter_execution(
        written,
        A1AdapterEvent::Observe {
            event: global_layer::GlobalEvent::WalFlushAck { cut },
        },
    )
}

pub proof fn a1_observe_full_append_exec(
    request: replay_layer::RequestId,
    initial_members: ISet<config_layer::Resource>,
    execution: A1AdapterExecution,
    record: replay_layer::JournalRecord,
    cut: nat,
)
    requires a1_exec(request, initial_members, execution),
    ensures a1_exec(
        request,
        initial_members,
        a1_observe_full_append(execution, record, cut),
    ),
    a1_observe_full_append(execution, record, cut).events.len()
        == execution.events.len() + 3,
    a1_global_trace(
        a1_observe_full_append(execution, record, cut).events,
    ) == a1_global_trace(execution.events)
        .push(global_layer::GlobalEvent::WalStage { record })
        .push(global_layer::GlobalEvent::WalWriteFull { record })
        .push(global_layer::GlobalEvent::WalFlushAck { cut }),
{
    let stage = A1AdapterEvent::Observe {
        event: global_layer::GlobalEvent::WalStage { record },
    };
    let staged = a1_extend_adapter_execution(execution, stage);
    assert(a1_enabled(execution.configs.last(), stage));
    a1_extend_adapter_execution_exec(
        request, initial_members, execution, stage,
    );

    let write = A1AdapterEvent::Observe {
        event: global_layer::GlobalEvent::WalWriteFull { record },
    };
    let written = a1_extend_adapter_execution(staged, write);
    assert(a1_enabled(staged.configs.last(), write));
    a1_extend_adapter_execution_exec(
        request, initial_members, staged, write,
    );

    let flush = A1AdapterEvent::Observe {
        event: global_layer::GlobalEvent::WalFlushAck { cut },
    };
    assert(a1_enabled(written.configs.last(), flush));
    a1_extend_adapter_execution_exec(
        request, initial_members, written, flush,
    );
}

pub open spec fn a1_observe_recovery(
    execution: A1AdapterExecution,
) -> A1AdapterExecution {
    let crashed = a1_extend_adapter_execution(
        execution,
        A1AdapterEvent::Observe {
            event: global_layer::GlobalEvent::Crash,
        },
    );
    let scanning = a1_extend_adapter_execution(
        crashed,
        A1AdapterEvent::Observe {
            event: global_layer::GlobalEvent::BeginScan,
        },
    );
    let scanned = a1_extend_adapter_execution(
        scanning,
        A1AdapterEvent::Observe {
            event: global_layer::GlobalEvent::FinishScan,
        },
    );
    let truncated = a1_extend_adapter_execution(
        scanned,
        A1AdapterEvent::Observe {
            event: global_layer::GlobalEvent::TruncateTail,
        },
    );
    let recovering = a1_extend_adapter_execution(
        truncated,
        A1AdapterEvent::Observe {
            event: global_layer::GlobalEvent::BeginRecover,
        },
    );
    a1_extend_adapter_execution(
        recovering,
        A1AdapterEvent::Observe {
            event: global_layer::GlobalEvent::FinishRecover,
        },
    )
}

pub proof fn a1_observe_recovery_exec(
    request: replay_layer::RequestId,
    initial_members: ISet<config_layer::Resource>,
    execution: A1AdapterExecution,
)
    requires
        a1_exec(request, initial_members, execution),
        execution.configs.last().mode == A1AdapterMode::Online,
    ensures
        a1_exec(
            request,
            initial_members,
            a1_observe_recovery(execution),
        ),
        a1_observe_recovery(execution).configs.last().mode
            == A1AdapterMode::Online,
        a1_observe_recovery(execution).events.len()
            == execution.events.len() + 6,
        a1_global_trace(a1_observe_recovery(execution).events)
            == a1_global_trace(execution.events)
                .push(global_layer::GlobalEvent::Crash)
                .push(global_layer::GlobalEvent::BeginScan)
                .push(global_layer::GlobalEvent::FinishScan)
                .push(global_layer::GlobalEvent::TruncateTail)
                .push(global_layer::GlobalEvent::BeginRecover)
                .push(global_layer::GlobalEvent::FinishRecover),
{
    let crash = A1AdapterEvent::Observe {
        event: global_layer::GlobalEvent::Crash,
    };
    let crashed = a1_extend_adapter_execution(execution, crash);
    assert(a1_enabled(execution.configs.last(), crash));
    a1_extend_adapter_execution_exec(
        request, initial_members, execution, crash,
    );
    assert(crashed.configs.last().mode == A1AdapterMode::Crashed);

    let begin_scan = A1AdapterEvent::Observe {
        event: global_layer::GlobalEvent::BeginScan,
    };
    let scanning = a1_extend_adapter_execution(crashed, begin_scan);
    assert(a1_enabled(crashed.configs.last(), begin_scan));
    a1_extend_adapter_execution_exec(
        request, initial_members, crashed, begin_scan,
    );

    let finish_scan = A1AdapterEvent::Observe {
        event: global_layer::GlobalEvent::FinishScan,
    };
    let scanned = a1_extend_adapter_execution(scanning, finish_scan);
    assert(a1_enabled(scanning.configs.last(), finish_scan));
    a1_extend_adapter_execution_exec(
        request, initial_members, scanning, finish_scan,
    );

    let truncate = A1AdapterEvent::Observe {
        event: global_layer::GlobalEvent::TruncateTail,
    };
    let truncated = a1_extend_adapter_execution(scanned, truncate);
    assert(a1_enabled(scanned.configs.last(), truncate));
    a1_extend_adapter_execution_exec(
        request, initial_members, scanned, truncate,
    );

    let begin_recover = A1AdapterEvent::Observe {
        event: global_layer::GlobalEvent::BeginRecover,
    };
    let recovering = a1_extend_adapter_execution(
        truncated, begin_recover,
    );
    assert(a1_enabled(truncated.configs.last(), begin_recover));
    a1_extend_adapter_execution_exec(
        request, initial_members, truncated, begin_recover,
    );
    assert(recovering.configs.last().mode
        == A1AdapterMode::Recovering);

    let finish_recover = A1AdapterEvent::Observe {
        event: global_layer::GlobalEvent::FinishRecover,
    };
    assert(a1_enabled(recovering.configs.last(), finish_recover));
    a1_extend_adapter_execution_exec(
        request, initial_members, recovering, finish_recover,
    );
}

pub open spec fn a1_start_two_record() -> replay_layer::JournalRecord {
    replay_layer::JournalRecord::Start {
        request: ensure_member_request_zero(),
        attempt: 2,
        digest: replay_layer::Digest { id: 0 },
        key: Option::None,
        arm_ref: 3,
    }
}

pub open spec fn a1_failure_outcome_record()
    -> replay_layer::JournalRecord
{
    replay_layer::JournalRecord::Outcome {
        request: ensure_member_request_zero(),
        attempt: 2,
        observation: replay_layer::Observation::Failure,
        digest: replay_layer::Digest { id: 0 },
        key: Option::None,
        start_ref: 5,
    }
}

pub open spec fn a1_unknown_record() -> replay_layer::JournalRecord {
    replay_layer::JournalRecord::UnknownRec {
        request: ensure_member_request_zero(),
        attempt: Option::Some(2),
        reason: replay_layer::UnknownReason::NonConclusiveFailure,
        digest: replay_layer::Digest { id: 0 },
        key: Option::None,
        evidence_ref: 6,
    }
}

pub open spec fn a1_retry_records()
    -> Seq<replay_layer::JournalRecord>
{
    Seq::empty()
        .push(ensure_member_authorize_record())
        .push(ensure_member_prepare_record())
        .push(ensure_member_arm_record())
        .push(ensure_member_start_record())
        .push(a1_start_two_record())
        .push(a1_failure_outcome_record())
        .push(a1_unknown_record())
}

pub open spec fn a1_precrash_records()
    -> Seq<replay_layer::JournalRecord>
{
    Seq::empty()
        .push(ensure_member_authorize_record())
        .push(ensure_member_prepare_record())
        .push(ensure_member_arm_record())
        .push(ensure_member_start_record())
}

pub open spec fn a1_retry_started_records()
    -> Seq<replay_layer::JournalRecord>
{
    a1_precrash_records().push(a1_start_two_record())
}

pub open spec fn a1_failure_records()
    -> Seq<replay_layer::JournalRecord>
{
    a1_retry_started_records().push(a1_failure_outcome_record())
}

pub open spec fn a1_invoke_one_wal_event()
    -> wal_runtime_layer::WalEvent
{
    ensure_member_invoke_wal_event()
}

pub open spec fn a1_success_one_wal_event()
    -> wal_runtime_layer::WalEvent
{
    ensure_member_deliver_wal_event()
}

pub open spec fn a1_invoke_two_wal_event()
    -> wal_runtime_layer::WalEvent
{
    let cfg = ensure_member_full_config();
    let request = ensure_member_request_zero();
    wal_runtime_layer::WalEvent::InvokeEvent {
        request,
        attempt: 2,
        call: config_layer::canonical_call(cfg, request),
        journal_cut: 5,
        ack_cut: 5,
    }
}

pub open spec fn a1_failure_two_wal_event()
    -> wal_runtime_layer::WalEvent
{
    wal_runtime_layer::WalEvent::DeliverEvent {
        request: ensure_member_request_zero(),
        attempt: 2,
        observation: replay_layer::Observation::Failure,
        journal_cut: 5,
    }
}

pub open spec fn a1_wal_pre_crash_execution()
    -> wal_runtime_layer::WalExecution {
    let cfg = ensure_member_full_config();
    let e0 = t6_a0_zero_wal_execution(cfg);
    let e1 = t6_a0_append_full_wal_execution(
        cfg, e0, ensure_member_authorize_record(),
    );
    let e2 = t6_a0_append_full_wal_execution(
        cfg, e1, ensure_member_prepare_record(),
    );
    let e3 = t6_a0_append_full_wal_execution(
        cfg, e2, ensure_member_arm_record(),
    );
    let e4 = t6_a0_append_full_wal_execution(
        cfg, e3, ensure_member_start_record(),
    );
    let e5 = t6_a0_extend_wal_execution(
        cfg, e4, a1_invoke_one_wal_event(),
    );
    t6_a0_extend_wal_execution(
        cfg, e5, a1_success_one_wal_event(),
    )
}

pub open spec fn a1_wal_recovered_execution()
    -> wal_runtime_layer::WalExecution {
    let cfg = ensure_member_full_config();
    let e6 = a1_wal_pre_crash_execution();
    let e7 = t6_a0_extend_wal_execution(
        cfg, e6, wal_runtime_layer::WalEvent::Crash,
    );
    let e8 = t6_a0_extend_wal_execution(
        cfg, e7, wal_runtime_layer::WalEvent::BeginScan,
    );
    let e9 = t6_a0_extend_wal_execution(
        cfg, e8, wal_runtime_layer::WalEvent::FinishScan,
    );
    let e10 = t6_a0_extend_wal_execution(
        cfg, e9, wal_runtime_layer::WalEvent::TruncateTail,
    );
    let e11 = t6_a0_extend_wal_execution(
        cfg, e10, wal_runtime_layer::WalEvent::BeginRecover,
    );
    t6_a0_extend_wal_execution(
        cfg, e11, wal_runtime_layer::WalEvent::FinishRecover,
    )
}

pub open spec fn a1_wal_retry_observed_execution()
    -> wal_runtime_layer::WalExecution {
    let cfg = ensure_member_full_config();
    let e12 = a1_wal_recovered_execution();
    let e13 = t6_a0_append_full_wal_execution(
        cfg, e12, a1_start_two_record(),
    );
    let e14 = t6_a0_extend_wal_execution(
        cfg, e13, a1_invoke_two_wal_event(),
    );
    t6_a0_extend_wal_execution(
        cfg, e14, a1_failure_two_wal_event(),
    )
}

pub open spec fn a1_wal_failure_outcome_execution()
    -> wal_runtime_layer::WalExecution
{
    t6_a0_append_full_wal_execution(
        ensure_member_full_config(),
        a1_wal_retry_observed_execution(),
        a1_failure_outcome_record(),
    )
}

pub open spec fn a1_retry_wal_execution()
    -> wal_runtime_layer::WalExecution
{
    let cfg = ensure_member_full_config();
    let e16 = a1_wal_failure_outcome_execution();
    t6_a0_append_full_wal_execution(
        cfg, e16, a1_unknown_record(),
    )
}

pub open spec fn a1_observe_wal_event(
    execution: A1AdapterExecution,
    local: wal_runtime_layer::WalEvent,
) -> A1AdapterExecution {
    a1_extend_adapter_execution(
        execution,
        A1AdapterEvent::Observe {
            event: wal_runtime_layer::wal_encode(local),
        },
    )
}

pub open spec fn a1_adapter_pre_crash_execution()
    -> A1AdapterExecution {
    let request = ensure_member_request_zero();
    let cfg = ensure_member_full_config();
    let w0 = t6_a0_zero_wal_execution(cfg);
    let a0 = a1_zero_adapter_execution(request, ISet::empty());
    let a1 = a1_observe_full_append(
        a0,
        ensure_member_authorize_record(),
        wal_runtime_layer::journal_view(w0.configs.last()).len() + 1,
    );
    let w1 = t6_a0_append_full_wal_execution(
        cfg, w0, ensure_member_authorize_record(),
    );
    let a2 = a1_observe_full_append(
        a1,
        ensure_member_prepare_record(),
        wal_runtime_layer::journal_view(w1.configs.last()).len() + 1,
    );
    let w2 = t6_a0_append_full_wal_execution(
        cfg, w1, ensure_member_prepare_record(),
    );
    let a3 = a1_observe_full_append(
        a2,
        ensure_member_arm_record(),
        wal_runtime_layer::journal_view(w2.configs.last()).len() + 1,
    );
    let w3 = t6_a0_append_full_wal_execution(
        cfg, w2, ensure_member_arm_record(),
    );
    let a4 = a1_observe_full_append(
        a3,
        ensure_member_start_record(),
        wal_runtime_layer::journal_view(w3.configs.last()).len() + 1,
    );
    let a5 = a1_observe_wal_event(a4, a1_invoke_one_wal_event());
    let a6 = a1_extend_adapter_execution(
        a5, A1AdapterEvent::ServiceLinearize { attempt: 1 },
    );
    a1_observe_wal_event(a6, a1_success_one_wal_event())
}

pub open spec fn a1_adapter_recovered_execution()
    -> A1AdapterExecution {
    a1_observe_recovery(a1_adapter_pre_crash_execution())
}

pub open spec fn a1_adapter_retry_observed_execution()
    -> A1AdapterExecution {
    let w12 = a1_wal_recovered_execution();
    let a8 = a1_adapter_recovered_execution();
    let a9 = a1_observe_full_append(
        a8,
        a1_start_two_record(),
        wal_runtime_layer::journal_view(w12.configs.last()).len() + 1,
    );
    let a10 = a1_observe_wal_event(a9, a1_invoke_two_wal_event());
    a1_observe_wal_event(a10, a1_failure_two_wal_event())
}

pub open spec fn a1_retry_adapter_execution()
    -> A1AdapterExecution
{
    let cfg = ensure_member_full_config();
    let w15 = a1_wal_retry_observed_execution();
    let a11 = a1_adapter_retry_observed_execution();
    let a12 = a1_observe_full_append(
        a11,
        a1_failure_outcome_record(),
        wal_runtime_layer::journal_view(w15.configs.last()).len() + 1,
    );
    let w16 = t6_a0_append_full_wal_execution(
        cfg, w15, a1_failure_outcome_record(),
    );
    a1_observe_full_append(
        a12,
        a1_unknown_record(),
        wal_runtime_layer::journal_view(w16.configs.last()).len() + 1,
    )
}

pub open spec fn a1_retry_history()
    -> Seq<p0_layer::PhysicalEvent>
{
    let cfg = ensure_member_full_config();
    let request = ensure_member_request_zero();
    Seq::empty()
        .push(p0_layer::PhysicalEvent::Invoke {
            request,
            attempt: 1,
            call: config_layer::canonical_call(cfg, request),
            journal_cut: 4,
            ack_cut: 4,
        })
        .push(p0_layer::PhysicalEvent::Delivered {
            request,
            attempt: 1,
            observation: replay_layer::Observation::Success(
                ensure_member_success_value(),
            ),
            journal_cut: 4,
        })
        .push(p0_layer::PhysicalEvent::Invoke {
            request,
            attempt: 2,
            call: config_layer::canonical_call(cfg, request),
            journal_cut: 5,
            ack_cut: 5,
        })
        .push(p0_layer::PhysicalEvent::Delivered {
            request,
            attempt: 2,
            observation: replay_layer::Observation::Failure,
            journal_cut: 5,
        })
}

pub open spec fn a1_retry_outcome() -> TerminalOutcome {
    TerminalOutcome::UnknownOutcome {
        attempt: Option::Some(2),
        reason: replay_layer::UnknownReason::NonConclusiveFailure,
    }
}

pub open spec fn a1_retry_run() -> ExternalRun<
    ISet<config_layer::Resource>, EnsureMemberWitness,
> {
    a1_external_run(a1_retry_adapter_execution().configs.last())
}

pub open spec fn a1_explicit_crash_retry_trace_shape(
    events: Seq<global_layer::GlobalEvent>,
) -> bool {
    &&& events.len() == 31
    &&& events[14] == global_layer::GlobalEvent::Crash
    &&& events[15] == global_layer::GlobalEvent::BeginScan
    &&& events[16] == global_layer::GlobalEvent::FinishScan
    &&& events[17] == global_layer::GlobalEvent::TruncateTail
    &&& events[18] == global_layer::GlobalEvent::BeginRecover
    &&& events[19] == global_layer::GlobalEvent::FinishRecover
    &&& events[20] == global_layer::GlobalEvent::WalStage {
        record: a1_start_two_record(),
    }
    &&& events[21] == global_layer::GlobalEvent::WalWriteFull {
        record: a1_start_two_record(),
    }
    &&& events[22] == global_layer::GlobalEvent::WalFlushAck { cut: 5 }
    &&& events[23] == wal_runtime_layer::wal_encode(
        a1_invoke_two_wal_event(),
    )
    &&& events[24] == wal_runtime_layer::wal_encode(
        a1_failure_two_wal_event(),
    )
}

proof fn a1_observe_wal_event_exec(
    request: replay_layer::RequestId,
    initial_members: ISet<config_layer::Resource>,
    execution: A1AdapterExecution,
    local: wal_runtime_layer::WalEvent,
)
    requires
        a1_exec(request, initial_members, execution),
        a1_enabled(
            execution.configs.last(),
            A1AdapterEvent::Observe {
                event: wal_runtime_layer::wal_encode(local),
            },
        ),
    ensures a1_exec(
        request,
        initial_members,
        a1_observe_wal_event(execution, local),
    ),
    a1_observe_wal_event(execution, local).events.len()
        == execution.events.len() + 1,
    a1_global_trace(a1_observe_wal_event(execution, local).events)
        == a1_global_trace(execution.events).push(
            wal_runtime_layer::wal_encode(local),
        ),
{
    a1_extend_adapter_execution_exec(
        request,
        initial_members,
        execution,
        A1AdapterEvent::Observe {
            event: wal_runtime_layer::wal_encode(local),
        },
    );
}

proof fn a1_wal_pre_crash_execution_exec()
    ensures
        wal_runtime_layer::exec(
            ensure_member_full_config(),
            a1_wal_pre_crash_execution(),
        ),
        a1_wal_pre_crash_execution().events.len() == 14,
        a1_wal_pre_crash_execution().configs.last().runtime.mode
            == record_layer::Mode::Online,
        wal_runtime_layer::wal_quiescent(
            a1_wal_pre_crash_execution().configs.last(),
        ),
        wal_runtime_layer::journal_view(
            a1_wal_pre_crash_execution().configs.last(),
        ) == a1_precrash_records(),
        a1_wal_pre_crash_execution().configs.last().evidence.physical
            == ensure_member_success_history(),
{
    let cfg = ensure_member_full_config();
    let request = ensure_member_request_zero();
    reveal_with_fuel(replay_layer::replay, 8);
    reveal_with_fuel(replay_layer::authorize_lsn, 8);
    reveal_with_fuel(replay_layer::prepare_lsn, 8);
    reveal_with_fuel(replay_layer::arm_lsn, 8);
    reveal_with_fuel(replay_layer::start_lsn, 8);
    reveal_with_fuel(replay_layer::outcome_lsn, 8);
    reveal_with_fuel(replay_layer::started_count, 8);
    reveal_with_fuel(replay_layer::outcome_count, 8);
    reveal_with_fuel(replay_layer::outcome_observation, 8);
    let e0 = t6_a0_zero_wal_execution(cfg);
    t6_a0_zero_wal_execution_exec(cfg);
    ensure_member_authorize_is_runtime_enabled();
    let e1 = t6_a0_append_full_wal_execution(
        cfg, e0, ensure_member_authorize_record(),
    );
    t6_a0_append_full_wal_execution_exec(
        cfg, e0, ensure_member_authorize_record(),
    );
    assert(wal_runtime_layer::journal_view(e1.configs.last())
        == Seq::empty().push(ensure_member_authorize_record()));
    assert(wal_runtime_layer::runtime_record_enabled(
        cfg, e1.configs.last(), ensure_member_prepare_record(),
    ));
    let e2 = t6_a0_append_full_wal_execution(
        cfg, e1, ensure_member_prepare_record(),
    );
    t6_a0_append_full_wal_execution_exec(
        cfg, e1, ensure_member_prepare_record(),
    );
    assert(wal_runtime_layer::journal_view(e2.configs.last())
        == Seq::empty()
            .push(ensure_member_authorize_record())
            .push(ensure_member_prepare_record()));
    assert(wal_runtime_layer::runtime_record_enabled(
        cfg, e2.configs.last(), ensure_member_arm_record(),
    ));
    let e3 = t6_a0_append_full_wal_execution(
        cfg, e2, ensure_member_arm_record(),
    );
    t6_a0_append_full_wal_execution_exec(
        cfg, e2, ensure_member_arm_record(),
    );
    assert(wal_runtime_layer::journal_view(e3.configs.last())
        == Seq::empty()
            .push(ensure_member_authorize_record())
            .push(ensure_member_prepare_record())
            .push(ensure_member_arm_record()));
    assert(wal_runtime_layer::runtime_record_enabled(
        cfg, e3.configs.last(), ensure_member_start_record(),
    ));
    let e4 = t6_a0_append_full_wal_execution(
        cfg, e3, ensure_member_start_record(),
    );
    t6_a0_append_full_wal_execution_exec(
        cfg, e3, ensure_member_start_record(),
    );
    assert(e4.configs.last().runtime.slot
        == (record_layer::ExecSlot::Ready { request, attempt: 1 }));

    let invoke1 = a1_invoke_one_wal_event();
    let e5 = t6_a0_extend_wal_execution(cfg, e4, invoke1);
    assert(wal_runtime_layer::admissibly_enabled(
        cfg, e4.configs.last(), invoke1,
    ));
    t6_a0_extend_wal_execution_exec(cfg, e4, invoke1);
    assert(e5.configs.last().runtime.slot
        == (record_layer::ExecSlot::InFlight { request, attempt: 1 }));

    let success1 = a1_success_one_wal_event();
    let e6 = t6_a0_extend_wal_execution(cfg, e5, success1);
    assert(wal_runtime_layer::admissibly_enabled(
        cfg, e5.configs.last(), success1,
    ));
    t6_a0_extend_wal_execution_exec(cfg, e5, success1);
    assert(e6 == a1_wal_pre_crash_execution());
    assert(e6.configs.last().runtime.slot
        == (record_layer::ExecSlot::Received {
            request,
            attempt: 1,
            observation: replay_layer::Observation::Success(
                ensure_member_success_value(),
            ),
        }));
    assert(wal_runtime_layer::journal_view(e6.configs.last())
        == a1_precrash_records());
    assert(e6.configs.last().evidence.physical
        == ensure_member_success_history());
}

proof fn a1_adapter_pre_crash_execution_exec()
    ensures
        a1_exec(
            ensure_member_request_zero(),
            ISet::empty(),
            a1_adapter_pre_crash_execution(),
        ),
        a1_adapter_pre_crash_execution().configs.last().mode
            == A1AdapterMode::Online,
        a1_adapter_pre_crash_execution().configs.last().active.is_none(),
        a1_adapter_pre_crash_execution().configs.last()
            .linearized_attempts.contains(1),
        a1_adapter_pre_crash_execution().configs.last().history
            == ensure_member_success_history(),
        a1_global_trace(a1_adapter_pre_crash_execution().events)
            == a1_wal_pre_crash_execution().events,
        a1_adapter_pre_crash_execution().events.len() == 15,
{
    let request = ensure_member_request_zero();
    let initial = ISet::<config_layer::Resource>::empty();
    let cfg = ensure_member_full_config();
    let w0 = t6_a0_zero_wal_execution(cfg);
    let a0 = a1_zero_adapter_execution(request, initial);
    a1_zero_adapter_execution_exec(request, initial);
    assert(a1_global_trace(a0.events) == w0.events);
    let cut1 = wal_runtime_layer::journal_view(w0.configs.last()).len() + 1;
    let a1 = a1_observe_full_append(
        a0, ensure_member_authorize_record(), cut1,
    );
    let w1 = t6_a0_append_full_wal_execution(
        cfg, w0, ensure_member_authorize_record(),
    );
    a1_observe_full_append_exec(
        request, initial, a0, ensure_member_authorize_record(), cut1,
    );
    assert(a1_global_trace(a1.events) == w1.events);
    let cut2 = wal_runtime_layer::journal_view(w1.configs.last()).len() + 1;
    let a2 = a1_observe_full_append(
        a1, ensure_member_prepare_record(), cut2,
    );
    let w2 = t6_a0_append_full_wal_execution(
        cfg, w1, ensure_member_prepare_record(),
    );
    a1_observe_full_append_exec(
        request, initial, a1, ensure_member_prepare_record(), cut2,
    );
    assert(a1_global_trace(a2.events) == w2.events);
    let cut3 = wal_runtime_layer::journal_view(w2.configs.last()).len() + 1;
    let a3 = a1_observe_full_append(
        a2, ensure_member_arm_record(), cut3,
    );
    let w3 = t6_a0_append_full_wal_execution(
        cfg, w2, ensure_member_arm_record(),
    );
    a1_observe_full_append_exec(
        request, initial, a2, ensure_member_arm_record(), cut3,
    );
    assert(a1_global_trace(a3.events) == w3.events);
    let cut4 = wal_runtime_layer::journal_view(w3.configs.last()).len() + 1;
    let a4 = a1_observe_full_append(
        a3, ensure_member_start_record(), cut4,
    );
    let w4 = t6_a0_append_full_wal_execution(
        cfg, w3, ensure_member_start_record(),
    );
    a1_observe_full_append_exec(
        request, initial, a3, ensure_member_start_record(), cut4,
    );
    assert(a1_global_trace(a4.events) == w4.events);
    assert(a4.configs.last().mode == A1AdapterMode::Online);
    assert(a4.configs.last().active.is_none());
    assert(a4.configs.last().history == Seq::empty());

    let invoke1 = a1_invoke_one_wal_event();
    let a5 = a1_observe_wal_event(a4, invoke1);
    let w5 = t6_a0_extend_wal_execution(cfg, w4, invoke1);
    assert(a1_enabled(
        a4.configs.last(),
        A1AdapterEvent::Observe {
            event: wal_runtime_layer::wal_encode(invoke1),
        },
    ));
    a1_observe_wal_event_exec(request, initial, a4, invoke1);
    assert(a1_global_trace(a5.events) == w5.events);
    a1_every_exec_configuration_satisfies_invariant(
        request, initial, a5,
    );
    assert(a5.configs.last()
        == a5.configs[a5.events.len() as int]);
    assert(a1_execution_invariant(
        request, initial, a5.configs.last(),
    ));

    let linearize = A1AdapterEvent::ServiceLinearize { attempt: 1 };
    let a6 = a1_extend_adapter_execution(a5, linearize);
    assert(a1_enabled(a5.configs.last(), linearize));
    a1_extend_adapter_execution_exec(
        request, initial, a5, linearize,
    );
    assert(a6.configs.last().linearized_attempts.contains(1));

    let success1 = a1_success_one_wal_event();
    let a7 = a1_observe_wal_event(a6, success1);
    let w6 = t6_a0_extend_wal_execution(cfg, w5, success1);
    assert(a1_enabled(
        a6.configs.last(),
        A1AdapterEvent::Observe {
            event: wal_runtime_layer::wal_encode(success1),
        },
    ));
    a1_observe_wal_event_exec(request, initial, a6, success1);
    assert(a1_global_trace(a6.events) == w5.events);
    assert(a1_global_trace(a7.events) == w6.events);
    assert(a7 == a1_adapter_pre_crash_execution());
    assert(w6 == a1_wal_pre_crash_execution());
    assert(a7.configs.last().history == ensure_member_success_history());
    assert(a1_global_trace(a7.events)
        == a1_wal_pre_crash_execution().events);
    assert(a7.events.len() == 15);
}

proof fn a1_adapter_recovered_execution_exec()
    ensures
        a1_exec(
            ensure_member_request_zero(),
            ISet::empty(),
            a1_adapter_recovered_execution(),
        ),
        a1_adapter_recovered_execution().configs.last().mode
            == A1AdapterMode::Online,
        a1_adapter_recovered_execution().configs.last().active.is_none(),
        a1_adapter_recovered_execution().configs.last().history
            == ensure_member_success_history(),
        a1_global_trace(a1_adapter_recovered_execution().events)
            == a1_wal_recovered_execution().events,
        a1_adapter_recovered_execution().events.len() == 21,
{
    let request = ensure_member_request_zero();
    let initial = ISet::<config_layer::Resource>::empty();
    let before = a1_adapter_pre_crash_execution();
    a1_adapter_pre_crash_execution_exec();
    a1_observe_recovery_exec(request, initial, before);
    assert(a1_global_trace(a1_adapter_recovered_execution().events)
        == a1_wal_recovered_execution().events);
}

proof fn a1_precrash_recovery_complete()
    ensures
        query_layer::recovery_complete_j(
            config_layer::erase_config(ensure_member_full_config()),
            a1_precrash_records(),
        ),
{
    let cfg = ensure_member_full_config();
    let erased = config_layer::erase_config(cfg);
    let journal = a1_precrash_records();
    ensure_member_full_config_is_well_formed();
    assert(journal =~= Seq::empty()
        .push(ensure_member_authorize_record())
        .push(ensure_member_prepare_record())
        .push(ensure_member_arm_record())
        .push(ensure_member_start_record()));
    reveal_with_fuel(replay_layer::replay, 8);
    reveal_with_fuel(replay_layer::started_count, 8);
    reveal_with_fuel(replay_layer::outcome_count, 8);
    reveal_with_fuel(replay_layer::outcome_observation, 8);
    reveal_with_fuel(replay_layer::arm_lsn, 8);
    assert forall|request: replay_layer::RequestId|
        !#[trigger] query_layer::unsafe_uncontrolled_j(
            erased, journal, request,
        )
        && !(replay_layer::replay(erased, journal).phase[request]
            == replay_layer::Phase::Armed
            && replay_layer::failure_conclusive(erased, journal, request)) by {
        assert(erased.request_class[request]
            == replay_layer::RetryClass::Idempotent);
        assert(!query_layer::unsafe_uncontrolled_j(
            erased, journal, request,
        ));
        if request == ensure_member_request_zero() {
            assert(replay_layer::replay(erased, journal).phase[request]
                == replay_layer::Phase::Armed);
            assert(replay_layer::outcome_count(journal, request, 1) == 0);
            query_layer::outcome_count_zero_implies_no_observation(
                journal, request, 1,
            );
            assert(replay_layer::outcome_observation(
                journal, request, 1,
            ).is_none());
            assert(!replay_layer::failure_conclusive(
                erased, journal, request,
            ));
        } else {
            assert(replay_layer::replay(erased, journal).phase[request]
                == replay_layer::Phase::New);
        }
    }
}

proof fn a1_wal_recovered_execution_exec()
    ensures
        wal_runtime_layer::exec(
            ensure_member_full_config(),
            a1_wal_recovered_execution(),
        ),
        a1_wal_recovered_execution().events.len() == 20,
        a1_wal_recovered_execution().configs.len() == 21,
        a1_wal_recovered_execution().configs.last().runtime.mode
            == record_layer::Mode::Online,
        wal_runtime_layer::wal_quiescent(
            a1_wal_recovered_execution().configs.last(),
        ),
        wal_runtime_layer::journal_view(
            a1_wal_recovered_execution().configs.last(),
        ) == a1_precrash_records(),
        a1_wal_recovered_execution().configs.last().evidence.physical
            == ensure_member_success_history(),
{
    let cfg = ensure_member_full_config();
    let e6 = a1_wal_pre_crash_execution();
    a1_wal_pre_crash_execution_exec();

    let crash = wal_runtime_layer::WalEvent::Crash;
    let e7 = t6_a0_extend_wal_execution(cfg, e6, crash);
    assert(wal_runtime_layer::admissibly_enabled(
        cfg, e6.configs.last(), crash,
    ));
    t6_a0_extend_wal_execution_exec(cfg, e6, crash);
    assert(e7.configs.last().runtime.mode == record_layer::Mode::Crashed);
    assert(e7.configs.last().runtime.slot == record_layer::ExecSlot::Idle);
    assert(e7.configs.last().runtime.store.cache == Seq::empty());
    assert(e7.configs.last().runtime.store.acked_len == 0);
    assert(wal_runtime_layer::journal_view(e7.configs.last())
        == a1_precrash_records());

    let begin_scan = wal_runtime_layer::WalEvent::BeginScan;
    let e8 = t6_a0_extend_wal_execution(cfg, e7, begin_scan);
    assert(wal_runtime_layer::admissibly_enabled(
        cfg, e7.configs.last(), begin_scan,
    ));
    t6_a0_extend_wal_execution_exec(cfg, e7, begin_scan);
    assert(e8.configs.last().runtime.mode == record_layer::Mode::Crashed);
    assert(e8.configs.last().runtime.store.scan_phase
        == wal_runtime_layer::ScanPhase::Scanning);

    let finish_scan = wal_runtime_layer::WalEvent::FinishScan;
    let e9 = t6_a0_extend_wal_execution(cfg, e8, finish_scan);
    assert(wal_runtime_layer::admissibly_enabled(
        cfg, e8.configs.last(), finish_scan,
    ));
    t6_a0_extend_wal_execution_exec(cfg, e8, finish_scan);
    assert(e9.configs.last().runtime.store.scan_phase
        == wal_runtime_layer::ScanPhase::Scanned);
    assert(e9.configs.last().runtime.store.scan_result
        == a1_precrash_records());

    let truncate = wal_runtime_layer::WalEvent::TruncateTail;
    let e10 = t6_a0_extend_wal_execution(cfg, e9, truncate);
    assert(wal_runtime_layer::admissibly_enabled(
        cfg, e9.configs.last(), truncate,
    ));
    t6_a0_extend_wal_execution_exec(cfg, e9, truncate);
    assert(e10.configs.last().runtime.store.scan_phase
        == wal_runtime_layer::ScanPhase::Truncated);
    assert(e10.configs.last().runtime.store.media
        == wal_runtime_layer::full_frames(a1_precrash_records()));
    wal_runtime_layer::parse_full_frames(a1_precrash_records());
    assert(wal_runtime_layer::journal_view(e10.configs.last())
        == a1_precrash_records());

    let begin_recover = wal_runtime_layer::WalEvent::BeginRecover;
    let e11 = t6_a0_extend_wal_execution(cfg, e10, begin_recover);
    assert(wal_runtime_layer::admissibly_enabled(
        cfg, e10.configs.last(), begin_recover,
    ));
    t6_a0_extend_wal_execution_exec(cfg, e10, begin_recover);
    assert(e11.configs.last().runtime.mode
        == record_layer::Mode::Recovering);
    assert(e11.configs.last().runtime.store.cache
        == a1_precrash_records());
    assert(e11.configs.last().runtime.store.acked_len == 4);
    assert(e11.configs.last().runtime.store.scan_phase
        == wal_runtime_layer::ScanPhase::Idle);

    let finish_recover = wal_runtime_layer::WalEvent::FinishRecover;
    a1_precrash_recovery_complete();
    assert(wal_runtime_layer::journal_view(e11.configs.last())
        == a1_precrash_records());
    let e12 = t6_a0_extend_wal_execution(cfg, e11, finish_recover);
    assert(wal_runtime_layer::admissibly_enabled(
        cfg, e11.configs.last(), finish_recover,
    ));
    t6_a0_extend_wal_execution_exec(cfg, e11, finish_recover);
    assert(e12 == a1_wal_recovered_execution());
    assert(e12.configs.last().runtime.mode == record_layer::Mode::Online);
    assert(wal_runtime_layer::wal_quiescent(e12.configs.last()));
    assert(wal_runtime_layer::journal_view(e12.configs.last())
        == a1_precrash_records());
    assert(e12.configs.last().evidence.physical
        == ensure_member_success_history());
}

proof fn a1_adapter_retry_observed_execution_exec()
    ensures
        a1_exec(
            ensure_member_request_zero(),
            ISet::empty(),
            a1_adapter_retry_observed_execution(),
        ),
        a1_adapter_retry_observed_execution().configs.last().history
            == a1_retry_history(),
        a1_adapter_retry_observed_execution().configs.last()
            .linearized_attempts.contains(1),
        !a1_adapter_retry_observed_execution().configs.last()
            .linearized_attempts.contains(2),
        a1_global_trace(a1_adapter_retry_observed_execution().events)
            == a1_wal_retry_observed_execution().events,
        a1_adapter_retry_observed_execution().events.len() == 26,
{
    let request = ensure_member_request_zero();
    let initial = ISet::<config_layer::Resource>::empty();
    let w12 = a1_wal_recovered_execution();
    let a8 = a1_adapter_recovered_execution();
    a1_adapter_recovered_execution_exec();
    let cut5 = wal_runtime_layer::journal_view(w12.configs.last()).len() + 1;
    let a9 = a1_observe_full_append(a8, a1_start_two_record(), cut5);
    a1_observe_full_append_exec(
        request, initial, a8, a1_start_two_record(), cut5,
    );
    assert(a9.configs.last().mode == A1AdapterMode::Online);
    assert(a9.configs.last().active.is_none());
    assert(a9.configs.last().history == ensure_member_success_history());
    reveal_with_fuel(p1_layer::invoke_count, 4);
    reveal_with_fuel(p1_layer::delivery_count, 4);
    assert(p1_layer::invoke_count(
        a9.configs.last().history, request, 2,
    ) == 0);
    assert(p1_layer::delivery_count(
        a9.configs.last().history, request, 2,
    ) == 0);

    let invoke2 = a1_invoke_two_wal_event();
    let a10 = a1_observe_wal_event(a9, invoke2);
    assert(a1_enabled(
        a9.configs.last(),
        A1AdapterEvent::Observe {
            event: wal_runtime_layer::wal_encode(invoke2),
        },
    ));
    a1_observe_wal_event_exec(request, initial, a9, invoke2);
    a1_every_exec_configuration_satisfies_invariant(
        request, initial, a10,
    );
    assert(a10.configs.last()
        == a10.configs[a10.events.len() as int]);
    assert(a1_execution_invariant(
        request, initial, a10.configs.last(),
    ));
    assert(a10.configs.last().active == Option::Some(2));
    assert(!a10.configs.last().linearized_attempts.contains(2));

    let failure2 = a1_failure_two_wal_event();
    let a11 = a1_observe_wal_event(a10, failure2);
    assert(a1_enabled(
        a10.configs.last(),
        A1AdapterEvent::Observe {
            event: wal_runtime_layer::wal_encode(failure2),
        },
    ));
    a1_observe_wal_event_exec(request, initial, a10, failure2);
    assert(a11 == a1_adapter_retry_observed_execution());
    assert(a11.configs.last().history == a1_retry_history());
    assert(a1_global_trace(a11.events)
        == a1_wal_retry_observed_execution().events);
}

proof fn a1_start_two_runtime_enabled(
    cfg: config_layer::FullConfig,
    state: wal_runtime_layer::WalConfiguration,
)
    requires
        cfg == ensure_member_full_config(),
        state.runtime.mode == record_layer::Mode::Online,
        state.runtime.slot == record_layer::ExecSlot::Idle,
        wal_runtime_layer::journal_view(state) == a1_precrash_records(),
    ensures
        wal_runtime_layer::runtime_record_enabled(
            cfg, state, a1_start_two_record(),
        ),
{
    let request = ensure_member_request_zero();
    let erased = config_layer::erase_config(cfg);
    let journal = a1_precrash_records();
    ensure_member_full_config_is_well_formed();
    assert(journal =~= Seq::empty()
        .push(ensure_member_authorize_record())
        .push(ensure_member_prepare_record())
        .push(ensure_member_arm_record())
        .push(ensure_member_start_record()));
    reveal_with_fuel(replay_layer::replay, 8);
    reveal_with_fuel(replay_layer::started_count, 8);
    reveal_with_fuel(replay_layer::outcome_count, 8);
    reveal_with_fuel(replay_layer::outcome_observation, 8);
    reveal_with_fuel(replay_layer::arm_lsn, 8);
    assert(replay_layer::replay(erased, journal).phase[request]
        == replay_layer::Phase::Armed);
    assert(replay_layer::started_count(journal, request) == 1);
    assert(replay_layer::outcome_count(journal, request, 1) == 0);
    query_layer::outcome_count_zero_implies_no_observation(
        journal, request, 1,
    );
    assert(replay_layer::outcome_observation(journal, request, 1)
        == Option::None);
    assert(!replay_layer::failure_conclusive(erased, journal, request));
    assert(replay_layer::request_fields_match(
        erased,
        request,
        replay_layer::Digest { id: 0 },
        Option::None,
    ));
    assert(replay_layer::arm_lsn(journal, request)
        == Option::Some(3));
    assert(replay_layer::ref_is(
        3, replay_layer::arm_lsn(journal, request),
    ));
    assert(2 <= erased.max_attempts[request]);
    assert(erased.request_class[request]
        != replay_layer::RetryClass::Uncontrolled);
    assert(replay_layer::structural_enabled(
        erased, journal, a1_start_two_record(),
    ));
    assert(record_layer::durable_slot_update(
        erased,
        replay_layer::replay(erased, journal),
        record_layer::Mode::Online,
        record_layer::ExecSlot::Idle,
        a1_start_two_record(),
    ).is_some());
}

proof fn a1_wal_retry_start_two_exec()
    ensures
        wal_runtime_layer::exec(
            ensure_member_full_config(),
            t6_a0_append_full_wal_execution(
                ensure_member_full_config(),
                a1_wal_recovered_execution(),
                a1_start_two_record(),
            ),
        ),
        t6_a0_append_full_wal_execution(
            ensure_member_full_config(),
            a1_wal_recovered_execution(),
            a1_start_two_record(),
        ).configs.last().runtime.slot
            == (record_layer::ExecSlot::Ready {
                request: ensure_member_request_zero(),
                attempt: 2,
            }),
        t6_a0_append_full_wal_execution(
            ensure_member_full_config(),
            a1_wal_recovered_execution(),
            a1_start_two_record(),
        ).configs.last().runtime.mode
            == record_layer::Mode::Online,
        wal_runtime_layer::wal_quiescent(
            t6_a0_append_full_wal_execution(
                ensure_member_full_config(),
                a1_wal_recovered_execution(),
                a1_start_two_record(),
            ).configs.last(),
        ),
        wal_runtime_layer::journal_view(
            t6_a0_append_full_wal_execution(
                ensure_member_full_config(),
                a1_wal_recovered_execution(),
                a1_start_two_record(),
            ).configs.last(),
        ) == a1_precrash_records().push(a1_start_two_record()),
        t6_a0_append_full_wal_execution(
            ensure_member_full_config(),
            a1_wal_recovered_execution(),
            a1_start_two_record(),
        ).configs.last().evidence.records
            == a1_precrash_records().push(a1_start_two_record()),
        t6_a0_append_full_wal_execution(
            ensure_member_full_config(),
            a1_wal_recovered_execution(),
            a1_start_two_record(),
        ).configs.last().evidence.acknowledged_prefix
            == a1_precrash_records().push(a1_start_two_record()),
        t6_a0_append_full_wal_execution(
            ensure_member_full_config(),
            a1_wal_recovered_execution(),
            a1_start_two_record(),
        ).configs.last().evidence.physical
            == ensure_member_success_history(),
        t6_a0_append_full_wal_execution(
            ensure_member_full_config(),
            a1_wal_recovered_execution(),
            a1_start_two_record(),
        ).configs.last().runtime.store.media
            == wal_runtime_layer::full_frames(
                a1_precrash_records().push(a1_start_two_record()),
            ),
{
    let cfg = ensure_member_full_config();
    let e12 = a1_wal_recovered_execution();
    a1_wal_recovered_execution_exec();
    let start2 = a1_start_two_record();
    a1_start_two_runtime_enabled(cfg, e12.configs.last());
    t6_a0_append_full_wal_execution_exec(cfg, e12, start2);
    let e13 = t6_a0_append_full_wal_execution(cfg, e12, start2);
    assert(e13.configs.last().runtime.slot
        == (record_layer::ExecSlot::Ready {
            request: ensure_member_request_zero(),
            attempt: 2,
        }));
    assert(wal_runtime_layer::journal_view(e13.configs.last())
        == a1_precrash_records().push(start2));
    assert(e13.configs.last().evidence.records
        == a1_precrash_records().push(start2));
    assert(e13.configs.last().evidence.acknowledged_prefix
        == e13.configs.last().evidence.records);
    assert(e13.configs.last().evidence.physical
        == ensure_member_success_history());
    assert(e13.configs.last().runtime.store.media
        == wal_runtime_layer::full_frames(
            a1_precrash_records().push(start2),
        ));
}

proof fn a1_wal_retry_invoke_two_exec()
    ensures
        wal_runtime_layer::exec(
            ensure_member_full_config(),
            t6_a0_extend_wal_execution(
                ensure_member_full_config(),
                t6_a0_append_full_wal_execution(
                    ensure_member_full_config(),
                    a1_wal_recovered_execution(),
                    a1_start_two_record(),
                ),
                a1_invoke_two_wal_event(),
            ),
        ),
        t6_a0_extend_wal_execution(
            ensure_member_full_config(),
            t6_a0_append_full_wal_execution(
                ensure_member_full_config(),
                a1_wal_recovered_execution(),
                a1_start_two_record(),
            ),
            a1_invoke_two_wal_event(),
        ).configs.last().runtime.slot
            == (record_layer::ExecSlot::InFlight {
                request: ensure_member_request_zero(),
                attempt: 2,
            }),
        t6_a0_extend_wal_execution(
            ensure_member_full_config(),
            t6_a0_append_full_wal_execution(
                ensure_member_full_config(),
                a1_wal_recovered_execution(),
                a1_start_two_record(),
            ),
            a1_invoke_two_wal_event(),
        ).configs.last().runtime.mode
            == record_layer::Mode::Online,
        wal_runtime_layer::wal_quiescent(
            t6_a0_extend_wal_execution(
                ensure_member_full_config(),
                t6_a0_append_full_wal_execution(
                    ensure_member_full_config(),
                    a1_wal_recovered_execution(),
                    a1_start_two_record(),
                ),
                a1_invoke_two_wal_event(),
            ).configs.last(),
        ),
        wal_runtime_layer::journal_view(
            t6_a0_extend_wal_execution(
                ensure_member_full_config(),
                t6_a0_append_full_wal_execution(
                    ensure_member_full_config(),
                    a1_wal_recovered_execution(),
                    a1_start_two_record(),
                ),
                a1_invoke_two_wal_event(),
            ).configs.last(),
        ) == a1_precrash_records().push(a1_start_two_record()),
        t6_a0_extend_wal_execution(
            ensure_member_full_config(),
            t6_a0_append_full_wal_execution(
                ensure_member_full_config(),
                a1_wal_recovered_execution(),
                a1_start_two_record(),
            ),
            a1_invoke_two_wal_event(),
        ).configs.last().evidence.physical
            == a1_retry_history().take(3),
        t6_a0_extend_wal_execution(
            ensure_member_full_config(),
            t6_a0_append_full_wal_execution(
                ensure_member_full_config(),
                a1_wal_recovered_execution(),
                a1_start_two_record(),
            ),
            a1_invoke_two_wal_event(),
        ).configs.last().runtime.store.media
            == wal_runtime_layer::full_frames(
                a1_precrash_records().push(a1_start_two_record()),
            ),
        t6_a0_extend_wal_execution(
            ensure_member_full_config(),
            t6_a0_append_full_wal_execution(
                ensure_member_full_config(),
                a1_wal_recovered_execution(),
                a1_start_two_record(),
            ),
            a1_invoke_two_wal_event(),
        ).configs.last().evidence.records
            == a1_precrash_records().push(a1_start_two_record()),
        t6_a0_extend_wal_execution(
            ensure_member_full_config(),
            t6_a0_append_full_wal_execution(
                ensure_member_full_config(),
                a1_wal_recovered_execution(),
                a1_start_two_record(),
            ),
            a1_invoke_two_wal_event(),
        ).configs.last().evidence.acknowledged_prefix
            == a1_precrash_records().push(a1_start_two_record()),
{
    let cfg = ensure_member_full_config();
    let e12 = a1_wal_recovered_execution();
    a1_wal_retry_start_two_exec();
    let e13 = t6_a0_append_full_wal_execution(cfg, e12,
        a1_start_two_record());
    let invoke2 = a1_invoke_two_wal_event();
    assert(e13.configs.last().evidence.acknowledged_prefix.len() == 5);
    assert(journal_runtime_layer::start_covered_by_cut(
        e13.configs.last().evidence.records,
        ensure_member_request_zero(),
        2,
        5,
    ));
    assert(wal_runtime_layer::admissibly_enabled(
        cfg, e13.configs.last(), invoke2,
    ));
    t6_a0_extend_wal_execution_exec(cfg, e13, invoke2);
    assert(t6_a0_extend_wal_execution(cfg, e13, invoke2)
        .configs.last().runtime.slot
        == (record_layer::ExecSlot::InFlight {
            request: ensure_member_request_zero(),
            attempt: 2,
        }));
    let e14 = t6_a0_extend_wal_execution(cfg, e13, invoke2);
    assert(e14.configs.last().runtime.mode == record_layer::Mode::Online);
    assert(wal_runtime_layer::wal_quiescent(e14.configs.last()));
    assert(wal_runtime_layer::journal_view(e14.configs.last())
        == a1_precrash_records().push(a1_start_two_record()));
    assert(e14.configs.last().evidence.physical
        == a1_retry_history().take(3));
    assert(e14.configs.last().runtime.store.media
        == wal_runtime_layer::full_frames(
            a1_precrash_records().push(a1_start_two_record()),
        ));
    assert(e14.configs.last().evidence.records
        == a1_precrash_records().push(a1_start_two_record()));
    assert(e14.configs.last().evidence.acknowledged_prefix
        == a1_precrash_records().push(a1_start_two_record()));
}

proof fn a1_wal_retry_failure_two_exec()
    ensures
        wal_runtime_layer::exec(
            ensure_member_full_config(),
            a1_wal_retry_observed_execution(),
        ),
        a1_wal_retry_observed_execution().configs.last().runtime.slot
            == (record_layer::ExecSlot::Received {
                request: ensure_member_request_zero(),
                attempt: 2,
                observation: replay_layer::Observation::Failure,
            }),
        a1_wal_retry_observed_execution().events.len() == 25,
        a1_wal_retry_observed_execution().configs.len() == 26,
        a1_wal_retry_observed_execution().configs.last().runtime.mode
            == record_layer::Mode::Online,
        wal_runtime_layer::wal_quiescent(
            a1_wal_retry_observed_execution().configs.last(),
        ),
        wal_runtime_layer::journal_view(
            a1_wal_retry_observed_execution().configs.last(),
        ) == a1_precrash_records().push(a1_start_two_record()),
        a1_wal_retry_observed_execution().configs.last().evidence.physical
            == a1_retry_history(),
        a1_wal_retry_observed_execution().configs.last().runtime.store.media
            == wal_runtime_layer::full_frames(
                a1_precrash_records().push(a1_start_two_record()),
            ),
        a1_wal_retry_observed_execution().configs.last().evidence.records
            == a1_precrash_records().push(a1_start_two_record()),
        a1_wal_retry_observed_execution().configs.last()
            .evidence.acknowledged_prefix
            == a1_precrash_records().push(a1_start_two_record()),
{
    let cfg = ensure_member_full_config();
    let e12 = a1_wal_recovered_execution();
    a1_wal_retry_invoke_two_exec();
    let e13 = t6_a0_append_full_wal_execution(cfg, e12,
        a1_start_two_record());
    let e14 = t6_a0_extend_wal_execution(cfg, e13,
        a1_invoke_two_wal_event());
    let failure2 = a1_failure_two_wal_event();
    assert(wal_runtime_layer::admissibly_enabled(
        cfg, e14.configs.last(), failure2,
    ));
    t6_a0_extend_wal_execution_exec(cfg, e14, failure2);
    let e15 = t6_a0_extend_wal_execution(cfg, e14, failure2);
    assert(e15 == a1_wal_retry_observed_execution());
    assert(e15.configs.last().runtime.slot
        == (record_layer::ExecSlot::Received {
            request: ensure_member_request_zero(),
            attempt: 2,
            observation: replay_layer::Observation::Failure,
        }));
    assert(e15.configs.last().evidence.physical == a1_retry_history());
    assert(e15.configs.last().runtime.store.media
        == wal_runtime_layer::full_frames(
            a1_precrash_records().push(a1_start_two_record()),
        ));
    assert(e15.configs.last().evidence.records
        == a1_precrash_records().push(a1_start_two_record()));
    assert(e15.configs.last().evidence.acknowledged_prefix
        == a1_precrash_records().push(a1_start_two_record()));
    assert(e15.configs.last().runtime.mode == record_layer::Mode::Online);
    assert(wal_runtime_layer::wal_quiescent(e15.configs.last()));
    assert(wal_runtime_layer::journal_view(e15.configs.last())
        == a1_precrash_records().push(a1_start_two_record()));
    assert(e15.events.len() == 25);
    assert(e15.configs.len() == 26);
}

proof fn a1_wal_retry_observed_execution_exec()
    ensures
        wal_runtime_layer::exec(
            ensure_member_full_config(),
            a1_wal_retry_observed_execution(),
        ),
        a1_wal_retry_observed_execution().events.len() == 25,
        a1_wal_retry_observed_execution().configs.len() == 26,
        a1_wal_retry_observed_execution().configs.last().runtime.mode
            == record_layer::Mode::Online,
        wal_runtime_layer::wal_quiescent(
            a1_wal_retry_observed_execution().configs.last(),
        ),
        wal_runtime_layer::journal_view(
            a1_wal_retry_observed_execution().configs.last(),
        ) == a1_precrash_records().push(a1_start_two_record()),
        a1_wal_retry_observed_execution().configs.last().evidence.physical
            == a1_retry_history(),
        a1_wal_retry_observed_execution().configs.last().runtime.store.media
            == wal_runtime_layer::full_frames(
                a1_precrash_records().push(a1_start_two_record()),
            ),
        a1_wal_retry_observed_execution().configs.last().evidence.records
            == a1_precrash_records().push(a1_start_two_record()),
        a1_wal_retry_observed_execution().configs.last()
            .evidence.acknowledged_prefix
            == a1_precrash_records().push(a1_start_two_record()),
{
    a1_wal_retry_failure_two_exec();
}

proof fn a1_failure_outcome_runtime_enabled(
    cfg: config_layer::FullConfig,
    state: wal_runtime_layer::WalConfiguration,
)
    requires
        cfg == ensure_member_full_config(),
        state.runtime.mode == record_layer::Mode::Online,
        state.runtime.slot == (record_layer::ExecSlot::Received {
            request: ensure_member_request_zero(),
            attempt: 2,
            observation: replay_layer::Observation::Failure,
        }),
        wal_runtime_layer::journal_view(state)
            == a1_retry_started_records(),
    ensures
        wal_runtime_layer::runtime_record_enabled(
            cfg, state, a1_failure_outcome_record(),
        ),
{
    let request = ensure_member_request_zero();
    let erased = config_layer::erase_config(cfg);
    let journal = a1_retry_started_records();
    ensure_member_full_config_is_well_formed();
    assert(journal =~= Seq::empty()
        .push(ensure_member_authorize_record())
        .push(ensure_member_prepare_record())
        .push(ensure_member_arm_record())
        .push(ensure_member_start_record())
        .push(a1_start_two_record()));
    reveal_with_fuel(replay_layer::replay, 9);
    reveal_with_fuel(replay_layer::started_count, 9);
    reveal_with_fuel(replay_layer::outcome_count, 9);
    reveal_with_fuel(replay_layer::start_lsn, 9);
    assert(replay_layer::replay(erased, journal).phase[request]
        == replay_layer::Phase::Armed);
    assert(replay_layer::started_count(journal, request) == 2);
    assert(replay_layer::outcome_count(journal, request, 2) == 0);
    assert(replay_layer::start_lsn(journal, request, 2)
        == Option::Some(5));
    assert(replay_layer::request_fields_match(
        erased,
        request,
        replay_layer::Digest { id: 0 },
        Option::None,
    ));
    assert(replay_layer::structural_enabled(
        erased, journal, a1_failure_outcome_record(),
    ));
    assert(record_layer::durable_slot_update(
        erased,
        replay_layer::replay(erased, journal),
        record_layer::Mode::Online,
        record_layer::ExecSlot::Received {
            request,
            attempt: 2,
            observation: replay_layer::Observation::Failure,
        },
        a1_failure_outcome_record(),
    ).is_some());
}

proof fn a1_wal_failure_outcome_execution_exec()
    ensures
        wal_runtime_layer::exec(
            ensure_member_full_config(),
            a1_wal_failure_outcome_execution(),
        ),
        a1_wal_failure_outcome_execution().events.len() == 28,
        a1_wal_failure_outcome_execution().configs.len() == 29,
        a1_wal_failure_outcome_execution().configs.last().runtime.mode
            == record_layer::Mode::Online,
        a1_wal_failure_outcome_execution().configs.last().runtime.slot
            == (record_layer::ExecSlot::ObservedFailure {
                request: ensure_member_request_zero(),
                attempt: 2,
            }),
        wal_runtime_layer::wal_quiescent(
            a1_wal_failure_outcome_execution().configs.last(),
        ),
        wal_runtime_layer::journal_view(
            a1_wal_failure_outcome_execution().configs.last(),
        ) == a1_failure_records(),
        a1_wal_failure_outcome_execution().configs.last()
            .runtime.store.media
            == wal_runtime_layer::full_frames(a1_failure_records()),
        a1_wal_failure_outcome_execution().configs.last().evidence.records
            == a1_failure_records(),
        a1_wal_failure_outcome_execution().configs.last()
            .evidence.acknowledged_prefix == a1_failure_records(),
        a1_wal_failure_outcome_execution().configs.last().evidence.physical
            == a1_retry_history(),
{
    let cfg = ensure_member_full_config();
    let e15 = a1_wal_retry_observed_execution();
    a1_wal_retry_observed_execution_exec();
    assert(wal_runtime_layer::journal_view(e15.configs.last())
        == a1_retry_started_records());
    a1_failure_outcome_runtime_enabled(cfg, e15.configs.last());
    t6_a0_append_full_wal_execution_exec(
        cfg, e15, a1_failure_outcome_record(),
    );
    let e16 = a1_wal_failure_outcome_execution();
    assert(e16.configs.last().runtime.slot
        == (record_layer::ExecSlot::ObservedFailure {
            request: ensure_member_request_zero(),
            attempt: 2,
        }));
    assert(wal_runtime_layer::journal_view(e16.configs.last())
        == a1_failure_records());
    assert(e16.configs.last().runtime.store.media
        == wal_runtime_layer::full_frames(a1_failure_records()));
    assert(e16.configs.last().evidence.records
        == a1_failure_records());
    assert(e16.configs.last().evidence.acknowledged_prefix
        == a1_failure_records());
    assert(e16.configs.last().evidence.physical == a1_retry_history());
    assert(e16.events.len() == 28);
    assert(e16.configs.len() == 29);
}

proof fn a1_unknown_runtime_enabled(
    cfg: config_layer::FullConfig,
    state: wal_runtime_layer::WalConfiguration,
)
    requires
        cfg == ensure_member_full_config(),
        state.runtime.mode == record_layer::Mode::Online,
        state.runtime.slot == (record_layer::ExecSlot::ObservedFailure {
            request: ensure_member_request_zero(),
            attempt: 2,
        }),
        wal_runtime_layer::journal_view(state) == a1_failure_records(),
    ensures
        wal_runtime_layer::runtime_record_enabled(
            cfg, state, a1_unknown_record(),
        ),
{
    let request = ensure_member_request_zero();
    let erased = config_layer::erase_config(cfg);
    let journal = a1_failure_records();
    ensure_member_full_config_is_well_formed();
    assert(journal =~= Seq::empty()
        .push(ensure_member_authorize_record())
        .push(ensure_member_prepare_record())
        .push(ensure_member_arm_record())
        .push(ensure_member_start_record())
        .push(a1_start_two_record())
        .push(a1_failure_outcome_record()));
    reveal_with_fuel(replay_layer::replay, 10);
    reveal_with_fuel(replay_layer::started_count, 10);
    reveal_with_fuel(replay_layer::outcome_count, 10);
    reveal_with_fuel(replay_layer::outcome_observation, 10);
    reveal_with_fuel(replay_layer::outcome_lsn, 10);
    assert(replay_layer::replay(erased, journal).phase[request]
        == replay_layer::Phase::Armed);
    assert(replay_layer::started_count(journal, request) == 2);
    assert(replay_layer::outcome_count(journal, request, 1) == 0);
    query_layer::outcome_count_zero_implies_no_observation(
        journal, request, 1,
    );
    assert(replay_layer::outcome_observation(journal, request, 1)
        == Option::None);
    assert(replay_layer::outcome_observation(journal, request, 2)
        == Option::Some(replay_layer::Observation::Failure));
    assert(!replay_layer::all_attempts_failed(journal, request)) by {
        if replay_layer::all_attempts_failed(journal, request) {
            assert(replay_layer::outcome_observation(journal, request, 1)
                == Option::Some(replay_layer::Observation::Failure));
            assert(false);
        }
    }
    assert(erased.request_class[request]
        == replay_layer::RetryClass::Idempotent);
    assert(!replay_layer::failure_conclusive(erased, journal, request));
    assert(replay_layer::outcome_lsn(journal, request, 2)
        == Option::Some(6));
    assert(replay_layer::latest_evidence_lsn(journal, request)
        == Option::Some(6));
    assert(replay_layer::request_fields_match(
        erased,
        request,
        replay_layer::Digest { id: 0 },
        Option::None,
    ));
    assert(replay_layer::unknown_enabled(
        erased,
        journal,
        request,
        Option::Some(2),
        replay_layer::UnknownReason::NonConclusiveFailure,
        6,
    ));
    assert(replay_layer::structural_enabled(
        erased, journal, a1_unknown_record(),
    ));
    assert(record_layer::durable_slot_update(
        erased,
        replay_layer::replay(erased, journal),
        record_layer::Mode::Online,
        record_layer::ExecSlot::ObservedFailure {
            request,
            attempt: 2,
        },
        a1_unknown_record(),
    ).is_some());
}

pub proof fn a1_retry_wal_execution_exec()
    ensures
        wal_runtime_layer::exec(
            ensure_member_full_config(), a1_retry_wal_execution(),
        ),
        a1_retry_wal_execution().events.len() == 31,
        a1_retry_wal_execution().configs.len() == 32,
        a1_retry_wal_execution().configs.last().runtime.mode
            == record_layer::Mode::Online,
        a1_retry_wal_execution().configs.last().runtime.slot
            == record_layer::ExecSlot::Idle,
        wal_runtime_layer::wal_quiescent(
            a1_retry_wal_execution().configs.last(),
        ),
        wal_runtime_layer::journal_view(
            a1_retry_wal_execution().configs.last(),
        ) == a1_retry_records(),
        a1_retry_wal_execution().configs.last().runtime.store.media
            == wal_runtime_layer::full_frames(a1_retry_records()),
        a1_retry_wal_execution().configs.last().evidence.records
            == a1_retry_records(),
        a1_retry_wal_execution().configs.last()
            .evidence.acknowledged_prefix == a1_retry_records(),
        a1_retry_wal_execution().configs.last().evidence.physical
            == a1_retry_history(),
{
    let cfg = ensure_member_full_config();
    let e16 = a1_wal_failure_outcome_execution();
    a1_wal_failure_outcome_execution_exec();
    a1_unknown_runtime_enabled(cfg, e16.configs.last());
    t6_a0_append_full_wal_execution_exec(
        cfg, e16, a1_unknown_record(),
    );
    let e17 = a1_retry_wal_execution();
    assert(e17.configs.last().runtime.slot
        == record_layer::ExecSlot::Idle);
    assert(wal_runtime_layer::journal_view(e17.configs.last())
        == a1_retry_records());
    assert(e17.configs.last().runtime.store.media
        == wal_runtime_layer::full_frames(a1_retry_records()));
    assert(e17.configs.last().evidence.records == a1_retry_records());
    assert(e17.configs.last().evidence.acknowledged_prefix
        == a1_retry_records());
    assert(e17.configs.last().evidence.physical == a1_retry_history());
    assert(e17.events.len() == 31);
    assert(e17.configs.len() == 32);
}

pub proof fn a1_retry_records_select_terminal_unknown()
    ensures
        terminal_from_records(
            a1_retry_records(), ensure_member_request_zero(),
        ) == Option::Some(a1_retry_outcome()),
{
    reveal_with_fuel(replay_layer::terminal_count, 10);
    reveal_with_fuel(latest_terminal_record, 10);
}

pub proof fn a1_retry_wal_trace_shape()
    ensures
        projection_layer::pi_journal(
            a1_retry_wal_execution().events,
        ) == a1_retry_records(),
        projection_layer::pi_physical(
            a1_retry_wal_execution().events,
        ) == a1_retry_history(),
        projection_layer::pi_adapter(
            a1_retry_wal_execution().events,
            ensure_member_request_zero(),
        ) == a1_retry_history(),
        terminal(
            a1_retry_wal_execution().events,
            ensure_member_request_zero(),
        ) == Option::Some(a1_retry_outcome()),
{
    let cfg = ensure_member_full_config();
    let source = a1_retry_wal_execution();
    let length = source.events.len();
    let final_state = source.configs[length as int];
    a1_retry_wal_execution_exec();
    wal_trace_layer::trace_agreement_for_exec(cfg, source);
    assert(wal_trace_layer::trace_agreement_at(cfg, source, length));
    assert(wal_trace_layer::prefix_events(source, length)
        == source.events);
    assert(final_state.evidence.records
        == projection_layer::pi_journal(source.events));
    assert(final_state.evidence.physical
        == projection_layer::pi_physical(source.events));
    assert(projection_layer::pi_journal(source.events)
        == a1_retry_records());
    assert(projection_layer::pi_physical(source.events)
        == a1_retry_history());
    reveal_with_fuel(projection_layer::adapter_from_physical, 6);
    assert(projection_layer::pi_adapter(
        source.events, ensure_member_request_zero(),
    ) == a1_retry_history());
    a1_retry_records_select_terminal_unknown();
}

pub proof fn a1_retry_has_explicit_crash_recovery_shape()
    ensures a1_explicit_crash_retry_trace_shape(
        a1_retry_wal_execution().events,
    ),
{
    let cfg = ensure_member_full_config();
    let e6 = a1_wal_pre_crash_execution();
    a1_wal_pre_crash_execution_exec();
    assert(e6.events.len() == 14);

    let e7 = t6_a0_extend_wal_execution(
        cfg, e6, wal_runtime_layer::WalEvent::Crash,
    );
    assert(e7.events == e6.events.push(
        global_layer::GlobalEvent::Crash,
    ));
    let e8 = t6_a0_extend_wal_execution(
        cfg, e7, wal_runtime_layer::WalEvent::BeginScan,
    );
    assert(e8.events == e7.events.push(
        global_layer::GlobalEvent::BeginScan,
    ));
    let e9 = t6_a0_extend_wal_execution(
        cfg, e8, wal_runtime_layer::WalEvent::FinishScan,
    );
    assert(e9.events == e8.events.push(
        global_layer::GlobalEvent::FinishScan,
    ));
    let e10 = t6_a0_extend_wal_execution(
        cfg, e9, wal_runtime_layer::WalEvent::TruncateTail,
    );
    assert(e10.events == e9.events.push(
        global_layer::GlobalEvent::TruncateTail,
    ));
    let e11 = t6_a0_extend_wal_execution(
        cfg, e10, wal_runtime_layer::WalEvent::BeginRecover,
    );
    assert(e11.events == e10.events.push(
        global_layer::GlobalEvent::BeginRecover,
    ));
    let e12 = t6_a0_extend_wal_execution(
        cfg, e11, wal_runtime_layer::WalEvent::FinishRecover,
    );
    assert(e12.events == e11.events.push(
        global_layer::GlobalEvent::FinishRecover,
    ));
    assert(e12 == a1_wal_recovered_execution());
    a1_wal_recovered_execution_exec();
    assert(wal_runtime_layer::journal_view(e12.configs.last()).len() == 4);

    let start2 = a1_start_two_record();
    let e13 = t6_a0_append_full_wal_execution(cfg, e12, start2);
    assert(e13.events == e12.events
        .push(global_layer::GlobalEvent::WalStage { record: start2 })
        .push(global_layer::GlobalEvent::WalWriteFull { record: start2 })
        .push(global_layer::GlobalEvent::WalFlushAck { cut: 5 }));
    let invoke2 = a1_invoke_two_wal_event();
    let e14 = t6_a0_extend_wal_execution(cfg, e13, invoke2);
    assert(e14.events == e13.events.push(
        wal_runtime_layer::wal_encode(invoke2),
    ));
    let failure2 = a1_failure_two_wal_event();
    let e15 = t6_a0_extend_wal_execution(cfg, e14, failure2);
    assert(e15.events == e14.events.push(
        wal_runtime_layer::wal_encode(failure2),
    ));
    assert(e15 == a1_wal_retry_observed_execution());

    let e16 = t6_a0_append_full_wal_execution(
        cfg, e15, a1_failure_outcome_record(),
    );
    assert(e16 == a1_wal_failure_outcome_execution());
    let e17 = t6_a0_append_full_wal_execution(
        cfg, e16, a1_unknown_record(),
    );
    assert(e17 == a1_retry_wal_execution());
    a1_retry_wal_execution_exec();
    assert(a1_explicit_crash_retry_trace_shape(e17.events));
}

pub proof fn a1_retry_history_has_mixed_outcomes()
    ensures
        invoked(
            a1_retry_history(), ensure_member_request_zero(), 1,
        ),
        delivery(
            a1_retry_history(), ensure_member_request_zero(), 1,
        ) == Option::Some(replay_layer::Observation::Success(
            ensure_member_success_value(),
        )),
        delivery(
            a1_retry_history(), ensure_member_request_zero(), 2,
        ) == Option::Some(replay_layer::Observation::Failure),
        !all_invocations_failed(
            a1_retry_history(), ensure_member_request_zero(),
        ),
{
    let history = a1_retry_history();
    let request = ensure_member_request_zero();
    reveal_with_fuel(p1_layer::invoke_count, 6);
    reveal_with_fuel(p1_layer::delivery_count, 6);
    reveal_with_fuel(latest_delivery_observation, 6);
    assert(invoked(history, request, 1));
    assert(delivery(history, request, 1)
        == Option::Some(replay_layer::Observation::Success(
            ensure_member_success_value(),
        )));
    assert(delivery(history, request, 2)
        == Option::Some(replay_layer::Observation::Failure));
    if all_invocations_failed(history, request) {
        assert(delivery(history, request, 1)
            == Option::Some(replay_layer::Observation::Failure));
        assert(false);
    }
}

pub proof fn a1_retry_terminal_is_not_fail()
    ensures
        terminal(
            a1_retry_wal_execution().events,
            ensure_member_request_zero(),
        ) == Option::Some(a1_retry_outcome()),
        forall|attempt: replay_layer::AttemptId|
            terminal(
                a1_retry_wal_execution().events,
                ensure_member_request_zero(),
            ) != Option::Some(TerminalOutcome::Fail { attempt }),
        !all_invocations_failed(
            a1_retry_history(), ensure_member_request_zero(),
        ),
{
    a1_retry_wal_trace_shape();
    a1_retry_history_has_mixed_outcomes();
    assert forall|attempt: replay_layer::AttemptId|
        terminal(
            a1_retry_wal_execution().events,
            ensure_member_request_zero(),
        ) != Option::Some(TerminalOutcome::Fail { attempt }) by {
    }
}

proof fn a1_retry_adapter_execution_core()
    ensures
        a1_exec(
            ensure_member_request_zero(),
            ISet::empty(),
            a1_retry_adapter_execution(),
        ),
        a1_retry_adapter_execution().configs.last().history
            == a1_retry_history(),
        a1_retry_adapter_execution().configs.last()
            .linearized_attempts.contains(1),
        !a1_retry_adapter_execution().configs.last()
            .linearized_attempts.contains(2),
        a1_global_trace(a1_retry_adapter_execution().events)
            == a1_retry_wal_execution().events,
        a1_retry_adapter_execution().events.len() == 32,
{
    let request = ensure_member_request_zero();
    let initial = ISet::<config_layer::Resource>::empty();
    let cfg = ensure_member_full_config();
    let w15 = a1_wal_retry_observed_execution();
    let a11 = a1_adapter_retry_observed_execution();
    a1_adapter_retry_observed_execution_exec();
    let cut6 = wal_runtime_layer::journal_view(w15.configs.last()).len() + 1;
    let a12 = a1_observe_full_append(
        a11, a1_failure_outcome_record(), cut6,
    );
    a1_observe_full_append_exec(
        request, initial, a11, a1_failure_outcome_record(), cut6,
    );
    let w16 = t6_a0_append_full_wal_execution(
        cfg, w15, a1_failure_outcome_record(),
    );
    let cut7 = wal_runtime_layer::journal_view(w16.configs.last()).len() + 1;
    let a13 = a1_observe_full_append(a12, a1_unknown_record(), cut7);
    a1_observe_full_append_exec(
        request, initial, a12, a1_unknown_record(), cut7,
    );
    assert(a13 == a1_retry_adapter_execution());
    assert(a13.configs.last().history == a1_retry_history());
    assert(a13.configs.last().linearized_attempts.contains(1));
    assert(!a13.configs.last().linearized_attempts.contains(2));
    assert(a1_global_trace(a13.events)
        == a1_retry_wal_execution().events);
}

proof fn a1_retry_adapter_trace_shape()
    ensures
        a1_global_trace(a1_retry_adapter_execution().events)
            == a1_retry_wal_execution().events,
        a1_retry_adapter_execution().events.len() == 32,
        a1_global_trace(a1_retry_adapter_execution().events).len() == 31,
{
    a1_retry_adapter_execution_core();
    assert(a1_retry_wal_execution().events.len() == 31);
}

proof fn a1_retry_adapter_effect_is_one()
    ensures
        (ensure_member_adapter().one_effect)(
            ensure_member_request_zero(),
            a1_external_run(
                a1_retry_adapter_execution().configs.last(),
            ),
        ),
        !(ensure_member_adapter().zero_effect)(
            ensure_member_request_zero(),
            a1_external_run(
                a1_retry_adapter_execution().configs.last(),
            ),
        ),
{
    let request = ensure_member_request_zero();
    let initial = ISet::<config_layer::Resource>::empty();
    let execution = a1_retry_adapter_execution();
    a1_retry_adapter_execution_core();
    assert(execution.configs.last().linearized_attempts.contains(1));
    a1_every_exec_configuration_satisfies_invariant(
        request, initial, execution,
    );
    let final_state = execution.configs.last();
    assert(final_state
        == execution.configs[execution.events.len() as int]);
    assert(a1_execution_invariant(request, initial, final_state));
    assert(a1_machine_invariant(final_state));
    assert(final_state.linearized_attempts.contains(1));
    assert(a1_has_linearization(final_state)) by {
        assert(final_state.linearized_attempts.contains(1));
    }
    assert(final_state.members.contains(ensure_member_target(request)));
    assert(!final_state.initial_members.contains(
        ensure_member_target(request),
    ));
    assert(!final_state.environment_additions.contains(
        ensure_member_target(request),
    ));
    let run = a1_external_run(final_state);
    assert(ensure_member_one_effect(request, run));
    if ensure_member_zero_effect(request, run) {
        assert(run.post.contains(ensure_member_target(request)));
        assert(!ensure_member_baseline_contains(
            run, ensure_member_target(request),
        ));
        assert(false);
    }
}

pub proof fn a1_retry_adapter_execution_exec()
    ensures
        a1_exec(
            ensure_member_request_zero(),
            ISet::empty(),
            a1_retry_adapter_execution(),
        ),
        a1_global_trace(a1_retry_adapter_execution().events)
            == a1_retry_wal_execution().events,
        a1_retry_adapter_execution().configs.last().history
            == a1_retry_history(),
        a1_retry_adapter_execution().configs.last()
            .linearized_attempts.contains(1),
        !a1_retry_adapter_execution().configs.last()
            .linearized_attempts.contains(2),
        a1_retry_adapter_execution().events.len() == 32,
        a1_global_trace(a1_retry_adapter_execution().events).len() == 31,
        (ensure_member_adapter().one_effect)(
            ensure_member_request_zero(),
            a1_external_run(
                a1_retry_adapter_execution().configs.last(),
            ),
        ),
        !(ensure_member_adapter().zero_effect)(
            ensure_member_request_zero(),
            a1_external_run(
                a1_retry_adapter_execution().configs.last(),
            ),
        ),
{
    a1_retry_adapter_execution_core();
    a1_retry_adapter_trace_shape();
    a1_retry_adapter_effect_is_one();
}

pub proof fn t6_a1_executable_crash_retry_refines()
    ensures
        adapter_rely(
            ensure_member_paper(),
            a1_retry_wal_execution().events,
            ensure_member_request_zero(),
            a1_retry_run(),
        ),
        refines(
            ensure_member_paper(),
            ensure_member_request_zero(),
            projection_layer::pi_adapter(
                a1_retry_wal_execution().events,
                ensure_member_request_zero(),
            ),
            a1_retry_run(),
            a1_retry_outcome(),
        ),
        per_request_effect_refinement(
            ensure_member_paper(),
            a1_retry_wal_execution().events,
            ensure_member_request_zero(),
            a1_retry_run(),
        ),
        (ensure_member_adapter().one_effect)(
            ensure_member_request_zero(), a1_retry_run(),
        ),
        !(ensure_member_adapter().zero_effect)(
            ensure_member_request_zero(), a1_retry_run(),
        ),
        terminal(
            a1_retry_wal_execution().events,
            ensure_member_request_zero(),
        ) == Option::Some(a1_retry_outcome()),
        !all_invocations_failed(
            a1_retry_history(), ensure_member_request_zero(),
        ),
{
    let request = ensure_member_request_zero();
    let adapter_execution = a1_retry_adapter_execution();
    let wal_execution = a1_retry_wal_execution();
    let outcome = a1_retry_outcome();
    a1_retry_adapter_execution_exec();
    a1_retry_wal_execution_exec();
    a1_retry_terminal_is_not_fail();
    assert(adapter_execution.configs.last()
        == adapter_execution.configs[
            adapter_execution.events.len() as int
        ]);
    assert(a1_retry_run() == a1_external_run(
        adapter_execution.configs[
            adapter_execution.events.len() as int
        ],
    ));
    ensure_member_executable_wal_terminal_refines(
        request,
        ISet::<config_layer::Resource>::empty(),
        adapter_execution,
        wal_execution,
        outcome,
    );
}

pub open spec fn a1_executable_retry_operational_package(
    adapter_execution: A1AdapterExecution,
    wal_execution: wal_runtime_layer::WalExecution,
    request: replay_layer::RequestId,
    run: ExternalRun<
        ISet<config_layer::Resource>, EnsureMemberWitness,
    >,
    outcome: TerminalOutcome,
) -> bool {
    let cfg = ensure_member_full_config();
    let final_adapter = adapter_execution.configs.last();
    let final_wal = wal_execution.configs.last();
    &&& a1_exec(request, ISet::empty(), adapter_execution)
    &&& a1_global_trace(adapter_execution.events)
        == wal_execution.events
    &&& run == a1_external_run(final_adapter)
    &&& wal_runtime_layer::exec(cfg, wal_execution)
    &&& wal_trace_layer::admissible_wal_trace(cfg, wal_execution)
    &&& wal_trace_layer::trace_agreement(cfg, wal_execution)
    &&& adapter_execution.events.len() == 32
    &&& a1_global_trace(adapter_execution.events).len() == 31
    &&& wal_execution.events.len() == 31
    &&& wal_execution.configs.len() == 32
    &&& projection_layer::pi_adapter(
        wal_execution.events, request,
    ) == a1_retry_history()
    &&& final_adapter.history == a1_retry_history()
    &&& final_adapter.linearized_attempts.contains(1)
    &&& !final_adapter.linearized_attempts.contains(2)
    &&& final_wal.evidence.records == a1_retry_records()
    &&& final_wal.evidence.physical == a1_retry_history()
    &&& outcome == a1_retry_outcome()
}

pub open spec fn a1_executable_retry_semantic_package(
    wal_execution: wal_runtime_layer::WalExecution,
    request: replay_layer::RequestId,
    run: ExternalRun<
        ISet<config_layer::Resource>, EnsureMemberWitness,
    >,
    outcome: TerminalOutcome,
) -> bool {
    let paper = ensure_member_paper();
    &&& t1_layer::paper_config_wf(paper)
    &&& adapter_verified(paper)
    &&& adapter_rely(paper, wal_execution.events, request, run)
    &&& terminal(wal_execution.events, request)
        == Option::Some(outcome)
    &&& refines(
        paper,
        request,
        projection_layer::pi_adapter(wal_execution.events, request),
        run,
        outcome,
    )
    &&& per_request_effect_refinement(
        paper, wal_execution.events, request, run,
    )
    &&& (paper.adapter.one_effect)(request, run)
    &&& !(paper.adapter.zero_effect)(request, run)
    &&& !all_invocations_failed(a1_retry_history(), request)
}

pub open spec fn a1_executable_retry_package(
    adapter_execution: A1AdapterExecution,
    wal_execution: wal_runtime_layer::WalExecution,
    request: replay_layer::RequestId,
    run: ExternalRun<
        ISet<config_layer::Resource>, EnsureMemberWitness,
    >,
    outcome: TerminalOutcome,
) -> bool {
    a1_executable_retry_operational_package(
        adapter_execution, wal_execution, request, run, outcome,
    ) && a1_executable_retry_semantic_package(
        wal_execution, request, run, outcome,
    )
}

proof fn a1_concrete_executable_retry_operational_package()
    ensures
        a1_executable_retry_operational_package(
            a1_retry_adapter_execution(),
            a1_retry_wal_execution(),
            ensure_member_request_zero(),
            a1_retry_run(),
            a1_retry_outcome(),
        ),
{
    let cfg = ensure_member_full_config();
    let adapter_execution = a1_retry_adapter_execution();
    let wal_execution = a1_retry_wal_execution();
    let run = a1_retry_run();
    ensure_member_full_config_is_well_formed();
    a1_retry_adapter_execution_exec();
    a1_retry_wal_execution_exec();
    a1_retry_wal_trace_shape();
    wal_trace_layer::exec_implies_admissible_wal_trace(
        cfg, wal_execution,
    );
    wal_trace_layer::trace_agreement_for_exec(cfg, wal_execution);
    assert(run == a1_external_run(adapter_execution.configs.last()));
    assert(adapter_execution.configs.last().history
        == a1_retry_history());
    assert(adapter_execution.configs.last()
        .linearized_attempts.contains(1));
    assert(!adapter_execution.configs.last()
        .linearized_attempts.contains(2));
    assert(wal_execution.configs.last().evidence.records
        == a1_retry_records());
    assert(wal_execution.configs.last().evidence.physical
        == a1_retry_history());
}

proof fn a1_concrete_executable_retry_semantic_package()
    ensures
        a1_executable_retry_semantic_package(
            a1_retry_wal_execution(),
            ensure_member_request_zero(),
            a1_retry_run(),
            a1_retry_outcome(),
        ),
{
    ensure_member_full_config_is_well_formed();
    ensure_member_adapter_is_verified();
    a1_retry_history_has_mixed_outcomes();
    t6_a1_executable_crash_retry_refines();
}

pub proof fn a1_concrete_executable_retry_package()
    ensures
        a1_executable_retry_package(
            a1_retry_adapter_execution(),
            a1_retry_wal_execution(),
            ensure_member_request_zero(),
            a1_retry_run(),
            a1_retry_outcome(),
        ),
{
    a1_concrete_executable_retry_operational_package();
    a1_concrete_executable_retry_semantic_package();
}

pub proof fn t6_a1_executable_crash_retry_nonvacuity()
    ensures
        exists|
            adapter_execution: A1AdapterExecution,
            wal_execution: wal_runtime_layer::WalExecution,
            request: replay_layer::RequestId,
            run: ExternalRun<
                ISet<config_layer::Resource>, EnsureMemberWitness,
            >,
            outcome: TerminalOutcome| #![auto] {
                &&& adapter_execution == a1_retry_adapter_execution()
                &&& wal_execution == a1_retry_wal_execution()
                &&& request == ensure_member_request_zero()
                &&& run == a1_retry_run()
                &&& outcome == a1_retry_outcome()
                &&& a1_executable_retry_package(
                    adapter_execution,
                    wal_execution,
                    request,
                    run,
                    outcome,
                )
            },
{
    a1_concrete_executable_retry_package();
    assert(exists|
        adapter_execution: A1AdapterExecution,
        wal_execution: wal_runtime_layer::WalExecution,
        request: replay_layer::RequestId,
        run: ExternalRun<
            ISet<config_layer::Resource>, EnsureMemberWitness,
        >,
        outcome: TerminalOutcome| #![auto] {
            &&& adapter_execution == a1_retry_adapter_execution()
            &&& wal_execution == a1_retry_wal_execution()
            &&& request == ensure_member_request_zero()
            &&& run == a1_retry_run()
            &&& outcome == a1_retry_outcome()
            &&& a1_executable_retry_package(
                adapter_execution,
                wal_execution,
                request,
                run,
                outcome,
            )
        }) by {
        let adapter_execution = a1_retry_adapter_execution();
        let wal_execution = a1_retry_wal_execution();
        let request = ensure_member_request_zero();
        let run = a1_retry_run();
        let outcome = a1_retry_outcome();
    }
}

} // verus!
