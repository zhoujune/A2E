use vstd::prelude::*;

#[path = "t6_readonly_operational.rs"]
pub mod t6_ro0_layer;

verus! {

use t6_ro0_layer::*;
use t6_ro0_layer::t6_x0_layer;
use t6_x0_layer::*;
use t6_x0_layer::t6_p0_layer;
use t6_p0_layer::t6_m0_layer;
use t6_m0_layer::*;
use t6_m0_layer::t6_a1_layer;
use t6_a1_layer::*;
use t6_a1_layer::t6_a0_layer;
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
use c1_layer::append_layer;
use c1_layer::replay_layer;

// T6-DD0 is the third executable adapter instance, for the Deduplicated
// retry class.  The protected target is a service-owned keyed slot.  The
// service decides each stable key at most once: a silent ServiceDecide
// linearization either applies the keyed mutation and memoizes the applied
// value, or rejects the key and memoizes the rejection.  Every subsequent
// delivery for the request replays the memoized decision, so a retried
// attempt that arrives after the decision receives the same Success value
// that the deciding attempt produced.  This is the mechanism that lets the
// adapter DERIVE `deduplicated_observations_consistent` and the
// `dedup_service_law` from its transition invariant, rather than assuming
// them: at most one decision record can ever exist, Success deliveries are
// enabled only against an Applied memo, and Failure deliveries only against
// a Rejected memo, so no execution can deliver contradictory outcomes.
// Transport uncertainty is not modeled as a service reply: an attempt whose
// outcome never arrives simply delivers nothing, and the Broker-side Unknown
// machinery covers it.
//
// MILESTONE 1 (this revision): adapter interpretation, configuration and its
// well-formedness proof, and the operational machine definitions.
// MILESTONE 2 adds the inductive invariant, its preservation proofs, and the
// AdapterRely derivation.  MILESTONE 3 adds the coupled crash/retry witness
// (Invoke 1, silent decide, crash before any outcome is journaled, recovery,
// retry, memoized Success delivery, Commit) and the terminal-refinement and
// nonvacuity package theorems.

#[allow(inconsistent_fields)]
#[derive(PartialEq, Eq)]
pub enum DDDecision {
    Applied { value: replay_layer::Value },
    Rejected,
}

pub struct DDDecisionRecord {
    pub attempt: replay_layer::AttemptId,
    pub decision: DDDecision,
    // Physical-history prefix at which the service decision linearized.
    // This witnesses Invoke < ServiceDecide < any memoized Delivered
    // without exposing the silent service action as a Broker/WAL label.
    pub history_cut: nat,
}

pub struct DedupWitness {
    pub decisions: Seq<DDDecisionRecord>,
}

pub open spec fn dd_has_applied(
    decisions: Seq<DDDecisionRecord>,
    value: replay_layer::Value,
) -> bool {
    exists|index: int| 0 <= index < decisions.len()
        && #[trigger] decisions[index].decision
            == (DDDecision::Applied { value })
}

pub open spec fn dd_has_any_applied(
    decisions: Seq<DDDecisionRecord>,
) -> bool {
    exists|index: int| 0 <= index < decisions.len()
        && (#[trigger] decisions[index].decision) is Applied
}

pub open spec fn dd_has_rejected(
    decisions: Seq<DDDecisionRecord>,
) -> bool {
    exists|index: int| 0 <= index < decisions.len()
        && #[trigger] decisions[index].decision == DDDecision::Rejected
}

// Memoization: the service decides a stable key at most once, ever.
pub open spec fn dd_decisions_well_formed(
    decisions: Seq<DDDecisionRecord>,
) -> bool {
    &&& decisions.len() <= 1
    &&& forall|index: int| 0 <= index < decisions.len() ==>
        #[trigger] decisions[index].attempt > 0
}

pub open spec fn dd_decisions_have_history_provenance(
    history: Seq<p0_layer::PhysicalEvent>,
    request: replay_layer::RequestId,
    decisions: Seq<DDDecisionRecord>,
) -> bool {
    forall|index: int| 0 <= index < decisions.len() ==> {
        let record = #[trigger] decisions[index];
        &&& record.history_cut <= history.len()
        &&& invoked(
            history.take(record.history_cut as int),
            request,
            record.attempt,
        )
        &&& p1_layer::delivery_count(
            history.take(record.history_cut as int),
            request,
            record.attempt,
        ) == 0
    }
}

// The keyed slot after the run is exactly the initial slot plus the single
// applied decision, if any.  Rejection memoizes an answer without mutating
// the slot.
pub open spec fn dd_post_state_factored(
    run: ExternalRun<Option<replay_layer::Value>, DedupWitness>,
) -> bool {
    if dd_has_any_applied(run.interference.decisions) {
        exists|value: replay_layer::Value| {
            &&& #[trigger] dd_has_applied(run.interference.decisions, value)
            &&& run.post == Option::<replay_layer::Value>::Some(value)
        }
    } else {
        run.post == run.pre
    }
}

pub open spec fn dd_zero_effect(
    _request: replay_layer::RequestId,
    run: ExternalRun<Option<replay_layer::Value>, DedupWitness>,
) -> bool {
    &&& !dd_has_any_applied(run.interference.decisions)
    &&& run.post == run.pre
}

pub open spec fn dd_one_effect(
    _request: replay_layer::RequestId,
    run: ExternalRun<Option<replay_layer::Value>, DedupWitness>,
) -> bool {
    exists|value: replay_layer::Value| {
        &&& #[trigger] dd_has_applied(run.interference.decisions, value)
        &&& run.post == Option::<replay_layer::Value>::Some(value)
    }
}

pub open spec fn dd_env_rely(
    request: replay_layer::RequestId,
    history: Seq<p0_layer::PhysicalEvent>,
    run: ExternalRun<Option<replay_layer::Value>, DedupWitness>,
) -> bool {
    &&& dd_decisions_well_formed(run.interference.decisions)
    &&& dd_decisions_have_history_provenance(
        history, request, run.interference.decisions,
    )
    &&& dd_post_state_factored(run)
}

pub open spec fn dd_classification_ok(
    _request: replay_layer::RequestId,
    _attempt: replay_layer::AttemptId,
    observation: replay_layer::Observation,
    run: ExternalRun<Option<replay_layer::Value>, DedupWitness>,
) -> bool {
    match observation {
        replay_layer::Observation::Success(value) => {
            dd_has_applied(run.interference.decisions, value)
        },
        replay_layer::Observation::Failure => {
            dd_has_rejected(run.interference.decisions)
        },
        replay_layer::Observation::Ambiguous
        | replay_layer::Observation::InvalidResult(_) => false,
    }
}

pub open spec fn dd_result_spec(
    _request: replay_layer::RequestId,
    value: replay_layer::Value,
    run: ExternalRun<Option<replay_layer::Value>, DedupWitness>,
) -> bool {
    dd_has_applied(run.interference.decisions, value)
}

// The history-level service law consumed by `adapter_class_law`: every
// delivered conclusive observation for the request replays the memoized
// decision.  Together with at-most-one-decision this is what makes the
// Deduplicated consistency conjuncts of `AdapterRely` derivable.
pub open spec fn dd_service_law(
    request: replay_layer::RequestId,
    _namespace: replay_layer::AdapterNamespace,
    _key: replay_layer::StableKey,
    history: Seq<p0_layer::PhysicalEvent>,
    run: ExternalRun<Option<replay_layer::Value>, DedupWitness>,
) -> bool {
    &&& dd_decisions_well_formed(run.interference.decisions)
    &&& forall|index: int| 0 <= index < history.len() ==>
        match #[trigger] history[index] {
            p0_layer::PhysicalEvent::Delivered {
                request: event_request, observation, ..
            } if event_request == request => match observation {
                replay_layer::Observation::Success(value) => {
                    dd_has_applied(run.interference.decisions, value)
                },
                replay_layer::Observation::Failure => {
                    dd_has_rejected(run.interference.decisions)
                },
                replay_layer::Observation::Ambiguous
                | replay_layer::Observation::InvalidResult(_) => false,
            },
            _ => true,
        }
}

pub open spec fn dd_adapter() -> Adapter<
    Option<replay_layer::Value>,
    DedupWitness,
> {
    Adapter {
        env_rely: |request, history, run|
            dd_env_rely(request, history, run),
        classification_ok: |request, attempt, observation, run|
            dd_classification_ok(request, attempt, observation, run),
        zero_effect: |request, run| dd_zero_effect(request, run),
        one_effect: |request, run| dd_one_effect(request, run),
        result_spec: |request, value, run|
            dd_result_spec(request, value, run),
        read_preserves: |_request, _run| false,
        idempotent_under_rely: |_request, _run| false,
        dedup_service_law: |request, namespace, key, history, run|
            dd_service_law(request, namespace, key, history, run),
    }
}

pub open spec fn dd_request_zero() -> replay_layer::RequestId {
    replay_layer::RequestId { id: 0 }
}

// Every request is Deduplicated.  The stable key is derived injectively
// from the request identity, which discharges the configuration
// well-formedness clause that distinct Deduplicated requests sharing a
// namespace must carry distinct keys.
pub open spec fn dd_request(
    request: replay_layer::RequestId,
) -> config_layer::Request {
    config_layer::Request {
        principal: config_layer::Principal { id: 0 },
        tool: config_layer::Tool { id: 0 },
        operation: config_layer::Operation { id: 0 },
        resource: config_layer::Resource { id: 0 },
        arguments: config_layer::Arguments { id: 0 },
        capability: replay_layer::CapabilityId { id: 0 },
        retry_class: replay_layer::RetryClass::Deduplicated,
        digest: replay_layer::Digest { id: 0 },
        adapter_namespace: replay_layer::AdapterNamespace { id: 0 },
        stable_key: Option::Some(replay_layer::StableKey { id: request.id }),
        max_attempts: 2,
    }
}

pub open spec fn dd_capability(
    _capability: replay_layer::CapabilityId,
) -> config_layer::Capability {
    config_layer::Capability {
        principal: config_layer::Principal { id: 0 },
        tool: config_layer::Tool { id: 0 },
        operation: config_layer::Operation { id: 0 },
        resources: ISet::<config_layer::Resource>::full(),
        arguments: ISet::<config_layer::Arguments>::full(),
        initial_budget: 1,
    }
}

pub open spec fn dd_full_config() -> config_layer::FullConfig {
    config_layer::FullConfig {
        request: IMap::new(
            |_request: replay_layer::RequestId| true,
            |request: replay_layer::RequestId| dd_request(request),
        ),
        capability: IMap::new(
            |_capability: replay_layer::CapabilityId| true,
            |capability: replay_layer::CapabilityId|
                dd_capability(capability),
        ),
        valid_results: ISet::new(
            |pair: (replay_layer::RequestId, replay_layer::Value)|
                pair.1.id == 0 || pair.1.id == 1,
        ),
    }
}

pub open spec fn dd_paper() -> t1_layer::PaperConfig<
    Adapter<Option<replay_layer::Value>, DedupWitness>,
> {
    t1_layer::PaperConfig {
        broker: dd_full_config(),
        adapter: dd_adapter(),
    }
}

pub proof fn dd_full_config_is_well_formed()
    ensures
        config_layer::full_config_wf(dd_full_config()),
        t1_layer::paper_config_wf(dd_paper()),
        forall|request: replay_layer::RequestId|
            #[trigger] dd_full_config().request[request].retry_class
                == replay_layer::RetryClass::Deduplicated,
        forall|request: replay_layer::RequestId|
            #[trigger] dd_full_config().request[request].stable_key
                == Option::Some(
                    replay_layer::StableKey { id: request.id },
                ),
        forall|request: replay_layer::RequestId|
            #[trigger] dd_full_config().request[request].max_attempts == 2,
{
    let cfg = dd_full_config();
    t1_layer::paper_broker_config_is_broker(dd_paper());
    assert(cfg.request.dom() == ISet::<replay_layer::RequestId>::full());
    assert(cfg.capability.dom()
        == ISet::<replay_layer::CapabilityId>::full());
    assert forall|request: replay_layer::RequestId|
        #[trigger] cfg.request[request].retry_class
            == replay_layer::RetryClass::Deduplicated by {
    }
    assert forall|request: replay_layer::RequestId|
        #[trigger] cfg.request[request].stable_key
            == Option::Some(
                replay_layer::StableKey { id: request.id },
            ) by {
    }
    assert forall|request: replay_layer::RequestId|
        #[trigger] cfg.request[request].max_attempts == 2 by {
    }
    assert forall|request: replay_layer::RequestId|
        #[trigger] cfg.request[request].max_attempts > 0 by {
    }
    assert forall|request: replay_layer::RequestId|
        (#[trigger] cfg.request[request].retry_class
                == replay_layer::RetryClass::Deduplicated
            <==> cfg.request[request].stable_key.is_some()) by {
    }
    assert forall|left: replay_layer::RequestId,
                  right: replay_layer::RequestId| #![auto]
        cfg.request[left].retry_class
                == replay_layer::RetryClass::Deduplicated
            && cfg.request[right].retry_class
                == replay_layer::RetryClass::Deduplicated
            && cfg.request[left].adapter_namespace
                == cfg.request[right].adapter_namespace
            && cfg.request[left].stable_key
                == cfg.request[right].stable_key
                ==> left == right by {
        if cfg.request[left].stable_key == cfg.request[right].stable_key {
            assert(cfg.request[left].stable_key
                == Option::Some(
                    replay_layer::StableKey { id: left.id },
                ));
            assert(cfg.request[right].stable_key
                == Option::Some(
                    replay_layer::StableKey { id: right.id },
                ));
            assert(left.id == right.id);
        }
    }
}

#[allow(inconsistent_fields)]
#[derive(PartialEq, Eq)]
pub enum DDAdapterMode {
    Online,
    Crashed,
    Recovering,
}

#[allow(inconsistent_fields)]
#[derive(PartialEq, Eq)]
pub enum DDAdapterEvent {
    Observe { event: global_layer::GlobalEvent },
    ServiceDecide { decision: DDDecision },
}

pub struct DDAdapterState {
    pub request: replay_layer::RequestId,
    pub initial_slot: Option<replay_layer::Value>,
    pub slot: Option<replay_layer::Value>,
    pub decisions: Seq<DDDecisionRecord>,
    pub failed_attempts: ISet<replay_layer::AttemptId>,
    pub globals: Seq<global_layer::GlobalEvent>,
    pub history: Seq<p0_layer::PhysicalEvent>,
    pub mode: DDAdapterMode,
    pub active: Option<replay_layer::AttemptId>,
}

pub struct DDAdapterExecution {
    pub configs: Seq<DDAdapterState>,
    pub events: Seq<DDAdapterEvent>,
}

pub open spec fn dd_initial_state(
    request: replay_layer::RequestId,
    initial_slot: Option<replay_layer::Value>,
) -> DDAdapterState {
    DDAdapterState {
        request,
        initial_slot,
        slot: initial_slot,
        decisions: Seq::empty(),
        failed_attempts: ISet::empty(),
        globals: Seq::empty(),
        history: Seq::empty(),
        mode: DDAdapterMode::Online,
        active: Option::None,
    }
}

pub open spec fn dd_external_run(
    state: DDAdapterState,
) -> ExternalRun<Option<replay_layer::Value>, DedupWitness> {
    ExternalRun {
        pre: state.initial_slot,
        post: state.slot,
        interference: DedupWitness { decisions: state.decisions },
    }
}

pub open spec fn dd_global_trace(
    events: Seq<DDAdapterEvent>,
) -> Seq<global_layer::GlobalEvent>
    decreases events.len()
{
    if events.len() == 0 {
        Seq::empty()
    } else {
        let prefix = dd_global_trace(events.drop_last());
        match events.last() {
            DDAdapterEvent::Observe { event } => prefix.push(event),
            DDAdapterEvent::ServiceDecide { .. } => prefix,
        }
    }
}

pub open spec fn dd_observe_enabled(
    state: DDAdapterState,
    event: global_layer::GlobalEvent,
) -> bool {
    let cfg = dd_full_config();
    let request = state.request;
    match event {
        global_layer::GlobalEvent::InvokeEvent {
            request: event_request, attempt, call, ..
        } if event_request == request => {
            &&& state.mode == DDAdapterMode::Online
            &&& state.active.is_none()
            &&& attempt > 0
            &&& attempt <= cfg.request[request].max_attempts
            &&& call == config_layer::canonical_call(cfg, request)
            &&& p1_layer::invoke_count(
                state.history, request, attempt,
            ) == 0
            &&& p1_layer::delivery_count(
                state.history, request, attempt,
            ) == 0
        },
        global_layer::GlobalEvent::DeliverEvent {
            request: event_request, attempt, observation, ..
        } if event_request == request => {
            &&& state.mode == DDAdapterMode::Online
            &&& state.active == Option::Some(attempt)
            &&& attempt > 0
            &&& p1_layer::delivery_count(
                state.history, request, attempt,
            ) == 0
            &&& match observation {
                replay_layer::Observation::Success(value) => {
                    dd_has_applied(state.decisions, value)
                },
                replay_layer::Observation::Failure => {
                    dd_has_rejected(state.decisions)
                },
                replay_layer::Observation::Ambiguous
                | replay_layer::Observation::InvalidResult(_) => false,
            }
        },
        global_layer::GlobalEvent::Crash => {
            state.mode != DDAdapterMode::Crashed
        },
        global_layer::GlobalEvent::BeginRecover => {
            state.mode == DDAdapterMode::Crashed
        },
        global_layer::GlobalEvent::FinishRecover => {
            state.mode == DDAdapterMode::Recovering
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

pub open spec fn dd_enabled(
    state: DDAdapterState,
    event: DDAdapterEvent,
) -> bool {
    match event {
        DDAdapterEvent::Observe { event } => dd_observe_enabled(state, event),
        DDAdapterEvent::ServiceDecide { decision } => {
            &&& state.mode == DDAdapterMode::Online
            &&& state.active.is_some()
            &&& invoked(
                state.history,
                state.request,
                state.active.unwrap(),
            )
            &&& p1_layer::delivery_count(
                state.history, state.request, state.active.unwrap(),
            ) == 0
            // Memoization: the key is decided at most once, ever.
            &&& state.decisions.len() == 0
            &&& match decision {
                DDDecision::Applied { value } => value.id == 1,
                DDDecision::Rejected => true,
            }
        },
    }
}

pub open spec fn dd_apply_observe(
    state: DDAdapterState,
    event: global_layer::GlobalEvent,
) -> DDAdapterState {
    let request = state.request;
    let globals = state.globals.push(event);
    let history = a1_history_after_global(state.history, event, request);
    match event {
        global_layer::GlobalEvent::InvokeEvent {
            request: event_request, attempt, ..
        } if event_request == request => DDAdapterState {
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
        } if event_request == request => DDAdapterState {
            failed_attempts: state.failed_attempts.insert(attempt),
            globals,
            history,
            active: Option::None,
            ..state
        },
        global_layer::GlobalEvent::DeliverEvent {
            request: event_request, ..
        } if event_request == request => DDAdapterState {
            globals,
            history,
            active: Option::None,
            ..state
        },
        global_layer::GlobalEvent::Crash => DDAdapterState {
            globals,
            mode: DDAdapterMode::Crashed,
            active: Option::None,
            ..state
        },
        global_layer::GlobalEvent::BeginRecover => DDAdapterState {
            globals,
            mode: DDAdapterMode::Recovering,
            ..state
        },
        global_layer::GlobalEvent::FinishRecover => DDAdapterState {
            globals,
            mode: DDAdapterMode::Online,
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
        | global_layer::GlobalEvent::AbortScan => DDAdapterState {
            globals,
            ..state
        },
    }
}

pub open spec fn dd_apply(
    state: DDAdapterState,
    event: DDAdapterEvent,
) -> DDAdapterState {
    match event {
        DDAdapterEvent::Observe { event } => dd_apply_observe(state, event),
        DDAdapterEvent::ServiceDecide { decision } => DDAdapterState {
            decisions: state.decisions.push(DDDecisionRecord {
                attempt: state.active.unwrap(),
                decision,
                history_cut: state.history.len(),
            }),
            slot: match decision {
                DDDecision::Applied { value } =>
                    Option::Some(value),
                DDDecision::Rejected => state.slot,
            },
            ..state
        },
    }
}

pub open spec fn dd_step(
    before: DDAdapterState,
    event: DDAdapterEvent,
    after: DDAdapterState,
) -> bool {
    dd_enabled(before, event) && after == dd_apply(before, event)
}

pub open spec fn dd_exec(
    request: replay_layer::RequestId,
    initial_slot: Option<replay_layer::Value>,
    execution: DDAdapterExecution,
) -> bool {
    execution.configs.len() == execution.events.len() + 1
        && execution.configs[0] == dd_initial_state(request, initial_slot)
        && forall|index: nat| index < execution.events.len() ==>
            #[trigger] dd_step(
                execution.configs[index as int],
                execution.events[index as int],
                execution.configs[(index + 1) as int],
            )
}

pub open spec fn dd_execution_prefix(
    execution: DDAdapterExecution,
    length: nat,
) -> DDAdapterExecution {
    DDAdapterExecution {
        configs: execution.configs.take((length + 1) as int),
        events: execution.events.take(length as int),
    }
}

} // verus!
