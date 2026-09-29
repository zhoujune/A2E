use vstd::prelude::*;

#[path = "t6_contextual_end_to_end.rs"]
pub mod t6_x0_layer;

verus! {

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

// T6-RO0 is a second executable adapter instance.  A read is linearized by
// sampling an environment-owned Boolean at an explicit environment-history
// cut.  Neither sampling nor retry changes that Boolean.  EnvironmentSet is
// the only transition that changes it, so zero_effect factors out exactly the
// environment transitions instead of treating an arbitrary post-state as a
// read-only execution.

#[derive(PartialEq, Eq)]
pub struct ROReadSample {
    pub attempt: replay_layer::AttemptId,
    pub present: bool,
    pub environment_cut: nat,
    // Physical-history prefix at which the remote read linearized.  This
    // witnesses Invoke < ServiceRead < Delivered without exposing the silent
    // service action as a Broker/WAL label.
    pub history_cut: nat,
}

pub struct ReadOnlyWitness {
    pub environment_updates: Seq<bool>,
    pub samples: Seq<ROReadSample>,
}

pub open spec fn ro_environment_value(
    initial: bool,
    updates: Seq<bool>,
) -> bool {
    if updates.len() == 0 { initial } else { updates.last() }
}

pub open spec fn ro_result_value(present: bool) -> replay_layer::Value {
    replay_layer::Value { id: if present { 1 } else { 0 } }
}

pub open spec fn ro_has_sample(
    samples: Seq<ROReadSample>,
    attempt: replay_layer::AttemptId,
) -> bool {
    exists|index: int| 0 <= index < samples.len()
        && #[trigger] samples[index].attempt == attempt
}

pub open spec fn ro_has_sample_value(
    samples: Seq<ROReadSample>,
    attempt: replay_layer::AttemptId,
    value: replay_layer::Value,
) -> bool {
    exists|index: int| 0 <= index < samples.len()
        && #[trigger] samples[index].attempt == attempt
        && value == ro_result_value(samples[index].present)
}

pub open spec fn ro_samples_well_formed(
    initial: bool,
    updates: Seq<bool>,
    samples: Seq<ROReadSample>,
) -> bool {
    &&& forall|index: int| 0 <= index < samples.len() ==> {
        let sample = #[trigger] samples[index];
        &&& sample.attempt > 0
        &&& sample.environment_cut <= updates.len()
        &&& sample.present == ro_environment_value(
            initial,
            updates.take(sample.environment_cut as int),
        )
    }
    &&& forall|left: int, right: int|
        0 <= left < samples.len() && 0 <= right < samples.len()
            && #[trigger] samples[left].attempt
                == #[trigger] samples[right].attempt
            ==> left == right
}

pub open spec fn ro_samples_have_history_provenance(
    history: Seq<p0_layer::PhysicalEvent>,
    request: replay_layer::RequestId,
    samples: Seq<ROReadSample>,
) -> bool {
    forall|index: int| 0 <= index < samples.len() ==> {
        let sample = #[trigger] samples[index];
        &&& sample.history_cut <= history.len()
        &&& invoked(
            history.take(sample.history_cut as int),
            request,
            sample.attempt,
        )
        &&& p1_layer::delivery_count(
            history.take(sample.history_cut as int),
            request,
            sample.attempt,
        ) == 0
    }
}

pub open spec fn ro_zero_effect(
    _request: replay_layer::RequestId,
    run: ExternalRun<bool, ReadOnlyWitness>,
) -> bool {
    run.post == ro_environment_value(
        run.pre, run.interference.environment_updates,
    )
}

pub open spec fn ro_one_effect(
    _request: replay_layer::RequestId,
    _run: ExternalRun<bool, ReadOnlyWitness>,
) -> bool {
    false
}

pub open spec fn ro_env_rely(
    request: replay_layer::RequestId,
    history: Seq<p0_layer::PhysicalEvent>,
    run: ExternalRun<bool, ReadOnlyWitness>,
) -> bool {
    &&& ro_zero_effect(request, run)
    &&& ro_samples_well_formed(
        run.pre,
        run.interference.environment_updates,
        run.interference.samples,
    )
    &&& ro_samples_have_history_provenance(
        history, request, run.interference.samples,
    )
}

pub open spec fn ro_classification_ok(
    _request: replay_layer::RequestId,
    attempt: replay_layer::AttemptId,
    observation: replay_layer::Observation,
    run: ExternalRun<bool, ReadOnlyWitness>,
) -> bool {
    match observation {
        replay_layer::Observation::Success(value) => {
            ro_has_sample_value(run.interference.samples, attempt, value)
        },
        replay_layer::Observation::Failure => {
            !ro_has_sample(run.interference.samples, attempt)
        },
        replay_layer::Observation::Ambiguous
        | replay_layer::Observation::InvalidResult(_) => false,
    }
}

pub open spec fn ro_result_spec(
    _request: replay_layer::RequestId,
    value: replay_layer::Value,
    run: ExternalRun<bool, ReadOnlyWitness>,
) -> bool {
    exists|index: int| 0 <= index < run.interference.samples.len()
        && value == ro_result_value(
            #[trigger] run.interference.samples[index].present,
        )
}

pub open spec fn ro_read_preserves(
    request: replay_layer::RequestId,
    run: ExternalRun<bool, ReadOnlyWitness>,
) -> bool {
    ro_zero_effect(request, run)
}

pub open spec fn ro_adapter() -> Adapter<bool, ReadOnlyWitness> {
    Adapter {
        env_rely: |request, history, run|
            ro_env_rely(request, history, run),
        classification_ok: |request, attempt, observation, run|
            ro_classification_ok(request, attempt, observation, run),
        zero_effect: |request, run| ro_zero_effect(request, run),
        one_effect: |request, run| ro_one_effect(request, run),
        result_spec: |request, value, run|
            ro_result_spec(request, value, run),
        read_preserves: |request, run|
            ro_read_preserves(request, run),
        idempotent_under_rely: |_request, _run| false,
        dedup_service_law:
            |_request, _namespace, _key, _history, _run| false,
    }
}

pub open spec fn ro_request_zero() -> replay_layer::RequestId {
    replay_layer::RequestId { id: 0 }
}

pub open spec fn ro_request(
    _request: replay_layer::RequestId,
) -> config_layer::Request {
    config_layer::Request {
        principal: config_layer::Principal { id: 0 },
        tool: config_layer::Tool { id: 0 },
        operation: config_layer::Operation { id: 0 },
        resource: config_layer::Resource { id: 0 },
        arguments: config_layer::Arguments { id: 0 },
        capability: replay_layer::CapabilityId { id: 0 },
        retry_class: replay_layer::RetryClass::ReadOnly,
        digest: replay_layer::Digest { id: 0 },
        adapter_namespace: replay_layer::AdapterNamespace { id: 0 },
        stable_key: Option::None,
        max_attempts: 2,
    }
}

pub open spec fn ro_capability(
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

pub open spec fn ro_full_config() -> config_layer::FullConfig {
    config_layer::FullConfig {
        request: IMap::new(
            |_request: replay_layer::RequestId| true,
            |request: replay_layer::RequestId| ro_request(request),
        ),
        capability: IMap::new(
            |_capability: replay_layer::CapabilityId| true,
            |capability: replay_layer::CapabilityId|
                ro_capability(capability),
        ),
        valid_results: ISet::new(
            |pair: (replay_layer::RequestId, replay_layer::Value)|
                pair.1.id == 0 || pair.1.id == 1,
        ),
    }
}

pub open spec fn ro_paper() -> t1_layer::PaperConfig<
    Adapter<bool, ReadOnlyWitness>,
> {
    t1_layer::PaperConfig {
        broker: ro_full_config(),
        adapter: ro_adapter(),
    }
}

pub proof fn ro_full_config_is_well_formed()
    ensures
        config_layer::full_config_wf(ro_full_config()),
        t1_layer::paper_config_wf(ro_paper()),
        forall|request: replay_layer::RequestId|
            #[trigger] ro_full_config().request[request].retry_class
                == replay_layer::RetryClass::ReadOnly,
        forall|request: replay_layer::RequestId|
            #[trigger] ro_full_config().request[request].stable_key
                == Option::None,
        forall|request: replay_layer::RequestId|
            #[trigger] ro_full_config().request[request].max_attempts == 2,
{
    let cfg = ro_full_config();
    t1_layer::paper_broker_config_is_broker(ro_paper());
    assert(cfg.request.dom() == ISet::<replay_layer::RequestId>::full());
    assert(cfg.capability.dom()
        == ISet::<replay_layer::CapabilityId>::full());
    assert forall|request: replay_layer::RequestId|
        #[trigger] cfg.request[request].retry_class
            == replay_layer::RetryClass::ReadOnly by {
    }
    assert forall|request: replay_layer::RequestId|
        #[trigger] cfg.request[request].stable_key == Option::None by {
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
    }
}

proof fn ro_selected_delivery_is_classified(
    cfg: config_layer::FullConfig,
    history: Seq<p0_layer::PhysicalEvent>,
    request: replay_layer::RequestId,
    attempt: replay_layer::AttemptId,
    observation: replay_layer::Observation,
    run: ExternalRun<bool, ReadOnlyWitness>,
)
    requires
        p1_layer::physical_unique(history),
        delivered_observations_classified(
            cfg, ro_adapter(), history, request, run,
        ),
        delivery(history, request, attempt) == Option::Some(observation),
    ensures
        ro_classification_ok(request, attempt, observation, run),
        match observation {
            replay_layer::Observation::Success(value) => {
                cfg.valid_results.contains((request, value))
            },
            replay_layer::Observation::Failure
            | replay_layer::Observation::Ambiguous
            | replay_layer::Observation::InvalidResult(_) => true,
        },
{
    t6_c0_layer::selected_delivery_has_witness(
        history, request, attempt, observation,
    );
    assert(ro_classification_ok(request, attempt, observation, run));
}

proof fn ro_adapter_verified_direct()
    ensures adapter_verified(ro_paper()),
{
    let paper = ro_paper();
    let cfg = ro_full_config();
    t1_layer::paper_broker_config_is_broker(paper);
    assert(t1_layer::paper_broker_config(paper) == cfg);
    assert forall|request: replay_layer::RequestId,
                  records: Seq<replay_layer::JournalRecord>,
                  history: Seq<p0_layer::PhysicalEvent>,
                  run: ExternalRun<bool, ReadOnlyWitness>,
                  outcome: TerminalOutcome| #![auto] {
        &&& replay_layer::journal_legal(
            config_layer::erase_config(cfg), records,
        )
        &&& adapter_rely_trace(paper, request, history, run)
        &&& outcome_evidence(cfg, records, request, history, outcome)
        &&& broker_outcome_compatible(
            cfg, records, request, history, outcome,
        )
    } implies refines(paper, request, history, run, outcome) by {
        assert(cfg.request[request].retry_class
            == replay_layer::RetryClass::ReadOnly);
        assert((paper.adapter.env_rely)(request, history, run));
        assert(ro_env_rely(request, history, run));
        assert(ro_zero_effect(request, run));
        assert(delivered_observations_classified(
            cfg, paper.adapter, history, request, run,
        ));
        assert(p1_layer::physical_unique(history));
        match outcome {
            TerminalOutcome::Commit { attempt, value } => {
                assert(delivery(history, request, attempt)
                    == Option::Some(
                        replay_layer::Observation::Success(value),
                    ));
                ro_selected_delivery_is_classified(
                    cfg,
                    history,
                    request,
                    attempt,
                    replay_layer::Observation::Success(value),
                    run,
                );
                assert(ro_has_sample_value(
                    run.interference.samples, attempt, value,
                ));
                let index = choose|index: int|
                    0 <= index < run.interference.samples.len()
                        && run.interference.samples[index].attempt == attempt
                        && value == ro_result_value(
                            run.interference.samples[index].present,
                        );
                assert(ro_result_spec(request, value, run)) by {
                    assert(exists|selected: int|
                        0 <= selected < run.interference.samples.len()
                            && value == ro_result_value(
                                run.interference.samples[selected].present,
                            )) by {
                        let selected = index;
                    }
                }
            },
            TerminalOutcome::Fail { .. }
            | TerminalOutcome::UnknownOutcome { .. } => {},
        }
    }
}

#[derive(PartialEq, Eq)]
pub enum ROAdapterMode {
    Online,
    Crashed,
    Recovering,
}

#[allow(inconsistent_fields)]
#[derive(PartialEq, Eq)]
pub enum ROAdapterEvent {
    Observe { event: global_layer::GlobalEvent },
    ServiceRead { attempt: replay_layer::AttemptId },
    EnvironmentSet { present: bool },
}

pub struct ROAdapterState {
    pub request: replay_layer::RequestId,
    pub initial_present: bool,
    pub present: bool,
    pub environment_updates: Seq<bool>,
    pub samples: Seq<ROReadSample>,
    pub failed_attempts: ISet<replay_layer::AttemptId>,
    pub globals: Seq<global_layer::GlobalEvent>,
    pub history: Seq<p0_layer::PhysicalEvent>,
    pub mode: ROAdapterMode,
    pub active: Option<replay_layer::AttemptId>,
}

pub struct ROAdapterExecution {
    pub configs: Seq<ROAdapterState>,
    pub events: Seq<ROAdapterEvent>,
}

pub open spec fn ro_initial_state(
    request: replay_layer::RequestId,
    initial_present: bool,
) -> ROAdapterState {
    ROAdapterState {
        request,
        initial_present,
        present: initial_present,
        environment_updates: Seq::empty(),
        samples: Seq::empty(),
        failed_attempts: ISet::empty(),
        globals: Seq::empty(),
        history: Seq::empty(),
        mode: ROAdapterMode::Online,
        active: Option::None,
    }
}

pub open spec fn ro_external_run(
    state: ROAdapterState,
) -> ExternalRun<bool, ReadOnlyWitness> {
    ExternalRun {
        pre: state.initial_present,
        post: state.present,
        interference: ReadOnlyWitness {
            environment_updates: state.environment_updates,
            samples: state.samples,
        },
    }
}

pub open spec fn ro_global_trace(
    events: Seq<ROAdapterEvent>,
) -> Seq<global_layer::GlobalEvent>
    decreases events.len()
{
    if events.len() == 0 {
        Seq::empty()
    } else {
        let prefix = ro_global_trace(events.drop_last());
        match events.last() {
            ROAdapterEvent::Observe { event } => prefix.push(event),
            ROAdapterEvent::ServiceRead { .. }
            | ROAdapterEvent::EnvironmentSet { .. } => prefix,
        }
    }
}

pub open spec fn ro_observe_enabled(
    state: ROAdapterState,
    event: global_layer::GlobalEvent,
) -> bool {
    let cfg = ro_full_config();
    let request = state.request;
    match event {
        global_layer::GlobalEvent::InvokeEvent {
            request: event_request, attempt, call, ..
        } if event_request == request => {
            &&& state.mode == ROAdapterMode::Online
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
            &&& state.mode == ROAdapterMode::Online
            &&& state.active == Option::Some(attempt)
            &&& attempt > 0
            &&& p1_layer::delivery_count(
                state.history, request, attempt,
            ) == 0
            &&& match observation {
                replay_layer::Observation::Success(value) => {
                    ro_has_sample_value(state.samples, attempt, value)
                },
                replay_layer::Observation::Failure => {
                    !ro_has_sample(state.samples, attempt)
                },
                replay_layer::Observation::Ambiguous
                | replay_layer::Observation::InvalidResult(_) => false,
            }
        },
        global_layer::GlobalEvent::Crash => {
            state.mode != ROAdapterMode::Crashed
        },
        global_layer::GlobalEvent::BeginRecover => {
            state.mode == ROAdapterMode::Crashed
        },
        global_layer::GlobalEvent::FinishRecover => {
            state.mode == ROAdapterMode::Recovering
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

pub open spec fn ro_enabled(
    state: ROAdapterState,
    event: ROAdapterEvent,
) -> bool {
    match event {
        ROAdapterEvent::Observe { event } => ro_observe_enabled(state, event),
        ROAdapterEvent::ServiceRead { attempt } => {
            &&& state.mode == ROAdapterMode::Online
            &&& state.active == Option::Some(attempt)
            &&& attempt > 0
            &&& invoked(state.history, state.request, attempt)
            &&& p1_layer::delivery_count(
                state.history, state.request, attempt,
            ) == 0
            &&& !ro_has_sample(state.samples, attempt)
            &&& !state.failed_attempts.contains(attempt)
        },
        ROAdapterEvent::EnvironmentSet { .. } => true,
    }
}

pub open spec fn ro_apply_observe(
    state: ROAdapterState,
    event: global_layer::GlobalEvent,
) -> ROAdapterState {
    let request = state.request;
    let globals = state.globals.push(event);
    let history = a1_history_after_global(state.history, event, request);
    match event {
        global_layer::GlobalEvent::InvokeEvent {
            request: event_request, attempt, ..
        } if event_request == request => ROAdapterState {
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
        } if event_request == request => ROAdapterState {
            failed_attempts: state.failed_attempts.insert(attempt),
            globals,
            history,
            active: Option::None,
            ..state
        },
        global_layer::GlobalEvent::DeliverEvent {
            request: event_request, ..
        } if event_request == request => ROAdapterState {
            globals,
            history,
            active: Option::None,
            ..state
        },
        global_layer::GlobalEvent::Crash => ROAdapterState {
            globals,
            mode: ROAdapterMode::Crashed,
            active: Option::None,
            ..state
        },
        global_layer::GlobalEvent::BeginRecover => ROAdapterState {
            globals,
            mode: ROAdapterMode::Recovering,
            ..state
        },
        global_layer::GlobalEvent::FinishRecover => ROAdapterState {
            globals,
            mode: ROAdapterMode::Online,
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
        | global_layer::GlobalEvent::AbortScan => ROAdapterState {
            globals,
            ..state
        },
    }
}

pub open spec fn ro_apply(
    state: ROAdapterState,
    event: ROAdapterEvent,
) -> ROAdapterState {
    match event {
        ROAdapterEvent::Observe { event } => ro_apply_observe(state, event),
        ROAdapterEvent::ServiceRead { attempt } => ROAdapterState {
            samples: state.samples.push(ROReadSample {
                attempt,
                present: state.present,
                environment_cut: state.environment_updates.len(),
                history_cut: state.history.len(),
            }),
            ..state
        },
        ROAdapterEvent::EnvironmentSet { present } => ROAdapterState {
            present,
            environment_updates: state.environment_updates.push(present),
            ..state
        },
    }
}

pub open spec fn ro_step(
    before: ROAdapterState,
    event: ROAdapterEvent,
    after: ROAdapterState,
) -> bool {
    ro_enabled(before, event) && after == ro_apply(before, event)
}

pub open spec fn ro_exec(
    request: replay_layer::RequestId,
    initial_present: bool,
    execution: ROAdapterExecution,
) -> bool {
    execution.configs.len() == execution.events.len() + 1
        && execution.configs[0] == ro_initial_state(request, initial_present)
        && forall|index: nat| index < execution.events.len() ==>
            #[trigger] ro_step(
                execution.configs[index as int],
                execution.events[index as int],
                execution.configs[(index + 1) as int],
            )
}

pub open spec fn ro_execution_prefix(
    execution: ROAdapterExecution,
    length: nat,
) -> ROAdapterExecution {
    ROAdapterExecution {
        configs: execution.configs.take((length + 1) as int),
        events: execution.events.take(length as int),
    }
}

pub open spec fn ro_history_classified(state: ROAdapterState) -> bool {
    forall|index: int| 0 <= index < state.history.len() ==>
        match #[trigger] state.history[index] {
            p0_layer::PhysicalEvent::Invoke { .. } => true,
            p0_layer::PhysicalEvent::Delivered {
                attempt,
                observation: replay_layer::Observation::Success(value),
                ..
            } => ro_has_sample_value(state.samples, attempt, value),
            p0_layer::PhysicalEvent::Delivered {
                attempt,
                observation: replay_layer::Observation::Failure,
                ..
            } => state.failed_attempts.contains(attempt)
                && !ro_has_sample(state.samples, attempt),
            p0_layer::PhysicalEvent::Delivered {
                observation: replay_layer::Observation::Ambiguous, ..
            }
            | p0_layer::PhysicalEvent::Delivered {
                observation: replay_layer::Observation::InvalidResult(_), ..
            } => false,
        }
}

pub open spec fn ro_machine_invariant(state: ROAdapterState) -> bool {
    let cfg = ro_full_config();
    &&& state.history
        == projection_layer::pi_adapter(state.globals, state.request)
    &&& request_local_history(state.history, state.request)
    &&& canonical_invocations(cfg, state.history, state.request)
    &&& positive_attempt_identifiers(state.history)
    &&& p1_layer::physical_unique(state.history)
    &&& p1_layer::physical_ordered(state.history)
    &&& state.present == ro_environment_value(
        state.initial_present, state.environment_updates,
    )
    &&& ro_samples_well_formed(
        state.initial_present,
        state.environment_updates,
        state.samples,
    )
    &&& ro_samples_have_history_provenance(
        state.history, state.request, state.samples,
    )
    &&& forall|index: int| 0 <= index < state.samples.len() ==>
        invoked(
            state.history,
            state.request,
            #[trigger] state.samples[index].attempt,
        )
    &&& ro_history_classified(state)
    &&& forall|attempt: replay_layer::AttemptId|
        #[trigger] state.failed_attempts.contains(attempt) ==>
            !ro_has_sample(state.samples, attempt)
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

pub open spec fn ro_execution_invariant(
    request: replay_layer::RequestId,
    initial_present: bool,
    state: ROAdapterState,
) -> bool {
    state.request == request
        && state.initial_present == initial_present
        && ro_machine_invariant(state)
}

proof fn ro_append_history_shape(
    state: ROAdapterState,
    physical: p0_layer::PhysicalEvent,
)
    requires
        request_local_history(state.history, state.request),
        canonical_invocations(
            ro_full_config(), state.history, state.request,
        ),
        positive_attempt_identifiers(state.history),
        event_is_for_request(physical, state.request),
        match physical {
            p0_layer::PhysicalEvent::Invoke { call, attempt, .. } => {
                call == config_layer::canonical_call(
                    ro_full_config(), state.request,
                ) && attempt > 0
            },
            p0_layer::PhysicalEvent::Delivered { attempt, .. } => attempt > 0,
        },
    ensures
        request_local_history(state.history.push(physical), state.request),
        canonical_invocations(
            ro_full_config(),
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
                    ro_full_config(), state.request,
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

proof fn ro_samples_history_push(
    history: Seq<p0_layer::PhysicalEvent>,
    physical: p0_layer::PhysicalEvent,
    request: replay_layer::RequestId,
    samples: Seq<ROReadSample>,
)
    requires ro_samples_have_history_provenance(
        history, request, samples,
    ),
    ensures ro_samples_have_history_provenance(
        history.push(physical), request, samples,
    ),
{
    assert forall|index: int| 0 <= index < samples.len() implies {
        let sample = #[trigger] samples[index];
        &&& sample.history_cut <= history.push(physical).len()
        &&& invoked(
            history.push(physical).take(sample.history_cut as int),
            request, sample.attempt,
        )
        &&& p1_layer::delivery_count(
            history.push(physical).take(sample.history_cut as int),
            request, sample.attempt,
        ) == 0
    } by {
        let sample = samples[index];
        assert(sample.history_cut <= history.len());
        append_layer::take_push_stable(
            history,
            physical,
            sample.history_cut,
        );
        if sample.history_cut < history.len() {
            assert(history.push(physical).take(
                sample.history_cut as int,
            ) =~= history.take(sample.history_cut as int));
        } else {
            assert(sample.history_cut == history.len());
            assert(history.push(physical).take(
                sample.history_cut as int,
            ) =~= history);
        }
    }
}

pub proof fn ro_initial_state_satisfies_invariant(
    request: replay_layer::RequestId,
    initial_present: bool,
)
    ensures ro_execution_invariant(
        request,
        initial_present,
        ro_initial_state(request, initial_present),
    ),
{
    reveal_with_fuel(projection_layer::adapter_from_physical, 1);
    reveal_with_fuel(projection_layer::pi_physical, 1);
    reveal_with_fuel(p1_layer::physical_unique, 1);
    reveal_with_fuel(p1_layer::physical_ordered, 1);
}

proof fn ro_samples_wf_push(
    initial: bool,
    updates: Seq<bool>,
    samples: Seq<ROReadSample>,
    sample: ROReadSample,
)
    requires
        ro_samples_well_formed(initial, updates, samples),
        !ro_has_sample(samples, sample.attempt),
        sample.attempt > 0,
        sample.environment_cut <= updates.len(),
        sample.present == ro_environment_value(
            initial, updates.take(sample.environment_cut as int),
        ),
    ensures ro_samples_well_formed(
        initial, updates, samples.push(sample),
    ),
{
    assert forall|index: int| 0 <= index < samples.push(sample).len()
        implies {
            let current = #[trigger] samples.push(sample)[index];
            &&& current.attempt > 0
            &&& current.environment_cut <= updates.len()
            &&& current.present == ro_environment_value(
                initial, updates.take(current.environment_cut as int),
            )
        } by {
        if index < samples.len() {
            assert(samples.push(sample)[index] == samples[index]);
        } else {
            assert(index == samples.len());
            assert(samples.push(sample)[index] == sample);
        }
    }
    assert forall|left: int, right: int|
        0 <= left < samples.push(sample).len()
            && 0 <= right < samples.push(sample).len()
            && #[trigger] samples.push(sample)[left].attempt
                == #[trigger] samples.push(sample)[right].attempt
        implies left == right by {
        if left < samples.len() && right < samples.len() {
            assert forall|old_left: int, old_right: int|
                0 <= old_left < samples.len()
                    && 0 <= old_right < samples.len()
                    && #[trigger] samples[old_left].attempt
                        == #[trigger] samples[old_right].attempt
                implies old_left == old_right by {
            }
        } else if left < samples.len() {
            assert(right == samples.len());
            assert(!ro_has_sample(samples, sample.attempt));
            if ro_has_sample(samples, sample.attempt) {
                let witness = choose|index: int|
                    0 <= index < samples.len()
                        && samples[index].attempt == sample.attempt;
                assert(witness == left);
                assert(false);
            }
        } else if right < samples.len() {
            assert(left == samples.len());
            assert(!ro_has_sample(samples, sample.attempt));
            if ro_has_sample(samples, sample.attempt) {
                let witness = choose|index: int|
                    0 <= index < samples.len()
                        && samples[index].attempt == sample.attempt;
                assert(witness == right);
                assert(false);
            }
        } else {
            assert(left == samples.len());
            assert(right == samples.len());
        }
    }
}

proof fn ro_samples_provenance_push(
    history: Seq<p0_layer::PhysicalEvent>,
    request: replay_layer::RequestId,
    samples: Seq<ROReadSample>,
    sample: ROReadSample,
)
    requires
        ro_samples_have_history_provenance(history, request, samples),
        sample.history_cut <= history.len(),
        invoked(
            history.take(sample.history_cut as int),
            request, sample.attempt,
        ),
        p1_layer::delivery_count(
            history.take(sample.history_cut as int),
            request, sample.attempt,
        ) == 0,
    ensures ro_samples_have_history_provenance(
        history, request, samples.push(sample),
    ),
{
    assert forall|index: int| 0 <= index < samples.push(sample).len()
        implies {
            let current = #[trigger] samples.push(sample)[index];
            &&& current.history_cut <= history.len()
            &&& invoked(
                history.take(current.history_cut as int),
                request, current.attempt,
            )
            &&& p1_layer::delivery_count(
                history.take(current.history_cut as int),
                request, current.attempt,
            ) == 0
        } by {
        if index < samples.len() {
            assert(samples.push(sample)[index] == samples[index]);
        } else {
            assert(index == samples.len());
            assert(samples.push(sample)[index] == sample);
        }
    }
}

proof fn ro_has_sample_value_push(
    samples: Seq<ROReadSample>,
    sample: ROReadSample,
    attempt: replay_layer::AttemptId,
    value: replay_layer::Value,
)
    requires ro_has_sample_value(samples, attempt, value),
    ensures ro_has_sample_value(
        samples.push(sample), attempt, value,
    ),
{
    let witness = choose|index: int|
        0 <= index < samples.len()
            && samples[index].attempt == attempt
            && value == ro_result_value(samples[index].present);
    assert(witness < samples.push(sample).len());
    assert(samples.push(sample)[witness] == samples[witness]);
}

proof fn ro_has_sample_value_singleton(
    sample: ROReadSample,
    attempt: replay_layer::AttemptId,
    value: replay_layer::Value,
)
    requires
        sample.attempt == attempt,
        value == ro_result_value(sample.present),
    ensures ro_has_sample_value(
        Seq::empty().push(sample), attempt, value,
    ),
{
    reveal(ro_has_sample_value);
    assert(exists|index: int|
        0 <= index < Seq::empty().push(sample).len()
            && #[trigger] Seq::empty().push(sample)[index].attempt
                == attempt
            && value == ro_result_value(
                Seq::empty().push(sample)[index].present,
            )) by {
        let index = 0;
        assert(Seq::empty().push(sample)[index] == sample);
    }
}

proof fn ro_service_read_preserves_invariant(
    before: ROAdapterState,
    attempt: replay_layer::AttemptId,
)
    requires
        ro_machine_invariant(before),
        ro_enabled(
            before,
            ROAdapterEvent::ServiceRead { attempt },
        ),
    ensures ro_machine_invariant(ro_apply(
        before, ROAdapterEvent::ServiceRead { attempt },
    )),
{
    let after = ro_apply(
        before, ROAdapterEvent::ServiceRead { attempt },
    );
    reveal(ro_enabled);
    assert(ro_enabled(
        before, ROAdapterEvent::ServiceRead { attempt },
    ));
    assert(
        before.mode == ROAdapterMode::Online
            && before.active == Option::Some(attempt)
            && invoked(before.history, before.request, attempt)
            && p1_layer::delivery_count(
                before.history, before.request, attempt,
            ) == 0
            && !ro_has_sample(before.samples, attempt)
            && !before.failed_attempts.contains(attempt)
    );
    let sample = ROReadSample {
        attempt,
        present: before.present,
        environment_cut: before.environment_updates.len(),
        history_cut: before.history.len(),
    };
    assert(after.samples == before.samples.push(sample));
    assert(after.present == before.present);
    assert(after.environment_updates == before.environment_updates);
    assert(after.failed_attempts == before.failed_attempts);
    assert(after.history == before.history);
    assert(attempt > 0);
    assert(invoked(before.history, before.request, attempt));
    assert(p1_layer::delivery_count(
        before.history, before.request, attempt,
    ) == 0);
    assert(sample.present == ro_environment_value(
        before.initial_present,
        before.environment_updates.take(
            sample.environment_cut as int,
        ),
    ));
    assert(before.environment_updates.take(
        sample.environment_cut as int,
    ) =~= before.environment_updates);
    assert(!ro_has_sample(before.samples, attempt));
    assert(sample.attempt > 0);
    assert(sample.environment_cut
        <= before.environment_updates.len());
    assert(sample.history_cut <= before.history.len());
    assert(before.history.take(sample.history_cut as int)
        =~= before.history);
    ro_samples_wf_push(
        before.initial_present,
        before.environment_updates,
        before.samples,
        sample,
    );
    ro_samples_provenance_push(
        before.history,
        before.request,
        before.samples,
        sample,
    );
    assert(ro_history_classified(after)) by {
        assert forall|index: int| 0 <= index < after.history.len()
            implies match #[trigger] after.history[index] {
                p0_layer::PhysicalEvent::Invoke { .. } => true,
                p0_layer::PhysicalEvent::Delivered {
                    attempt: observed_attempt,
                    observation: replay_layer::Observation::Success(value),
                    ..
                } => ro_has_sample_value(
                    after.samples, observed_attempt, value,
                ),
                p0_layer::PhysicalEvent::Delivered {
                    attempt: observed_attempt,
                    observation: replay_layer::Observation::Failure,
                    ..
                } => after.failed_attempts.contains(observed_attempt)
                    && !ro_has_sample(
                        after.samples, observed_attempt,
                    ),
                p0_layer::PhysicalEvent::Delivered {
                    observation: replay_layer::Observation::Ambiguous, ..
                }
                | p0_layer::PhysicalEvent::Delivered {
                    observation: replay_layer::Observation::InvalidResult(_), ..
                } => false,
            } by {
            match before.history[index] {
                p0_layer::PhysicalEvent::Invoke { .. } => {},
                p0_layer::PhysicalEvent::Delivered {
                    attempt: observed_attempt,
                    observation: replay_layer::Observation::Success(value),
                    ..
                } => {
                    assert(ro_has_sample_value(
                        before.samples, observed_attempt, value,
                    ));
                    ro_has_sample_value_push(
                        before.samples, sample, observed_attempt, value,
                    );
                },
                p0_layer::PhysicalEvent::Delivered {
                    attempt: observed_attempt,
                    observation: replay_layer::Observation::Failure,
                    ..
                } => {
                    assert(before.failed_attempts.contains(
                        observed_attempt,
                    ));
                    assert(after.failed_attempts.contains(
                        observed_attempt,
                    ));
                    assert(!ro_has_sample(
                        before.samples, observed_attempt,
                    ));
                    assert(!ro_has_sample(
                        after.samples, observed_attempt,
                    )) by {
                        if ro_has_sample(after.samples, observed_attempt) {
                            let witness = choose|sample_index: int|
                                0 <= sample_index < after.samples.len()
                                    && after.samples[sample_index].attempt
                                        == observed_attempt;
                            assert(witness < before.samples.len());
                            assert(before.samples[witness].attempt
                                == observed_attempt);
                            assert(false);
                        }
                    }
                },
                p0_layer::PhysicalEvent::Delivered {
                    observation: replay_layer::Observation::Ambiguous, ..
                }
                | p0_layer::PhysicalEvent::Delivered {
                    observation: replay_layer::Observation::InvalidResult(_), ..
                } => {},
            }
        }
    }
    assert forall|failed: replay_layer::AttemptId|
        #[trigger] after.failed_attempts.contains(failed)
            implies !ro_has_sample(after.samples, failed) by {
        if after.failed_attempts.contains(failed) {
            assert(before.failed_attempts.contains(failed));
            assert(!ro_has_sample(before.samples, failed));
            if ro_has_sample(after.samples, failed) {
                let witness = choose|sample_index: int|
                    0 <= sample_index < after.samples.len()
                        && after.samples[sample_index].attempt == failed;
                assert(witness < before.samples.len());
                assert(before.samples[witness].attempt == failed);
                assert(false);
            }
        }
    }
    assert(after.history
        == projection_layer::pi_adapter(after.globals, after.request));
    assert(request_local_history(after.history, after.request));
    assert(canonical_invocations(
        ro_full_config(), after.history, after.request,
    ));
    assert(positive_attempt_identifiers(after.history));
    assert(p1_layer::physical_unique(after.history));
    assert(p1_layer::physical_ordered(after.history));
    assert(after.active == before.active);
    assert(after.present == ro_environment_value(
        after.initial_present, after.environment_updates,
    ));
}

proof fn ro_environment_set_preserves_invariant(
    before: ROAdapterState,
    present: bool,
)
    requires
        ro_machine_invariant(before),
        ro_enabled(
            before,
            ROAdapterEvent::EnvironmentSet { present },
        ),
    ensures ro_machine_invariant(ro_apply(
        before, ROAdapterEvent::EnvironmentSet { present },
    )),
{
    let after = ro_apply(
        before, ROAdapterEvent::EnvironmentSet { present },
    );
    assert(after.history == before.history);
    assert(after.samples == before.samples);
    assert(after.failed_attempts == before.failed_attempts);
    assert(after.active == before.active);
    assert(after.environment_updates
        == before.environment_updates.push(present));
    assert(after.present == present);
    assert(ro_samples_well_formed(
        after.initial_present,
        after.environment_updates,
        after.samples,
    )) by {
        assert forall|index: int| 0 <= index < after.samples.len()
            implies {
                let sample = #[trigger] after.samples[index];
                &&& sample.attempt > 0
                &&& sample.environment_cut
                    <= after.environment_updates.len()
                &&& sample.present == ro_environment_value(
                    after.initial_present,
                    after.environment_updates.take(
                        sample.environment_cut as int,
                    ),
                )
            } by {
            assert(index < before.samples.len());
            assert(after.samples[index] == before.samples[index]);
            let sample = before.samples[index];
            assert(sample.environment_cut
                <= before.environment_updates.len());
            if sample.environment_cut < before.environment_updates.len() {
                assert(after.environment_updates.take(
                    sample.environment_cut as int,
                ) =~= before.environment_updates.take(
                    sample.environment_cut as int,
                ));
            } else {
                assert(sample.environment_cut
                    == before.environment_updates.len());
                assert(after.environment_updates.take(
                    sample.environment_cut as int,
                ) =~= before.environment_updates);
            }
        }
    }
    assert(ro_samples_have_history_provenance(
        after.history, after.request, after.samples,
    ));
    assert(ro_history_classified(after));
    assert(after.history
        == projection_layer::pi_adapter(after.globals, after.request));
    assert(request_local_history(after.history, after.request));
    assert(canonical_invocations(
        ro_full_config(), after.history, after.request,
    ));
    assert(positive_attempt_identifiers(after.history));
    assert(p1_layer::physical_unique(after.history));
    assert(p1_layer::physical_ordered(after.history));
    assert(after.present == ro_environment_value(
        after.initial_present, after.environment_updates,
    ));
}

proof fn ro_observe_preserves_invariant(
    before: ROAdapterState,
    event: global_layer::GlobalEvent,
)
    requires
        ro_machine_invariant(before),
        ro_observe_enabled(before, event),
    ensures ro_machine_invariant(ro_apply_observe(before, event)),
{
    let after = ro_apply_observe(before, event);
    let request = before.request;
    let cfg = ro_full_config();
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
            ro_append_history_shape(before, physical);
            ro_samples_history_push(
                before.history, physical, request, before.samples,
            );
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
            assert(after.history
                == projection_layer::pi_adapter(after.globals, request));
            assert(request_local_history(after.history, request));
            assert(canonical_invocations(cfg, after.history, request));
            assert(positive_attempt_identifiers(after.history));
            assert(p1_layer::physical_unique(after.history));
            assert(p1_layer::physical_ordered(after.history));
            assert(after.samples == before.samples);
            assert(after.failed_attempts == before.failed_attempts);
            assert(after.present == before.present);
            assert(after.environment_updates
                == before.environment_updates);
            assert(ro_samples_well_formed(
                after.initial_present,
                after.environment_updates,
                after.samples,
            ));
            assert(after.history.len() == before.history.len() + 1);
            assert(ro_history_classified(after));
            assert forall|sample_index: int|
                0 <= sample_index < after.samples.len() implies
                invoked(
                    after.history,
                    request,
                    #[trigger] after.samples[sample_index].attempt,
                ) by {
                assert(before.samples[sample_index].attempt
                    == after.samples[sample_index].attempt);
                assert(invoked(
                    before.history,
                    request,
                    before.samples[sample_index].attempt,
                ));
                p1_layer::invoke_count_push(
                    before.history, physical, request,
                    before.samples[sample_index].attempt,
                );
            }
            assert forall|failed: replay_layer::AttemptId|
                #[trigger] after.failed_attempts.contains(failed)
                    implies !ro_has_sample(after.samples, failed) by {
            }
            assert(after.active == Option::Some(attempt));
            assert(p1_layer::invoke_count(
                after.history, request, attempt,
            ) == 1);
            assert(p1_layer::delivery_count(
                after.history, request, attempt,
            ) == 0);
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
            ro_append_history_shape(before, physical);
            ro_samples_history_push(
                before.history, physical, request, before.samples,
            );
            p1_layer::unique_push_delivery(
                before.history, physical, request, attempt,
            );
            p1_layer::ordered_push_delivery(
                before.history, physical, request, attempt,
            );
            p1_layer::invoke_count_push(
                before.history, physical, request, attempt,
            );
            p1_layer::delivery_count_push(
                before.history, physical, request, attempt,
            );
            assert(after.history
                == projection_layer::pi_adapter(after.globals, request));
            assert(request_local_history(after.history, request));
            assert(canonical_invocations(cfg, after.history, request));
            assert(positive_attempt_identifiers(after.history));
            assert(p1_layer::physical_unique(after.history));
            assert(p1_layer::physical_ordered(after.history));
            assert(after.samples == before.samples);
            assert(after.present == before.present);
            assert(after.environment_updates
                == before.environment_updates);
            assert(ro_samples_well_formed(
                after.initial_present,
                after.environment_updates,
                after.samples,
            ));
            assert(ro_history_classified(after));
            assert forall|sample_index: int|
                0 <= sample_index < after.samples.len() implies
                invoked(
                    after.history,
                    request,
                    #[trigger] after.samples[sample_index].attempt,
                ) by {
                assert(invoked(
                    before.history,
                    request,
                    after.samples[sample_index].attempt,
                ));
                p1_layer::invoke_count_push(
                    before.history, physical, request,
                    after.samples[sample_index].attempt,
                );
            }
            assert forall|failed: replay_layer::AttemptId|
                #[trigger] after.failed_attempts.contains(failed)
                    implies !ro_has_sample(after.samples, failed) by {
                if failed == attempt {
                    match observation {
                        replay_layer::Observation::Failure => {
                            assert(!ro_has_sample(before.samples, attempt));
                        },
                        replay_layer::Observation::Success(_) => {},
                        replay_layer::Observation::Ambiguous
                        | replay_layer::Observation::InvalidResult(_) => {},
                    }
                }
            }
            match observation {
                replay_layer::Observation::Failure => {
                    assert(after.failed_attempts.contains(attempt));
                    assert(!ro_has_sample(after.samples, attempt));
                },
                replay_layer::Observation::Success(value) => {
                    assert(ro_has_sample_value(
                        after.samples, attempt, value,
                    ));
                },
                replay_layer::Observation::Ambiguous
                | replay_layer::Observation::InvalidResult(_) => {},
            }
            assert(after.active == Option::None);
        },
        global_layer::GlobalEvent::Crash
        | global_layer::GlobalEvent::BeginRecover
        | global_layer::GlobalEvent::FinishRecover
        | global_layer::GlobalEvent::BrokerLinearize { .. }
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
        => {
            assert(after.history == before.history);
            assert(ro_samples_have_history_provenance(
                after.history, request, after.samples,
            ));
            assert(after.samples == before.samples);
            assert(after.failed_attempts == before.failed_attempts);
            assert(after.present == before.present);
            assert(after.environment_updates
                == before.environment_updates);
            assert(after.history
                == projection_layer::pi_adapter(after.globals, request));
            assert(request_local_history(after.history, request));
            assert(canonical_invocations(cfg, after.history, request));
            assert(positive_attempt_identifiers(after.history));
            assert(p1_layer::physical_unique(after.history));
            assert(p1_layer::physical_ordered(after.history));
            assert(ro_samples_well_formed(
                after.initial_present,
                after.environment_updates,
                after.samples,
            ));
            assert(ro_history_classified(after));
            assert forall|sample_index: int|
                0 <= sample_index < after.samples.len() implies
                invoked(
                    after.history,
                    request,
                    #[trigger] after.samples[sample_index].attempt,
                ) by {
                assert(invoked(
                    before.history,
                    request,
                    after.samples[sample_index].attempt,
                ));
            }
            assert forall|failed: replay_layer::AttemptId|
                #[trigger] after.failed_attempts.contains(failed)
                    implies !ro_has_sample(after.samples, failed) by {
            }
            match after.active {
                Option::None => {},
                Option::Some(active) => {
                    assert(before.active == Option::Some(active));
                    assert(p1_layer::invoke_count(
                        after.history, request, active,
                    ) == 1);
                    assert(p1_layer::delivery_count(
                        after.history, request, active,
                    ) == 0);
                },
            }
        },
    }
    assert(after.present == ro_environment_value(
        after.initial_present, after.environment_updates,
    ));
}

pub proof fn ro_step_preserves_invariant(
    request: replay_layer::RequestId,
    initial_present: bool,
    before: ROAdapterState,
    event: ROAdapterEvent,
)
    requires
        ro_execution_invariant(request, initial_present, before),
        ro_enabled(before, event),
    ensures ro_execution_invariant(
        request, initial_present, ro_apply(before, event),
    ),
{
    match event {
        ROAdapterEvent::Observe { event } => {
            ro_observe_preserves_invariant(before, event);
        },
        ROAdapterEvent::ServiceRead { attempt } => {
            ro_service_read_preserves_invariant(before, attempt);
        },
        ROAdapterEvent::EnvironmentSet { present } => {
            ro_environment_set_preserves_invariant(before, present);
        },
    }
}

pub proof fn ro_exec_prefix(
    request: replay_layer::RequestId,
    initial_present: bool,
    execution: ROAdapterExecution,
    length: nat,
)
    requires
        ro_exec(request, initial_present, execution),
        length <= execution.events.len(),
    ensures ro_exec(
        request,
        initial_present,
        ro_execution_prefix(execution, length),
    ),
{
    let prefix = ro_execution_prefix(execution, length);
    assert(prefix.events.len() == length);
    assert(prefix.configs.len() == length + 1);
    assert(prefix.configs[0] == execution.configs[0]);
    assert forall|index: nat| index < prefix.events.len() implies
        #[trigger] ro_step(
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

pub proof fn ro_every_exec_configuration_satisfies_invariant(
    request: replay_layer::RequestId,
    initial_present: bool,
    execution: ROAdapterExecution,
)
    requires ro_exec(request, initial_present, execution),
    ensures forall|index: nat| index < execution.configs.len() ==>
        #[trigger] ro_execution_invariant(
            request,
            initial_present,
            execution.configs[index as int],
        ),
    decreases execution.events.len(),
{
    if execution.events.len() == 0 {
        ro_initial_state_satisfies_invariant(
            request, initial_present,
        );
    } else {
        let last_index: nat = (execution.events.len() - 1) as nat;
        let prefix = ro_execution_prefix(execution, last_index);
        ro_exec_prefix(
            request, initial_present, execution, last_index,
        );
        ro_every_exec_configuration_satisfies_invariant(
            request, initial_present, prefix,
        );
        assert(prefix.configs.len() == execution.events.len());
        assert forall|index: nat| index < execution.events.len() implies
            #[trigger] ro_execution_invariant(
                request,
                initial_present,
                execution.configs[index as int],
            ) by {
            assert(index < prefix.configs.len());
            assert(prefix.configs[index as int]
                == execution.configs[index as int]);
        }
        let before = execution.configs[last_index as int];
        let event = execution.events[last_index as int];
        let after = execution.configs[(last_index + 1) as int];
        assert(ro_execution_invariant(
            request, initial_present, before,
        ));
        assert(ro_step(before, event, after));
        ro_step_preserves_invariant(
            request, initial_present, before, event,
        );
        assert(after == ro_apply(before, event));
        assert(ro_execution_invariant(
            request, initial_present, after,
        ));
        assert forall|index: nat| index < execution.configs.len() implies
            #[trigger] ro_execution_invariant(
                request,
                initial_present,
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

proof fn ro_global_trace_push(
    events: Seq<ROAdapterEvent>,
    event: ROAdapterEvent,
)
    ensures ro_global_trace(events.push(event)) == match event {
        ROAdapterEvent::Observe { event: global } => {
            ro_global_trace(events).push(global)
        },
        ROAdapterEvent::ServiceRead { .. }
        | ROAdapterEvent::EnvironmentSet { .. } => {
            ro_global_trace(events)
        },
    },
{
    assert(events.push(event).drop_last() =~= events);
    assert(events.push(event).last() == event);
}

pub proof fn ro_exec_final_globals_are_projected(
    request: replay_layer::RequestId,
    initial_present: bool,
    execution: ROAdapterExecution,
)
    requires ro_exec(request, initial_present, execution),
    ensures execution.configs[execution.events.len() as int].globals
        == ro_global_trace(execution.events),
    decreases execution.events.len(),
{
    if execution.events.len() == 0 {
        assert(execution.configs[0]
            == ro_initial_state(request, initial_present));
    } else {
        let last_index: nat = (execution.events.len() - 1) as nat;
        let prefix = ro_execution_prefix(execution, last_index);
        ro_exec_prefix(
            request, initial_present, execution, last_index,
        );
        ro_exec_final_globals_are_projected(
            request, initial_present, prefix,
        );
        assert(prefix.events =~= execution.events.drop_last());
        assert(prefix.configs.len() == execution.events.len());
        assert(prefix.configs[last_index as int]
            == execution.configs[last_index as int]);
        let before = execution.configs[last_index as int];
        let event = execution.events[last_index as int];
        let after = execution.configs[(last_index + 1) as int];
        assert(ro_step(before, event, after));
        assert(after == ro_apply(before, event));
        ro_global_trace_push(prefix.events, event);
        assert(execution.events =~= prefix.events.push(event));
        match event {
            ROAdapterEvent::Observe { event: global } => {
                assert(after.globals == before.globals.push(global));
            },
            ROAdapterEvent::ServiceRead { .. }
            | ROAdapterEvent::EnvironmentSet { .. } => {
                assert(after.globals == before.globals);
            },
        }
    }
}

pub proof fn ro_invariant_implies_adapter_rely_trace(
    state: ROAdapterState,
)
    requires ro_machine_invariant(state),
    ensures adapter_rely_trace(
        ro_paper(),
        state.request,
        state.history,
        ro_external_run(state),
    ),
{
    let cfg = ro_full_config();
    let paper = ro_paper();
    let run = ro_external_run(state);
    t1_layer::paper_broker_config_is_broker(paper);
    assert(t1_layer::paper_broker_config(paper) == cfg);
    assert(run.post == state.present);
    assert(state.present == ro_environment_value(
        state.initial_present, state.environment_updates,
    ));
    assert(ro_zero_effect(state.request, run));
    assert(ro_env_rely(state.request, state.history, run)) by {
        assert(ro_samples_well_formed(
            run.pre,
            run.interference.environment_updates,
            run.interference.samples,
        ));
        assert(ro_samples_have_history_provenance(
            state.history, state.request, state.samples,
        ));
    }
    assert(delivered_observations_classified(
        cfg, ro_adapter(), state.history, state.request, run,
    )) by {
        assert forall|index: int| 0 <= index < state.history.len()
            implies match #[trigger] state.history[index] {
                p0_layer::PhysicalEvent::Invoke { .. } => true,
                p0_layer::PhysicalEvent::Delivered {
                    attempt, observation, ..
                } => ro_classification_ok(
                    state.request, attempt, observation, run,
                ),
            } by {
            match state.history[index] {
                p0_layer::PhysicalEvent::Invoke { .. } => {},
                p0_layer::PhysicalEvent::Delivered {
                    attempt, observation, ..
                } => {
                    assert(ro_classification_ok(
                        state.request, attempt, observation, run,
                    ));
                },
            }
        }
    }
    assert(adapter_class_law(
        cfg, ro_adapter(), state.history, state.request, run,
    ));
    assert(cfg.request[state.request].retry_class
        == replay_layer::RetryClass::ReadOnly);
    assert(ro_read_preserves(state.request, run));
    assert(ro_zero_effect(state.request, run));
    assert(request_local_history(state.history, state.request));
    assert(canonical_invocations(cfg, state.history, state.request));
    assert(positive_attempt_identifiers(state.history));
    assert(p1_layer::physical_unique(state.history));
    assert(p1_layer::physical_ordered(state.history));
    assert(state.history == projection_layer::pi_adapter(
        state.globals, state.request,
    ));
    assert(cfg.request[state.request].retry_class
        != replay_layer::RetryClass::Deduplicated);
    assert(adapter_rely_trace(
        paper, state.request, state.history, run,
    ));
}

pub proof fn ro_exec_derives_adapter_rely(
    request: replay_layer::RequestId,
    initial_present: bool,
    execution: ROAdapterExecution,
)
    requires ro_exec(request, initial_present, execution),
    ensures
        adapter_rely(
            ro_paper(),
            execution.configs[execution.events.len() as int].globals,
            request,
            ro_external_run(
                execution.configs[execution.events.len() as int],
            ),
        ),
        ro_execution_invariant(
            request,
            initial_present,
            execution.configs[execution.events.len() as int],
        ),
{
    ro_every_exec_configuration_satisfies_invariant(
        request, initial_present, execution,
    );
    let final_state = execution.configs[execution.events.len() as int];
    assert(ro_execution_invariant(
        request, initial_present, final_state,
    ));
    assert(ro_machine_invariant(final_state));
    ro_invariant_implies_adapter_rely_trace(final_state);
    ro_exec_final_globals_are_projected(
        request, initial_present, execution,
    );
    adapter_rely_is_projected_rely(
        ro_paper(),
        final_state.globals,
        request,
        ro_external_run(final_state),
    );
}

pub open spec fn ro_zero_adapter_execution(
    request: replay_layer::RequestId,
    initial_present: bool,
) -> ROAdapterExecution {
    ROAdapterExecution {
        configs: Seq::empty().push(
            ro_initial_state(request, initial_present),
        ),
        events: Seq::empty(),
    }
}

pub open spec fn ro_extend_adapter_execution(
    execution: ROAdapterExecution,
    event: ROAdapterEvent,
) -> ROAdapterExecution {
    let before = execution.configs.last();
    ROAdapterExecution {
        configs: execution.configs.push(ro_apply(before, event)),
        events: execution.events.push(event),
    }
}

pub proof fn ro_zero_adapter_execution_exec(
    request: replay_layer::RequestId,
    initial_present: bool,
)
    ensures ro_exec(
        request,
        initial_present,
        ro_zero_adapter_execution(request, initial_present),
    ),
{
}

pub proof fn ro_extend_adapter_execution_exec(
    request: replay_layer::RequestId,
    initial_present: bool,
    execution: ROAdapterExecution,
    event: ROAdapterEvent,
)
    requires
        ro_exec(request, initial_present, execution),
        ro_enabled(execution.configs.last(), event),
    ensures ro_exec(
        request,
        initial_present,
        ro_extend_adapter_execution(execution, event),
    ),
    ro_extend_adapter_execution(execution, event).events.len()
        == execution.events.len() + 1,
    ro_global_trace(
        ro_extend_adapter_execution(execution, event).events,
    ) == match event {
        ROAdapterEvent::Observe { event: global } => {
            ro_global_trace(execution.events).push(global)
        },
        ROAdapterEvent::ServiceRead { .. }
        | ROAdapterEvent::EnvironmentSet { .. } => {
            ro_global_trace(execution.events)
        },
    },
{
    let extended = ro_extend_adapter_execution(execution, event);
    let old_len = execution.events.len();
    assert(execution.configs.len() == old_len + 1);
    assert(execution.configs.last()
        == execution.configs[old_len as int]);
    assert forall|index: nat| index < extended.events.len() implies
        #[trigger] ro_step(
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
                == ro_apply(execution.configs.last(), event));
        }
    }
    ro_global_trace_push(execution.events, event);
}

pub open spec fn ro_observe_full_append(
    execution: ROAdapterExecution,
    record: replay_layer::JournalRecord,
    cut: nat,
) -> ROAdapterExecution {
    let staged = ro_extend_adapter_execution(
        execution,
        ROAdapterEvent::Observe {
            event: global_layer::GlobalEvent::WalStage { record },
        },
    );
    let written = ro_extend_adapter_execution(
        staged,
        ROAdapterEvent::Observe {
            event: global_layer::GlobalEvent::WalWriteFull { record },
        },
    );
    ro_extend_adapter_execution(
        written,
        ROAdapterEvent::Observe {
            event: global_layer::GlobalEvent::WalFlushAck { cut },
        },
    )
}

pub proof fn ro_observe_full_append_exec(
    request: replay_layer::RequestId,
    initial_present: bool,
    execution: ROAdapterExecution,
    record: replay_layer::JournalRecord,
    cut: nat,
)
    requires ro_exec(request, initial_present, execution),
    ensures ro_exec(
        request,
        initial_present,
        ro_observe_full_append(execution, record, cut),
    ),
    ro_observe_full_append(execution, record, cut).events.len()
        == execution.events.len() + 3,
    ro_global_trace(
        ro_observe_full_append(execution, record, cut).events,
    ) == ro_global_trace(execution.events)
        .push(global_layer::GlobalEvent::WalStage { record })
        .push(global_layer::GlobalEvent::WalWriteFull { record })
        .push(global_layer::GlobalEvent::WalFlushAck { cut }),
{
    let stage = ROAdapterEvent::Observe {
        event: global_layer::GlobalEvent::WalStage { record },
    };
    let staged = ro_extend_adapter_execution(execution, stage);
    assert(ro_enabled(execution.configs.last(), stage));
    ro_extend_adapter_execution_exec(
        request, initial_present, execution, stage,
    );
    let write = ROAdapterEvent::Observe {
        event: global_layer::GlobalEvent::WalWriteFull { record },
    };
    let written = ro_extend_adapter_execution(staged, write);
    assert(ro_enabled(staged.configs.last(), write));
    ro_extend_adapter_execution_exec(
        request, initial_present, staged, write,
    );
    let flush = ROAdapterEvent::Observe {
        event: global_layer::GlobalEvent::WalFlushAck { cut },
    };
    assert(ro_enabled(written.configs.last(), flush));
    ro_extend_adapter_execution_exec(
        request, initial_present, written, flush,
    );
}

pub proof fn ro_observe_full_append_preserves_adapter_state(
    request: replay_layer::RequestId,
    initial_present: bool,
    execution: ROAdapterExecution,
    record: replay_layer::JournalRecord,
    cut: nat,
)
    requires
        ro_exec(request, initial_present, execution),
    ensures
        ro_observe_full_append(execution, record, cut)
            .configs.last().mode
            == execution.configs.last().mode,
        ro_observe_full_append(execution, record, cut)
            .configs.last().active
            == execution.configs.last().active,
        ro_observe_full_append(execution, record, cut)
            .configs.last().present
            == execution.configs.last().present,
        ro_observe_full_append(execution, record, cut)
            .configs.last().environment_updates
            == execution.configs.last().environment_updates,
        ro_observe_full_append(execution, record, cut)
            .configs.last().samples
            == execution.configs.last().samples,
        ro_observe_full_append(execution, record, cut)
            .configs.last().history
            == execution.configs.last().history,
        ro_observe_full_append(execution, record, cut)
            .configs.last().failed_attempts
            == execution.configs.last().failed_attempts,
{
    let stage = ROAdapterEvent::Observe {
        event: global_layer::GlobalEvent::WalStage { record },
    };
    let staged = ro_extend_adapter_execution(execution, stage);
    ro_extend_adapter_execution_exec(
        request, initial_present, execution, stage,
    );
    let write = ROAdapterEvent::Observe {
        event: global_layer::GlobalEvent::WalWriteFull { record },
    };
    let written = ro_extend_adapter_execution(staged, write);
    ro_extend_adapter_execution_exec(
        request, initial_present, staged, write,
    );
    let flush = ROAdapterEvent::Observe {
        event: global_layer::GlobalEvent::WalFlushAck { cut },
    };
    ro_extend_adapter_execution_exec(
        request, initial_present, written, flush,
    );
    assert(ro_observe_full_append(execution, record, cut)
        .configs.last()
        == ro_apply_observe(
            written.configs.last(),
            global_layer::GlobalEvent::WalFlushAck { cut },
        ));
    assert(ro_apply_observe(
        written.configs.last(),
        global_layer::GlobalEvent::WalFlushAck { cut },
    ).mode == written.configs.last().mode);
    assert(ro_apply_observe(
        written.configs.last(),
        global_layer::GlobalEvent::WalFlushAck { cut },
    ).active == written.configs.last().active);
    assert(ro_apply_observe(
        written.configs.last(),
        global_layer::GlobalEvent::WalFlushAck { cut },
    ).present == written.configs.last().present);
    assert(ro_apply_observe(
        written.configs.last(),
        global_layer::GlobalEvent::WalFlushAck { cut },
    ).environment_updates == written.configs.last().environment_updates);
    assert(ro_apply_observe(
        written.configs.last(),
        global_layer::GlobalEvent::WalFlushAck { cut },
    ).samples == written.configs.last().samples);
    assert(ro_apply_observe(
        written.configs.last(),
        global_layer::GlobalEvent::WalFlushAck { cut },
    ).history == written.configs.last().history);
    assert(ro_apply_observe(
        written.configs.last(),
        global_layer::GlobalEvent::WalFlushAck { cut },
    ).failed_attempts == written.configs.last().failed_attempts);
    assert(written.configs.last().mode == execution.configs.last().mode);
    assert(written.configs.last().active == execution.configs.last().active);
    assert(written.configs.last().present == execution.configs.last().present);
    assert(written.configs.last().environment_updates
        == execution.configs.last().environment_updates);
    assert(written.configs.last().samples
        == execution.configs.last().samples);
    assert(written.configs.last().history
        == execution.configs.last().history);
    assert(written.configs.last().failed_attempts
        == execution.configs.last().failed_attempts);
}

pub open spec fn ro_observe_wal_event(
    execution: ROAdapterExecution,
    local: wal_runtime_layer::WalEvent,
) -> ROAdapterExecution {
    ro_extend_adapter_execution(
        execution,
        ROAdapterEvent::Observe {
            event: wal_runtime_layer::wal_encode(local),
        },
    )
}

pub proof fn ro_observe_wal_event_exec(
    request: replay_layer::RequestId,
    initial_present: bool,
    execution: ROAdapterExecution,
    local: wal_runtime_layer::WalEvent,
)
    requires
        ro_exec(request, initial_present, execution),
        ro_enabled(
            execution.configs.last(),
            ROAdapterEvent::Observe {
                event: wal_runtime_layer::wal_encode(local),
            },
        ),
    ensures
        ro_exec(
            request,
            initial_present,
            ro_observe_wal_event(execution, local),
        ),
        ro_observe_wal_event(execution, local).events.len()
            == execution.events.len() + 1,
        ro_global_trace(
            ro_observe_wal_event(execution, local).events,
        ) == ro_global_trace(execution.events).push(
            wal_runtime_layer::wal_encode(local),
        ),
{
    ro_extend_adapter_execution_exec(
        request,
        initial_present,
        execution,
        ROAdapterEvent::Observe {
            event: wal_runtime_layer::wal_encode(local),
        },
    );
}

pub open spec fn ro_observe_recovery(
    execution: ROAdapterExecution,
) -> ROAdapterExecution {
    let crashed = ro_extend_adapter_execution(
        execution,
        ROAdapterEvent::Observe {
            event: global_layer::GlobalEvent::Crash,
        },
    );
    let scanning = ro_extend_adapter_execution(
        crashed,
        ROAdapterEvent::Observe {
            event: global_layer::GlobalEvent::BeginScan,
        },
    );
    let scanned = ro_extend_adapter_execution(
        scanning,
        ROAdapterEvent::Observe {
            event: global_layer::GlobalEvent::FinishScan,
        },
    );
    let truncated = ro_extend_adapter_execution(
        scanned,
        ROAdapterEvent::Observe {
            event: global_layer::GlobalEvent::TruncateTail,
        },
    );
    let recovering = ro_extend_adapter_execution(
        truncated,
        ROAdapterEvent::Observe {
            event: global_layer::GlobalEvent::BeginRecover,
        },
    );
    ro_extend_adapter_execution(
        recovering,
        ROAdapterEvent::Observe {
            event: global_layer::GlobalEvent::FinishRecover,
        },
    )
}

pub proof fn ro_observe_recovery_exec(
    request: replay_layer::RequestId,
    initial_present: bool,
    execution: ROAdapterExecution,
)
    requires
        ro_exec(request, initial_present, execution),
        execution.configs.last().mode == ROAdapterMode::Online,
    ensures
        ro_exec(
            request,
            initial_present,
            ro_observe_recovery(execution),
        ),
        ro_observe_recovery(execution).configs.last().mode
            == ROAdapterMode::Online,
        ro_observe_recovery(execution).events.len()
            == execution.events.len() + 6,
        ro_global_trace(ro_observe_recovery(execution).events)
            == ro_global_trace(execution.events)
                .push(global_layer::GlobalEvent::Crash)
                .push(global_layer::GlobalEvent::BeginScan)
                .push(global_layer::GlobalEvent::FinishScan)
                .push(global_layer::GlobalEvent::TruncateTail)
                .push(global_layer::GlobalEvent::BeginRecover)
                .push(global_layer::GlobalEvent::FinishRecover),
{
    let crash = ROAdapterEvent::Observe {
        event: global_layer::GlobalEvent::Crash,
    };
    let crashed = ro_extend_adapter_execution(execution, crash);
    assert(ro_enabled(execution.configs.last(), crash));
    ro_extend_adapter_execution_exec(
        request, initial_present, execution, crash,
    );
    let begin_scan = ROAdapterEvent::Observe {
        event: global_layer::GlobalEvent::BeginScan,
    };
    let scanning = ro_extend_adapter_execution(crashed, begin_scan);
    assert(ro_enabled(crashed.configs.last(), begin_scan));
    ro_extend_adapter_execution_exec(
        request, initial_present, crashed, begin_scan,
    );
    let finish_scan = ROAdapterEvent::Observe {
        event: global_layer::GlobalEvent::FinishScan,
    };
    let scanned = ro_extend_adapter_execution(scanning, finish_scan);
    assert(ro_enabled(scanning.configs.last(), finish_scan));
    ro_extend_adapter_execution_exec(
        request, initial_present, scanning, finish_scan,
    );
    let truncate = ROAdapterEvent::Observe {
        event: global_layer::GlobalEvent::TruncateTail,
    };
    let truncated = ro_extend_adapter_execution(scanned, truncate);
    assert(ro_enabled(scanned.configs.last(), truncate));
    ro_extend_adapter_execution_exec(
        request, initial_present, scanned, truncate,
    );
    let begin_recover = ROAdapterEvent::Observe {
        event: global_layer::GlobalEvent::BeginRecover,
    };
    let recovering = ro_extend_adapter_execution(
        truncated, begin_recover,
    );
    assert(ro_enabled(truncated.configs.last(), begin_recover));
    ro_extend_adapter_execution_exec(
        request, initial_present, truncated, begin_recover,
    );
    let finish_recover = ROAdapterEvent::Observe {
        event: global_layer::GlobalEvent::FinishRecover,
    };
    assert(ro_enabled(recovering.configs.last(), finish_recover));
    ro_extend_adapter_execution_exec(
        request, initial_present, recovering, finish_recover,
    );
    assert(ro_observe_recovery(execution).events.len()
        == execution.events.len() + 6);
}

pub open spec fn ro_success_value() -> replay_layer::Value {
    ro_result_value(false)
}

pub open spec fn ro_authorize_record()
    -> replay_layer::JournalRecord
{
    replay_layer::JournalRecord::Authorize {
        request: ro_request_zero(),
        capability: replay_layer::CapabilityId { id: 0 },
        digest: replay_layer::Digest { id: 0 },
    }
}

pub open spec fn ro_prepare_record()
    -> replay_layer::JournalRecord
{
    replay_layer::JournalRecord::Prepare {
        request: ro_request_zero(),
        class: replay_layer::RetryClass::ReadOnly,
        digest: replay_layer::Digest { id: 0 },
        key: Option::None,
        auth_ref: 1,
    }
}

pub open spec fn ro_arm_record()
    -> replay_layer::JournalRecord
{
    replay_layer::JournalRecord::Arm {
        request: ro_request_zero(),
        digest: replay_layer::Digest { id: 0 },
        key: Option::None,
        prepare_ref: 2,
    }
}

pub open spec fn ro_start_one_record()
    -> replay_layer::JournalRecord
{
    replay_layer::JournalRecord::Start {
        request: ro_request_zero(),
        attempt: 1,
        digest: replay_layer::Digest { id: 0 },
        key: Option::None,
        arm_ref: 3,
    }
}

pub open spec fn ro_start_two_record()
    -> replay_layer::JournalRecord
{
    replay_layer::JournalRecord::Start {
        request: ro_request_zero(),
        attempt: 2,
        digest: replay_layer::Digest { id: 0 },
        key: Option::None,
        arm_ref: 3,
    }
}

pub open spec fn ro_failure_outcome_record()
    -> replay_layer::JournalRecord
{
    replay_layer::JournalRecord::Outcome {
        request: ro_request_zero(),
        attempt: 2,
        observation: replay_layer::Observation::Failure,
        digest: replay_layer::Digest { id: 0 },
        key: Option::None,
        start_ref: 5,
    }
}

pub open spec fn ro_fail_record()
    -> replay_layer::JournalRecord
{
    replay_layer::JournalRecord::FailRec {
        request: ro_request_zero(),
        attempt: 2,
        digest: replay_layer::Digest { id: 0 },
        key: Option::None,
        outcome_ref: 6,
    }
}

pub open spec fn ro_records()
    -> Seq<replay_layer::JournalRecord>
{
    Seq::empty()
        .push(ro_authorize_record())
        .push(ro_prepare_record())
        .push(ro_arm_record())
        .push(ro_start_one_record())
        .push(ro_start_two_record())
        .push(ro_failure_outcome_record())
        .push(ro_fail_record())
}

// Named journal prefixes keep the executable witness proofs readable and
// give the replay solver a small, stable term at each cut.  They are
// definitionally equal to the corresponding prefixes of `ro_records()`.
pub open spec fn ro_precrash_records()
    -> Seq<replay_layer::JournalRecord>
{
    Seq::empty()
        .push(ro_authorize_record())
        .push(ro_prepare_record())
        .push(ro_arm_record())
        .push(ro_start_one_record())
}

pub open spec fn ro_retry_started_records()
    -> Seq<replay_layer::JournalRecord>
{
    ro_precrash_records().push(ro_start_two_record())
}

pub open spec fn ro_failure_records()
    -> Seq<replay_layer::JournalRecord>
{
    ro_retry_started_records().push(ro_failure_outcome_record())
}

pub open spec fn ro_invoke_one_wal_event()
    -> wal_runtime_layer::WalEvent
{
    wal_runtime_layer::WalEvent::InvokeEvent {
        request: ro_request_zero(),
        attempt: 1,
        call: config_layer::canonical_call(
            ro_full_config(), ro_request_zero(),
        ),
        journal_cut: 4,
        ack_cut: 4,
    }
}

pub open spec fn ro_success_one_wal_event()
    -> wal_runtime_layer::WalEvent
{
    wal_runtime_layer::WalEvent::DeliverEvent {
        request: ro_request_zero(),
        attempt: 1,
        observation: replay_layer::Observation::Success(
            ro_success_value(),
        ),
        journal_cut: 4,
    }
}

pub open spec fn ro_invoke_two_wal_event()
    -> wal_runtime_layer::WalEvent
{
    wal_runtime_layer::WalEvent::InvokeEvent {
        request: ro_request_zero(),
        attempt: 2,
        call: config_layer::canonical_call(
            ro_full_config(), ro_request_zero(),
        ),
        journal_cut: 5,
        ack_cut: 5,
    }
}

pub open spec fn ro_failure_two_wal_event()
    -> wal_runtime_layer::WalEvent
{
    wal_runtime_layer::WalEvent::DeliverEvent {
        request: ro_request_zero(),
        attempt: 2,
        observation: replay_layer::Observation::Failure,
        journal_cut: 5,
    }
}

pub open spec fn ro_wal_pre_crash_execution()
    -> wal_runtime_layer::WalExecution
{
    let cfg = ro_full_config();
    let e0 = t6_a0_zero_wal_execution(cfg);
    let e1 = t6_a0_append_full_wal_execution(
        cfg, e0, ro_authorize_record(),
    );
    let e2 = t6_a0_append_full_wal_execution(
        cfg, e1, ro_prepare_record(),
    );
    let e3 = t6_a0_append_full_wal_execution(
        cfg, e2, ro_arm_record(),
    );
    let e4 = t6_a0_append_full_wal_execution(
        cfg, e3, ro_start_one_record(),
    );
    let e5 = t6_a0_extend_wal_execution(
        cfg, e4, ro_invoke_one_wal_event(),
    );
    t6_a0_extend_wal_execution(
        cfg, e5, ro_success_one_wal_event(),
    )
}

pub open spec fn ro_wal_recovered_execution()
    -> wal_runtime_layer::WalExecution
{
    let cfg = ro_full_config();
    let e6 = ro_wal_pre_crash_execution();
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

pub open spec fn ro_wal_retry_observed_execution()
    -> wal_runtime_layer::WalExecution
{
    let cfg = ro_full_config();
    let e12 = ro_wal_recovered_execution();
    let e13 = t6_a0_append_full_wal_execution(
        cfg, e12, ro_start_two_record(),
    );
    let e14 = t6_a0_extend_wal_execution(
        cfg, e13, ro_invoke_two_wal_event(),
    );
    t6_a0_extend_wal_execution(
        cfg, e14, ro_failure_two_wal_event(),
    )
}

pub open spec fn ro_wal_failure_outcome_execution()
    -> wal_runtime_layer::WalExecution
{
    t6_a0_append_full_wal_execution(
        ro_full_config(),
        ro_wal_retry_observed_execution(),
        ro_failure_outcome_record(),
    )
}

pub open spec fn ro_wal_execution()
    -> wal_runtime_layer::WalExecution
{
    t6_a0_append_full_wal_execution(
        ro_full_config(),
        ro_wal_failure_outcome_execution(),
        ro_fail_record(),
    )
}

pub open spec fn ro_adapter_pre_crash_execution()
    -> ROAdapterExecution
{
    let request = ro_request_zero();
    let cfg = ro_full_config();
    let w0 = t6_a0_zero_wal_execution(cfg);
    let a0 = ro_zero_adapter_execution(request, false);
    let a1 = ro_observe_full_append(
        a0,
        ro_authorize_record(),
        wal_runtime_layer::journal_view(w0.configs.last()).len() + 1,
    );
    let w1 = t6_a0_append_full_wal_execution(
        cfg, w0, ro_authorize_record(),
    );
    let a2 = ro_observe_full_append(
        a1,
        ro_prepare_record(),
        wal_runtime_layer::journal_view(w1.configs.last()).len() + 1,
    );
    let w2 = t6_a0_append_full_wal_execution(
        cfg, w1, ro_prepare_record(),
    );
    let a3 = ro_observe_full_append(
        a2,
        ro_arm_record(),
        wal_runtime_layer::journal_view(w2.configs.last()).len() + 1,
    );
    let w3 = t6_a0_append_full_wal_execution(
        cfg, w2, ro_arm_record(),
    );
    let a4 = ro_observe_full_append(
        a3,
        ro_start_one_record(),
        wal_runtime_layer::journal_view(w3.configs.last()).len() + 1,
    );
    let a5 = ro_observe_wal_event(a4, ro_invoke_one_wal_event());
    let a6 = ro_extend_adapter_execution(
        a5,
        ROAdapterEvent::ServiceRead { attempt: 1 },
    );
    ro_observe_wal_event(a6, ro_success_one_wal_event())
}

pub open spec fn ro_adapter_recovered_execution()
    -> ROAdapterExecution
{
    ro_observe_recovery(ro_adapter_pre_crash_execution())
}

pub open spec fn ro_adapter_retry_observed_execution()
    -> ROAdapterExecution
{
    let w12 = ro_wal_recovered_execution();
    let a8 = ro_adapter_recovered_execution();
    let a9 = ro_extend_adapter_execution(
        a8,
        ROAdapterEvent::EnvironmentSet { present: true },
    );
    let a10 = ro_observe_full_append(
        a9,
        ro_start_two_record(),
        wal_runtime_layer::journal_view(w12.configs.last()).len() + 1,
    );
    let a11 = ro_observe_wal_event(
        a10, ro_invoke_two_wal_event(),
    );
    ro_observe_wal_event(a11, ro_failure_two_wal_event())
}

pub open spec fn ro_adapter_failure_outcome_execution()
    -> ROAdapterExecution
{
    let w15 = ro_wal_retry_observed_execution();
    ro_observe_full_append(
        ro_adapter_retry_observed_execution(),
        ro_failure_outcome_record(),
        wal_runtime_layer::journal_view(w15.configs.last()).len() + 1,
    )
}

pub open spec fn ro_adapter_execution()
    -> ROAdapterExecution
{
    let cfg = ro_full_config();
    let a13 = ro_adapter_failure_outcome_execution();
    let w15 = ro_wal_retry_observed_execution();
    let w16 = t6_a0_append_full_wal_execution(
        cfg, w15, ro_failure_outcome_record(),
    );
    ro_observe_full_append(
        a13,
        ro_fail_record(),
        wal_runtime_layer::journal_view(w16.configs.last()).len() + 1,
    )
}

pub open spec fn ro_retry_history()
    -> Seq<p0_layer::PhysicalEvent>
{
    let cfg = ro_full_config();
    let request = ro_request_zero();
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
                ro_success_value(),
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

pub proof fn ro_authorize_is_runtime_enabled()
    ensures wal_runtime_layer::runtime_record_enabled(
        ro_full_config(),
        wal_runtime_layer::initial_configuration(ro_full_config()),
        ro_authorize_record(),
    ),
{
}

pub proof fn ro_wal_pre_crash_execution_exec()
    ensures
        wal_runtime_layer::exec(
            ro_full_config(), ro_wal_pre_crash_execution(),
        ),
        ro_wal_pre_crash_execution().events.len() == 14,
        ro_wal_pre_crash_execution().configs.last().runtime.mode
            == record_layer::Mode::Online,
        wal_runtime_layer::wal_quiescent(
            ro_wal_pre_crash_execution().configs.last(),
        ),
        wal_runtime_layer::journal_view(
            ro_wal_pre_crash_execution().configs.last(),
        ) == ro_records().take(4),
{
    let cfg = ro_full_config();
    let request = ro_request_zero();
    ro_full_config_is_well_formed();
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
    ro_authorize_is_runtime_enabled();
    let e1 = t6_a0_append_full_wal_execution(
        cfg, e0, ro_authorize_record(),
    );
    t6_a0_append_full_wal_execution_exec(
        cfg, e0, ro_authorize_record(),
    );
    assert(wal_runtime_layer::runtime_record_enabled(
        cfg, e1.configs.last(), ro_prepare_record(),
    ));
    let e2 = t6_a0_append_full_wal_execution(
        cfg, e1, ro_prepare_record(),
    );
    t6_a0_append_full_wal_execution_exec(
        cfg, e1, ro_prepare_record(),
    );
    assert(wal_runtime_layer::runtime_record_enabled(
        cfg, e2.configs.last(), ro_arm_record(),
    ));
    let e3 = t6_a0_append_full_wal_execution(
        cfg, e2, ro_arm_record(),
    );
    t6_a0_append_full_wal_execution_exec(
        cfg, e2, ro_arm_record(),
    );
    assert(wal_runtime_layer::runtime_record_enabled(
        cfg, e3.configs.last(), ro_start_one_record(),
    ));
    let e4 = t6_a0_append_full_wal_execution(
        cfg, e3, ro_start_one_record(),
    );
    t6_a0_append_full_wal_execution_exec(
        cfg, e3, ro_start_one_record(),
    );
    assert(e4.configs.last().runtime.slot
        == record_layer::ExecSlot::Ready { request, attempt: 1 });
    let invoke1 = ro_invoke_one_wal_event();
    let e5 = t6_a0_extend_wal_execution(cfg, e4, invoke1);
    assert(wal_runtime_layer::admissibly_enabled(
        cfg, e4.configs.last(), invoke1,
    ));
    t6_a0_extend_wal_execution_exec(cfg, e4, invoke1);
    assert(e5.configs.last().runtime.slot
        == record_layer::ExecSlot::InFlight { request, attempt: 1 });
    let success1 = ro_success_one_wal_event();
    let e6 = t6_a0_extend_wal_execution(cfg, e5, success1);
    assert(wal_runtime_layer::admissibly_enabled(
        cfg, e5.configs.last(), success1,
    ));
    t6_a0_extend_wal_execution_exec(cfg, e5, success1);
    assert(e6 == ro_wal_pre_crash_execution());
    assert(e6.configs.last().runtime.slot
        == record_layer::ExecSlot::Received {
            request,
            attempt: 1,
            observation: replay_layer::Observation::Success(
                ro_success_value(),
            ),
        });
    assert(wal_runtime_layer::journal_view(e6.configs.last())
        == ro_records().take(4));
}

proof fn ro_precrash_recovery_complete()
    ensures query_layer::recovery_complete_j(
        config_layer::erase_config(ro_full_config()),
        ro_records().take(4),
    ),
{
    let cfg = ro_full_config();
    let erased = config_layer::erase_config(cfg);
    let journal = ro_records().take(4);
    ro_full_config_is_well_formed();
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
            == replay_layer::RetryClass::ReadOnly);
        assert(!query_layer::unsafe_uncontrolled_j(
            erased, journal, request,
        ));
        if request == ro_request_zero() {
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

// The next Start record is enabled after recovery.  This is proved against
// the replay state rather than assumed from the concrete execution builder:
// the journal is armed, has one prior start, no outcome for attempt two, and
// the ReadOnly class permits another bounded attempt.
proof fn ro_start_two_runtime_enabled(
    cfg: config_layer::FullConfig,
    state: wal_runtime_layer::WalConfiguration,
)
    requires
        cfg == ro_full_config(),
        state.runtime.mode == record_layer::Mode::Online,
        state.runtime.slot == record_layer::ExecSlot::Idle,
        wal_runtime_layer::journal_view(state) == ro_precrash_records(),
    ensures
        wal_runtime_layer::runtime_record_enabled(
            cfg, state, ro_start_two_record(),
        ),
{
    let request = ro_request_zero();
    let erased = config_layer::erase_config(cfg);
    let journal = ro_precrash_records();
    ro_full_config_is_well_formed();
    assert(journal =~= Seq::empty()
        .push(ro_authorize_record())
        .push(ro_prepare_record())
        .push(ro_arm_record())
        .push(ro_start_one_record()));
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
    assert(replay_layer::outcome_observation(
        journal, request, 1,
    ) == Option::None);
    assert(!replay_layer::failure_conclusive(
        erased, journal, request,
    ));
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
        erased, journal, ro_start_two_record(),
    ));
    assert(record_layer::durable_slot_update(
        erased,
        replay_layer::replay(erased, journal),
        record_layer::Mode::Online,
        record_layer::ExecSlot::Idle,
        ro_start_two_record(),
    ).is_some());
}

pub proof fn ro_wal_recovered_execution_exec()
    ensures
        wal_runtime_layer::exec(
            ro_full_config(), ro_wal_recovered_execution(),
        ),
        ro_wal_recovered_execution().events.len() == 20,
        ro_wal_recovered_execution().configs.last().runtime.mode
            == record_layer::Mode::Online,
        wal_runtime_layer::wal_quiescent(
            ro_wal_recovered_execution().configs.last(),
        ),
        wal_runtime_layer::journal_view(
            ro_wal_recovered_execution().configs.last(),
        ) == ro_records().take(4),
{
    let cfg = ro_full_config();
    let e6 = ro_wal_pre_crash_execution();
    ro_wal_pre_crash_execution_exec();
    let crash = wal_runtime_layer::WalEvent::Crash;
    let e7 = t6_a0_extend_wal_execution(cfg, e6, crash);
    assert(wal_runtime_layer::admissibly_enabled(
        cfg, e6.configs.last(), crash,
    ));
    t6_a0_extend_wal_execution_exec(cfg, e6, crash);
    assert(wal_runtime_layer::journal_view(e7.configs.last())
        == ro_records().take(4));
    let scan = wal_runtime_layer::WalEvent::BeginScan;
    let e8 = t6_a0_extend_wal_execution(cfg, e7, scan);
    assert(wal_runtime_layer::admissibly_enabled(
        cfg, e7.configs.last(), scan,
    ));
    t6_a0_extend_wal_execution_exec(cfg, e7, scan);
    assert(wal_runtime_layer::journal_view(e8.configs.last())
        == ro_records().take(4));
    let finish_scan = wal_runtime_layer::WalEvent::FinishScan;
    let e9 = t6_a0_extend_wal_execution(
        cfg, e8, finish_scan,
    );
    assert(wal_runtime_layer::admissibly_enabled(
        cfg, e8.configs.last(), finish_scan,
    ));
    t6_a0_extend_wal_execution_exec(cfg, e8, finish_scan);
    assert(wal_runtime_layer::journal_view(e9.configs.last())
        == ro_records().take(4));
    let truncate = wal_runtime_layer::WalEvent::TruncateTail;
    let e10 = t6_a0_extend_wal_execution(cfg, e9, truncate);
    assert(wal_runtime_layer::admissibly_enabled(
        cfg, e9.configs.last(), truncate,
    ));
    t6_a0_extend_wal_execution_exec(cfg, e9, truncate);
    assert(e10.configs.last().runtime.store.media
        == wal_runtime_layer::full_frames(ro_records().take(4)));
    wal_runtime_layer::parse_full_frames(ro_records().take(4));
    assert(wal_runtime_layer::journal_view(e10.configs.last())
        == ro_records().take(4));
    let begin_recover = wal_runtime_layer::WalEvent::BeginRecover;
    let e11 = t6_a0_extend_wal_execution(
        cfg, e10, begin_recover,
    );
    assert(wal_runtime_layer::admissibly_enabled(
        cfg, e10.configs.last(), begin_recover,
    ));
    t6_a0_extend_wal_execution_exec(cfg, e10, begin_recover);
    assert(wal_runtime_layer::journal_view(e11.configs.last())
        == ro_records().take(4));
    let finish_recover = wal_runtime_layer::WalEvent::FinishRecover;
    ro_precrash_recovery_complete();
    assert(wal_runtime_layer::journal_view(e11.configs.last())
        == ro_records().take(4));
    assert(e11.configs.last().runtime.mode
        == record_layer::Mode::Recovering);
    assert(e11.configs.last().runtime.store.scan_phase
        == wal_runtime_layer::ScanPhase::Idle);
    assert(e11.configs.last().runtime.store.cache
        == ro_records().take(4));
    assert(e11.configs.last().runtime.store.acked_len == 4);
    assert(wal_runtime_layer::admissibly_enabled(
        cfg, e11.configs.last(), finish_recover,
    ));
    t6_a0_extend_wal_execution_exec(
        cfg, e11, finish_recover,
    );
    assert(ro_wal_recovered_execution().events.len() == 20);
    assert(ro_wal_recovered_execution().configs.len() == 21);
}

pub proof fn ro_wal_retry_observed_execution_exec()
    ensures
        wal_runtime_layer::exec(
            ro_full_config(), ro_wal_retry_observed_execution(),
        ),
        ro_wal_retry_observed_execution().events.len() == 25,
        ro_wal_retry_observed_execution().configs.last().runtime.mode
            == record_layer::Mode::Online,
        ro_wal_retry_observed_execution().configs.last().runtime.slot
            == (record_layer::ExecSlot::Received {
                request: ro_request_zero(),
                attempt: 2,
                observation: replay_layer::Observation::Failure,
            }),
        wal_runtime_layer::wal_quiescent(
            ro_wal_retry_observed_execution().configs.last(),
        ),
        wal_runtime_layer::journal_view(
            ro_wal_retry_observed_execution().configs.last(),
        ) == ro_records().take(5),
        ro_wal_retry_observed_execution().configs.last()
            .runtime.store.media
            == wal_runtime_layer::full_frames(ro_retry_started_records()),
        ro_wal_retry_observed_execution().configs.last().evidence.records
            == ro_retry_started_records(),
        ro_wal_retry_observed_execution().configs.last()
            .evidence.acknowledged_prefix == ro_retry_started_records(),
        ro_wal_retry_observed_execution().configs.last()
            .evidence.physical == ro_retry_history(),
{
    let cfg = ro_full_config();
    let e12 = ro_wal_recovered_execution();
    ro_wal_recovered_execution_exec();
    assert(ro_records().take(4) =~= ro_precrash_records());
    assert(wal_runtime_layer::journal_view(e12.configs.last())
        == ro_precrash_records());
    let start2 = ro_start_two_record();
    ro_start_two_runtime_enabled(cfg, e12.configs.last());
    let e13 = t6_a0_append_full_wal_execution(
        cfg, e12, start2,
    );
    t6_a0_append_full_wal_execution_exec(cfg, e12, start2);
    assert(e13.configs.last().runtime.slot
        == (record_layer::ExecSlot::Ready {
            request: ro_request_zero(),
            attempt: 2,
        }));
    assert(wal_runtime_layer::journal_view(e13.configs.last())
        == ro_retry_started_records());
    let invoke2 = ro_invoke_two_wal_event();
    let e14 = t6_a0_extend_wal_execution(
        cfg, e13, invoke2,
    );
    assert(wal_runtime_layer::admissibly_enabled(
        cfg, e13.configs.last(), invoke2,
    ));
    t6_a0_extend_wal_execution_exec(cfg, e13, invoke2);
    assert(e14.configs.last().runtime.slot
        == (record_layer::ExecSlot::InFlight {
            request: ro_request_zero(),
            attempt: 2,
        }));
    let failure2 = ro_failure_two_wal_event();
    assert(wal_runtime_layer::admissibly_enabled(
        cfg, e14.configs.last(), failure2,
    ));
    t6_a0_extend_wal_execution_exec(cfg, e14, failure2);
    let e15 = t6_a0_extend_wal_execution(cfg, e14, failure2);
    assert(e15.configs.last().runtime.slot
        == (record_layer::ExecSlot::Received {
            request: ro_request_zero(),
            attempt: 2,
            observation: replay_layer::Observation::Failure,
        }));
    assert(wal_runtime_layer::journal_view(e15.configs.last())
        == ro_retry_started_records());
    assert(e15.configs.last().evidence.physical
        == ro_retry_history());
    assert(e15.configs.last().runtime.store.media
        == wal_runtime_layer::full_frames(ro_retry_started_records()));
    assert(e15.configs.last().evidence.records
        == ro_retry_started_records());
    assert(e15.configs.last().evidence.acknowledged_prefix
        == ro_retry_started_records());
    assert(wal_runtime_layer::wal_quiescent(e15.configs.last()));
    assert(ro_wal_retry_observed_execution().events.len() == 25);
    assert(ro_wal_retry_observed_execution().configs.len() == 26);
}

pub proof fn ro_failure_outcome_runtime_enabled(
    cfg: config_layer::FullConfig,
    state: wal_runtime_layer::WalConfiguration,
)
    requires
        cfg == ro_full_config(),
        state.runtime.mode == record_layer::Mode::Online,
        state.runtime.slot
            == (record_layer::ExecSlot::Received {
                request: ro_request_zero(),
                attempt: 2,
                observation: replay_layer::Observation::Failure,
            }),
        wal_runtime_layer::journal_view(state)
            == ro_retry_started_records(),
    ensures
        wal_runtime_layer::runtime_record_enabled(
            cfg, state, ro_failure_outcome_record(),
        ),
{
    let request = ro_request_zero();
    let erased = config_layer::erase_config(cfg);
    let journal = ro_retry_started_records();
    ro_full_config_is_well_formed();
    assert(journal =~= Seq::empty()
        .push(ro_authorize_record())
        .push(ro_prepare_record())
        .push(ro_arm_record())
        .push(ro_start_one_record())
        .push(ro_start_two_record()));
    reveal_with_fuel(replay_layer::replay, 9);
    reveal_with_fuel(replay_layer::started_count, 9);
    reveal_with_fuel(replay_layer::outcome_count, 9);
    reveal_with_fuel(replay_layer::start_lsn, 9);
    assert(replay_layer::replay(erased, journal).phase[request]
        == replay_layer::Phase::Armed);
    assert(replay_layer::started_count(journal, request) == 2);
    assert(replay_layer::outcome_count(journal, request, 2) == 0);
    query_layer::outcome_count_zero_implies_no_observation(
        journal, request, 2,
    );
    assert(replay_layer::outcome_observation(
        journal, request, 2,
    ) == Option::None);
    assert(replay_layer::start_lsn(journal, request, 2)
        == Option::Some(5));
    assert(replay_layer::request_fields_match(
        erased,
        request,
        replay_layer::Digest { id: 0 },
        Option::None,
    ));
    assert(replay_layer::structural_enabled(
        erased, journal, ro_failure_outcome_record(),
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
        ro_failure_outcome_record(),
    ).is_some());
}

pub proof fn ro_fail_runtime_enabled(
    cfg: config_layer::FullConfig,
    state: wal_runtime_layer::WalConfiguration,
)
    requires
        cfg == ro_full_config(),
        state.runtime.mode == record_layer::Mode::Online,
        state.runtime.slot
            == (record_layer::ExecSlot::ObservedFailure {
                request: ro_request_zero(),
                attempt: 2,
            }),
        wal_runtime_layer::journal_view(state)
            == ro_failure_records(),
    ensures
        wal_runtime_layer::runtime_record_enabled(
            cfg, state, ro_fail_record(),
        ),
{
    let request = ro_request_zero();
    let erased = config_layer::erase_config(cfg);
    let journal = ro_failure_records();
    ro_full_config_is_well_formed();
    assert(journal =~= Seq::empty()
        .push(ro_authorize_record())
        .push(ro_prepare_record())
        .push(ro_arm_record())
        .push(ro_start_one_record())
        .push(ro_start_two_record())
        .push(ro_failure_outcome_record()));
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
    assert(replay_layer::outcome_observation(
        journal, request, 1,
    ) == Option::None);
    assert(replay_layer::outcome_observation(
        journal, request, 2,
    ) == Option::Some(replay_layer::Observation::Failure));
    assert(!replay_layer::all_attempts_failed(journal, request)) by {
        if replay_layer::all_attempts_failed(journal, request) {
            assert(replay_layer::outcome_observation(
                journal, request, 1,
            ) == Option::Some(replay_layer::Observation::Failure));
            assert(false);
        }
    }
    assert(erased.request_class[request]
        == replay_layer::RetryClass::ReadOnly);
    assert(replay_layer::failure_conclusive(
        erased, journal, request,
    ));
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
    assert(replay_layer::structural_enabled(
        erased, journal, ro_fail_record(),
    ));
    query_layer::replay_d_failure_conclusive_exact(
        erased, journal, request,
    );
    assert(query_layer::d_failure_conclusive(
        erased,
        replay_layer::replay(erased, journal),
        request,
    ));
    assert(record_layer::durable_slot_update(
        erased,
        replay_layer::replay(erased, journal),
        record_layer::Mode::Online,
        record_layer::ExecSlot::ObservedFailure {
            request,
            attempt: 2,
        },
        ro_fail_record(),
    ).is_some());
}

pub proof fn ro_wal_failure_outcome_execution_exec()
    ensures
        wal_runtime_layer::exec(
            ro_full_config(), ro_wal_failure_outcome_execution(),
        ),
        ro_wal_failure_outcome_execution().events.len() == 28,
        ro_wal_failure_outcome_execution().configs.len() == 29,
        ro_wal_failure_outcome_execution().configs.last().runtime.mode
            == record_layer::Mode::Online,
        ro_wal_failure_outcome_execution().configs.last().runtime.slot
            == (record_layer::ExecSlot::ObservedFailure {
                request: ro_request_zero(),
                attempt: 2,
            }),
        wal_runtime_layer::wal_quiescent(
            ro_wal_failure_outcome_execution().configs.last(),
        ),
        wal_runtime_layer::journal_view(
            ro_wal_failure_outcome_execution().configs.last(),
        ) == ro_failure_records(),
        ro_wal_failure_outcome_execution().configs.last()
            .runtime.store.media
            == wal_runtime_layer::full_frames(ro_failure_records()),
        ro_wal_failure_outcome_execution().configs.last().evidence.records
            == ro_failure_records(),
        ro_wal_failure_outcome_execution().configs.last()
            .evidence.acknowledged_prefix == ro_failure_records(),
        ro_wal_failure_outcome_execution().configs.last()
            .evidence.physical == ro_retry_history(),
{
    let cfg = ro_full_config();
    let e15 = ro_wal_retry_observed_execution();
    ro_wal_retry_observed_execution_exec();
    assert(wal_runtime_layer::journal_view(e15.configs.last())
        == ro_retry_started_records());
    assert(e15.configs.last().runtime.mode
        == record_layer::Mode::Online);
    assert(wal_runtime_layer::wal_quiescent(e15.configs.last()));
    ro_failure_outcome_runtime_enabled(cfg, e15.configs.last());
    t6_a0_append_full_wal_execution_exec(
        cfg, e15, ro_failure_outcome_record(),
    );
    let e16 = ro_wal_failure_outcome_execution();
    assert(e16.configs.last().runtime.slot
        == (record_layer::ExecSlot::ObservedFailure {
            request: ro_request_zero(),
            attempt: 2,
        }));
    assert(wal_runtime_layer::journal_view(e16.configs.last())
        == ro_failure_records());
    assert(e16.configs.last().runtime.store.media
        == wal_runtime_layer::full_frames(ro_failure_records()));
    assert(e16.configs.last().evidence.records
        == ro_failure_records());
    assert(e16.configs.last().evidence.acknowledged_prefix
        == ro_failure_records());
    assert(e16.configs.last().evidence.physical
        == ro_retry_history());
    assert(e16.events.len() == 28);
    assert(e16.configs.len() == 29);
}

pub proof fn ro_wal_execution_exec()
    ensures
        wal_runtime_layer::exec(
            ro_full_config(), ro_wal_execution(),
        ),
        ro_wal_execution().events.len() == 31,
        ro_wal_execution().configs.len() == 32,
        ro_wal_execution().configs.last().runtime.mode
            == record_layer::Mode::Online,
        ro_wal_execution().configs.last().runtime.slot
            == record_layer::ExecSlot::Idle,
        wal_runtime_layer::wal_quiescent(
            ro_wal_execution().configs.last(),
        ),
        wal_runtime_layer::journal_view(
            ro_wal_execution().configs.last(),
        ) == ro_records(),
        ro_wal_execution().configs.last().evidence.records
            == ro_records(),
        ro_wal_execution().configs.last().evidence.physical
            == ro_retry_history(),
{
    let cfg = ro_full_config();
    let e15 = ro_wal_retry_observed_execution();
    ro_wal_failure_outcome_execution_exec();
    let e16 = ro_wal_failure_outcome_execution();
    ro_fail_runtime_enabled(cfg, e16.configs.last());
    t6_a0_append_full_wal_execution_exec(
        cfg, e16, ro_fail_record(),
    );
    let final_state = ro_wal_execution().configs.last();
    assert(final_state.runtime.slot == record_layer::ExecSlot::Idle);
    assert(wal_runtime_layer::journal_view(final_state)
        == ro_records());
    assert(final_state.evidence.records == ro_records());
    assert(final_state.evidence.physical == ro_retry_history());
    assert(ro_wal_execution().events.len() == 31);
    assert(ro_wal_execution().configs.len() == 32);
}

pub proof fn ro_adapter_pre_crash_execution_exec()
    ensures
        ro_exec(
            ro_request_zero(),
            false,
            ro_adapter_pre_crash_execution(),
        ),
        ro_adapter_pre_crash_execution().configs.last().mode
            == ROAdapterMode::Online,
        ro_adapter_pre_crash_execution().configs.last().active.is_none(),
        ro_adapter_pre_crash_execution().configs.last().present == false,
        ro_adapter_pre_crash_execution().configs.last()
            .environment_updates == Seq::empty(),
        ro_adapter_pre_crash_execution().configs.last().samples
            == Seq::empty().push(ROReadSample {
                attempt: 1,
                present: false,
                environment_cut: 0,
                history_cut: 1,
            }),
        ro_adapter_pre_crash_execution().configs.last().history
            == ro_retry_history().take(2),
        ro_global_trace(ro_adapter_pre_crash_execution().events)
            == ro_wal_pre_crash_execution().events,
        ro_adapter_pre_crash_execution().events.len() == 15,
{
    let request = ro_request_zero();
    let cfg = ro_full_config();
    let w0 = t6_a0_zero_wal_execution(cfg);
    let a0 = ro_zero_adapter_execution(request, false);
    ro_zero_adapter_execution_exec(request, false);
    assert(ro_global_trace(a0.events) == w0.events);
    let cut1 = wal_runtime_layer::journal_view(
        w0.configs.last(),
    ).len() + 1;
    let a1 = ro_observe_full_append(
        a0, ro_authorize_record(), cut1,
    );
    let w1 = t6_a0_append_full_wal_execution(
        cfg, w0, ro_authorize_record(),
    );
    ro_observe_full_append_exec(
        request, false, a0, ro_authorize_record(), cut1,
    );
    assert(ro_global_trace(a1.events) == w1.events);
    let cut2 = wal_runtime_layer::journal_view(
        w1.configs.last(),
    ).len() + 1;
    let a2 = ro_observe_full_append(
        a1, ro_prepare_record(), cut2,
    );
    let w2 = t6_a0_append_full_wal_execution(
        cfg, w1, ro_prepare_record(),
    );
    ro_observe_full_append_exec(
        request, false, a1, ro_prepare_record(), cut2,
    );
    assert(ro_global_trace(a2.events) == w2.events);
    let cut3 = wal_runtime_layer::journal_view(
        w2.configs.last(),
    ).len() + 1;
    let a3 = ro_observe_full_append(
        a2, ro_arm_record(), cut3,
    );
    let w3 = t6_a0_append_full_wal_execution(
        cfg, w2, ro_arm_record(),
    );
    ro_observe_full_append_exec(
        request, false, a2, ro_arm_record(), cut3,
    );
    assert(ro_global_trace(a3.events) == w3.events);
    let cut4 = wal_runtime_layer::journal_view(
        w3.configs.last(),
    ).len() + 1;
    let a4 = ro_observe_full_append(
        a3, ro_start_one_record(), cut4,
    );
    let w4 = t6_a0_append_full_wal_execution(
        cfg, w3, ro_start_one_record(),
    );
    ro_observe_full_append_exec(
        request, false, a3, ro_start_one_record(), cut4,
    );
    assert(ro_global_trace(a4.events) == w4.events);
    assert(a4.configs.last().mode == ROAdapterMode::Online);
    assert(a4.configs.last().active.is_none());
    assert(a4.configs.last().history == Seq::empty());

    let invoke1 = ro_invoke_one_wal_event();
    let a5 = ro_observe_wal_event(a4, invoke1);
    let w5 = t6_a0_extend_wal_execution(cfg, w4, invoke1);
    assert(ro_enabled(
        a4.configs.last(),
        ROAdapterEvent::Observe {
            event: wal_runtime_layer::wal_encode(invoke1),
        },
    ));
    ro_observe_wal_event_exec(request, false, a4, invoke1);
    assert(ro_global_trace(a5.events) == w5.events);
    assert(a5.configs.last().mode == ROAdapterMode::Online);
    assert(a5.configs.last().active == Option::Some(1));
    reveal_with_fuel(p1_layer::invoke_count, 6);
    reveal_with_fuel(p1_layer::delivery_count, 6);
    assert(invoked(a5.configs.last().history, request, 1));
    assert(p1_layer::delivery_count(
        a5.configs.last().history, request, 1,
    ) == 0);
    assert(!ro_has_sample(a5.configs.last().samples, 1));
    assert(!a5.configs.last().failed_attempts.contains(1));

    let read1 = ROAdapterEvent::ServiceRead { attempt: 1 };
    let a6 = ro_extend_adapter_execution(a5, read1);
    reveal(ro_enabled);
    assert(ro_enabled(a5.configs.last(), read1));
    ro_extend_adapter_execution_exec(request, false, a5, read1);
    assert(a6.configs.last().samples
        == Seq::empty().push(ROReadSample {
            attempt: 1,
            present: false,
            environment_cut: 0,
            history_cut: 1,
        }));
    ro_has_sample_value_singleton(
        ROReadSample {
            attempt: 1,
            present: false,
            environment_cut: 0,
            history_cut: 1,
        },
        1,
        ro_success_value(),
    );

    let success1 = ro_success_one_wal_event();
    let a7 = ro_observe_wal_event(a6, success1);
    let w6 = t6_a0_extend_wal_execution(cfg, w5, success1);
    reveal(ro_observe_enabled);
    reveal(ro_has_sample_value);
    assert(ro_enabled(
        a6.configs.last(),
        ROAdapterEvent::Observe {
            event: wal_runtime_layer::wal_encode(success1),
        },
    ));
    ro_observe_wal_event_exec(request, false, a6, success1);
    assert(ro_global_trace(a7.events) == w6.events);
    assert(a7 == ro_adapter_pre_crash_execution());
    assert(w6 == ro_wal_pre_crash_execution());
    assert(a7.configs.last().history
        == ro_retry_history().take(2));
    assert(a7.configs.last().samples
        == Seq::empty().push(ROReadSample {
            attempt: 1,
            present: false,
            environment_cut: 0,
            history_cut: 1,
        }));
    assert(ro_global_trace(a7.events)
        == ro_wal_pre_crash_execution().events);
    assert(a7.events.len() == 15);
}

pub proof fn ro_adapter_recovered_execution_exec()
    ensures
        ro_exec(
            ro_request_zero(),
            false,
            ro_adapter_recovered_execution(),
        ),
        ro_adapter_recovered_execution().configs.last().mode
            == ROAdapterMode::Online,
        ro_adapter_recovered_execution().configs.last().active.is_none(),
        ro_adapter_recovered_execution().configs.last().present == false,
        ro_adapter_recovered_execution().configs.last()
            .environment_updates == Seq::empty(),
        ro_adapter_recovered_execution().configs.last().samples
            == Seq::empty().push(ROReadSample {
                attempt: 1,
                present: false,
                environment_cut: 0,
                history_cut: 1,
            }),
        ro_adapter_recovered_execution().configs.last().history
            == ro_retry_history().take(2),
        ro_global_trace(ro_adapter_recovered_execution().events)
            == ro_wal_recovered_execution().events,
        ro_adapter_recovered_execution().events.len() == 21,
{
    let request = ro_request_zero();
    let before = ro_adapter_pre_crash_execution();
    ro_adapter_pre_crash_execution_exec();
    ro_observe_recovery_exec(request, false, before);
    assert(ro_global_trace(
        ro_adapter_recovered_execution().events,
    ) == ro_wal_recovered_execution().events);
    assert(ro_adapter_recovered_execution().events.len() == 21);
    assert(ro_adapter_recovered_execution().configs.last().history
        == ro_retry_history().take(2));
    assert(ro_adapter_recovered_execution().configs.last().samples
        == Seq::empty().push(ROReadSample {
            attempt: 1,
            present: false,
            environment_cut: 0,
            history_cut: 1,
        }));
}

pub proof fn ro_adapter_retry_observed_execution_exec()
    ensures
        ro_exec(
            ro_request_zero(),
            false,
            ro_adapter_retry_observed_execution(),
        ),
        ro_adapter_retry_observed_execution().configs.last().mode
            == ROAdapterMode::Online,
        ro_adapter_retry_observed_execution().configs.last().active.is_none(),
        ro_adapter_retry_observed_execution().configs.last().present == true,
        ro_adapter_retry_observed_execution().configs.last()
            .environment_updates == Seq::empty().push(true),
        ro_adapter_retry_observed_execution().configs.last().samples
            == Seq::empty().push(ROReadSample {
                attempt: 1,
                present: false,
                environment_cut: 0,
                history_cut: 1,
            }),
        ro_adapter_retry_observed_execution().configs.last().history
            == ro_retry_history(),
        ro_adapter_retry_observed_execution().configs.last()
            .failed_attempts.contains(2),
        ro_global_trace(ro_adapter_retry_observed_execution().events)
            == ro_wal_retry_observed_execution().events,
        ro_adapter_retry_observed_execution().events.len() == 27,
{
    let request = ro_request_zero();
    let cfg = ro_full_config();
    let before = ro_adapter_recovered_execution();
    ro_adapter_recovered_execution_exec();
    let environment = ROAdapterEvent::EnvironmentSet {
        present: true,
    };
    let a9 = ro_extend_adapter_execution(before, environment);
    assert(ro_enabled(before.configs.last(), environment));
    ro_extend_adapter_execution_exec(
        request, false, before, environment,
    );
    assert(a9.configs.last().present == true);
    assert(a9.configs.last().environment_updates
        == Seq::empty().push(true));

    let w12 = ro_wal_recovered_execution();
    ro_wal_recovered_execution_exec();
    let cut5 = wal_runtime_layer::journal_view(
        w12.configs.last(),
    ).len() + 1;
    let a10 = ro_observe_full_append(
        a9, ro_start_two_record(), cut5,
    );
    ro_observe_full_append_exec(
        request, false, a9, ro_start_two_record(), cut5,
    );
    assert(a10.configs.last().present == true);
    assert(a10.configs.last().samples
        == Seq::empty().push(ROReadSample {
            attempt: 1,
            present: false,
            environment_cut: 0,
            history_cut: 1,
        }));
    assert(a10.configs.last().mode == ROAdapterMode::Online);
    assert(a10.configs.last().active.is_none());
    assert(a10.configs.last().history
        == ro_retry_history().take(2));
    reveal_with_fuel(p1_layer::invoke_count, 8);
    reveal_with_fuel(p1_layer::delivery_count, 8);
    assert(p1_layer::invoke_count(
        a10.configs.last().history, request, 2,
    ) == 0);
    assert(p1_layer::delivery_count(
        a10.configs.last().history, request, 2,
    ) == 0);

    let invoke2 = ro_invoke_two_wal_event();
    let a11 = ro_observe_wal_event(a10, invoke2);
    reveal(ro_enabled);
    reveal(ro_observe_enabled);
    assert(ro_enabled(
        a10.configs.last(),
        ROAdapterEvent::Observe {
            event: wal_runtime_layer::wal_encode(invoke2),
        },
    ));
    ro_observe_wal_event_exec(request, false, a10, invoke2);
    assert(a11.configs.last().active == Option::Some(2));
    assert(!ro_has_sample(a11.configs.last().samples, 2));
    assert(p1_layer::delivery_count(
        a11.configs.last().history, request, 2,
    ) == 0);

    let failure2 = ro_failure_two_wal_event();
    let a12 = ro_observe_wal_event(a11, failure2);
    reveal(ro_observe_enabled);
    assert(ro_enabled(
        a11.configs.last(),
        ROAdapterEvent::Observe {
            event: wal_runtime_layer::wal_encode(failure2),
        },
    ));
    ro_observe_wal_event_exec(request, false, a11, failure2);
    assert(a12 == ro_adapter_retry_observed_execution());
    assert(a12.configs.last().history == ro_retry_history());
    assert(a12.configs.last().failed_attempts.contains(2));
    assert(a12.configs.last().present == true);
    assert(ro_global_trace(a12.events)
        == ro_wal_retry_observed_execution().events);
    assert(a12.events.len() == 27);
}

pub proof fn ro_adapter_failure_outcome_execution_exec()
    ensures
        ro_exec(
            ro_request_zero(),
            false,
            ro_adapter_failure_outcome_execution(),
        ),
        ro_adapter_failure_outcome_execution().configs.len() == 31,
        ro_adapter_failure_outcome_execution().events.len() == 30,
        ro_adapter_failure_outcome_execution().configs.last().mode
            == ROAdapterMode::Online,
        ro_adapter_failure_outcome_execution().configs.last()
            .active.is_none(),
        ro_adapter_failure_outcome_execution().configs.last().present
            == true,
        ro_adapter_failure_outcome_execution().configs.last()
            .environment_updates == Seq::empty().push(true),
        ro_adapter_failure_outcome_execution().configs.last().samples
            == Seq::empty().push(ROReadSample {
                attempt: 1,
                present: false,
                environment_cut: 0,
                history_cut: 1,
            }),
        ro_adapter_failure_outcome_execution().configs.last().history
            == ro_retry_history(),
        ro_adapter_failure_outcome_execution().configs.last()
            .failed_attempts.contains(2),
        ro_global_trace(
            ro_adapter_failure_outcome_execution().events,
        ) == ro_wal_failure_outcome_execution().events,
{
    let request = ro_request_zero();
    let w15 = ro_wal_retry_observed_execution();
    let a12 = ro_adapter_retry_observed_execution();
    ro_adapter_retry_observed_execution_exec();
    ro_wal_retry_observed_execution_exec();
    let cut6 = wal_runtime_layer::journal_view(
        w15.configs.last(),
    ).len() + 1;
    ro_observe_full_append_exec(
        request,
        false,
        a12,
        ro_failure_outcome_record(),
        cut6,
    );
    let a13 = ro_adapter_failure_outcome_execution();
    assert(a13.configs.last().history == ro_retry_history());
    assert(a13.configs.last().present == true);
    assert(a13.configs.last().environment_updates
        == Seq::empty().push(true));
    assert(a13.configs.last().samples
        == Seq::empty().push(ROReadSample {
            attempt: 1,
            present: false,
            environment_cut: 0,
            history_cut: 1,
        }));
    assert(ro_global_trace(a13.events)
        == ro_wal_failure_outcome_execution().events);
    assert(a13.events.len() == 30);
    assert(a13.configs.len() == 31);
}

pub proof fn ro_adapter_final_fail_append_exec()
    requires
        ro_exec(
            ro_request_zero(),
            false,
            ro_adapter_failure_outcome_execution(),
        ),
    ensures
        ro_exec(
            ro_request_zero(),
            false,
            ro_adapter_execution(),
        ),
        ro_adapter_execution().events.len()
            == ro_adapter_failure_outcome_execution().events.len() + 3,
        ro_global_trace(ro_adapter_execution().events)
            == ro_global_trace(
                ro_adapter_failure_outcome_execution().events,
            )
                .push(global_layer::GlobalEvent::WalStage {
                    record: ro_fail_record(),
                })
                .push(global_layer::GlobalEvent::WalWriteFull {
                    record: ro_fail_record(),
                })
                .push(global_layer::GlobalEvent::WalFlushAck { cut: 7 }),
{
    let request = ro_request_zero();
    let w16 = ro_wal_failure_outcome_execution();
    ro_wal_failure_outcome_execution_exec();
    let cut7 = wal_runtime_layer::journal_view(
        w16.configs.last(),
    ).len() + 1;
    assert(cut7 == 7);
    ro_observe_full_append_exec(
        request,
        false,
        ro_adapter_failure_outcome_execution(),
        ro_fail_record(),
        cut7,
    );
}

pub proof fn ro_adapter_execution_exec()
    ensures
        ro_exec(
            ro_request_zero(),
            false,
            ro_adapter_execution(),
        ),
        ro_adapter_execution().events.len() == 33,
        ro_global_trace(ro_adapter_execution().events)
            == ro_wal_execution().events,
{
    ro_adapter_failure_outcome_execution_exec();
    ro_adapter_final_fail_append_exec();
    assert(ro_adapter_failure_outcome_execution().events.len() == 30);
    assert(ro_adapter_execution().events.len() == 33);
}

pub proof fn ro_adapter_final_present()
    ensures
        ro_adapter_execution().configs.last().present == true,
{
}

pub proof fn ro_adapter_final_environment_update()
    ensures
        ro_adapter_execution().configs.last().environment_updates
            == Seq::empty().push(true),
{
    let request = ro_request_zero();
    let before = ro_adapter_failure_outcome_execution();
    let w16 = ro_wal_failure_outcome_execution();
    ro_adapter_failure_outcome_execution_exec();
    ro_wal_failure_outcome_execution_exec();
    let cut7 = wal_runtime_layer::journal_view(
        w16.configs.last(),
    ).len() + 1;
    assert(cut7 == 7);
    ro_observe_full_append_preserves_adapter_state(
        request, false, before, ro_fail_record(), cut7,
    );
    assert(before.configs.last().environment_updates
        == Seq::empty().push(true));
}

pub proof fn ro_primitive_adapter_laws()
    ensures primitive_adapter_laws(ro_paper()),
{
    let paper = ro_paper();
    let cfg = ro_full_config();
    let adapter = ro_adapter();
    t1_layer::paper_broker_config_is_broker(paper);
    assert(t1_layer::paper_broker_config(paper) == cfg);
    assert forall|request: replay_layer::RequestId,
                  history: Seq<p0_layer::PhysicalEvent>,
                  run: ExternalRun<bool, ReadOnlyWitness>,
                  attempt: replay_layer::AttemptId,
                  value: replay_layer::Value| #![auto] {
        &&& adapter_rely_trace(paper, request, history, run)
        &&& commit_outcome_compatible(cfg, request, history, attempt, value)
    } implies {
        &&& (adapter.result_spec)(request, value, run)
        &&& (adapter.zero_effect)(request, run)
    } by {
        assert(adapter_rely_trace(paper, request, history, run));
        assert((adapter.env_rely)(request, history, run));
        assert(ro_env_rely(request, history, run));
        assert(ro_zero_effect(request, run));
        assert(delivered_observations_classified(
            cfg, adapter, history, request, run,
        ));
        assert(p1_layer::physical_unique(history));
        assert(delivery(history, request, attempt)
            == Option::Some(replay_layer::Observation::Success(value)));
        ro_selected_delivery_is_classified(
            cfg, history, request, attempt,
            replay_layer::Observation::Success(value), run,
        );
        assert(ro_has_sample_value(
            run.interference.samples, attempt, value,
        ));
        let index = choose|index: int|
            0 <= index < run.interference.samples.len()
                && run.interference.samples[index].attempt == attempt
                && value == ro_result_value(
                    run.interference.samples[index].present,
                );
        assert(ro_result_spec(request, value, run)) by {
            assert(exists|selected: int|
                0 <= selected < run.interference.samples.len()
                    && value == ro_result_value(
                        run.interference.samples[selected].present,
                    )) by {
                let selected = index;
            }
        }
        assert((adapter.result_spec)(request, value, run));
        assert((adapter.zero_effect)(request, run));
    }
    assert forall|request: replay_layer::RequestId,
                  history: Seq<p0_layer::PhysicalEvent>,
                  run: ExternalRun<bool, ReadOnlyWitness>,
                  attempt: replay_layer::AttemptId| #![auto] {
        &&& adapter_rely_trace(paper, request, history, run)
        &&& fail_outcome_compatible(cfg, request, history, attempt)
    } implies (adapter.zero_effect)(request, run) by {
        assert(ro_env_rely(request, history, run));
        assert(ro_zero_effect(request, run));
    }
    assert forall|request: replay_layer::RequestId,
                  history: Seq<p0_layer::PhysicalEvent>,
                  run: ExternalRun<bool, ReadOnlyWitness>| #![auto]
        adapter_rely_trace(paper, request, history, run) implies {
            ||| (adapter.zero_effect)(request, run)
            ||| (adapter.one_effect)(request, run)
        } by {
        assert(ro_env_rely(request, history, run));
        assert(ro_zero_effect(request, run));
    }
}

pub proof fn ro_adapter_is_verified()
    ensures adapter_verified(ro_paper()),
{
    ro_primitive_adapter_laws();
    t6_d0_layer::primitive_adapter_laws_imply_verified(ro_paper());
}

pub open spec fn ro_retry_run()
    -> ExternalRun<bool, ReadOnlyWitness>
{
    ro_external_run(ro_adapter_execution().configs.last())
}

pub open spec fn ro_terminal_outcome() -> TerminalOutcome {
    TerminalOutcome::Fail { attempt: 2 }
}

pub proof fn ro_records_select_terminal_record()
    ensures
        terminal_record(
            ro_records(), ro_request_zero(),
        ) == Option::Some(IndexedTerminalRecord {
            lsn: 7,
            record: ro_fail_record(),
        }),
{
    reveal_with_fuel(replay_layer::terminal_count, 10);
    reveal_with_fuel(latest_terminal_record, 10);
    assert(ro_records().len() == 7);
    assert(ro_records().last() == ro_fail_record());
}

pub proof fn ro_records_select_terminal_fail()
    ensures
        terminal_from_records(
            ro_records(), ro_request_zero(),
        ) == Option::Some(ro_terminal_outcome()),
{
    ro_records_select_terminal_record();
    assert(terminal_outcome_of_record(
        ro_fail_record(), ro_request_zero(),
    ) == Option::Some(ro_terminal_outcome()));
}

pub proof fn ro_retry_history_has_mixed_outcomes()
    ensures
        invoked(ro_retry_history(), ro_request_zero(), 1),
        delivery(
            ro_retry_history(), ro_request_zero(), 1,
        ) == Option::Some(replay_layer::Observation::Success(
            ro_success_value(),
        )),
        delivery(
            ro_retry_history(), ro_request_zero(), 2,
        ) == Option::Some(replay_layer::Observation::Failure),
        !all_invocations_failed(
            ro_retry_history(), ro_request_zero(),
        ),
{
    let history = ro_retry_history();
    let request = ro_request_zero();
    reveal_with_fuel(p1_layer::invoke_count, 6);
    reveal_with_fuel(p1_layer::delivery_count, 6);
    reveal_with_fuel(latest_delivery_observation, 6);
    assert(invoked(history, request, 1));
    assert(delivery(history, request, 1)
        == Option::Some(replay_layer::Observation::Success(
            ro_success_value(),
        )));
    assert(delivery(history, request, 2)
        == Option::Some(replay_layer::Observation::Failure));
    if all_invocations_failed(history, request) {
        assert(delivery(history, request, 1)
            == Option::Some(replay_layer::Observation::Failure));
        assert(false);
    }
}

pub proof fn ro_wal_trace_shape()
    ensures
        projection_layer::pi_journal(
            ro_wal_execution().events,
        ) == ro_records(),
        projection_layer::pi_physical(
            ro_wal_execution().events,
        ) == ro_retry_history(),
        projection_layer::pi_adapter(
            ro_wal_execution().events,
            ro_request_zero(),
        ) == ro_retry_history(),
        terminal(
            ro_wal_execution().events,
            ro_request_zero(),
        ) == Option::Some(ro_terminal_outcome()),
{
    let cfg = ro_full_config();
    let source = ro_wal_execution();
    let length = source.events.len();
    let final_state = source.configs[length as int];
    ro_wal_execution_exec();
    wal_trace_layer::trace_agreement_for_exec(cfg, source);
    assert(wal_trace_layer::trace_agreement_at(
        cfg, source, length,
    ));
    assert(wal_trace_layer::prefix_events(source, length)
        == source.events);
    assert(final_state.evidence.records
        == projection_layer::pi_journal(source.events));
    assert(final_state.evidence.physical
        == projection_layer::pi_physical(source.events));
    assert(projection_layer::pi_journal(source.events)
        == ro_records());
    assert(projection_layer::pi_physical(source.events)
        == ro_retry_history());
    reveal_with_fuel(projection_layer::adapter_from_physical, 6);
    assert(projection_layer::pi_adapter(
        source.events, ro_request_zero(),
    ) == ro_retry_history());
    ro_records_select_terminal_fail();
    ro_retry_history_has_mixed_outcomes();
}

pub proof fn ro_failure_records_conclusive()
    ensures replay_layer::failure_conclusive(
        config_layer::erase_config(ro_full_config()),
        ro_failure_records(),
        ro_request_zero(),
    ),
{
    let cfg = ro_full_config();
    let erased = config_layer::erase_config(cfg);
    let journal = ro_failure_records();
    let request = ro_request_zero();
    ro_full_config_is_well_formed();
    reveal_with_fuel(replay_layer::replay, 10);
    reveal_with_fuel(replay_layer::started_count, 10);
    reveal_with_fuel(replay_layer::outcome_count, 10);
    reveal_with_fuel(replay_layer::outcome_observation, 10);
    assert(replay_layer::started_count(journal, request) == 2);
    assert(replay_layer::outcome_observation(
        journal, request, 2,
    ) == Option::Some(replay_layer::Observation::Failure));
    assert(erased.request_class[request]
        == replay_layer::RetryClass::ReadOnly);
    assert(replay_layer::failure_conclusive(
        erased, journal, request,
    ));
}

pub proof fn ro_nonconclusive_unknown_disabled()
    ensures
        replay_layer::failure_conclusive(
            config_layer::erase_config(ro_full_config()),
            ro_records(),
            ro_request_zero(),
        ),
        !replay_layer::unknown_enabled(
            config_layer::erase_config(ro_full_config()),
            ro_records(),
            ro_request_zero(),
            Option::Some(2),
            replay_layer::UnknownReason::NonConclusiveFailure,
            6,
        ),
{
    let cfg = ro_full_config();
    let erased = config_layer::erase_config(cfg);
    let request = ro_request_zero();
    let prefix = ro_failure_records();
    ro_failure_records_conclusive();
    assert(!replay_layer::touches_attempt(
        ro_fail_record(), request,
    ));
    replay_layer::attempt_evidence_stutters(
        erased, prefix, ro_fail_record(), request,
    );
    assert(ro_records() =~= prefix.push(ro_fail_record()));
    assert(replay_layer::failure_conclusive(
        erased, ro_records(), request,
    ));
    assert(!replay_layer::unknown_enabled(
        erased, ro_records(), request,
        Option::Some(2),
        replay_layer::UnknownReason::NonConclusiveFailure,
        6,
    )) by {
        reveal(replay_layer::unknown_enabled);
        assert(replay_layer::failure_conclusive(
            erased, ro_records(), request,
        ));
    }
}

pub open spec fn ro_broker_execution()
    -> execution_layer::BrokerExecution
{
    t4_c0_layer::canonical_target_execution(
        ro_full_config(), ro_wal_execution(),
    )
}

pub open spec fn ro_final_broker() -> p0_layer::State {
    let target = ro_broker_execution();
    target.configs[target.events.len() as int]
}

pub proof fn ro_adapter_verified_instance()
    ensures adapter_verified(ro_paper()),
{
    ro_adapter_is_verified();
}

pub proof fn ro_wal_closed_representation()
    ensures
        t1_layer::paper_config_wf(ro_paper()),
        wal_runtime_layer::exec(
            ro_full_config(), ro_wal_execution(),
        ),
        wal_trace_layer::admissible_wal_trace(
            ro_full_config(), ro_wal_execution(),
        ),
        wal_trace_layer::trace_agreement(
            ro_full_config(), ro_wal_execution(),
        ),
        t4_c0_layer::wal_broker_representation(
            ro_full_config(),
            ro_wal_execution().configs[
                ro_wal_execution().events.len() as int
            ],
            ro_final_broker(),
        ),
        terminal(
            ro_wal_execution().events,
            ro_request_zero(),
        ) == Option::Some(ro_terminal_outcome()),
{
    ro_full_config_is_well_formed();
    ro_wal_execution_exec();
    ro_wal_trace_shape();
    wal_trace_layer::exec_implies_admissible_wal_trace(
        ro_full_config(), ro_wal_execution(),
    );
    wal_trace_layer::trace_agreement_for_exec(
        ro_full_config(), ro_wal_execution(),
    );
    t4_c0_layer::canonical_closed_wal_broker_composition(
        ro_full_config(), ro_wal_execution(),
    );
}

pub proof fn ro_adapter_rely_on_wal()
    ensures adapter_rely(
        ro_paper(),
        ro_wal_execution().events,
        ro_request_zero(),
        ro_retry_run(),
    ),
{
    let adapter = ro_adapter_execution();
    let request = ro_request_zero();
    let final_adapter = adapter.configs[
        adapter.events.len() as int
    ];
    ro_adapter_execution_exec();
    ro_exec_derives_adapter_rely(request, false, adapter);
    ro_exec_final_globals_are_projected(request, false, adapter);
    assert(adapter.configs.len() == adapter.events.len() + 1);
    assert(final_adapter == adapter.configs.last());
    assert(ro_retry_run() == ro_external_run(final_adapter));
    assert(final_adapter.globals == ro_global_trace(adapter.events));
    assert(ro_global_trace(adapter.events)
        == ro_wal_execution().events);
    assert(adapter_rely(
        ro_paper(), final_adapter.globals, request,
        ro_external_run(final_adapter),
    ));
    assert(adapter_rely(
        ro_paper(), ro_wal_execution().events, request,
        ro_retry_run(),
    ));
}

pub proof fn ro_concrete_zero_effect()
    ensures ro_zero_effect(
        ro_request_zero(), ro_retry_run(),
    ),
{
    let adapter = ro_adapter_execution();
    let final_state = adapter.configs[
        adapter.events.len() as int
    ];
    ro_adapter_execution_exec();
    ro_adapter_final_present();
    ro_adapter_final_environment_update();
    assert(adapter.configs.len() == adapter.events.len() + 1);
    assert(final_state == adapter.configs.last());
    assert(ro_retry_run() == ro_external_run(final_state));
    assert(ro_zero_effect(
        ro_request_zero(), ro_external_run(final_state),
    ));
}

pub proof fn ro_concrete_refines()
    ensures refines(
        ro_paper(),
        ro_request_zero(),
        projection_layer::pi_adapter(
            ro_wal_execution().events,
            ro_request_zero(),
        ),
        ro_retry_run(),
        ro_terminal_outcome(),
    ),
{
    let paper = ro_paper();
    let events = ro_wal_execution().events;
    let request = ro_request_zero();
    let run = ro_retry_run();
    let outcome = ro_terminal_outcome();
    ro_adapter_rely_on_wal();
    ro_wal_trace_shape();
    ro_concrete_zero_effect();
    adapter_rely_is_projected_rely(
        paper, events, request, run,
    );
    assert(adapter_rely(
        paper, events, request, run,
    ) == adapter_rely_trace(
        paper, request,
        projection_layer::pi_adapter(events, request),
        run,
    ));
    assert(delivery(
        projection_layer::pi_adapter(events, request),
        request,
        2,
    ) == Option::Some(replay_layer::Observation::Failure));
    assert(ro_zero_effect(request, run));
    assert(refines(
        paper, request,
        projection_layer::pi_adapter(events, request),
        run, outcome,
    ));
}

pub proof fn ro_concrete_effect_refines()
    ensures per_request_effect_refinement(
        ro_paper(),
        ro_wal_execution().events,
        ro_request_zero(),
        ro_retry_run(),
    ),
{
    ro_concrete_refines();
    ro_wal_trace_shape();
    assert(terminal(
        ro_wal_execution().events,
        ro_request_zero(),
    ) == Option::Some(ro_terminal_outcome()));
    assert(per_request_effect_refinement(
        ro_paper(),
        ro_wal_execution().events,
        ro_request_zero(),
        ro_retry_run(),
    ));
}

// Concrete paper-facing refinement for the read-only witness.  The theorem
// deliberately stops at the WAL/Broker boundary: ServiceRead and
// EnvironmentSet are adapter-local events that stutter in the global trace,
// so a deployment-level service/transport refinement remains a separate
// obligation.
pub proof fn ro_wal_terminal_refines()
    ensures
        terminal(
            ro_wal_execution().events,
            ro_request_zero(),
        ) == Option::Some(ro_terminal_outcome()),
        refines(
            ro_paper(),
            ro_request_zero(),
            projection_layer::pi_adapter(
                ro_wal_execution().events,
                ro_request_zero(),
            ),
            ro_retry_run(),
            ro_terminal_outcome(),
        ),
        per_request_effect_refinement(
            ro_paper(),
            ro_wal_execution().events,
            ro_request_zero(),
            ro_retry_run(),
        ),
{
    let paper = ro_paper();
    let cfg = ro_full_config();
    let wal = ro_wal_execution();
    let adapter = ro_adapter_execution();
    let request = ro_request_zero();
    let run = ro_retry_run();
    let outcome = ro_terminal_outcome();
    let broker = ro_final_broker();
    ro_wal_closed_representation();
    ro_adapter_verified_instance();
    ro_concrete_refines();
    ro_concrete_effect_refines();
    assert(terminal(wal.events, request)
        == Option::Some(outcome));
    assert(refines(
        paper,
        request,
        projection_layer::pi_adapter(wal.events, request),
        run,
        outcome,
    ));
    assert(per_request_effect_refinement(
        paper, wal.events, request, run,
    ));
}

pub closed spec fn ro_executable_crash_retry_operational_package() -> bool {
    let adapter = ro_adapter_execution();
    let wal = ro_wal_execution();
    let request = ro_request_zero();
    &&& ro_exec(request, false, adapter)
    &&& wal_runtime_layer::exec(ro_full_config(), wal)
    &&& adapter.events.len() == 33
    &&& wal.events.len() == 31
    &&& ro_global_trace(adapter.events) == wal.events
    &&& projection_layer::pi_physical(wal.events)
        == ro_retry_history()
}

pub closed spec fn ro_executable_crash_retry_semantic_package() -> bool {
    let wal = ro_wal_execution();
    let request = ro_request_zero();
    &&& terminal(wal.events, request)
        == Option::Some(ro_terminal_outcome())
    &&& refines(
        ro_paper(),
        request,
        projection_layer::pi_adapter(wal.events, request),
        ro_retry_run(),
        ro_terminal_outcome(),
    )
    &&& per_request_effect_refinement(
        ro_paper(), wal.events, request, ro_retry_run(),
    )
    &&& !all_invocations_failed(
        ro_retry_history(), request,
    )
    &&& replay_layer::failure_conclusive(
        config_layer::erase_config(ro_full_config()),
        ro_records(), request,
    )
    &&& !replay_layer::unknown_enabled(
        config_layer::erase_config(ro_full_config()),
        ro_records(),
        request,
        Option::Some(2),
        replay_layer::UnknownReason::NonConclusiveFailure,
        6,
    )
}

pub closed spec fn ro_executable_crash_retry_package() -> bool {
    ro_executable_crash_retry_operational_package()
        && ro_executable_crash_retry_semantic_package()
}

pub proof fn ro_concrete_operational_package()
    ensures ro_executable_crash_retry_operational_package(),
{
    let adapter = ro_adapter_execution();
    let wal = ro_wal_execution();
    let request = ro_request_zero();
    ro_adapter_execution_exec();
    ro_wal_execution_exec();
    ro_wal_trace_shape();
    assert(ro_exec(request, false, adapter));
    assert(wal_runtime_layer::exec(ro_full_config(), wal));
    assert(adapter.events.len() == 33);
    assert(wal.events.len() == 31);
    assert(ro_global_trace(adapter.events) == wal.events);
    assert(projection_layer::pi_physical(wal.events)
        == ro_retry_history());
    reveal(ro_executable_crash_retry_operational_package);
}

pub proof fn ro_concrete_semantic_package()
    ensures ro_executable_crash_retry_semantic_package(),
{
    let wal = ro_wal_execution();
    let request = ro_request_zero();
    ro_wal_terminal_refines();
    ro_nonconclusive_unknown_disabled();
    ro_retry_history_has_mixed_outcomes();
    assert(terminal(wal.events, request)
        == Option::Some(ro_terminal_outcome()));
    assert(refines(
        ro_paper(),
        request,
        projection_layer::pi_adapter(wal.events, request),
        ro_retry_run(),
        ro_terminal_outcome(),
    ));
    assert(per_request_effect_refinement(
        ro_paper(), wal.events, request, ro_retry_run(),
    ));
    assert(!all_invocations_failed(
        ro_retry_history(), request,
    ));
    assert(replay_layer::failure_conclusive(
        config_layer::erase_config(ro_full_config()),
        ro_records(), request,
    ));
    assert(!replay_layer::unknown_enabled(
        config_layer::erase_config(ro_full_config()),
        ro_records(),
        request,
        Option::Some(2),
        replay_layer::UnknownReason::NonConclusiveFailure,
        6,
    ));
    reveal(ro_executable_crash_retry_semantic_package);
}

pub proof fn t6_ro0_executable_crash_retry_nonvacuity()
    ensures ro_executable_crash_retry_package(),
{
    ro_concrete_operational_package();
    ro_concrete_semantic_package();
    reveal(ro_executable_crash_retry_package);
    assert(ro_executable_crash_retry_operational_package());
    assert(ro_executable_crash_retry_semantic_package());
}

} // verus!
