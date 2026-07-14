use vstd::prelude::*;

#[path = "t2_representation.rs"]
pub mod representation_layer;

verus! {

use representation_layer::event_layer;
use event_layer::trace_layer;
use trace_layer::runtime_layer;
use runtime_layer::t1_layer;
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
use query_layer::c1_layer::replay_layer;

// T2 is lockstep for the atomic Journal, but the witness is packaged using a
// general nondecreasing prefix-index map so T3 can later reuse the definition
// for internal WAL stutters.
pub struct WeakIndexMap {
    pub points: Seq<nat>,
}

pub open spec fn identity_index_map(length: nat) -> WeakIndexMap {
    WeakIndexMap {
        points: Seq::new((length + 1) as nat, |index: int| index as nat),
    }
}

// Backend-independent arithmetic spine for a weak simulation.  Each source
// step contributes either zero or one target step.  T3 can reuse this shape
// with its own WAL-to-Journal event match and representation predicates.
pub open spec fn weak_index_shape(
    source_length: nat,
    target_length: nat,
    map: WeakIndexMap,
) -> bool {
    &&& map.points.len() == source_length + 1
    &&& map.points[0] == 0
    &&& map.points[source_length as int] == target_length
    &&& forall|index: nat| index < source_length ==> {
        let left = #[trigger] map.points[index as int];
        let right = map.points[(index + 1) as int];
        &&& left <= right
        &&& right <= target_length
        &&& (right == left || right == left + 1)
    }
}

pub open spec fn lift_configurations(
    cfg: config_layer::FullConfig,
    configs: Seq<runtime_layer::JournalConfiguration>,
) -> Seq<p0_layer::State> {
    Seq::new(configs.len(), |index: int|
        representation_layer::abstract_broker_state(cfg, configs[index]))
}

pub open spec fn lift_execution(
    cfg: config_layer::FullConfig,
    source: runtime_layer::JournalExecution,
) -> execution_layer::BrokerExecution {
    execution_layer::BrokerExecution {
        configs: lift_configurations(cfg, source.configs),
        events: event_layer::translate_trace(source.events),
    }
}

pub open spec fn related_prefixes(
    cfg: config_layer::FullConfig,
    source: runtime_layer::JournalExecution,
    target: execution_layer::BrokerExecution,
    map: WeakIndexMap,
) -> bool {
    forall|index: nat| index < source.configs.len() ==> {
        &&& index < map.points.len()
        &&& #[trigger] map.points[index as int] < target.configs.len()
        &&& representation_layer::representation(
            cfg,
            source.configs[index as int],
            target.configs[map.points[index as int] as int],
        )
    }
}

pub open spec fn related_prefix_projections(
    source: runtime_layer::JournalExecution,
    target: execution_layer::BrokerExecution,
    map: WeakIndexMap,
) -> bool {
    forall|index: nat| index <= source.events.len() ==> {
        &&& index < map.points.len()
        &&& map.points[index as int] <= target.events.len()
        &&& #[trigger] event_layer::t2_projection_agreement(
            source.events.take(index as int),
            target.events.take(map.points[index as int] as int),
        )
    }
}

pub open spec fn weak_simulation_index_map(
    cfg: config_layer::FullConfig,
    source: runtime_layer::JournalExecution,
    target: execution_layer::BrokerExecution,
    map: WeakIndexMap,
) -> bool {
    &&& weak_index_shape(
        source.events.len(), target.events.len(), map,
    )
    &&& forall|index: nat| index < source.events.len() ==> {
        let left = #[trigger] map.points[index as int];
        let right = map.points[(index + 1) as int];
        &&& if left == right {
            event_layer::t2_projection_silent(source.events[index as int])
        } else {
            &&& right == left + 1
            &&& left < target.events.len()
            &&& event_layer::event_match(
                source.events[index as int],
                target.events[left as int],
            )
        }
    }
    &&& related_prefixes(cfg, source, target, map)
    &&& related_prefix_projections(source, target, map)
}

pub open spec fn t2_simulation_statement(
    cfg: config_layer::FullConfig,
    source: runtime_layer::JournalExecution,
) -> bool {
    exists|target: execution_layer::BrokerExecution, map: WeakIndexMap| {
        &&& execution_layer::exec(cfg, target)
        &&& weak_simulation_index_map(cfg, source, target, map)
        &&& event_layer::t2_projection_agreement(
            source.events, target.events,
        )
    }
}

pub proof fn runtime_record_enabled_refines_abstract(
    cfg: config_layer::FullConfig,
    state: runtime_layer::JournalConfiguration,
    record: replay_layer::JournalRecord,
)
    requires
        config_layer::full_config_wf(cfg),
        runtime_layer::basic_invariant(cfg, state),
        runtime_layer::runtime_record_enabled(cfg, state, record),
    ensures record_layer::abstract_enabled(
        config_layer::erase_config(cfg),
        representation_layer::abstract_broker_state(cfg, state).core.broker,
        record,
    ),
{
    let erased = config_layer::erase_config(cfg);
    config_layer::erasure_is_replay_well_formed(cfg);
    query_layer::structural_enabled_implies_abstract_record_enabled(
        erased, runtime_layer::journal_view(state), record,
    );
}

pub proof fn local_control_refines(
    cfg: config_layer::FullConfig,
    state: runtime_layer::JournalConfiguration,
    event: runtime_layer::JournalEvent,
)
    requires
        config_layer::full_config_wf(cfg),
        runtime_layer::basic_invariant(cfg, state),
        runtime_layer::control_enabled(cfg, state, event),
    ensures p0_layer::control_enabled(
        cfg,
        representation_layer::abstract_broker_state(cfg, state),
        event_layer::journal_local_to_broker(event),
    ),
{
    match event {
        runtime_layer::JournalEvent::JournalAppendCall { record }
        | runtime_layer::JournalEvent::JournalAppendLinearize { record }
        | runtime_layer::JournalEvent::JournalDiskFull { record, .. } => {
            runtime_record_enabled_refines_abstract(cfg, state, record);
        },
        runtime_layer::JournalEvent::FinishRecover => {
            config_layer::erasure_is_replay_well_formed(cfg);
            query_layer::replay_recovery_predicates_exact(
                config_layer::erase_config(cfg),
                runtime_layer::journal_view(state),
            );
        },
        runtime_layer::JournalEvent::JournalAppendReturn { .. }
        | runtime_layer::JournalEvent::InvokeEvent { .. }
        | runtime_layer::JournalEvent::DeliverEvent { .. }
        | runtime_layer::JournalEvent::IgnoreStale { .. }
        | runtime_layer::JournalEvent::RetryRelease { .. }
        | runtime_layer::JournalEvent::Crash
        | runtime_layer::JournalEvent::BeginRecover => {},
    }
}

pub proof fn local_evidence_refines(
    cfg: config_layer::FullConfig,
    state: runtime_layer::JournalConfiguration,
    event: runtime_layer::JournalEvent,
)
    requires
        runtime_layer::basic_invariant(cfg, state),
        runtime_layer::control_enabled(cfg, state, event),
        runtime_layer::evidence_admissible(state, event),
    ensures p0_layer::evidence_admissible(
        cfg,
        representation_layer::abstract_broker_state(cfg, state),
        event_layer::journal_local_to_broker(event),
    ),
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

pub proof fn local_apply_commutes(
    cfg: config_layer::FullConfig,
    state: runtime_layer::JournalConfiguration,
    event: runtime_layer::JournalEvent,
)
    ensures representation_layer::abstract_broker_state(
        cfg, runtime_layer::apply(cfg, state, event),
    ) == p0_layer::apply(
        cfg,
        representation_layer::abstract_broker_state(cfg, state),
        event_layer::journal_local_to_broker(event),
    ),
{
    match event {
        runtime_layer::JournalEvent::JournalAppendLinearize { record } => {
            replay_layer::replay_push(
                config_layer::erase_config(cfg),
                runtime_layer::journal_view(state),
                record,
            );
        },
        runtime_layer::JournalEvent::JournalAppendCall { .. }
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

pub proof fn journal_local_step_simulates_broker(
    cfg: config_layer::FullConfig,
    before: runtime_layer::JournalConfiguration,
    source_event: global_layer::GlobalEvent,
    local: runtime_layer::JournalEvent,
    after: runtime_layer::JournalConfiguration,
)
    requires
        config_layer::full_config_wf(cfg),
        runtime_layer::basic_invariant(cfg, before),
        runtime_layer::journal_decode(source_event) == Option::Some(local),
        runtime_layer::journal_local_step(cfg, before, local, after),
    ensures execution_layer::broker_step(
        cfg,
        representation_layer::abstract_broker_state(cfg, before),
        event_layer::journal_to_broker_event(source_event),
        representation_layer::abstract_broker_state(cfg, after),
    ),
{
    assert(runtime_layer::control_enabled(cfg, before, local));
    assert(runtime_layer::evidence_admissible(before, local));
    assert(after == runtime_layer::apply(cfg, before, local));
    local_control_refines(cfg, before, local);
    local_evidence_refines(cfg, before, local);
    local_apply_commutes(cfg, before, local);
    event_layer::translated_decoded_event_is_broker_event(source_event, local);
    let broker_local = event_layer::journal_local_to_broker(local);
    assert(p0_layer::admissibly_enabled(
        cfg,
        representation_layer::abstract_broker_state(cfg, before),
        broker_local,
    ));
    assert(representation_layer::abstract_broker_state(cfg, after)
        == p0_layer::apply(
            cfg,
            representation_layer::abstract_broker_state(cfg, before),
            broker_local,
        ));
}

pub proof fn journal_runtime_step_simulates_broker(
    cfg: config_layer::FullConfig,
    before: runtime_layer::JournalConfiguration,
    source_event: global_layer::GlobalEvent,
    after: runtime_layer::JournalConfiguration,
)
    requires
        config_layer::full_config_wf(cfg),
        runtime_layer::basic_invariant(cfg, before),
        runtime_layer::journal_runtime_step(
            cfg, before, source_event, after,
        ),
    ensures execution_layer::broker_step(
        cfg,
        representation_layer::abstract_broker_state(cfg, before),
        event_layer::journal_to_broker_event(source_event),
        representation_layer::abstract_broker_state(cfg, after),
    ),
{
    match runtime_layer::journal_decode(source_event) {
        Option::None => {},
        Option::Some(local) => {
            journal_local_step_simulates_broker(
                cfg, before, source_event, local, after,
            );
        },
    }
}

pub proof fn lifted_execution_is_broker_execution(
    cfg: config_layer::FullConfig,
    source: runtime_layer::JournalExecution,
)
    requires
        config_layer::full_config_wf(cfg),
        runtime_layer::exec(cfg, source),
    ensures execution_layer::exec(cfg, lift_execution(cfg, source)),
{
    let target = lift_execution(cfg, source);
    runtime_layer::every_exec_configuration_is_basic(cfg, source);
    event_layer::translate_trace_len(source.events);
    representation_layer::abstract_initial_is_broker_initial(cfg);
    assert(target.configs.len() == source.configs.len());
    assert(target.events.len() == source.events.len());
    assert(target.configs.len() == target.events.len() + 1);
    assert(target.configs[0]
        == representation_layer::abstract_broker_state(cfg, source.configs[0]));
    assert(source.configs[0] == runtime_layer::initial_configuration(cfg));
    assert(execution_layer::broker_init(cfg, target.configs[0]));
    assert forall|index: nat| index < target.events.len() implies
        #[trigger] execution_layer::broker_step(
            cfg,
            target.configs[index as int],
            target.events[index as int],
            target.configs[(index + 1) as int],
        ) by {
        assert(index < source.events.len());
        event_layer::translate_trace_index(source.events, index);
        assert(target.configs[index as int]
            == representation_layer::abstract_broker_state(
                cfg, source.configs[index as int],
            ));
        assert(target.configs[(index + 1) as int]
            == representation_layer::abstract_broker_state(
                cfg, source.configs[(index + 1) as int],
            ));
        assert(runtime_layer::basic_invariant(
            cfg, source.configs[index as int],
        ));
        assert(runtime_layer::journal_runtime_step(
            cfg,
            source.configs[index as int],
            source.events[index as int],
            source.configs[(index + 1) as int],
        ));
        journal_runtime_step_simulates_broker(
            cfg,
            source.configs[index as int],
            source.events[index as int],
            source.configs[(index + 1) as int],
        );
    }
}

pub proof fn every_lifted_configuration_is_represented(
    cfg: config_layer::FullConfig,
    source: runtime_layer::JournalExecution,
)
    requires
        config_layer::full_config_wf(cfg),
        runtime_layer::exec(cfg, source),
    ensures forall|index: nat| index < source.configs.len() ==>
        #[trigger] representation_layer::representation(
            cfg,
            source.configs[index as int],
            lift_execution(cfg, source).configs[index as int],
        ),
{
    let target = lift_execution(cfg, source);
    lifted_execution_is_broker_execution(cfg, source);
    runtime_layer::every_exec_configuration_is_basic(cfg, source);
    execution_layer::every_exec_config_preserves_local_inductive_invariant(
        cfg, target,
    );
    assert forall|index: nat| index < source.configs.len() implies
        #[trigger] representation_layer::representation(
            cfg,
            source.configs[index as int],
            target.configs[index as int],
        ) by {
        assert(index < target.configs.len());
        assert(target.configs[index as int]
            == representation_layer::abstract_broker_state(
                cfg, source.configs[index as int],
            ));
        assert(runtime_layer::basic_invariant(
            cfg, source.configs[index as int],
        ));
        assert(runtime_layer::storage_agreement(
            source.configs[index as int],
        ));
        assert(contract_layer::local_inductive_invariant(
            cfg, target.configs[index as int],
        ));
        representation_layer::local_inductive_invariant_implies_representation(
            cfg,
            source.configs[index as int],
            target.configs[index as int],
        );
    }
}

pub proof fn identity_map_is_weak_simulation(
    cfg: config_layer::FullConfig,
    source: runtime_layer::JournalExecution,
)
    requires
        config_layer::full_config_wf(cfg),
        runtime_layer::exec(cfg, source),
    ensures weak_simulation_index_map(
        cfg,
        source,
        lift_execution(cfg, source),
        identity_index_map(source.events.len()),
    ),
{
    let target = lift_execution(cfg, source);
    let map = identity_index_map(source.events.len());
    lifted_execution_is_broker_execution(cfg, source);
    every_lifted_configuration_is_represented(cfg, source);
    event_layer::translate_trace_len(source.events);
    assert(map.points.len() == source.events.len() + 1);
    assert(map.points[0] == 0);
    assert(map.points[source.events.len() as int] == target.events.len());
    assert(weak_index_shape(
        source.events.len(), target.events.len(), map,
    )) by {
        assert forall|index: nat| index < source.events.len() implies {
            let left = #[trigger] map.points[index as int];
            let right = map.points[(index + 1) as int];
            &&& left <= right
            &&& right <= target.events.len()
            &&& (right == left || right == left + 1)
        } by {
            assert(map.points[index as int] == index);
            assert(map.points[(index + 1) as int] == index + 1);
        }
    }
    assert forall|index: nat| index < source.events.len() implies {
        let left = #[trigger] map.points[index as int];
        let right = map.points[(index + 1) as int];
        if left == right {
            event_layer::t2_projection_silent(source.events[index as int])
        } else {
            &&& right == left + 1
            &&& left < target.events.len()
            &&& event_layer::event_match(
                source.events[index as int], target.events[left as int],
            )
        }
    } by {
        event_layer::translate_trace_index(source.events, index);
    }
    assert(related_prefixes(cfg, source, target, map)) by {
        assert forall|index: nat| index < source.configs.len() implies {
            &&& index < map.points.len()
            &&& #[trigger] map.points[index as int] < target.configs.len()
            &&& representation_layer::representation(
                cfg,
                source.configs[index as int],
                target.configs[map.points[index as int] as int],
            )
        } by {
            assert(map.points[index as int] == index);
        }
    }
    assert(related_prefix_projections(source, target, map)) by {
        assert forall|index: nat| index <= source.events.len() implies {
            &&& index < map.points.len()
            &&& map.points[index as int] <= target.events.len()
            &&& #[trigger] event_layer::t2_projection_agreement(
                source.events.take(index as int),
                target.events.take(map.points[index as int] as int),
            )
        } by {
            assert(map.points[index as int] == index);
            event_layer::translate_trace_take(source.events, index);
            event_layer::translated_trace_projection_agreement(
                source.events.take(index as int),
            );
        }
    }
}

pub proof fn canonical_atomic_journal_simulation(
    cfg: config_layer::FullConfig,
    source: runtime_layer::JournalExecution,
)
    requires
        config_layer::full_config_wf(cfg),
        runtime_layer::exec(cfg, source),
    ensures
        trace_layer::admissible_journal_trace(cfg, source),
        trace_layer::trace_agreement(cfg, source),
        execution_layer::exec(cfg, lift_execution(cfg, source)),
        weak_simulation_index_map(
            cfg,
            source,
            lift_execution(cfg, source),
            identity_index_map(source.events.len()),
        ),
        event_layer::t2_projection_agreement(
            source.events, lift_execution(cfg, source).events,
        ),
        t2_simulation_statement(cfg, source),
{
    trace_layer::exec_implies_admissible_journal_trace(cfg, source);
    trace_layer::trace_agreement_for_exec(cfg, source);
    lifted_execution_is_broker_execution(cfg, source);
    identity_map_is_weak_simulation(cfg, source);
    event_layer::translated_trace_projection_agreement(source.events);
    let target = lift_execution(cfg, source);
    let map = identity_index_map(source.events.len());
    assert(execution_layer::exec(cfg, target));
    assert(weak_simulation_index_map(cfg, source, target, map));
}

// Exported paper theorem.  The explicit admissibility and TraceAgreement
// premises match the normative T2 statement; the mechanized runtime actually
// derives both from Exec, yielding a slightly stronger canonical theorem.
pub proof fn t2_atomic_journal_runtime_simulation<A>(
    cfg: t1_layer::PaperConfig<A>,
    source: runtime_layer::JournalExecution,
)
    requires
        t1_layer::paper_config_wf(cfg),
        runtime_layer::exec(t1_layer::paper_broker_config(cfg), source),
        trace_layer::admissible_journal_trace(
            t1_layer::paper_broker_config(cfg), source,
        ),
        trace_layer::trace_agreement(
            t1_layer::paper_broker_config(cfg), source,
        ),
    ensures t2_simulation_statement(
        t1_layer::paper_broker_config(cfg), source,
    ),
{
    canonical_atomic_journal_simulation(
        t1_layer::paper_broker_config(cfg), source,
    );
}

} // verus!
