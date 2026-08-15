use vstd::prelude::*;

#[path = "t5_durable_success_recovery.rs"]
pub mod t5_r1_layer;
// Preserve the historical public module path for downstream T6 targets while
// making the R1 layer the source of the contextual types.
pub use t5_r1_layer::t5_r0_layer;

verus! {

use t5_r1_layer::t5_r0_layer::t5_e0_layer;
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
use contract_layer::p3_layer::p2_layer::p1_layer::p0_layer;
use p0_layer::config_layer;
use config_layer::broker_layer as record_layer;
use record_layer::query_layer::c1_layer::append_layer;

// T5-C0 transports T5's committed-history laws through T4's canonical weak
// map. Event-delta commutation explains matched and erased source steps, while
// exact state equality at map points comes from the representation relations.

pub open spec fn mapped_commit_histories_equal(
    cfg: config_layer::FullConfig,
    source: wal_runtime_layer::WalExecution,
    target: execution_layer::BrokerExecution,
    map: t2_layer::WeakIndexMap,
) -> bool {
    &&& t4_c0_layer::related_prefixes(cfg, source, target, map)
    &&& forall|index: nat| index <= source.events.len() ==>
        #[trigger] t5_s0_layer::alpha_commit_wal(
            cfg, source.configs[index as int],
        ) == t5_s0_layer::alpha_commit_broker(
            target.configs[map.points[index as int] as int],
        )
}

pub open spec fn mapped_recovery_commit_history_equal(
    cfg: config_layer::FullConfig,
    source: wal_runtime_layer::WalExecution,
    target: execution_layer::BrokerExecution,
    map: t2_layer::WeakIndexMap,
    crash: nat,
    finish: nat,
) -> bool {
    &&& crash < source.configs.len()
    &&& finish + 1 < source.configs.len()
    &&& crash < map.points.len()
    &&& finish + 1 < map.points.len()
    &&& map.points[crash as int] < target.configs.len()
    &&& map.points[(finish + 1) as int] < target.configs.len()
    &&& t5_s0_layer::alpha_commit_wal(
        cfg, source.configs[crash as int],
    ) == t5_s0_layer::alpha_commit_wal(
        cfg, source.configs[(finish + 1) as int],
    )
    &&& t5_s0_layer::alpha_commit_wal(
        cfg, source.configs[crash as int],
    ) == t5_s0_layer::alpha_commit_broker(
        target.configs[map.points[crash as int] as int],
    )
    &&& t5_s0_layer::alpha_commit_wal(
        cfg, source.configs[(finish + 1) as int],
    ) == t5_s0_layer::alpha_commit_broker(
        target.configs[map.points[(finish + 1) as int] as int],
    )
    &&& t5_s0_layer::alpha_commit_broker(
        target.configs[map.points[crash as int] as int],
    ) == t5_s0_layer::alpha_commit_broker(
        target.configs[map.points[(finish + 1) as int] as int],
    )
}

pub open spec fn mapped_recovery_commit_history_extends(
    cfg: config_layer::FullConfig,
    source: wal_runtime_layer::WalExecution,
    target: execution_layer::BrokerExecution,
    map: t2_layer::WeakIndexMap,
    crash: nat,
    finish: nat,
) -> bool {
    &&& crash < source.configs.len()
    &&& finish + 1 < source.configs.len()
    &&& crash < map.points.len()
    &&& finish + 1 < map.points.len()
    &&& map.points[crash as int] < target.configs.len()
    &&& map.points[(finish + 1) as int] < target.configs.len()
    &&& append_layer::is_prefix(
        t5_s0_layer::alpha_commit_wal(
            cfg, source.configs[crash as int],
        ),
        t5_s0_layer::alpha_commit_wal(
            cfg, source.configs[(finish + 1) as int],
        ),
    )
    &&& append_layer::is_prefix(
        t5_s0_layer::alpha_commit_broker(
            target.configs[map.points[crash as int] as int],
        ),
        t5_s0_layer::alpha_commit_broker(
            target.configs[map.points[(finish + 1) as int] as int],
        ),
    )
    &&& t5_r1_layer::wal_recovery_episode_has_crash_prefix_provenance(
        source, crash, finish,
    )
}

pub open spec fn t5_c0_statement<S>(
    cfg: config_layer::FullConfig,
    context: t4_c1_layer::ProgramContext<S>,
    source: t4_c1_layer::PluggedWalExecution<S>,
    crash: nat,
    finish: nat,
) -> bool {
    let target = t4_layer::canonical_plugged_broker_execution(cfg, source);
    let map = t4_c0_layer::canonical_composed_map(source.machine);
    &&& t4_layer::t4_c2_statement(cfg, context, source)
    &&& mapped_commit_histories_equal(
        cfg, source.machine, target.machine, map,
    )
    &&& mapped_recovery_commit_history_equal(
        cfg, source.machine, target.machine, map, crash, finish,
    )
}

pub proof fn t3_commit_delta_translation_exact(
    source: global_layer::GlobalEvent,
)
    ensures t5_s0_layer::wal_commit_delta(source) ==
        match t3_event_layer::translate_event(source) {
            Option::None => Option::None,
            Option::Some(target) => {
                t5_s0_layer::journal_commit_delta(target)
            },
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

pub proof fn t2_commit_delta_translation_exact(
    source: global_layer::GlobalEvent,
)
    requires journal_runtime_layer::journal_constructor(source),
    ensures t5_s0_layer::journal_commit_delta(source)
        == t5_s0_layer::broker_commit_delta(
            t2_event_layer::journal_to_broker_event(source),
        ),
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

pub proof fn t4_commit_delta_translation_exact(
    source: global_layer::GlobalEvent,
)
    ensures t5_s0_layer::wal_commit_delta(source) ==
        match t4_c0_layer::wal_to_broker_event(source) {
            Option::None => Option::None,
            Option::Some(target) => {
                t5_s0_layer::broker_commit_delta(target)
            },
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

pub proof fn weak_simulation_step_commit_delta_correspondence(
    cfg: config_layer::FullConfig,
    source: wal_runtime_layer::WalExecution,
    target: execution_layer::BrokerExecution,
    map: t2_layer::WeakIndexMap,
    index: nat,
)
    requires
        wal_runtime_layer::exec(cfg, source),
        t4_c0_layer::weak_simulation_index_map(
            cfg, source, target, map,
        ),
        index < source.events.len(),
    ensures {
        let left = map.points[index as int];
        let right = map.points[(index + 1) as int];
        if left == right {
            t5_s0_layer::wal_commit_delta(
                source.events[index as int],
            ).is_none()
        } else {
            &&& right == left + 1
            &&& left < target.events.len()
            &&& t5_s0_layer::wal_commit_delta(
                source.events[index as int],
            ) == t5_s0_layer::broker_commit_delta(
                target.events[left as int],
            )
        }
    },
{
    let source_event = source.events[index as int];
    let left = map.points[index as int];
    let right = map.points[(index + 1) as int];
    assert(wal_runtime_layer::wal_runtime_step(
        cfg,
        source.configs[index as int],
        source_event,
        source.configs[(index + 1) as int],
    ));
    wal_runtime_layer::wal_step_is_closed(
        cfg,
        source.configs[index as int],
        source_event,
        source.configs[(index + 1) as int],
    );
    assert(t4_c0_layer::step_correspondence(
        source, target, map,
    ));
    if left == right {
        assert(t4_c0_layer::composed_projection_silent(source_event));
        t3_event_layer::translation_silence_classifier_exact(source_event);
        assert(t3_event_layer::translate_event(source_event).is_none());
        t3_commit_delta_translation_exact(source_event);
    } else {
        assert(t4_c0_layer::composed_event_match(
            source_event, target.events[left as int],
        ));
        assert(t4_c0_layer::wal_to_broker_event(source_event)
            == Option::Some(target.events[left as int]));
        t4_commit_delta_translation_exact(source_event);
    }
}

pub proof fn t3_representation_preserves_commit_history(
    cfg: config_layer::FullConfig,
    wal: wal_runtime_layer::WalConfiguration,
    journal: journal_runtime_layer::JournalConfiguration,
)
    requires t3_representation_layer::representation(wal, journal),
    ensures t5_s0_layer::alpha_commit_wal(cfg, wal)
        == t5_s0_layer::alpha_commit_journal(cfg, journal),
{
    t3_representation_layer::representation_determines_projection(
        wal, journal,
    );
}

pub proof fn t2_representation_preserves_commit_history(
    cfg: config_layer::FullConfig,
    journal: journal_runtime_layer::JournalConfiguration,
    broker: p0_layer::State,
)
    requires t2_representation_layer::representation(cfg, journal, broker),
    ensures t5_s0_layer::alpha_commit_journal(cfg, journal)
        == t5_s0_layer::alpha_commit_broker(broker),
{
}

pub proof fn wal_broker_representation_preserves_commit_history(
    cfg: config_layer::FullConfig,
    wal: wal_runtime_layer::WalConfiguration,
    broker: p0_layer::State,
)
    requires t4_c0_layer::wal_broker_representation(cfg, wal, broker),
    ensures t5_s0_layer::alpha_commit_wal(cfg, wal)
        == t5_s0_layer::alpha_commit_broker(broker),
{
    t2_representation_preserves_commit_history(
        cfg, wal_runtime_layer::journal_projection(wal), broker,
    );
}

pub proof fn related_prefixes_preserve_commit_histories(
    cfg: config_layer::FullConfig,
    source: wal_runtime_layer::WalExecution,
    target: execution_layer::BrokerExecution,
    map: t2_layer::WeakIndexMap,
)
    requires t4_c0_layer::related_prefixes(cfg, source, target, map),
    ensures mapped_commit_histories_equal(cfg, source, target, map),
{
    assert forall|index: nat| index <= source.events.len() implies
            #[trigger] t5_s0_layer::alpha_commit_wal(
                cfg, source.configs[index as int],
            ) == t5_s0_layer::alpha_commit_broker(
                target.configs[map.points[index as int] as int],
            ) by {
        assert(index < source.configs.len());
        assert(index < map.points.len());
        assert(map.points[index as int] < target.configs.len());
        assert(t4_c0_layer::wal_broker_representation(
            cfg,
            source.configs[index as int],
            target.configs[map.points[index as int] as int],
        ));
        wal_broker_representation_preserves_commit_history(
            cfg,
            source.configs[index as int],
            target.configs[map.points[index as int] as int],
        );
    }
}

pub proof fn mapped_recovery_commit_history_equal_at(
    cfg: config_layer::FullConfig,
    source: wal_runtime_layer::WalExecution,
    target: execution_layer::BrokerExecution,
    map: t2_layer::WeakIndexMap,
    crash: nat,
    finish: nat,
)
    requires
        wal_runtime_layer::exec(cfg, source),
        t4_c0_layer::weak_simulation_index_map(
            cfg, source, target, map,
        ),
        t5_r0_layer::commit_stuttering_recovery_episode(
            source.events, crash, finish,
        ),
    ensures mapped_recovery_commit_history_equal(
        cfg, source, target, map, crash, finish,
    ),
{
    related_prefixes_preserve_commit_histories(
        cfg, source, target, map,
    );
    t5_r0_layer::wal_recovery_episode_commit_history_equal(
        cfg, source, crash, finish,
    );
    assert(crash <= source.events.len());
    assert(finish + 1 <= source.events.len());
    assert(mapped_commit_histories_equal(cfg, source, target, map));
}

pub open spec fn t5_c1_statement<S>(
    cfg: config_layer::FullConfig,
    context: t4_c1_layer::ProgramContext<S>,
    source: t4_c1_layer::PluggedWalExecution<S>,
    crash: nat,
    finish: nat,
) -> bool {
    let target = t4_layer::canonical_plugged_broker_execution(cfg, source);
    let map = t4_c0_layer::canonical_composed_map(source.machine);
    &&& t4_layer::t4_c2_statement(cfg, context, source)
    &&& mapped_commit_histories_equal(
        cfg, source.machine, target.machine, map,
    )
    &&& mapped_recovery_commit_history_extends(
        cfg, source.machine, target.machine, map, crash, finish,
    )
}

pub proof fn transport_commit_prefix<T>(
    source_first: Seq<T>,
    source_last: Seq<T>,
    target_first: Seq<T>,
    target_last: Seq<T>,
)
    requires
        append_layer::is_prefix(source_first, source_last),
        target_first == source_first,
        target_last == source_last,
    ensures append_layer::is_prefix(target_first, target_last),
{
    assert(source_first.len() <= source_last.len());
    assert(source_first == source_last.take(source_first.len() as int));
    assert(target_first.len() == source_first.len());
    assert(target_last.take(target_first.len() as int)
        == source_last.take(source_first.len() as int));
    assert(target_first == target_last.take(target_first.len() as int));
}

pub proof fn mapped_recovery_commit_history_extends_at(
    cfg: config_layer::FullConfig,
    source: wal_runtime_layer::WalExecution,
    target: execution_layer::BrokerExecution,
    map: t2_layer::WeakIndexMap,
    crash: nat,
    finish: nat,
)
    requires
        wal_runtime_layer::exec(cfg, source),
        mapped_commit_histories_equal(cfg, source, target, map),
        t5_r0_layer::recovery_episode(source.events, crash, finish),
    ensures mapped_recovery_commit_history_extends(
        cfg, source, target, map, crash, finish,
    ),
{
    t5_r1_layer::wal_recovery_episode_commit_history_extends(
        cfg, source, crash, finish,
    );
    t5_r1_layer::wal_recovery_episode_crash_prefix_provenance(
        cfg, source, crash, finish,
    );
    assert(crash <= source.events.len());
    assert(finish + 1 <= source.events.len());
    assert(crash < source.configs.len());
    assert(finish + 1 < source.configs.len());
    assert(crash < map.points.len());
    assert(finish + 1 < map.points.len());
    assert(map.points[crash as int] < target.configs.len());
    assert(map.points[(finish + 1) as int] < target.configs.len());
    assert(t5_s0_layer::alpha_commit_wal(
        cfg, source.configs[crash as int],
    ) == t5_s0_layer::alpha_commit_broker(
        target.configs[map.points[crash as int] as int],
    ));
    assert(t5_s0_layer::alpha_commit_wal(
        cfg, source.configs[(finish + 1) as int],
    ) == t5_s0_layer::alpha_commit_broker(
        target.configs[map.points[(finish + 1) as int] as int],
    ));
    transport_commit_prefix(
        t5_s0_layer::alpha_commit_wal(
            cfg, source.configs[crash as int],
        ),
        t5_s0_layer::alpha_commit_wal(
            cfg, source.configs[(finish + 1) as int],
        ),
        t5_s0_layer::alpha_commit_broker(
            target.configs[map.points[crash as int] as int],
        ),
        t5_s0_layer::alpha_commit_broker(
            target.configs[map.points[(finish + 1) as int] as int],
        ),
    );
}

pub proof fn canonical_mapped_commit_histories_equal(
    cfg: config_layer::FullConfig,
    source: wal_runtime_layer::WalExecution,
)
    requires
        config_layer::full_config_wf(cfg),
        wal_runtime_layer::exec(cfg, source),
    ensures mapped_commit_histories_equal(
        cfg,
        source,
        t4_c0_layer::canonical_target_execution(cfg, source),
        t4_c0_layer::canonical_composed_map(source),
    ),
{
    t4_c0_layer::canonical_closed_wal_broker_composition(cfg, source);
    related_prefixes_preserve_commit_histories(
        cfg,
        source,
        t4_c0_layer::canonical_target_execution(cfg, source),
        t4_c0_layer::canonical_composed_map(source),
    );
}

pub proof fn canonical_mapped_recovery_commit_history_equal(
    cfg: config_layer::FullConfig,
    source: wal_runtime_layer::WalExecution,
    crash: nat,
    finish: nat,
)
    requires
        config_layer::full_config_wf(cfg),
        wal_runtime_layer::exec(cfg, source),
        t5_r0_layer::commit_stuttering_recovery_episode(
            source.events, crash, finish,
        ),
    ensures mapped_recovery_commit_history_equal(
        cfg,
        source,
        t4_c0_layer::canonical_target_execution(cfg, source),
        t4_c0_layer::canonical_composed_map(source),
        crash,
        finish,
    ),
{
    t4_c0_layer::canonical_closed_wal_broker_composition(cfg, source);
    mapped_recovery_commit_history_equal_at(
        cfg,
        source,
        t4_c0_layer::canonical_target_execution(cfg, source),
        t4_c0_layer::canonical_composed_map(source),
        crash,
        finish,
    );
}

pub proof fn canonical_mapped_recovery_commit_history_extends(
    cfg: config_layer::FullConfig,
    source: wal_runtime_layer::WalExecution,
    crash: nat,
    finish: nat,
)
    requires
        config_layer::full_config_wf(cfg),
        wal_runtime_layer::exec(cfg, source),
        t5_r0_layer::recovery_episode(source.events, crash, finish),
    ensures mapped_recovery_commit_history_extends(
        cfg,
        source,
        t4_c0_layer::canonical_target_execution(cfg, source),
        t4_c0_layer::canonical_composed_map(source),
        crash,
        finish,
    ),
{
    t4_c0_layer::canonical_closed_wal_broker_composition(cfg, source);
    canonical_mapped_commit_histories_equal(cfg, source);
    mapped_recovery_commit_history_extends_at(
        cfg,
        source,
        t4_c0_layer::canonical_target_execution(cfg, source),
        t4_c0_layer::canonical_composed_map(source),
        crash,
        finish,
    );
}

// The minimal recovery episode is compatible with a concrete storage-
// parametric context, so the contextual T5-C0 premises are jointly inhabited.
pub open spec fn minimal_contextual_recovery_execution<S>(
    cfg: config_layer::FullConfig,
    state: S,
) -> t4_c1_layer::PluggedWalExecution<S> {
    t4_c1_layer::PluggedWalExecution {
        machine: t5_r0_layer::minimal_wal_recovery_execution(cfg),
        contexts: Seq::empty()
            .push(state)
            .push(state)
            .push(state)
            .push(state)
            .push(state)
            .push(state)
            .push(state),
    }
}

pub proof fn inert_context_has_minimal_contextual_recovery_episode<S>(
    cfg: config_layer::FullConfig,
    state: S,
)
    requires config_layer::full_config_wf(cfg),
    ensures
        t4_c1_layer::storage_parametric_context(
            cfg, t4_c1_layer::inert_context(cfg, state),
        ),
        t4_c1_layer::plugged_wal_exec(
            cfg,
            t4_c1_layer::inert_context(cfg, state),
            minimal_contextual_recovery_execution(cfg, state),
        ),
        t5_r0_layer::commit_stuttering_recovery_episode(
            minimal_contextual_recovery_execution(cfg, state).machine.events,
            0,
            5,
        ),
        t5_c0_statement(
            cfg,
            t4_c1_layer::inert_context(cfg, state),
            minimal_contextual_recovery_execution(cfg, state),
            0,
            5,
        ),
{
    let execution = minimal_contextual_recovery_execution(cfg, state);
    let machine = execution.machine;
    let context = t4_c1_layer::inert_context(cfg, state);

    t4_c1_layer::inert_context_is_storage_parametric(cfg, state);
    t5_r0_layer::minimal_wal_recovery_episode_is_inhabited(cfg);
    t4_c1_layer::initialized_wal_has_initial_context_view(cfg, machine);

    assert(machine.events.len() == 6);
    assert(machine.configs.len() == 7);
    assert(execution.contexts.len() == 7);
    assert forall|index: nat| index < execution.contexts.len() implies
        #[trigger] execution.contexts[index as int] == state by {
        if index == 0 {
        } else if index == 1 {
        } else if index == 2 {
        } else if index == 3 {
        } else if index == 4 {
        } else if index == 5 {
        } else {
            assert(index == 6);
        }
    }
    assert(context.initial.contains(t4_c1_layer::ContextInitial {
        view: t4_c1_layer::wal_context_view_at(cfg, machine, 0),
        state: execution.contexts[0],
    }));
    assert forall|index: nat| index < machine.events.len() implies {
        &&& #[trigger] wal_runtime_layer::wal_runtime_step(
            cfg,
            machine.configs[index as int],
            machine.events[index as int],
            machine.configs[(index + 1) as int],
        )
        &&& t4_c1_layer::context_accepts_step(
            context,
            execution.contexts[index as int],
            t4_c1_layer::wal_context_view_at(cfg, machine, index),
            machine.events[index as int],
            t4_c1_layer::wal_context_view_at(cfg, machine, index + 1),
            execution.contexts[(index + 1) as int],
        )
    } by {
        let event = machine.events[index as int];
        let delta = t4_c1_layer::context_delta(event);
        let history = t4_c1_layer::context_history(
            machine.events.take(index as int),
        );
        assert(index + 1 < execution.contexts.len());
        assert(execution.contexts[index as int] == state);
        assert(execution.contexts[(index + 1) as int] == state);
        assert(wal_runtime_layer::wal_runtime_step(
            cfg,
            machine.configs[index as int],
            event,
            machine.configs[(index + 1) as int],
        ));
        t4_c1_layer::context_delta_classification(event);
        if delta.len() == 0 {
            t3_layer::take_succ(machine.events, index);
            t4_c1_layer::context_history_push(
                machine.events.take(index as int), event,
            );
            t4_c1_layer::wal_hidden_step_preserves_context_view(
                cfg,
                history,
                machine.configs[index as int],
                event,
                machine.configs[(index + 1) as int],
            );
            assert(t4_c1_layer::wal_context_view_at(cfg, machine, index)
                == t4_c1_layer::wal_context_view_at(
                    cfg, machine, index + 1,
                ));
        } else {
            assert(t4_c1_layer::valid_context_delta(delta)) by {
                assert(exists|witness: global_layer::GlobalEvent|
                    t4_c1_layer::context_delta(witness) == delta) by {
                    let witness = event;
                }
            }
            assert(context.transitions.contains(t4_c1_layer::ContextTransition {
                before: state,
                view: t4_c1_layer::wal_context_view_at(cfg, machine, index),
                delta,
                after_view: t4_c1_layer::wal_context_view_at(
                    cfg, machine, index + 1,
                ),
                after: state,
            }));
        }
    }
    assert(t4_c1_layer::plugged_wal_exec(cfg, context, execution));
    canonical_contextual_recovery_preservation(
        cfg, context, execution, 0, 5,
    );
}

pub proof fn canonical_contextual_recovery_preservation<S>(
    cfg: config_layer::FullConfig,
    context: t4_c1_layer::ProgramContext<S>,
    source: t4_c1_layer::PluggedWalExecution<S>,
    crash: nat,
    finish: nat,
)
    requires
        config_layer::full_config_wf(cfg),
        t4_c1_layer::storage_parametric_context(cfg, context),
        t4_c1_layer::plugged_wal_exec(cfg, context, source),
        t5_r0_layer::commit_stuttering_recovery_episode(
            source.machine.events, crash, finish,
        ),
    ensures t5_c0_statement(cfg, context, source, crash, finish),
{
    t4_c1_layer::plugged_wal_embeds(cfg, context, source);
    t4_layer::canonical_contextual_wal_broker_composition(
        cfg, context, source,
    );
    canonical_mapped_commit_histories_equal(cfg, source.machine);
    canonical_mapped_recovery_commit_history_equal(
        cfg, source.machine, crash, finish,
    );
}

pub proof fn canonical_contextual_recovery_extension<S>(
    cfg: config_layer::FullConfig,
    context: t4_c1_layer::ProgramContext<S>,
    source: t4_c1_layer::PluggedWalExecution<S>,
    crash: nat,
    finish: nat,
)
    requires
        config_layer::full_config_wf(cfg),
        t4_c1_layer::storage_parametric_context(cfg, context),
        t4_c1_layer::plugged_wal_exec(cfg, context, source),
        t5_r0_layer::recovery_episode(source.machine.events, crash, finish),
    ensures t5_c1_statement(cfg, context, source, crash, finish),
{
    t4_c1_layer::plugged_wal_embeds(cfg, context, source);
    t4_layer::canonical_contextual_wal_broker_composition(
        cfg, context, source,
    );
    canonical_mapped_commit_histories_equal(cfg, source.machine);
    canonical_mapped_recovery_commit_history_extends(
        cfg, source.machine, crash, finish,
    );
}

pub proof fn t5_c0_contextual_recovery_preservation<A, S>(
    cfg: t1_layer::PaperConfig<A>,
    context: t4_c1_layer::ProgramContext<S>,
    source: t4_c1_layer::PluggedWalExecution<S>,
    crash: nat,
    finish: nat,
)
    requires
        t1_layer::paper_config_wf(cfg),
        t4_c1_layer::storage_parametric_context(
            t1_layer::paper_broker_config(cfg), context,
        ),
        t4_c1_layer::plugged_wal_exec(
            t1_layer::paper_broker_config(cfg), context, source,
        ),
        t5_r0_layer::commit_stuttering_recovery_episode(
            source.machine.events, crash, finish,
        ),
    ensures t5_c0_statement(
        t1_layer::paper_broker_config(cfg),
        context,
        source,
        crash,
        finish,
    ),
{
    canonical_contextual_recovery_preservation(
        t1_layer::paper_broker_config(cfg),
        context,
        source,
        crash,
        finish,
    );
}

} // verus!
