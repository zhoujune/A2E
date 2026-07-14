use vstd::prelude::*;

#[path = "t3_wal_journal_simulation.rs"]
pub mod t3_layer;

verus! {

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
use config_layer::broker_layer::query_layer::c1_layer::replay_layer;

// T4-C0 is the closed-machine composition of T3 and T2.  It deliberately
// contains no context state or plugging semantics; those belong to T4-C1.
// Later T4 roots must import this file alone so the nested runtime types keep
// the single nominal identity established by the T3 -> T2 -> T1 chain.

pub open spec fn compose_index_maps(
    first: t2_layer::WeakIndexMap,
    second: t2_layer::WeakIndexMap,
) -> t2_layer::WeakIndexMap {
    t2_layer::WeakIndexMap {
        points: Seq::new(first.points.len(), |index: int|
            if first.points[index] < second.points.len() {
                second.points[first.points[index] as int]
            } else {
                0nat
            }),
    }
}

pub proof fn weak_index_point_bounded(
    source_length: nat,
    target_length: nat,
    map: t2_layer::WeakIndexMap,
    index: nat,
)
    requires
        t2_layer::weak_index_shape(source_length, target_length, map),
        index <= source_length,
    ensures
        index < map.points.len(),
        map.points[index as int] <= target_length,
{
    assert(map.points.len() == source_length + 1);
    assert(index < map.points.len());
    if index == 0 {
        assert(map.points[0] == 0);
    } else {
        let previous = index - 1;
        assert(previous < source_length);
        assert(previous + 1 == index);
        assert({
            let left = #[trigger] map.points[previous as int];
            let right = map.points[(previous + 1) as int];
            &&& left <= right
            &&& right <= target_length
            &&& (right == left || right == left + 1)
        });
    }
}

pub proof fn compose_index_map_point(
    first: t2_layer::WeakIndexMap,
    second: t2_layer::WeakIndexMap,
    index: nat,
)
    requires
        index < first.points.len(),
        first.points[index as int] < second.points.len(),
    ensures compose_index_maps(first, second).points[index as int]
        == second.points[first.points[index as int] as int],
{
}

pub proof fn compose_weak_index_shapes(
    source_length: nat,
    middle_length: nat,
    target_length: nat,
    first: t2_layer::WeakIndexMap,
    second: t2_layer::WeakIndexMap,
)
    requires
        t2_layer::weak_index_shape(
            source_length, middle_length, first,
        ),
        t2_layer::weak_index_shape(
            middle_length, target_length, second,
        ),
    ensures t2_layer::weak_index_shape(
        source_length,
        target_length,
        compose_index_maps(first, second),
    ),
{
    let composed = compose_index_maps(first, second);
    assert(composed.points.len() == source_length + 1);
    weak_index_point_bounded(
        source_length, middle_length, first, 0,
    );
    assert(first.points[0] == 0);
    assert(second.points.len() == middle_length + 1);
    compose_index_map_point(first, second, 0);
    assert(composed.points[0] == second.points[0]);
    assert(composed.points[0] == 0);

    weak_index_point_bounded(
        source_length, middle_length, first, source_length,
    );
    assert(first.points[source_length as int] == middle_length);
    assert(middle_length < second.points.len());
    compose_index_map_point(first, second, source_length);
    assert(second.points[middle_length as int] == target_length);
    assert(composed.points[source_length as int] == target_length);

    assert forall|index: nat| index < source_length implies {
        let left = #[trigger] composed.points[index as int];
        let right = composed.points[(index + 1) as int];
        &&& left <= right
        &&& right <= target_length
        &&& (right == left || right == left + 1)
    } by {
        weak_index_point_bounded(
            source_length, middle_length, first, index,
        );
        weak_index_point_bounded(
            source_length, middle_length, first, index + 1,
        );
        let middle_left = first.points[index as int];
        let middle_right = first.points[(index + 1) as int];
        assert(middle_left < second.points.len());
        assert(middle_right < second.points.len());
        compose_index_map_point(first, second, index);
        compose_index_map_point(first, second, index + 1);
        assert({
            let left = #[trigger] first.points[index as int];
            let right = first.points[(index + 1) as int];
            &&& left <= right
            &&& right <= middle_length
            &&& (right == left || right == left + 1)
        });
        if middle_left == middle_right {
            assert(composed.points[index as int]
                == composed.points[(index + 1) as int]);
        } else {
            assert(middle_right == middle_left + 1);
            assert(middle_left < middle_length);
            assert({
                let left = #[trigger] second.points[middle_left as int];
                let right = second.points[(middle_left + 1) as int];
                &&& left <= right
                &&& right <= target_length
                &&& (right == left || right == left + 1)
            });
        }
    }
}

pub proof fn compose_with_identity(
    source_length: nat,
    middle_length: nat,
    first: t2_layer::WeakIndexMap,
)
    requires t2_layer::weak_index_shape(
        source_length, middle_length, first,
    ),
    ensures compose_index_maps(
        first, t2_layer::identity_index_map(middle_length),
    ) == first,
{
    let identity = t2_layer::identity_index_map(middle_length);
    let composed = compose_index_maps(first, identity);
    assert(identity.points.len() == middle_length + 1);
    assert(composed.points.len() == first.points.len());
    assert forall|index: int| 0 <= index < first.points.len() implies
        composed.points[index] == first.points[index] by {
        let point: nat = first.points[index];
        let source_index: nat = index as nat;
        assert(source_index <= source_length);
        weak_index_point_bounded(
            source_length, middle_length, first, source_index,
        );
        assert(point <= middle_length);
        assert(point < identity.points.len());
        compose_index_map_point(first, identity, source_index);
        assert(identity.points[point as int] == point);
    }
    assert(composed.points =~= first.points);
    assert(composed == first);
}

pub open spec fn wal_to_broker_event(
    event: global_layer::GlobalEvent,
) -> Option<global_layer::GlobalEvent> {
    match t3_event_layer::translate_event(event) {
        Option::None => Option::None,
        Option::Some(journal_event) => Option::Some(
            t2_event_layer::journal_to_broker_event(journal_event),
        ),
    }
}

pub open spec fn composed_event_match(
    source: global_layer::GlobalEvent,
    target: global_layer::GlobalEvent,
) -> bool {
    wal_to_broker_event(source) == Option::Some(target)
}

pub open spec fn composed_projection_silent(
    event: global_layer::GlobalEvent,
) -> bool {
    t3_event_layer::t3_projection_silent(event)
}

pub open spec fn t4_projection_agreement(
    source: Seq<global_layer::GlobalEvent>,
    target: Seq<global_layer::GlobalEvent>,
) -> bool {
    t3_event_layer::t3_projection_agreement(source, target)
}

pub proof fn event_matches_compose(
    source: global_layer::GlobalEvent,
    middle: global_layer::GlobalEvent,
    target: global_layer::GlobalEvent,
)
    requires
        t3_event_layer::event_match(source, middle),
        t2_event_layer::event_match(middle, target),
    ensures composed_event_match(source, target),
{
}

pub proof fn projection_agreements_compose(
    source: Seq<global_layer::GlobalEvent>,
    middle: Seq<global_layer::GlobalEvent>,
    target: Seq<global_layer::GlobalEvent>,
)
    requires
        t3_event_layer::t3_projection_agreement(source, middle),
        t2_event_layer::t2_projection_agreement(middle, target),
    ensures t4_projection_agreement(source, target),
{
    assert forall|request: replay_layer::RequestId|
        #[trigger] projection_layer::pi_adapter(source, request)
            == projection_layer::pi_adapter(target, request) by {
        assert(projection_layer::pi_adapter(source, request)
            == projection_layer::pi_adapter(middle, request));
        assert(projection_layer::pi_adapter(middle, request)
            == projection_layer::pi_adapter(target, request));
    }
}

pub open spec fn wal_broker_representation(
    cfg: config_layer::FullConfig,
    wal: wal_runtime_layer::WalConfiguration,
    broker: p0_layer::State,
) -> bool {
    t2_representation_layer::representation(
        cfg, wal_runtime_layer::journal_projection(wal), broker,
    )
}

pub proof fn representations_compose(
    cfg: config_layer::FullConfig,
    wal: wal_runtime_layer::WalConfiguration,
    journal: journal_runtime_layer::JournalConfiguration,
    broker: p0_layer::State,
)
    requires
        t3_representation_layer::representation(wal, journal),
        t2_representation_layer::representation(cfg, journal, broker),
    ensures wal_broker_representation(cfg, wal, broker),
{
    t3_representation_layer::representation_determines_projection(
        wal, journal,
    );
}

pub open spec fn related_prefixes(
    cfg: config_layer::FullConfig,
    source: wal_runtime_layer::WalExecution,
    target: execution_layer::BrokerExecution,
    map: t2_layer::WeakIndexMap,
) -> bool {
    forall|index: nat| index <= source.events.len() ==> {
        &&& index < source.configs.len()
        &&& index < map.points.len()
        &&& #[trigger] map.points[index as int] < target.configs.len()
        &&& wal_broker_representation(
            cfg,
            source.configs[index as int],
            target.configs[map.points[index as int] as int],
        )
    }
}

pub open spec fn related_prefix_projection_at(
    source: wal_runtime_layer::WalExecution,
    target: execution_layer::BrokerExecution,
    map: t2_layer::WeakIndexMap,
    index: nat,
) -> bool {
    &&& index < map.points.len()
    &&& map.points[index as int] <= target.events.len()
    &&& t4_projection_agreement(
        source.events.take(index as int),
        target.events.take(map.points[index as int] as int),
    )
}

pub open spec fn related_prefix_projections(
    source: wal_runtime_layer::WalExecution,
    target: execution_layer::BrokerExecution,
    map: t2_layer::WeakIndexMap,
) -> bool {
    forall|index: nat| index <= source.events.len() ==>
        #[trigger] related_prefix_projection_at(source, target, map, index)
}

pub open spec fn step_correspondence(
    source: wal_runtime_layer::WalExecution,
    target: execution_layer::BrokerExecution,
    map: t2_layer::WeakIndexMap,
) -> bool {
    forall|index: nat| index < source.events.len() ==> {
        let left = #[trigger] map.points[index as int];
        let right = map.points[(index + 1) as int];
        &&& if left == right {
            composed_projection_silent(source.events[index as int])
        } else {
            &&& right == left + 1
            &&& left < target.events.len()
            &&& composed_event_match(
                source.events[index as int], target.events[left as int],
            )
        }
    }
}

pub open spec fn weak_simulation_index_map(
    cfg: config_layer::FullConfig,
    source: wal_runtime_layer::WalExecution,
    target: execution_layer::BrokerExecution,
    map: t2_layer::WeakIndexMap,
) -> bool {
    &&& t2_layer::weak_index_shape(
        source.events.len(), target.events.len(), map,
    )
    &&& step_correspondence(source, target, map)
    &&& related_prefixes(cfg, source, target, map)
    &&& related_prefix_projections(source, target, map)
}

pub proof fn t2_step_correspondence_is_lockstep(
    cfg: config_layer::FullConfig,
    source: journal_runtime_layer::JournalExecution,
    target: execution_layer::BrokerExecution,
    map: t2_layer::WeakIndexMap,
    index: nat,
)
    requires
        journal_runtime_layer::exec(cfg, source),
        t2_layer::weak_simulation_index_map(cfg, source, target, map),
        index < source.events.len(),
    ensures {
        let left = map.points[index as int];
        let right = map.points[(index + 1) as int];
        &&& right == left + 1
        &&& left < target.events.len()
        &&& t2_event_layer::event_match(
            source.events[index as int], target.events[left as int],
        )
    },
{
    let left = map.points[index as int];
    let right = map.points[(index + 1) as int];
    assert(journal_runtime_layer::journal_runtime_step(
        cfg,
        source.configs[index as int],
        source.events[index as int],
        source.configs[(index + 1) as int],
    ));
    journal_runtime_layer::journal_step_is_closed(
        cfg,
        source.configs[index as int],
        source.events[index as int],
        source.configs[(index + 1) as int],
    );
    t2_event_layer::accepted_journal_event_is_not_silent(
        source.events[index as int],
    );
    assert({
        let step_left = #[trigger] map.points[index as int];
        let step_right = map.points[(index + 1) as int];
        if step_left == step_right {
            t2_event_layer::t2_projection_silent(
                source.events[index as int],
            )
        } else {
            &&& step_right == step_left + 1
            &&& step_left < target.events.len()
            &&& t2_event_layer::event_match(
                source.events[index as int],
                target.events[step_left as int],
            )
        }
    });
    if left == right {
        assert(false);
    }
}

pub proof fn related_prefixes_compose(
    cfg: config_layer::FullConfig,
    source: wal_runtime_layer::WalExecution,
    middle: journal_runtime_layer::JournalExecution,
    target: execution_layer::BrokerExecution,
    first: t2_layer::WeakIndexMap,
    second: t2_layer::WeakIndexMap,
)
    requires
        t3_layer::weak_simulation_index_map(source, middle, first),
        t2_layer::weak_simulation_index_map(
            cfg, middle, target, second,
        ),
    ensures related_prefixes(
        cfg, source, target, compose_index_maps(first, second),
    ),
{
    let composed = compose_index_maps(first, second);
    assert forall|index: nat| index <= source.events.len() implies {
        &&& index < source.configs.len()
        &&& index < composed.points.len()
        &&& #[trigger] composed.points[index as int] < target.configs.len()
        &&& wal_broker_representation(
            cfg,
            source.configs[index as int],
            target.configs[composed.points[index as int] as int],
        )
    } by {
        let middle_index = first.points[index as int];
        assert({
            &&& index < source.configs.len()
            &&& index < first.points.len()
            &&& #[trigger] first.points[index as int] < middle.configs.len()
            &&& t3_representation_layer::representation(
                source.configs[index as int],
                middle.configs[first.points[index as int] as int],
            )
        });
        assert(middle_index < middle.configs.len());
        assert({
            &&& middle_index < second.points.len()
            &&& #[trigger] second.points[middle_index as int]
                < target.configs.len()
            &&& t2_representation_layer::representation(
                cfg,
                middle.configs[middle_index as int],
                target.configs[second.points[middle_index as int] as int],
            )
        });
        compose_index_map_point(first, second, index);
        representations_compose(
            cfg,
            source.configs[index as int],
            middle.configs[middle_index as int],
            target.configs[second.points[middle_index as int] as int],
        );
    }
}

pub proof fn related_prefix_projections_compose(
    cfg: config_layer::FullConfig,
    source: wal_runtime_layer::WalExecution,
    middle: journal_runtime_layer::JournalExecution,
    target: execution_layer::BrokerExecution,
    first: t2_layer::WeakIndexMap,
    second: t2_layer::WeakIndexMap,
)
    requires
        t3_layer::weak_simulation_index_map(source, middle, first),
        t2_layer::weak_simulation_index_map(
            cfg, middle, target, second,
        ),
    ensures related_prefix_projections(
        source, target, compose_index_maps(first, second),
    ),
{
    let composed = compose_index_maps(first, second);
    assert forall|index: nat| index <= source.events.len() implies
        #[trigger] related_prefix_projection_at(
            source, target, composed, index,
        ) by {
        let middle_index = first.points[index as int];
        assert(#[trigger] t3_layer::related_prefix_projection_at(
            source, middle, first, index,
        ));
        assert(index < first.points.len());
        assert(middle_index <= middle.events.len());
        assert({
            &&& middle_index < second.points.len()
            &&& second.points[middle_index as int] <= target.events.len()
            &&& #[trigger] t2_event_layer::t2_projection_agreement(
                middle.events.take(middle_index as int),
                target.events.take(
                    second.points[middle_index as int] as int,
                ),
            )
        });
        compose_index_map_point(first, second, index);
        projection_agreements_compose(
            source.events.take(index as int),
            middle.events.take(middle_index as int),
            target.events.take(
                second.points[middle_index as int] as int,
            ),
        );
    }
}

pub proof fn step_correspondences_compose(
    cfg: config_layer::FullConfig,
    source: wal_runtime_layer::WalExecution,
    middle: journal_runtime_layer::JournalExecution,
    target: execution_layer::BrokerExecution,
    first: t2_layer::WeakIndexMap,
    second: t2_layer::WeakIndexMap,
)
    requires
        journal_runtime_layer::exec(cfg, middle),
        t3_layer::weak_simulation_index_map(source, middle, first),
        t2_layer::weak_simulation_index_map(
            cfg, middle, target, second,
        ),
    ensures step_correspondence(
        source, target, compose_index_maps(first, second),
    ),
{
    let composed = compose_index_maps(first, second);
    assert forall|index: nat| index < source.events.len() implies {
        let left = #[trigger] composed.points[index as int];
        let right = composed.points[(index + 1) as int];
        &&& if left == right {
            composed_projection_silent(source.events[index as int])
        } else {
            &&& right == left + 1
            &&& left < target.events.len()
            &&& composed_event_match(
                source.events[index as int], target.events[left as int],
            )
        }
    } by {
        let middle_left = first.points[index as int];
        let middle_right = first.points[(index + 1) as int];
        assert(t2_layer::weak_index_shape(
            source.events.len(), middle.events.len(), first,
        ));
        assert(t2_layer::weak_index_shape(
            middle.events.len(), target.events.len(), second,
        ));
        weak_index_point_bounded(
            source.events.len(), middle.events.len(), first, index,
        );
        weak_index_point_bounded(
            source.events.len(), middle.events.len(), first, index + 1,
        );
        assert(second.points.len() == middle.events.len() + 1);
        assert(middle_left < second.points.len());
        assert(middle_right < second.points.len());
        compose_index_map_point(first, second, index);
        compose_index_map_point(first, second, index + 1);
        assert({
            let left = #[trigger] first.points[index as int];
            let right = first.points[(index + 1) as int];
            if left == right {
                t3_event_layer::t3_projection_silent(
                    source.events[index as int],
                )
            } else {
                &&& right == left + 1
                &&& left < middle.events.len()
                &&& t3_event_layer::event_match(
                    source.events[index as int],
                    middle.events[left as int],
                )
            }
        });
        if middle_left == middle_right {
            assert(composed.points[index as int]
                == composed.points[(index + 1) as int]);
        } else {
            assert(middle_right == middle_left + 1);
            assert(middle_left < middle.events.len());
            t2_step_correspondence_is_lockstep(
                cfg, middle, target, second, middle_left,
            );
            assert(second.points[middle_right as int]
                == second.points[middle_left as int] + 1);
            assert(composed.points[(index + 1) as int]
                == composed.points[index as int] + 1);
            event_matches_compose(
                source.events[index as int],
                middle.events[middle_left as int],
                target.events[second.points[middle_left as int] as int],
            );
        }
    }
}

pub proof fn weak_simulations_compose(
    cfg: config_layer::FullConfig,
    source: wal_runtime_layer::WalExecution,
    middle: journal_runtime_layer::JournalExecution,
    target: execution_layer::BrokerExecution,
    first: t2_layer::WeakIndexMap,
    second: t2_layer::WeakIndexMap,
)
    requires
        journal_runtime_layer::exec(cfg, middle),
        t3_layer::weak_simulation_index_map(source, middle, first),
        t2_layer::weak_simulation_index_map(
            cfg, middle, target, second,
        ),
    ensures weak_simulation_index_map(
        cfg, source, target, compose_index_maps(first, second),
    ),
{
    compose_weak_index_shapes(
        source.events.len(),
        middle.events.len(),
        target.events.len(),
        first,
        second,
    );
    step_correspondences_compose(
        cfg, source, middle, target, first, second,
    );
    related_prefixes_compose(
        cfg, source, middle, target, first, second,
    );
    related_prefix_projections_compose(
        cfg, source, middle, target, first, second,
    );
}

pub open spec fn mapped_prefixes_t1_safe(
    cfg: config_layer::FullConfig,
    source: wal_runtime_layer::WalExecution,
    target: execution_layer::BrokerExecution,
    map: t2_layer::WeakIndexMap,
) -> bool {
    forall|index: nat| index <= source.events.len() ==>
        #[trigger] t1_layer::t1_parameterized_safety_statement(
            cfg,
            execution_layer::execution_prefix(
                target, map.points[index as int],
            ),
        )
}

pub open spec fn t4_c0_statement(
    cfg: config_layer::FullConfig,
    source: wal_runtime_layer::WalExecution,
) -> bool {
    &&& wal_trace_layer::admissible_wal_trace(cfg, source)
    &&& wal_trace_layer::trace_agreement(cfg, source)
    &&& t3_layer::acknowledged_prefix_durable_through_execution(source)
    &&& exists|target: execution_layer::BrokerExecution,
               map: t2_layer::WeakIndexMap| {
        &&& execution_layer::exec(cfg, target)
        &&& weak_simulation_index_map(cfg, source, target, map)
        &&& t4_projection_agreement(source.events, target.events)
        &&& t1_layer::t1_parameterized_safety_statement(cfg, target)
        &&& mapped_prefixes_t1_safe(cfg, source, target, map)
    }
}

pub open spec fn canonical_middle_execution(
    source: wal_runtime_layer::WalExecution,
) -> journal_runtime_layer::JournalExecution {
    t3_layer::compressed_execution(source)
}

pub open spec fn canonical_target_execution(
    cfg: config_layer::FullConfig,
    source: wal_runtime_layer::WalExecution,
) -> execution_layer::BrokerExecution {
    t2_layer::lift_execution(cfg, canonical_middle_execution(source))
}

pub open spec fn canonical_composed_map(
    source: wal_runtime_layer::WalExecution,
) -> t2_layer::WeakIndexMap {
    let middle = canonical_middle_execution(source);
    compose_index_maps(
        t3_layer::compression_index_map(source.events),
        t2_layer::identity_index_map(middle.events.len()),
    )
}

pub proof fn canonical_composed_map_is_compression(
    source: wal_runtime_layer::WalExecution,
)
    ensures canonical_composed_map(source)
        == t3_layer::compression_index_map(source.events),
{
    t3_layer::compression_map_has_weak_shape(source.events);
    compose_with_identity(
        source.events.len(),
        canonical_middle_execution(source).events.len(),
        t3_layer::compression_index_map(source.events),
    );
}

pub proof fn full_projection_agreement_from_weak_simulation(
    cfg: config_layer::FullConfig,
    source: wal_runtime_layer::WalExecution,
    target: execution_layer::BrokerExecution,
    map: t2_layer::WeakIndexMap,
)
    requires weak_simulation_index_map(cfg, source, target, map),
    ensures t4_projection_agreement(source.events, target.events),
{
    assert(related_prefix_projection_at(
        source, target, map, source.events.len(),
    ));
    assert(map.points[source.events.len() as int]
        == target.events.len());
    assert(source.events.take(source.events.len() as int) =~= source.events);
    assert(target.events.take(target.events.len() as int) =~= target.events);
}

pub proof fn every_mapped_broker_prefix_is_t1_safe(
    cfg: config_layer::FullConfig,
    source: wal_runtime_layer::WalExecution,
    target: execution_layer::BrokerExecution,
    map: t2_layer::WeakIndexMap,
)
    requires
        config_layer::full_config_wf(cfg),
        execution_layer::exec(cfg, target),
        weak_simulation_index_map(cfg, source, target, map),
    ensures mapped_prefixes_t1_safe(cfg, source, target, map),
{
    assert forall|index: nat| index <= source.events.len() implies
        #[trigger] t1_layer::t1_parameterized_safety_statement(
            cfg,
            execution_layer::execution_prefix(
                target, map.points[index as int],
            ),
        ) by {
        weak_index_point_bounded(
            source.events.len(), target.events.len(), map, index,
        );
        t1_layer::t1_prefix_trace_agreement(
            cfg, target, map.points[index as int],
        );
    }
}

pub proof fn canonical_closed_wal_broker_composition(
    cfg: config_layer::FullConfig,
    source: wal_runtime_layer::WalExecution,
)
    requires
        config_layer::full_config_wf(cfg),
        wal_runtime_layer::exec(cfg, source),
    ensures
        execution_layer::exec(
            cfg, canonical_target_execution(cfg, source),
        ),
        weak_simulation_index_map(
            cfg,
            source,
            canonical_target_execution(cfg, source),
            canonical_composed_map(source),
        ),
        t4_projection_agreement(
            source.events,
            canonical_target_execution(cfg, source).events,
        ),
        t1_layer::t1_parameterized_safety_statement(
            cfg, canonical_target_execution(cfg, source),
        ),
        mapped_prefixes_t1_safe(
            cfg,
            source,
            canonical_target_execution(cfg, source),
            canonical_composed_map(source),
        ),
        t4_c0_statement(cfg, source),
{
    let middle = canonical_middle_execution(source);
    let target = canonical_target_execution(cfg, source);
    let first = t3_layer::compression_index_map(source.events);
    let second = t2_layer::identity_index_map(middle.events.len());
    let composed = canonical_composed_map(source);

    t3_layer::canonical_typed_wal_simulation(cfg, source);
    t2_layer::canonical_atomic_journal_simulation(cfg, middle);
    weak_simulations_compose(
        cfg, source, middle, target, first, second,
    );
    full_projection_agreement_from_weak_simulation(
        cfg, source, target, composed,
    );
    t1_layer::t1_parameterized_broker_safety_core(cfg, target);
    every_mapped_broker_prefix_is_t1_safe(
        cfg, source, target, composed,
    );
}

// Exported T4-C0 theorem.  This is intentionally not the contextual T4
// replacement theorem: it composes only the three closed runtime relations.
pub proof fn t4_c0_closed_wal_broker_composition<A>(
    cfg: t1_layer::PaperConfig<A>,
    source: wal_runtime_layer::WalExecution,
)
    requires
        t1_layer::paper_config_wf(cfg),
        wal_runtime_layer::exec(
            t1_layer::paper_broker_config(cfg), source,
        ),
    ensures t4_c0_statement(
        t1_layer::paper_broker_config(cfg), source,
    ),
{
    canonical_closed_wal_broker_composition(
        t1_layer::paper_broker_config(cfg), source,
    );
}

} // verus!
