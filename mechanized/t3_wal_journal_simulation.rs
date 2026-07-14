use vstd::prelude::*;

#[path = "t3_wal_representation.rs"]
pub mod representation_layer;

verus! {

use representation_layer::event_layer;
use event_layer::trace_layer;
use trace_layer::runtime_layer;
use runtime_layer::t2_layer;
use t2_layer::representation_layer::event_layer::trace_layer
    as journal_trace_layer;
use journal_trace_layer::runtime_layer as journal_runtime_layer;
use journal_runtime_layer::t1_layer;
use t1_layer::execution_layer;
use execution_layer::projection_layer;
use projection_layer::global_layer;
use global_layer::bridge_layer;
use bridge_layer::contract_layer;
use contract_layer::p3_layer::p2_layer::p1_layer::p0_layer;
use p0_layer::config_layer;
use config_layer::broker_layer::query_layer::c1_layer::append_layer;

// A deterministic compression retains the projected initial state and then
// retains one projected post-state for each WAL event visible at the atomic
// Journal boundary.
pub open spec fn compress_configurations(
    configs: Seq<runtime_layer::WalConfiguration>,
    events: Seq<global_layer::GlobalEvent>,
) -> Seq<journal_runtime_layer::JournalConfiguration>
    decreases events.len()
{
    if configs.len() != events.len() + 1 {
        Seq::empty()
    } else if events.len() == 0 {
        Seq::empty().push(runtime_layer::journal_projection(configs[0]))
    } else {
        let prefix = compress_configurations(
            configs.drop_last(), events.drop_last(),
        );
        match event_layer::translate_event(events.last()) {
            Option::Some(_) => prefix.push(
                runtime_layer::journal_projection(configs.last()),
            ),
            Option::None => prefix,
        }
    }
}

pub open spec fn compressed_execution(
    source: runtime_layer::WalExecution,
) -> journal_runtime_layer::JournalExecution {
    journal_runtime_layer::JournalExecution {
        configs: compress_configurations(source.configs, source.events),
        events: event_layer::translate_trace(source.events),
    }
}

pub open spec fn compression_index_map(
    events: Seq<global_layer::GlobalEvent>,
) -> t2_layer::WeakIndexMap {
    t2_layer::WeakIndexMap {
        points: Seq::new((events.len() + 1) as nat, |index: int|
            event_layer::matched_count(events.take(index))),
    }
}

pub struct CompressionWitness {
    pub target: journal_runtime_layer::JournalExecution,
    pub map: t2_layer::WeakIndexMap,
}

pub open spec fn compression_witness(
    source: runtime_layer::WalExecution,
) -> CompressionWitness {
    CompressionWitness {
        target: compressed_execution(source),
        map: compression_index_map(source.events),
    }
}

pub open spec fn related_prefixes(
    source: runtime_layer::WalExecution,
    target: journal_runtime_layer::JournalExecution,
    map: t2_layer::WeakIndexMap,
) -> bool {
    forall|index: nat| index <= source.events.len() ==> {
        &&& index < source.configs.len()
        &&& index < map.points.len()
        &&& #[trigger] map.points[index as int] < target.configs.len()
        &&& representation_layer::representation(
            source.configs[index as int],
            target.configs[map.points[index as int] as int],
        )
    }
}

pub open spec fn related_prefix_projection_at(
    source: runtime_layer::WalExecution,
    target: journal_runtime_layer::JournalExecution,
    map: t2_layer::WeakIndexMap,
    index: nat,
) -> bool {
    &&& index < map.points.len()
    &&& map.points[index as int] <= target.events.len()
    &&& event_layer::t3_projection_agreement(
        source.events.take(index as int),
        target.events.take(map.points[index as int] as int),
    )
}

pub open spec fn related_prefix_projections(
    source: runtime_layer::WalExecution,
    target: journal_runtime_layer::JournalExecution,
    map: t2_layer::WeakIndexMap,
) -> bool {
    forall|index: nat| index <= source.events.len() ==>
        #[trigger] related_prefix_projection_at(source, target, map, index)
}

pub open spec fn step_correspondence(
    source: runtime_layer::WalExecution,
    target: journal_runtime_layer::JournalExecution,
    map: t2_layer::WeakIndexMap,
) -> bool {
    forall|index: nat| index < source.events.len() ==> {
        let left = #[trigger] map.points[index as int];
        let right = map.points[(index + 1) as int];
        &&& if left == right {
            event_layer::t3_projection_silent(source.events[index as int])
        } else {
            &&& right == left + 1
            &&& left < target.events.len()
            &&& event_layer::event_match(
                source.events[index as int], target.events[left as int],
            )
        }
    }
}

pub open spec fn weak_simulation_index_map(
    source: runtime_layer::WalExecution,
    target: journal_runtime_layer::JournalExecution,
    map: t2_layer::WeakIndexMap,
) -> bool {
    &&& t2_layer::weak_index_shape(
        source.events.len(), target.events.len(), map,
    )
    &&& step_correspondence(source, target, map)
    &&& related_prefixes(source, target, map)
    &&& related_prefix_projections(source, target, map)
}

pub open spec fn acknowledged_prefix_durable_through_execution(
    source: runtime_layer::WalExecution,
) -> bool {
    forall|earlier: nat, later: nat|
        earlier <= later && later <= source.events.len() ==> {
            #[trigger] append_layer::is_prefix(
                source.configs[earlier as int].evidence.acknowledged_prefix,
                runtime_layer::journal_view(source.configs[later as int]),
            )
        }
}

pub open spec fn t3_simulation_statement(
    cfg: config_layer::FullConfig,
    source: runtime_layer::WalExecution,
) -> bool {
    &&& acknowledged_prefix_durable_through_execution(source)
    &&& exists|target: journal_runtime_layer::JournalExecution,
               map: t2_layer::WeakIndexMap| {
        &&& journal_runtime_layer::exec(cfg, target)
        &&& weak_simulation_index_map(source, target, map)
        &&& event_layer::t3_projection_agreement(
            source.events, target.events,
        )
    }
}

pub proof fn take_succ<T>(items: Seq<T>, index: nat)
    requires index < items.len(),
    ensures items.take((index + 1) as int)
        == items.take(index as int).push(items[index as int]),
{
    assert(items.take((index + 1) as int) =~=
        items.take(index as int).push(items[index as int]));
}

pub proof fn prefix_transitive<T>(
    first: Seq<T>, middle: Seq<T>, last: Seq<T>,
)
    requires
        append_layer::is_prefix(first, middle),
        append_layer::is_prefix(middle, last),
    ensures append_layer::is_prefix(first, last),
{
    assert(first.len() <= middle.len());
    assert(middle.len() <= last.len());
    assert(first == middle.take(first.len() as int));
    assert(middle == last.take(middle.len() as int));
    assert(last.take(middle.len() as int).take(first.len() as int) =~=
        last.take(first.len() as int));
}

pub proof fn compression_map_point(
    events: Seq<global_layer::GlobalEvent>,
    index: nat,
)
    requires index <= events.len(),
    ensures compression_index_map(events).points[index as int]
        == event_layer::matched_count(events.take(index as int)),
{
}

pub proof fn matched_count_step(
    events: Seq<global_layer::GlobalEvent>,
    index: nat,
)
    requires index < events.len(),
    ensures event_layer::matched_count(events.take((index + 1) as int))
        == event_layer::matched_count(events.take(index as int))
            + match event_layer::translate_event(events[index as int]) {
                Option::Some(_) => 1nat,
                Option::None => 0nat,
            },
{
    take_succ(events, index);
    event_layer::matched_count_push(
        events.take(index as int), events[index as int],
    );
}

pub proof fn compression_map_has_weak_shape(
    events: Seq<global_layer::GlobalEvent>,
)
    ensures t2_layer::weak_index_shape(
        events.len(),
        event_layer::translate_trace(events).len(),
        compression_index_map(events),
    ),
{
    let map = compression_index_map(events);
    event_layer::translate_trace_len(events);
    assert(map.points.len() == events.len() + 1);
    assert(map.points[0] == 0);
    assert(events.take(events.len() as int) =~= events);
    assert(map.points[events.len() as int]
        == event_layer::matched_count(events));
    assert forall|index: nat| index < events.len() implies {
        let left = #[trigger] map.points[index as int];
        let right = map.points[(index + 1) as int];
        &&& left <= right
        &&& right <= event_layer::translate_trace(events).len()
        &&& (right == left || right == left + 1)
    } by {
        compression_map_point(events, index);
        compression_map_point(events, index + 1);
        matched_count_step(events, index);
        event_layer::matched_count_take_le(events, index + 1);
        match event_layer::translate_event(events[index as int]) {
            Option::Some(_) => {},
            Option::None => {},
        }
    }
}

pub proof fn compressed_configurations_len(
    configs: Seq<runtime_layer::WalConfiguration>,
    events: Seq<global_layer::GlobalEvent>,
)
    requires configs.len() == events.len() + 1,
    ensures compress_configurations(configs, events).len()
        == event_layer::matched_count(events) + 1,
    decreases events.len(),
{
    if events.len() == 0 {
        assert(configs.len() == 1);
    } else {
        assert(configs.drop_last().len() == events.drop_last().len() + 1);
        compressed_configurations_len(
            configs.drop_last(), events.drop_last(),
        );
        event_layer::matched_count_push(
            events.drop_last(), events.last(),
        );
        assert(events.drop_last().push(events.last()) =~= events);
        match event_layer::translate_event(events.last()) {
            Option::Some(_) => {},
            Option::None => {},
        }
    }
}

pub proof fn compression_unfold_last(
    source: runtime_layer::WalExecution,
)
    requires
        source.events.len() > 0,
        source.configs.len() == source.events.len() + 1,
    ensures {
        let length: nat = (source.events.len() - 1) as nat;
        let prefix = runtime_layer::execution_prefix(source, length);
        &&& prefix.events == source.events.drop_last()
        &&& prefix.configs == source.configs.drop_last()
        &&& compressed_execution(source).events ==
            match event_layer::translate_event(source.events.last()) {
                Option::Some(target) =>
                    compressed_execution(prefix).events.push(target),
                Option::None => compressed_execution(prefix).events,
            }
        &&& compressed_execution(source).configs ==
            match event_layer::translate_event(source.events.last()) {
                Option::Some(_) => compressed_execution(prefix).configs.push(
                    runtime_layer::journal_projection(source.configs.last()),
                ),
                Option::None => compressed_execution(prefix).configs,
            }
    },
{
    let length: nat = (source.events.len() - 1) as nat;
    let prefix = runtime_layer::execution_prefix(source, length);
    assert(prefix.events =~= source.events.drop_last());
    assert(prefix.configs =~= source.configs.drop_last());
    event_layer::translate_trace_push(
        source.events.drop_last(), source.events.last(),
    );
    assert(source.events.drop_last().push(source.events.last()) =~=
        source.events);
}

pub proof fn compressed_execution_is_journal_execution(
    cfg: config_layer::FullConfig,
    source: runtime_layer::WalExecution,
)
    requires runtime_layer::exec(cfg, source),
    ensures journal_runtime_layer::exec(cfg, compressed_execution(source)),
    decreases source.events.len(),
{
    let target = compressed_execution(source);
    if source.events.len() == 0 {
        assert(source.configs.len() == 1);
        assert(source.configs[0] == runtime_layer::initial_configuration(cfg));
        representation_layer::initial_projection(cfg);
        assert(target.configs.len() == 1);
        assert(target.events.len() == 0);
        assert(target.configs[0]
            == journal_runtime_layer::initial_configuration(cfg));
    } else {
        let length: nat = (source.events.len() - 1) as nat;
        let prefix = runtime_layer::execution_prefix(source, length);
        runtime_layer::exec_prefix(cfg, source, length);
        compressed_execution_is_journal_execution(cfg, prefix);
        compression_unfold_last(source);
        let before = source.configs[length as int];
        let after = source.configs[(length + 1) as int];
        let source_event = source.events[length as int];
        assert(source_event == source.events.last());
        assert(after == source.configs.last());
        assert(runtime_layer::wal_runtime_step(
            cfg, before, source_event, after,
        ));
        runtime_layer::every_exec_configuration_is_basic(cfg, source);
        match event_layer::translate_event(source_event) {
            Option::Some(target_event) => {
                representation_layer::matched_runtime_step_commutes(
                    cfg, before, source_event, target_event, after,
                );
                let prefix_target = compressed_execution(prefix);
                compressed_configuration_at_prefix(
                    cfg, prefix, prefix.events.len(),
                );
                compressed_configurations_len(
                    prefix.configs, prefix.events,
                );
                assert(prefix.events.take(prefix.events.len() as int) =~=
                    prefix.events);
                assert(target.events == prefix_target.events.push(target_event));
                assert(target.configs == prefix_target.configs.push(
                    runtime_layer::journal_projection(after),
                ));
                assert(target.configs.len() == target.events.len() + 1);
                assert(target.configs[0] == prefix_target.configs[0]);
                assert forall|index: nat| index < target.events.len() implies
                    #[trigger] journal_runtime_layer::journal_runtime_step(
                        cfg,
                        target.configs[index as int],
                        target.events[index as int],
                        target.configs[(index + 1) as int],
                    ) by {
                    if index < prefix_target.events.len() {
                        assert(target.events[index as int]
                            == prefix_target.events[index as int]);
                        assert(target.configs[index as int]
                            == prefix_target.configs[index as int]);
                        assert(target.configs[(index + 1) as int]
                            == prefix_target.configs[(index + 1) as int]);
                    } else {
                        assert(index == prefix_target.events.len());
                        assert(prefix_target.configs.len()
                            == prefix_target.events.len() + 1);
                        assert(prefix_target.configs.last()
                            == runtime_layer::journal_projection(before));
                    }
                }
            },
            Option::None => {
                representation_layer::internal_runtime_step_preserves_projection(
                    cfg, before, source_event, after,
                );
                assert(target == compressed_execution(prefix));
            },
        }
    }
}

pub proof fn compressed_configuration_at_prefix(
    cfg: config_layer::FullConfig,
    source: runtime_layer::WalExecution,
    index: nat,
)
    requires
        runtime_layer::exec(cfg, source),
        index <= source.events.len(),
    ensures
        event_layer::matched_count(source.events.take(index as int))
            < compressed_execution(source).configs.len(),
        compressed_execution(source).configs[
            event_layer::matched_count(source.events.take(index as int)) as int
        ] == runtime_layer::journal_projection(source.configs[index as int]),
    decreases source.events.len(),
{
    compressed_configurations_len(source.configs, source.events);
    event_layer::matched_count_take_le(source.events, index);
    if source.events.len() == 0 {
        assert(index == 0);
        assert(compressed_execution(source).configs[0]
            == runtime_layer::journal_projection(source.configs[0]));
    } else {
        let length: nat = (source.events.len() - 1) as nat;
        let prefix = runtime_layer::execution_prefix(source, length);
        runtime_layer::exec_prefix(cfg, source, length);
        compression_unfold_last(source);
        compressed_configurations_len(prefix.configs, prefix.events);
        let target = compressed_execution(source);
        let prefix_target = compressed_execution(prefix);
        if index < source.events.len() {
            assert(index <= length);
            compressed_configuration_at_prefix(cfg, prefix, index);
            assert(prefix.events.take(index as int) =~=
                source.events.take(index as int));
            assert(prefix.configs[index as int]
                == source.configs[index as int]);
            let count = event_layer::matched_count(
                source.events.take(index as int),
            );
            assert(count == event_layer::matched_count(
                prefix.events.take(index as int),
            ));
            assert(count < prefix_target.configs.len());
            match event_layer::translate_event(source.events.last()) {
                Option::Some(_) => {
                    assert(target.configs == prefix_target.configs.push(
                        runtime_layer::journal_projection(source.configs.last()),
                    ));
                    assert(target.configs[count as int]
                        == prefix_target.configs[count as int]);
                },
                Option::None => {
                    assert(target.configs == prefix_target.configs);
                },
            }
            assert(target.configs[count as int]
                == runtime_layer::journal_projection(
                    source.configs[index as int],
                ));
        } else {
            assert(index == source.events.len());
            assert(index == length + 1);
            assert(source.events.take(index as int) =~= source.events);
            let before = source.configs[length as int];
            let after = source.configs[(length + 1) as int];
            let source_event = source.events[length as int];
            assert(source_event == source.events.last());
            assert(after == source.configs.last());
            assert(source.configs[index as int] == after);
            assert(runtime_layer::wal_runtime_step(
                cfg, before, source_event, after,
            ));
            event_layer::matched_count_push(
                source.events.drop_last(), source.events.last(),
            );
            assert(source.events.drop_last().push(source.events.last()) =~=
                source.events);
            match event_layer::translate_event(source_event) {
                Option::Some(_) => {
                    let prefix_count = event_layer::matched_count(prefix.events);
                    assert(prefix.events == source.events.drop_last());
                    assert(event_layer::matched_count(source.events)
                        == prefix_count + 1);
                    assert(prefix_target.configs.len() == prefix_count + 1);
                    assert(target.configs == prefix_target.configs.push(
                        runtime_layer::journal_projection(after),
                    ));
                    assert(target.configs[(prefix_count + 1) as int]
                        == runtime_layer::journal_projection(after));
                    assert(event_layer::matched_count(
                        source.events.take(index as int),
                    ) == prefix_count + 1);
                    assert(target.configs[
                        event_layer::matched_count(
                            source.events.take(index as int),
                        ) as int
                    ] == runtime_layer::journal_projection(
                        source.configs[index as int],
                    ));
                },
                Option::None => {
                    compressed_configuration_at_prefix(cfg, prefix, length);
                    representation_layer::internal_runtime_step_preserves_projection(
                        cfg, before, source_event, after,
                    );
                    assert(prefix.events == source.events.drop_last());
                    assert(event_layer::matched_count(source.events)
                        == event_layer::matched_count(prefix.events));
                    assert(target.configs == prefix_target.configs);
                    assert(length == prefix.events.len());
                    assert(prefix.events.take(length as int) =~= prefix.events);
                    let prefix_count = event_layer::matched_count(prefix.events);
                    assert(prefix.configs[length as int] == before);
                    assert(prefix_target.configs[prefix_count as int]
                        == runtime_layer::journal_projection(before));
                    assert(event_layer::matched_count(
                        source.events.take(index as int),
                    ) == prefix_count);
                    assert(target.configs[
                        event_layer::matched_count(
                            source.events.take(index as int),
                        ) as int
                    ] == runtime_layer::journal_projection(
                        source.configs[index as int],
                    ));
                },
            }
            assert(target.configs[
                event_layer::matched_count(
                    source.events.take(index as int),
                ) as int
            ] == runtime_layer::journal_projection(
                source.configs[index as int],
            ));
        }
    }
}

pub proof fn compression_related_prefixes(
    cfg: config_layer::FullConfig,
    source: runtime_layer::WalExecution,
)
    requires runtime_layer::exec(cfg, source),
    ensures related_prefixes(
        source,
        compressed_execution(source),
        compression_index_map(source.events),
    ),
{
    let target = compressed_execution(source);
    let map = compression_index_map(source.events);
    assert forall|index: nat| index <= source.events.len() implies {
        &&& index < source.configs.len()
        &&& index < map.points.len()
        &&& #[trigger] map.points[index as int] < target.configs.len()
        &&& representation_layer::representation(
            source.configs[index as int],
            target.configs[map.points[index as int] as int],
        )
    } by {
        compression_map_point(source.events, index);
        compressed_configuration_at_prefix(cfg, source, index);
        representation_layer::projection_satisfies_representation(
            source.configs[index as int],
        );
    }
}

pub proof fn compression_related_prefix_projections(
    cfg: config_layer::FullConfig,
    source: runtime_layer::WalExecution,
)
    requires runtime_layer::exec(cfg, source),
    ensures related_prefix_projections(
        source,
        compressed_execution(source),
        compression_index_map(source.events),
    ),
{
    let target = compressed_execution(source);
    let map = compression_index_map(source.events);
    assert forall|index: nat| index <= source.events.len() implies
        #[trigger] related_prefix_projection_at(source, target, map, index) by {
        assert({
            &&& index < map.points.len()
            &&& map.points[index as int] <= target.events.len()
            &&& event_layer::t3_projection_agreement(
                source.events.take(index as int),
                target.events.take(map.points[index as int] as int),
            )
        }) by {
            compression_map_point(source.events, index);
            event_layer::matched_count_take_le(source.events, index);
            event_layer::translate_trace_len(source.events);
            event_layer::translate_trace_take(source.events, index);
            let prefix = runtime_layer::execution_prefix(source, index);
            runtime_layer::exec_prefix(cfg, source, index);
            runtime_layer::exec_trace_closed(cfg, prefix);
            assert(prefix.events =~= source.events.take(index as int));
            event_layer::translated_trace_projection_agreement(prefix.events);
            assert(target.events == event_layer::translate_trace(source.events));
            let source_prefix = source.events.take(index as int);
            let target_prefix = target.events.take(map.points[index as int] as int);
            assert(target_prefix == event_layer::translate_trace(source_prefix));
            assert(event_layer::t3_projection_agreement(
                source_prefix, target_prefix,
            ));
        }
    }
}

pub proof fn compression_step_correspondence(
    cfg: config_layer::FullConfig,
    source: runtime_layer::WalExecution,
)
    requires runtime_layer::exec(cfg, source),
    ensures step_correspondence(
        source,
        compressed_execution(source),
        compression_index_map(source.events),
    ),
{
    runtime_layer::exec_trace_closed(cfg, source);
    let map = compression_index_map(source.events);
    let target = compressed_execution(source);
    assert forall|index: nat| index < source.events.len() implies {
        let left = #[trigger] map.points[index as int];
        let right = map.points[(index + 1) as int];
        &&& if left == right {
            event_layer::t3_projection_silent(source.events[index as int])
        } else {
            &&& right == left + 1
            &&& left < target.events.len()
            &&& event_layer::event_match(
                source.events[index as int], target.events[left as int],
            )
        }
    } by {
        compression_map_point(source.events, index);
        compression_map_point(source.events, index + 1);
        matched_count_step(source.events, index);
        let source_event = source.events[index as int];
        runtime_layer::wal_step_is_closed(
            cfg,
            source.configs[index as int],
            source_event,
            source.configs[(index + 1) as int],
        );
        match event_layer::translate_event(source_event) {
            Option::Some(target_event) => {
                event_layer::translate_trace_index(
                    source.events, index, target_event,
                );
            },
            Option::None => {
                event_layer::translation_silence_classifier_exact(source_event);
            },
        }
    }
}

pub proof fn compression_is_weak_simulation(
    cfg: config_layer::FullConfig,
    source: runtime_layer::WalExecution,
)
    requires runtime_layer::exec(cfg, source),
    ensures weak_simulation_index_map(
        source,
        compressed_execution(source),
        compression_index_map(source.events),
    ),
{
    compression_map_has_weak_shape(source.events);
    compression_step_correspondence(cfg, source);
    compression_related_prefixes(cfg, source);
    compression_related_prefix_projections(cfg, source);
}

pub proof fn execution_parse_monotone_between(
    cfg: config_layer::FullConfig,
    source: runtime_layer::WalExecution,
    earlier: nat,
    later: nat,
)
    requires
        runtime_layer::exec(cfg, source),
        earlier <= later,
        later <= source.events.len(),
    ensures append_layer::is_prefix(
        runtime_layer::journal_view(source.configs[earlier as int]),
        runtime_layer::journal_view(source.configs[later as int]),
    ),
    decreases later - earlier,
{
    if earlier == later {
        append_layer::prefix_reflexive(
            runtime_layer::journal_view(source.configs[earlier as int]),
        );
    } else {
        let previous: nat = (later - 1) as nat;
        assert(previous < source.events.len());
        assert(later == previous + 1);
        assert(runtime_layer::wal_runtime_step(
            cfg,
            source.configs[previous as int],
            source.events[previous as int],
            source.configs[(previous + 1) as int],
        ));
        execution_parse_monotone_between(
            cfg, source, earlier, previous,
        );
        runtime_layer::every_exec_configuration_is_basic(cfg, source);
        assert(runtime_layer::basic_invariant(
            cfg, source.configs[previous as int],
        ));
        assert(runtime_layer::wal_invariant(
            cfg,
            source.configs[previous as int].runtime.store,
            source.configs[previous as int].runtime.mode,
            source.configs[previous as int].runtime.append,
        ));
        runtime_layer::runtime_step_parse_monotone(
            cfg,
            source.configs[previous as int],
            source.events[previous as int],
            source.configs[later as int],
        );
        prefix_transitive(
            runtime_layer::journal_view(source.configs[earlier as int]),
            runtime_layer::journal_view(source.configs[previous as int]),
            runtime_layer::journal_view(source.configs[later as int]),
        );
    }
}

pub proof fn execution_acknowledged_prefix_is_durable(
    cfg: config_layer::FullConfig,
    source: runtime_layer::WalExecution,
)
    requires runtime_layer::exec(cfg, source),
    ensures acknowledged_prefix_durable_through_execution(source),
{
    runtime_layer::every_exec_configuration_is_basic(cfg, source);
    assert forall|earlier: nat, later: nat|
        earlier <= later && later <= source.events.len() implies {
            #[trigger] append_layer::is_prefix(
                source.configs[earlier as int].evidence.acknowledged_prefix,
                runtime_layer::journal_view(source.configs[later as int]),
            )
        } by {
        assert(earlier < source.configs.len());
        runtime_layer::basic_invariant_acknowledged_prefix_durable(
            cfg, source.configs[earlier as int],
        );
        execution_parse_monotone_between(
            cfg, source, earlier, later,
        );
        prefix_transitive(
            source.configs[earlier as int].evidence.acknowledged_prefix,
            runtime_layer::journal_view(source.configs[earlier as int]),
            runtime_layer::journal_view(source.configs[later as int]),
        );
    }
}

pub proof fn canonical_typed_wal_simulation(
    cfg: config_layer::FullConfig,
    source: runtime_layer::WalExecution,
)
    requires
        config_layer::full_config_wf(cfg),
        runtime_layer::exec(cfg, source),
    ensures
        trace_layer::admissible_wal_trace(cfg, source),
        trace_layer::trace_agreement(cfg, source),
        journal_runtime_layer::exec(cfg, compressed_execution(source)),
        weak_simulation_index_map(
            source,
            compressed_execution(source),
            compression_index_map(source.events),
        ),
        event_layer::t3_projection_agreement(
            source.events, compressed_execution(source).events,
        ),
        acknowledged_prefix_durable_through_execution(source),
        t3_simulation_statement(cfg, source),
{
    trace_layer::exec_implies_admissible_wal_trace(cfg, source);
    trace_layer::trace_agreement_for_exec(cfg, source);
    runtime_layer::exec_trace_closed(cfg, source);
    compressed_execution_is_journal_execution(cfg, source);
    compression_is_weak_simulation(cfg, source);
    event_layer::translated_trace_projection_agreement(source.events);
    execution_acknowledged_prefix_is_durable(cfg, source);
    let target = compressed_execution(source);
    let map = compression_index_map(source.events);
    assert(journal_runtime_layer::exec(cfg, target));
    assert(weak_simulation_index_map(source, target, map));
}

// Exported paper theorem.  Its explicit admissibility premise mirrors the
// normative T3 statement; the canonical theorem derives both admissibility
// and TraceAgreement from the typed runtime execution.
pub proof fn t3_typed_wal_runtime_simulation<A>(
    cfg: t1_layer::PaperConfig<A>,
    source: runtime_layer::WalExecution,
)
    requires
        t1_layer::paper_config_wf(cfg),
        runtime_layer::exec(t1_layer::paper_broker_config(cfg), source),
        trace_layer::admissible_wal_trace(
            t1_layer::paper_broker_config(cfg), source,
        ),
    ensures t3_simulation_statement(
        t1_layer::paper_broker_config(cfg), source,
    ),
{
    canonical_typed_wal_simulation(
        t1_layer::paper_broker_config(cfg), source,
    );
}

} // verus!
