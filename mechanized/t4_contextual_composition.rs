use vstd::prelude::*;

#[path = "t4_context_interface.rs"]
pub mod t4_c1_layer;

verus! {

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

// T4-C2 lifts the canonical closed T4-C0 composition through the T4-C1
// context interface. Context states are compressed by the T3 event
// translation, so every retained Journal/Broker step has one synchronized
// context-state step and every private WAL step remains inside one map fiber.

pub open spec fn compress_contexts<S>(
    contexts: Seq<S>,
    events: Seq<global_layer::GlobalEvent>,
) -> Seq<S>
    decreases events.len()
{
    if contexts.len() != events.len() + 1 {
        Seq::empty()
    } else if events.len() == 0 {
        Seq::empty().push(contexts[0])
    } else {
        let prefix = compress_contexts(
            contexts.drop_last(), events.drop_last(),
        );
        match t3_event_layer::translate_event(events.last()) {
            Option::Some(_) => prefix.push(contexts.last()),
            Option::None => prefix,
        }
    }
}

pub open spec fn canonical_plugged_journal_execution<S>(
    source: t4_c1_layer::PluggedWalExecution<S>,
) -> t4_c1_layer::PluggedJournalExecution<S> {
    t4_c1_layer::PluggedJournalExecution {
        machine: t4_c0_layer::canonical_middle_execution(source.machine),
        contexts: compress_contexts(source.contexts, source.machine.events),
    }
}

pub open spec fn canonical_plugged_broker_execution<S>(
    cfg: config_layer::FullConfig,
    source: t4_c1_layer::PluggedWalExecution<S>,
) -> t4_c1_layer::PluggedBrokerExecution<S> {
    t4_c1_layer::PluggedBrokerExecution {
        machine: t4_c0_layer::canonical_target_execution(cfg, source.machine),
        contexts: compress_contexts(source.contexts, source.machine.events),
    }
}

pub open spec fn lifted_plugged_broker_execution<S>(
    cfg: config_layer::FullConfig,
    source: t4_c1_layer::PluggedJournalExecution<S>,
) -> t4_c1_layer::PluggedBrokerExecution<S> {
    t4_c1_layer::PluggedBrokerExecution {
        machine: t2_layer::lift_execution(cfg, source.machine),
        contexts: source.contexts,
    }
}

pub open spec fn mapped_context_states_equal<S>(
    source: t4_c1_layer::PluggedWalExecution<S>,
    target: t4_c1_layer::PluggedBrokerExecution<S>,
    map: t2_layer::WeakIndexMap,
) -> bool {
    forall|index: nat| index <= source.machine.events.len() ==> {
        &&& index < source.contexts.len()
        &&& index < map.points.len()
        &&& #[trigger] map.points[index as int] < target.contexts.len()
        &&& source.contexts[index as int]
            == target.contexts[map.points[index as int] as int]
    }
}

pub open spec fn mapped_context_views_equal<S>(
    cfg: config_layer::FullConfig,
    source: t4_c1_layer::PluggedWalExecution<S>,
    target: t4_c1_layer::PluggedBrokerExecution<S>,
    map: t2_layer::WeakIndexMap,
) -> bool {
    forall|index: nat| index <= source.machine.events.len() ==> {
        &&& index < map.points.len()
        &&& index < source.machine.configs.len()
        &&& map.points[index as int] <= target.machine.events.len()
        &&& map.points[index as int] < target.machine.configs.len()
        &&& #[trigger] t4_c1_layer::wal_context_view_at(
            cfg, source.machine, index,
        ) == t4_c1_layer::broker_context_view_at(
            cfg, target.machine, map.points[index as int],
        )
    }
}

pub open spec fn t4_c2_statement<S>(
    cfg: config_layer::FullConfig,
    context: t4_c1_layer::ProgramContext<S>,
    source: t4_c1_layer::PluggedWalExecution<S>,
) -> bool {
    let target = canonical_plugged_broker_execution(cfg, source);
    let map = t4_c0_layer::canonical_composed_map(source.machine);
    &&& t4_c1_layer::plugged_broker_exec(cfg, context, target)
    &&& t4_c0_layer::weak_simulation_index_map(
        cfg, source.machine, target.machine, map,
    )
    &&& mapped_context_states_equal(source, target, map)
    &&& mapped_context_views_equal(cfg, source, target, map)
    &&& t4_c0_layer::t4_projection_agreement(
        source.machine.events, target.machine.events,
    )
    &&& t1_layer::t1_parameterized_safety_statement(cfg, target.machine)
    &&& t4_c0_layer::mapped_prefixes_t1_safe(
        cfg, source.machine, target.machine, map,
    )
    &&& t4_c0_layer::t4_c0_statement(cfg, source.machine)
}

pub proof fn compressed_contexts_len<S>(
    contexts: Seq<S>,
    events: Seq<global_layer::GlobalEvent>,
)
    requires contexts.len() == events.len() + 1,
    ensures compress_contexts(contexts, events).len()
        == t3_event_layer::matched_count(events) + 1,
    decreases events.len(),
{
    if events.len() == 0 {
        assert(contexts.len() == 1);
    } else {
        assert(contexts.drop_last().len() == events.drop_last().len() + 1);
        compressed_contexts_len(contexts.drop_last(), events.drop_last());
        t3_event_layer::matched_count_push(
            events.drop_last(), events.last(),
        );
        assert(events.drop_last().push(events.last()) =~= events);
        match t3_event_layer::translate_event(events.last()) {
            Option::Some(_) => {},
            Option::None => {},
        }
    }
}

pub proof fn compressed_contexts_unfold_last<S>(
    contexts: Seq<S>,
    events: Seq<global_layer::GlobalEvent>,
)
    requires
        events.len() > 0,
        contexts.len() == events.len() + 1,
    ensures compress_contexts(contexts, events) ==
        match t3_event_layer::translate_event(events.last()) {
            Option::Some(_) => compress_contexts(
                contexts.drop_last(), events.drop_last(),
            ).push(contexts.last()),
            Option::None => compress_contexts(
                contexts.drop_last(), events.drop_last(),
            ),
        },
{
}

pub proof fn erased_wal_step_stutters_context<S>(
    cfg: config_layer::FullConfig,
    context: t4_c1_layer::ProgramContext<S>,
    before_machine: wal_runtime_layer::WalConfiguration,
    event: global_layer::GlobalEvent,
    after_machine: wal_runtime_layer::WalConfiguration,
    before_context: S,
    before_view: t4_c1_layer::ContextView,
    after_view: t4_c1_layer::ContextView,
    after_context: S,
)
    requires
        wal_runtime_layer::wal_runtime_step(
            cfg, before_machine, event, after_machine,
        ),
        t3_event_layer::translate_event(event).is_none(),
        t4_c1_layer::context_accepts_step(
            context,
            before_context,
            before_view,
            event,
            after_view,
            after_context,
        ),
    ensures
        after_view == before_view,
        after_context == before_context,
{
    wal_runtime_layer::wal_step_is_closed(
        cfg, before_machine, event, after_machine,
    );
    t3_event_layer::wal_translation_classifier_exact(event);
    t4_c1_layer::t3_internal_events_have_empty_context_delta(event);
    assert(t4_c1_layer::context_delta(event).len() == 0);
}

pub proof fn compressed_context_at_prefix<S>(
    cfg: config_layer::FullConfig,
    context: t4_c1_layer::ProgramContext<S>,
    source: t4_c1_layer::PluggedWalExecution<S>,
    index: nat,
)
    requires
        t4_c1_layer::plugged_wal_exec(cfg, context, source),
        index <= source.machine.events.len(),
    ensures
        t3_event_layer::matched_count(
            source.machine.events.take(index as int),
        ) < compress_contexts(
            source.contexts, source.machine.events,
        ).len(),
        compress_contexts(
            source.contexts, source.machine.events,
        )[t3_event_layer::matched_count(
            source.machine.events.take(index as int),
        ) as int] == source.contexts[index as int],
    decreases source.machine.events.len(),
{
    compressed_contexts_len(source.contexts, source.machine.events);
    t3_event_layer::matched_count_take_le(source.machine.events, index);
    if source.machine.events.len() == 0 {
        assert(index == 0);
        assert(source.contexts.len() == 1);
        assert(source.machine.events.take(index as int) =~= Seq::empty());
        assert(t3_event_layer::matched_count(
            source.machine.events.take(index as int),
        ) == 0);
        assert(compress_contexts(
            source.contexts, source.machine.events,
        ) == Seq::empty().push(source.contexts[0]));
        assert(compress_contexts(
            source.contexts, source.machine.events,
        )[t3_event_layer::matched_count(
            source.machine.events.take(index as int),
        ) as int] == source.contexts[index as int]);
    } else {
        let length: nat = (source.machine.events.len() - 1) as nat;
        let prefix = t4_c1_layer::plugged_wal_prefix(source, length);
        t4_c1_layer::plugged_wal_prefix_closed(
            cfg, context, source, length,
        );
        assert(prefix.machine.events =~= source.machine.events.drop_last());
        assert(prefix.machine.configs =~= source.machine.configs.drop_last());
        assert(prefix.contexts =~= source.contexts.drop_last());
        compressed_contexts_unfold_last(
            source.contexts, source.machine.events,
        );
        compressed_contexts_len(prefix.contexts, prefix.machine.events);
        if index < source.machine.events.len() {
            assert(index <= length);
            compressed_context_at_prefix(cfg, context, prefix, index);
            assert(prefix.machine.events.take(index as int) =~=
                source.machine.events.take(index as int));
            assert(prefix.contexts[index as int]
                == source.contexts[index as int]);
            let count = t3_event_layer::matched_count(
                source.machine.events.take(index as int),
            );
            assert(count == t3_event_layer::matched_count(
                prefix.machine.events.take(index as int),
            ));
            assert(count < compress_contexts(
                prefix.contexts, prefix.machine.events,
            ).len());
            match t3_event_layer::translate_event(
                source.machine.events.last(),
            ) {
                Option::Some(_) => {
                    assert(compress_contexts(
                        source.contexts, source.machine.events,
                    ) == compress_contexts(
                        prefix.contexts, prefix.machine.events,
                    ).push(source.contexts.last()));
                    assert(compress_contexts(
                        source.contexts, source.machine.events,
                    )[count as int] == compress_contexts(
                        prefix.contexts, prefix.machine.events,
                    )[count as int]);
                },
                Option::None => {
                    assert(compress_contexts(
                        source.contexts, source.machine.events,
                    ) == compress_contexts(
                        prefix.contexts, prefix.machine.events,
                    ));
                },
            }
            assert(compress_contexts(
                source.contexts, source.machine.events,
            )[count as int] == source.contexts[index as int]);
        } else {
            assert(index == source.machine.events.len());
            assert(index == length + 1);
            assert(source.machine.events.take(index as int) =~=
                source.machine.events);
            assert(source.machine.events.drop_last().push(
                source.machine.events.last(),
            ) =~= source.machine.events);
            t3_event_layer::matched_count_push(
                source.machine.events.drop_last(),
                source.machine.events.last(),
            );
            let prefix_count = t3_event_layer::matched_count(
                prefix.machine.events,
            );
            match t3_event_layer::translate_event(
                source.machine.events.last(),
            ) {
                Option::Some(_) => {
                    assert(t3_event_layer::matched_count(
                        source.machine.events,
                    ) == prefix_count + 1);
                    assert(compress_contexts(
                        source.contexts, source.machine.events,
                    ) == compress_contexts(
                        prefix.contexts, prefix.machine.events,
                    ).push(source.contexts.last()));
                    assert(compress_contexts(
                        prefix.contexts, prefix.machine.events,
                    ).len() == prefix_count + 1);
                    assert(source.contexts[index as int]
                        == source.contexts.last());
                    assert(compress_contexts(
                        source.contexts, source.machine.events,
                    )[t3_event_layer::matched_count(
                        source.machine.events.take(index as int),
                    ) as int] == source.contexts[index as int]);
                },
                Option::None => {
                    compressed_context_at_prefix(
                        cfg, context, prefix, length,
                    );
                    assert(prefix.machine.events.take(length as int) =~=
                        prefix.machine.events);
                    assert(prefix.contexts[length as int]
                        == source.contexts[length as int]);
                    assert(compress_contexts(
                        prefix.contexts, prefix.machine.events,
                    )[prefix_count as int]
                        == prefix.contexts[length as int]);
                    let event = source.machine.events[length as int];
                    assert(event == source.machine.events.last());
                    assert(wal_runtime_layer::wal_runtime_step(
                        cfg,
                        source.machine.configs[length as int],
                        event,
                        source.machine.configs[(length + 1) as int],
                    ));
                    assert(t4_c1_layer::context_accepts_step(
                        context,
                        source.contexts[length as int],
                        t4_c1_layer::wal_context_view_at(
                            cfg, source.machine, length,
                        ),
                        event,
                        t4_c1_layer::wal_context_view_at(
                            cfg, source.machine, length + 1,
                        ),
                        source.contexts[(length + 1) as int],
                    ));
                    erased_wal_step_stutters_context(
                        cfg,
                        context,
                        source.machine.configs[length as int],
                        event,
                        source.machine.configs[(length + 1) as int],
                        source.contexts[length as int],
                        t4_c1_layer::wal_context_view_at(
                            cfg, source.machine, length,
                        ),
                        t4_c1_layer::wal_context_view_at(
                            cfg, source.machine, length + 1,
                        ),
                        source.contexts[(length + 1) as int],
                    );
                    assert(source.contexts[index as int]
                        == source.contexts[length as int]);
                    assert(t3_event_layer::matched_count(
                        source.machine.events,
                    ) == prefix_count);
                    assert(t3_event_layer::matched_count(
                        source.machine.events.take(index as int),
                    ) == prefix_count);
                    assert(compress_contexts(
                        source.contexts, source.machine.events,
                    ) == compress_contexts(
                        prefix.contexts, prefix.machine.events,
                    ));
                    assert(compress_contexts(
                        source.contexts, source.machine.events,
                    )[t3_event_layer::matched_count(
                        source.machine.events.take(index as int),
                    ) as int] == source.contexts[index as int]);
                },
            }
        }
    }
}

pub proof fn t3_compressed_context_view_at_prefix(
    cfg: config_layer::FullConfig,
    source: wal_runtime_layer::WalExecution,
    index: nat,
)
    requires
        wal_runtime_layer::exec(cfg, source),
        index <= source.events.len(),
    ensures t4_c1_layer::wal_context_view_at(cfg, source, index)
        == t4_c1_layer::journal_context_view_at(
            cfg,
            t3_layer::compressed_execution(source),
            t3_event_layer::matched_count(
                source.events.take(index as int),
            ),
        ),
{
    let target = t3_layer::compressed_execution(source);
    let count = t3_event_layer::matched_count(
        source.events.take(index as int),
    );
    let prefix = wal_runtime_layer::execution_prefix(source, index);

    wal_runtime_layer::exec_prefix(cfg, source, index);
    wal_runtime_layer::exec_trace_closed(cfg, prefix);
    assert(prefix.events =~= source.events.take(index as int));
    t4_c1_layer::t3_translation_preserves_context_history(prefix.events);
    t3_event_layer::translate_trace_take(source.events, index);
    assert(target.events == t3_event_layer::translate_trace(source.events));
    assert(target.events.take(count as int)
        == t3_event_layer::translate_trace(prefix.events));
    assert(t4_c1_layer::context_history(
        target.events.take(count as int),
    ) == t4_c1_layer::context_history(
        source.events.take(index as int),
    ));

    t3_layer::compressed_configuration_at_prefix(cfg, source, index);
    t3_representation_layer::projection_satisfies_representation(
        source.configs[index as int],
    );
    assert(target.configs[count as int]
        == wal_runtime_layer::journal_projection(
            source.configs[index as int],
        ));
    t4_c1_layer::t3_representation_preserves_runtime_view(
        source.configs[index as int],
        target.configs[count as int],
    );
}

pub proof fn compressed_journal_context_steps_accepted<S>(
    cfg: config_layer::FullConfig,
    context: t4_c1_layer::ProgramContext<S>,
    source: t4_c1_layer::PluggedWalExecution<S>,
)
    requires t4_c1_layer::plugged_wal_exec(cfg, context, source),
    ensures
        canonical_plugged_journal_execution(source).contexts.len()
            == canonical_plugged_journal_execution(source)
                .machine.events.len() + 1,
        forall|index: nat|
        index < canonical_plugged_journal_execution(source).machine.events.len()
        ==> #[trigger] t4_c1_layer::context_accepts_step(
            context,
            canonical_plugged_journal_execution(source)
                .contexts[index as int],
            t4_c1_layer::journal_context_view_at(
                cfg,
                canonical_plugged_journal_execution(source).machine,
                index,
            ),
            canonical_plugged_journal_execution(source)
                .machine.events[index as int],
            t4_c1_layer::journal_context_view_at(
                cfg,
                canonical_plugged_journal_execution(source).machine,
                index + 1,
            ),
            canonical_plugged_journal_execution(source)
                .contexts[(index + 1) as int],
        ),
    decreases source.machine.events.len(),
{
    let target = canonical_plugged_journal_execution(source);
    t4_c1_layer::plugged_wal_embeds(cfg, context, source);
    t3_layer::compressed_execution_is_journal_execution(cfg, source.machine);
    compressed_contexts_len(source.contexts, source.machine.events);
    t3_event_layer::translate_trace_len(source.machine.events);
    assert(target.contexts.len() == target.machine.events.len() + 1);
    if source.machine.events.len() > 0 {
        let length: nat = (source.machine.events.len() - 1) as nat;
        let prefix = t4_c1_layer::plugged_wal_prefix(source, length);
        let prefix_target = canonical_plugged_journal_execution(prefix);
        t4_c1_layer::plugged_wal_prefix_closed(
            cfg, context, source, length,
        );
        compressed_journal_context_steps_accepted(cfg, context, prefix);
        assert(prefix_target.contexts.len()
            == prefix_target.machine.events.len() + 1);
        assert(prefix.machine.events =~= source.machine.events.drop_last());
        assert(prefix.machine.configs =~= source.machine.configs.drop_last());
        assert(prefix.contexts =~= source.contexts.drop_last());
        t3_layer::compression_unfold_last(source.machine);
        compressed_contexts_unfold_last(
            source.contexts, source.machine.events,
        );
        match t3_event_layer::translate_event(
            source.machine.events.last(),
        ) {
            Option::None => {
                assert(target.machine == prefix_target.machine);
                assert(target.contexts == prefix_target.contexts);
            },
            Option::Some(target_event) => {
                assert(target.machine.events
                    == prefix_target.machine.events.push(target_event));
                assert(target.machine.configs
                    == prefix_target.machine.configs.push(
                        wal_runtime_layer::journal_projection(
                            source.machine.configs.last(),
                        ),
                    ));
                assert(target.contexts
                    == prefix_target.contexts.push(source.contexts.last()));
                assert forall|index: nat|
                    index < target.machine.events.len()
                    implies #[trigger] t4_c1_layer::context_accepts_step(
                        context,
                        target.contexts[index as int],
                        t4_c1_layer::journal_context_view_at(
                            cfg, target.machine, index,
                        ),
                        target.machine.events[index as int],
                        t4_c1_layer::journal_context_view_at(
                            cfg, target.machine, index + 1,
                        ),
                        target.contexts[(index + 1) as int],
                    ) by {
                    if index < prefix_target.machine.events.len() {
                        assert(index + 1 < prefix_target.contexts.len());
                        assert(index + 1 < target.contexts.len());
                        assert(target.machine.events[index as int]
                            == prefix_target.machine.events[index as int]);
                        assert(target.machine.configs[index as int]
                            == prefix_target.machine.configs[index as int]);
                        assert(target.machine.configs[(index + 1) as int]
                            == prefix_target.machine.configs[
                                (index + 1) as int
                            ]);
                        assert(target.contexts[index as int]
                            == prefix_target.contexts[index as int]);
                        assert(target.contexts[(index + 1) as int]
                            == prefix_target.contexts[(index + 1) as int]);
                        assert(target.machine.events.take(index as int) =~=
                            prefix_target.machine.events.take(index as int));
                        assert(target.machine.events.take(
                            (index + 1) as int,
                        ) =~= prefix_target.machine.events.take(
                            (index + 1) as int,
                        ));
                        assert(t4_c1_layer::journal_context_view_at(
                            cfg, target.machine, index,
                        ) == t4_c1_layer::journal_context_view_at(
                            cfg, prefix_target.machine, index,
                        ));
                        assert(t4_c1_layer::journal_context_view_at(
                            cfg, target.machine, index + 1,
                        ) == t4_c1_layer::journal_context_view_at(
                            cfg, prefix_target.machine, index + 1,
                        ));
                        assert(t4_c1_layer::context_accepts_step(
                            context,
                            prefix_target.contexts[index as int],
                            t4_c1_layer::journal_context_view_at(
                                cfg, prefix_target.machine, index,
                            ),
                            prefix_target.machine.events[index as int],
                            t4_c1_layer::journal_context_view_at(
                                cfg, prefix_target.machine, index + 1,
                            ),
                            prefix_target.contexts[(index + 1) as int],
                        ));
                    } else {
                        assert(index == prefix_target.machine.events.len());
                        t3_event_layer::translate_trace_len(
                            prefix.machine.events,
                        );
                        let prefix_count = t3_event_layer::matched_count(
                            prefix.machine.events,
                        );
                        assert(index == prefix_count);
                        assert(length == prefix.machine.events.len());
                        assert(source.machine.events.take(length as int) =~=
                            prefix.machine.events);
                        compressed_context_at_prefix(
                            cfg, context, source, length,
                        );
                        compressed_context_at_prefix(
                            cfg, context, source, length + 1,
                        );
                        t3_compressed_context_view_at_prefix(
                            cfg, source.machine, length,
                        );
                        t3_compressed_context_view_at_prefix(
                            cfg, source.machine, length + 1,
                        );
                        assert(source.machine.events.take(
                            (length + 1) as int,
                        ) =~= source.machine.events);
                        t3_event_layer::matched_count_push(
                            prefix.machine.events,
                            source.machine.events.last(),
                        );
                        assert(t3_event_layer::matched_count(
                            source.machine.events,
                        ) == prefix_count + 1);
                        assert(target.contexts[index as int]
                            == source.contexts[length as int]);
                        assert(target.contexts[(index + 1) as int]
                            == source.contexts[(length + 1) as int]);
                        assert(target.machine.events[index as int]
                            == target_event);
                        assert(wal_runtime_layer::wal_runtime_step(
                            cfg,
                            source.machine.configs[length as int],
                            source.machine.events[length as int],
                            source.machine.configs[(length + 1) as int],
                        ));
                        assert(t4_c1_layer::context_accepts_step(
                            context,
                            source.contexts[length as int],
                            t4_c1_layer::wal_context_view_at(
                                cfg, source.machine, length,
                            ),
                            source.machine.events[length as int],
                            t4_c1_layer::wal_context_view_at(
                                cfg, source.machine, length + 1,
                            ),
                            source.contexts[(length + 1) as int],
                        ));
                        t3_event_layer::translate_trace_index(
                            source.machine.events,
                            length,
                            target_event,
                        );
                        t4_c1_layer::t3_matched_events_have_equal_context_delta(
                            source.machine.events[length as int],
                            target_event,
                        );
                        t4_c1_layer::context_acceptance_transfers(
                            context,
                            source.contexts[length as int],
                            t4_c1_layer::wal_context_view_at(
                                cfg, source.machine, length,
                            ),
                            t4_c1_layer::journal_context_view_at(
                                cfg, target.machine, index,
                            ),
                            source.machine.events[length as int],
                            target_event,
                            t4_c1_layer::wal_context_view_at(
                                cfg, source.machine, length + 1,
                            ),
                            t4_c1_layer::journal_context_view_at(
                                cfg, target.machine, index + 1,
                            ),
                            source.contexts[(length + 1) as int],
                        );
                    }
                }
            },
        }
    }
}

pub proof fn plugged_wal_to_canonical_journal<S>(
    cfg: config_layer::FullConfig,
    context: t4_c1_layer::ProgramContext<S>,
    source: t4_c1_layer::PluggedWalExecution<S>,
)
    requires t4_c1_layer::plugged_wal_exec(cfg, context, source),
    ensures t4_c1_layer::plugged_journal_exec(
        cfg, context, canonical_plugged_journal_execution(source),
    ),
{
    let target = canonical_plugged_journal_execution(source);
    t4_c1_layer::plugged_wal_embeds(cfg, context, source);
    t3_layer::compressed_execution_is_journal_execution(cfg, source.machine);
    compressed_contexts_len(source.contexts, source.machine.events);
    t3_event_layer::translate_trace_len(source.machine.events);
    assert(target.contexts.len() == target.machine.events.len() + 1);

    compressed_context_at_prefix(cfg, context, source, 0);
    t3_compressed_context_view_at_prefix(cfg, source.machine, 0);
    assert(source.machine.events.take(0) =~= Seq::empty());
    assert(t3_event_layer::matched_count(
        source.machine.events.take(0),
    ) == 0);
    assert(target.contexts[0] == source.contexts[0]);
    assert(t4_c1_layer::wal_context_view_at(cfg, source.machine, 0)
        == t4_c1_layer::journal_context_view_at(cfg, target.machine, 0));
    assert(context.initial.contains(t4_c1_layer::ContextInitial {
        view: t4_c1_layer::wal_context_view_at(cfg, source.machine, 0),
        state: source.contexts[0],
    }));
    assert(context.initial.contains(t4_c1_layer::ContextInitial {
        view: t4_c1_layer::journal_context_view_at(cfg, target.machine, 0),
        state: target.contexts[0],
    }));

    compressed_journal_context_steps_accepted(cfg, context, source);
}

pub proof fn t2_lifted_context_view_at_prefix(
    cfg: config_layer::FullConfig,
    source: journal_runtime_layer::JournalExecution,
    index: nat,
)
    requires
        config_layer::full_config_wf(cfg),
        journal_runtime_layer::exec(cfg, source),
        index <= source.events.len(),
    ensures t4_c1_layer::journal_context_view_at(cfg, source, index)
        == t4_c1_layer::broker_context_view_at(
            cfg, t2_layer::lift_execution(cfg, source), index,
        ),
{
    let target = t2_layer::lift_execution(cfg, source);
    t2_event_layer::translate_trace_take(source.events, index);
    t4_c1_layer::t2_translation_preserves_context_history(
        source.events.take(index as int),
    );
    assert(target.events == t2_event_layer::translate_trace(source.events));
    assert(target.events.take(index as int)
        == t2_event_layer::translate_trace(
            source.events.take(index as int),
        ));
    assert(t4_c1_layer::context_history(
        target.events.take(index as int),
    ) == t4_c1_layer::context_history(
        source.events.take(index as int),
    ));

    t2_layer::every_lifted_configuration_is_represented(cfg, source);
    assert(index < source.configs.len());
    assert(t2_representation_layer::representation(
        cfg,
        source.configs[index as int],
        target.configs[index as int],
    ));
    t4_c1_layer::t2_representation_preserves_runtime_view(
        cfg,
        source.configs[index as int],
        target.configs[index as int],
    );
}

pub proof fn plugged_journal_to_lifted_broker<S>(
    cfg: config_layer::FullConfig,
    context: t4_c1_layer::ProgramContext<S>,
    source: t4_c1_layer::PluggedJournalExecution<S>,
)
    requires
        config_layer::full_config_wf(cfg),
        t4_c1_layer::plugged_journal_exec(cfg, context, source),
    ensures t4_c1_layer::plugged_broker_exec(
        cfg, context, lifted_plugged_broker_execution(cfg, source),
    ),
{
    let target = lifted_plugged_broker_execution(cfg, source);
    t4_c1_layer::plugged_journal_embeds(cfg, context, source);
    t2_layer::lifted_execution_is_broker_execution(cfg, source.machine);
    t2_event_layer::translate_trace_len(source.machine.events);
    assert(target.contexts.len() == target.machine.events.len() + 1);

    t2_lifted_context_view_at_prefix(cfg, source.machine, 0);
    assert(target.contexts[0] == source.contexts[0]);
    assert(t4_c1_layer::journal_context_view_at(cfg, source.machine, 0)
        == t4_c1_layer::broker_context_view_at(cfg, target.machine, 0));
    assert(context.initial.contains(t4_c1_layer::ContextInitial {
        view: t4_c1_layer::journal_context_view_at(cfg, source.machine, 0),
        state: source.contexts[0],
    }));
    assert(context.initial.contains(t4_c1_layer::ContextInitial {
        view: t4_c1_layer::broker_context_view_at(cfg, target.machine, 0),
        state: target.contexts[0],
    }));

    assert forall|index: nat| index < target.machine.events.len() implies {
        &&& #[trigger] execution_layer::broker_step(
            cfg,
            target.machine.configs[index as int],
            target.machine.events[index as int],
            target.machine.configs[(index + 1) as int],
        )
        &&& t4_c1_layer::context_accepts_step(
            context,
            target.contexts[index as int],
            t4_c1_layer::broker_context_view_at(
                cfg, target.machine, index,
            ),
            target.machine.events[index as int],
            t4_c1_layer::broker_context_view_at(
                cfg, target.machine, index + 1,
            ),
            target.contexts[(index + 1) as int],
        )
    } by {
        assert(index < source.machine.events.len());
        assert(index + 1 < source.contexts.len());
        assert(index + 1 < target.contexts.len());
        assert(execution_layer::broker_step(
            cfg,
            target.machine.configs[index as int],
            target.machine.events[index as int],
            target.machine.configs[(index + 1) as int],
        ));
        assert(journal_runtime_layer::journal_runtime_step(
            cfg,
            source.machine.configs[index as int],
            source.machine.events[index as int],
            source.machine.configs[(index + 1) as int],
        ));
        assert(t4_c1_layer::context_accepts_step(
            context,
            source.contexts[index as int],
            t4_c1_layer::journal_context_view_at(
                cfg, source.machine, index,
            ),
            source.machine.events[index as int],
            t4_c1_layer::journal_context_view_at(
                cfg, source.machine, index + 1,
            ),
            source.contexts[(index + 1) as int],
        ));
        t2_event_layer::translate_trace_index(source.machine.events, index);
        assert(target.machine.events[index as int]
            == t2_event_layer::journal_to_broker_event(
                source.machine.events[index as int],
            ));
        t2_lifted_context_view_at_prefix(cfg, source.machine, index);
        t2_lifted_context_view_at_prefix(cfg, source.machine, index + 1);
        t4_c1_layer::t2_renaming_preserves_context_delta(
            source.machine.events[index as int],
        );
        t4_c1_layer::context_acceptance_transfers(
            context,
            source.contexts[index as int],
            t4_c1_layer::journal_context_view_at(
                cfg, source.machine, index,
            ),
            t4_c1_layer::broker_context_view_at(
                cfg, target.machine, index,
            ),
            source.machine.events[index as int],
            target.machine.events[index as int],
            t4_c1_layer::journal_context_view_at(
                cfg, source.machine, index + 1,
            ),
            t4_c1_layer::broker_context_view_at(
                cfg, target.machine, index + 1,
            ),
            source.contexts[(index + 1) as int],
        );
    }
}

pub proof fn canonical_mapped_context_states_equal<S>(
    cfg: config_layer::FullConfig,
    context: t4_c1_layer::ProgramContext<S>,
    source: t4_c1_layer::PluggedWalExecution<S>,
)
    requires t4_c1_layer::plugged_wal_exec(cfg, context, source),
    ensures mapped_context_states_equal(
        source,
        canonical_plugged_broker_execution(cfg, source),
        t4_c0_layer::canonical_composed_map(source.machine),
    ),
{
    let target = canonical_plugged_broker_execution(cfg, source);
    let map = t4_c0_layer::canonical_composed_map(source.machine);
    t4_c0_layer::canonical_composed_map_is_compression(source.machine);
    compressed_contexts_len(source.contexts, source.machine.events);
    assert forall|index: nat| index <= source.machine.events.len() implies {
        &&& index < source.contexts.len()
        &&& index < map.points.len()
        &&& #[trigger] map.points[index as int] < target.contexts.len()
        &&& source.contexts[index as int]
            == target.contexts[map.points[index as int] as int]
    } by {
        assert(index < source.contexts.len());
        t3_layer::compression_map_point(source.machine.events, index);
        let count = t3_event_layer::matched_count(
            source.machine.events.take(index as int),
        );
        assert(map.points[index as int] == count);
        compressed_context_at_prefix(cfg, context, source, index);
        assert(target.contexts
            == compress_contexts(source.contexts, source.machine.events));
    }
}

pub proof fn canonical_mapped_context_views_equal<S>(
    cfg: config_layer::FullConfig,
    context: t4_c1_layer::ProgramContext<S>,
    source: t4_c1_layer::PluggedWalExecution<S>,
)
    requires
        config_layer::full_config_wf(cfg),
        t4_c1_layer::plugged_wal_exec(cfg, context, source),
    ensures mapped_context_views_equal(
        cfg,
        source,
        canonical_plugged_broker_execution(cfg, source),
        t4_c0_layer::canonical_composed_map(source.machine),
    ),
{
    let middle = t4_c0_layer::canonical_middle_execution(source.machine);
    let target = canonical_plugged_broker_execution(cfg, source);
    let map = t4_c0_layer::canonical_composed_map(source.machine);
    t4_c1_layer::plugged_wal_embeds(cfg, context, source);
    t3_layer::compressed_execution_is_journal_execution(cfg, source.machine);
    t4_c0_layer::canonical_composed_map_is_compression(source.machine);
    t3_event_layer::translate_trace_len(source.machine.events);
    t2_event_layer::translate_trace_len(middle.events);
    assert forall|index: nat| index <= source.machine.events.len() implies {
        &&& index < map.points.len()
        &&& index < source.machine.configs.len()
        &&& map.points[index as int] <= target.machine.events.len()
        &&& map.points[index as int] < target.machine.configs.len()
        &&& #[trigger] t4_c1_layer::wal_context_view_at(
            cfg, source.machine, index,
        ) == t4_c1_layer::broker_context_view_at(
            cfg, target.machine, map.points[index as int],
        )
    } by {
        t3_layer::compression_map_point(source.machine.events, index);
        let count = t3_event_layer::matched_count(
            source.machine.events.take(index as int),
        );
        assert(map.points[index as int] == count);
        assert(index < source.machine.configs.len());
        t3_event_layer::matched_count_take_le(
            source.machine.events, index,
        );
        assert(count <= middle.events.len());
        assert(count < middle.configs.len());
        assert(target.machine.configs.len() == middle.configs.len());
        assert(map.points[index as int] < target.machine.configs.len());
        t3_compressed_context_view_at_prefix(
            cfg, source.machine, index,
        );
        t2_lifted_context_view_at_prefix(cfg, middle, count);
        assert(target.machine == t2_layer::lift_execution(cfg, middle));
    }
}

pub proof fn canonical_contextual_wal_broker_composition<S>(
    cfg: config_layer::FullConfig,
    context: t4_c1_layer::ProgramContext<S>,
    source: t4_c1_layer::PluggedWalExecution<S>,
)
    requires
        config_layer::full_config_wf(cfg),
        t4_c1_layer::plugged_wal_exec(cfg, context, source),
    ensures
        t4_c1_layer::plugged_broker_exec(
            cfg,
            context,
            canonical_plugged_broker_execution(cfg, source),
        ),
        t4_c0_layer::weak_simulation_index_map(
            cfg,
            source.machine,
            canonical_plugged_broker_execution(cfg, source).machine,
            t4_c0_layer::canonical_composed_map(source.machine),
        ),
        mapped_context_states_equal(
            source,
            canonical_plugged_broker_execution(cfg, source),
            t4_c0_layer::canonical_composed_map(source.machine),
        ),
        mapped_context_views_equal(
            cfg,
            source,
            canonical_plugged_broker_execution(cfg, source),
            t4_c0_layer::canonical_composed_map(source.machine),
        ),
        t4_c0_layer::t4_projection_agreement(
            source.machine.events,
            canonical_plugged_broker_execution(cfg, source).machine.events,
        ),
        t1_layer::t1_parameterized_safety_statement(
            cfg,
            canonical_plugged_broker_execution(cfg, source).machine,
        ),
        t4_c0_layer::mapped_prefixes_t1_safe(
            cfg,
            source.machine,
            canonical_plugged_broker_execution(cfg, source).machine,
            t4_c0_layer::canonical_composed_map(source.machine),
        ),
        t4_c0_layer::t4_c0_statement(cfg, source.machine),
        t4_c2_statement(cfg, context, source),
{
    let middle = canonical_plugged_journal_execution(source);
    let target = canonical_plugged_broker_execution(cfg, source);
    plugged_wal_to_canonical_journal(cfg, context, source);
    plugged_journal_to_lifted_broker(cfg, context, middle);
    assert(target == lifted_plugged_broker_execution(cfg, middle));
    assert(t4_c1_layer::plugged_broker_exec(cfg, context, target));

    t4_c1_layer::plugged_wal_embeds(cfg, context, source);
    t4_c0_layer::canonical_closed_wal_broker_composition(
        cfg, source.machine,
    );
    canonical_mapped_context_states_equal(cfg, context, source);
    canonical_mapped_context_views_equal(cfg, context, source);
}

// Exported T4 theorem: forward contextual replacement for every finite,
// event-synchronized execution admitted by a storage-parametric context.
pub proof fn t4_c2_contextual_replacement<A, S>(
    cfg: t1_layer::PaperConfig<A>,
    context: t4_c1_layer::ProgramContext<S>,
    source: t4_c1_layer::PluggedWalExecution<S>,
)
    requires
        t1_layer::paper_config_wf(cfg),
        t4_c1_layer::storage_parametric_context(
            t1_layer::paper_broker_config(cfg), context,
        ),
        t4_c1_layer::plugged_wal_exec(
            t1_layer::paper_broker_config(cfg), context, source,
        ),
    ensures t4_c2_statement(
        t1_layer::paper_broker_config(cfg), context, source,
    ),
{
    canonical_contextual_wal_broker_composition(
        t1_layer::paper_broker_config(cfg), context, source,
    );
}

} // verus!
