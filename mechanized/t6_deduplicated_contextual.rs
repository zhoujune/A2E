use vstd::prelude::*;

#[path = "t6_deduplicated_mediation.rs"]
pub mod t6_dd3_layer;

verus! {

use t6_dd3_layer::*;
use t6_dd3_layer::t6_dd2_layer;
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

// T6-DD4 composes the DD3 adapter/protected pair with the typed WAL at every
// adapter prefix, then lifts those prefixes through T4-C2's canonical context.

pub open spec fn dd4_adapter_wal_step_match(
    event: DDAdapterEvent,
    wal: wal_runtime_layer::WalExecution,
    left: nat,
    right: nat,
) -> bool {
    match event {
        DDAdapterEvent::Observe { event: global } => {
            &&& left < wal.events.len()
            &&& right == left + 1
            &&& wal.events[left as int] == global
        },
        DDAdapterEvent::ServiceDecide { .. } => right == left,
    }
}

pub open spec fn dd4_adapter_wal_coupled(
    adapter: DDAdapterExecution,
    wal: wal_runtime_layer::WalExecution,
    map: t2_layer::WeakIndexMap,
) -> bool {
    &&& t2_layer::weak_index_shape(
        adapter.events.len(), wal.events.len(), map,
    )
    &&& forall|index: nat| index < adapter.events.len() ==>
        #[trigger] dd4_adapter_wal_step_match(
            adapter.events[index as int],
            wal,
            map.points[index as int],
            map.points[(index + 1) as int],
        )
}

pub open spec fn dd4_projection_index(
    events: Seq<DDAdapterEvent>,
    index: nat,
) -> nat {
    dd_global_trace(events.take(index as int)).len()
}

pub open spec fn dd4_canonical_index_map(
    events: Seq<DDAdapterEvent>,
) -> t2_layer::WeakIndexMap {
    t2_layer::WeakIndexMap {
        points: Seq::new((events.len() + 1) as nat, |index: int|
            dd4_projection_index(events, index as nat),
        ),
    }
}

proof fn dd4_global_trace_push(
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
    assert(events.push(event).last() == event);
}

proof fn dd4_seq_prefix_reflexive<A>(sequence: Seq<A>)
    ensures append_layer::is_prefix(sequence, sequence),
{
    assert(sequence.take(sequence.len() as int) =~= sequence);
}

proof fn dd4_seq_prefix_survives_push<A>(
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

proof fn dd4_global_trace_prefix(
    events: Seq<DDAdapterEvent>,
    length: nat,
)
    requires length <= events.len(),
    ensures append_layer::is_prefix(
        dd_global_trace(events.take(length as int)),
        dd_global_trace(events),
    ),
    decreases events.len(),
{
    if length == events.len() {
        assert(events.take(length as int) =~= events);
        dd4_seq_prefix_reflexive(dd_global_trace(events));
    } else {
        let prefix = events.drop_last();
        let event = events.last();
        assert(length <= prefix.len());
        assert(events.take(length as int) =~= prefix.take(length as int));
        dd4_global_trace_prefix(prefix, length);
        dd4_global_trace_push(prefix, event);
        assert(events =~= prefix.push(event));
        match event {
            DDAdapterEvent::Observe { event: global } => {
                dd4_seq_prefix_survives_push(
                    dd_global_trace(prefix.take(length as int)),
                    dd_global_trace(prefix),
                    global,
                );
            },
            DDAdapterEvent::ServiceDecide { .. } => {},
        }
    }
}

pub proof fn dd4_projection_prefix_exact(
    events: Seq<DDAdapterEvent>,
    length: nat,
)
    requires length <= events.len(),
    ensures
        append_layer::is_prefix(
            dd_global_trace(events.take(length as int)),
            dd_global_trace(events),
        ),
        dd_global_trace(events.take(length as int)).len()
            <= dd_global_trace(events).len(),
        dd_global_trace(events.take(length as int))
            == dd_global_trace(events).take(
                dd4_projection_index(events, length) as int,
            ),
{
    dd4_global_trace_prefix(events, length);
}

pub proof fn dd4_canonical_index_map_has_shape(
    events: Seq<DDAdapterEvent>,
)
    ensures t2_layer::weak_index_shape(
        events.len(),
        dd_global_trace(events).len(),
        dd4_canonical_index_map(events),
    ),
{
    let map = dd4_canonical_index_map(events);
    assert(map.points.len() == events.len() + 1);
    assert(events.take(0) =~= Seq::empty());
    assert(map.points[0] == 0);
    assert(events.take(events.len() as int) =~= events);
    assert(map.points[events.len() as int]
        == dd_global_trace(events).len());
    assert forall|index: nat| index < events.len() implies {
        let left = #[trigger] map.points[index as int];
        let right = map.points[(index + 1) as int];
        &&& left <= right
        &&& right <= dd_global_trace(events).len()
        &&& (right == left || right == left + 1)
    } by {
        let event = events[index as int];
        let left = map.points[index as int];
        let right = map.points[(index + 1) as int];
        assert(events.take((index + 1) as int) =~=
            events.take(index as int).push(event));
        dd4_global_trace_push(events.take(index as int), event);
        dd4_projection_prefix_exact(events, index + 1);
        match event {
            DDAdapterEvent::Observe { .. } => {
                assert(right == left + 1);
            },
            DDAdapterEvent::ServiceDecide { .. } => {
                assert(right == left);
            },
        }
    }
}

proof fn dd4_canonical_step_match_at(
    adapter: DDAdapterExecution,
    wal: wal_runtime_layer::WalExecution,
    index: nat,
)
    requires
        dd_global_trace(adapter.events) == wal.events,
        index < adapter.events.len(),
    ensures dd4_adapter_wal_step_match(
        adapter.events[index as int],
        wal,
        dd4_canonical_index_map(adapter.events).points[index as int],
        dd4_canonical_index_map(adapter.events).points[(index + 1) as int],
    ),
{
    let map = dd4_canonical_index_map(adapter.events);
    let event = adapter.events[index as int];
    let left = map.points[index as int];
    let right = map.points[(index + 1) as int];
    assert(adapter.events.take((index + 1) as int) =~=
        adapter.events.take(index as int).push(event));
    dd4_global_trace_push(adapter.events.take(index as int), event);
    dd4_projection_prefix_exact(adapter.events, index);
    dd4_projection_prefix_exact(adapter.events, index + 1);
    match event {
        DDAdapterEvent::Observe { event: global } => {
            assert(right == left + 1);
            assert(dd_global_trace(adapter.events).take(right as int)
                =~= dd_global_trace(adapter.events).take(left as int)
                    .push(global));
            assert(left < dd_global_trace(adapter.events).len());
            assert(dd_global_trace(adapter.events).take(right as int)[
                left as int
            ] == global);
            assert(dd_global_trace(adapter.events)[left as int] == global);
        },
        DDAdapterEvent::ServiceDecide { .. } => {
            assert(right == left);
        },
    }
}

pub proof fn dd4_canonical_map_couples_trace_equal_execution(
    adapter: DDAdapterExecution,
    wal: wal_runtime_layer::WalExecution,
)
    requires dd_global_trace(adapter.events) == wal.events,
    ensures dd4_adapter_wal_coupled(
        adapter, wal, dd4_canonical_index_map(adapter.events),
    ),
{
    let map = dd4_canonical_index_map(adapter.events);
    dd4_canonical_index_map_has_shape(adapter.events);
    assert forall|index: nat| index < adapter.events.len() implies
        #[trigger] dd4_adapter_wal_step_match(
            adapter.events[index as int],
            wal,
            map.points[index as int],
            map.points[(index + 1) as int],
        ) by {
        dd4_canonical_step_match_at(adapter, wal, index);
    }
}

proof fn dd4_prefix_trace_agreement_at(
    adapter: DDAdapterExecution,
    wal: wal_runtime_layer::WalExecution,
    map: t2_layer::WeakIndexMap,
    length: nat,
)
    requires
        dd4_adapter_wal_coupled(adapter, wal, map),
        length <= adapter.events.len(),
    ensures dd_global_trace(adapter.events.take(length as int))
        == wal.events.take(map.points[length as int] as int),
    decreases length,
{
    if length == 0 {
        assert(map.points[0] == 0);
        assert(adapter.events.take(0) =~= Seq::empty());
        assert(wal.events.take(0) =~= Seq::empty());
    } else {
        let prior: nat = (length - 1) as nat;
        let event = adapter.events[prior as int];
        let left = map.points[prior as int];
        let right = map.points[length as int];
        dd4_prefix_trace_agreement_at(adapter, wal, map, prior);
        assert(length == prior + 1);
        assert(adapter.events.take(length as int) =~=
            adapter.events.take(prior as int).push(event));
        dd4_global_trace_push(
            adapter.events.take(prior as int), event,
        );
        assert(dd4_adapter_wal_step_match(event, wal, left, right));
        match event {
            DDAdapterEvent::Observe { event: global } => {
                assert(right == left + 1);
                assert(wal.events[left as int] == global);
                assert(wal.events.take(right as int) =~=
                    wal.events.take(left as int).push(global));
            },
            DDAdapterEvent::ServiceDecide { .. } => {
                assert(right == left);
            },
        }
    }
}

pub proof fn dd4_adapter_wal_prefix_trace_agreement(
    adapter: DDAdapterExecution,
    wal: wal_runtime_layer::WalExecution,
    map: t2_layer::WeakIndexMap,
)
    requires dd4_adapter_wal_coupled(adapter, wal, map),
    ensures
        forall|index: nat| index <= adapter.events.len() ==>
            #[trigger] dd_global_trace(
                adapter.events.take(index as int),
            ) == wal.events.take(map.points[index as int] as int),
        dd_global_trace(adapter.events) == wal.events,
{
    assert forall|index: nat| index <= adapter.events.len() implies
        #[trigger] dd_global_trace(
            adapter.events.take(index as int),
        ) == wal.events.take(map.points[index as int] as int) by {
        dd4_prefix_trace_agreement_at(adapter, wal, map, index);
    }
    dd4_prefix_trace_agreement_at(
        adapter, wal, map, adapter.events.len(),
    );
    assert(map.points[adapter.events.len() as int] == wal.events.len());
    assert(adapter.events.take(adapter.events.len() as int)
        =~= adapter.events);
    assert(wal.events.take(wal.events.len() as int) =~= wal.events);
}

pub open spec fn dd4_effect_state_agreement(
    adapter: DDAdapterState,
    protected: DD3ProtectedState,
) -> bool {
    &&& adapter.request == protected.request
    &&& adapter.initial_slot == protected.initial_slot
    &&& adapter.slot == protected.slot
    &&& adapter.decisions.len() == protected.decisions.len()
    &&& forall|index: nat| index < adapter.decisions.len() ==>
        #[trigger] adapter.decisions[index as int].decision
            == protected.decisions[index as int].decision
}

proof fn dd4_initial_effect_state_agreement(
    request: replay_layer::RequestId,
    stable_key: replay_layer::StableKey,
    initial_slot: Option<replay_layer::Value>,
)
    ensures dd4_effect_state_agreement(
        dd_initial_state(request, initial_slot),
        dd3_initial_protected_state(request, stable_key, initial_slot),
    ),
{
}

proof fn dd4_observe_preserves_effect_fields(
    state: DDAdapterState,
    event: global_layer::GlobalEvent,
)
    ensures
        dd_apply_observe(state, event).request == state.request,
        dd_apply_observe(state, event).initial_slot == state.initial_slot,
        dd_apply_observe(state, event).slot == state.slot,
        dd_apply_observe(state, event).decisions == state.decisions,
{
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

proof fn dd4_coupled_step_preserves_effect_state_agreement(
    adapter_before: DDAdapterState,
    adapter_event: DDAdapterEvent,
    adapter_after: DDAdapterState,
    protected_before: DD3ProtectedState,
    protected_event: DD3ProtectedEvent,
    protected_after: DD3ProtectedState,
)
    requires
        dd4_effect_state_agreement(adapter_before, protected_before),
        dd_step(adapter_before, adapter_event, adapter_after),
        dd3_protected_step(
            protected_before, protected_event, protected_after,
        ),
        dd3_event_coupled(
            adapter_before,
            adapter_event,
            protected_before,
            protected_event,
        ),
    ensures dd4_effect_state_agreement(adapter_after, protected_after),
{
    assert(adapter_after == dd_apply(adapter_before, adapter_event));
    assert(protected_after
        == dd3_protected_apply(protected_before, protected_event));
    match adapter_event {
        DDAdapterEvent::Observe { event: global } => {
            dd4_observe_preserves_effect_fields(adapter_before, global);
            match global {
                global_layer::GlobalEvent::InvokeEvent { .. } => {
                    match protected_event {
                        DD3ProtectedEvent::BrokerInvoke { .. } => {},
                        DD3ProtectedEvent::ServiceDecide { .. }
                        | DD3ProtectedEvent::ServiceReturn { .. }
                        | DD3ProtectedEvent::Stutter => assert(false),
                    }
                },
                global_layer::GlobalEvent::DeliverEvent { .. } => {
                    match protected_event {
                        DD3ProtectedEvent::ServiceReturn { .. } => {},
                        DD3ProtectedEvent::BrokerInvoke { .. }
                        | DD3ProtectedEvent::ServiceDecide { .. }
                        | DD3ProtectedEvent::Stutter => assert(false),
                    }
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
                | global_layer::GlobalEvent::FinishRecover => {
                    assert(protected_event == DD3ProtectedEvent::Stutter);
                },
            }
        },
        DDAdapterEvent::ServiceDecide { decision } => {
            let call_ref = choose|call_ref: nat| {
                &&& call_ref < protected_before.calls.len()
                &&& protected_event == DD3ProtectedEvent::ServiceDecide {
                    call_ref,
                    decision,
                }
            };
            assert(call_ref < protected_before.calls.len());
            assert(protected_event == DD3ProtectedEvent::ServiceDecide {
                call_ref,
                decision,
            });
            assert(adapter_after.decisions.len()
                == adapter_before.decisions.len() + 1);
            assert(protected_after.decisions.len()
                == protected_before.decisions.len() + 1);
            assert forall|index: nat| index < adapter_after.decisions.len()
                implies #[trigger] adapter_after.decisions[index as int].decision
                    == protected_after.decisions[index as int].decision by {
                if index < adapter_before.decisions.len() {
                } else {
                    assert(index == adapter_before.decisions.len());
                    assert(index == protected_before.decisions.len());
                }
            }
        },
    }
}

pub proof fn dd4_coupled_exec_prefix(
    request: replay_layer::RequestId,
    stable_key: replay_layer::StableKey,
    initial_slot: Option<replay_layer::Value>,
    adapter: DDAdapterExecution,
    protected: DD3ProtectedExecution,
    length: nat,
)
    requires
        dd3_coupled_exec(
            request, stable_key, initial_slot, adapter, protected,
        ),
        length <= adapter.events.len(),
    ensures dd3_coupled_exec(
        request,
        stable_key,
        initial_slot,
        dd_execution_prefix(adapter, length),
        dd3_protected_execution_prefix(protected, length),
    ),
{
    let adapter_prefix = dd_execution_prefix(adapter, length);
    let protected_prefix = dd3_protected_execution_prefix(
        protected, length,
    );
    dd1_exec_prefix(request, initial_slot, adapter, length);
    dd3_protected_exec_prefix(
        request, stable_key, initial_slot, protected, length,
    );
    assert(adapter_prefix.events.len() == length);
    assert(protected_prefix.events.len() == length);
    assert forall|index: nat| index < length implies
        #[trigger] dd3_event_coupled(
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

proof fn dd4_coupled_final_effect_state_agreement(
    request: replay_layer::RequestId,
    stable_key: replay_layer::StableKey,
    initial_slot: Option<replay_layer::Value>,
    adapter: DDAdapterExecution,
    protected: DD3ProtectedExecution,
)
    requires dd3_coupled_exec(
        request, stable_key, initial_slot, adapter, protected,
    ),
    ensures dd4_effect_state_agreement(
        adapter.configs[adapter.events.len() as int],
        protected.configs[protected.events.len() as int],
    ),
    decreases adapter.events.len(),
{
    if adapter.events.len() == 0 {
        assert(protected.events.len() == 0);
        dd4_initial_effect_state_agreement(request, stable_key, initial_slot);
    } else {
        let last: nat = (adapter.events.len() - 1) as nat;
        let adapter_prefix = dd_execution_prefix(adapter, last);
        let protected_prefix = dd3_protected_execution_prefix(
            protected, last,
        );
        dd4_coupled_exec_prefix(
            request, stable_key, initial_slot, adapter, protected, last,
        );
        dd4_coupled_final_effect_state_agreement(
            request,
            stable_key,
            initial_slot,
            adapter_prefix,
            protected_prefix,
        );
        dd4_coupled_step_preserves_effect_state_agreement(
            adapter.configs[last as int],
            adapter.events[last as int],
            adapter.configs[(last + 1) as int],
            protected.configs[last as int],
            protected.events[last as int],
            protected.configs[(last + 1) as int],
        );
    }
}

pub proof fn dd4_coupled_every_prefix_effect_state_agreement(
    request: replay_layer::RequestId,
    stable_key: replay_layer::StableKey,
    initial_slot: Option<replay_layer::Value>,
    adapter: DDAdapterExecution,
    protected: DD3ProtectedExecution,
)
    requires dd3_coupled_exec(
        request, stable_key, initial_slot, adapter, protected,
    ),
    ensures forall|index: nat| index <= adapter.events.len() ==>
        #[trigger] dd4_effect_state_agreement(
            adapter.configs[index as int],
            protected.configs[index as int],
        ),
{
    assert forall|index: nat| index <= adapter.events.len() implies
        #[trigger] dd4_effect_state_agreement(
            adapter.configs[index as int],
            protected.configs[index as int],
        ) by {
        let adapter_prefix = dd_execution_prefix(adapter, index);
        let protected_prefix = dd3_protected_execution_prefix(
            protected, index,
        );
        dd4_coupled_exec_prefix(
            request, stable_key, initial_slot, adapter, protected, index,
        );
        dd4_coupled_final_effect_state_agreement(
            request,
            stable_key,
            initial_slot,
            adapter_prefix,
            protected_prefix,
        );
        assert(adapter_prefix.configs[index as int]
            == adapter.configs[index as int]);
        assert(protected_prefix.configs[index as int]
            == protected.configs[index as int]);
    }
}

pub open spec fn dd4_prefix_product_at(
    request: replay_layer::RequestId,
    stable_key: replay_layer::StableKey,
    initial_slot: Option<replay_layer::Value>,
    adapter: DDAdapterExecution,
    protected: DD3ProtectedExecution,
    wal: wal_runtime_layer::WalExecution,
    map: t2_layer::WeakIndexMap,
    index: nat,
) -> bool {
    if index < map.points.len()
        && index < adapter.configs.len()
        && index < protected.configs.len()
    {
        let point = map.points[index as int];
        if point < wal.configs.len() && point <= wal.events.len() {
            let adapter_prefix = dd_execution_prefix(adapter, index);
            let protected_prefix = dd3_protected_execution_prefix(
                protected, index,
            );
            let wal_prefix = wal_runtime_layer::execution_prefix(wal, point);
            let accepted = dd3_erase_calls(
                protected.configs[index as int].calls,
            );
            &&& dd_global_trace(adapter.events.take(index as int))
                == wal.events.take(point as int)
            &&& adapter.configs[index as int].globals
                == wal.events.take(point as int)
            &&& adapter.configs[index as int].history
                == projection_layer::pi_adapter(
                    wal.events.take(point as int), request,
                )
            &&& dd3_coupled_exec(
                request,
                stable_key,
                initial_slot,
                adapter_prefix,
                protected_prefix,
            )
            &&& wal_runtime_layer::exec(dd_full_config(), wal_prefix)
            &&& dd4_effect_state_agreement(
                adapter.configs[index as int],
                protected.configs[index as int],
            )
            &&& accepted == projection_layer::pi_invocations(
                wal.events.take(point as int),
            )
            &&& projection_layer::complete_mediation(
                wal.events.take(point as int), accepted,
            )
        } else {
            false
        }
    } else {
        false
    }
}

pub open spec fn dd4_execution_pair(
    request: replay_layer::RequestId,
    stable_key: replay_layer::StableKey,
    initial_slot: Option<replay_layer::Value>,
    adapter: DDAdapterExecution,
    protected: DD3ProtectedExecution,
    wal: wal_runtime_layer::WalExecution,
    map: t2_layer::WeakIndexMap,
) -> bool {
    &&& dd3_coupled_exec(
        request, stable_key, initial_slot, adapter, protected,
    )
    &&& wal_runtime_layer::exec(dd_full_config(), wal)
    &&& dd4_adapter_wal_coupled(adapter, wal, map)
}

pub open spec fn dd4_prefix_product(
    request: replay_layer::RequestId,
    stable_key: replay_layer::StableKey,
    initial_slot: Option<replay_layer::Value>,
    adapter: DDAdapterExecution,
    protected: DD3ProtectedExecution,
    wal: wal_runtime_layer::WalExecution,
    map: t2_layer::WeakIndexMap,
) -> bool {
    &&& dd4_execution_pair(
        request, stable_key, initial_slot, adapter, protected, wal, map,
    )
    &&& forall|index: nat| index <= adapter.events.len() ==>
        #[trigger] dd4_prefix_product_at(
            request,
            stable_key,
            initial_slot,
            adapter,
            protected,
            wal,
            map,
            index,
        )
}

pub proof fn dd4_execution_pair_derives_prefix_product(
    request: replay_layer::RequestId,
    stable_key: replay_layer::StableKey,
    initial_slot: Option<replay_layer::Value>,
    adapter: DDAdapterExecution,
    protected: DD3ProtectedExecution,
    wal: wal_runtime_layer::WalExecution,
    map: t2_layer::WeakIndexMap,
)
    requires dd4_execution_pair(
        request, stable_key, initial_slot, adapter, protected, wal, map,
    ),
    ensures
        dd4_prefix_product(
            request, stable_key, initial_slot, adapter, protected, wal, map,
        ),
        dd_global_trace(adapter.events) == wal.events,
        dd4_effect_state_agreement(
            adapter.configs[adapter.events.len() as int],
            protected.configs[protected.events.len() as int],
        ),
{
    assert(dd3_coupled_exec(
        request, stable_key, initial_slot, adapter, protected,
    ));
    assert(dd4_adapter_wal_coupled(adapter, wal, map));
    dd4_adapter_wal_prefix_trace_agreement(adapter, wal, map);
    dd4_coupled_every_prefix_effect_state_agreement(
        request, stable_key, initial_slot, adapter, protected,
    );
    dd1_every_exec_configuration_satisfies_invariant(
        request, initial_slot, adapter,
    );
    assert forall|index: nat| index <= adapter.events.len() implies
        #[trigger] dd4_prefix_product_at(
            request,
            stable_key,
            initial_slot,
            adapter,
            protected,
            wal,
            map,
            index,
        ) by {
        let point = map.points[index as int];
        let adapter_prefix = dd_execution_prefix(adapter, index);
        let protected_prefix = dd3_protected_execution_prefix(
            protected, index,
        );
        let wal_prefix = wal_runtime_layer::execution_prefix(wal, point);
        t4_c0_layer::weak_index_point_bounded(
            adapter.events.len(), wal.events.len(), map, index,
        );
        dd4_coupled_exec_prefix(
            request, stable_key, initial_slot, adapter, protected, index,
        );
        wal_runtime_layer::exec_prefix(dd_full_config(), wal, point);
        dd1_exec_final_globals_are_projected(
            request, initial_slot, adapter_prefix,
        );
        dd3_coupled_exec_derives_complete_mediation(
            request,
            stable_key,
            initial_slot,
            adapter_prefix,
            protected_prefix,
        );
        assert(adapter_prefix.events
            =~= adapter.events.take(index as int));
        assert(adapter_prefix.configs[index as int]
            == adapter.configs[index as int]);
        assert(protected_prefix.configs[index as int]
            == protected.configs[index as int]);
        assert(wal_prefix.events =~= wal.events.take(point as int));
        assert(dd_global_trace(adapter.events.take(index as int))
            == wal.events.take(point as int));
        assert(dd1_execution_invariant(
            request, initial_slot, adapter.configs[index as int],
        ));
        assert(adapter.configs[index as int].history
            == projection_layer::pi_adapter(
                adapter.configs[index as int].globals, request,
            ));
    }
}

pub proof fn t6_dd4_deduplicated_prefix_product()
    ensures dd4_prefix_product(
        dd_request_zero(),
        dd2_key(),
        Option::None,
        dd2_adapter_execution(),
        dd3_protected_execution(),
        dd2_wal_execution(),
        dd4_canonical_index_map(dd2_adapter_execution().events),
    ),
{
    let adapter = dd2_adapter_execution();
    let protected = dd3_protected_execution();
    let wal = dd2_wal_execution();
    let map = dd4_canonical_index_map(adapter.events);
    dd2_adapter_execution_exec();
    dd2_wal_execution_exec();
    dd3_adapter_and_service_are_coupled();
    dd4_canonical_map_couples_trace_equal_execution(adapter, wal);
    assert(dd4_execution_pair(
        dd_request_zero(),
        dd2_key(),
        Option::None,
        adapter,
        protected,
        wal,
        map,
    ));
    dd4_execution_pair_derives_prefix_product(
        dd_request_zero(),
        dd2_key(),
        Option::None,
        adapter,
        protected,
        wal,
        map,
    );
}

pub open spec fn dd4_adapter_broker_map(
    adapter_wal_map: t2_layer::WeakIndexMap,
    wal: wal_runtime_layer::WalExecution,
) -> t2_layer::WeakIndexMap {
    t4_c0_layer::compose_index_maps(
        adapter_wal_map,
        t4_c0_layer::canonical_composed_map(wal),
    )
}

pub open spec fn dd4_contextual_prefix_at(
    adapter: DDAdapterExecution,
    protected: DD3ProtectedExecution,
    plugged: t4_c1_layer::PluggedWalExecution<M0ProtectedHandleState>,
    adapter_wal_map: t2_layer::WeakIndexMap,
    index: nat,
) -> bool {
    let cfg = dd_full_config();
    let request = dd_request_zero();
    let key = dd2_key();
    let initial = Option::<replay_layer::Value>::None;
    let wal = plugged.machine;
    let context = m0_exclusive_handle_context(cfg);
    let target = t4_layer::canonical_plugged_broker_execution(cfg, plugged);
    let combined = dd4_adapter_broker_map(adapter_wal_map, wal);
    if index <= adapter.events.len()
        && index < adapter.configs.len()
        && index < protected.configs.len()
        && index < adapter_wal_map.points.len()
        && index < combined.points.len()
    {
        let wal_point = adapter_wal_map.points[index as int];
        let broker_point = combined.points[index as int];
        if wal_point <= wal.events.len()
            && wal_point < wal.configs.len()
            && wal_point < plugged.contexts.len()
            && broker_point <= target.machine.events.len()
            && broker_point < target.machine.configs.len()
            && broker_point < target.contexts.len()
        {
            let accepted = dd3_erase_calls(
                protected.configs[index as int].calls,
            );
            &&& dd4_prefix_product_at(
                request,
                key,
                initial,
                adapter,
                protected,
                wal,
                adapter_wal_map,
                index,
            )
            &&& t4_c1_layer::plugged_wal_exec(
                cfg,
                context,
                t4_c1_layer::plugged_wal_prefix(plugged, wal_point),
            )
            &&& t4_c1_layer::plugged_broker_exec(
                cfg,
                context,
                t4_c1_layer::plugged_broker_prefix(
                    target, broker_point,
                ),
            )
            &&& adapter.configs[index as int].history
                == projection_layer::pi_adapter(
                    target.machine.events.take(broker_point as int),
                    request,
                )
            &&& plugged.contexts[wal_point as int].invocations == accepted
            &&& target.contexts[broker_point as int].invocations == accepted
            &&& plugged.contexts[wal_point as int]
                == target.contexts[broker_point as int]
            &&& t4_c1_layer::wal_context_view_at(
                cfg, wal, wal_point,
            ) == t4_c1_layer::broker_context_view_at(
                cfg, target.machine, broker_point,
            )
            &&& projection_layer::complete_mediation(
                target.machine.events.take(broker_point as int), accepted,
            )
            &&& t1_layer::t1_parameterized_safety_statement(
                cfg,
                execution_layer::execution_prefix(
                    target.machine, broker_point,
                ),
            )
        } else {
            false
        }
    } else {
        false
    }
}

pub closed spec fn dd4_contextual_product(
    adapter: DDAdapterExecution,
    protected: DD3ProtectedExecution,
    plugged: t4_c1_layer::PluggedWalExecution<M0ProtectedHandleState>,
    adapter_wal_map: t2_layer::WeakIndexMap,
) -> bool {
    let cfg = dd_full_config();
    let context = m0_exclusive_handle_context(cfg);
    let target = t4_layer::canonical_plugged_broker_execution(cfg, plugged);
    let combined = dd4_adapter_broker_map(
        adapter_wal_map, plugged.machine,
    );
    &&& t4_c1_layer::storage_parametric_context(cfg, context)
    &&& t4_c1_layer::plugged_wal_exec(cfg, context, plugged)
    &&& dd4_prefix_product(
        dd_request_zero(),
        dd2_key(),
        Option::None,
        adapter,
        protected,
        plugged.machine,
        adapter_wal_map,
    )
    &&& t4_layer::t4_c2_statement(cfg, context, plugged)
    &&& t2_layer::weak_index_shape(
        adapter.events.len(), target.machine.events.len(), combined,
    )
    &&& forall|index: nat| index <= adapter.events.len() ==>
        #[trigger] dd4_contextual_prefix_at(
            adapter, protected, plugged, adapter_wal_map, index,
        )
}

proof fn dd4_composed_map_has_weak_shape(
    adapter: DDAdapterExecution,
    plugged: t4_c1_layer::PluggedWalExecution<M0ProtectedHandleState>,
    adapter_wal_map: t2_layer::WeakIndexMap,
)
    requires
        dd4_adapter_wal_coupled(
            adapter, plugged.machine, adapter_wal_map,
        ),
        t4_layer::t4_c2_statement(
            dd_full_config(),
            m0_exclusive_handle_context(dd_full_config()),
            plugged,
        ),
    ensures t2_layer::weak_index_shape(
        adapter.events.len(),
        t4_layer::canonical_plugged_broker_execution(
            dd_full_config(), plugged,
        ).machine.events.len(),
        dd4_adapter_broker_map(adapter_wal_map, plugged.machine),
    ),
{
    let cfg = dd_full_config();
    let wal = plugged.machine;
    let target = t4_layer::canonical_plugged_broker_execution(cfg, plugged);
    let wal_broker_map = t4_c0_layer::canonical_composed_map(wal);
    assert(t2_layer::weak_index_shape(
        adapter.events.len(), wal.events.len(), adapter_wal_map,
    ));
    assert(t4_c0_layer::weak_simulation_index_map(
        cfg, wal, target.machine, wal_broker_map,
    ));
    assert(t2_layer::weak_index_shape(
        wal.events.len(), target.machine.events.len(), wal_broker_map,
    ));
    t4_c0_layer::compose_weak_index_shapes(
        adapter.events.len(),
        wal.events.len(),
        target.machine.events.len(),
        adapter_wal_map,
        wal_broker_map,
    );
}

pub open spec fn dd4_contextual_prefix_structure(
    adapter: DDAdapterExecution,
    protected: DD3ProtectedExecution,
    plugged: t4_c1_layer::PluggedWalExecution<M0ProtectedHandleState>,
    adapter_wal_map: t2_layer::WeakIndexMap,
    index: nat,
) -> bool {
    let cfg = dd_full_config();
    let request = dd_request_zero();
    let wal = plugged.machine;
    let context = m0_exclusive_handle_context(cfg);
    let target = t4_layer::canonical_plugged_broker_execution(cfg, plugged);
    let wal_broker_map = t4_c0_layer::canonical_composed_map(wal);
    let combined = dd4_adapter_broker_map(adapter_wal_map, wal);
    let wal_point = adapter_wal_map.points[index as int];
    let broker_point = combined.points[index as int];
    &&& index < adapter.configs.len()
    &&& index < protected.configs.len()
    &&& index < adapter_wal_map.points.len()
    &&& index < combined.points.len()
    &&& wal_point <= wal.events.len()
    &&& wal_point < wal.configs.len()
    &&& wal_point < plugged.contexts.len()
    &&& broker_point <= target.machine.events.len()
    &&& broker_point < target.machine.configs.len()
    &&& broker_point < target.contexts.len()
    &&& broker_point == wal_broker_map.points[wal_point as int]
    &&& dd4_prefix_product_at(
        request,
        dd2_key(),
        Option::None,
        adapter,
        protected,
        wal,
        adapter_wal_map,
        index,
    )
    &&& t4_c1_layer::plugged_wal_exec(
        cfg,
        context,
        t4_c1_layer::plugged_wal_prefix(plugged, wal_point),
    )
    &&& t4_c1_layer::plugged_broker_exec(
        cfg,
        context,
        t4_c1_layer::plugged_broker_prefix(target, broker_point),
    )
    &&& t4_c0_layer::t4_projection_agreement(
        wal.events.take(wal_point as int),
        target.machine.events.take(broker_point as int),
    )
    &&& adapter.configs[index as int].history
        == projection_layer::pi_adapter(
            target.machine.events.take(broker_point as int), request,
        )
    &&& plugged.contexts[wal_point as int]
        == target.contexts[broker_point as int]
    &&& t4_c1_layer::wal_context_view_at(cfg, wal, wal_point)
        == t4_c1_layer::broker_context_view_at(
            cfg, target.machine, broker_point,
        )
}

proof fn dd4_contextual_prefix_structure_from_products(
    adapter: DDAdapterExecution,
    protected: DD3ProtectedExecution,
    plugged: t4_c1_layer::PluggedWalExecution<M0ProtectedHandleState>,
    adapter_wal_map: t2_layer::WeakIndexMap,
    index: nat,
)
    requires
        t4_c1_layer::plugged_wal_exec(
            dd_full_config(),
            m0_exclusive_handle_context(dd_full_config()),
            plugged,
        ),
        dd4_prefix_product(
            dd_request_zero(),
            dd2_key(),
            Option::None,
            adapter,
            protected,
            plugged.machine,
            adapter_wal_map,
        ),
        t4_layer::t4_c2_statement(
            dd_full_config(),
            m0_exclusive_handle_context(dd_full_config()),
            plugged,
        ),
        t2_layer::weak_index_shape(
            adapter.events.len(),
            t4_layer::canonical_plugged_broker_execution(
                dd_full_config(), plugged,
            ).machine.events.len(),
            dd4_adapter_broker_map(adapter_wal_map, plugged.machine),
        ),
        index <= adapter.events.len(),
    ensures dd4_contextual_prefix_structure(
        adapter, protected, plugged, adapter_wal_map, index,
    ),
{
    let cfg = dd_full_config();
    let request = dd_request_zero();
    let wal = plugged.machine;
    let context = m0_exclusive_handle_context(cfg);
    let target = t4_layer::canonical_plugged_broker_execution(cfg, plugged);
    let wal_broker_map = t4_c0_layer::canonical_composed_map(wal);
    let combined = dd4_adapter_broker_map(adapter_wal_map, wal);
    let wal_point = adapter_wal_map.points[index as int];
    let broker_point = combined.points[index as int];
    assert(dd4_adapter_wal_coupled(adapter, wal, adapter_wal_map));
    assert(t4_c0_layer::weak_simulation_index_map(
        cfg, wal, target.machine, wal_broker_map,
    ));
    t4_c0_layer::weak_index_point_bounded(
        adapter.events.len(), wal.events.len(), adapter_wal_map, index,
    );
    t4_c0_layer::compose_index_map_point(
        adapter_wal_map, wal_broker_map, index,
    );
    assert(broker_point == wal_broker_map.points[wal_point as int]);
    t4_c0_layer::weak_index_point_bounded(
        wal.events.len(),
        target.machine.events.len(),
        wal_broker_map,
        wal_point,
    );
    assert(dd4_prefix_product_at(
        request,
        dd2_key(),
        Option::None,
        adapter,
        protected,
        wal,
        adapter_wal_map,
        index,
    ));
    assert(wal_point < wal.configs.len());
    assert(wal_point < plugged.contexts.len());
    assert(broker_point < target.machine.configs.len());
    assert(broker_point < target.contexts.len());
    t4_c1_layer::plugged_wal_prefix_closed(
        cfg, context, plugged, wal_point,
    );
    assert(t4_c1_layer::plugged_broker_exec(cfg, context, target));
    t4_c1_layer::plugged_broker_prefix_closed(
        cfg, context, target, broker_point,
    );
    assert(t4_c0_layer::related_prefix_projection_at(
        wal, target.machine, wal_broker_map, wal_point,
    ));
    assert(t4_c0_layer::t4_projection_agreement(
        wal.events.take(wal_point as int),
        target.machine.events.take(broker_point as int),
    ));
    assert(adapter.configs[index as int].history
        == projection_layer::pi_adapter(
            wal.events.take(wal_point as int), request,
        ));
    assert(adapter.configs[index as int].history
        == projection_layer::pi_adapter(
            target.machine.events.take(broker_point as int), request,
        ));
    assert(t4_layer::mapped_context_states_equal(
        plugged, target, wal_broker_map,
    ));
    assert(plugged.contexts[wal_point as int]
        == target.contexts[broker_point as int]);
    assert(t4_layer::mapped_context_views_equal(
        cfg, plugged, target, wal_broker_map,
    ));
    assert(t4_c1_layer::wal_context_view_at(
        cfg, wal, wal_point,
    ) == t4_c1_layer::broker_context_view_at(
        cfg, target.machine, broker_point,
    ));
}

pub open spec fn dd4_contextual_prefix_endpoint(
    adapter: DDAdapterExecution,
    protected: DD3ProtectedExecution,
    plugged: t4_c1_layer::PluggedWalExecution<M0ProtectedHandleState>,
    adapter_wal_map: t2_layer::WeakIndexMap,
    index: nat,
) -> bool {
    let cfg = dd_full_config();
    let wal = plugged.machine;
    let target = t4_layer::canonical_plugged_broker_execution(cfg, plugged);
    let combined = dd4_adapter_broker_map(adapter_wal_map, wal);
    let wal_point = adapter_wal_map.points[index as int];
    let broker_point = combined.points[index as int];
    let accepted = dd3_erase_calls(
        protected.configs[index as int].calls,
    );
    &&& plugged.contexts[wal_point as int].invocations == accepted
    &&& target.contexts[broker_point as int].invocations == accepted
    &&& projection_layer::complete_mediation(
        target.machine.events.take(broker_point as int), accepted,
    )
    &&& t1_layer::t1_parameterized_safety_statement(
        cfg,
        execution_layer::execution_prefix(target.machine, broker_point),
    )
}

proof fn dd4_contextual_prefix_endpoint_from_structure(
    adapter: DDAdapterExecution,
    protected: DD3ProtectedExecution,
    plugged: t4_c1_layer::PluggedWalExecution<M0ProtectedHandleState>,
    adapter_wal_map: t2_layer::WeakIndexMap,
    index: nat,
)
    requires
        dd4_contextual_prefix_structure(
            adapter, protected, plugged, adapter_wal_map, index,
        ),
        t4_layer::t4_c2_statement(
            dd_full_config(),
            m0_exclusive_handle_context(dd_full_config()),
            plugged,
        ),
    ensures dd4_contextual_prefix_endpoint(
        adapter, protected, plugged, adapter_wal_map, index,
    ),
{
    let cfg = dd_full_config();
    let wal = plugged.machine;
    let target = t4_layer::canonical_plugged_broker_execution(cfg, plugged);
    let wal_broker_map = t4_c0_layer::canonical_composed_map(wal);
    let combined = dd4_adapter_broker_map(adapter_wal_map, wal);
    let wal_point = adapter_wal_map.points[index as int];
    let broker_point = combined.points[index as int];
    let accepted = dd3_erase_calls(
        protected.configs[index as int].calls,
    );
    let plugged_prefix = t4_c1_layer::plugged_wal_prefix(
        plugged, wal_point,
    );
    m0_exclusive_context_derives_complete_mediation(
        cfg, plugged_prefix,
    );
    assert(plugged_prefix.machine.events
        =~= wal.events.take(wal_point as int));
    assert(plugged_prefix.contexts[wal_point as int]
        == plugged.contexts[wal_point as int]);
    assert(plugged.contexts[wal_point as int].invocations == accepted);
    assert(target.contexts[broker_point as int].invocations == accepted);
    x0_projection_transports_complete_mediation(
        wal.events.take(wal_point as int),
        target.machine.events.take(broker_point as int),
        accepted,
    );
    assert(t4_c0_layer::mapped_prefixes_t1_safe(
        cfg, wal, target.machine, wal_broker_map,
    ));
}

proof fn dd4_contextual_prefix_from_products(
    adapter: DDAdapterExecution,
    protected: DD3ProtectedExecution,
    plugged: t4_c1_layer::PluggedWalExecution<M0ProtectedHandleState>,
    adapter_wal_map: t2_layer::WeakIndexMap,
    index: nat,
)
    requires
        t4_c1_layer::plugged_wal_exec(
            dd_full_config(),
            m0_exclusive_handle_context(dd_full_config()),
            plugged,
        ),
        dd4_prefix_product(
            dd_request_zero(),
            dd2_key(),
            Option::None,
            adapter,
            protected,
            plugged.machine,
            adapter_wal_map,
        ),
        t4_layer::t4_c2_statement(
            dd_full_config(),
            m0_exclusive_handle_context(dd_full_config()),
            plugged,
        ),
        t2_layer::weak_index_shape(
            adapter.events.len(),
            t4_layer::canonical_plugged_broker_execution(
                dd_full_config(), plugged,
            ).machine.events.len(),
            dd4_adapter_broker_map(adapter_wal_map, plugged.machine),
        ),
        index <= adapter.events.len(),
    ensures dd4_contextual_prefix_at(
        adapter, protected, plugged, adapter_wal_map, index,
    ),
{
    dd4_contextual_prefix_structure_from_products(
        adapter, protected, plugged, adapter_wal_map, index,
    );
    dd4_contextual_prefix_endpoint_from_structure(
        adapter, protected, plugged, adapter_wal_map, index,
    );
}

proof fn dd4_every_prefix_is_contextually_related(
    adapter: DDAdapterExecution,
    protected: DD3ProtectedExecution,
    plugged: t4_c1_layer::PluggedWalExecution<M0ProtectedHandleState>,
    adapter_wal_map: t2_layer::WeakIndexMap,
)
    requires
        t4_c1_layer::plugged_wal_exec(
            dd_full_config(),
            m0_exclusive_handle_context(dd_full_config()),
            plugged,
        ),
        dd4_prefix_product(
            dd_request_zero(),
            dd2_key(),
            Option::None,
            adapter,
            protected,
            plugged.machine,
            adapter_wal_map,
        ),
        t4_layer::t4_c2_statement(
            dd_full_config(),
            m0_exclusive_handle_context(dd_full_config()),
            plugged,
        ),
        t2_layer::weak_index_shape(
            adapter.events.len(),
            t4_layer::canonical_plugged_broker_execution(
                dd_full_config(), plugged,
            ).machine.events.len(),
            dd4_adapter_broker_map(adapter_wal_map, plugged.machine),
        ),
    ensures forall|index: nat| index <= adapter.events.len() ==>
        #[trigger] dd4_contextual_prefix_at(
            adapter, protected, plugged, adapter_wal_map, index,
        ),
{
    assert forall|index: nat| index <= adapter.events.len() implies
        #[trigger] dd4_contextual_prefix_at(
            adapter, protected, plugged, adapter_wal_map, index,
        ) by {
        dd4_contextual_prefix_from_products(
            adapter, protected, plugged, adapter_wal_map, index,
        );
    }
}

pub proof fn dd4_prefix_and_context_derive_product(
    adapter: DDAdapterExecution,
    protected: DD3ProtectedExecution,
    plugged: t4_c1_layer::PluggedWalExecution<M0ProtectedHandleState>,
    adapter_wal_map: t2_layer::WeakIndexMap,
)
    requires
        t4_c1_layer::storage_parametric_context(
            dd_full_config(),
            m0_exclusive_handle_context(dd_full_config()),
        ),
        t4_c1_layer::plugged_wal_exec(
            dd_full_config(),
            m0_exclusive_handle_context(dd_full_config()),
            plugged,
        ),
        dd4_prefix_product(
            dd_request_zero(),
            dd2_key(),
            Option::None,
            adapter,
            protected,
            plugged.machine,
            adapter_wal_map,
        ),
        t4_layer::t4_c2_statement(
            dd_full_config(),
            m0_exclusive_handle_context(dd_full_config()),
            plugged,
        ),
    ensures dd4_contextual_product(
        adapter, protected, plugged, adapter_wal_map,
    ),
{
    dd4_composed_map_has_weak_shape(adapter, plugged, adapter_wal_map);
    dd4_every_prefix_is_contextually_related(
        adapter, protected, plugged, adapter_wal_map,
    );
    reveal(dd4_contextual_product);
}

pub proof fn dd4_concrete_context_inputs()
    ensures {
        let cfg = dd_full_config();
        let context = m0_exclusive_handle_context(cfg);
        let plugged = m0_plugged_wal_execution(dd2_wal_execution());
        &&& t1_layer::paper_config_wf(dd_paper())
        &&& t4_c1_layer::storage_parametric_context(cfg, context)
        &&& t4_c1_layer::plugged_wal_exec(cfg, context, plugged)
    },
{
    let cfg = dd_full_config();
    let wal = dd2_wal_execution();
    let plugged = m0_plugged_wal_execution(wal);
    let context = m0_exclusive_handle_context(cfg);
    dd2_wal_closed_representation();
    m0_exclusive_context_is_storage_parametric(cfg);
    m0_wal_exec_has_exclusive_handle_context(cfg, wal);
}

pub proof fn dd4_concrete_context_replacement()
    ensures {
        let cfg = dd_full_config();
        let context = m0_exclusive_handle_context(cfg);
        let plugged = m0_plugged_wal_execution(dd2_wal_execution());
        t4_layer::t4_c2_statement(cfg, context, plugged)
    },
{
    let cfg = dd_full_config();
    let plugged = m0_plugged_wal_execution(dd2_wal_execution());
    let context = m0_exclusive_handle_context(cfg);
    dd4_concrete_context_inputs();
    t1_layer::paper_broker_config_is_broker(dd_paper());
    assert(t1_layer::paper_broker_config(dd_paper()) == cfg);
    t4_layer::t4_c2_contextual_replacement(
        dd_paper(), context, plugged,
    );
}

pub proof fn dd4_concrete_context_foundation()
    ensures {
        let cfg = dd_full_config();
        let context = m0_exclusive_handle_context(cfg);
        let plugged = m0_plugged_wal_execution(dd2_wal_execution());
        &&& t1_layer::paper_config_wf(dd_paper())
        &&& t4_c1_layer::storage_parametric_context(cfg, context)
        &&& t4_c1_layer::plugged_wal_exec(cfg, context, plugged)
        &&& t4_layer::t4_c2_statement(cfg, context, plugged)
    },
{
    dd4_concrete_context_inputs();
    dd4_concrete_context_replacement();
}

pub proof fn t6_dd4_deduplicated_contextual_product()
    ensures dd4_contextual_product(
        dd2_adapter_execution(),
        dd3_protected_execution(),
        m0_plugged_wal_execution(dd2_wal_execution()),
        dd4_canonical_index_map(dd2_adapter_execution().events),
    ),
{
    let adapter = dd2_adapter_execution();
    let protected = dd3_protected_execution();
    let plugged = m0_plugged_wal_execution(dd2_wal_execution());
    let map = dd4_canonical_index_map(adapter.events);
    t6_dd4_deduplicated_prefix_product();
    dd4_concrete_context_inputs();
    dd4_concrete_context_replacement();
    dd4_prefix_and_context_derive_product(
        adapter, protected, plugged, map,
    );
}

pub proof fn dd4_source_terminal_semantics()
    ensures {
        let request = dd_request_zero();
        let wal = dd2_wal_execution();
        let run = dd2_retry_run();
        let outcome = dd2_terminal_outcome();
        &&& terminal(wal.events, request) == Option::Some(outcome)
        &&& refines(
            dd_paper(),
            request,
            projection_layer::pi_adapter(wal.events, request),
            run,
            outcome,
        )
        &&& per_request_effect_refinement(
            dd_paper(), wal.events, request, run,
        )
    },
{
    dd2_wal_terminal_refines();
}

pub proof fn dd4_source_history_agreement()
    ensures {
        let request = dd_request_zero();
        let adapter = dd2_adapter_execution();
        let wal = dd2_wal_execution();
        adapter.configs[adapter.events.len() as int].history
            == projection_layer::pi_adapter(wal.events, request)
    },
{
    let request = dd_request_zero();
    let adapter = dd2_adapter_execution();
    let wal = dd2_wal_execution();
    let map = dd4_canonical_index_map(adapter.events);
    t6_dd4_deduplicated_prefix_product();
    assert(dd4_prefix_product_at(
        request,
        dd2_key(),
        Option::None,
        adapter,
        dd3_protected_execution(),
        wal,
        map,
        adapter.events.len(),
    ));
    assert(map.points[adapter.events.len() as int] == wal.events.len());
    assert(wal.events.take(wal.events.len() as int) =~= wal.events);
}

pub proof fn dd4_source_terminal_refinement()
    ensures {
        let request = dd_request_zero();
        let adapter = dd2_adapter_execution();
        let wal = dd2_wal_execution();
        let run = dd2_retry_run();
        let outcome = dd2_terminal_outcome();
        &&& terminal(wal.events, request) == Option::Some(outcome)
        &&& refines(
            dd_paper(),
            request,
            adapter.configs[adapter.events.len() as int].history,
            run,
            outcome,
        )
        &&& per_request_effect_refinement(
            dd_paper(), wal.events, request, run,
        )
    },
{
    dd4_source_terminal_semantics();
    dd4_source_history_agreement();
}

pub proof fn dd4_wal_broker_projection_agreement()
    ensures {
        let cfg = dd_full_config();
        let wal = dd2_wal_execution();
        let plugged = m0_plugged_wal_execution(wal);
        let target = t4_layer::canonical_plugged_broker_execution(cfg, plugged);
        t4_c0_layer::t4_projection_agreement(
            wal.events, target.machine.events,
        )
    },
{
    let cfg = dd_full_config();
    let wal = dd2_wal_execution();
    let plugged = m0_plugged_wal_execution(wal);
    let target = t4_layer::canonical_plugged_broker_execution(cfg, plugged);
    dd4_concrete_context_replacement();
    assert(t4_layer::t4_c2_statement(
        cfg, m0_exclusive_handle_context(cfg), plugged,
    ));
    assert(t4_c0_layer::t4_projection_agreement(
        wal.events, target.machine.events,
    ));
}

pub proof fn dd4_target_terminal_refinement()
    ensures {
        let cfg = dd_full_config();
        let request = dd_request_zero();
        let wal = dd2_wal_execution();
        let plugged = m0_plugged_wal_execution(wal);
        let target = t4_layer::canonical_plugged_broker_execution(cfg, plugged);
        let run = dd2_retry_run();
        let outcome = dd2_terminal_outcome();
        &&& terminal(target.machine.events, request)
            == Option::Some(outcome)
        &&& refines(
            dd_paper(),
            request,
            projection_layer::pi_adapter(
                target.machine.events, request,
            ),
            run,
            outcome,
        )
        &&& per_request_effect_refinement(
            dd_paper(), target.machine.events, request, run,
        )
    },
{
    let cfg = dd_full_config();
    let request = dd_request_zero();
    let wal = dd2_wal_execution();
    let plugged = m0_plugged_wal_execution(wal);
    let target = t4_layer::canonical_plugged_broker_execution(cfg, plugged);
    let run = dd2_retry_run();
    let outcome = dd2_terminal_outcome();
    dd4_source_terminal_refinement();
    dd4_wal_broker_projection_agreement();
    x0_projection_transports_terminal_refinement(
        dd_paper(),
        wal.events,
        target.machine.events,
        request,
        run,
        outcome,
    );
}

pub proof fn dd4_source_and_target_terminal_refinement()
    ensures {
        let cfg = dd_full_config();
        let request = dd_request_zero();
        let adapter = dd2_adapter_execution();
        let wal = dd2_wal_execution();
        let plugged = m0_plugged_wal_execution(wal);
        let target = t4_layer::canonical_plugged_broker_execution(cfg, plugged);
        let run = dd2_retry_run();
        let outcome = dd2_terminal_outcome();
        &&& terminal(wal.events, request) == Option::Some(outcome)
        &&& refines(
            dd_paper(),
            request,
            adapter.configs[adapter.events.len() as int].history,
            run,
            outcome,
        )
        &&& per_request_effect_refinement(
            dd_paper(), wal.events, request, run,
        )
        &&& terminal(target.machine.events, request)
            == Option::Some(outcome)
        &&& refines(
            dd_paper(),
            request,
            projection_layer::pi_adapter(
                target.machine.events, request,
            ),
            run,
            outcome,
        )
        &&& per_request_effect_refinement(
            dd_paper(), target.machine.events, request, run,
        )
    },
{
    dd4_source_terminal_refinement();
    dd4_target_terminal_refinement();
}

pub closed spec fn dd4_prefix_context_package() -> bool {
    let cfg = dd_full_config();
    let request = dd_request_zero();
    let adapter = dd2_adapter_execution();
    let protected = dd3_protected_execution();
    let wal = dd2_wal_execution();
    let plugged = m0_plugged_wal_execution(wal);
    let map = dd4_canonical_index_map(adapter.events);
    let final_protected = protected.configs[protected.events.len() as int];
    &&& dd4_prefix_product(
        request,
        dd2_key(),
        Option::None,
        adapter,
        protected,
        wal,
        map,
    )
    &&& dd4_contextual_product(adapter, protected, plugged, map)
    &&& adapter.events.len() == 31
    &&& protected.events.len() == 31
    &&& wal.events.len() == 30
    &&& dd4_effect_state_agreement(
        adapter.configs[adapter.events.len() as int],
        final_protected,
    )
}

pub proof fn dd4_closed_prefix_context_package()
    ensures dd4_prefix_context_package(),
{
    let request = dd_request_zero();
    let adapter = dd2_adapter_execution();
    let protected = dd3_protected_execution();
    let wal = dd2_wal_execution();
    let plugged = m0_plugged_wal_execution(wal);
    let map = dd4_canonical_index_map(adapter.events);
    dd2_adapter_execution_exec();
    dd2_wal_execution_exec();
    dd3_protected_execution_exec();
    t6_dd4_deduplicated_prefix_product();
    t6_dd4_deduplicated_contextual_product();
    assert(dd4_execution_pair(
        request,
        dd2_key(),
        Option::None,
        adapter,
        protected,
        wal,
        map,
    ));
    dd4_coupled_every_prefix_effect_state_agreement(
        request, dd2_key(), Option::None, adapter, protected,
    );
    assert(adapter.events.len() == protected.events.len());
    assert(dd4_effect_state_agreement(
        adapter.configs[adapter.events.len() as int],
        protected.configs[protected.events.len() as int],
    ));
    reveal(dd4_prefix_context_package);
}

pub closed spec fn dd4_terminal_refinement_package() -> bool {
    let cfg = dd_full_config();
    let request = dd_request_zero();
    let adapter = dd2_adapter_execution();
    let wal = dd2_wal_execution();
    let plugged = m0_plugged_wal_execution(wal);
    let target = t4_layer::canonical_plugged_broker_execution(cfg, plugged);
    let run = dd2_retry_run();
    let outcome = dd2_terminal_outcome();
    &&& terminal(wal.events, request) == Option::Some(outcome)
    &&& refines(
        dd_paper(),
        request,
        adapter.configs[adapter.events.len() as int].history,
        run,
        outcome,
    )
    &&& terminal(target.machine.events, request) == Option::Some(outcome)
    &&& refines(
        dd_paper(),
        request,
        projection_layer::pi_adapter(target.machine.events, request),
        run,
        outcome,
    )
    &&& per_request_effect_refinement(
        dd_paper(), target.machine.events, request, run,
    )
}

pub proof fn dd4_closed_terminal_refinement_package()
    ensures dd4_terminal_refinement_package(),
{
    dd4_source_and_target_terminal_refinement();
    reveal(dd4_terminal_refinement_package);
}

pub closed spec fn dd4_mediation_endpoint_package() -> bool {
    let cfg = dd_full_config();
    let protected = dd3_protected_execution();
    let wal = dd2_wal_execution();
    let plugged = m0_plugged_wal_execution(wal);
    let target = t4_layer::canonical_plugged_broker_execution(cfg, plugged);
    let final_protected = protected.configs[protected.events.len() as int];
    let accepted = dd3_erase_calls(final_protected.calls);
    &&& plugged.contexts[wal.events.len() as int].invocations == accepted
    &&& target.contexts[target.machine.events.len() as int].invocations
        == accepted
    &&& projection_layer::complete_mediation(wal.events, accepted)
    &&& projection_layer::complete_mediation(
        target.machine.events, accepted,
    )
}

pub proof fn dd4_closed_mediation_endpoint_package()
    ensures dd4_mediation_endpoint_package(),
{
    let cfg = dd_full_config();
    let adapter = dd2_adapter_execution();
    let protected = dd3_protected_execution();
    let wal = dd2_wal_execution();
    let plugged = m0_plugged_wal_execution(wal);
    let target = t4_layer::canonical_plugged_broker_execution(cfg, plugged);
    let final_protected = protected.configs[protected.events.len() as int];
    let accepted = dd3_erase_calls(final_protected.calls);
    dd2_adapter_execution_exec();
    dd3_adapter_and_service_are_coupled();
    dd3_coupled_exec_derives_complete_mediation(
        dd_request_zero(),
        dd2_key(),
        Option::None,
        adapter,
        protected,
    );
    dd4_concrete_context_inputs();
    dd4_concrete_context_replacement();
    m0_exclusive_context_derives_complete_mediation(cfg, plugged);
    assert(dd_global_trace(adapter.events) == wal.events);
    assert(accepted == projection_layer::pi_invocations(wal.events));
    assert(plugged.contexts[wal.events.len() as int].invocations
        == projection_layer::pi_invocations(wal.events));
    assert(t4_layer::mapped_context_states_equal(
        plugged,
        target,
        t4_c0_layer::canonical_composed_map(wal),
    ));
    assert(plugged.contexts[wal.events.len() as int]
        == target.contexts[target.machine.events.len() as int]);
    assert(t4_c0_layer::t4_projection_agreement(
        wal.events, target.machine.events,
    ));
    x0_projection_transports_complete_mediation(
        wal.events, target.machine.events, accepted,
    );
    reveal(dd4_mediation_endpoint_package);
}

pub closed spec fn dd4_retained_packages() -> bool {
    let adapter = dd2_adapter_execution();
    let protected = dd3_protected_execution();
    let wal = dd2_wal_execution();
    let plugged = m0_plugged_wal_execution(wal);
    &&& dd3_mediation_package(adapter, protected, wal, plugged)
    &&& dd2_executable_crash_retry_package()
}

pub proof fn dd4_closed_retained_packages()
    ensures dd4_retained_packages(),
{
    t6_dd3_deduplicated_mediation();
    t6_dd2_executable_crash_retry_nonvacuity();
    reveal(dd4_retained_packages);
}

pub closed spec fn dd4_contextual_end_to_end_package() -> bool {
    &&& dd4_prefix_context_package()
    &&& dd4_terminal_refinement_package()
    &&& dd4_mediation_endpoint_package()
    &&& dd4_retained_packages()
}

pub proof fn t6_dd4_deduplicated_contextual_end_to_end()
    ensures dd4_contextual_end_to_end_package(),
{
    dd4_closed_prefix_context_package();
    dd4_closed_terminal_refinement_package();
    dd4_closed_mediation_endpoint_package();
    dd4_closed_retained_packages();
    reveal(dd4_contextual_end_to_end_package);
}

pub proof fn t6_dd4_contextual_nonvacuity()
    ensures exists|
        adapter: DDAdapterExecution,
        protected: DD3ProtectedExecution,
        plugged: t4_c1_layer::PluggedWalExecution<M0ProtectedHandleState>,
        map: t2_layer::WeakIndexMap,
    | #![auto] {
        &&& adapter == dd2_adapter_execution()
        &&& protected == dd3_protected_execution()
        &&& plugged == m0_plugged_wal_execution(dd2_wal_execution())
        &&& map == dd4_canonical_index_map(adapter.events)
        &&& dd4_contextual_product(adapter, protected, plugged, map)
        &&& dd4_contextual_end_to_end_package()
    },
{
    t6_dd4_deduplicated_contextual_end_to_end();
    t6_dd4_deduplicated_contextual_product();
    assert(exists|
        adapter: DDAdapterExecution,
        protected: DD3ProtectedExecution,
        plugged: t4_c1_layer::PluggedWalExecution<M0ProtectedHandleState>,
        map: t2_layer::WeakIndexMap,
    | #![auto] {
        &&& adapter == dd2_adapter_execution()
        &&& protected == dd3_protected_execution()
        &&& plugged == m0_plugged_wal_execution(dd2_wal_execution())
        &&& map == dd4_canonical_index_map(adapter.events)
        &&& dd4_contextual_product(adapter, protected, plugged, map)
        &&& dd4_contextual_end_to_end_package()
    }) by {
        let adapter = dd2_adapter_execution();
        let protected = dd3_protected_execution();
        let plugged = m0_plugged_wal_execution(dd2_wal_execution());
        let map = dd4_canonical_index_map(adapter.events);
    }
}

} // verus!
