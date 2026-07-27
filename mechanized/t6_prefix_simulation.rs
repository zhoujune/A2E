use vstd::prelude::*;
use vstd::assert_isets_equal;

#[path = "t6_mediation_exclusivity.rs"]
pub mod t6_m0_layer;

verus! {

use t6_m0_layer::*;
use t6_m0_layer::t6_a1_layer;
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

// T6-P0 relates independently valid A1, protected-service, and typed-WAL
// executions by a prefix index.  It is an execution-pair relation, not an
// existence theorem constructing a WAL execution from every A1 execution.
// Observe consumes exactly one matching WAL label; service linearization and
// environment interference are silent at the WAL boundary.

pub open spec fn p0_a1_wal_step_match(
    event: A1AdapterEvent,
    wal: wal_runtime_layer::WalExecution,
    left: nat,
    right: nat,
) -> bool {
    match event {
        A1AdapterEvent::Observe { event: global } => {
            if left < wal.events.len() {
                right == left + 1
                    && wal.events[left as int] == global
            } else {
                false
            }
        },
        A1AdapterEvent::ServiceLinearize { .. }
        | A1AdapterEvent::EnvironmentAdd { .. } => right == left,
    }
}

pub open spec fn p0_a1_wal_step_coupling(
    adapter: A1AdapterExecution,
    wal: wal_runtime_layer::WalExecution,
    map: t2_layer::WeakIndexMap,
) -> bool {
    map.points.len() == adapter.events.len() + 1
        && forall|index: nat| if index < adapter.events.len() {
            #[trigger] p0_a1_wal_step_match(
                adapter.events[index as int],
                wal,
                map.points[index as int],
                map.points[(index + 1) as int],
            )
        } else {
            true
        }
}

pub open spec fn p0_a1_wal_coupled(
    adapter: A1AdapterExecution,
    wal: wal_runtime_layer::WalExecution,
    map: t2_layer::WeakIndexMap,
) -> bool {
    &&& t2_layer::weak_index_shape(
        adapter.events.len(), wal.events.len(), map,
    )
    &&& p0_a1_wal_step_coupling(adapter, wal, map)
}

pub open spec fn p0_a1_wal_related_prefix_at(
    request: replay_layer::RequestId,
    adapter: A1AdapterExecution,
    wal: wal_runtime_layer::WalExecution,
    map: t2_layer::WeakIndexMap,
    index: nat,
) -> bool {
    if index <= adapter.events.len()
        && index < adapter.configs.len()
        && index < map.points.len()
    {
        let point = map.points[index as int];
        &&& point < wal.configs.len()
        &&& point <= wal.events.len()
        &&& a1_global_trace(adapter.events.take(index as int))
            == wal.events.take(point as int)
        &&& adapter.configs[index as int].globals
            == wal.events.take(point as int)
        &&& adapter.configs[index as int].history
            == projection_layer::pi_adapter(
                wal.events.take(point as int), request,
            )
    } else {
        false
    }
}

pub open spec fn p0_a1_wal_prefix_simulation(
    request: replay_layer::RequestId,
    adapter: A1AdapterExecution,
    wal: wal_runtime_layer::WalExecution,
    map: t2_layer::WeakIndexMap,
) -> bool {
    &&& p0_a1_wal_coupled(adapter, wal, map)
    &&& forall|index: nat| index <= adapter.events.len() ==>
        #[trigger] p0_a1_wal_related_prefix_at(
            request, adapter, wal, map, index,
        )
}

// This relation connects the abstract run used by A0/A1 to the separately
// executed protected service.  The reference-bounds conjunct prevents a
// previously out-of-range ghost reference from becoming a new effect witness
// merely because a later call was appended.
pub open spec fn p0_protected_linearized_attempts(
    protected: M0ProtectedState,
) -> ISet<replay_layer::AttemptId> {
    ISet::new(|attempt: replay_layer::AttemptId|
        exists|call_ref: nat| {
            &&& call_ref < protected.calls.len()
            &&& protected.linearized_refs.contains(call_ref)
            &&& protected.calls[call_ref as int].request == protected.request
            &&& protected.calls[call_ref as int].attempt == attempt
        },
    )
}

pub open spec fn p0_effect_state_agreement(
    adapter: A1AdapterState,
    protected: M0ProtectedState,
) -> bool {
    &&& adapter.request == protected.request
    &&& adapter.initial_members == protected.initial_members
    &&& adapter.members == protected.members
    &&& adapter.environment_additions == protected.environment_additions
    &&& forall|call_ref: nat|
        #[trigger] protected.linearized_refs.contains(call_ref) ==> {
            &&& call_ref < protected.calls.len()
            &&& protected.calls[call_ref as int].request == protected.request
        }
    &&& adapter.linearized_attempts
        =~= p0_protected_linearized_attempts(protected)
}

pub open spec fn p0_prefix_product_at(
    request: replay_layer::RequestId,
    initial_members: ISet<config_layer::Resource>,
    adapter: A1AdapterExecution,
    protected: M0ProtectedExecution,
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
            let adapter_prefix = a1_execution_prefix(adapter, index);
            let protected_prefix = m0_protected_execution_prefix(
                protected, index,
            );
            let wal_prefix = wal_runtime_layer::execution_prefix(wal, point);
            let accepted = m0_erase_calls(
                protected.configs[index as int].calls,
            );
            &&& p0_a1_wal_related_prefix_at(
                request, adapter, wal, map, index,
            )
            &&& m0_coupled_exec(
                request, initial_members, adapter_prefix, protected_prefix,
            )
            &&& wal_runtime_layer::exec(
                ensure_member_full_config(), wal_prefix,
            )
            &&& p0_effect_state_agreement(
                adapter.configs[index as int],
                protected.configs[index as int],
            )
            &&& accepted == projection_layer::pi_invocations(
                wal.events.take(point as int),
            )
            &&& projection_layer::complete_mediation(
                wal.events.take(point as int), accepted,
            )
            &&& m0_every_linearization_durably_authorized(
                ensure_member_full_config(), wal_prefix, protected_prefix,
            )
        } else {
            false
        }
    } else {
        false
    }
}

pub open spec fn p0_execution_pair(
    request: replay_layer::RequestId,
    initial_members: ISet<config_layer::Resource>,
    adapter: A1AdapterExecution,
    protected: M0ProtectedExecution,
    wal: wal_runtime_layer::WalExecution,
    map: t2_layer::WeakIndexMap,
) -> bool {
    &&& m0_coupled_exec(
        request, initial_members, adapter, protected,
    )
    &&& wal_runtime_layer::exec(ensure_member_full_config(), wal)
    &&& p0_a1_wal_coupled(adapter, wal, map)
}

pub open spec fn p0_prefix_product(
    request: replay_layer::RequestId,
    initial_members: ISet<config_layer::Resource>,
    adapter: A1AdapterExecution,
    protected: M0ProtectedExecution,
    wal: wal_runtime_layer::WalExecution,
    map: t2_layer::WeakIndexMap,
) -> bool {
    &&& p0_execution_pair(
        request, initial_members, adapter, protected, wal, map,
    )
    &&& p0_a1_wal_prefix_simulation(request, adapter, wal, map)
    &&& forall|index: nat| index <= adapter.events.len() ==>
        #[trigger] p0_prefix_product_at(
            request,
            initial_members,
            adapter,
            protected,
            wal,
            map,
            index,
        )
}

pub proof fn p0_a1_global_trace_push(
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

proof fn p0_prefix_trace_agreement_at(
    adapter: A1AdapterExecution,
    wal: wal_runtime_layer::WalExecution,
    map: t2_layer::WeakIndexMap,
    length: nat,
)
    requires
        p0_a1_wal_coupled(adapter, wal, map),
        length <= adapter.events.len(),
    ensures a1_global_trace(adapter.events.take(length as int))
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
        p0_prefix_trace_agreement_at(adapter, wal, map, prior);
        assert(prior < adapter.events.len());
        assert(length == prior + 1);
        assert(adapter.events.take(length as int) =~=
            adapter.events.take(prior as int).push(event));
        p0_a1_global_trace_push(
            adapter.events.take(prior as int), event,
        );
        assert(p0_a1_wal_step_match(event, wal, left, right));
        match event {
            A1AdapterEvent::Observe { event: global } => {
                assert(right == left + 1);
                assert(left < wal.events.len());
                assert(wal.events[left as int] == global);
                assert(wal.events.take(right as int) =~=
                    wal.events.take(left as int).push(global));
            },
            A1AdapterEvent::ServiceLinearize { .. }
            | A1AdapterEvent::EnvironmentAdd { .. } => {
                assert(right == left);
            },
        }
    }
}

pub proof fn p0_a1_wal_prefix_trace_agreement(
    adapter: A1AdapterExecution,
    wal: wal_runtime_layer::WalExecution,
    map: t2_layer::WeakIndexMap,
)
    requires p0_a1_wal_coupled(adapter, wal, map),
    ensures forall|index: nat| index <= adapter.events.len() ==>
        #[trigger] a1_global_trace(
            adapter.events.take(index as int),
        ) == wal.events.take(map.points[index as int] as int),
{
    assert forall|index: nat| index <= adapter.events.len() implies
        #[trigger] a1_global_trace(
            adapter.events.take(index as int),
        ) == wal.events.take(map.points[index as int] as int) by {
        p0_prefix_trace_agreement_at(adapter, wal, map, index);
    }
}

pub proof fn p0_a1_wal_final_trace_agreement(
    adapter: A1AdapterExecution,
    wal: wal_runtime_layer::WalExecution,
    map: t2_layer::WeakIndexMap,
)
    requires p0_a1_wal_coupled(adapter, wal, map),
    ensures a1_global_trace(adapter.events) == wal.events,
{
    p0_prefix_trace_agreement_at(
        adapter, wal, map, adapter.events.len(),
    );
    assert(map.points[adapter.events.len() as int] == wal.events.len());
    assert(adapter.events.take(adapter.events.len() as int)
        =~= adapter.events);
    assert(wal.events.take(wal.events.len() as int) =~= wal.events);
}

pub proof fn p0_a1_wal_steps_derive_related_prefixes(
    request: replay_layer::RequestId,
    initial_members: ISet<config_layer::Resource>,
    adapter: A1AdapterExecution,
    wal: wal_runtime_layer::WalExecution,
    map: t2_layer::WeakIndexMap,
)
    requires
        a1_exec(request, initial_members, adapter),
        wal_runtime_layer::exec(ensure_member_full_config(), wal),
        p0_a1_wal_coupled(adapter, wal, map),
    ensures
        p0_a1_wal_prefix_simulation(request, adapter, wal, map),
        a1_global_trace(adapter.events) == wal.events,
{
    p0_a1_wal_prefix_trace_agreement(adapter, wal, map);
    a1_every_exec_configuration_satisfies_invariant(
        request, initial_members, adapter,
    );
    assert forall|index: nat| index <= adapter.events.len() implies
        #[trigger] p0_a1_wal_related_prefix_at(
            request, adapter, wal, map, index,
        ) by {
        let point = map.points[index as int];
        let prefix = a1_execution_prefix(adapter, index);
        a1_exec_prefix(request, initial_members, adapter, index);
        a1_exec_final_globals_are_projected(
            request, initial_members, prefix,
        );
        assert(prefix.events =~= adapter.events.take(index as int));
        assert(prefix.configs[index as int]
            == adapter.configs[index as int]);
        assert(adapter.configs.len() == adapter.events.len() + 1);
        assert(index < adapter.configs.len());
        if index < adapter.events.len() {
            assert(point <= wal.events.len()) by {
                assert(map.points[(index + 1) as int]
                    <= wal.events.len());
            }
        } else {
            assert(index == adapter.events.len());
            assert(point == wal.events.len());
        }
        assert(wal.configs.len() == wal.events.len() + 1);
        assert(point < wal.configs.len());
        assert(a1_execution_invariant(
            request, initial_members, adapter.configs[index as int],
        ));
        assert(adapter.configs[index as int].history
            == projection_layer::pi_adapter(
                adapter.configs[index as int].globals, request,
            ));
    }
    p0_a1_wal_final_trace_agreement(adapter, wal, map);
}

pub proof fn p0_initial_effect_state_agreement(
    request: replay_layer::RequestId,
    initial_members: ISet<config_layer::Resource>,
)
    ensures p0_effect_state_agreement(
        a1_initial_state(request, initial_members),
        m0_initial_protected_state(request, initial_members),
    ),
{
    assert forall|call_ref: nat|
        #[trigger] ISet::<nat>::empty().contains(call_ref) implies {
            &&& call_ref < Seq::<M0ProtectedCall>::empty().len()
            &&& Seq::<M0ProtectedCall>::empty()[call_ref as int].request
                == request
        } by {
    }
    assert forall|attempt: replay_layer::AttemptId|
        #[trigger] ISet::<replay_layer::AttemptId>::empty().contains(attempt)
            <==> exists|call_ref: nat| {
                &&& call_ref < Seq::<M0ProtectedCall>::empty().len()
                &&& ISet::<nat>::empty().contains(call_ref)
                &&& Seq::<M0ProtectedCall>::empty()[call_ref as int].request
                    == request
                &&& Seq::<M0ProtectedCall>::empty()[call_ref as int].attempt
                    == attempt
            } by {
    }
    assert_isets_equal!(
        ISet::<replay_layer::AttemptId>::empty(),
        p0_protected_linearized_attempts(
            m0_initial_protected_state(request, initial_members),
        ),
    );
}

proof fn p0_a1_observe_preserves_effect_fields(
    state: A1AdapterState,
    event: global_layer::GlobalEvent,
)
    ensures
        a1_apply_observe(state, event).request == state.request,
        a1_apply_observe(state, event).initial_members
            == state.initial_members,
        a1_apply_observe(state, event).members == state.members,
        a1_apply_observe(state, event).environment_additions
            == state.environment_additions,
        a1_apply_observe(state, event).linearized_attempts
            == state.linearized_attempts,
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

proof fn p0_call_append_preserves_effect_state(
    adapter: A1AdapterState,
    before: M0ProtectedState,
    call: M0ProtectedCall,
)
    requires
        p0_effect_state_agreement(adapter, before),
        call.request == before.request,
    ensures p0_effect_state_agreement(
        adapter,
        m0_protected_apply(
            before, M0ProtectedEvent::BrokerInvoke { call },
        ),
    ),
{
    let after = m0_protected_apply(
        before, M0ProtectedEvent::BrokerInvoke { call },
    );
    assert forall|call_ref: nat|
        #[trigger] after.linearized_refs.contains(call_ref) implies {
            &&& call_ref < after.calls.len()
            &&& after.calls[call_ref as int].request == after.request
        } by {
        assert(before.linearized_refs.contains(call_ref));
        assert(call_ref < before.calls.len());
        assert(after.calls[call_ref as int]
            == before.calls[call_ref as int]);
    }
    assert forall|attempt: replay_layer::AttemptId|
        #[trigger] adapter.linearized_attempts.contains(attempt) <==>
            exists|call_ref: nat| {
                &&& call_ref < after.calls.len()
                &&& after.linearized_refs.contains(call_ref)
                &&& after.calls[call_ref as int].request == after.request
                &&& after.calls[call_ref as int].attempt == attempt
            } by {
        if adapter.linearized_attempts.contains(attempt) {
            let call_ref = choose|call_ref: nat| {
                &&& call_ref < before.calls.len()
                &&& before.linearized_refs.contains(call_ref)
                &&& before.calls[call_ref as int].request == before.request
                &&& before.calls[call_ref as int].attempt == attempt
            };
            assert(after.calls[call_ref as int]
                == before.calls[call_ref as int]);
        }
        if exists|call_ref: nat| {
            &&& call_ref < after.calls.len()
            &&& after.linearized_refs.contains(call_ref)
            &&& after.calls[call_ref as int].request == after.request
            &&& after.calls[call_ref as int].attempt == attempt
        } {
            let call_ref = choose|call_ref: nat| {
                &&& call_ref < after.calls.len()
                &&& after.linearized_refs.contains(call_ref)
                &&& after.calls[call_ref as int].request == after.request
                &&& after.calls[call_ref as int].attempt == attempt
            };
            assert(call_ref < before.calls.len());
            assert(after.calls[call_ref as int]
                == before.calls[call_ref as int]);
        }
    }
    assert_isets_equal!(
        adapter.linearized_attempts,
        p0_protected_linearized_attempts(after),
        attempt => {
            if adapter.linearized_attempts.contains(attempt) {
                assert(exists|call_ref: nat| {
                    &&& call_ref < after.calls.len()
                    &&& after.linearized_refs.contains(call_ref)
                    &&& after.calls[call_ref as int].request == after.request
                    &&& after.calls[call_ref as int].attempt == attempt
                });
            }
            if p0_protected_linearized_attempts(after).contains(attempt) {
                assert(adapter.linearized_attempts.contains(attempt));
            }
        }
    );
}

pub proof fn p0_coupled_step_preserves_effect_state_agreement(
    adapter_before: A1AdapterState,
    adapter_event: A1AdapterEvent,
    adapter_after: A1AdapterState,
    protected_before: M0ProtectedState,
    protected_event: M0ProtectedEvent,
    protected_after: M0ProtectedState,
)
    requires
        p0_effect_state_agreement(adapter_before, protected_before),
        a1_step(adapter_before, adapter_event, adapter_after),
        m0_protected_step(
            protected_before, protected_event, protected_after,
        ),
        m0_event_coupled(
            adapter_before,
            adapter_event,
            protected_before,
            protected_event,
        ),
    ensures p0_effect_state_agreement(adapter_after, protected_after),
{
    assert(adapter_after == a1_apply(adapter_before, adapter_event));
    assert(protected_after
        == m0_protected_apply(protected_before, protected_event));
    match adapter_event {
        A1AdapterEvent::Observe { event: global } => {
            p0_a1_observe_preserves_effect_fields(adapter_before, global);
            assert(adapter_after.request == adapter_before.request);
            assert(adapter_after.initial_members
                == adapter_before.initial_members);
            assert(adapter_after.members == adapter_before.members);
            assert(adapter_after.environment_additions
                == adapter_before.environment_additions);
            assert(adapter_after.linearized_attempts
                == adapter_before.linearized_attempts);
            match global {
                global_layer::GlobalEvent::InvokeEvent { .. } => {
                    match protected_event {
                        M0ProtectedEvent::BrokerInvoke { call } => {
                            assert(call.request == protected_before.request);
                            p0_call_append_preserves_effect_state(
                                adapter_after, protected_before, call,
                            );
                            assert(protected_after == m0_protected_apply(
                                protected_before,
                                M0ProtectedEvent::BrokerInvoke { call },
                            ));
                            assert(p0_effect_state_agreement(
                                adapter_after, protected_after,
                            ));
                        },
                        M0ProtectedEvent::ServiceLinearize { .. }
                        | M0ProtectedEvent::ServiceReturn { .. }
                        | M0ProtectedEvent::EnvironmentAdd { .. }
                        | M0ProtectedEvent::Stutter => {
                            assert(false);
                        },
                    }
                },
                global_layer::GlobalEvent::DeliverEvent { .. } => {
                    match protected_event {
                        M0ProtectedEvent::ServiceReturn { .. } => {
                            assert(protected_after.request
                                == protected_before.request);
                            assert(protected_after.initial_members
                                == protected_before.initial_members);
                            assert(protected_after.members
                                == protected_before.members);
                            assert(protected_after.environment_additions
                                == protected_before.environment_additions);
                            assert(protected_after.calls
                                == protected_before.calls);
                            assert(protected_after.linearized_refs
                                == protected_before.linearized_refs);
                            assert(p0_effect_state_agreement(
                                adapter_after, protected_after,
                            ));
                        },
                        M0ProtectedEvent::BrokerInvoke { .. }
                        | M0ProtectedEvent::ServiceLinearize { .. }
                        | M0ProtectedEvent::EnvironmentAdd { .. }
                        | M0ProtectedEvent::Stutter => {
                            assert(false);
                        },
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
                    assert(protected_event == M0ProtectedEvent::Stutter);
                    assert(protected_after == protected_before);
                    assert(p0_effect_state_agreement(
                        adapter_after, protected_after,
                    ));
                },
            }
            assert(protected_after.linearized_refs
                == protected_before.linearized_refs) by {
                match protected_event {
                    M0ProtectedEvent::BrokerInvoke { .. }
                    | M0ProtectedEvent::ServiceReturn { .. }
                    | M0ProtectedEvent::Stutter => {},
                    M0ProtectedEvent::ServiceLinearize { .. }
                    | M0ProtectedEvent::EnvironmentAdd { .. } => {
                        assert(false);
                    },
                }
            }
            assert forall|call_ref: nat|
                call_ref < protected_before.calls.len() implies
                #[trigger] protected_after.calls[call_ref as int]
                    == protected_before.calls[call_ref as int] by {
                match protected_event {
                    M0ProtectedEvent::BrokerInvoke { .. }
                    | M0ProtectedEvent::ServiceReturn { .. }
                    | M0ProtectedEvent::Stutter => {},
                    M0ProtectedEvent::ServiceLinearize { .. }
                    | M0ProtectedEvent::EnvironmentAdd { .. } => {
                        assert(false);
                    },
                }
            }
            assert forall|attempt: replay_layer::AttemptId|
                #[trigger] adapter_after.linearized_attempts.contains(attempt)
                implies exists|call_ref: nat| {
                    &&& call_ref < protected_after.calls.len()
                    &&& protected_after.linearized_refs.contains(call_ref)
                    &&& protected_after.calls[call_ref as int].request
                        == protected_after.request
                    &&& protected_after.calls[call_ref as int].attempt
                        == attempt
                } by {
                assert(adapter_before.linearized_attempts.contains(attempt));
                assert(exists|call_ref: nat| {
                    &&& call_ref < protected_before.calls.len()
                    &&& protected_before.linearized_refs.contains(call_ref)
                    &&& protected_before.calls[call_ref as int].request
                        == protected_before.request
                    &&& protected_before.calls[call_ref as int].attempt
                        == attempt
                });
                let call_ref = choose|call_ref: nat| {
                    &&& call_ref < protected_before.calls.len()
                    &&& protected_before.linearized_refs.contains(call_ref)
                    &&& protected_before.calls[call_ref as int].request
                        == protected_before.request
                    &&& protected_before.calls[call_ref as int].attempt
                        == attempt
                };
                assert(protected_after.calls[call_ref as int]
                    == protected_before.calls[call_ref as int]);
                assert(protected_after.linearized_refs.contains(call_ref));
            }
            assert forall|attempt: replay_layer::AttemptId|
                #[trigger] adapter_after.linearized_attempts.contains(attempt)
                    <==> exists|call_ref: nat| {
                        &&& call_ref < protected_after.calls.len()
                        &&& protected_after.linearized_refs.contains(call_ref)
                        &&& protected_after.calls[call_ref as int].request
                            == protected_after.request
                        &&& protected_after.calls[call_ref as int].attempt
                            == attempt
                    } by {
                if adapter_after.linearized_attempts.contains(attempt) {
                    assert(exists|call_ref: nat| {
                        &&& call_ref < protected_after.calls.len()
                        &&& protected_after.linearized_refs.contains(call_ref)
                        &&& protected_after.calls[call_ref as int].request
                            == protected_after.request
                        &&& protected_after.calls[call_ref as int].attempt
                            == attempt
                    });
                }
                if exists|call_ref: nat| {
                    &&& call_ref < protected_after.calls.len()
                    &&& protected_after.linearized_refs.contains(call_ref)
                    &&& protected_after.calls[call_ref as int].request
                        == protected_after.request
                    &&& protected_after.calls[call_ref as int].attempt
                        == attempt
                } {
                    let call_ref = choose|call_ref: nat| {
                        &&& call_ref < protected_after.calls.len()
                        &&& protected_after.linearized_refs.contains(call_ref)
                        &&& protected_after.calls[call_ref as int].request
                            == protected_after.request
                        &&& protected_after.calls[call_ref as int].attempt
                            == attempt
                    };
                    assert(protected_before.linearized_refs.contains(call_ref));
                    assert(call_ref < protected_before.calls.len());
                    assert(protected_after.calls[call_ref as int]
                        == protected_before.calls[call_ref as int]);
                    assert(adapter_before.linearized_attempts.contains(attempt));
                    assert(adapter_after.linearized_attempts.contains(attempt));
                }
            }
            assert_isets_equal!(
                adapter_after.linearized_attempts,
                p0_protected_linearized_attempts(protected_after),
                attempt => {
                    if adapter_after.linearized_attempts.contains(attempt) {
                        assert(exists|call_ref: nat| {
                            &&& call_ref < protected_after.calls.len()
                            &&& protected_after.linearized_refs
                                .contains(call_ref)
                            &&& protected_after.calls[call_ref as int].request
                                == protected_after.request
                            &&& protected_after.calls[call_ref as int].attempt
                                == attempt
                        });
                    }
                    if p0_protected_linearized_attempts(protected_after)
                        .contains(attempt)
                    {
                        assert(adapter_after.linearized_attempts
                            .contains(attempt));
                    }
                }
            );
            assert(p0_effect_state_agreement(
                adapter_after, protected_after,
            ));
        },
        A1AdapterEvent::ServiceLinearize { attempt } => {
            let call_ref = choose|call_ref: nat| {
                &&& call_ref < protected_before.calls.len()
                &&& protected_before.calls[call_ref as int].request
                    == adapter_before.request
                &&& protected_before.calls[call_ref as int].attempt == attempt
                &&& protected_event
                    == M0ProtectedEvent::ServiceLinearize { call_ref }
            };
            assert(call_ref < protected_before.calls.len());
            assert(protected_before.calls[call_ref as int].request
                == protected_before.request);
            assert(protected_before.calls[call_ref as int].attempt == attempt);
            assert(protected_event
                == M0ProtectedEvent::ServiceLinearize { call_ref });
            assert(protected_after.calls == protected_before.calls);
            assert(protected_after.linearized_refs
                == protected_before.linearized_refs.insert(call_ref));
            assert(protected_after.linearized_refs.contains(call_ref));
            assert(protected_after.calls[call_ref as int]
                == protected_before.calls[call_ref as int]);
            assert(protected_after.request == protected_before.request);
            assert(adapter_after.linearized_attempts
                == adapter_before.linearized_attempts.insert(attempt));
            assert(adapter_after.linearized_attempts.contains(attempt));
            assert forall|selected: nat|
                #[trigger] protected_after.linearized_refs.contains(selected)
                implies {
                    &&& selected < protected_after.calls.len()
                    &&& protected_after.calls[selected as int].request
                        == protected_after.request
                } by {
                if selected == call_ref {
                } else {
                    assert(protected_before.linearized_refs.contains(selected));
                }
            }
            assert forall|candidate: replay_layer::AttemptId|
                #[trigger] adapter_after.linearized_attempts.contains(candidate)
                    <==> exists|selected: nat| {
                        &&& selected < protected_after.calls.len()
                        &&& protected_after.linearized_refs.contains(selected)
                        &&& protected_after.calls[selected as int].request
                            == protected_after.request
                        &&& protected_after.calls[selected as int].attempt
                            == candidate
                    } by {
                if adapter_after.linearized_attempts.contains(candidate) {
                    if candidate == attempt {
                        assert(protected_after.calls[call_ref as int].request
                            == protected_after.request);
                        assert(protected_after.calls[call_ref as int].attempt
                            == candidate);
                        assert(exists|selected: nat| {
                            &&& selected < protected_after.calls.len()
                            &&& protected_after.linearized_refs.contains(selected)
                            &&& protected_after.calls[selected as int].request
                                == protected_after.request
                            &&& protected_after.calls[selected as int].attempt
                                == candidate
                        }) by {
                            let selected = call_ref;
                        }
                    } else {
                        assert(adapter_before.linearized_attempts
                            .contains(candidate));
                        let selected = choose|selected: nat| {
                            &&& selected < protected_before.calls.len()
                            &&& protected_before.linearized_refs
                                .contains(selected)
                            &&& protected_before.calls[selected as int].request
                                == protected_before.request
                            &&& protected_before.calls[selected as int].attempt
                                == candidate
                        };
                        assert(protected_after.linearized_refs
                            .contains(selected));
                    }
                }
                if exists|selected: nat| {
                    &&& selected < protected_after.calls.len()
                    &&& protected_after.linearized_refs.contains(selected)
                    &&& protected_after.calls[selected as int].request
                        == protected_after.request
                    &&& protected_after.calls[selected as int].attempt
                        == candidate
                } {
                    let selected = choose|selected: nat| {
                        &&& selected < protected_after.calls.len()
                        &&& protected_after.linearized_refs.contains(selected)
                        &&& protected_after.calls[selected as int].request
                            == protected_after.request
                        &&& protected_after.calls[selected as int].attempt
                            == candidate
                    };
                    if selected == call_ref {
                        assert(candidate == attempt);
                    } else {
                        assert(protected_before.linearized_refs
                            .contains(selected));
                        assert(adapter_before.linearized_attempts
                            .contains(candidate));
                    }
                }
            }
        },
        A1AdapterEvent::EnvironmentAdd { resource } => {
            assert(protected_event
                == M0ProtectedEvent::EnvironmentAdd { resource });
        },
    }
    assert(p0_effect_state_agreement(adapter_after, protected_after));
}

pub proof fn p0_coupled_final_effect_state_agreement(
    request: replay_layer::RequestId,
    initial_members: ISet<config_layer::Resource>,
    adapter: A1AdapterExecution,
    protected: M0ProtectedExecution,
)
    requires m0_coupled_exec(
        request, initial_members, adapter, protected,
    ),
    ensures p0_effect_state_agreement(
        adapter.configs[adapter.events.len() as int],
        protected.configs[protected.events.len() as int],
    ),
    decreases adapter.events.len(),
{
    if adapter.events.len() == 0 {
        assert(protected.events.len() == 0);
        p0_initial_effect_state_agreement(request, initial_members);
    } else {
        let last: nat = (adapter.events.len() - 1) as nat;
        let adapter_prefix = a1_execution_prefix(adapter, last);
        let protected_prefix = m0_protected_execution_prefix(protected, last);
        m0_coupled_exec_prefix(
            request, initial_members, adapter, protected, last,
        );
        p0_coupled_final_effect_state_agreement(
            request,
            initial_members,
            adapter_prefix,
            protected_prefix,
        );
        assert(adapter_prefix.configs[last as int]
            == adapter.configs[last as int]);
        assert(protected_prefix.configs[last as int]
            == protected.configs[last as int]);
        p0_coupled_step_preserves_effect_state_agreement(
            adapter.configs[last as int],
            adapter.events[last as int],
            adapter.configs[(last + 1) as int],
            protected.configs[last as int],
            protected.events[last as int],
            protected.configs[(last + 1) as int],
        );
    }
}

pub proof fn p0_coupled_every_prefix_effect_state_agreement(
    request: replay_layer::RequestId,
    initial_members: ISet<config_layer::Resource>,
    adapter: A1AdapterExecution,
    protected: M0ProtectedExecution,
)
    requires m0_coupled_exec(
        request, initial_members, adapter, protected,
    ),
    ensures forall|index: nat| index <= adapter.events.len() ==>
        #[trigger] p0_effect_state_agreement(
            adapter.configs[index as int],
            protected.configs[index as int],
        ),
{
    assert forall|index: nat| index <= adapter.events.len() implies
        #[trigger] p0_effect_state_agreement(
            adapter.configs[index as int],
            protected.configs[index as int],
        ) by {
        let adapter_prefix = a1_execution_prefix(adapter, index);
        let protected_prefix = m0_protected_execution_prefix(
            protected, index,
        );
        m0_coupled_exec_prefix(
            request, initial_members, adapter, protected, index,
        );
        p0_coupled_final_effect_state_agreement(
            request,
            initial_members,
            adapter_prefix,
            protected_prefix,
        );
        assert(adapter_prefix.configs[index as int]
            == adapter.configs[index as int]);
        assert(protected_prefix.configs[index as int]
            == protected.configs[index as int]);
    }
}

pub proof fn p0_execution_pair_derives_prefix_product(
    request: replay_layer::RequestId,
    initial_members: ISet<config_layer::Resource>,
    adapter: A1AdapterExecution,
    protected: M0ProtectedExecution,
    wal: wal_runtime_layer::WalExecution,
    map: t2_layer::WeakIndexMap,
)
    requires p0_execution_pair(
        request, initial_members, adapter, protected, wal, map,
    ),
    ensures
        p0_prefix_product(
            request, initial_members, adapter, protected, wal, map,
        ),
        a1_global_trace(adapter.events) == wal.events,
        projection_layer::complete_mediation(
            wal.events,
            m0_erase_calls(
                protected.configs[protected.events.len() as int].calls,
            ),
        ),
        p0_effect_state_agreement(
            adapter.configs[adapter.events.len() as int],
            protected.configs[protected.events.len() as int],
        ),
{
    assert(a1_exec(request, initial_members, adapter));
    assert(wal_runtime_layer::exec(ensure_member_full_config(), wal));
    ensure_member_full_config_is_well_formed();
    p0_a1_wal_steps_derive_related_prefixes(
        request, initial_members, adapter, wal, map,
    );
    p0_coupled_every_prefix_effect_state_agreement(
        request, initial_members, adapter, protected,
    );
    assert(protected.events.len() == adapter.events.len());
    assert forall|index: nat| index <= adapter.events.len() implies
        #[trigger] p0_prefix_product_at(
            request,
            initial_members,
            adapter,
            protected,
            wal,
            map,
            index,
        ) by {
        let point = map.points[index as int];
        let adapter_prefix = a1_execution_prefix(adapter, index);
        let protected_prefix = m0_protected_execution_prefix(
            protected, index,
        );
        let wal_prefix = wal_runtime_layer::execution_prefix(wal, point);
        assert(p0_a1_wal_related_prefix_at(
            request, adapter, wal, map, index,
        ));
        assert(point < wal.configs.len());
        assert(point <= wal.events.len());
        m0_coupled_exec_prefix(
            request, initial_members, adapter, protected, index,
        );
        wal_runtime_layer::exec_prefix(
            ensure_member_full_config(), wal, point,
        );
        m0_coupled_exec_derives_complete_mediation(
            request,
            initial_members,
            adapter_prefix,
            protected_prefix,
        );
        assert(adapter_prefix.events
            =~= adapter.events.take(index as int));
        assert(protected_prefix.configs[index as int]
            == protected.configs[index as int]);
        assert(a1_global_trace(adapter_prefix.events)
            == wal.events.take(point as int));
        assert(wal_prefix.events =~= wal.events.take(point as int));
        assert(a1_global_trace(adapter_prefix.events)
            == wal_prefix.events);
        assert(m0_deployment_exec(
            ensure_member_full_config(),
            request,
            initial_members,
            adapter_prefix,
            protected_prefix,
            wal_prefix,
        ));
        m0_deployment_derives_authorized_linearizations(
            ensure_member_full_config(),
            request,
            initial_members,
            adapter_prefix,
            protected_prefix,
            wal_prefix,
        );
        assert(m0_erase_calls(
            protected.configs[index as int].calls,
        ) == projection_layer::pi_invocations(
            wal.events.take(point as int),
        ));
        assert(projection_layer::complete_mediation(
            wal.events.take(point as int),
            m0_erase_calls(protected.configs[index as int].calls),
        ));
        assert(p0_effect_state_agreement(
            adapter.configs[index as int],
            protected.configs[index as int],
        ));
        assert(m0_every_linearization_durably_authorized(
            ensure_member_full_config(), wal_prefix, protected_prefix,
        ));
    }
    assert(p0_prefix_product(
        request, initial_members, adapter, protected, wal, map,
    ));
    assert(p0_prefix_product_at(
        request,
        initial_members,
        adapter,
        protected,
        wal,
        map,
        adapter.events.len(),
    ));
    assert(map.points[adapter.events.len() as int] == wal.events.len());
    assert(wal.events.take(wal.events.len() as int) =~= wal.events);
}

pub open spec fn p0_index_map_prefix(
    map: t2_layer::WeakIndexMap,
    length: nat,
) -> t2_layer::WeakIndexMap {
    t2_layer::WeakIndexMap {
        points: map.points.take((length + 1) as int),
    }
}

proof fn p0_weak_index_points_monotone(
    source_length: nat,
    target_length: nat,
    map: t2_layer::WeakIndexMap,
    lower: nat,
    upper: nat,
)
    requires
        t2_layer::weak_index_shape(source_length, target_length, map),
        lower <= upper,
        upper <= source_length,
    ensures
        lower < map.points.len(),
        upper < map.points.len(),
        map.points[lower as int] <= map.points[upper as int],
    decreases upper - lower,
{
    if lower < upper {
        let prior: nat = (upper - 1) as nat;
        assert(lower <= prior);
        assert(prior < source_length);
        p0_weak_index_points_monotone(
            source_length, target_length, map, lower, prior,
        );
        assert(prior + 1 == upper);
        assert(map.points[prior as int]
            <= map.points[upper as int]);
    } else {
        assert(lower == upper);
        assert(upper < map.points.len());
    }
}

pub proof fn p0_weak_index_shape_prefix(
    adapter: A1AdapterExecution,
    wal: wal_runtime_layer::WalExecution,
    map: t2_layer::WeakIndexMap,
    length: nat,
)
    requires
        p0_a1_wal_coupled(adapter, wal, map),
        length <= adapter.events.len(),
    ensures t2_layer::weak_index_shape(
        length,
        map.points[length as int],
        p0_index_map_prefix(map, length),
    ),
{
    let prefix_map = p0_index_map_prefix(map, length);
    let endpoint = map.points[length as int];
    assert(prefix_map.points.len() == length + 1);
    assert(prefix_map.points[0] == map.points[0]);
    assert(prefix_map.points[0] == 0);
    assert(prefix_map.points[length as int] == endpoint);
    assert forall|index: nat| index < length implies {
        let left = #[trigger] prefix_map.points[index as int];
        let right = prefix_map.points[(index + 1) as int];
        &&& left <= right
        &&& right <= endpoint
        &&& (right == left || right == left + 1)
    } by {
        assert(index < adapter.events.len());
        assert(prefix_map.points[index as int]
            == map.points[index as int]);
        assert(prefix_map.points[(index + 1) as int]
            == map.points[(index + 1) as int]);
        p0_weak_index_points_monotone(
            adapter.events.len(),
            wal.events.len(),
            map,
            index + 1,
            length,
        );
        assert(map.points[(index + 1) as int] <= endpoint);
    }
}

pub proof fn p0_execution_pair_prefix_closed(
    request: replay_layer::RequestId,
    initial_members: ISet<config_layer::Resource>,
    adapter: A1AdapterExecution,
    protected: M0ProtectedExecution,
    wal: wal_runtime_layer::WalExecution,
    map: t2_layer::WeakIndexMap,
    length: nat,
)
    requires
        p0_execution_pair(
            request, initial_members, adapter, protected, wal, map,
        ),
        length <= adapter.events.len(),
    ensures p0_execution_pair(
        request,
        initial_members,
        a1_execution_prefix(adapter, length),
        m0_protected_execution_prefix(protected, length),
        wal_runtime_layer::execution_prefix(
            wal, map.points[length as int],
        ),
        p0_index_map_prefix(map, length),
    ),
{
    let adapter_prefix = a1_execution_prefix(adapter, length);
    let protected_prefix = m0_protected_execution_prefix(
        protected, length,
    );
    let endpoint = map.points[length as int];
    let wal_prefix = wal_runtime_layer::execution_prefix(wal, endpoint);
    let prefix_map = p0_index_map_prefix(map, length);
    m0_coupled_exec_prefix(
        request, initial_members, adapter, protected, length,
    );
    t4_c0_layer::weak_index_point_bounded(
        adapter.events.len(), wal.events.len(), map, length,
    );
    wal_runtime_layer::exec_prefix(
        ensure_member_full_config(), wal, endpoint,
    );
    p0_weak_index_shape_prefix(adapter, wal, map, length);
    assert(adapter_prefix.events.len() == length);
    assert(wal_prefix.events.len() == endpoint);
    assert(prefix_map.points.len() == length + 1);
    assert forall|index: nat| index < adapter_prefix.events.len() implies
        #[trigger] p0_a1_wal_step_match(
            adapter_prefix.events[index as int],
            wal_prefix,
            prefix_map.points[index as int],
            prefix_map.points[(index + 1) as int],
        ) by {
        let left = prefix_map.points[index as int];
        let right = prefix_map.points[(index + 1) as int];
        assert(index < adapter.events.len());
        assert(adapter_prefix.events[index as int]
            == adapter.events[index as int]);
        assert(left == map.points[index as int]);
        assert(right == map.points[(index + 1) as int]);
        assert(p0_a1_wal_step_match(
            adapter.events[index as int], wal, left, right,
        ));
        p0_weak_index_points_monotone(
            adapter.events.len(),
            wal.events.len(),
            map,
            index + 1,
            length,
        );
        match adapter.events[index as int] {
            A1AdapterEvent::Observe { event: global } => {
                assert(right == left + 1);
                assert(right <= endpoint);
                assert(left < endpoint);
                assert(wal_prefix.events[left as int]
                    == wal.events[left as int]);
                assert(wal_prefix.events[left as int] == global);
            },
            A1AdapterEvent::ServiceLinearize { .. }
            | A1AdapterEvent::EnvironmentAdd { .. } => {
                assert(right == left);
            },
        }
    }
}

pub proof fn p0_prefix_product_closed(
    request: replay_layer::RequestId,
    initial_members: ISet<config_layer::Resource>,
    adapter: A1AdapterExecution,
    protected: M0ProtectedExecution,
    wal: wal_runtime_layer::WalExecution,
    map: t2_layer::WeakIndexMap,
    length: nat,
)
    requires
        p0_execution_pair(
            request, initial_members, adapter, protected, wal, map,
        ),
        length <= adapter.events.len(),
    ensures p0_prefix_product(
        request,
        initial_members,
        a1_execution_prefix(adapter, length),
        m0_protected_execution_prefix(protected, length),
        wal_runtime_layer::execution_prefix(
            wal, map.points[length as int],
        ),
        p0_index_map_prefix(map, length),
    ),
{
    let adapter_prefix = a1_execution_prefix(adapter, length);
    let protected_prefix = m0_protected_execution_prefix(
        protected, length,
    );
    let wal_prefix = wal_runtime_layer::execution_prefix(
        wal, map.points[length as int],
    );
    let prefix_map = p0_index_map_prefix(map, length);
    p0_execution_pair_prefix_closed(
        request,
        initial_members,
        adapter,
        protected,
        wal,
        map,
        length,
    );
    p0_execution_pair_derives_prefix_product(
        request,
        initial_members,
        adapter_prefix,
        protected_prefix,
        wal_prefix,
        prefix_map,
    );
}

pub open spec fn p0_projection_index(
    events: Seq<A1AdapterEvent>,
    index: nat,
) -> nat {
    a1_global_trace(events.take(index as int)).len()
}

pub open spec fn p0_canonical_index_map(
    events: Seq<A1AdapterEvent>,
) -> t2_layer::WeakIndexMap {
    t2_layer::WeakIndexMap {
        points: Seq::new((events.len() + 1) as nat, |index: int|
            p0_projection_index(events, index as nat),
        ),
    }
}

pub proof fn p0_projection_prefix_exact(
    events: Seq<A1AdapterEvent>,
    length: nat,
)
    requires length <= events.len(),
    ensures
        append_layer::is_prefix(
            a1_global_trace(events.take(length as int)),
            a1_global_trace(events),
        ),
        a1_global_trace(events.take(length as int)).len()
            <= a1_global_trace(events).len(),
        a1_global_trace(events.take(length as int))
            == a1_global_trace(events).take(
                p0_projection_index(events, length) as int,
            ),
{
    m0_a1_global_trace_prefix(events, length);
    assert(append_layer::is_prefix(
        a1_global_trace(events.take(length as int)),
        a1_global_trace(events),
    ));
}

pub proof fn p0_canonical_index_map_has_shape(
    events: Seq<A1AdapterEvent>,
)
    ensures t2_layer::weak_index_shape(
        events.len(),
        a1_global_trace(events).len(),
        p0_canonical_index_map(events),
    ),
{
    let map = p0_canonical_index_map(events);
    assert(map.points.len() == events.len() + 1);
    assert(events.take(0) =~= Seq::empty());
    assert(map.points[0] == 0);
    assert(events.take(events.len() as int) =~= events);
    assert(map.points[events.len() as int]
        == a1_global_trace(events).len());
    assert forall|index: nat| index < events.len() implies {
        let left = #[trigger] map.points[index as int];
        let right = map.points[(index + 1) as int];
        &&& left <= right
        &&& right <= a1_global_trace(events).len()
        &&& (right == left || right == left + 1)
    } by {
        let event = events[index as int];
        let left = map.points[index as int];
        let right = map.points[(index + 1) as int];
        assert(events.take((index + 1) as int) =~=
            events.take(index as int).push(event));
        p0_a1_global_trace_push(events.take(index as int), event);
        p0_projection_prefix_exact(events, index + 1);
        assert(append_layer::is_prefix(
            a1_global_trace(events.take((index + 1) as int)),
            a1_global_trace(events),
        ));
        assert(a1_global_trace(events.take((index + 1) as int)).len()
            <= a1_global_trace(events).len());
        match event {
            A1AdapterEvent::Observe { .. } => {
                assert(right == left + 1);
            },
            A1AdapterEvent::ServiceLinearize { .. }
            | A1AdapterEvent::EnvironmentAdd { .. } => {
                assert(right == left);
            },
        }
    }
}

proof fn p0_canonical_step_match_at(
    adapter: A1AdapterExecution,
    wal: wal_runtime_layer::WalExecution,
    index: nat,
)
    requires
        a1_global_trace(adapter.events) == wal.events,
        index < adapter.events.len(),
    ensures p0_a1_wal_step_match(
        adapter.events[index as int],
        wal,
        p0_canonical_index_map(adapter.events).points[index as int],
        p0_canonical_index_map(adapter.events).points[
            (index + 1) as int
        ],
    ),
{
    let map = p0_canonical_index_map(adapter.events);
    let event = adapter.events[index as int];
    let left = map.points[index as int];
    let right = map.points[(index + 1) as int];
    assert(adapter.events.take((index + 1) as int) =~=
        adapter.events.take(index as int).push(event));
    p0_a1_global_trace_push(
        adapter.events.take(index as int), event,
    );
    p0_projection_prefix_exact(adapter.events, index);
    p0_projection_prefix_exact(adapter.events, index + 1);
    match event {
        A1AdapterEvent::Observe { event: global } => {
            assert(right == left + 1);
            assert(a1_global_trace(adapter.events).take(right as int)
                =~= a1_global_trace(adapter.events).take(left as int)
                    .push(global));
            assert(left < a1_global_trace(adapter.events).len());
            assert(a1_global_trace(adapter.events).take(right as int)[
                left as int
            ] == global);
            assert(a1_global_trace(adapter.events).take(right as int)[
                left as int
            ] == a1_global_trace(adapter.events)[left as int]);
            assert(a1_global_trace(adapter.events)[left as int]
                == global);
            assert(wal.events[left as int] == global);
        },
        A1AdapterEvent::ServiceLinearize { .. }
        | A1AdapterEvent::EnvironmentAdd { .. } => {
            assert(right == left);
        },
    }
}

pub proof fn p0_canonical_map_couples_trace_equal_execution(
    adapter: A1AdapterExecution,
    wal: wal_runtime_layer::WalExecution,
)
    requires a1_global_trace(adapter.events) == wal.events,
    ensures p0_a1_wal_coupled(
        adapter,
        wal,
        p0_canonical_index_map(adapter.events),
    ),
{
    let map = p0_canonical_index_map(adapter.events);
    p0_canonical_index_map_has_shape(adapter.events);
    assert(t2_layer::weak_index_shape(
        adapter.events.len(), wal.events.len(), map,
    ));
    assert forall|index: nat| index < adapter.events.len() implies
        #[trigger] p0_a1_wal_step_match(
            adapter.events[index as int],
            wal,
            map.points[index as int],
            map.points[(index + 1) as int],
        ) by {
        p0_canonical_step_match_at(adapter, wal, index);
    }
}

pub proof fn p0_trace_equal_execution_pair(
    request: replay_layer::RequestId,
    initial_members: ISet<config_layer::Resource>,
    adapter: A1AdapterExecution,
    protected: M0ProtectedExecution,
    wal: wal_runtime_layer::WalExecution,
)
    requires
        m0_coupled_exec(
            request, initial_members, adapter, protected,
        ),
        wal_runtime_layer::exec(ensure_member_full_config(), wal),
        a1_global_trace(adapter.events) == wal.events,
    ensures p0_execution_pair(
        request,
        initial_members,
        adapter,
        protected,
        wal,
        p0_canonical_index_map(adapter.events),
    ),
{
    p0_canonical_map_couples_trace_equal_execution(adapter, wal);
}

pub proof fn t6_p0_executable_crash_retry_prefix_product()
    ensures {
        let request = ensure_member_request_zero();
        let initial = ISet::<config_layer::Resource>::empty();
        let adapter = a1_retry_adapter_execution();
        let protected = m0_retry_protected_execution();
        let wal = a1_retry_wal_execution();
        let map = p0_canonical_index_map(adapter.events);
        &&& p0_prefix_product(
            request, initial, adapter, protected, wal, map,
        )
        &&& adapter.events.len() == 32
        &&& wal.events.len() == 31
        &&& map.points.len() == 33
        &&& map.points[0] == 0
        &&& map.points[32] == 31
        &&& adapter.events[13]
            == A1AdapterEvent::ServiceLinearize { attempt: 1 }
        &&& map.points[13] == map.points[14]
        &&& a1_explicit_crash_retry_trace_shape(wal.events)
        &&& m0_linearization_count(protected.events) == 1
        &&& adapter.configs[adapter.events.len() as int]
            .linearized_attempts.contains(1)
        &&& !adapter.configs[adapter.events.len() as int]
            .linearized_attempts.contains(2)
        &&& protected.configs[protected.events.len() as int]
            .members.contains(ensure_member_target(request))
        &&& projection_layer::complete_mediation(
            wal.events,
            m0_erase_calls(
                protected.configs[protected.events.len() as int].calls,
            ),
        )
        &&& p0_effect_state_agreement(
            adapter.configs[adapter.events.len() as int],
            protected.configs[protected.events.len() as int],
        )
    },
{
    let request = ensure_member_request_zero();
    let initial = ISet::<config_layer::Resource>::empty();
    let adapter = a1_retry_adapter_execution();
    let protected = m0_retry_protected_execution();
    let wal = a1_retry_wal_execution();
    let map = p0_canonical_index_map(adapter.events);
    a1_retry_adapter_execution_exec();
    a1_retry_wal_execution_exec();
    a1_retry_has_explicit_crash_recovery_shape();
    m0_retry_protected_execution_exec();
    m0_retry_adapter_and_service_are_coupled();
    m0_retry_adapter_execution_has_shape();
    m0_retry_has_one_target_action();
    assert(a1_global_trace(adapter.events) == wal.events);
    p0_trace_equal_execution_pair(
        request, initial, adapter, protected, wal,
    );
    p0_execution_pair_derives_prefix_product(
        request, initial, adapter, protected, wal, map,
    );
    assert(adapter.events.len() == 32);
    assert(wal.events.len() == 31);
    assert(map.points.len() == 33);
    assert(map.points[0] == 0);
    assert(map.points[32] == 31);
    assert(adapter.events[13]
        == A1AdapterEvent::ServiceLinearize { attempt: 1 });
    assert(p0_a1_wal_step_match(
        adapter.events[13], wal, map.points[13], map.points[14],
    ));
    assert(map.points[13] == map.points[14]);
    assert(a1_explicit_crash_retry_trace_shape(wal.events));
    assert(m0_linearization_count(protected.events) == 1);
    assert(protected.configs[protected.events.len() as int]
        .members.contains(ensure_member_target(request)));
}

pub proof fn t6_p0_prefix_product_nonvacuity()
    ensures exists|
        adapter: A1AdapterExecution,
        protected: M0ProtectedExecution,
        wal: wal_runtime_layer::WalExecution,
        map: t2_layer::WeakIndexMap,
    | #![auto] {
        &&& adapter == a1_retry_adapter_execution()
        &&& protected == m0_retry_protected_execution()
        &&& wal == a1_retry_wal_execution()
        &&& map == p0_canonical_index_map(adapter.events)
        &&& p0_prefix_product(
            ensure_member_request_zero(),
            ISet::<config_layer::Resource>::empty(),
            adapter,
            protected,
            wal,
            map,
        )
        &&& adapter.events.len() == 32
        &&& wal.events.len() == 31
        &&& map.points[13] == map.points[14]
        &&& a1_explicit_crash_retry_trace_shape(wal.events)
        &&& m0_linearization_count(protected.events) == 1
        &&& adapter.configs[adapter.events.len() as int]
            .linearized_attempts.contains(1)
        &&& !adapter.configs[adapter.events.len() as int]
            .linearized_attempts.contains(2)
        &&& protected.configs[protected.events.len() as int]
            .members.contains(
                ensure_member_target(ensure_member_request_zero()),
            )
        &&& projection_layer::complete_mediation(
            wal.events,
            m0_erase_calls(
                protected.configs[protected.events.len() as int].calls,
            ),
        )
        &&& p0_effect_state_agreement(
            adapter.configs[adapter.events.len() as int],
            protected.configs[protected.events.len() as int],
        )
    },
{
    t6_p0_executable_crash_retry_prefix_product();
    assert(exists|
        adapter: A1AdapterExecution,
        protected: M0ProtectedExecution,
        wal: wal_runtime_layer::WalExecution,
        map: t2_layer::WeakIndexMap,
    | #![auto] {
        &&& adapter == a1_retry_adapter_execution()
        &&& protected == m0_retry_protected_execution()
        &&& wal == a1_retry_wal_execution()
        &&& map == p0_canonical_index_map(adapter.events)
        &&& p0_prefix_product(
            ensure_member_request_zero(),
            ISet::<config_layer::Resource>::empty(),
            adapter,
            protected,
            wal,
            map,
        )
        &&& adapter.events.len() == 32
        &&& wal.events.len() == 31
        &&& map.points[13] == map.points[14]
        &&& a1_explicit_crash_retry_trace_shape(wal.events)
        &&& m0_linearization_count(protected.events) == 1
        &&& adapter.configs[adapter.events.len() as int]
            .linearized_attempts.contains(1)
        &&& !adapter.configs[adapter.events.len() as int]
            .linearized_attempts.contains(2)
        &&& protected.configs[protected.events.len() as int]
            .members.contains(
                ensure_member_target(ensure_member_request_zero()),
            )
        &&& projection_layer::complete_mediation(
            wal.events,
            m0_erase_calls(
                protected.configs[protected.events.len() as int].calls,
            ),
        )
        &&& p0_effect_state_agreement(
            adapter.configs[adapter.events.len() as int],
            protected.configs[protected.events.len() as int],
        )
    }) by {
        let adapter = a1_retry_adapter_execution();
        let protected = m0_retry_protected_execution();
        let wal = a1_retry_wal_execution();
        let map = p0_canonical_index_map(adapter.events);
    }
}

} // verus!
