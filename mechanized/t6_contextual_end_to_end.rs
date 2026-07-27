use vstd::prelude::*;

#[path = "t6_prefix_simulation.rs"]
pub mod t6_p0_layer;

verus! {

use t6_p0_layer::*;
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
use c1_layer::replay_layer;

// T6-X0 composes the P0 adapter-to-WAL index with T4-C2's canonical
// WAL-to-Broker index.  The generic theorem remains conditional on a plugged
// execution and adapter semantics.  The EnsureMember theorem additionally
// grounds that semantic run in P0's independently executed protected state.

pub open spec fn x0_adapter_broker_map(
    adapter_wal_map: t2_layer::WeakIndexMap,
    wal: wal_runtime_layer::WalExecution,
) -> t2_layer::WeakIndexMap {
    t4_c0_layer::compose_index_maps(
        adapter_wal_map,
        t4_c0_layer::canonical_composed_map(wal),
    )
}

pub open spec fn x0_external_run_matches_protected(
    adapter: A1AdapterState,
    protected: M0ProtectedState,
) -> bool {
    let run = a1_external_run(adapter);
    &&& adapter.request == protected.request
    &&& run.pre == protected.initial_members
    &&& run.post == protected.members
    &&& run.interference.environment_additions
        == protected.environment_additions
    &&& run.interference.linearized_attempts
        =~= p0_protected_linearized_attempts(protected)
}

pub proof fn p0_effect_agreement_grounds_external_run(
    adapter: A1AdapterState,
    protected: M0ProtectedState,
)
    requires p0_effect_state_agreement(adapter, protected),
    ensures x0_external_run_matches_protected(adapter, protected),
{
}

pub open spec fn x0_contextual_prefix_at<S>(
    request: replay_layer::RequestId,
    initial_members: ISet<config_layer::Resource>,
    adapter: A1AdapterExecution,
    protected: M0ProtectedExecution,
    context: t4_c1_layer::ProgramContext<S>,
    plugged: t4_c1_layer::PluggedWalExecution<S>,
    adapter_wal_map: t2_layer::WeakIndexMap,
    index: nat,
) -> bool {
    let cfg = ensure_member_full_config();
    let target = t4_layer::canonical_plugged_broker_execution(cfg, plugged);
    let combined = x0_adapter_broker_map(
        adapter_wal_map, plugged.machine,
    );
    if index <= adapter.events.len()
        && index < adapter.configs.len()
        && index < protected.configs.len()
        && index < adapter_wal_map.points.len()
        && index < combined.points.len()
    {
        let wal_point = adapter_wal_map.points[index as int];
        let broker_point = combined.points[index as int];
        if wal_point <= plugged.machine.events.len()
            && wal_point < plugged.machine.configs.len()
            && wal_point < plugged.contexts.len()
            && broker_point <= target.machine.events.len()
            && broker_point < target.machine.configs.len()
            && broker_point < target.contexts.len()
        {
            &&& p0_prefix_product_at(
                request,
                initial_members,
                adapter,
                protected,
                plugged.machine,
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
            &&& x0_external_run_matches_protected(
                adapter.configs[index as int],
                protected.configs[index as int],
            )
            &&& adapter.configs[index as int].history
                == projection_layer::pi_adapter(
                    target.machine.events.take(broker_point as int),
                    request,
                )
            &&& plugged.contexts[wal_point as int]
                == target.contexts[broker_point as int]
            &&& t4_c1_layer::wal_context_view_at(
                cfg, plugged.machine, wal_point,
            ) == t4_c1_layer::broker_context_view_at(
                cfg, target.machine, broker_point,
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

pub closed spec fn x0_contextual_product<S>(
    request: replay_layer::RequestId,
    initial_members: ISet<config_layer::Resource>,
    adapter: A1AdapterExecution,
    protected: M0ProtectedExecution,
    context: t4_c1_layer::ProgramContext<S>,
    plugged: t4_c1_layer::PluggedWalExecution<S>,
    adapter_wal_map: t2_layer::WeakIndexMap,
) -> bool {
    let cfg = ensure_member_full_config();
    let target = t4_layer::canonical_plugged_broker_execution(cfg, plugged);
    let combined = x0_adapter_broker_map(
        adapter_wal_map, plugged.machine,
    );
    &&& t4_c1_layer::storage_parametric_context(cfg, context)
    &&& t4_c1_layer::plugged_wal_exec(cfg, context, plugged)
    &&& p0_execution_pair(
        request,
        initial_members,
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
        #[trigger] x0_contextual_prefix_at(
            request,
            initial_members,
            adapter,
            protected,
            context,
            plugged,
            adapter_wal_map,
            index,
        )
}

pub open spec fn x0_single_request_end_to_end<S>(
    request: replay_layer::RequestId,
    initial_members: ISet<config_layer::Resource>,
    adapter: A1AdapterExecution,
    protected: M0ProtectedExecution,
    context: t4_c1_layer::ProgramContext<S>,
    plugged: t4_c1_layer::PluggedWalExecution<S>,
    adapter_wal_map: t2_layer::WeakIndexMap,
) -> bool {
    if adapter.events.len() < adapter.configs.len()
        && protected.events.len() < protected.configs.len()
    {
        let final_adapter = adapter.configs[adapter.events.len() as int];
        let final_protected = protected.configs[
            protected.events.len() as int
        ];
        let run = a1_external_run(final_adapter);
        &&& x0_contextual_product(
            request,
            initial_members,
            adapter,
            protected,
            context,
            plugged,
            adapter_wal_map,
        )
        &&& adapter_rely(
            ensure_member_paper(),
            plugged.machine.events,
            request,
            run,
        )
        &&& per_request_effect_refinement(
            ensure_member_paper(),
            plugged.machine.events,
            request,
            run,
        )
        &&& x0_external_run_matches_protected(
            final_adapter, final_protected,
        )
    } else {
        false
    }
}

pub closed spec fn x0_ensure_member_source_terminal_statement(
    request: replay_layer::RequestId,
    adapter: A1AdapterExecution,
    protected: M0ProtectedExecution,
    wal: wal_runtime_layer::WalExecution,
    outcome: TerminalOutcome,
) -> bool {
    if adapter.events.len() < adapter.configs.len()
        && protected.events.len() < protected.configs.len()
        && wal.events.len() < wal.configs.len()
    {
        let cfg = ensure_member_full_config();
        let final_adapter = adapter.configs[adapter.events.len() as int];
        let final_protected = protected.configs[
            protected.events.len() as int
        ];
        let final_wal = wal.configs[wal.events.len() as int];
        let run = a1_external_run(final_adapter);
        let accepted = m0_erase_calls(final_protected.calls);
        &&& t1_layer::paper_config_wf(ensure_member_paper())
        &&& adapter_verified(ensure_member_paper())
        &&& terminal(wal.events, request) == Option::Some(outcome)
        &&& terminal_evidence_and_compatibility(
            cfg,
            wal.events,
            final_wal.evidence.records,
            request,
            outcome,
        )
        &&& refines(
            ensure_member_paper(),
            request,
            projection_layer::pi_adapter(
                wal.events, request,
            ),
            run,
            outcome,
        )
        &&& projection_layer::complete_mediation(
            wal.events, accepted,
        )
        &&& p0_effect_state_agreement(final_adapter, final_protected)
        &&& m0_every_linearization_durably_authorized(
            cfg, wal, protected,
        )
    } else {
        false
    }
}

pub closed spec fn x0_ensure_member_target_terminal_statement<S>(
    request: replay_layer::RequestId,
    adapter: A1AdapterExecution,
    protected: M0ProtectedExecution,
    plugged: t4_c1_layer::PluggedWalExecution<S>,
    outcome: TerminalOutcome,
) -> bool {
    if adapter.events.len() < adapter.configs.len()
        && protected.events.len() < protected.configs.len()
    {
        let cfg = ensure_member_full_config();
        let final_adapter = adapter.configs[adapter.events.len() as int];
        let final_protected = protected.configs[
            protected.events.len() as int
        ];
        let run = a1_external_run(final_adapter);
        let accepted = m0_erase_calls(final_protected.calls);
        let target = t4_layer::canonical_plugged_broker_execution(
            cfg, plugged,
        );
        &&& terminal(target.machine.events, request)
            == Option::Some(outcome)
        &&& refines(
            ensure_member_paper(),
            request,
            projection_layer::pi_adapter(
                target.machine.events, request,
            ),
            run,
            outcome,
        )
        &&& per_request_effect_refinement(
            ensure_member_paper(), target.machine.events, request, run,
        )
        &&& projection_layer::complete_mediation(
            target.machine.events, accepted,
        )
    } else {
        false
    }
}

pub closed spec fn x0_ensure_member_terminal_statement<S>(
    request: replay_layer::RequestId,
    initial_members: ISet<config_layer::Resource>,
    adapter: A1AdapterExecution,
    protected: M0ProtectedExecution,
    context: t4_c1_layer::ProgramContext<S>,
    plugged: t4_c1_layer::PluggedWalExecution<S>,
    adapter_wal_map: t2_layer::WeakIndexMap,
    outcome: TerminalOutcome,
) -> bool {
    &&& x0_single_request_end_to_end(
        request,
        initial_members,
        adapter,
        protected,
        context,
        plugged,
        adapter_wal_map,
    )
    &&& x0_ensure_member_source_terminal_statement(
        request,
        adapter,
        protected,
        plugged.machine,
        outcome,
    )
    &&& x0_ensure_member_target_terminal_statement(
        request,
        adapter,
        protected,
        plugged,
        outcome,
    )
}

pub proof fn x0_contextual_wal_final_representation<X, I, S>(
    paper: t1_layer::PaperConfig<Adapter<X, I>>,
    context: t4_c1_layer::ProgramContext<S>,
    plugged: t4_c1_layer::PluggedWalExecution<S>,
)
    requires
        t1_layer::paper_config_wf(paper),
        t4_c1_layer::storage_parametric_context(
            t1_layer::paper_broker_config(paper), context,
        ),
        t4_c1_layer::plugged_wal_exec(
            t1_layer::paper_broker_config(paper), context, plugged,
        ),
    ensures {
        let cfg = t1_layer::paper_broker_config(paper);
        let target = t4_layer::canonical_plugged_broker_execution(
            cfg, plugged,
        );
        &&& t4_layer::t4_c2_statement(cfg, context, plugged)
        &&& wal_runtime_layer::exec(cfg, plugged.machine)
        &&& wal_trace_layer::admissible_wal_trace(cfg, plugged.machine)
        &&& wal_trace_layer::trace_agreement(cfg, plugged.machine)
        &&& t4_c0_layer::wal_broker_representation(
            cfg,
            plugged.machine.configs[
                plugged.machine.events.len() as int
            ],
            target.machine.configs[target.machine.events.len() as int],
        )
    },
{
    let cfg = t1_layer::paper_broker_config(paper);
    let source = plugged.machine;
    let target = t4_layer::canonical_plugged_broker_execution(cfg, plugged);
    let map = t4_c0_layer::canonical_composed_map(source);
    t4_layer::t4_c2_contextual_replacement(paper, context, plugged);
    t4_c1_layer::plugged_wal_embeds(cfg, context, plugged);
    assert(t4_layer::t4_c2_statement(cfg, context, plugged));
    assert(t4_c0_layer::weak_simulation_index_map(
        cfg, source, target.machine, map,
    ));
    assert(t4_c0_layer::related_prefixes(
        cfg, source, target.machine, map,
    ));
    assert(t2_layer::weak_index_shape(
        source.events.len(), target.machine.events.len(), map,
    ));
    assert(map.points[source.events.len() as int]
        == target.machine.events.len());
    assert(t4_c0_layer::wal_broker_representation(
        cfg,
        source.configs[source.events.len() as int],
        target.machine.configs[target.machine.events.len() as int],
    ));
    assert(t4_c0_layer::t4_c0_statement(cfg, source));
}

// Generic conditional adapter theorem.  It is intentionally separate from
// the protected-state grounding below: AdapterRely remains an explicit premise
// for an arbitrary adapter and arbitrary storage-parametric program context.
pub proof fn x0_contextual_per_request_effect_refines<X, I, S>(
    paper: t1_layer::PaperConfig<Adapter<X, I>>,
    context: t4_c1_layer::ProgramContext<S>,
    plugged: t4_c1_layer::PluggedWalExecution<S>,
    request: replay_layer::RequestId,
    run: ExternalRun<X, I>,
)
    requires
        t1_layer::paper_config_wf(paper),
        t4_c1_layer::storage_parametric_context(
            t1_layer::paper_broker_config(paper), context,
        ),
        t4_c1_layer::plugged_wal_exec(
            t1_layer::paper_broker_config(paper), context, plugged,
        ),
        adapter_verified(paper),
        adapter_rely(paper, plugged.machine.events, request, run),
    ensures
        t4_layer::t4_c2_statement(
            t1_layer::paper_broker_config(paper), context, plugged,
        ),
        per_request_effect_refinement(
            paper, plugged.machine.events, request, run,
        ),
{
    let cfg = t1_layer::paper_broker_config(paper);
    let target = t4_layer::canonical_plugged_broker_execution(cfg, plugged);
    x0_contextual_wal_final_representation(paper, context, plugged);
    wal_per_request_effect_refines(
        paper,
        plugged.machine,
        target.machine.configs[target.machine.events.len() as int],
        request,
        run,
    );
}

pub proof fn x0_contextual_terminal_outcome_refines<X, I, S>(
    paper: t1_layer::PaperConfig<Adapter<X, I>>,
    context: t4_c1_layer::ProgramContext<S>,
    plugged: t4_c1_layer::PluggedWalExecution<S>,
    request: replay_layer::RequestId,
    run: ExternalRun<X, I>,
    outcome: TerminalOutcome,
)
    requires
        t1_layer::paper_config_wf(paper),
        t4_c1_layer::storage_parametric_context(
            t1_layer::paper_broker_config(paper), context,
        ),
        t4_c1_layer::plugged_wal_exec(
            t1_layer::paper_broker_config(paper), context, plugged,
        ),
        adapter_verified(paper),
        adapter_rely(paper, plugged.machine.events, request, run),
        terminal(plugged.machine.events, request) == Option::Some(outcome),
    ensures
        t4_layer::t4_c2_statement(
            t1_layer::paper_broker_config(paper), context, plugged,
        ),
        refines(
            paper,
            request,
            projection_layer::pi_adapter(
                plugged.machine.events, request,
            ),
            run,
            outcome,
        ),
        per_request_effect_refinement(
            paper, plugged.machine.events, request, run,
        ),
{
    let cfg = t1_layer::paper_broker_config(paper);
    let target = t4_layer::canonical_plugged_broker_execution(cfg, plugged);
    x0_contextual_wal_final_representation(paper, context, plugged);
    wal_terminal_outcome_refines(
        paper,
        plugged.machine,
        target.machine.configs[target.machine.events.len() as int],
        request,
        run,
        outcome,
    );
}

pub proof fn x0_projection_transports_terminal_refinement<X, I>(
    paper: t1_layer::PaperConfig<Adapter<X, I>>,
    source: Seq<global_layer::GlobalEvent>,
    target: Seq<global_layer::GlobalEvent>,
    request: replay_layer::RequestId,
    run: ExternalRun<X, I>,
    outcome: TerminalOutcome,
)
    requires
        t4_c0_layer::t4_projection_agreement(source, target),
        terminal(source, request) == Option::Some(outcome),
        refines(
            paper,
            request,
            projection_layer::pi_adapter(source, request),
            run,
            outcome,
        ),
    ensures
        projection_layer::pi_adapter(source, request)
            == projection_layer::pi_adapter(target, request),
        terminal(target, request) == Option::Some(outcome),
        refines(
            paper,
            request,
            projection_layer::pi_adapter(target, request),
            run,
            outcome,
        ),
        per_request_effect_refinement(paper, target, request, run),
{
    assert(projection_layer::pi_journal(source)
        == projection_layer::pi_journal(target));
    assert(projection_layer::pi_adapter(source, request)
        == projection_layer::pi_adapter(target, request));
}

// Paper-facing generic contextual theorem.  The operational P0 instance below
// discharges its adapter premises for EnsureMember; this theorem itself remains
// polymorphic in the adapter state, interference witness, and context state.
pub proof fn x0_contextual_broker_terminal_outcome_refines<X, I, S>(
    paper: t1_layer::PaperConfig<Adapter<X, I>>,
    context: t4_c1_layer::ProgramContext<S>,
    plugged: t4_c1_layer::PluggedWalExecution<S>,
    request: replay_layer::RequestId,
    run: ExternalRun<X, I>,
    outcome: TerminalOutcome,
)
    requires
        t1_layer::paper_config_wf(paper),
        t4_c1_layer::storage_parametric_context(
            t1_layer::paper_broker_config(paper), context,
        ),
        t4_c1_layer::plugged_wal_exec(
            t1_layer::paper_broker_config(paper), context, plugged,
        ),
        adapter_verified(paper),
        adapter_rely(paper, plugged.machine.events, request, run),
        terminal(plugged.machine.events, request) == Option::Some(outcome),
    ensures {
        let cfg = t1_layer::paper_broker_config(paper);
        let target = t4_layer::canonical_plugged_broker_execution(
            cfg, plugged,
        );
        &&& t4_layer::t4_c2_statement(cfg, context, plugged)
        &&& terminal(target.machine.events, request)
            == Option::Some(outcome)
        &&& refines(
            paper,
            request,
            projection_layer::pi_adapter(
                target.machine.events, request,
            ),
            run,
            outcome,
        )
        &&& per_request_effect_refinement(
            paper, target.machine.events, request, run,
        )
    },
{
    let cfg = t1_layer::paper_broker_config(paper);
    let source = plugged.machine;
    let target = t4_layer::canonical_plugged_broker_execution(cfg, plugged);
    x0_contextual_terminal_outcome_refines(
        paper, context, plugged, request, run, outcome,
    );
    assert(t4_c0_layer::t4_projection_agreement(
        source.events, target.machine.events,
    ));
    x0_projection_transports_terminal_refinement(
        paper,
        source.events,
        target.machine.events,
        request,
        run,
        outcome,
    );
}

pub proof fn x0_exclusive_context_endpoint_mediation(
    plugged: t4_c1_layer::PluggedWalExecution<M0ProtectedHandleState>,
    accepted: Seq<projection_layer::ProtectedInvocation>,
)
    requires
        t4_layer::t4_c2_statement(
            ensure_member_full_config(),
            m0_exclusive_handle_context(ensure_member_full_config()),
            plugged,
        ),
        accepted == plugged.contexts[
            plugged.machine.events.len() as int
        ].invocations,
        projection_layer::complete_mediation(
            plugged.machine.events, accepted,
        ),
    ensures {
        let target = t4_layer::canonical_plugged_broker_execution(
            ensure_member_full_config(), plugged,
        );
        &&& target.contexts[target.machine.events.len() as int].invocations
            == accepted
        &&& projection_layer::complete_mediation(
            target.machine.events,
            target.contexts[target.machine.events.len() as int].invocations,
        )
    },
{
    let cfg = ensure_member_full_config();
    let target = t4_layer::canonical_plugged_broker_execution(cfg, plugged);
    let map = t4_c0_layer::canonical_composed_map(plugged.machine);
    assert(t4_c0_layer::weak_simulation_index_map(
        cfg, plugged.machine, target.machine, map,
    ));
    assert(t2_layer::weak_index_shape(
        plugged.machine.events.len(), target.machine.events.len(), map,
    ));
    assert(map.points[plugged.machine.events.len() as int]
        == target.machine.events.len());
    assert(t4_layer::mapped_context_states_equal(plugged, target, map));
    assert(plugged.contexts[plugged.machine.events.len() as int]
        == target.contexts[target.machine.events.len() as int]);
    assert(t4_c0_layer::t4_projection_agreement(
        plugged.machine.events, target.machine.events,
    ));
    assert(projection_layer::pi_physical(plugged.machine.events)
        == projection_layer::pi_physical(target.machine.events));
    assert(projection_layer::pi_invocations(plugged.machine.events)
        == projection_layer::pi_invocations(target.machine.events));
}

proof fn x0_contextual_prefix_from_products<S>(
    request: replay_layer::RequestId,
    initial_members: ISet<config_layer::Resource>,
    adapter: A1AdapterExecution,
    protected: M0ProtectedExecution,
    context: t4_c1_layer::ProgramContext<S>,
    plugged: t4_c1_layer::PluggedWalExecution<S>,
    adapter_wal_map: t2_layer::WeakIndexMap,
    index: nat,
)
    requires
        t4_c1_layer::plugged_wal_exec(
            ensure_member_full_config(), context, plugged,
        ),
        p0_prefix_product(
            request,
            initial_members,
            adapter,
            protected,
            plugged.machine,
            adapter_wal_map,
        ),
        t4_layer::t4_c2_statement(
            ensure_member_full_config(), context, plugged,
        ),
        t2_layer::weak_index_shape(
            adapter.events.len(),
            t4_layer::canonical_plugged_broker_execution(
                ensure_member_full_config(), plugged,
            ).machine.events.len(),
            x0_adapter_broker_map(adapter_wal_map, plugged.machine),
        ),
        index <= adapter.events.len(),
    ensures x0_contextual_prefix_at(
        request,
        initial_members,
        adapter,
        protected,
        context,
        plugged,
        adapter_wal_map,
        index,
    ),
{
    let cfg = ensure_member_full_config();
    let wal = plugged.machine;
    let target = t4_layer::canonical_plugged_broker_execution(cfg, plugged);
    let wal_broker_map = t4_c0_layer::canonical_composed_map(wal);
    let combined = x0_adapter_broker_map(adapter_wal_map, wal);
    assert(p0_a1_wal_coupled(adapter, wal, adapter_wal_map));
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
    assert(t2_layer::weak_index_shape(
        adapter.events.len(), target.machine.events.len(), combined,
    ));
    assert(t4_layer::mapped_context_states_equal(
        plugged, target, wal_broker_map,
    ));
    assert(t4_layer::mapped_context_views_equal(
        cfg, plugged, target, wal_broker_map,
    ));
    assert(t4_c0_layer::mapped_prefixes_t1_safe(
        cfg, wal, target.machine, wal_broker_map,
    ));
    let wal_point = adapter_wal_map.points[index as int];
    let broker_point = combined.points[index as int];
    t4_c0_layer::weak_index_point_bounded(
        adapter.events.len(), wal.events.len(), adapter_wal_map, index,
    );
    t4_c0_layer::weak_index_point_bounded(
        wal.events.len(),
        target.machine.events.len(),
        wal_broker_map,
        wal_point,
    );
    t4_c0_layer::weak_index_point_bounded(
        adapter.events.len(),
        target.machine.events.len(),
        combined,
        index,
    );
    t4_c0_layer::compose_index_map_point(
        adapter_wal_map, wal_broker_map, index,
    );
    assert(broker_point == wal_broker_map.points[wal_point as int]);
    assert(p0_prefix_product_at(
        request,
        initial_members,
        adapter,
        protected,
        wal,
        adapter_wal_map,
        index,
    ));
    p0_effect_agreement_grounds_external_run(
        adapter.configs[index as int],
        protected.configs[index as int],
    );
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
    assert(plugged.contexts[wal_point as int]
        == target.contexts[broker_point as int]);
    assert(t4_c1_layer::wal_context_view_at(
        cfg, wal, wal_point,
    ) == t4_c1_layer::broker_context_view_at(
        cfg, target.machine, broker_point,
    ));
    assert(t1_layer::t1_parameterized_safety_statement(
        cfg,
        execution_layer::execution_prefix(target.machine, broker_point),
    ));
}

pub proof fn x0_composed_map_has_weak_shape<S>(
    adapter: A1AdapterExecution,
    context: t4_c1_layer::ProgramContext<S>,
    plugged: t4_c1_layer::PluggedWalExecution<S>,
    adapter_wal_map: t2_layer::WeakIndexMap,
)
    requires
        p0_a1_wal_coupled(
            adapter, plugged.machine, adapter_wal_map,
        ),
        t4_layer::t4_c2_statement(
            ensure_member_full_config(),
            context,
            plugged,
        ),
    ensures t2_layer::weak_index_shape(
        adapter.events.len(),
        t4_layer::canonical_plugged_broker_execution(
            ensure_member_full_config(), plugged,
        ).machine.events.len(),
        x0_adapter_broker_map(adapter_wal_map, plugged.machine),
    ),
{
    let cfg = ensure_member_full_config();
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

pub proof fn x0_every_adapter_prefix_is_contextually_related<S>(
    request: replay_layer::RequestId,
    initial_members: ISet<config_layer::Resource>,
    adapter: A1AdapterExecution,
    protected: M0ProtectedExecution,
    context: t4_c1_layer::ProgramContext<S>,
    plugged: t4_c1_layer::PluggedWalExecution<S>,
    adapter_wal_map: t2_layer::WeakIndexMap,
)
    requires
        t4_c1_layer::plugged_wal_exec(
            ensure_member_full_config(), context, plugged,
        ),
        p0_prefix_product(
            request,
            initial_members,
            adapter,
            protected,
            plugged.machine,
            adapter_wal_map,
        ),
        t4_layer::t4_c2_statement(
            ensure_member_full_config(), context, plugged,
        ),
        t2_layer::weak_index_shape(
            adapter.events.len(),
            t4_layer::canonical_plugged_broker_execution(
                ensure_member_full_config(), plugged,
            ).machine.events.len(),
            x0_adapter_broker_map(adapter_wal_map, plugged.machine),
        ),
    ensures forall|index: nat| index <= adapter.events.len() ==>
        #[trigger] x0_contextual_prefix_at(
            request,
            initial_members,
            adapter,
            protected,
            context,
            plugged,
            adapter_wal_map,
            index,
        ),
{
    assert forall|index: nat| index <= adapter.events.len() implies
        #[trigger] x0_contextual_prefix_at(
            request,
            initial_members,
            adapter,
            protected,
            context,
            plugged,
            adapter_wal_map,
            index,
        ) by {
        x0_contextual_prefix_from_products(
            request,
            initial_members,
            adapter,
            protected,
            context,
            plugged,
            adapter_wal_map,
            index,
        );
    }
}

pub proof fn x0_ensure_member_contextual_replacement<S>(
    context: t4_c1_layer::ProgramContext<S>,
    plugged: t4_c1_layer::PluggedWalExecution<S>,
)
    requires
        t4_c1_layer::storage_parametric_context(
            ensure_member_full_config(), context,
        ),
        t4_c1_layer::plugged_wal_exec(
            ensure_member_full_config(), context, plugged,
        ),
    ensures t4_layer::t4_c2_statement(
        ensure_member_full_config(), context, plugged,
    ),
{
    ensure_member_full_config_is_well_formed();
    t1_layer::paper_broker_config_is_broker(ensure_member_paper());
    assert(t1_layer::paper_broker_config(ensure_member_paper())
        == ensure_member_full_config());
    x0_contextual_wal_final_representation(
        ensure_member_paper(), context, plugged,
    );
}

pub proof fn x0_p0_and_context_derive_product<S>(
    request: replay_layer::RequestId,
    initial_members: ISet<config_layer::Resource>,
    adapter: A1AdapterExecution,
    protected: M0ProtectedExecution,
    context: t4_c1_layer::ProgramContext<S>,
    plugged: t4_c1_layer::PluggedWalExecution<S>,
    adapter_wal_map: t2_layer::WeakIndexMap,
)
    requires
        t4_c1_layer::storage_parametric_context(
            ensure_member_full_config(), context,
        ),
        t4_c1_layer::plugged_wal_exec(
            ensure_member_full_config(), context, plugged,
        ),
        p0_prefix_product(
            request,
            initial_members,
            adapter,
            protected,
            plugged.machine,
            adapter_wal_map,
        ),
        t4_layer::t4_c2_statement(
            ensure_member_full_config(), context, plugged,
        ),
    ensures x0_contextual_product(
        request,
        initial_members,
        adapter,
        protected,
        context,
        plugged,
        adapter_wal_map,
    ),
{
    x0_composed_map_has_weak_shape(
        adapter, context, plugged, adapter_wal_map,
    );
    x0_every_adapter_prefix_is_contextually_related(
        request,
        initial_members,
        adapter,
        protected,
        context,
        plugged,
        adapter_wal_map,
    );
    reveal(x0_contextual_product);
}

pub proof fn x0_lift_p0_through_context<S>(
    request: replay_layer::RequestId,
    initial_members: ISet<config_layer::Resource>,
    adapter: A1AdapterExecution,
    protected: M0ProtectedExecution,
    context: t4_c1_layer::ProgramContext<S>,
    plugged: t4_c1_layer::PluggedWalExecution<S>,
    adapter_wal_map: t2_layer::WeakIndexMap,
)
    requires
        t4_c1_layer::storage_parametric_context(
            ensure_member_full_config(), context,
        ),
        t4_c1_layer::plugged_wal_exec(
            ensure_member_full_config(), context, plugged,
        ),
        p0_prefix_product(
            request,
            initial_members,
            adapter,
            protected,
            plugged.machine,
            adapter_wal_map,
        ),
    ensures x0_contextual_product(
        request,
        initial_members,
        adapter,
        protected,
        context,
        plugged,
        adapter_wal_map,
    ),
{
    x0_ensure_member_contextual_replacement(context, plugged);
    x0_p0_and_context_derive_product(
        request,
        initial_members,
        adapter,
        protected,
        context,
        plugged,
        adapter_wal_map,
    );
}

pub proof fn x0_p0_terminal_semantics_and_mediation(
    request: replay_layer::RequestId,
    initial_members: ISet<config_layer::Resource>,
    adapter: A1AdapterExecution,
    protected: M0ProtectedExecution,
    wal: wal_runtime_layer::WalExecution,
    adapter_wal_map: t2_layer::WeakIndexMap,
    outcome: TerminalOutcome,
)
    requires
        p0_prefix_product(
            request,
            initial_members,
            adapter,
            protected,
            wal,
            adapter_wal_map,
        ),
        terminal(wal.events, request) == Option::Some(outcome),
    ensures {
        let final_adapter = adapter.configs[adapter.events.len() as int];
        let final_protected = protected.configs[
            protected.events.len() as int
        ];
        let run = a1_external_run(final_adapter);
        let accepted = m0_erase_calls(final_protected.calls);
        &&& t1_layer::paper_config_wf(ensure_member_paper())
        &&& adapter_verified(ensure_member_paper())
        &&& adapter_rely(
            ensure_member_paper(), wal.events, request, run,
        )
        &&& refines(
            ensure_member_paper(),
            request,
            projection_layer::pi_adapter(wal.events, request),
            run,
            outcome,
        )
        &&& per_request_effect_refinement(
            ensure_member_paper(), wal.events, request, run,
        )
        &&& p0_effect_state_agreement(final_adapter, final_protected)
        &&& x0_external_run_matches_protected(
            final_adapter, final_protected,
        )
        &&& projection_layer::complete_mediation(wal.events, accepted)
        &&& m0_every_linearization_durably_authorized(
            ensure_member_full_config(), wal, protected,
        )
    },
{
    let cfg = ensure_member_full_config();
    let final_adapter = adapter.configs[adapter.events.len() as int];
    let final_protected = protected.configs[protected.events.len() as int];
    let accepted = m0_erase_calls(final_protected.calls);
    assert(p0_execution_pair(
        request,
        initial_members,
        adapter,
        protected,
        wal,
        adapter_wal_map,
    ));
    assert(m0_coupled_exec(
        request, initial_members, adapter, protected,
    ));
    assert(a1_exec(request, initial_members, adapter));
    assert(wal_runtime_layer::exec(cfg, wal));
    p0_a1_wal_final_trace_agreement(adapter, wal, adapter_wal_map);
    assert(a1_global_trace(adapter.events) == wal.events);
    ensure_member_full_config_is_well_formed();
    ensure_member_adapter_is_verified();
    ensure_member_executable_wal_terminal_refines(
        request, initial_members, adapter, wal, outcome,
    );
    p0_coupled_final_effect_state_agreement(
        request, initial_members, adapter, protected,
    );
    p0_effect_agreement_grounds_external_run(
        final_adapter, final_protected,
    );
    m0_coupled_exec_derives_complete_mediation(
        request, initial_members, adapter, protected,
    );
    assert(projection_layer::complete_mediation(wal.events, accepted));
    assert(m0_deployment_exec(
        cfg, request, initial_members, adapter, protected, wal,
    ));
    m0_deployment_derives_authorized_linearizations(
        cfg, request, initial_members, adapter, protected, wal,
    );
}

pub proof fn x0_wal_terminal_evidence_from_representation<X, I>(
    paper: t1_layer::PaperConfig<Adapter<X, I>>,
    wal: wal_runtime_layer::WalExecution,
    broker: p0_layer::State,
    request: replay_layer::RequestId,
    run: ExternalRun<X, I>,
    outcome: TerminalOutcome,
)
    requires
        t1_layer::paper_config_wf(paper),
        wal_runtime_layer::exec(
            t1_layer::paper_broker_config(paper), wal,
        ),
        wal_trace_layer::admissible_wal_trace(
            t1_layer::paper_broker_config(paper), wal,
        ),
        wal_trace_layer::trace_agreement(
            t1_layer::paper_broker_config(paper), wal,
        ),
        t4_c0_layer::wal_broker_representation(
            t1_layer::paper_broker_config(paper),
            wal.configs[wal.events.len() as int],
            broker,
        ),
        adapter_rely(paper, wal.events, request, run),
        terminal(wal.events, request) == Option::Some(outcome),
    ensures terminal_evidence_and_compatibility(
        t1_layer::paper_broker_config(paper),
        wal.events,
        wal.configs[wal.events.len() as int].evidence.records,
        request,
        outcome,
    ),
{
    t6_s0_layer::wal_terminal_outcome_has_evidence_and_is_compatible(
        paper,
        wal,
        broker,
        request,
        run,
        outcome,
    );
}

pub proof fn x0_projection_transports_complete_mediation(
    source: Seq<global_layer::GlobalEvent>,
    target: Seq<global_layer::GlobalEvent>,
    accepted: Seq<projection_layer::ProtectedInvocation>,
)
    requires
        t4_c0_layer::t4_projection_agreement(source, target),
        projection_layer::complete_mediation(source, accepted),
    ensures projection_layer::complete_mediation(target, accepted),
{
    assert(t4_c0_layer::t4_projection_agreement(
        source, target,
    ));
    assert(projection_layer::pi_physical(source)
        == projection_layer::pi_physical(target));
    assert(projection_layer::pi_invocations(source)
        == projection_layer::pi_invocations(target));
}

pub proof fn x0_ensure_member_single_request<S>(
    request: replay_layer::RequestId,
    initial_members: ISet<config_layer::Resource>,
    adapter: A1AdapterExecution,
    protected: M0ProtectedExecution,
    context: t4_c1_layer::ProgramContext<S>,
    plugged: t4_c1_layer::PluggedWalExecution<S>,
    adapter_wal_map: t2_layer::WeakIndexMap,
    outcome: TerminalOutcome,
)
    requires
        t4_c1_layer::storage_parametric_context(
            ensure_member_full_config(), context,
        ),
        t4_c1_layer::plugged_wal_exec(
            ensure_member_full_config(), context, plugged,
        ),
        p0_prefix_product(
            request,
            initial_members,
            adapter,
            protected,
            plugged.machine,
            adapter_wal_map,
        ),
        terminal(plugged.machine.events, request)
            == Option::Some(outcome),
    ensures x0_single_request_end_to_end(
        request,
        initial_members,
        adapter,
        protected,
        context,
        plugged,
        adapter_wal_map,
    ),
{
    x0_p0_terminal_semantics_and_mediation(
        request,
        initial_members,
        adapter,
        protected,
        plugged.machine,
        adapter_wal_map,
        outcome,
    );
    x0_lift_p0_through_context(
        request,
        initial_members,
        adapter,
        protected,
        context,
        plugged,
        adapter_wal_map,
    );
}

pub proof fn x0_ensure_member_source_terminal<S>(
    request: replay_layer::RequestId,
    initial_members: ISet<config_layer::Resource>,
    adapter: A1AdapterExecution,
    protected: M0ProtectedExecution,
    context: t4_c1_layer::ProgramContext<S>,
    plugged: t4_c1_layer::PluggedWalExecution<S>,
    adapter_wal_map: t2_layer::WeakIndexMap,
    outcome: TerminalOutcome,
)
    requires
        t4_c1_layer::storage_parametric_context(
            ensure_member_full_config(), context,
        ),
        t4_c1_layer::plugged_wal_exec(
            ensure_member_full_config(), context, plugged,
        ),
        p0_prefix_product(
            request,
            initial_members,
            adapter,
            protected,
            plugged.machine,
            adapter_wal_map,
        ),
        terminal(plugged.machine.events, request)
            == Option::Some(outcome),
    ensures x0_ensure_member_source_terminal_statement(
        request, adapter, protected, plugged.machine, outcome,
    ),
{
    let wal = plugged.machine;
    let final_adapter = adapter.configs[adapter.events.len() as int];
    let run = a1_external_run(final_adapter);
    let target = t4_layer::canonical_plugged_broker_execution(
        ensure_member_full_config(), plugged,
    );
    x0_p0_terminal_semantics_and_mediation(
        request,
        initial_members,
        adapter,
        protected,
        wal,
        adapter_wal_map,
        outcome,
    );
    ensure_member_full_config_is_well_formed();
    t1_layer::paper_broker_config_is_broker(ensure_member_paper());
    assert(t1_layer::paper_broker_config(ensure_member_paper())
        == ensure_member_full_config());
    x0_contextual_wal_final_representation(
        ensure_member_paper(), context, plugged,
    );
    x0_wal_terminal_evidence_from_representation(
        ensure_member_paper(),
        wal,
        target.machine.configs[target.machine.events.len() as int],
        request,
        run,
        outcome,
    );
    reveal(x0_ensure_member_source_terminal_statement);
}

pub proof fn x0_ensure_member_target_terminal<S>(
    request: replay_layer::RequestId,
    initial_members: ISet<config_layer::Resource>,
    adapter: A1AdapterExecution,
    protected: M0ProtectedExecution,
    context: t4_c1_layer::ProgramContext<S>,
    plugged: t4_c1_layer::PluggedWalExecution<S>,
    adapter_wal_map: t2_layer::WeakIndexMap,
    outcome: TerminalOutcome,
)
    requires
        t4_c1_layer::storage_parametric_context(
            ensure_member_full_config(), context,
        ),
        t4_c1_layer::plugged_wal_exec(
            ensure_member_full_config(), context, plugged,
        ),
        p0_prefix_product(
            request,
            initial_members,
            adapter,
            protected,
            plugged.machine,
            adapter_wal_map,
        ),
        terminal(plugged.machine.events, request)
            == Option::Some(outcome),
    ensures x0_ensure_member_target_terminal_statement(
        request, adapter, protected, plugged, outcome,
    ),
{
    let wal = plugged.machine;
    let final_adapter = adapter.configs[adapter.events.len() as int];
    let final_protected = protected.configs[protected.events.len() as int];
    let run = a1_external_run(final_adapter);
    let accepted = m0_erase_calls(final_protected.calls);
    let target = t4_layer::canonical_plugged_broker_execution(
        ensure_member_full_config(), plugged,
    );
    x0_p0_terminal_semantics_and_mediation(
        request,
        initial_members,
        adapter,
        protected,
        wal,
        adapter_wal_map,
        outcome,
    );
    ensure_member_full_config_is_well_formed();
    t1_layer::paper_broker_config_is_broker(ensure_member_paper());
    assert(t1_layer::paper_broker_config(ensure_member_paper())
        == ensure_member_full_config());
    x0_contextual_broker_terminal_outcome_refines(
        ensure_member_paper(), context, plugged, request, run, outcome,
    );
    assert(t4_c0_layer::t4_projection_agreement(
        wal.events, target.machine.events,
    ));
    x0_projection_transports_complete_mediation(
        wal.events, target.machine.events, accepted,
    );
    reveal(x0_ensure_member_target_terminal_statement);
}

pub proof fn t6_x0_ensure_member_terminal_end_to_end<S>(
    request: replay_layer::RequestId,
    initial_members: ISet<config_layer::Resource>,
    adapter: A1AdapterExecution,
    protected: M0ProtectedExecution,
    context: t4_c1_layer::ProgramContext<S>,
    plugged: t4_c1_layer::PluggedWalExecution<S>,
    adapter_wal_map: t2_layer::WeakIndexMap,
    outcome: TerminalOutcome,
)
    requires
        t4_c1_layer::storage_parametric_context(
            ensure_member_full_config(), context,
        ),
        t4_c1_layer::plugged_wal_exec(
            ensure_member_full_config(), context, plugged,
        ),
        p0_prefix_product(
            request,
            initial_members,
            adapter,
            protected,
            plugged.machine,
            adapter_wal_map,
        ),
        terminal(plugged.machine.events, request)
            == Option::Some(outcome),
    ensures x0_ensure_member_terminal_statement(
        request,
        initial_members,
        adapter,
        protected,
        context,
        plugged,
        adapter_wal_map,
        outcome,
    ),
{
    x0_ensure_member_single_request(
        request,
        initial_members,
        adapter,
        protected,
        context,
        plugged,
        adapter_wal_map,
        outcome,
    );
    x0_ensure_member_source_terminal(
        request,
        initial_members,
        adapter,
        protected,
        context,
        plugged,
        adapter_wal_map,
        outcome,
    );
    x0_ensure_member_target_terminal(
        request,
        initial_members,
        adapter,
        protected,
        context,
        plugged,
        adapter_wal_map,
        outcome,
    );
    reveal(x0_ensure_member_terminal_statement);
}

pub closed spec fn x0_executable_crash_retry_package(
    adapter: A1AdapterExecution,
    protected: M0ProtectedExecution,
    plugged: t4_c1_layer::PluggedWalExecution<M0ProtectedHandleState>,
    adapter_wal_map: t2_layer::WeakIndexMap,
) -> bool {
    let cfg = ensure_member_full_config();
    let request = ensure_member_request_zero();
    let initial = ISet::<config_layer::Resource>::empty();
    let wal = plugged.machine;
    let context = m0_exclusive_handle_context(cfg);
    let target = t4_layer::canonical_plugged_broker_execution(cfg, plugged);
    if adapter.events.len() < adapter.configs.len()
        && protected.events.len() < protected.configs.len()
    {
        let final_adapter = adapter.configs[adapter.events.len() as int];
        let final_protected = protected.configs[
            protected.events.len() as int
        ];
        let run = a1_external_run(final_adapter);
        let accepted = m0_erase_calls(final_protected.calls);
        &&& adapter == a1_retry_adapter_execution()
        &&& protected == m0_retry_protected_execution()
        &&& plugged == m0_plugged_wal_execution(
            a1_retry_wal_execution(),
        )
        &&& adapter_wal_map == p0_canonical_index_map(adapter.events)
        &&& x0_ensure_member_terminal_statement(
            request,
            initial,
            adapter,
            protected,
            context,
            plugged,
            adapter_wal_map,
            a1_retry_outcome(),
        )
        &&& t4_layer::t4_c2_statement(cfg, context, plugged)
        &&& t2_layer::weak_index_shape(
            adapter.events.len(),
            target.machine.events.len(),
            x0_adapter_broker_map(adapter_wal_map, wal),
        )
        &&& adapter.events.len() == 32
        &&& protected.events.len() == 32
        &&& wal.events.len() == 31
        &&& terminal(target.machine.events, request)
            == Option::Some(a1_retry_outcome())
        &&& refines(
            ensure_member_paper(),
            request,
            projection_layer::pi_adapter(
                target.machine.events, request,
            ),
            run,
            a1_retry_outcome(),
        )
        &&& (ensure_member_paper().adapter.one_effect)(request, run)
        &&& !(ensure_member_paper().adapter.zero_effect)(request, run)
        &&& m0_linearization_count(protected.events) == 1
        &&& final_protected.members.contains(
            ensure_member_target(request),
        )
        &&& projection_layer::complete_mediation(
            wal.events, accepted,
        )
        &&& target.contexts[
            target.machine.events.len() as int
        ].invocations == accepted
        &&& projection_layer::complete_mediation(
            target.machine.events, accepted,
        )
        &&& m0_every_linearization_durably_authorized(
            cfg, wal, protected,
        )
    } else {
        false
    }
}

pub proof fn t6_x0_executable_crash_retry_end_to_end()
    ensures x0_executable_crash_retry_package(
        a1_retry_adapter_execution(),
        m0_retry_protected_execution(),
        m0_plugged_wal_execution(a1_retry_wal_execution()),
        p0_canonical_index_map(a1_retry_adapter_execution().events),
    ),
{
    let cfg = ensure_member_full_config();
    let request = ensure_member_request_zero();
    let initial = ISet::<config_layer::Resource>::empty();
    let adapter = a1_retry_adapter_execution();
    let protected = m0_retry_protected_execution();
    let wal = a1_retry_wal_execution();
    let plugged = m0_plugged_wal_execution(wal);
    let context = m0_exclusive_handle_context(cfg);
    let map = p0_canonical_index_map(adapter.events);
    let final_protected = protected.configs[protected.events.len() as int];
    let accepted = m0_erase_calls(final_protected.calls);
    let target = t4_layer::canonical_plugged_broker_execution(cfg, plugged);
    a1_concrete_executable_retry_package();
    t6_m0_executable_crash_retry_mediation();
    t6_p0_executable_crash_retry_prefix_product();
    assert(t4_c1_layer::storage_parametric_context(cfg, context));
    assert(t4_c1_layer::plugged_wal_exec(cfg, context, plugged));
    assert(p0_prefix_product(
        request, initial, adapter, protected, wal, map,
    ));
    assert(terminal(wal.events, request)
        == Option::Some(a1_retry_outcome()));
    t6_x0_ensure_member_terminal_end_to_end(
        request,
        initial,
        adapter,
        protected,
        context,
        plugged,
        map,
        a1_retry_outcome(),
    );
    x0_ensure_member_contextual_replacement(context, plugged);
    x0_composed_map_has_weak_shape(adapter, context, plugged, map);
    assert(accepted
        == plugged.contexts[wal.events.len() as int].invocations);
    x0_exclusive_context_endpoint_mediation(plugged, accepted);
    reveal(x0_ensure_member_terminal_statement);
    reveal(x0_ensure_member_target_terminal_statement);
    reveal(x0_executable_crash_retry_package);
}

pub proof fn t6_x0_contextual_end_to_end_nonvacuity()
    ensures exists|
        adapter: A1AdapterExecution,
        protected: M0ProtectedExecution,
        plugged: t4_c1_layer::PluggedWalExecution<
            M0ProtectedHandleState,
        >,
        adapter_wal_map: t2_layer::WeakIndexMap,
    | #![auto] {
        &&& adapter == a1_retry_adapter_execution()
        &&& protected == m0_retry_protected_execution()
        &&& plugged == m0_plugged_wal_execution(
            a1_retry_wal_execution(),
        )
        &&& adapter_wal_map
            == p0_canonical_index_map(adapter.events)
        &&& x0_executable_crash_retry_package(
            adapter, protected, plugged, adapter_wal_map,
        )
    },
{
    t6_x0_executable_crash_retry_end_to_end();
    assert(exists|
        adapter: A1AdapterExecution,
        protected: M0ProtectedExecution,
        plugged: t4_c1_layer::PluggedWalExecution<
            M0ProtectedHandleState,
        >,
        adapter_wal_map: t2_layer::WeakIndexMap,
    | #![auto] {
        &&& adapter == a1_retry_adapter_execution()
        &&& protected == m0_retry_protected_execution()
        &&& plugged == m0_plugged_wal_execution(
            a1_retry_wal_execution(),
        )
        &&& adapter_wal_map
            == p0_canonical_index_map(adapter.events)
        &&& x0_executable_crash_retry_package(
            adapter, protected, plugged, adapter_wal_map,
        )
    }) by {
        let adapter = a1_retry_adapter_execution();
        let protected = m0_retry_protected_execution();
        let plugged = m0_plugged_wal_execution(
            a1_retry_wal_execution(),
        );
        let adapter_wal_map = p0_canonical_index_map(adapter.events);
    }
}

} // verus!
