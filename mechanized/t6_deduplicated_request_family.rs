use vstd::prelude::*;

#[path = "t6_deduplicated_contextual.rs"]
pub mod t6_dd4_layer;

verus! {

use t6_dd4_layer::*;
use t6_dd4_layer::t6_dd3_layer;
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

// T6-DD5 makes the operational/protected premise request-indexed. A family
// member is required for every request that is terminal in the shared WAL.

pub struct DD5OperationalMember {
    pub initial_slot: Option<replay_layer::Value>,
    pub stable_key: replay_layer::StableKey,
    pub adapter: DDAdapterExecution,
    pub protected: DD3ProtectedExecution,
}

pub struct DD5RequestFamily {
    pub member: spec_fn(
        replay_layer::RequestId,
    ) -> DD5OperationalMember,
}

pub open spec fn dd5_member_run(
    member: DD5OperationalMember,
) -> ExternalRun<Option<replay_layer::Value>, DedupWitness> {
    dd_external_run(
        member.adapter.configs[member.adapter.events.len() as int],
    )
}

pub open spec fn dd5_member_accepted(
    member: DD5OperationalMember,
) -> Seq<projection_layer::ProtectedInvocation> {
    dd3_erase_calls(
        member.protected.configs[
            member.protected.events.len() as int
        ].calls,
    )
}

pub open spec fn dd5_operational_member_valid(
    request: replay_layer::RequestId,
    wal: wal_runtime_layer::WalExecution,
    member: DD5OperationalMember,
) -> bool {
    &&& dd_full_config().request[request].stable_key
        == Option::Some(member.stable_key)
    &&& dd3_coupled_exec(
        request,
        member.stable_key,
        member.initial_slot,
        member.adapter,
        member.protected,
    )
    &&& dd_global_trace(member.adapter.events) == wal.events
}

pub open spec fn dd5_family_covers_terminal_requests(
    wal: wal_runtime_layer::WalExecution,
    family: DD5RequestFamily,
) -> bool {
    forall|request: replay_layer::RequestId|
        terminal(wal.events, request).is_some() ==>
        #[trigger] dd5_operational_member_valid(
            request, wal, (family.member)(request),
        )
}

pub proof fn dd5_member_derives_prefix_product_and_rely(
    request: replay_layer::RequestId,
    wal: wal_runtime_layer::WalExecution,
    member: DD5OperationalMember,
)
    requires
        wal_runtime_layer::exec(dd_full_config(), wal),
        dd5_operational_member_valid(request, wal, member),
    ensures
        dd4_prefix_product(
            request,
            member.stable_key,
            member.initial_slot,
            member.adapter,
            member.protected,
            wal,
            dd4_canonical_index_map(member.adapter.events),
        ),
        adapter_rely(
            dd_paper(), wal.events, request, dd5_member_run(member),
        ),
        projection_layer::complete_mediation(
            wal.events, dd5_member_accepted(member),
        ),
{
    let adapter = member.adapter;
    let protected = member.protected;
    let map = dd4_canonical_index_map(adapter.events);
    assert(dd_exec(request, member.initial_slot, adapter));
    dd1_exec_derives_adapter_rely(
        request, member.initial_slot, adapter,
    );
    assert(dd_global_trace(adapter.events) == wal.events);
    assert(adapter_rely(
        dd_paper(), wal.events, request, dd5_member_run(member),
    ));
    dd4_canonical_map_couples_trace_equal_execution(adapter, wal);
    assert(dd4_execution_pair(
        request,
        member.stable_key,
        member.initial_slot,
        adapter,
        protected,
        wal,
        map,
    ));
    dd4_execution_pair_derives_prefix_product(
        request,
        member.stable_key,
        member.initial_slot,
        adapter,
        protected,
        wal,
        map,
    );
    dd3_coupled_exec_derives_complete_mediation(
        request,
        member.stable_key,
        member.initial_slot,
        adapter,
        protected,
    );
    assert(dd5_member_accepted(member)
        == projection_layer::pi_invocations(wal.events));
}

pub open spec fn dd5_terminal_member_statement<S>(
    context: t4_c1_layer::ProgramContext<S>,
    plugged: t4_c1_layer::PluggedWalExecution<S>,
    family: DD5RequestFamily,
    request: replay_layer::RequestId,
    outcome: TerminalOutcome,
) -> bool {
    let member = (family.member)(request);
    let run = dd5_member_run(member);
    let accepted = dd5_member_accepted(member);
    let target = t4_layer::canonical_plugged_broker_execution(
        dd_full_config(), plugged,
    );
    &&& dd5_operational_member_valid(request, plugged.machine, member)
    &&& dd4_prefix_product(
        request,
        member.stable_key,
        member.initial_slot,
        member.adapter,
        member.protected,
        plugged.machine,
        dd4_canonical_index_map(member.adapter.events),
    )
    &&& terminal(plugged.machine.events, request) == Option::Some(outcome)
    &&& refines(
        dd_paper(),
        request,
        projection_layer::pi_adapter(plugged.machine.events, request),
        run,
        outcome,
    )
    &&& per_request_effect_refinement(
        dd_paper(), plugged.machine.events, request, run,
    )
    &&& projection_layer::complete_mediation(
        plugged.machine.events, accepted,
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
    &&& projection_layer::complete_mediation(
        target.machine.events, accepted,
    )
}

pub open spec fn dd5_request_family_contextual_statement<S>(
    context: t4_c1_layer::ProgramContext<S>,
    plugged: t4_c1_layer::PluggedWalExecution<S>,
    family: DD5RequestFamily,
) -> bool {
    &&& t4_layer::t4_c2_statement(
        dd_full_config(), context, plugged,
    )
    &&& forall|
        request: replay_layer::RequestId,
        outcome: TerminalOutcome,
    | terminal(plugged.machine.events, request) == Option::Some(outcome) ==>
        #[trigger] dd5_terminal_member_statement(
            context, plugged, family, request, outcome,
        )
}

pub proof fn dd5_request_family_contextual_refinement<S>(
    context: t4_c1_layer::ProgramContext<S>,
    plugged: t4_c1_layer::PluggedWalExecution<S>,
    family: DD5RequestFamily,
)
    requires
        t4_c1_layer::storage_parametric_context(
            dd_full_config(), context,
        ),
        t4_c1_layer::plugged_wal_exec(
            dd_full_config(), context, plugged,
        ),
        dd5_family_covers_terminal_requests(plugged.machine, family),
    ensures dd5_request_family_contextual_statement(
        context, plugged, family,
    ),
{
    let cfg = dd_full_config();
    let wal = plugged.machine;
    let target = t4_layer::canonical_plugged_broker_execution(cfg, plugged);
    dd_full_config_is_well_formed();
    dd_adapter_is_verified();
    t1_layer::paper_broker_config_is_broker(dd_paper());
    assert(t1_layer::paper_broker_config(dd_paper()) == cfg);
    t4_layer::t4_c2_contextual_replacement(
        dd_paper(), context, plugged,
    );
    assert forall|
        request: replay_layer::RequestId,
        outcome: TerminalOutcome,
    | terminal(wal.events, request) == Option::Some(outcome) implies
        #[trigger] dd5_terminal_member_statement(
            context, plugged, family, request, outcome,
        ) by {
        let member = (family.member)(request);
        let run = dd5_member_run(member);
        let accepted = dd5_member_accepted(member);
        assert(dd5_operational_member_valid(request, wal, member));
        assert(wal_runtime_layer::exec(cfg, wal));
        dd5_member_derives_prefix_product_and_rely(
            request, wal, member,
        );
        x0_contextual_terminal_outcome_refines(
            dd_paper(), context, plugged, request, run, outcome,
        );
        x0_contextual_broker_terminal_outcome_refines(
            dd_paper(), context, plugged, request, run, outcome,
        );
        assert(t4_c0_layer::t4_projection_agreement(
            wal.events, target.machine.events,
        ));
        x0_projection_transports_complete_mediation(
            wal.events, target.machine.events, accepted,
        );
    }
}

pub open spec fn dd5_dd2_member() -> DD5OperationalMember {
    DD5OperationalMember {
        initial_slot: Option::None,
        stable_key: dd2_key(),
        adapter: dd2_adapter_execution(),
        protected: dd3_protected_execution(),
    }
}

pub open spec fn dd5_dd2_family() -> DD5RequestFamily {
    DD5RequestFamily {
        member: |_request: replay_layer::RequestId| dd5_dd2_member(),
    }
}

pub proof fn dd5_dd2_terminal_request_is_zero(
    request: replay_layer::RequestId,
    outcome: TerminalOutcome,
)
    requires terminal(dd2_wal_execution().events, request)
        == Option::Some(outcome),
    ensures
        request == dd_request_zero(),
        outcome == dd2_terminal_outcome(),
{
    let cfg = dd_full_config();
    let wal = dd2_wal_execution();
    dd2_wal_closed_representation();
    dd2_wal_execution_exec();
    assert(wal_trace_layer::trace_agreement_at(
        cfg, wal, wal.events.len(),
    ));
    assert(wal.configs[wal.events.len() as int] == wal.configs.last());
    assert(wal_runtime_layer::journal_view(wal.configs.last())
        == dd2_records());
    assert(wal.events.take(wal.events.len() as int) =~= wal.events);
    assert(wal_trace_layer::prefix_events(wal, wal.events.len())
        =~= wal.events);
    assert(wal_runtime_layer::journal_view(
        wal.configs[wal.events.len() as int],
    ) == projection_layer::pi_journal(wal.events));
    assert(projection_layer::pi_journal(wal.events) == dd2_records());
    if request != dd_request_zero() {
        reveal_with_fuel(replay_layer::terminal_count, 8);
        assert(replay_layer::terminal_count(dd2_records(), request) == 0);
        assert(terminal_record(dd2_records(), request).is_none());
        assert(terminal_from_records(dd2_records(), request).is_none());
        assert(false);
    }
    dd2_wal_terminal_refines();
}

pub proof fn dd5_dd2_family_covers_terminal_requests()
    ensures dd5_family_covers_terminal_requests(
        dd2_wal_execution(), dd5_dd2_family(),
    ),
{
    assert forall|request: replay_layer::RequestId|
        terminal(dd2_wal_execution().events, request).is_some() implies
        #[trigger] dd5_operational_member_valid(
            request,
            dd2_wal_execution(),
            (dd5_dd2_family().member)(request),
        ) by {
        match terminal(dd2_wal_execution().events, request) {
            Option::Some(outcome) => {
                dd5_dd2_terminal_request_is_zero(request, outcome);
                dd3_adapter_and_service_are_coupled();
                dd2_adapter_execution_exec();
                assert(dd_full_config().request[dd_request_zero()].stable_key
                    == Option::Some(dd2_key()));
            },
            Option::None => {},
        }
    }
}

pub closed spec fn dd5_dd2_request_family_package() -> bool {
    let cfg = dd_full_config();
    let wal = dd2_wal_execution();
    let plugged = m0_plugged_wal_execution(wal);
    let context = m0_exclusive_handle_context(cfg);
    let family = dd5_dd2_family();
    &&& dd5_family_covers_terminal_requests(wal, family)
    &&& dd5_request_family_contextual_statement(
        context, plugged, family,
    )
    &&& forall|
        request: replay_layer::RequestId,
        outcome: TerminalOutcome,
    | terminal(wal.events, request) == Option::Some(outcome) ==> {
        &&& request == dd_request_zero()
        &&& outcome == dd2_terminal_outcome()
    }
    &&& dd4_contextual_end_to_end_package()
}

pub proof fn t6_dd5_request_indexed_contextual_refinement()
    ensures dd5_dd2_request_family_package(),
{
    let cfg = dd_full_config();
    let wal = dd2_wal_execution();
    let plugged = m0_plugged_wal_execution(wal);
    let context = m0_exclusive_handle_context(cfg);
    let family = dd5_dd2_family();
    dd5_dd2_family_covers_terminal_requests();
    dd4_concrete_context_inputs();
    dd5_request_family_contextual_refinement(
        context, plugged, family,
    );
    assert forall|
        request: replay_layer::RequestId,
        outcome: TerminalOutcome,
    | terminal(wal.events, request) == Option::Some(outcome) implies {
        &&& request == dd_request_zero()
        &&& outcome == dd2_terminal_outcome()
    } by {
        dd5_dd2_terminal_request_is_zero(request, outcome);
    }
    t6_dd4_deduplicated_contextual_end_to_end();
    reveal(dd5_dd2_request_family_package);
}

pub proof fn t6_dd5_request_family_nonvacuity()
    ensures exists|family: DD5RequestFamily| #![auto] {
        &&& family == dd5_dd2_family()
        &&& dd5_family_covers_terminal_requests(
            dd2_wal_execution(), family,
        )
        &&& dd5_dd2_request_family_package()
    },
{
    t6_dd5_request_indexed_contextual_refinement();
    assert(exists|family: DD5RequestFamily| #![auto] {
        &&& family == dd5_dd2_family()
        &&& dd5_family_covers_terminal_requests(
            dd2_wal_execution(), family,
        )
        &&& dd5_dd2_request_family_package()
    }) by {
        let family = dd5_dd2_family();
    }
}

} // verus!
