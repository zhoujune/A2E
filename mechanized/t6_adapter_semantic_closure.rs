use vstd::prelude::*;

#[path = "t6_terminal_bridge.rs"]
pub mod t6_s0_layer;

verus! {

use t6_s0_layer::*;
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

// T6-A0 closes the generic semantic implication and then inhabits it with a
// concrete adapter contract and terminal execution.  The core implication
// consumes exactly the frozen T6-S0 conjunction.  Its Event, Journal, and WAL
// wrappers discharge that conjunction from existing execution, trace, and
// representation premises; no new persistence or mediation theorem is added.

pub proof fn terminal_evidence_and_compatibility_imply_refines<X, I>(
    paper: t1_layer::PaperConfig<Adapter<X, I>>,
    events: Seq<global_layer::GlobalEvent>,
    records: Seq<replay_layer::JournalRecord>,
    request: replay_layer::RequestId,
    run: ExternalRun<X, I>,
    outcome: TerminalOutcome,
)
    requires
        adapter_verified(paper),
        replay_layer::journal_legal(
            config_layer::erase_config(
                t1_layer::paper_broker_config(paper),
            ),
            records,
        ),
        adapter_rely(paper, events, request, run),
        terminal_evidence_and_compatibility(
            t1_layer::paper_broker_config(paper),
            events,
            records,
            request,
            outcome,
        ),
    ensures refines(
        paper,
        request,
        projection_layer::pi_adapter(events, request),
        run,
        outcome,
    ),
{
    let cfg = t1_layer::paper_broker_config(paper);
    let history = projection_layer::pi_adapter(events, request);
    t6_d0_layer::adapter_rely_is_projected_rely(
        paper, events, request, run,
    );
    assert(adapter_rely_trace(paper, request, history, run));
    assert(outcome_evidence(
        cfg, records, request, history, outcome,
    ));
    assert(broker_outcome_compatible(
        cfg, records, request, history, outcome,
    ));
    t6_d0_layer::adapter_verified_applies(
        paper, request, records, history, run, outcome,
    );
}

pub proof fn selected_terminal_implies_per_request_refinement<X, I>(
    paper: t1_layer::PaperConfig<Adapter<X, I>>,
    events: Seq<global_layer::GlobalEvent>,
    records: Seq<replay_layer::JournalRecord>,
    request: replay_layer::RequestId,
    run: ExternalRun<X, I>,
    outcome: TerminalOutcome,
)
    requires
        adapter_verified(paper),
        replay_layer::journal_legal(
            config_layer::erase_config(
                t1_layer::paper_broker_config(paper),
            ),
            records,
        ),
        adapter_rely(paper, events, request, run),
        terminal(events, request) == Option::Some(outcome),
        terminal_evidence_and_compatibility(
            t1_layer::paper_broker_config(paper),
            events,
            records,
            request,
            outcome,
        ),
    ensures
        refines(
            paper,
            request,
            projection_layer::pi_adapter(events, request),
            run,
            outcome,
        ),
        per_request_effect_refinement(
            paper, events, request, run,
        ),
{
    terminal_evidence_and_compatibility_imply_refines(
        paper, events, records, request, run, outcome,
    );
}

pub proof fn event_terminal_outcome_refines<X, I>(
    paper: t1_layer::PaperConfig<Adapter<X, I>>,
    events: Seq<global_layer::GlobalEvent>,
    broker: p0_layer::State,
    request: replay_layer::RequestId,
    run: ExternalRun<X, I>,
    outcome: TerminalOutcome,
)
    requires
        t1_layer::paper_config_wf(paper),
        adapter_verified(paper),
        contract_layer::broker_contract_invariant(
            t1_layer::paper_broker_config(paper), broker,
        ),
        broker.core.evidence.records
            == projection_layer::pi_journal(events),
        broker.physical.physical
            == projection_layer::pi_physical(events),
        adapter_rely(paper, events, request, run),
        terminal(events, request) == Option::Some(outcome),
    ensures
        refines(
            paper,
            request,
            projection_layer::pi_adapter(events, request),
            run,
            outcome,
        ),
        per_request_effect_refinement(
            paper, events, request, run,
        ),
{
    let cfg = t1_layer::paper_broker_config(paper);
    t6_s0_layer::event_terminal_outcome_has_evidence_and_is_compatible(
        paper, events, broker, request, run, outcome,
    );
    assert(contract_layer::replay_agreement_clause(cfg, broker));
    selected_terminal_implies_per_request_refinement(
        paper,
        events,
        broker.core.evidence.records,
        request,
        run,
        outcome,
    );
}

pub proof fn event_per_request_effect_refines<X, I>(
    paper: t1_layer::PaperConfig<Adapter<X, I>>,
    events: Seq<global_layer::GlobalEvent>,
    broker: p0_layer::State,
    request: replay_layer::RequestId,
    run: ExternalRun<X, I>,
)
    requires
        t1_layer::paper_config_wf(paper),
        adapter_verified(paper),
        contract_layer::broker_contract_invariant(
            t1_layer::paper_broker_config(paper), broker,
        ),
        broker.core.evidence.records
            == projection_layer::pi_journal(events),
        broker.physical.physical
            == projection_layer::pi_physical(events),
        adapter_rely(paper, events, request, run),
    ensures per_request_effect_refinement(
        paper, events, request, run,
    ),
{
    match terminal(events, request) {
        Option::None => {},
        Option::Some(outcome) => {
            event_terminal_outcome_refines(
                paper, events, broker, request, run, outcome,
            );
        },
    }
}

pub proof fn journal_terminal_outcome_refines<X, I>(
    paper: t1_layer::PaperConfig<Adapter<X, I>>,
    execution: journal_runtime_layer::JournalExecution,
    broker: p0_layer::State,
    request: replay_layer::RequestId,
    run: ExternalRun<X, I>,
    outcome: TerminalOutcome,
)
    requires
        t1_layer::paper_config_wf(paper),
        adapter_verified(paper),
        journal_runtime_layer::exec(
            t1_layer::paper_broker_config(paper), execution,
        ),
        journal_trace_layer::admissible_journal_trace(
            t1_layer::paper_broker_config(paper), execution,
        ),
        journal_trace_layer::trace_agreement(
            t1_layer::paper_broker_config(paper), execution,
        ),
        t2_representation_layer::representation(
            t1_layer::paper_broker_config(paper),
            execution.configs[execution.events.len() as int],
            broker,
        ),
        adapter_rely(paper, execution.events, request, run),
        terminal(execution.events, request) == Option::Some(outcome),
    ensures
        refines(
            paper,
            request,
            projection_layer::pi_adapter(execution.events, request),
            run,
            outcome,
        ),
        per_request_effect_refinement(
            paper, execution.events, request, run,
        ),
{
    let cfg = t1_layer::paper_broker_config(paper);
    let final_state = execution.configs[execution.events.len() as int];
    t6_s0_layer::journal_terminal_outcome_has_evidence_and_is_compatible(
        paper, execution, broker, request, run, outcome,
    );
    assert(t2_representation_layer::broker_ghost_equals(
        broker, final_state.evidence,
    ));
    assert(contract_layer::broker_contract_invariant(cfg, broker));
    assert(contract_layer::replay_agreement_clause(cfg, broker));
    assert(broker.core.evidence.records
        == final_state.evidence.records);
    selected_terminal_implies_per_request_refinement(
        paper,
        execution.events,
        final_state.evidence.records,
        request,
        run,
        outcome,
    );
}

pub proof fn journal_per_request_effect_refines<X, I>(
    paper: t1_layer::PaperConfig<Adapter<X, I>>,
    execution: journal_runtime_layer::JournalExecution,
    broker: p0_layer::State,
    request: replay_layer::RequestId,
    run: ExternalRun<X, I>,
)
    requires
        t1_layer::paper_config_wf(paper),
        adapter_verified(paper),
        journal_runtime_layer::exec(
            t1_layer::paper_broker_config(paper), execution,
        ),
        journal_trace_layer::admissible_journal_trace(
            t1_layer::paper_broker_config(paper), execution,
        ),
        journal_trace_layer::trace_agreement(
            t1_layer::paper_broker_config(paper), execution,
        ),
        t2_representation_layer::representation(
            t1_layer::paper_broker_config(paper),
            execution.configs[execution.events.len() as int],
            broker,
        ),
        adapter_rely(paper, execution.events, request, run),
    ensures per_request_effect_refinement(
        paper, execution.events, request, run,
    ),
{
    match terminal(execution.events, request) {
        Option::None => {},
        Option::Some(outcome) => {
            journal_terminal_outcome_refines(
                paper, execution, broker, request, run, outcome,
            );
        },
    }
}

pub proof fn wal_terminal_outcome_refines<X, I>(
    paper: t1_layer::PaperConfig<Adapter<X, I>>,
    execution: wal_runtime_layer::WalExecution,
    broker: p0_layer::State,
    request: replay_layer::RequestId,
    run: ExternalRun<X, I>,
    outcome: TerminalOutcome,
)
    requires
        t1_layer::paper_config_wf(paper),
        adapter_verified(paper),
        wal_runtime_layer::exec(
            t1_layer::paper_broker_config(paper), execution,
        ),
        wal_trace_layer::admissible_wal_trace(
            t1_layer::paper_broker_config(paper), execution,
        ),
        wal_trace_layer::trace_agreement(
            t1_layer::paper_broker_config(paper), execution,
        ),
        t4_c0_layer::wal_broker_representation(
            t1_layer::paper_broker_config(paper),
            execution.configs[execution.events.len() as int],
            broker,
        ),
        adapter_rely(paper, execution.events, request, run),
        terminal(execution.events, request) == Option::Some(outcome),
    ensures
        refines(
            paper,
            request,
            projection_layer::pi_adapter(execution.events, request),
            run,
            outcome,
        ),
        per_request_effect_refinement(
            paper, execution.events, request, run,
        ),
{
    let cfg = t1_layer::paper_broker_config(paper);
    let final_state = execution.configs[execution.events.len() as int];
    t6_s0_layer::wal_terminal_outcome_has_evidence_and_is_compatible(
        paper, execution, broker, request, run, outcome,
    );
    assert(t2_representation_layer::representation(
        cfg, wal_runtime_layer::journal_projection(final_state), broker,
    ));
    assert(t2_representation_layer::broker_ghost_equals(
        broker,
        wal_runtime_layer::journal_projection(final_state).evidence,
    ));
    assert(wal_runtime_layer::journal_projection(final_state).evidence
        == final_state.evidence);
    assert(contract_layer::broker_contract_invariant(cfg, broker));
    assert(contract_layer::replay_agreement_clause(cfg, broker));
    assert(broker.core.evidence.records
        == final_state.evidence.records);
    selected_terminal_implies_per_request_refinement(
        paper,
        execution.events,
        final_state.evidence.records,
        request,
        run,
        outcome,
    );
}

pub proof fn wal_per_request_effect_refines<X, I>(
    paper: t1_layer::PaperConfig<Adapter<X, I>>,
    execution: wal_runtime_layer::WalExecution,
    broker: p0_layer::State,
    request: replay_layer::RequestId,
    run: ExternalRun<X, I>,
)
    requires
        t1_layer::paper_config_wf(paper),
        adapter_verified(paper),
        wal_runtime_layer::exec(
            t1_layer::paper_broker_config(paper), execution,
        ),
        wal_trace_layer::admissible_wal_trace(
            t1_layer::paper_broker_config(paper), execution,
        ),
        wal_trace_layer::trace_agreement(
            t1_layer::paper_broker_config(paper), execution,
        ),
        t4_c0_layer::wal_broker_representation(
            t1_layer::paper_broker_config(paper),
            execution.configs[execution.events.len() as int],
            broker,
        ),
        adapter_rely(paper, execution.events, request, run),
    ensures per_request_effect_refinement(
        paper, execution.events, request, run,
    ),
{
    match terminal(execution.events, request) {
        Option::None => {},
        Option::Some(outcome) => {
            wal_terminal_outcome_refines(
                paper, execution, broker, request, run, outcome,
            );
        },
    }
}

// -------------------------------------------------------------------------
// A concrete, nontrivial idempotent adapter contract instance.
//
// EnsureMember inserts the request's resource into an external membership
// set.  Environment interference may add other resources, and the witness
// records which invoked attempts are assumed to have linearized at the
// external service.
// This layer verifies consistency and refinement of that semantic contract;
// it does not verify executable adapter or external-service implementation.
// -------------------------------------------------------------------------

pub struct EnsureMemberWitness {
    pub environment_additions: ISet<config_layer::Resource>,
    pub linearized_attempts: ISet<replay_layer::AttemptId>,
}

pub open spec fn ensure_member_target(
    request: replay_layer::RequestId,
) -> config_layer::Resource {
    config_layer::Resource { id: request.id }
}

pub open spec fn ensure_member_baseline_contains(
    run: ExternalRun<
        ISet<config_layer::Resource>, EnsureMemberWitness,
    >,
    resource: config_layer::Resource,
) -> bool {
    run.pre.contains(resource)
        || run.interference.environment_additions.contains(resource)
}

pub open spec fn ensure_member_zero_effect(
    _request: replay_layer::RequestId,
    run: ExternalRun<
        ISet<config_layer::Resource>, EnsureMemberWitness,
    >,
) -> bool {
    forall|resource: config_layer::Resource|
        #[trigger] run.post.contains(resource)
            <==> ensure_member_baseline_contains(run, resource)
}

pub open spec fn ensure_member_one_effect(
    request: replay_layer::RequestId,
    run: ExternalRun<
        ISet<config_layer::Resource>, EnsureMemberWitness,
    >,
) -> bool {
    forall|resource: config_layer::Resource|
        #[trigger] run.post.contains(resource)
            <==> ensure_member_baseline_contains(run, resource)
                || resource == ensure_member_target(request)
}

pub open spec fn ensure_member_has_linearized_attempt(
    run: ExternalRun<
        ISet<config_layer::Resource>, EnsureMemberWitness,
    >,
) -> bool {
    exists|attempt: replay_layer::AttemptId|
        run.interference.linearized_attempts.contains(attempt)
}

pub open spec fn ensure_member_env_rely(
    request: replay_layer::RequestId,
    history: Seq<p0_layer::PhysicalEvent>,
    run: ExternalRun<
        ISet<config_layer::Resource>, EnsureMemberWitness,
    >,
) -> bool {
    &&& !run.interference.environment_additions.contains(
        ensure_member_target(request),
    )
    &&& forall|attempt: replay_layer::AttemptId|
        #[trigger] run.interference.linearized_attempts.contains(attempt)
            ==> invoked(history, request, attempt)
    &&& if ensure_member_has_linearized_attempt(run) {
        ensure_member_one_effect(request, run)
    } else {
        ensure_member_zero_effect(request, run)
    }
}

pub open spec fn ensure_member_classification_ok(
    _request: replay_layer::RequestId,
    attempt: replay_layer::AttemptId,
    observation: replay_layer::Observation,
    run: ExternalRun<
        ISet<config_layer::Resource>, EnsureMemberWitness,
    >,
) -> bool {
    match observation {
        replay_layer::Observation::Success(value) => {
            run.interference.linearized_attempts.contains(attempt)
                && value.id == 1
        },
        replay_layer::Observation::Failure => {
            !run.interference.linearized_attempts.contains(attempt)
        },
        replay_layer::Observation::Ambiguous
        | replay_layer::Observation::InvalidResult(_) => true,
    }
}

pub open spec fn ensure_member_result_spec(
    request: replay_layer::RequestId,
    value: replay_layer::Value,
    run: ExternalRun<
        ISet<config_layer::Resource>, EnsureMemberWitness,
    >,
) -> bool {
    value.id == 1
        && run.post.contains(ensure_member_target(request))
}

pub open spec fn ensure_member_read_preserves(
    request: replay_layer::RequestId,
    run: ExternalRun<
        ISet<config_layer::Resource>, EnsureMemberWitness,
    >,
) -> bool {
    ensure_member_zero_effect(request, run)
}

pub open spec fn ensure_member_idempotent_under_rely(
    request: replay_layer::RequestId,
    run: ExternalRun<
        ISet<config_layer::Resource>, EnsureMemberWitness,
    >,
) -> bool {
    ensure_member_zero_effect(request, run)
        || ensure_member_one_effect(request, run)
}

pub open spec fn ensure_member_dedup_service_law(
    _request: replay_layer::RequestId,
    _namespace: replay_layer::AdapterNamespace,
    _key: replay_layer::StableKey,
    _history: Seq<p0_layer::PhysicalEvent>,
    _run: ExternalRun<
        ISet<config_layer::Resource>, EnsureMemberWitness,
    >,
) -> bool {
    false
}

pub open spec fn ensure_member_adapter() -> Adapter<
    ISet<config_layer::Resource>, EnsureMemberWitness,
> {
    Adapter {
        env_rely: |request, history, run|
            ensure_member_env_rely(request, history, run),
        classification_ok: |request, attempt, observation, run|
            ensure_member_classification_ok(
                request, attempt, observation, run,
            ),
        zero_effect: |request, run|
            ensure_member_zero_effect(request, run),
        one_effect: |request, run|
            ensure_member_one_effect(request, run),
        result_spec: |request, value, run|
            ensure_member_result_spec(request, value, run),
        read_preserves: |request, run|
            ensure_member_read_preserves(request, run),
        idempotent_under_rely: |request, run|
            ensure_member_idempotent_under_rely(request, run),
        dedup_service_law: |request, namespace, key, history, run|
            ensure_member_dedup_service_law(
                request, namespace, key, history, run,
            ),
    }
}

pub open spec fn ensure_member_request(
    request: replay_layer::RequestId,
) -> config_layer::Request {
    config_layer::Request {
        principal: config_layer::Principal { id: 0 },
        tool: config_layer::Tool { id: 0 },
        operation: config_layer::Operation { id: 0 },
        resource: ensure_member_target(request),
        arguments: config_layer::Arguments { id: 0 },
        capability: replay_layer::CapabilityId { id: 0 },
        retry_class: replay_layer::RetryClass::Idempotent,
        digest: replay_layer::Digest { id: 0 },
        adapter_namespace: replay_layer::AdapterNamespace { id: 0 },
        stable_key: Option::None,
        max_attempts: 2,
    }
}

pub open spec fn ensure_member_capability(
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

pub open spec fn ensure_member_full_config() -> config_layer::FullConfig {
    config_layer::FullConfig {
        request: IMap::new(
            |_request: replay_layer::RequestId| true,
            |request: replay_layer::RequestId|
                ensure_member_request(request),
        ),
        capability: IMap::new(
            |_capability: replay_layer::CapabilityId| true,
            |capability: replay_layer::CapabilityId|
                ensure_member_capability(capability),
        ),
        valid_results: ISet::new(
            |pair: (replay_layer::RequestId, replay_layer::Value)|
                pair.1.id == 1,
        ),
    }
}

pub open spec fn ensure_member_paper() -> t1_layer::PaperConfig<
    Adapter<ISet<config_layer::Resource>, EnsureMemberWitness>,
> {
    t1_layer::PaperConfig {
        broker: ensure_member_full_config(),
        adapter: ensure_member_adapter(),
    }
}

pub proof fn ensure_member_full_config_is_well_formed()
    ensures
        config_layer::full_config_wf(ensure_member_full_config()),
        t1_layer::paper_config_wf(ensure_member_paper()),
        forall|request: replay_layer::RequestId|
            #[trigger] ensure_member_full_config().request[request]
                .retry_class == replay_layer::RetryClass::Idempotent,
        forall|request: replay_layer::RequestId|
            #[trigger] ensure_member_full_config().request[request]
                .stable_key == Option::None,
        forall|request: replay_layer::RequestId|
            #[trigger] ensure_member_full_config().request[request]
                .max_attempts == 2,
{
    let cfg = ensure_member_full_config();
    t1_layer::paper_broker_config_is_broker(ensure_member_paper());
    assert(cfg.request.dom()
        == ISet::<replay_layer::RequestId>::full());
    assert(cfg.capability.dom()
        == ISet::<replay_layer::CapabilityId>::full());
    assert forall|request: replay_layer::RequestId|
        #[trigger] cfg.request[request].retry_class
            == replay_layer::RetryClass::Idempotent by {
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

proof fn ensure_member_selected_delivery_is_classified(
    cfg: config_layer::FullConfig,
    history: Seq<p0_layer::PhysicalEvent>,
    request: replay_layer::RequestId,
    attempt: replay_layer::AttemptId,
    observation: replay_layer::Observation,
    run: ExternalRun<
        ISet<config_layer::Resource>, EnsureMemberWitness,
    >,
)
    requires
        p1_layer::physical_unique(history),
        delivered_observations_classified(
            cfg,
            ensure_member_adapter(),
            history,
            request,
            run,
        ),
        delivery(history, request, attempt)
            == Option::Some(observation),
    ensures
        ensure_member_classification_ok(
            request, attempt, observation, run,
        ),
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
    assert(ensure_member_classification_ok(
        request, attempt, observation, run,
    ));
    match observation {
        replay_layer::Observation::Success(value) => {
            assert(cfg.valid_results.contains((request, value)));
        },
        replay_layer::Observation::Failure
        | replay_layer::Observation::Ambiguous
        | replay_layer::Observation::InvalidResult(_) => {},
    }
}

proof fn ensure_member_all_failed_has_no_linearized_attempt(
    cfg: config_layer::FullConfig,
    history: Seq<p0_layer::PhysicalEvent>,
    request: replay_layer::RequestId,
    run: ExternalRun<
        ISet<config_layer::Resource>, EnsureMemberWitness,
    >,
)
    requires
        p1_layer::physical_unique(history),
        delivered_observations_classified(
            cfg,
            ensure_member_adapter(),
            history,
            request,
            run,
        ),
        all_invocations_failed(history, request),
        forall|attempt: replay_layer::AttemptId|
            #[trigger] run.interference.linearized_attempts
                .contains(attempt)
                ==> invoked(history, request, attempt),
    ensures !ensure_member_has_linearized_attempt(run),
{
    if ensure_member_has_linearized_attempt(run) {
        let attempt = choose|attempt: replay_layer::AttemptId|
            run.interference.linearized_attempts.contains(attempt);
        assert(run.interference.linearized_attempts.contains(attempt));
        assert(invoked(history, request, attempt));
        assert(delivery(history, request, attempt)
            == Option::Some(replay_layer::Observation::Failure));
        ensure_member_selected_delivery_is_classified(
            cfg,
            history,
            request,
            attempt,
            replay_layer::Observation::Failure,
            run,
        );
        assert(!run.interference.linearized_attempts.contains(attempt));
        assert(false);
    }
}

pub proof fn ensure_member_adapter_is_verified()
    ensures adapter_verified(ensure_member_paper()),
{
    let paper = ensure_member_paper();
    let cfg = ensure_member_full_config();
    t1_layer::paper_broker_config_is_broker(paper);
    assert(t1_layer::paper_broker_config(paper) == cfg);
    assert forall|request: replay_layer::RequestId,
                  records: Seq<replay_layer::JournalRecord>,
                  history: Seq<p0_layer::PhysicalEvent>,
                  run: ExternalRun<
                      ISet<config_layer::Resource>,
                      EnsureMemberWitness,
                  >,
                  outcome: TerminalOutcome| #![auto] {
        &&& replay_layer::journal_legal(
            config_layer::erase_config(cfg), records,
        )
        &&& adapter_rely_trace(
            paper, request, history, run,
        )
        &&& outcome_evidence(
            cfg, records, request, history, outcome,
        )
        &&& broker_outcome_compatible(
            cfg, records, request, history, outcome,
        )
    } implies refines(
        paper, request, history, run, outcome,
    ) by {
        let adapter = ensure_member_adapter();
        assert(cfg.request[request].retry_class
            == replay_layer::RetryClass::Idempotent);
        assert(adapter_rely_trace(
            paper, request, history, run,
        ));
        assert((adapter.env_rely)(request, history, run));
        assert(ensure_member_env_rely(request, history, run));
        assert(delivered_observations_classified(
            cfg, adapter, history, request, run,
        ));
        assert(p1_layer::physical_unique(history));
        match outcome {
            TerminalOutcome::Commit { attempt, value } => {
                assert(delivery(history, request, attempt)
                    == Option::Some(
                        replay_layer::Observation::Success(value),
                    ));
                ensure_member_selected_delivery_is_classified(
                    cfg,
                    history,
                    request,
                    attempt,
                    replay_layer::Observation::Success(value),
                    run,
                );
                assert(run.interference.linearized_attempts
                    .contains(attempt));
                assert(value.id == 1);
                assert(ensure_member_has_linearized_attempt(run));
                assert(ensure_member_one_effect(request, run));
                assert(run.post.contains(
                    ensure_member_target(request),
                ));
                assert(ensure_member_result_spec(
                    request, value, run,
                ));
            },
            TerminalOutcome::Fail { attempt } => {
                assert(delivery(history, request, attempt)
                    == Option::Some(
                        replay_layer::Observation::Failure,
                    ));
                assert(all_invocations_failed(history, request));
                ensure_member_all_failed_has_no_linearized_attempt(
                    cfg, history, request, run,
                );
                assert(!ensure_member_has_linearized_attempt(run));
                assert(ensure_member_zero_effect(request, run));
            },
            TerminalOutcome::UnknownOutcome { .. } => {
                if ensure_member_has_linearized_attempt(run) {
                    assert(ensure_member_one_effect(request, run));
                } else {
                    assert(ensure_member_zero_effect(request, run));
                }
            },
        }
    }
}

pub open spec fn ensure_member_request_zero()
    -> replay_layer::RequestId
{
    replay_layer::RequestId { id: 0 }
}

pub open spec fn ensure_member_success_value()
    -> replay_layer::Value
{
    replay_layer::Value { id: 1 }
}

pub open spec fn ensure_member_single_run() -> ExternalRun<
    ISet<config_layer::Resource>, EnsureMemberWitness,
> {
    let request = ensure_member_request_zero();
    ExternalRun {
        pre: ISet::empty(),
        post: ISet::new(
            |resource: config_layer::Resource|
                resource == ensure_member_target(request),
        ),
        interference: EnsureMemberWitness {
            environment_additions: ISet::empty(),
            linearized_attempts: ISet::new(
                |attempt: replay_layer::AttemptId| attempt == 1,
            ),
        },
    }
}

pub open spec fn ensure_member_two_attempt_run() -> ExternalRun<
    ISet<config_layer::Resource>, EnsureMemberWitness,
> {
    let request = ensure_member_request_zero();
    ExternalRun {
        pre: ISet::empty(),
        post: ISet::new(
            |resource: config_layer::Resource|
                resource == ensure_member_target(request),
        ),
        interference: EnsureMemberWitness {
            environment_additions: ISet::empty(),
            linearized_attempts: ISet::new(
                |attempt: replay_layer::AttemptId|
                    attempt == 1 || attempt == 2,
            ),
        },
    }
}

pub proof fn ensure_member_effect_model_is_nontrivial()
    ensures
        ensure_member_one_effect(
            ensure_member_request_zero(),
            ensure_member_single_run(),
        ),
        !ensure_member_zero_effect(
            ensure_member_request_zero(),
            ensure_member_single_run(),
        ),
        ensure_member_result_spec(
            ensure_member_request_zero(),
            ensure_member_success_value(),
            ensure_member_single_run(),
        ),
        ensure_member_one_effect(
            ensure_member_request_zero(),
            ensure_member_two_attempt_run(),
        ),
        ensure_member_single_run().interference
            .linearized_attempts.contains(1),
        ensure_member_two_attempt_run().interference
            .linearized_attempts.contains(1),
        ensure_member_two_attempt_run().interference
            .linearized_attempts.contains(2),
        !ensure_member_result_spec(
            ensure_member_request_zero(),
            replay_layer::Value { id: 2 },
            ensure_member_single_run(),
        ),
{
    let request = ensure_member_request_zero();
    let target = ensure_member_target(request);
    let single = ensure_member_single_run();
    let repeated = ensure_member_two_attempt_run();
    assert forall|resource: config_layer::Resource|
        #[trigger] single.post.contains(resource)
            <==> ensure_member_baseline_contains(single, resource)
                || resource == target by {
    }
    assert forall|resource: config_layer::Resource|
        #[trigger] repeated.post.contains(resource)
            <==> ensure_member_baseline_contains(repeated, resource)
                || resource == target by {
    }
    assert(ensure_member_one_effect(request, single));
    assert(ensure_member_one_effect(request, repeated));
    assert(!ensure_member_zero_effect(request, single)) by {
        if ensure_member_zero_effect(request, single) {
            assert(single.post.contains(target));
            assert(!ensure_member_baseline_contains(single, target));
            assert(false);
        }
    }
}

pub open spec fn ensure_member_mixed_history()
    -> Seq<p0_layer::PhysicalEvent>
{
    let cfg = ensure_member_full_config();
    let request = ensure_member_request_zero();
    let value = ensure_member_success_value();
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
            observation: replay_layer::Observation::Success(value),
            journal_cut: 4,
        })
        .push(p0_layer::PhysicalEvent::Invoke {
            request,
            attempt: 2,
            call: config_layer::canonical_call(cfg, request),
            journal_cut: 4,
            ack_cut: 4,
        })
        .push(p0_layer::PhysicalEvent::Delivered {
            request,
            attempt: 2,
            observation: replay_layer::Observation::Failure,
            journal_cut: 4,
        })
}

// This adapter-level rule models the crash-erased physical projection expected
// from Invoke, Success, Crash, Invoke, Failure.  It does not construct or
// establish realizability of an intervening Broker or WAL crash trace.
pub proof fn ensure_member_mixed_retry_is_one_effect()
    ensures
        adapter_rely_trace(
            ensure_member_paper(),
            ensure_member_request_zero(),
            ensure_member_mixed_history(),
            ensure_member_single_run(),
        ),
        ensure_member_one_effect(
            ensure_member_request_zero(),
            ensure_member_single_run(),
        ),
        !ensure_member_zero_effect(
            ensure_member_request_zero(),
            ensure_member_single_run(),
        ),
        delivery(
            ensure_member_mixed_history(),
            ensure_member_request_zero(),
            1,
        ) == Option::Some(replay_layer::Observation::Success(
            ensure_member_success_value(),
        )),
        delivery(
            ensure_member_mixed_history(),
            ensure_member_request_zero(),
            2,
        ) == Option::Some(replay_layer::Observation::Failure),
        !all_invocations_failed(
            ensure_member_mixed_history(),
            ensure_member_request_zero(),
        ),
{
    let cfg = ensure_member_full_config();
    let paper = ensure_member_paper();
    let request = ensure_member_request_zero();
    let value = ensure_member_success_value();
    let run = ensure_member_single_run();
    let invoke1 = p0_layer::PhysicalEvent::Invoke {
        request,
        attempt: 1,
        call: config_layer::canonical_call(cfg, request),
        journal_cut: 4,
        ack_cut: 4,
    };
    let success1 = p0_layer::PhysicalEvent::Delivered {
        request,
        attempt: 1,
        observation: replay_layer::Observation::Success(value),
        journal_cut: 4,
    };
    let invoke2 = p0_layer::PhysicalEvent::Invoke {
        request,
        attempt: 2,
        call: config_layer::canonical_call(cfg, request),
        journal_cut: 4,
        ack_cut: 4,
    };
    let failure2 = p0_layer::PhysicalEvent::Delivered {
        request,
        attempt: 2,
        observation: replay_layer::Observation::Failure,
        journal_cut: 4,
    };
    let h0 = Seq::<p0_layer::PhysicalEvent>::empty();
    let h1 = h0.push(invoke1);
    let h2 = h1.push(success1);
    let h3 = h2.push(invoke2);
    let history = h3.push(failure2);
    assert(history == ensure_member_mixed_history());

    p1_layer::unique_push_invoke(h0, invoke1, request, 1);
    p1_layer::delivery_count_push(h0, invoke1, request, 1);
    assert(p1_layer::delivery_count(h1, request, 1) == 0);
    p1_layer::delivery_count_push(h1, success1, request, 1);
    p1_layer::unique_push_delivery(h1, success1, request, 1);
    p1_layer::invoke_count_push(h0, invoke1, request, 2);
    p1_layer::invoke_count_push(h1, success1, request, 2);
    assert(p1_layer::invoke_count(h2, request, 2) == 0);
    p1_layer::invoke_count_push(h2, invoke2, request, 2);
    p1_layer::unique_push_invoke(h2, invoke2, request, 2);
    p1_layer::delivery_count_push(h0, invoke1, request, 2);
    p1_layer::delivery_count_push(h1, success1, request, 2);
    p1_layer::delivery_count_push(h2, invoke2, request, 2);
    assert(p1_layer::delivery_count(h3, request, 2) == 0);
    p1_layer::delivery_count_push(h3, failure2, request, 2);
    p1_layer::unique_push_delivery(h3, failure2, request, 2);
    assert(p1_layer::physical_unique(history));

    p1_layer::ordered_push_invoke(h0, invoke1);
    p1_layer::invoke_count_push(h1, success1, request, 1);
    p1_layer::ordered_push_delivery(h1, success1, request, 1);
    p1_layer::ordered_push_invoke(h2, invoke2);
    p1_layer::invoke_count_push(h3, failure2, request, 2);
    p1_layer::ordered_push_delivery(h3, failure2, request, 2);
    assert(p1_layer::physical_ordered(history));

    assert forall|index: int| 0 <= index < history.len() implies
        event_is_for_request(#[trigger] history[index], request) by {
        assert(index == 0 || index == 1 || index == 2 || index == 3);
    }
    assert forall|index: int| 0 <= index < history.len() implies
        match #[trigger] history[index] {
            p0_layer::PhysicalEvent::Invoke { call, .. } => {
                call == config_layer::canonical_call(cfg, request)
            },
            p0_layer::PhysicalEvent::Delivered { .. } => true,
        } by {
        assert(index == 0 || index == 1 || index == 2 || index == 3);
    }
    assert forall|index: int| 0 <= index < history.len() implies
        match #[trigger] history[index] {
            p0_layer::PhysicalEvent::Invoke { attempt, .. }
            | p0_layer::PhysicalEvent::Delivered { attempt, .. } => {
                attempt > 0
            },
        } by {
        assert(index == 0 || index == 1 || index == 2 || index == 3);
    }
    assert forall|index: int| 0 <= index < history.len() implies
        match #[trigger] history[index] {
            p0_layer::PhysicalEvent::Delivered {
                attempt, observation, ..
            } => {
                &&& ensure_member_classification_ok(
                    request, attempt, observation, run,
                )
                &&& match observation {
                    replay_layer::Observation::Success(result) => {
                        cfg.valid_results.contains((request, result))
                    },
                    replay_layer::Observation::Failure
                    | replay_layer::Observation::Ambiguous
                    | replay_layer::Observation::InvalidResult(_) => true,
                }
            },
            p0_layer::PhysicalEvent::Invoke { .. } => true,
        } by {
        assert(index == 0 || index == 1 || index == 2 || index == 3);
    }

    ensure_member_effect_model_is_nontrivial();
    p1_layer::invoke_count_push(h0, invoke1, request, 1);
    p1_layer::invoke_count_push(h1, success1, request, 1);
    p1_layer::invoke_count_push(h2, invoke2, request, 1);
    p1_layer::invoke_count_push(h3, failure2, request, 1);
    assert(p1_layer::invoke_count(history, request, 1) == 1);
    assert(invoked(history, request, 1));
    assert forall|attempt: replay_layer::AttemptId|
        #[trigger] run.interference.linearized_attempts.contains(attempt)
            implies invoked(history, request, attempt) by {
        assert(attempt == 1);
    }
    assert(ensure_member_has_linearized_attempt(run));
    assert(ensure_member_env_rely(request, history, run));
    t1_layer::paper_broker_config_is_broker(paper);
    assert(t1_layer::paper_broker_config(paper) == cfg);
    assert(adapter_rely_trace(paper, request, history, run));

    p1_layer::delivery_count_push(h0, invoke1, request, 1);
    p1_layer::delivery_count_push(h1, success1, request, 1);
    p1_layer::delivery_count_push(h2, invoke2, request, 1);
    p1_layer::delivery_count_push(h3, failure2, request, 1);
    assert(p1_layer::delivery_count(history, request, 1) == 1);
    reveal_with_fuel(latest_delivery_observation, 5);
    assert(latest_delivery_observation(history, request, 1)
        == Option::Some(replay_layer::Observation::Success(value)));
    assert(delivery(history, request, 1)
        == Option::Some(replay_layer::Observation::Success(value)));
    p1_layer::delivery_count_push(h0, invoke1, request, 2);
    p1_layer::delivery_count_push(h1, success1, request, 2);
    p1_layer::delivery_count_push(h2, invoke2, request, 2);
    p1_layer::delivery_count_push(h3, failure2, request, 2);
    assert(p1_layer::delivery_count(history, request, 2) == 1);
    assert(latest_delivery_observation(history, request, 2)
        == Option::Some(replay_layer::Observation::Failure));
    assert(delivery(history, request, 2)
        == Option::Some(replay_layer::Observation::Failure));
    assert(!all_invocations_failed(history, request));
}

pub open spec fn t6_a0_zero_wal_execution(
    cfg: config_layer::FullConfig,
) -> wal_runtime_layer::WalExecution {
    wal_runtime_layer::WalExecution {
        configs: Seq::empty().push(
            wal_runtime_layer::initial_configuration(cfg),
        ),
        events: Seq::empty(),
    }
}

pub open spec fn t6_a0_extend_wal_execution(
    cfg: config_layer::FullConfig,
    execution: wal_runtime_layer::WalExecution,
    local: wal_runtime_layer::WalEvent,
) -> wal_runtime_layer::WalExecution {
    let before = execution.configs.last();
    wal_runtime_layer::WalExecution {
        configs: execution.configs.push(
            wal_runtime_layer::apply(cfg, before, local),
        ),
        events: execution.events.push(
            wal_runtime_layer::wal_encode(local),
        ),
    }
}

pub proof fn t6_a0_zero_wal_execution_exec(
    cfg: config_layer::FullConfig,
)
    ensures wal_runtime_layer::exec(
        cfg, t6_a0_zero_wal_execution(cfg),
    ),
{
}

pub proof fn t6_a0_extend_wal_execution_exec(
    cfg: config_layer::FullConfig,
    execution: wal_runtime_layer::WalExecution,
    local: wal_runtime_layer::WalEvent,
)
    requires
        wal_runtime_layer::exec(cfg, execution),
        wal_runtime_layer::admissibly_enabled(
            cfg, execution.configs.last(), local,
        ),
    ensures wal_runtime_layer::exec(
        cfg, t6_a0_extend_wal_execution(cfg, execution, local),
    ),
{
    let extended = t6_a0_extend_wal_execution(cfg, execution, local);
    let old_len = execution.events.len();
    assert(execution.configs.len() == old_len + 1);
    assert(execution.configs.last()
        == execution.configs[old_len as int]);
    wal_runtime_layer::wal_decode_encode(local);
    assert(wal_runtime_layer::wal_runtime_step(
        cfg,
        execution.configs.last(),
        wal_runtime_layer::wal_encode(local),
        wal_runtime_layer::apply(
            cfg, execution.configs.last(), local,
        ),
    ));
    assert forall|index: nat| index < extended.events.len() implies
        #[trigger] wal_runtime_layer::wal_runtime_step(
            cfg,
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
            assert(extended.events[index as int]
                == wal_runtime_layer::wal_encode(local));
            assert(extended.configs[index as int]
                == execution.configs.last());
            assert(extended.configs[(index + 1) as int]
                == wal_runtime_layer::apply(
                    cfg, execution.configs.last(), local,
                ));
        }
    }
}

pub open spec fn t6_a0_append_full_wal_execution(
    cfg: config_layer::FullConfig,
    execution: wal_runtime_layer::WalExecution,
    record: replay_layer::JournalRecord,
) -> wal_runtime_layer::WalExecution {
    let before = execution.configs.last();
    let staged = t6_a0_extend_wal_execution(
        cfg,
        execution,
        wal_runtime_layer::WalEvent::WalStage { record },
    );
    let written = t6_a0_extend_wal_execution(
        cfg,
        staged,
        wal_runtime_layer::WalEvent::WalWriteFull { record },
    );
    t6_a0_extend_wal_execution(
        cfg,
        written,
        wal_runtime_layer::WalEvent::WalFlushAck {
            cut: wal_runtime_layer::journal_view(before).len() + 1,
        },
    )
}

pub proof fn t6_a0_append_full_wal_execution_exec(
    cfg: config_layer::FullConfig,
    execution: wal_runtime_layer::WalExecution,
    record: replay_layer::JournalRecord,
)
    requires
        wal_runtime_layer::exec(cfg, execution),
        execution.configs.last().runtime.mode
            == record_layer::Mode::Online,
        wal_runtime_layer::wal_quiescent(
            execution.configs.last(),
        ),
        execution.configs.last().runtime.store.media
            == wal_runtime_layer::full_frames(
                wal_runtime_layer::journal_view(
                    execution.configs.last(),
                ),
            ),
        wal_runtime_layer::runtime_record_enabled(
            cfg, execution.configs.last(), record,
        ),
    ensures
        wal_runtime_layer::exec(
            cfg, t6_a0_append_full_wal_execution(cfg, execution, record),
        ),
        t6_a0_append_full_wal_execution(cfg, execution, record)
            .events.len() == execution.events.len() + 3,
        t6_a0_append_full_wal_execution(cfg, execution, record)
            .configs.last().runtime.mode == record_layer::Mode::Online,
        wal_runtime_layer::wal_quiescent(
            t6_a0_append_full_wal_execution(cfg, execution, record)
                .configs.last(),
        ),
        wal_runtime_layer::journal_view(
            t6_a0_append_full_wal_execution(cfg, execution, record)
                .configs.last(),
        ) == wal_runtime_layer::journal_view(
            execution.configs.last(),
        ).push(record),
        t6_a0_append_full_wal_execution(cfg, execution, record)
            .configs.last().runtime.store.media
            == wal_runtime_layer::full_frames(
                wal_runtime_layer::journal_view(
                    t6_a0_append_full_wal_execution(cfg, execution, record)
                        .configs.last(),
                ),
            ),
        t6_a0_append_full_wal_execution(cfg, execution, record)
            .configs.last().evidence.records
            == execution.configs.last().evidence.records.push(record),
        t6_a0_append_full_wal_execution(cfg, execution, record)
            .configs.last().evidence.physical
            == execution.configs.last().evidence.physical,
        t6_a0_append_full_wal_execution(cfg, execution, record)
            .configs.last().runtime.slot
            == wal_runtime_layer::slot_after_record(
                cfg, execution.configs.last(), record,
            ),
{
    let before = execution.configs.last();
    let old_journal = wal_runtime_layer::journal_view(before);
    let stage_event = wal_runtime_layer::WalEvent::WalStage { record };
    let staged = t6_a0_extend_wal_execution(cfg, execution, stage_event);
    assert(wal_runtime_layer::admissibly_enabled(
        cfg, before, stage_event,
    ));
    t6_a0_extend_wal_execution_exec(cfg, execution, stage_event);
    let after_stage = staged.configs.last();
    assert(after_stage
        == wal_runtime_layer::apply(cfg, before, stage_event));
    assert(wal_runtime_layer::journal_view(after_stage) == old_journal);
    assert(wal_runtime_layer::runtime_record_enabled(
        cfg, after_stage, record,
    ));
    wal_runtime_layer::canonical_media_facts(
        before.runtime.store.media,
    );
    wal_runtime_layer::full_frames_no_torn(old_journal);
    assert(wal_runtime_layer::no_torn(
        after_stage.runtime.store.media,
    ));

    let write_event = wal_runtime_layer::WalEvent::WalWriteFull { record };
    let written = t6_a0_extend_wal_execution(cfg, staged, write_event);
    assert(wal_runtime_layer::admissibly_enabled(
        cfg, after_stage, write_event,
    ));
    t6_a0_extend_wal_execution_exec(cfg, staged, write_event);
    let after_write = written.configs.last();
    assert(after_write
        == wal_runtime_layer::apply(cfg, after_stage, write_event));
    wal_runtime_layer::parse_push_full(
        before.runtime.store.media,
        before.runtime.store.media.len() + 1,
        record,
    );
    assert(wal_runtime_layer::journal_view(after_write)
        == old_journal.push(record));
    assert(after_write.runtime.store.cache
        == wal_runtime_layer::journal_view(after_write));

    let cut = old_journal.len() + 1;
    let flush_event = wal_runtime_layer::WalEvent::WalFlushAck { cut };
    assert(wal_runtime_layer::admissibly_enabled(
        cfg, after_write, flush_event,
    ));
    t6_a0_extend_wal_execution_exec(cfg, written, flush_event);
    let finished = t6_a0_append_full_wal_execution(cfg, execution, record);
    let after_flush = finished.configs.last();
    assert(after_flush
        == wal_runtime_layer::apply(cfg, after_write, flush_event));
    wal_runtime_layer::full_frames_push(old_journal, record);
    assert(after_write.runtime.store.media
        == wal_runtime_layer::full_frames(old_journal.push(record)));
    assert(wal_runtime_layer::journal_view(after_flush)
        == old_journal.push(record));
}

pub open spec fn ensure_member_authorize_record()
    -> replay_layer::JournalRecord
{
    replay_layer::JournalRecord::Authorize {
        request: ensure_member_request_zero(),
        capability: replay_layer::CapabilityId { id: 0 },
        digest: replay_layer::Digest { id: 0 },
    }
}

pub open spec fn ensure_member_prepare_record()
    -> replay_layer::JournalRecord
{
    replay_layer::JournalRecord::Prepare {
        request: ensure_member_request_zero(),
        class: replay_layer::RetryClass::Idempotent,
        digest: replay_layer::Digest { id: 0 },
        key: Option::None,
        auth_ref: 1,
    }
}

pub open spec fn ensure_member_arm_record()
    -> replay_layer::JournalRecord
{
    replay_layer::JournalRecord::Arm {
        request: ensure_member_request_zero(),
        digest: replay_layer::Digest { id: 0 },
        key: Option::None,
        prepare_ref: 2,
    }
}

pub open spec fn ensure_member_start_record()
    -> replay_layer::JournalRecord
{
    replay_layer::JournalRecord::Start {
        request: ensure_member_request_zero(),
        attempt: 1,
        digest: replay_layer::Digest { id: 0 },
        key: Option::None,
        arm_ref: 3,
    }
}

pub open spec fn ensure_member_outcome_record()
    -> replay_layer::JournalRecord
{
    replay_layer::JournalRecord::Outcome {
        request: ensure_member_request_zero(),
        attempt: 1,
        observation: replay_layer::Observation::Success(
            ensure_member_success_value(),
        ),
        digest: replay_layer::Digest { id: 0 },
        key: Option::None,
        start_ref: 4,
    }
}

pub open spec fn ensure_member_commit_record()
    -> replay_layer::JournalRecord
{
    replay_layer::JournalRecord::CommitRec {
        request: ensure_member_request_zero(),
        attempt: 1,
        value: ensure_member_success_value(),
        digest: replay_layer::Digest { id: 0 },
        key: Option::None,
        outcome_ref: 5,
    }
}

pub open spec fn ensure_member_records()
    -> Seq<replay_layer::JournalRecord>
{
    Seq::empty()
        .push(ensure_member_authorize_record())
        .push(ensure_member_prepare_record())
        .push(ensure_member_arm_record())
        .push(ensure_member_start_record())
        .push(ensure_member_outcome_record())
        .push(ensure_member_commit_record())
}

pub proof fn ensure_member_authorize_is_runtime_enabled()
    ensures wal_runtime_layer::runtime_record_enabled(
        ensure_member_full_config(),
        wal_runtime_layer::initial_configuration(
            ensure_member_full_config(),
        ),
        ensure_member_authorize_record(),
    ),
{
}

pub open spec fn ensure_member_invoke_wal_event()
    -> wal_runtime_layer::WalEvent
{
    let cfg = ensure_member_full_config();
    let request = ensure_member_request_zero();
    wal_runtime_layer::WalEvent::InvokeEvent {
        request,
        attempt: 1,
        call: config_layer::canonical_call(cfg, request),
        journal_cut: 4,
        ack_cut: 4,
    }
}

pub open spec fn ensure_member_deliver_wal_event()
    -> wal_runtime_layer::WalEvent
{
    wal_runtime_layer::WalEvent::DeliverEvent {
        request: ensure_member_request_zero(),
        attempt: 1,
        observation: replay_layer::Observation::Success(
            ensure_member_success_value(),
        ),
        journal_cut: 4,
    }
}

pub open spec fn ensure_member_wal_execution()
    -> wal_runtime_layer::WalExecution
{
    let cfg = ensure_member_full_config();
    let e0 = t6_a0_zero_wal_execution(cfg);
    let e1 = t6_a0_append_full_wal_execution(
        cfg, e0, ensure_member_authorize_record(),
    );
    let e2 = t6_a0_append_full_wal_execution(
        cfg, e1, ensure_member_prepare_record(),
    );
    let e3 = t6_a0_append_full_wal_execution(
        cfg, e2, ensure_member_arm_record(),
    );
    let e4 = t6_a0_append_full_wal_execution(
        cfg, e3, ensure_member_start_record(),
    );
    let e5 = t6_a0_extend_wal_execution(
        cfg, e4, ensure_member_invoke_wal_event(),
    );
    let e6 = t6_a0_extend_wal_execution(
        cfg, e5, ensure_member_deliver_wal_event(),
    );
    let e7 = t6_a0_append_full_wal_execution(
        cfg, e6, ensure_member_outcome_record(),
    );
    t6_a0_append_full_wal_execution(
        cfg, e7, ensure_member_commit_record(),
    )
}

pub proof fn ensure_member_wal_execution_exec()
    ensures
        wal_runtime_layer::exec(
            ensure_member_full_config(),
            ensure_member_wal_execution(),
        ),
        ensure_member_wal_execution().events.len() == 20,
        ensure_member_wal_execution().configs.len() == 21,
        wal_runtime_layer::journal_view(
            ensure_member_wal_execution().configs.last(),
        ) == ensure_member_records(),
        ensure_member_wal_execution().configs.last()
            .evidence.records == ensure_member_records(),
        ensure_member_wal_execution().configs.last()
            .runtime.store.media
            == wal_runtime_layer::full_frames(ensure_member_records()),
        ensure_member_wal_execution().configs.last()
            .runtime.store.cache == ensure_member_records(),
        ensure_member_wal_execution().configs.last()
            .runtime.store.acked_len == 6,
        ensure_member_wal_execution().configs.last()
            .runtime.mode == record_layer::Mode::Online,
        ensure_member_wal_execution().configs.last()
            .runtime.append is Idle,
        ensure_member_wal_execution().configs.last()
            .runtime.slot == record_layer::ExecSlot::Idle,
        ensure_member_wal_execution().configs.last()
            .evidence.physical
            == Seq::empty()
                .push(p0_layer::PhysicalEvent::Invoke {
                    request: ensure_member_request_zero(),
                    attempt: 1,
                    call: config_layer::canonical_call(
                        ensure_member_full_config(),
                        ensure_member_request_zero(),
                    ),
                    journal_cut: 4,
                    ack_cut: 4,
                })
                .push(p0_layer::PhysicalEvent::Delivered {
                    request: ensure_member_request_zero(),
                    attempt: 1,
                    observation: replay_layer::Observation::Success(
                        ensure_member_success_value(),
                    ),
                    journal_cut: 4,
                }),
{
    let cfg = ensure_member_full_config();
    let request = ensure_member_request_zero();
    let auth = ensure_member_authorize_record();
    let prepare = ensure_member_prepare_record();
    let arm = ensure_member_arm_record();
    let start = ensure_member_start_record();
    let outcome = ensure_member_outcome_record();
    let commit = ensure_member_commit_record();

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
    ensure_member_authorize_is_runtime_enabled();
    assert(e0.configs.last().runtime.mode == record_layer::Mode::Online);
    assert(wal_runtime_layer::wal_quiescent(e0.configs.last()));
    assert(e0.configs.last().runtime.store.media
        == wal_runtime_layer::full_frames(
            wal_runtime_layer::journal_view(e0.configs.last()),
        ));
    let e1 = t6_a0_append_full_wal_execution(cfg, e0, auth);
    t6_a0_append_full_wal_execution_exec(cfg, e0, auth);
    assert(wal_runtime_layer::journal_view(e1.configs.last())
        == Seq::empty().push(auth));
    assert(wal_runtime_layer::runtime_record_enabled(
        cfg, e1.configs.last(), prepare,
    ));

    let e2 = t6_a0_append_full_wal_execution(cfg, e1, prepare);
    t6_a0_append_full_wal_execution_exec(cfg, e1, prepare);
    assert(wal_runtime_layer::journal_view(e2.configs.last())
        == Seq::empty().push(auth).push(prepare));
    assert(wal_runtime_layer::runtime_record_enabled(
        cfg, e2.configs.last(), arm,
    ));

    let e3 = t6_a0_append_full_wal_execution(cfg, e2, arm);
    t6_a0_append_full_wal_execution_exec(cfg, e2, arm);
    assert(wal_runtime_layer::journal_view(e3.configs.last())
        == Seq::empty().push(auth).push(prepare).push(arm));
    assert(wal_runtime_layer::runtime_record_enabled(
        cfg, e3.configs.last(), start,
    ));

    let e4 = t6_a0_append_full_wal_execution(cfg, e3, start);
    t6_a0_append_full_wal_execution_exec(cfg, e3, start);
    assert(wal_runtime_layer::journal_view(e4.configs.last())
        == Seq::empty().push(auth).push(prepare).push(arm).push(start));
    assert(e4.configs.last().runtime.slot
        == (record_layer::ExecSlot::Ready { request, attempt: 1 }));
    assert(e4.configs.last().evidence.acknowledged_prefix
        == e4.configs.last().evidence.records);
    assert(e4.configs.last().evidence.acknowledged_prefix.len() == 4);
    assert(journal_runtime_layer::start_covered_by_cut(
        e4.configs.last().evidence.records, request, 1, 4,
    ));

    let invoke = ensure_member_invoke_wal_event();
    assert(wal_runtime_layer::admissibly_enabled(
        cfg, e4.configs.last(), invoke,
    ));
    let e5 = t6_a0_extend_wal_execution(cfg, e4, invoke);
    t6_a0_extend_wal_execution_exec(cfg, e4, invoke);
    assert(e5.configs.last().runtime.slot
        == (record_layer::ExecSlot::InFlight {
            request, attempt: 1,
        }));

    let deliver = ensure_member_deliver_wal_event();
    assert(wal_runtime_layer::admissibly_enabled(
        cfg, e5.configs.last(), deliver,
    ));
    let e6 = t6_a0_extend_wal_execution(cfg, e5, deliver);
    t6_a0_extend_wal_execution_exec(cfg, e5, deliver);
    assert(e6.configs.last().runtime.slot
        == (record_layer::ExecSlot::Received {
            request,
            attempt: 1,
            observation: replay_layer::Observation::Success(
                ensure_member_success_value(),
            ),
        }));
    assert(wal_runtime_layer::runtime_record_enabled(
        cfg, e6.configs.last(), outcome,
    ));

    let e7 = t6_a0_append_full_wal_execution(cfg, e6, outcome);
    t6_a0_append_full_wal_execution_exec(cfg, e6, outcome);
    assert(wal_runtime_layer::journal_view(e7.configs.last())
        == Seq::empty().push(auth).push(prepare).push(arm)
            .push(start).push(outcome));
    assert(e7.configs.last().runtime.slot
        == (record_layer::ExecSlot::ObservedSuccess {
            request,
            attempt: 1,
            value: ensure_member_success_value(),
        }));
    assert(wal_runtime_layer::runtime_record_enabled(
        cfg, e7.configs.last(), commit,
    ));

    let e8 = t6_a0_append_full_wal_execution(cfg, e7, commit);
    t6_a0_append_full_wal_execution_exec(cfg, e7, commit);
    assert(e8 == ensure_member_wal_execution());
    assert(wal_runtime_layer::journal_view(e8.configs.last())
        == ensure_member_records());
    assert(e8.configs.last().evidence.records
        == ensure_member_records());
    assert(e8.configs.last().runtime.store.media
        == wal_runtime_layer::full_frames(ensure_member_records()));
    assert(e8.configs.last().runtime.store.cache
        == ensure_member_records());
    assert(e8.configs.last().runtime.store.acked_len == 6);
    assert(e8.configs.last().runtime.slot == record_layer::ExecSlot::Idle);
}

pub open spec fn ensure_member_success_history()
    -> Seq<p0_layer::PhysicalEvent>
{
    let cfg = ensure_member_full_config();
    let request = ensure_member_request_zero();
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
                ensure_member_success_value(),
            ),
            journal_cut: 4,
        })
}

pub proof fn ensure_member_success_history_satisfies_rely()
    ensures
        adapter_rely_trace(
            ensure_member_paper(),
            ensure_member_request_zero(),
            ensure_member_success_history(),
            ensure_member_single_run(),
        ),
        delivery(
            ensure_member_success_history(),
            ensure_member_request_zero(),
            1,
        ) == Option::Some(replay_layer::Observation::Success(
            ensure_member_success_value(),
        )),
        ensure_member_one_effect(
            ensure_member_request_zero(),
            ensure_member_single_run(),
        ),
        !ensure_member_zero_effect(
            ensure_member_request_zero(),
            ensure_member_single_run(),
        ),
{
    let cfg = ensure_member_full_config();
    let paper = ensure_member_paper();
    let request = ensure_member_request_zero();
    let value = ensure_member_success_value();
    let run = ensure_member_single_run();
    let invoke = p0_layer::PhysicalEvent::Invoke {
        request,
        attempt: 1,
        call: config_layer::canonical_call(cfg, request),
        journal_cut: 4,
        ack_cut: 4,
    };
    let delivered = p0_layer::PhysicalEvent::Delivered {
        request,
        attempt: 1,
        observation: replay_layer::Observation::Success(value),
        journal_cut: 4,
    };
    let empty = Seq::<p0_layer::PhysicalEvent>::empty();
    let invoked_history = empty.push(invoke);
    let history = invoked_history.push(delivered);
    assert(history == ensure_member_success_history());

    p1_layer::unique_push_invoke(empty, invoke, request, 1);
    p1_layer::delivery_count_push(empty, invoke, request, 1);
    p1_layer::unique_push_delivery(
        invoked_history, delivered, request, 1,
    );
    p1_layer::ordered_push_invoke(empty, invoke);
    p1_layer::invoke_count_push(empty, invoke, request, 1);
    p1_layer::invoke_count_push(
        invoked_history, delivered, request, 1,
    );
    p1_layer::ordered_push_delivery(
        invoked_history, delivered, request, 1,
    );
    assert(p1_layer::physical_unique(history));
    assert(p1_layer::physical_ordered(history));

    assert forall|index: int| 0 <= index < history.len() implies
        event_is_for_request(#[trigger] history[index], request) by {
        assert(index == 0 || index == 1);
    }
    assert forall|index: int| 0 <= index < history.len() implies
        match #[trigger] history[index] {
            p0_layer::PhysicalEvent::Invoke { call, .. } => {
                call == config_layer::canonical_call(cfg, request)
            },
            p0_layer::PhysicalEvent::Delivered { .. } => true,
        } by {
        assert(index == 0 || index == 1);
    }
    assert forall|index: int| 0 <= index < history.len() implies
        match #[trigger] history[index] {
            p0_layer::PhysicalEvent::Invoke { attempt, .. }
            | p0_layer::PhysicalEvent::Delivered { attempt, .. } => {
                attempt > 0
            },
        } by {
        assert(index == 0 || index == 1);
    }
    assert forall|index: int| 0 <= index < history.len() implies
        match #[trigger] history[index] {
            p0_layer::PhysicalEvent::Delivered {
                attempt, observation, ..
            } => {
                &&& ensure_member_classification_ok(
                    request, attempt, observation, run,
                )
                &&& match observation {
                    replay_layer::Observation::Success(result) => {
                        cfg.valid_results.contains((request, result))
                    },
                    replay_layer::Observation::Failure
                    | replay_layer::Observation::Ambiguous
                    | replay_layer::Observation::InvalidResult(_) => true,
                }
            },
            p0_layer::PhysicalEvent::Invoke { .. } => true,
        } by {
        assert(index == 0 || index == 1);
    }

    ensure_member_effect_model_is_nontrivial();
    p1_layer::invoke_count_push(empty, invoke, request, 1);
    p1_layer::invoke_count_push(
        invoked_history, delivered, request, 1,
    );
    assert(invoked(history, request, 1));
    assert forall|attempt: replay_layer::AttemptId|
        #[trigger] run.interference.linearized_attempts.contains(attempt)
            implies invoked(history, request, attempt) by {
        assert(attempt == 1);
    }
    assert(ensure_member_env_rely(request, history, run));
    t1_layer::paper_broker_config_is_broker(paper);
    assert(t1_layer::paper_broker_config(paper) == cfg);
    assert(adapter_rely_trace(paper, request, history, run));

    p1_layer::delivery_count_push(
        invoked_history, delivered, request, 1,
    );
    reveal_with_fuel(latest_delivery_observation, 3);
    assert(delivery(history, request, 1)
        == Option::Some(replay_layer::Observation::Success(value)));
}

pub open spec fn ensure_member_terminal_outcome() -> TerminalOutcome {
    TerminalOutcome::Commit {
        attempt: 1,
        value: ensure_member_success_value(),
    }
}

pub proof fn ensure_member_records_select_terminal_commit()
    ensures terminal_from_records(
        ensure_member_records(), ensure_member_request_zero(),
    ) == Option::Some(ensure_member_terminal_outcome()),
{
    reveal_with_fuel(replay_layer::terminal_count, 8);
    reveal_with_fuel(latest_terminal_record, 8);
}

pub open spec fn ensure_member_broker_execution()
    -> execution_layer::BrokerExecution
{
    t4_c0_layer::canonical_target_execution(
        ensure_member_full_config(), ensure_member_wal_execution(),
    )
}

pub open spec fn ensure_member_final_broker() -> p0_layer::State {
    let target = ensure_member_broker_execution();
    target.configs[target.events.len() as int]
}

pub open spec fn ensure_member_semantic_package(
    paper: t1_layer::PaperConfig<Adapter<
        ISet<config_layer::Resource>, EnsureMemberWitness,
    >>,
    execution: wal_runtime_layer::WalExecution,
    broker: p0_layer::State,
    request: replay_layer::RequestId,
    run: ExternalRun<
        ISet<config_layer::Resource>, EnsureMemberWitness,
    >,
    outcome: TerminalOutcome,
) -> bool {
    let cfg = t1_layer::paper_broker_config(paper);
    let final_state = execution.configs[execution.events.len() as int];
    &&& t1_layer::paper_config_wf(paper)
    &&& adapter_verified(paper)
    &&& wal_runtime_layer::exec(cfg, execution)
    &&& wal_trace_layer::admissible_wal_trace(cfg, execution)
    &&& wal_trace_layer::trace_agreement(cfg, execution)
    &&& t4_c0_layer::wal_broker_representation(
        cfg, final_state, broker,
    )
    &&& contract_layer::broker_contract_invariant(cfg, broker)
    &&& replay_layer::journal_legal(
        config_layer::erase_config(cfg), final_state.evidence.records,
    )
    &&& adapter_rely(paper, execution.events, request, run)
    &&& terminal(execution.events, request) == Option::Some(outcome)
    &&& terminal_evidence_and_compatibility(
        cfg,
        execution.events,
        final_state.evidence.records,
        request,
        outcome,
    )
    &&& refines(
        paper,
        request,
        projection_layer::pi_adapter(execution.events, request),
        run,
        outcome,
    )
    &&& per_request_effect_refinement(
        paper, execution.events, request, run,
    )
    &&& (paper.adapter.one_effect)(request, run)
    &&& !(paper.adapter.zero_effect)(request, run)
    &&& execution.events.len() == 20
    &&& projection_layer::pi_adapter(
        execution.events, request,
    ).len() == 2
    &&& final_state.evidence.records == ensure_member_records()
    &&& projection_layer::pi_adapter(
        execution.events, request,
    ) == ensure_member_success_history()
    &&& outcome == ensure_member_terminal_outcome()
}

pub proof fn ensure_member_concrete_semantic_package()
    ensures ensure_member_semantic_package(
        ensure_member_paper(),
        ensure_member_wal_execution(),
        ensure_member_final_broker(),
        ensure_member_request_zero(),
        ensure_member_single_run(),
        ensure_member_terminal_outcome(),
    ),
{
    let paper = ensure_member_paper();
    let cfg = ensure_member_full_config();
    let source = ensure_member_wal_execution();
    let request = ensure_member_request_zero();
    let run = ensure_member_single_run();
    let outcome = ensure_member_terminal_outcome();
    let target = t4_c0_layer::canonical_target_execution(cfg, source);
    let map = t4_c0_layer::canonical_composed_map(source);
    let broker = ensure_member_final_broker();
    let length = source.events.len();
    let final_state = source.configs[length as int];

    ensure_member_full_config_is_well_formed();
    t1_layer::paper_broker_config_is_broker(paper);
    assert(t1_layer::paper_broker_config(paper) == cfg);
    ensure_member_adapter_is_verified();
    ensure_member_wal_execution_exec();
    assert(wal_runtime_layer::exec(cfg, source));
    wal_trace_layer::exec_implies_admissible_wal_trace(cfg, source);
    wal_trace_layer::trace_agreement_for_exec(cfg, source);
    assert(wal_trace_layer::trace_agreement_at(cfg, source, length));
    assert(wal_trace_layer::prefix_events(source, length)
        == source.events);
    assert(final_state.evidence.records
        == projection_layer::pi_journal(source.events));
    assert(final_state.evidence.physical
        == projection_layer::pi_physical(source.events));

    config_layer::erasure_is_replay_well_formed(cfg);
    t4_c0_layer::canonical_closed_wal_broker_composition(cfg, source);
    assert(t4_c0_layer::weak_simulation_index_map(
        cfg, source, target, map,
    ));
    assert(t2_layer::weak_index_shape(
        source.events.len(), target.events.len(), map,
    ));
    assert(map.points[length as int] == target.events.len());
    assert(t4_c0_layer::related_prefixes(
        cfg, source, target, map,
    ));
    assert(t4_c0_layer::wal_broker_representation(
        cfg,
        source.configs[length as int],
        target.configs[target.events.len() as int],
    ));
    assert(target == ensure_member_broker_execution());
    assert(broker == target.configs[target.events.len() as int]);
    assert(t4_c0_layer::wal_broker_representation(
        cfg, final_state, broker,
    ));
    assert(t2_representation_layer::representation(
        cfg, wal_runtime_layer::journal_projection(final_state), broker,
    ));
    assert(contract_layer::broker_contract_invariant(cfg, broker));

    wal_runtime_layer::every_exec_configuration_is_basic(cfg, source);
    assert(wal_runtime_layer::basic_invariant(cfg, final_state));
    assert(replay_layer::journal_legal(
        config_layer::erase_config(cfg),
        wal_runtime_layer::journal_view(final_state),
    ));
    assert(final_state.evidence.records
        == wal_runtime_layer::journal_view(final_state));
    assert(replay_layer::journal_legal(
        config_layer::erase_config(cfg), final_state.evidence.records,
    ));

    assert(final_state.evidence.physical
        == ensure_member_success_history());
    assert(projection_layer::pi_physical(source.events)
        == ensure_member_success_history());
    reveal_with_fuel(projection_layer::adapter_from_physical, 3);
    assert(projection_layer::pi_adapter(source.events, request)
        == ensure_member_success_history());
    ensure_member_success_history_satisfies_rely();
    assert(adapter_rely_trace(
        paper, request, ensure_member_success_history(), run,
    ));
    assert(adapter_rely(paper, source.events, request, run));

    assert(final_state.evidence.records == ensure_member_records());
    assert(projection_layer::pi_journal(source.events)
        == ensure_member_records());
    ensure_member_records_select_terminal_commit();
    assert(terminal(source.events, request) == Option::Some(outcome));

    t6_s0_layer::wal_terminal_outcome_has_evidence_and_is_compatible(
        paper, source, broker, request, run, outcome,
    );
    assert(terminal_evidence_and_compatibility(
        cfg,
        source.events,
        final_state.evidence.records,
        request,
        outcome,
    ));
    wal_terminal_outcome_refines(
        paper, source, broker, request, run, outcome,
    );
    ensure_member_effect_model_is_nontrivial();
    assert((paper.adapter.one_effect)(request, run));
    assert(!(paper.adapter.zero_effect)(request, run));
    assert(source.events.len() == 20);
    assert(projection_layer::pi_adapter(
        source.events, request,
    ).len() == 2);
}

pub proof fn t6_a0_semantic_nonvacuity()
    ensures exists|
        paper: t1_layer::PaperConfig<Adapter<
            ISet<config_layer::Resource>, EnsureMemberWitness,
        >>,
        execution: wal_runtime_layer::WalExecution,
        broker: p0_layer::State,
        request: replay_layer::RequestId,
        run: ExternalRun<
            ISet<config_layer::Resource>, EnsureMemberWitness,
        >,
        outcome: TerminalOutcome| #![auto] {
            &&& paper == ensure_member_paper()
            &&& execution == ensure_member_wal_execution()
            &&& broker == ensure_member_final_broker()
            &&& request == ensure_member_request_zero()
            &&& run == ensure_member_single_run()
            &&& outcome == ensure_member_terminal_outcome()
            &&& ensure_member_semantic_package(
                paper, execution, broker, request, run, outcome,
            )
        },
{
    ensure_member_concrete_semantic_package();
    assert(exists|
        paper: t1_layer::PaperConfig<Adapter<
            ISet<config_layer::Resource>, EnsureMemberWitness,
        >>,
        execution: wal_runtime_layer::WalExecution,
        broker: p0_layer::State,
        request: replay_layer::RequestId,
        run: ExternalRun<
            ISet<config_layer::Resource>, EnsureMemberWitness,
        >,
        outcome: TerminalOutcome| #![auto] {
            &&& paper == ensure_member_paper()
            &&& execution == ensure_member_wal_execution()
            &&& broker == ensure_member_final_broker()
            &&& request == ensure_member_request_zero()
            &&& run == ensure_member_single_run()
            &&& outcome == ensure_member_terminal_outcome()
            &&& ensure_member_semantic_package(
                paper, execution, broker, request, run, outcome,
            )
        }) by {
        let paper = ensure_member_paper();
        let execution = ensure_member_wal_execution();
        let broker = ensure_member_final_broker();
        let request = ensure_member_request_zero();
        let run = ensure_member_single_run();
        let outcome = ensure_member_terminal_outcome();
    }
}

} // verus!
