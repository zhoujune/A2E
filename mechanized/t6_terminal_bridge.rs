use vstd::prelude::*;

#[path = "t6_terminal_compatibility.rs"]
pub mod t6_c0_layer;

verus! {

use t6_c0_layer::*;
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

// T6-S0 combines the two frozen Broker-side halves and transports the
// resulting conjunction through the already verified atomic-Journal and
// typed-WAL representation boundaries.  Adapter effects and Refines remain
// deliberately outside this checkpoint.

pub proof fn event_terminal_outcome_has_evidence_and_is_compatible<X, I>(
    paper: t1_layer::PaperConfig<Adapter<X, I>>,
    events: Seq<global_layer::GlobalEvent>,
    broker: p0_layer::State,
    request: replay_layer::RequestId,
    run: ExternalRun<X, I>,
    outcome: TerminalOutcome,
)
    requires
        t1_layer::paper_config_wf(paper),
        contract_layer::broker_contract_invariant(
            t1_layer::paper_broker_config(paper), broker,
        ),
        broker.core.evidence.records
            == projection_layer::pi_journal(events),
        broker.physical.physical
            == projection_layer::pi_physical(events),
        adapter_rely(paper, events, request, run),
        terminal(events, request) == Option::Some(outcome),
    ensures terminal_evidence_and_compatibility(
        t1_layer::paper_broker_config(paper),
        events,
        broker.core.evidence.records,
        request,
        outcome,
    ),
{
    let cfg = t1_layer::paper_broker_config(paper);
    t6_e0_layer::event_terminal_outcome_has_evidence(
        cfg, events, broker, request, outcome,
    );
    t6_c0_layer::event_terminal_outcome_is_compatible(
        paper, events, broker, request, run, outcome,
    );
}

pub proof fn t6_s0_core<X, I>(
    paper: t1_layer::PaperConfig<Adapter<X, I>>,
    events: Seq<global_layer::GlobalEvent>,
    broker: p0_layer::State,
    request: replay_layer::RequestId,
    run: ExternalRun<X, I>,
    outcome: TerminalOutcome,
)
    ensures t6_s0_core_statement(
        paper, events, broker, request, run, outcome,
    ),
{
    let cfg = t1_layer::paper_broker_config(paper);
    if t1_layer::paper_config_wf(paper)
        && contract_layer::broker_contract_invariant(cfg, broker)
        && broker.core.evidence.records
            == projection_layer::pi_journal(events)
        && broker.physical.physical
            == projection_layer::pi_physical(events)
        && adapter_rely(paper, events, request, run)
        && terminal(events, request) == Option::Some(outcome)
    {
        event_terminal_outcome_has_evidence_and_is_compatible(
            paper, events, broker, request, run, outcome,
        );
    }
}

pub proof fn journal_terminal_outcome_has_evidence_and_is_compatible<X, I>(
    paper: t1_layer::PaperConfig<Adapter<X, I>>,
    execution: journal_runtime_layer::JournalExecution,
    broker: p0_layer::State,
    request: replay_layer::RequestId,
    run: ExternalRun<X, I>,
    outcome: TerminalOutcome,
)
    requires
        t1_layer::paper_config_wf(paper),
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
    ensures terminal_evidence_and_compatibility(
        t1_layer::paper_broker_config(paper),
        execution.events,
        execution.configs[execution.events.len() as int].evidence.records,
        request,
        outcome,
    ),
{
    let cfg = t1_layer::paper_broker_config(paper);
    let length = execution.events.len();
    let final_state = execution.configs[length as int];
    assert(journal_trace_layer::trace_agreement_at(
        cfg, execution, length,
    ));
    assert(journal_trace_layer::prefix_events(execution, length)
        == execution.events);
    assert(final_state.evidence.records
        == projection_layer::pi_journal(execution.events));
    assert(final_state.evidence.physical
        == projection_layer::pi_physical(execution.events));
    assert(t2_representation_layer::broker_ghost_equals(
        broker, final_state.evidence,
    ));
    assert(broker.core.evidence.records
        == projection_layer::pi_journal(execution.events));
    assert(broker.physical.physical
        == projection_layer::pi_physical(execution.events));
    event_terminal_outcome_has_evidence_and_is_compatible(
        paper, execution.events, broker, request, run, outcome,
    );
}

pub proof fn journal_t6_s0<X, I>(
    paper: t1_layer::PaperConfig<Adapter<X, I>>,
    execution: journal_runtime_layer::JournalExecution,
    broker: p0_layer::State,
    request: replay_layer::RequestId,
    run: ExternalRun<X, I>,
    outcome: TerminalOutcome,
)
    ensures journal_t6_s0_statement(
        paper, execution, broker, request, run, outcome,
    ),
{
    let cfg = t1_layer::paper_broker_config(paper);
    let final_state = execution.configs[execution.events.len() as int];
    if t1_layer::paper_config_wf(paper)
        && journal_runtime_layer::exec(cfg, execution)
        && journal_trace_layer::admissible_journal_trace(cfg, execution)
        && journal_trace_layer::trace_agreement(cfg, execution)
        && t2_representation_layer::representation(
            cfg, final_state, broker,
        )
        && adapter_rely(paper, execution.events, request, run)
        && terminal(execution.events, request) == Option::Some(outcome)
    {
        journal_terminal_outcome_has_evidence_and_is_compatible(
            paper, execution, broker, request, run, outcome,
        );
    }
}

pub proof fn wal_terminal_outcome_has_evidence_and_is_compatible<X, I>(
    paper: t1_layer::PaperConfig<Adapter<X, I>>,
    execution: wal_runtime_layer::WalExecution,
    broker: p0_layer::State,
    request: replay_layer::RequestId,
    run: ExternalRun<X, I>,
    outcome: TerminalOutcome,
)
    requires
        t1_layer::paper_config_wf(paper),
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
    ensures terminal_evidence_and_compatibility(
        t1_layer::paper_broker_config(paper),
        execution.events,
        execution.configs[execution.events.len() as int].evidence.records,
        request,
        outcome,
    ),
{
    let cfg = t1_layer::paper_broker_config(paper);
    let length = execution.events.len();
    let final_state = execution.configs[length as int];
    assert(wal_trace_layer::trace_agreement_at(
        cfg, execution, length,
    ));
    assert(wal_trace_layer::prefix_events(execution, length)
        == execution.events);
    assert(final_state.evidence.records
        == projection_layer::pi_journal(execution.events));
    assert(final_state.evidence.physical
        == projection_layer::pi_physical(execution.events));
    assert(t2_representation_layer::broker_ghost_equals(
        broker,
        wal_runtime_layer::journal_projection(final_state).evidence,
    ));
    assert(wal_runtime_layer::journal_projection(final_state).evidence
        == final_state.evidence);
    assert(broker.core.evidence.records
        == projection_layer::pi_journal(execution.events));
    assert(broker.physical.physical
        == projection_layer::pi_physical(execution.events));
    event_terminal_outcome_has_evidence_and_is_compatible(
        paper, execution.events, broker, request, run, outcome,
    );
}

pub proof fn wal_t6_s0<X, I>(
    paper: t1_layer::PaperConfig<Adapter<X, I>>,
    execution: wal_runtime_layer::WalExecution,
    broker: p0_layer::State,
    request: replay_layer::RequestId,
    run: ExternalRun<X, I>,
    outcome: TerminalOutcome,
)
    ensures wal_t6_s0_statement(
        paper, execution, broker, request, run, outcome,
    ),
{
    let cfg = t1_layer::paper_broker_config(paper);
    let final_state = execution.configs[execution.events.len() as int];
    if t1_layer::paper_config_wf(paper)
        && wal_runtime_layer::exec(cfg, execution)
        && wal_trace_layer::admissible_wal_trace(cfg, execution)
        && wal_trace_layer::trace_agreement(cfg, execution)
        && t4_c0_layer::wal_broker_representation(
            cfg, final_state, broker,
        )
        && adapter_rely(paper, execution.events, request, run)
        && terminal(execution.events, request) == Option::Some(outcome)
    {
        wal_terminal_outcome_has_evidence_and_is_compatible(
            paper, execution, broker, request, run, outcome,
        );
    }
}

} // verus!
