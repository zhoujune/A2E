use vstd::prelude::*;

#[path = "t2_atomic_runtime.rs"]
pub mod runtime_layer;

verus! {

use runtime_layer::t1_layer;
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
use record_layer::query_layer::c1_layer;
use c1_layer::replay_layer;
use c1_layer::append_layer;

// T2-J1 states the atomic runtime's caller rely and trace agreement directly
// over its independent relational executions.  Nothing in this file obtains
// these facts by translating to a Broker execution.

pub open spec fn prefix_events(
    execution: runtime_layer::JournalExecution,
    length: nat,
) -> Seq<global_layer::GlobalEvent> {
    execution.events.take(length as int)
}

pub open spec fn admissible_step_at(
    cfg: config_layer::FullConfig,
    execution: runtime_layer::JournalExecution,
    index: nat,
) -> bool {
    index < execution.events.len()
        && index + 1 < execution.configs.len()
        && match runtime_layer::journal_decode(
            execution.events[index as int],
        ) {
            Option::None => false,
            Option::Some(local) => {
                let before = execution.configs[index as int];
                let after = execution.configs[(index + 1) as int];
                &&& runtime_layer::control_enabled(cfg, before, local)
                &&& runtime_layer::evidence_admissible(before, local)
                &&& after == runtime_layer::apply(cfg, before, local)
            },
        }
}

// Operational caller rules are already enforced by JournalRuntimeStep.  This
// predicate exposes those rules as the paper-level AdmissibleJournalTrace rely
// without identifying admissibility definitionally with Exec.
pub open spec fn admissible_journal_trace(
    cfg: config_layer::FullConfig,
    execution: runtime_layer::JournalExecution,
) -> bool {
    execution.configs.len() == execution.events.len() + 1
        && forall|index: nat| index < execution.events.len() ==>
            #[trigger] admissible_step_at(cfg, execution, index)
}

pub open spec fn successful_return_cuts_exact(
    events: Seq<global_layer::GlobalEvent>,
) -> bool {
    t1_layer::successful_return_cuts_exact(events)
}

pub open spec fn projection_agreement(
    state: runtime_layer::JournalConfiguration,
    events: Seq<global_layer::GlobalEvent>,
) -> bool {
    let records = projection_layer::pi_journal(events);
    &&& runtime_layer::journal_view(state) == records
    &&& state.evidence.records == records
    &&& state.evidence.physical == projection_layer::pi_physical(events)
    &&& state.evidence.ack_cuts == projection_layer::pi_ack(events)
}

// Exact agreement for one concrete relational execution prefix.  The first
// two conjuncts distinguish the concrete atomic Journal from the separate
// proof record history even though execution proves them equal.
pub open spec fn trace_agreement_at(
    cfg: config_layer::FullConfig,
    execution: runtime_layer::JournalExecution,
    length: nat,
) -> bool {
    length <= execution.events.len()
        && length < execution.configs.len()
        && {
            let events = prefix_events(execution, length);
            let state = execution.configs[length as int];
            let records = projection_layer::pi_journal(events);
            let physical = projection_layer::pi_physical(events);
            let cuts = projection_layer::pi_ack(events);
            &&& runtime_layer::journal_view(state) == records
            &&& state.evidence.records == records
            &&& state.evidence.physical == physical
            &&& state.evidence.ack_cuts == cuts
            &&& append_layer::cuts_bounded(cuts, records.len())
            &&& append_layer::cuts_monotone(cuts)
            &&& state.evidence.acknowledged_prefix
                == append_layer::acknowledged_prefix_for(records, cuts)
            &&& state.evidence.acknowledged_prefix.len()
                == append_layer::last_or_zero(cuts)
            &&& append_layer::is_prefix(
                state.evidence.acknowledged_prefix, records,
            )
            &&& successful_return_cuts_exact(events)
        }
}

pub open spec fn prefix_trace_agreement(
    cfg: config_layer::FullConfig,
    execution: runtime_layer::JournalExecution,
) -> bool {
    forall|length: nat| length <= execution.events.len() ==>
        #[trigger] trace_agreement_at(cfg, execution, length)
}

pub open spec fn invoke_cut_agreement_at(
    execution: runtime_layer::JournalExecution,
    index: nat,
) -> bool {
    index < execution.events.len() && match execution.events[index as int] {
        global_layer::GlobalEvent::InvokeEvent {
            journal_cut, ack_cut, ..
        } => {
            let events = execution.events.take(index as int);
            let state = execution.configs[index as int];
            journal_cut == projection_layer::pi_journal(events).len()
                && ack_cut == state.evidence.acknowledged_prefix.len()
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
        | global_layer::GlobalEvent::DeliverEvent { .. }
        | global_layer::GlobalEvent::IgnoreStale { .. }
        | global_layer::GlobalEvent::RetryRelease { .. }
        | global_layer::GlobalEvent::Crash
        | global_layer::GlobalEvent::BeginScan
        | global_layer::GlobalEvent::FinishScan
        | global_layer::GlobalEvent::TruncateTail
        | global_layer::GlobalEvent::AbortScan
        | global_layer::GlobalEvent::BeginRecover
        | global_layer::GlobalEvent::FinishRecover => true,
    }
}

pub open spec fn invoke_cut_agreement(
    execution: runtime_layer::JournalExecution,
) -> bool {
    forall|index: nat| index < execution.events.len() ==>
        #[trigger] invoke_cut_agreement_at(execution, index)
}

pub open spec fn trace_agreement(
    cfg: config_layer::FullConfig,
    execution: runtime_layer::JournalExecution,
) -> bool {
    prefix_trace_agreement(cfg, execution)
        && invoke_cut_agreement(execution)
}

pub proof fn exec_implies_admissible_journal_trace(
    cfg: config_layer::FullConfig,
    execution: runtime_layer::JournalExecution,
)
    requires runtime_layer::exec(cfg, execution),
    ensures admissible_journal_trace(cfg, execution),
{
    assert forall|index: nat| index < execution.events.len() implies
        #[trigger] admissible_step_at(cfg, execution, index) by {
        assert(index + 1 < execution.configs.len());
        assert(runtime_layer::journal_runtime_step(
            cfg,
            execution.configs[index as int],
            execution.events[index as int],
            execution.configs[(index + 1) as int],
        ));
        match runtime_layer::journal_decode(execution.events[index as int]) {
            Option::None => {},
            Option::Some(local) => {
                assert(runtime_layer::journal_local_step(
                    cfg,
                    execution.configs[index as int],
                    local,
                    execution.configs[(index + 1) as int],
                ));
            },
        }
    }
}

pub proof fn apply_preserves_projection_agreement(
    cfg: config_layer::FullConfig,
    before: runtime_layer::JournalConfiguration,
    global: global_layer::GlobalEvent,
    local: runtime_layer::JournalEvent,
    events: Seq<global_layer::GlobalEvent>,
)
    requires
        runtime_layer::journal_decode(global) == Option::Some(local),
        projection_agreement(before, events),
    ensures projection_agreement(
        runtime_layer::apply(cfg, before, local),
        events.push(global),
    ),
{
    projection_layer::pi_journal_push(events, global);
    projection_layer::pi_physical_push(events, global);
    projection_layer::pi_ack_push(events, global);
    match global {
        global_layer::GlobalEvent::BrokerLinearize { .. } => {},
        global_layer::GlobalEvent::JournalAppendCall { .. } => {},
        global_layer::GlobalEvent::JournalAppendLinearize { .. } => {},
        global_layer::GlobalEvent::JournalAppendReturn { .. } => {},
        global_layer::GlobalEvent::JournalDiskFull { .. } => {},
        global_layer::GlobalEvent::WalStage { .. } => {},
        global_layer::GlobalEvent::WalWriteFull { .. } => {},
        global_layer::GlobalEvent::WalWriteTorn { .. } => {},
        global_layer::GlobalEvent::WalFinishTorn { .. } => {},
        global_layer::GlobalEvent::WalFlushAck { .. } => {},
        global_layer::GlobalEvent::WalDiskFull { .. } => {},
        global_layer::GlobalEvent::InvokeEvent { .. } => {},
        global_layer::GlobalEvent::DeliverEvent { .. } => {},
        global_layer::GlobalEvent::IgnoreStale { .. } => {},
        global_layer::GlobalEvent::RetryRelease { .. } => {},
        global_layer::GlobalEvent::Crash => {},
        global_layer::GlobalEvent::BeginScan => {},
        global_layer::GlobalEvent::FinishScan => {},
        global_layer::GlobalEvent::TruncateTail => {},
        global_layer::GlobalEvent::AbortScan => {},
        global_layer::GlobalEvent::BeginRecover => {},
        global_layer::GlobalEvent::FinishRecover => {},
    }
}

pub proof fn final_projection_agreement_for_exec(
    cfg: config_layer::FullConfig,
    execution: runtime_layer::JournalExecution,
)
    requires runtime_layer::exec(cfg, execution),
    ensures projection_agreement(
        execution.configs[execution.events.len() as int],
        execution.events,
    ),
    decreases execution.events.len(),
{
    if execution.events.len() == 0 {
        assert(execution.configs[0]
            == runtime_layer::initial_configuration(cfg));
    } else {
        let length: nat = (execution.events.len() - 1) as nat;
        let prefix = runtime_layer::execution_prefix(execution, length);
        runtime_layer::exec_prefix(cfg, execution, length);
        final_projection_agreement_for_exec(cfg, prefix);
        assert(prefix.events =~= execution.events.drop_last());
        assert(prefix.configs.len() == length + 1);
        assert(prefix.configs[length as int]
            == execution.configs[length as int]);
        let global = execution.events[length as int];
        let before = execution.configs[length as int];
        let after = execution.configs[(length + 1) as int];
        assert(global == execution.events.last());
        assert(runtime_layer::journal_runtime_step(
            cfg, before, global, after,
        ));
        match runtime_layer::journal_decode(global) {
            Option::None => {},
            Option::Some(local) => {
                assert(runtime_layer::journal_local_step(
                    cfg, before, local, after,
                ));
                assert(after == runtime_layer::apply(cfg, before, local));
                apply_preserves_projection_agreement(
                    cfg, before, global, local, prefix.events,
                );
                assert(prefix.events.push(global) =~= execution.events);
            },
        }
    }
}

pub proof fn projection_agreement_at_for_exec(
    cfg: config_layer::FullConfig,
    execution: runtime_layer::JournalExecution,
    length: nat,
)
    requires
        runtime_layer::exec(cfg, execution),
        length <= execution.events.len(),
    ensures projection_agreement(
        execution.configs[length as int],
        prefix_events(execution, length),
    ),
{
    let prefix = runtime_layer::execution_prefix(execution, length);
    runtime_layer::exec_prefix(cfg, execution, length);
    final_projection_agreement_for_exec(cfg, prefix);
    assert(prefix.events =~= prefix_events(execution, length));
    assert(prefix.configs[length as int]
        == execution.configs[length as int]);
}

pub proof fn successful_return_cuts_exact_for_exec(
    cfg: config_layer::FullConfig,
    execution: runtime_layer::JournalExecution,
)
    requires runtime_layer::exec(cfg, execution),
    ensures successful_return_cuts_exact(execution.events),
{
    assert forall|index: nat| index < execution.events.len() implies
        match #[trigger] execution.events[index as int] {
            global_layer::GlobalEvent::JournalAppendReturn { cut }
            | global_layer::GlobalEvent::WalFlushAck { cut } => {
                cut == projection_layer::pi_journal(
                    execution.events.take(index as int),
                ).len()
            },
            _ => true,
        } by {
        projection_agreement_at_for_exec(cfg, execution, index);
        let before = execution.configs[index as int];
        let after = execution.configs[(index + 1) as int];
        let global = execution.events[index as int];
        assert(runtime_layer::journal_runtime_step(
            cfg, before, global, after,
        ));
        match global {
            global_layer::GlobalEvent::JournalAppendReturn { cut } => {
                match runtime_layer::journal_decode(global) {
                    Option::None => {},
                    Option::Some(local) => {
                        assert(runtime_layer::journal_local_step(
                            cfg, before, local, after,
                        ));
                        assert(runtime_layer::evidence_admissible(before, local));
                        assert(cut == runtime_layer::journal_view(before).len());
                    },
                }
            },
            global_layer::GlobalEvent::WalFlushAck { .. } => {
                assert(runtime_layer::journal_decode(global).is_none());
                assert(false);
            },
            global_layer::GlobalEvent::BrokerLinearize { .. }
            | global_layer::GlobalEvent::JournalAppendCall { .. }
            | global_layer::GlobalEvent::JournalAppendLinearize { .. }
            | global_layer::GlobalEvent::JournalDiskFull { .. }
            | global_layer::GlobalEvent::WalStage { .. }
            | global_layer::GlobalEvent::WalWriteFull { .. }
            | global_layer::GlobalEvent::WalWriteTorn { .. }
            | global_layer::GlobalEvent::WalFinishTorn { .. }
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
}

pub proof fn successful_return_cuts_exact_prefix(
    events: Seq<global_layer::GlobalEvent>,
    length: nat,
)
    requires
        successful_return_cuts_exact(events),
        length <= events.len(),
    ensures successful_return_cuts_exact(events.take(length as int)),
{
    t1_layer::successful_return_cuts_exact_prefix(events, length);
}

pub proof fn prefix_trace_agreement_for_exec(
    cfg: config_layer::FullConfig,
    execution: runtime_layer::JournalExecution,
)
    requires runtime_layer::exec(cfg, execution),
    ensures prefix_trace_agreement(cfg, execution),
{
    runtime_layer::every_exec_configuration_is_basic(cfg, execution);
    successful_return_cuts_exact_for_exec(cfg, execution);
    assert forall|length: nat| length <= execution.events.len() implies
        #[trigger] trace_agreement_at(cfg, execution, length) by {
        let events = prefix_events(execution, length);
        let state = execution.configs[length as int];
        let records = projection_layer::pi_journal(events);
        let cuts = projection_layer::pi_ack(events);
        assert(length < execution.configs.len());
        projection_agreement_at_for_exec(cfg, execution, length);
        assert(runtime_layer::basic_invariant(cfg, state));
        assert(append_layer::b1_invariant(runtime_layer::append_view(state)));
        successful_return_cuts_exact_prefix(execution.events, length);
        assert(state.evidence.records == records);
        assert(state.evidence.ack_cuts == cuts);
        assert(runtime_layer::append_view(state).evidence.records == records);
        assert(runtime_layer::append_view(state).evidence.ack_cuts == cuts);
    }
}

pub proof fn invoke_cut_agreement_at_for_exec(
    cfg: config_layer::FullConfig,
    execution: runtime_layer::JournalExecution,
    index: nat,
)
    requires
        runtime_layer::exec(cfg, execution),
        index < execution.events.len(),
    ensures invoke_cut_agreement_at(execution, index),
{
    let global = execution.events[index as int];
    let before = execution.configs[index as int];
    let after = execution.configs[(index + 1) as int];
    assert(index + 1 < execution.configs.len());
    assert(runtime_layer::journal_runtime_step(
        cfg, before, global, after,
    ));
    match global {
        global_layer::GlobalEvent::InvokeEvent {
            request, attempt, call, journal_cut, ack_cut,
        } => {
            let local = runtime_layer::JournalEvent::InvokeEvent {
                request, attempt, call, journal_cut, ack_cut,
            };
            assert(runtime_layer::journal_decode(global)
                == Option::Some(local));
            assert(runtime_layer::journal_local_step(
                cfg, before, local, after,
            ));
            assert(runtime_layer::evidence_admissible(before, local));
            projection_agreement_at_for_exec(cfg, execution, index);
            assert(runtime_layer::journal_view(before)
                == projection_layer::pi_journal(
                    execution.events.take(index as int),
                ));
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

pub proof fn trace_agreement_for_exec(
    cfg: config_layer::FullConfig,
    execution: runtime_layer::JournalExecution,
)
    requires runtime_layer::exec(cfg, execution),
    ensures trace_agreement(cfg, execution),
{
    prefix_trace_agreement_for_exec(cfg, execution);
    assert forall|index: nat| index < execution.events.len() implies
        #[trigger] invoke_cut_agreement_at(execution, index) by {
        invoke_cut_agreement_at_for_exec(cfg, execution, index);
    }
}

pub proof fn admissible_trace_prefix(
    cfg: config_layer::FullConfig,
    execution: runtime_layer::JournalExecution,
    length: nat,
)
    requires
        admissible_journal_trace(cfg, execution),
        runtime_layer::exec(cfg, execution),
        length <= execution.events.len(),
    ensures admissible_journal_trace(
        cfg, runtime_layer::execution_prefix(execution, length),
    ),
{
    let prefix = runtime_layer::execution_prefix(execution, length);
    runtime_layer::exec_prefix(cfg, execution, length);
    exec_implies_admissible_journal_trace(cfg, prefix);
}

pub proof fn journal_prefix_trace_agreement(
    cfg: config_layer::FullConfig,
    execution: runtime_layer::JournalExecution,
    length: nat,
)
    requires
        runtime_layer::exec(cfg, execution),
        length <= execution.events.len(),
    ensures
        runtime_layer::exec(
            cfg, runtime_layer::execution_prefix(execution, length),
        ),
        admissible_journal_trace(
            cfg, runtime_layer::execution_prefix(execution, length),
        ),
        trace_agreement(
            cfg, runtime_layer::execution_prefix(execution, length),
        ),
        trace_agreement_at(cfg, execution, length),
{
    let prefix = runtime_layer::execution_prefix(execution, length);
    runtime_layer::exec_prefix(cfg, execution, length);
    exec_implies_admissible_journal_trace(cfg, prefix);
    trace_agreement_for_exec(cfg, execution);
    trace_agreement_for_exec(cfg, prefix);
}

} // verus!
