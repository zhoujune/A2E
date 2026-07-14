use vstd::prelude::*;

#[path = "t5_commit_step.rs"]
pub mod t5_s0_layer;

verus! {

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
use contract_layer::p3_layer::p2_layer::p1_layer::p0_layer;
use p0_layer::config_layer;
use config_layer::broker_layer as record_layer;
use record_layer::query_layer::c1_layer::append_layer;

// T5-E0 lifts T5-S0's exact one-step equations over arbitrary finite
// execution intervals. The WAL proof discharges its local storage premise
// from the invariant already established for every reachable configuration.

pub proof fn commit_prefix_transitive<T>(
    first: Seq<T>,
    middle: Seq<T>,
    last: Seq<T>,
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

pub proof fn broker_execution_commit_history_monotone_between(
    cfg: config_layer::FullConfig,
    execution: execution_layer::BrokerExecution,
    earlier: nat,
    later: nat,
)
    requires
        execution_layer::exec(cfg, execution),
        earlier <= later,
        later < execution.configs.len(),
    ensures append_layer::is_prefix(
        t5_s0_layer::alpha_commit_broker(
            execution.configs[earlier as int],
        ),
        t5_s0_layer::alpha_commit_broker(
            execution.configs[later as int],
        ),
    ),
    decreases later - earlier,
{
    if earlier == later {
        append_layer::prefix_reflexive(
            t5_s0_layer::alpha_commit_broker(
                execution.configs[earlier as int],
            ),
        );
    } else {
        let previous: nat = (later - 1) as nat;
        assert(earlier <= previous);
        assert(previous < later);
        assert(previous < execution.configs.len());
        assert(later == previous + 1);
        assert(previous < execution.events.len());
        assert(execution_layer::broker_step(
            cfg,
            execution.configs[previous as int],
            execution.events[previous as int],
            execution.configs[later as int],
        ));
        broker_execution_commit_history_monotone_between(
            cfg, execution, earlier, previous,
        );
        t5_s0_layer::broker_step_commit_history_monotone(
            cfg,
            execution.configs[previous as int],
            execution.events[previous as int],
            execution.configs[later as int],
        );
        commit_prefix_transitive(
            t5_s0_layer::alpha_commit_broker(
                execution.configs[earlier as int],
            ),
            t5_s0_layer::alpha_commit_broker(
                execution.configs[previous as int],
            ),
            t5_s0_layer::alpha_commit_broker(
                execution.configs[later as int],
            ),
        );
    }
}

pub proof fn journal_execution_commit_history_monotone_between(
    cfg: config_layer::FullConfig,
    execution: journal_runtime_layer::JournalExecution,
    earlier: nat,
    later: nat,
)
    requires
        journal_runtime_layer::exec(cfg, execution),
        earlier <= later,
        later < execution.configs.len(),
    ensures append_layer::is_prefix(
        t5_s0_layer::alpha_commit_journal(
            cfg, execution.configs[earlier as int],
        ),
        t5_s0_layer::alpha_commit_journal(
            cfg, execution.configs[later as int],
        ),
    ),
    decreases later - earlier,
{
    if earlier == later {
        append_layer::prefix_reflexive(
            t5_s0_layer::alpha_commit_journal(
                cfg, execution.configs[earlier as int],
            ),
        );
    } else {
        let previous: nat = (later - 1) as nat;
        assert(earlier <= previous);
        assert(previous < later);
        assert(previous < execution.configs.len());
        assert(later == previous + 1);
        assert(previous < execution.events.len());
        assert(journal_runtime_layer::journal_runtime_step(
            cfg,
            execution.configs[previous as int],
            execution.events[previous as int],
            execution.configs[later as int],
        ));
        journal_execution_commit_history_monotone_between(
            cfg, execution, earlier, previous,
        );
        t5_s0_layer::journal_step_commit_history_monotone(
            cfg,
            execution.configs[previous as int],
            execution.events[previous as int],
            execution.configs[later as int],
        );
        commit_prefix_transitive(
            t5_s0_layer::alpha_commit_journal(
                cfg, execution.configs[earlier as int],
            ),
            t5_s0_layer::alpha_commit_journal(
                cfg, execution.configs[previous as int],
            ),
            t5_s0_layer::alpha_commit_journal(
                cfg, execution.configs[later as int],
            ),
        );
    }
}

pub proof fn wal_execution_commit_history_monotone_between(
    cfg: config_layer::FullConfig,
    execution: wal_runtime_layer::WalExecution,
    earlier: nat,
    later: nat,
)
    requires
        wal_runtime_layer::exec(cfg, execution),
        earlier <= later,
        later < execution.configs.len(),
    ensures append_layer::is_prefix(
        t5_s0_layer::alpha_commit_wal(
            cfg, execution.configs[earlier as int],
        ),
        t5_s0_layer::alpha_commit_wal(
            cfg, execution.configs[later as int],
        ),
    ),
    decreases later - earlier,
{
    if earlier == later {
        append_layer::prefix_reflexive(
            t5_s0_layer::alpha_commit_wal(
                cfg, execution.configs[earlier as int],
            ),
        );
    } else {
        let previous: nat = (later - 1) as nat;
        assert(earlier <= previous);
        assert(previous < later);
        assert(previous < execution.configs.len());
        assert(later == previous + 1);
        assert(previous < execution.events.len());
        assert(wal_runtime_layer::wal_runtime_step(
            cfg,
            execution.configs[previous as int],
            execution.events[previous as int],
            execution.configs[later as int],
        ));
        wal_execution_commit_history_monotone_between(
            cfg, execution, earlier, previous,
        );
        wal_runtime_layer::every_exec_configuration_is_basic(cfg, execution);
        assert(wal_runtime_layer::basic_invariant(
            cfg, execution.configs[previous as int],
        ));
        assert(wal_runtime_layer::wal_invariant(
            cfg,
            execution.configs[previous as int].runtime.store,
            execution.configs[previous as int].runtime.mode,
            execution.configs[previous as int].runtime.append,
        ));
        t5_s0_layer::wal_step_commit_history_monotone(
            cfg,
            execution.configs[previous as int],
            execution.events[previous as int],
            execution.configs[later as int],
        );
        commit_prefix_transitive(
            t5_s0_layer::alpha_commit_wal(
                cfg, execution.configs[earlier as int],
            ),
            t5_s0_layer::alpha_commit_wal(
                cfg, execution.configs[previous as int],
            ),
            t5_s0_layer::alpha_commit_wal(
                cfg, execution.configs[later as int],
            ),
        );
    }
}

} // verus!
