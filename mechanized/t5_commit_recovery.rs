use vstd::prelude::*;

#[path = "t5_commit_execution.rs"]
pub mod t5_e0_layer;

verus! {

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
use p3_layer::p2_layer::p1_layer::p0_layer;
use p0_layer::config_layer;
use config_layer::broker_layer as record_layer;
use record_layer::query_layer;
use query_layer::c1_layer;
use c1_layer::replay_layer;
use c1_layer::append_layer;

// T5-R0 defines a recovery episode using only event positions. The restriction
// to recovery repair records is derived from machine enabledness, rather than
// included as an assumption in the episode predicate.

pub open spec fn recovery_episode(
    events: Seq<global_layer::GlobalEvent>,
    crash: nat,
    finish: nat,
) -> bool {
    crash < finish
        && finish < events.len()
        && events[crash as int] == global_layer::GlobalEvent::Crash
        && events[finish as int] == global_layer::GlobalEvent::FinishRecover
        && forall|index: nat| crash < index && index < finish ==>
            #[trigger] events[index as int]
                != global_layer::GlobalEvent::FinishRecover
}

pub open spec fn broker_linearization_is_recovery_repair(
    cfg: config_layer::FullConfig,
    before: p0_layer::State,
    event: global_layer::GlobalEvent,
) -> bool {
    match event {
        global_layer::GlobalEvent::BrokerLinearize { record } => {
            p3_layer::recovery_repair_record(
                cfg, before.core.broker.durable, record,
            )
        },
        global_layer::GlobalEvent::JournalAppendCall { .. }
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
        | global_layer::GlobalEvent::FinishRecover => true,
    }
}

pub open spec fn journal_linearization_is_recovery_repair(
    cfg: config_layer::FullConfig,
    before: journal_runtime_layer::JournalConfiguration,
    event: global_layer::GlobalEvent,
) -> bool {
    match event {
        global_layer::GlobalEvent::JournalAppendLinearize { record } => {
            p3_layer::recovery_repair_record(
                cfg, journal_runtime_layer::replay_view(cfg, before), record,
            )
        },
        global_layer::GlobalEvent::BrokerLinearize { .. }
        | global_layer::GlobalEvent::JournalAppendCall { .. }
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
        | global_layer::GlobalEvent::FinishRecover => true,
    }
}

pub open spec fn wal_linearization_is_recovery_repair(
    cfg: config_layer::FullConfig,
    before: wal_runtime_layer::WalConfiguration,
    event: global_layer::GlobalEvent,
) -> bool {
    match event {
        global_layer::GlobalEvent::WalWriteFull { record }
        | global_layer::GlobalEvent::WalFinishTorn { record } => {
            p3_layer::recovery_repair_record(
                cfg, wal_runtime_layer::replay_view(cfg, before), record,
            )
        },
        global_layer::GlobalEvent::BrokerLinearize { .. }
        | global_layer::GlobalEvent::JournalAppendCall { .. }
        | global_layer::GlobalEvent::JournalAppendLinearize { .. }
        | global_layer::GlobalEvent::JournalAppendReturn { .. }
        | global_layer::GlobalEvent::JournalDiskFull { .. }
        | global_layer::GlobalEvent::WalStage { .. }
        | global_layer::GlobalEvent::WalWriteTorn { .. }
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
        | global_layer::GlobalEvent::FinishRecover => true,
    }
}

pub proof fn non_online_enabled_record_is_recovery_repair(
    cfg: config_layer::FullConfig,
    durable: replay_layer::DurableBroker,
    mode: record_layer::Mode,
    slot: record_layer::ExecSlot,
    record: replay_layer::JournalRecord,
)
    requires
        mode != record_layer::Mode::Online,
        record_layer::durable_slot_update(
            config_layer::erase_config(cfg), durable, mode, slot, record,
        ).is_some(),
    ensures
        mode == record_layer::Mode::Recovering,
        p3_layer::recovery_repair_record(cfg, durable, record),
        t5_s0_layer::record_commit_delta(record).is_none(),
{
    match record {
        replay_layer::JournalRecord::FailRec { .. } => {},
        replay_layer::JournalRecord::UnknownRec { .. } => {},
        replay_layer::JournalRecord::Authorize { .. }
        | replay_layer::JournalRecord::Revoke { .. }
        | replay_layer::JournalRecord::Prepare { .. }
        | replay_layer::JournalRecord::Arm { .. }
        | replay_layer::JournalRecord::Start { .. }
        | replay_layer::JournalRecord::Outcome { .. }
        | replay_layer::JournalRecord::CommitRec { .. } => {
            assert(false);
        },
    }
}

pub proof fn prefix_with_same_length_is_equal<T>(
    first: Seq<T>,
    last: Seq<T>,
)
    requires
        append_layer::is_prefix(first, last),
        first.len() == last.len(),
    ensures first == last,
{
    assert(first == last.take(first.len() as int));
    append_layer::take_full(last);
}

pub open spec fn minimal_broker_recovery_execution(
    cfg: config_layer::FullConfig,
) -> execution_layer::BrokerExecution {
    let initial = p0_layer::initial_state(cfg);
    let crashed = p0_layer::apply(cfg, initial, p0_layer::Event::Crash);
    let recovering = p0_layer::apply(
        cfg, crashed, p0_layer::Event::BeginRecover,
    );
    let online = p0_layer::apply(
        cfg, recovering, p0_layer::Event::FinishRecover,
    );
    execution_layer::BrokerExecution {
        configs: Seq::empty()
            .push(initial)
            .push(crashed)
            .push(recovering)
            .push(online),
        events: Seq::empty()
            .push(global_layer::GlobalEvent::Crash)
            .push(global_layer::GlobalEvent::BeginRecover)
            .push(global_layer::GlobalEvent::FinishRecover),
    }
}

pub open spec fn repeated_crash_broker_recovery_execution(
    cfg: config_layer::FullConfig,
) -> execution_layer::BrokerExecution {
    let initial = p0_layer::initial_state(cfg);
    let crashed_once = p0_layer::apply(
        cfg, initial, p0_layer::Event::Crash,
    );
    let recovering_once = p0_layer::apply(
        cfg, crashed_once, p0_layer::Event::BeginRecover,
    );
    let crashed_twice = p0_layer::apply(
        cfg, recovering_once, p0_layer::Event::Crash,
    );
    let recovering_twice = p0_layer::apply(
        cfg, crashed_twice, p0_layer::Event::BeginRecover,
    );
    let online = p0_layer::apply(
        cfg, recovering_twice, p0_layer::Event::FinishRecover,
    );
    execution_layer::BrokerExecution {
        configs: Seq::empty()
            .push(initial)
            .push(crashed_once)
            .push(recovering_once)
            .push(crashed_twice)
            .push(recovering_twice)
            .push(online),
        events: Seq::empty()
            .push(global_layer::GlobalEvent::Crash)
            .push(global_layer::GlobalEvent::BeginRecover)
            .push(global_layer::GlobalEvent::Crash)
            .push(global_layer::GlobalEvent::BeginRecover)
            .push(global_layer::GlobalEvent::FinishRecover),
    }
}

pub open spec fn minimal_journal_recovery_execution(
    cfg: config_layer::FullConfig,
) -> journal_runtime_layer::JournalExecution {
    let initial = journal_runtime_layer::initial_configuration(cfg);
    let crashed = journal_runtime_layer::apply(
        cfg, initial, journal_runtime_layer::JournalEvent::Crash,
    );
    let recovering = journal_runtime_layer::apply(
        cfg, crashed, journal_runtime_layer::JournalEvent::BeginRecover,
    );
    let online = journal_runtime_layer::apply(
        cfg, recovering, journal_runtime_layer::JournalEvent::FinishRecover,
    );
    journal_runtime_layer::JournalExecution {
        configs: Seq::empty()
            .push(initial)
            .push(crashed)
            .push(recovering)
            .push(online),
        events: Seq::empty()
            .push(global_layer::GlobalEvent::Crash)
            .push(global_layer::GlobalEvent::BeginRecover)
            .push(global_layer::GlobalEvent::FinishRecover),
    }
}

pub open spec fn minimal_wal_recovery_execution(
    cfg: config_layer::FullConfig,
) -> wal_runtime_layer::WalExecution {
    let initial = wal_runtime_layer::initial_configuration(cfg);
    let crashed = wal_runtime_layer::apply(
        cfg, initial, wal_runtime_layer::WalEvent::Crash,
    );
    let scanning = wal_runtime_layer::apply(
        cfg, crashed, wal_runtime_layer::WalEvent::BeginScan,
    );
    let scanned = wal_runtime_layer::apply(
        cfg, scanning, wal_runtime_layer::WalEvent::FinishScan,
    );
    let truncated = wal_runtime_layer::apply(
        cfg, scanned, wal_runtime_layer::WalEvent::TruncateTail,
    );
    let recovering = wal_runtime_layer::apply(
        cfg, truncated, wal_runtime_layer::WalEvent::BeginRecover,
    );
    let online = wal_runtime_layer::apply(
        cfg, recovering, wal_runtime_layer::WalEvent::FinishRecover,
    );
    wal_runtime_layer::WalExecution {
        configs: Seq::empty()
            .push(initial)
            .push(crashed)
            .push(scanning)
            .push(scanned)
            .push(truncated)
            .push(recovering)
            .push(online),
        events: Seq::empty()
            .push(global_layer::GlobalEvent::Crash)
            .push(global_layer::GlobalEvent::BeginScan)
            .push(global_layer::GlobalEvent::FinishScan)
            .push(global_layer::GlobalEvent::TruncateTail)
            .push(global_layer::GlobalEvent::BeginRecover)
            .push(global_layer::GlobalEvent::FinishRecover),
    }
}

pub proof fn initial_recovery_is_complete(
    cfg: config_layer::FullConfig,
)
    ensures
        query_layer::recovery_complete_d(
            config_layer::erase_config(cfg),
            replay_layer::initial_durable(config_layer::erase_config(cfg)),
        ),
        query_layer::recovery_complete_j(
            config_layer::erase_config(cfg), Seq::empty(),
        ),
{
    assert forall|request: replay_layer::RequestId|
        !#[trigger] query_layer::unsafe_uncontrolled_d(
            config_layer::erase_config(cfg),
            replay_layer::initial_durable(config_layer::erase_config(cfg)),
            request,
        )
            && !(replay_layer::initial_durable(
                    config_layer::erase_config(cfg),
                ).phase[request] == replay_layer::Phase::Armed
                && query_layer::d_failure_conclusive(
                    config_layer::erase_config(cfg),
                    replay_layer::initial_durable(
                        config_layer::erase_config(cfg),
                    ),
                    request,
                )) by {
    }
    assert(replay_layer::replay(
        config_layer::erase_config(cfg), Seq::empty(),
    ) == replay_layer::initial_durable(config_layer::erase_config(cfg)));
}

pub proof fn minimal_broker_recovery_episode_is_inhabited(
    cfg: config_layer::FullConfig,
)
    ensures
        execution_layer::exec(cfg, minimal_broker_recovery_execution(cfg)),
        recovery_episode(
            minimal_broker_recovery_execution(cfg).events, 0, 2,
        ),
{
    let execution = minimal_broker_recovery_execution(cfg);
    initial_recovery_is_complete(cfg);
    assert(execution.events.len() == 3);
    assert(execution.configs.len() == 4);
    assert(execution.configs[0] == p0_layer::initial_state(cfg));
    assert forall|index: nat| index < execution.events.len() implies
        #[trigger] execution_layer::broker_step(
            cfg,
            execution.configs[index as int],
            execution.events[index as int],
            execution.configs[(index + 1) as int],
        ) by {
        if index == 0 {
        } else if index == 1 {
        } else {
            assert(index == 2);
            assert(query_layer::recovery_complete_d(
                config_layer::erase_config(cfg),
                execution.configs[index as int].core.broker.durable,
            ));
        }
    }
}

pub proof fn repeated_crash_broker_recovery_episode_is_inhabited(
    cfg: config_layer::FullConfig,
)
    ensures
        execution_layer::exec(
            cfg, repeated_crash_broker_recovery_execution(cfg),
        ),
        recovery_episode(
            repeated_crash_broker_recovery_execution(cfg).events, 0, 4,
        ),
{
    let execution = repeated_crash_broker_recovery_execution(cfg);
    initial_recovery_is_complete(cfg);
    assert(execution.events.len() == 5);
    assert(execution.configs.len() == 6);
    assert(execution.configs[0] == p0_layer::initial_state(cfg));
    assert forall|index: nat| index < execution.events.len() implies
        #[trigger] execution_layer::broker_step(
            cfg,
            execution.configs[index as int],
            execution.events[index as int],
            execution.configs[(index + 1) as int],
        ) by {
        if index == 0 {
        } else if index == 1 {
        } else if index == 2 {
        } else if index == 3 {
        } else {
            assert(index == 4);
            assert(query_layer::recovery_complete_d(
                config_layer::erase_config(cfg),
                execution.configs[index as int].core.broker.durable,
            ));
        }
    }
}

pub proof fn minimal_journal_recovery_episode_is_inhabited(
    cfg: config_layer::FullConfig,
)
    ensures
        journal_runtime_layer::exec(
            cfg, minimal_journal_recovery_execution(cfg),
        ),
        recovery_episode(
            minimal_journal_recovery_execution(cfg).events, 0, 2,
        ),
{
    let execution = minimal_journal_recovery_execution(cfg);
    initial_recovery_is_complete(cfg);
    assert(execution.events.len() == 3);
    assert(execution.configs.len() == 4);
    assert(execution.configs[0]
        == journal_runtime_layer::initial_configuration(cfg));
    assert forall|index: nat| index < execution.events.len() implies
        #[trigger] journal_runtime_layer::journal_runtime_step(
            cfg,
            execution.configs[index as int],
            execution.events[index as int],
            execution.configs[(index + 1) as int],
        ) by {
        if index == 0 {
        } else if index == 1 {
        } else {
            assert(index == 2);
            assert(query_layer::recovery_complete_j(
                config_layer::erase_config(cfg),
                journal_runtime_layer::journal_view(
                    execution.configs[index as int],
                ),
            ));
        }
    }
}

pub proof fn minimal_wal_recovery_episode_is_inhabited(
    cfg: config_layer::FullConfig,
)
    ensures
        wal_runtime_layer::exec(cfg, minimal_wal_recovery_execution(cfg)),
        recovery_episode(
            minimal_wal_recovery_execution(cfg).events, 0, 5,
        ),
{
    let execution = minimal_wal_recovery_execution(cfg);
    initial_recovery_is_complete(cfg);
    assert(execution.events.len() == 6);
    assert(execution.configs.len() == 7);
    assert(execution.configs[0]
        == wal_runtime_layer::initial_configuration(cfg));
    assert forall|index: nat| index < execution.events.len() implies
        #[trigger] wal_runtime_layer::wal_runtime_step(
            cfg,
            execution.configs[index as int],
            execution.events[index as int],
            execution.configs[(index + 1) as int],
        ) by {
        if index == 0 {
        } else if index == 1 {
        } else if index == 2 {
        } else if index == 3 {
        } else if index == 4 {
        } else {
            assert(index == 5);
            assert(query_layer::recovery_complete_j(
                config_layer::erase_config(cfg),
                wal_runtime_layer::journal_view(
                    execution.configs[index as int],
                ),
            ));
        }
    }
}

pub proof fn broker_non_online_non_finish_step_preserves_mode(
    cfg: config_layer::FullConfig,
    before: p0_layer::State,
    event: global_layer::GlobalEvent,
    after: p0_layer::State,
)
    requires
        execution_layer::broker_step(cfg, before, event, after),
        before.core.broker.mode != record_layer::Mode::Online,
        event != global_layer::GlobalEvent::FinishRecover,
    ensures after.core.broker.mode != record_layer::Mode::Online,
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

pub proof fn journal_non_online_non_finish_step_preserves_mode(
    cfg: config_layer::FullConfig,
    before: journal_runtime_layer::JournalConfiguration,
    event: global_layer::GlobalEvent,
    after: journal_runtime_layer::JournalConfiguration,
)
    requires
        journal_runtime_layer::journal_runtime_step(cfg, before, event, after),
        before.runtime.mode != record_layer::Mode::Online,
        event != global_layer::GlobalEvent::FinishRecover,
    ensures after.runtime.mode != record_layer::Mode::Online,
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

pub proof fn wal_non_online_non_finish_step_preserves_mode(
    cfg: config_layer::FullConfig,
    before: wal_runtime_layer::WalConfiguration,
    event: global_layer::GlobalEvent,
    after: wal_runtime_layer::WalConfiguration,
)
    requires
        wal_runtime_layer::wal_runtime_step(cfg, before, event, after),
        before.runtime.mode != record_layer::Mode::Online,
        event != global_layer::GlobalEvent::FinishRecover,
    ensures after.runtime.mode != record_layer::Mode::Online,
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

pub proof fn broker_non_online_step_is_commit_stutter(
    cfg: config_layer::FullConfig,
    before: p0_layer::State,
    event: global_layer::GlobalEvent,
    after: p0_layer::State,
)
    requires
        execution_layer::broker_step(cfg, before, event, after),
        before.core.broker.mode != record_layer::Mode::Online,
    ensures
        broker_linearization_is_recovery_repair(cfg, before, event),
        t5_s0_layer::broker_commit_delta(event).is_none(),
        t5_s0_layer::alpha_commit_broker(after)
            == t5_s0_layer::alpha_commit_broker(before),
{
    t5_s0_layer::broker_step_commit_history_exact(cfg, before, event, after);
    match event {
        global_layer::GlobalEvent::BrokerLinearize { record } => {
            assert(global_layer::broker_decode(event) == Option::Some(
                p0_layer::Event::BrokerLinearize { record },
            ));
            assert(p0_layer::physical_step(
                cfg, before, p0_layer::Event::BrokerLinearize { record }, after,
            ));
            assert(p0_layer::admissibly_enabled(
                cfg, before, p0_layer::Event::BrokerLinearize { record },
            ));
            assert(record_layer::abstract_enabled(
                config_layer::erase_config(cfg), before.core.broker, record,
            ));
            assert(record_layer::durable_slot_update(
                config_layer::erase_config(cfg),
                before.core.broker.durable,
                before.core.broker.mode,
                before.core.broker.slot,
                record,
            ).is_some());
            non_online_enabled_record_is_recovery_repair(
                cfg,
                before.core.broker.durable,
                before.core.broker.mode,
                before.core.broker.slot,
                record,
            );
        },
        global_layer::GlobalEvent::JournalAppendCall { .. }
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

pub proof fn journal_non_online_step_is_commit_stutter(
    cfg: config_layer::FullConfig,
    before: journal_runtime_layer::JournalConfiguration,
    event: global_layer::GlobalEvent,
    after: journal_runtime_layer::JournalConfiguration,
)
    requires
        journal_runtime_layer::journal_runtime_step(cfg, before, event, after),
        before.runtime.mode != record_layer::Mode::Online,
    ensures
        journal_linearization_is_recovery_repair(cfg, before, event),
        t5_s0_layer::journal_commit_delta(event).is_none(),
        t5_s0_layer::alpha_commit_journal(cfg, after)
            == t5_s0_layer::alpha_commit_journal(cfg, before),
{
    t5_s0_layer::journal_step_commit_history_exact(cfg, before, event, after);
    match event {
        global_layer::GlobalEvent::JournalAppendLinearize { record } => {
            assert(journal_runtime_layer::journal_decode(event) == Option::Some(
                journal_runtime_layer::JournalEvent::JournalAppendLinearize {
                    record,
                },
            ));
            assert(journal_runtime_layer::journal_local_step(
                cfg,
                before,
                journal_runtime_layer::JournalEvent::JournalAppendLinearize {
                    record,
                },
                after,
            ));
            assert(journal_runtime_layer::runtime_record_enabled(
                cfg, before, record,
            ));
            assert(journal_runtime_layer::runtime_slot_update(
                cfg, before, record,
            ).is_some());
            non_online_enabled_record_is_recovery_repair(
                cfg,
                journal_runtime_layer::replay_view(cfg, before),
                before.runtime.mode,
                before.runtime.slot,
                record,
            );
        },
        global_layer::GlobalEvent::BrokerLinearize { .. }
        | global_layer::GlobalEvent::JournalAppendCall { .. }
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

pub proof fn wal_non_online_step_is_commit_stutter(
    cfg: config_layer::FullConfig,
    before: wal_runtime_layer::WalConfiguration,
    event: global_layer::GlobalEvent,
    after: wal_runtime_layer::WalConfiguration,
)
    requires
        wal_runtime_layer::wal_invariant(
            cfg,
            before.runtime.store,
            before.runtime.mode,
            before.runtime.append,
        ),
        wal_runtime_layer::wal_runtime_step(cfg, before, event, after),
        before.runtime.mode != record_layer::Mode::Online,
    ensures
        wal_linearization_is_recovery_repair(cfg, before, event),
        t5_s0_layer::wal_commit_delta(event).is_none(),
        t5_s0_layer::alpha_commit_wal(cfg, after)
            == t5_s0_layer::alpha_commit_wal(cfg, before),
{
    t5_s0_layer::wal_step_commit_history_exact(cfg, before, event, after);
    match event {
        global_layer::GlobalEvent::WalWriteFull { record }
        | global_layer::GlobalEvent::WalFinishTorn { record } => {
            assert(wal_runtime_layer::runtime_record_enabled(
                cfg, before, record,
            ));
            assert(journal_runtime_layer::runtime_slot_update(
                cfg, wal_runtime_layer::journal_projection(before), record,
            ).is_some());
            non_online_enabled_record_is_recovery_repair(
                cfg,
                wal_runtime_layer::replay_view(cfg, before),
                before.runtime.mode,
                before.runtime.slot,
                record,
            );
        },
        global_layer::GlobalEvent::BrokerLinearize { .. }
        | global_layer::GlobalEvent::JournalAppendCall { .. }
        | global_layer::GlobalEvent::JournalAppendLinearize { .. }
        | global_layer::GlobalEvent::JournalAppendReturn { .. }
        | global_layer::GlobalEvent::JournalDiskFull { .. }
        | global_layer::GlobalEvent::WalStage { .. }
        | global_layer::GlobalEvent::WalWriteTorn { .. }
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

pub proof fn broker_recovery_episode_prefix_invariant(
    cfg: config_layer::FullConfig,
    execution: execution_layer::BrokerExecution,
    crash: nat,
    finish: nat,
    index: nat,
)
    requires
        execution_layer::exec(cfg, execution),
        recovery_episode(execution.events, crash, finish),
        crash < index,
        index <= finish,
    ensures
        execution.configs[index as int].core.broker.mode
            != record_layer::Mode::Online,
        t5_s0_layer::alpha_commit_broker(
            execution.configs[crash as int],
        ).len() == t5_s0_layer::alpha_commit_broker(
            execution.configs[index as int],
        ).len(),
    decreases index - crash,
{
    if index == crash + 1 {
        assert(crash < execution.events.len());
        assert(execution.events[crash as int]
            == global_layer::GlobalEvent::Crash);
        assert(execution_layer::broker_step(
            cfg,
            execution.configs[crash as int],
            execution.events[crash as int],
            execution.configs[index as int],
        ));
        t5_s0_layer::broker_step_commit_history_exact(
            cfg,
            execution.configs[crash as int],
            execution.events[crash as int],
            execution.configs[index as int],
        );
        assert(t5_s0_layer::broker_commit_delta(
            execution.events[crash as int],
        ).is_none());
    } else {
        let previous: nat = (index - 1) as nat;
        assert(crash < previous);
        assert(previous < index);
        assert(previous < finish);
        assert(index == previous + 1);
        assert(previous < execution.events.len());
        broker_recovery_episode_prefix_invariant(
            cfg, execution, crash, finish, previous,
        );
        assert(execution.events[previous as int]
            != global_layer::GlobalEvent::FinishRecover);
        assert(execution_layer::broker_step(
            cfg,
            execution.configs[previous as int],
            execution.events[previous as int],
            execution.configs[index as int],
        ));
        broker_non_online_non_finish_step_preserves_mode(
            cfg,
            execution.configs[previous as int],
            execution.events[previous as int],
            execution.configs[index as int],
        );
        broker_non_online_step_is_commit_stutter(
            cfg,
            execution.configs[previous as int],
            execution.events[previous as int],
            execution.configs[index as int],
        );
    }
}

pub proof fn journal_recovery_episode_prefix_invariant(
    cfg: config_layer::FullConfig,
    execution: journal_runtime_layer::JournalExecution,
    crash: nat,
    finish: nat,
    index: nat,
)
    requires
        journal_runtime_layer::exec(cfg, execution),
        recovery_episode(execution.events, crash, finish),
        crash < index,
        index <= finish,
    ensures
        execution.configs[index as int].runtime.mode
            != record_layer::Mode::Online,
        t5_s0_layer::alpha_commit_journal(
            cfg, execution.configs[crash as int],
        ).len() == t5_s0_layer::alpha_commit_journal(
            cfg, execution.configs[index as int],
        ).len(),
    decreases index - crash,
{
    if index == crash + 1 {
        assert(crash < execution.events.len());
        assert(execution.events[crash as int]
            == global_layer::GlobalEvent::Crash);
        assert(journal_runtime_layer::journal_runtime_step(
            cfg,
            execution.configs[crash as int],
            execution.events[crash as int],
            execution.configs[index as int],
        ));
        t5_s0_layer::journal_step_commit_history_exact(
            cfg,
            execution.configs[crash as int],
            execution.events[crash as int],
            execution.configs[index as int],
        );
        assert(t5_s0_layer::journal_commit_delta(
            execution.events[crash as int],
        ).is_none());
    } else {
        let previous: nat = (index - 1) as nat;
        assert(crash < previous);
        assert(previous < index);
        assert(previous < finish);
        assert(index == previous + 1);
        assert(previous < execution.events.len());
        journal_recovery_episode_prefix_invariant(
            cfg, execution, crash, finish, previous,
        );
        assert(execution.events[previous as int]
            != global_layer::GlobalEvent::FinishRecover);
        assert(journal_runtime_layer::journal_runtime_step(
            cfg,
            execution.configs[previous as int],
            execution.events[previous as int],
            execution.configs[index as int],
        ));
        journal_non_online_non_finish_step_preserves_mode(
            cfg,
            execution.configs[previous as int],
            execution.events[previous as int],
            execution.configs[index as int],
        );
        journal_non_online_step_is_commit_stutter(
            cfg,
            execution.configs[previous as int],
            execution.events[previous as int],
            execution.configs[index as int],
        );
    }
}

pub proof fn wal_recovery_episode_prefix_invariant(
    cfg: config_layer::FullConfig,
    execution: wal_runtime_layer::WalExecution,
    crash: nat,
    finish: nat,
    index: nat,
)
    requires
        wal_runtime_layer::exec(cfg, execution),
        recovery_episode(execution.events, crash, finish),
        crash < index,
        index <= finish,
    ensures
        execution.configs[index as int].runtime.mode
            != record_layer::Mode::Online,
        t5_s0_layer::alpha_commit_wal(
            cfg, execution.configs[crash as int],
        ).len() == t5_s0_layer::alpha_commit_wal(
            cfg, execution.configs[index as int],
        ).len(),
    decreases index - crash,
{
    wal_runtime_layer::every_exec_configuration_is_basic(cfg, execution);
    if index == crash + 1 {
        assert(crash < execution.events.len());
        assert(execution.events[crash as int]
            == global_layer::GlobalEvent::Crash);
        assert(wal_runtime_layer::basic_invariant(
            cfg, execution.configs[crash as int],
        ));
        assert(wal_runtime_layer::wal_invariant(
            cfg,
            execution.configs[crash as int].runtime.store,
            execution.configs[crash as int].runtime.mode,
            execution.configs[crash as int].runtime.append,
        ));
        assert(wal_runtime_layer::wal_runtime_step(
            cfg,
            execution.configs[crash as int],
            execution.events[crash as int],
            execution.configs[index as int],
        ));
        t5_s0_layer::wal_step_commit_history_exact(
            cfg,
            execution.configs[crash as int],
            execution.events[crash as int],
            execution.configs[index as int],
        );
        assert(t5_s0_layer::wal_commit_delta(
            execution.events[crash as int],
        ).is_none());
    } else {
        let previous: nat = (index - 1) as nat;
        assert(crash < previous);
        assert(previous < index);
        assert(previous < finish);
        assert(index == previous + 1);
        assert(previous < execution.events.len());
        wal_recovery_episode_prefix_invariant(
            cfg, execution, crash, finish, previous,
        );
        assert(execution.events[previous as int]
            != global_layer::GlobalEvent::FinishRecover);
        assert(wal_runtime_layer::basic_invariant(
            cfg, execution.configs[previous as int],
        ));
        assert(wal_runtime_layer::wal_invariant(
            cfg,
            execution.configs[previous as int].runtime.store,
            execution.configs[previous as int].runtime.mode,
            execution.configs[previous as int].runtime.append,
        ));
        assert(wal_runtime_layer::wal_runtime_step(
            cfg,
            execution.configs[previous as int],
            execution.events[previous as int],
            execution.configs[index as int],
        ));
        wal_non_online_non_finish_step_preserves_mode(
            cfg,
            execution.configs[previous as int],
            execution.events[previous as int],
            execution.configs[index as int],
        );
        wal_non_online_step_is_commit_stutter(
            cfg,
            execution.configs[previous as int],
            execution.events[previous as int],
            execution.configs[index as int],
        );
    }
}

pub proof fn broker_recovery_episode_step_is_commit_stutter(
    cfg: config_layer::FullConfig,
    execution: execution_layer::BrokerExecution,
    crash: nat,
    finish: nat,
    index: nat,
)
    requires
        execution_layer::exec(cfg, execution),
        recovery_episode(execution.events, crash, finish),
        crash <= index,
        index <= finish,
    ensures
        broker_linearization_is_recovery_repair(
            cfg,
            execution.configs[index as int],
            execution.events[index as int],
        ),
        t5_s0_layer::broker_commit_delta(
            execution.events[index as int],
        ).is_none(),
        t5_s0_layer::alpha_commit_broker(
            execution.configs[(index + 1) as int],
        ) == t5_s0_layer::alpha_commit_broker(
            execution.configs[index as int],
        ),
{
    assert(index < execution.events.len());
    assert(execution_layer::broker_step(
        cfg,
        execution.configs[index as int],
        execution.events[index as int],
        execution.configs[(index + 1) as int],
    ));
    if index == crash {
        assert(execution.events[index as int]
            == global_layer::GlobalEvent::Crash);
        t5_s0_layer::broker_step_commit_history_exact(
            cfg,
            execution.configs[index as int],
            execution.events[index as int],
            execution.configs[(index + 1) as int],
        );
    } else if index == finish {
        assert(execution.events[index as int]
            == global_layer::GlobalEvent::FinishRecover);
        t5_s0_layer::broker_step_commit_history_exact(
            cfg,
            execution.configs[index as int],
            execution.events[index as int],
            execution.configs[(index + 1) as int],
        );
    } else {
        assert(crash < index);
        assert(index < finish);
        broker_recovery_episode_prefix_invariant(
            cfg, execution, crash, finish, index,
        );
        broker_non_online_step_is_commit_stutter(
            cfg,
            execution.configs[index as int],
            execution.events[index as int],
            execution.configs[(index + 1) as int],
        );
    }
}

pub proof fn journal_recovery_episode_step_is_commit_stutter(
    cfg: config_layer::FullConfig,
    execution: journal_runtime_layer::JournalExecution,
    crash: nat,
    finish: nat,
    index: nat,
)
    requires
        journal_runtime_layer::exec(cfg, execution),
        recovery_episode(execution.events, crash, finish),
        crash <= index,
        index <= finish,
    ensures
        journal_linearization_is_recovery_repair(
            cfg,
            execution.configs[index as int],
            execution.events[index as int],
        ),
        t5_s0_layer::journal_commit_delta(
            execution.events[index as int],
        ).is_none(),
        t5_s0_layer::alpha_commit_journal(
            cfg, execution.configs[(index + 1) as int],
        ) == t5_s0_layer::alpha_commit_journal(
            cfg, execution.configs[index as int],
        ),
{
    assert(index < execution.events.len());
    assert(journal_runtime_layer::journal_runtime_step(
        cfg,
        execution.configs[index as int],
        execution.events[index as int],
        execution.configs[(index + 1) as int],
    ));
    if index == crash {
        assert(execution.events[index as int]
            == global_layer::GlobalEvent::Crash);
        t5_s0_layer::journal_step_commit_history_exact(
            cfg,
            execution.configs[index as int],
            execution.events[index as int],
            execution.configs[(index + 1) as int],
        );
    } else if index == finish {
        assert(execution.events[index as int]
            == global_layer::GlobalEvent::FinishRecover);
        t5_s0_layer::journal_step_commit_history_exact(
            cfg,
            execution.configs[index as int],
            execution.events[index as int],
            execution.configs[(index + 1) as int],
        );
    } else {
        assert(crash < index);
        assert(index < finish);
        journal_recovery_episode_prefix_invariant(
            cfg, execution, crash, finish, index,
        );
        journal_non_online_step_is_commit_stutter(
            cfg,
            execution.configs[index as int],
            execution.events[index as int],
            execution.configs[(index + 1) as int],
        );
    }
}

pub proof fn wal_recovery_episode_step_is_commit_stutter(
    cfg: config_layer::FullConfig,
    execution: wal_runtime_layer::WalExecution,
    crash: nat,
    finish: nat,
    index: nat,
)
    requires
        wal_runtime_layer::exec(cfg, execution),
        recovery_episode(execution.events, crash, finish),
        crash <= index,
        index <= finish,
    ensures
        wal_linearization_is_recovery_repair(
            cfg,
            execution.configs[index as int],
            execution.events[index as int],
        ),
        t5_s0_layer::wal_commit_delta(
            execution.events[index as int],
        ).is_none(),
        t5_s0_layer::alpha_commit_wal(
            cfg, execution.configs[(index + 1) as int],
        ) == t5_s0_layer::alpha_commit_wal(
            cfg, execution.configs[index as int],
        ),
{
    wal_runtime_layer::every_exec_configuration_is_basic(cfg, execution);
    assert(index < execution.events.len());
    assert(wal_runtime_layer::basic_invariant(
        cfg, execution.configs[index as int],
    ));
    assert(wal_runtime_layer::wal_invariant(
        cfg,
        execution.configs[index as int].runtime.store,
        execution.configs[index as int].runtime.mode,
        execution.configs[index as int].runtime.append,
    ));
    assert(wal_runtime_layer::wal_runtime_step(
        cfg,
        execution.configs[index as int],
        execution.events[index as int],
        execution.configs[(index + 1) as int],
    ));
    if index == crash {
        assert(execution.events[index as int]
            == global_layer::GlobalEvent::Crash);
        t5_s0_layer::wal_step_commit_history_exact(
            cfg,
            execution.configs[index as int],
            execution.events[index as int],
            execution.configs[(index + 1) as int],
        );
    } else if index == finish {
        assert(execution.events[index as int]
            == global_layer::GlobalEvent::FinishRecover);
        t5_s0_layer::wal_step_commit_history_exact(
            cfg,
            execution.configs[index as int],
            execution.events[index as int],
            execution.configs[(index + 1) as int],
        );
    } else {
        assert(crash < index);
        assert(index < finish);
        wal_recovery_episode_prefix_invariant(
            cfg, execution, crash, finish, index,
        );
        wal_non_online_step_is_commit_stutter(
            cfg,
            execution.configs[index as int],
            execution.events[index as int],
            execution.configs[(index + 1) as int],
        );
    }
}

pub proof fn broker_recovery_episode_commit_history_equal(
    cfg: config_layer::FullConfig,
    execution: execution_layer::BrokerExecution,
    crash: nat,
    finish: nat,
)
    requires
        execution_layer::exec(cfg, execution),
        recovery_episode(execution.events, crash, finish),
    ensures t5_s0_layer::alpha_commit_broker(
        execution.configs[crash as int],
    ) == t5_s0_layer::alpha_commit_broker(
        execution.configs[(finish + 1) as int],
    ),
{
    broker_recovery_episode_prefix_invariant(
        cfg, execution, crash, finish, finish,
    );
    assert(finish < execution.events.len());
    assert(finish + 1 < execution.configs.len());
    assert(execution.events[finish as int]
        == global_layer::GlobalEvent::FinishRecover);
    assert(execution_layer::broker_step(
        cfg,
        execution.configs[finish as int],
        execution.events[finish as int],
        execution.configs[(finish + 1) as int],
    ));
    t5_s0_layer::broker_step_commit_history_exact(
        cfg,
        execution.configs[finish as int],
        execution.events[finish as int],
        execution.configs[(finish + 1) as int],
    );
    assert(t5_s0_layer::broker_commit_delta(
        execution.events[finish as int],
    ).is_none());
    t5_e0_layer::broker_execution_commit_history_monotone_between(
        cfg, execution, crash, finish + 1,
    );
    prefix_with_same_length_is_equal(
        t5_s0_layer::alpha_commit_broker(
            execution.configs[crash as int],
        ),
        t5_s0_layer::alpha_commit_broker(
            execution.configs[(finish + 1) as int],
        ),
    );
}

pub proof fn journal_recovery_episode_commit_history_equal(
    cfg: config_layer::FullConfig,
    execution: journal_runtime_layer::JournalExecution,
    crash: nat,
    finish: nat,
)
    requires
        journal_runtime_layer::exec(cfg, execution),
        recovery_episode(execution.events, crash, finish),
    ensures t5_s0_layer::alpha_commit_journal(
        cfg, execution.configs[crash as int],
    ) == t5_s0_layer::alpha_commit_journal(
        cfg, execution.configs[(finish + 1) as int],
    ),
{
    journal_recovery_episode_prefix_invariant(
        cfg, execution, crash, finish, finish,
    );
    assert(finish < execution.events.len());
    assert(finish + 1 < execution.configs.len());
    assert(execution.events[finish as int]
        == global_layer::GlobalEvent::FinishRecover);
    assert(journal_runtime_layer::journal_runtime_step(
        cfg,
        execution.configs[finish as int],
        execution.events[finish as int],
        execution.configs[(finish + 1) as int],
    ));
    t5_s0_layer::journal_step_commit_history_exact(
        cfg,
        execution.configs[finish as int],
        execution.events[finish as int],
        execution.configs[(finish + 1) as int],
    );
    assert(t5_s0_layer::journal_commit_delta(
        execution.events[finish as int],
    ).is_none());
    t5_e0_layer::journal_execution_commit_history_monotone_between(
        cfg, execution, crash, finish + 1,
    );
    prefix_with_same_length_is_equal(
        t5_s0_layer::alpha_commit_journal(
            cfg, execution.configs[crash as int],
        ),
        t5_s0_layer::alpha_commit_journal(
            cfg, execution.configs[(finish + 1) as int],
        ),
    );
}

pub proof fn wal_recovery_episode_commit_history_equal(
    cfg: config_layer::FullConfig,
    execution: wal_runtime_layer::WalExecution,
    crash: nat,
    finish: nat,
)
    requires
        wal_runtime_layer::exec(cfg, execution),
        recovery_episode(execution.events, crash, finish),
    ensures t5_s0_layer::alpha_commit_wal(
        cfg, execution.configs[crash as int],
    ) == t5_s0_layer::alpha_commit_wal(
        cfg, execution.configs[(finish + 1) as int],
    ),
{
    wal_recovery_episode_prefix_invariant(
        cfg, execution, crash, finish, finish,
    );
    wal_runtime_layer::every_exec_configuration_is_basic(cfg, execution);
    assert(finish < execution.events.len());
    assert(finish + 1 < execution.configs.len());
    assert(execution.events[finish as int]
        == global_layer::GlobalEvent::FinishRecover);
    assert(wal_runtime_layer::basic_invariant(
        cfg, execution.configs[finish as int],
    ));
    assert(wal_runtime_layer::wal_invariant(
        cfg,
        execution.configs[finish as int].runtime.store,
        execution.configs[finish as int].runtime.mode,
        execution.configs[finish as int].runtime.append,
    ));
    assert(wal_runtime_layer::wal_runtime_step(
        cfg,
        execution.configs[finish as int],
        execution.events[finish as int],
        execution.configs[(finish + 1) as int],
    ));
    t5_s0_layer::wal_step_commit_history_exact(
        cfg,
        execution.configs[finish as int],
        execution.events[finish as int],
        execution.configs[(finish + 1) as int],
    );
    assert(t5_s0_layer::wal_commit_delta(
        execution.events[finish as int],
    ).is_none());
    t5_e0_layer::wal_execution_commit_history_monotone_between(
        cfg, execution, crash, finish + 1,
    );
    prefix_with_same_length_is_equal(
        t5_s0_layer::alpha_commit_wal(
            cfg, execution.configs[crash as int],
        ),
        t5_s0_layer::alpha_commit_wal(
            cfg, execution.configs[(finish + 1) as int],
        ),
    );
}

} // verus!
