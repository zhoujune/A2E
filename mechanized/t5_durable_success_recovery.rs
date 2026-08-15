use vstd::prelude::*;

#[path = "t5_commit_recovery.rs"]
pub mod t5_r0_layer;

verus! {

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
use p3_layer::p2_layer::p1_layer::p0_layer;
use p0_layer::config_layer;
use config_layer::broker_layer as record_layer;
use record_layer::query_layer;
use query_layer::c1_layer;
use c1_layer::replay_layer;
use c1_layer::append_layer;

// T5-R1 spike: recovery may expose a Commit only when the typed durable state
// already contains its matching successful Outcome.  The endpoint property is
// therefore monotone extension, while T5-R0's equality remains the explicit
// no-recovery-Commit corollary.

pub open spec fn wal_recovery_resolution_is_durably_backed(
    cfg: config_layer::FullConfig,
    before: wal_runtime_layer::WalConfiguration,
    event: global_layer::GlobalEvent,
) -> bool {
    match event {
        global_layer::GlobalEvent::WalWriteFull { record }
        | global_layer::GlobalEvent::WalFinishTorn { record } => {
            t5_r0_layer::recovery_commit_backed_by_durable_success(
                wal_runtime_layer::replay_view(cfg, before), record,
            )
        },
        _ => true,
    }
}

pub open spec fn recovery_resolution_record(
    record: replay_layer::JournalRecord,
) -> bool {
    match record {
        replay_layer::JournalRecord::CommitRec { .. }
        | replay_layer::JournalRecord::FailRec { .. }
        | replay_layer::JournalRecord::UnknownRec { .. } => true,
        replay_layer::JournalRecord::Authorize { .. }
        | replay_layer::JournalRecord::Revoke { .. }
        | replay_layer::JournalRecord::Prepare { .. }
        | replay_layer::JournalRecord::Arm { .. }
        | replay_layer::JournalRecord::Start { .. }
        | replay_layer::JournalRecord::Outcome { .. } => false,
    }
}

/// The formal recovery decision alphabet.  The class is derived from the
/// typed terminal record rather than from an implementation-side string or
/// error code; `NotRecovery` is the explicit result for ordinary records.
#[derive(PartialEq, Eq, Clone, Copy)]
pub enum RecoveryDecisionClass {
    Commit,
    Fail,
    Unknown,
    NotRecovery,
}

pub open spec fn recovery_decision_class(
    record: replay_layer::JournalRecord,
) -> RecoveryDecisionClass {
    match record {
        replay_layer::JournalRecord::CommitRec { .. } =>
            RecoveryDecisionClass::Commit,
        replay_layer::JournalRecord::FailRec { .. } =>
            RecoveryDecisionClass::Fail,
        replay_layer::JournalRecord::UnknownRec { .. } =>
            RecoveryDecisionClass::Unknown,
        replay_layer::JournalRecord::Authorize { .. }
        | replay_layer::JournalRecord::Revoke { .. }
        | replay_layer::JournalRecord::Prepare { .. }
        | replay_layer::JournalRecord::Arm { .. }
        | replay_layer::JournalRecord::Start { .. }
        | replay_layer::JournalRecord::Outcome { .. } =>
            RecoveryDecisionClass::NotRecovery,
    }
}

pub open spec fn recovery_decision_for_event(
    event: global_layer::GlobalEvent,
) -> RecoveryDecisionClass {
    match event {
        global_layer::GlobalEvent::WalWriteFull { record }
        | global_layer::GlobalEvent::WalFinishTorn { record } =>
            recovery_decision_class(record),
        _ => RecoveryDecisionClass::NotRecovery,
    }
}

pub proof fn recovery_decision_class_is_complete(
    record: replay_layer::JournalRecord,
)
    requires recovery_resolution_record(record),
    ensures
        recovery_decision_class(record) != RecoveryDecisionClass::NotRecovery,
        match recovery_decision_class(record) {
            RecoveryDecisionClass::Commit =>
                record is CommitRec,
            RecoveryDecisionClass::Fail =>
                record is FailRec,
            RecoveryDecisionClass::Unknown =>
                record is UnknownRec,
            RecoveryDecisionClass::NotRecovery => false,
        },
{
    match record {
        replay_layer::JournalRecord::CommitRec { .. }
        | replay_layer::JournalRecord::FailRec { .. }
        | replay_layer::JournalRecord::UnknownRec { .. } => {},
        replay_layer::JournalRecord::Authorize { .. }
        | replay_layer::JournalRecord::Revoke { .. }
        | replay_layer::JournalRecord::Prepare { .. }
        | replay_layer::JournalRecord::Arm { .. }
        | replay_layer::JournalRecord::Start { .. }
        | replay_layer::JournalRecord::Outcome { .. } => {
            assert(false);
        },
    }
}

/// Enabled recovery records are classified exhaustively at the durable
/// decision boundary.  Commit is the only class that carries a semantic value
/// refinement obligation; Fail and Unknown are terminal repairs but do not
/// claim an effect value.
pub proof fn recovery_decision_guard_is_sound_and_complete(
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
        recovery_resolution_record(record),
        recovery_decision_class(record) != RecoveryDecisionClass::NotRecovery,
        match recovery_decision_class(record) {
            RecoveryDecisionClass::Commit =>
                t5_r0_layer::recovery_commit_backed_by_durable_success(
                    durable, record,
                ),
            RecoveryDecisionClass::Fail
            | RecoveryDecisionClass::Unknown => true,
            RecoveryDecisionClass::NotRecovery => false,
        },
{
    t5_r0_layer::non_online_enabled_record_is_recovery_repair(
        cfg, durable, mode, slot, record,
    );
    recovery_decision_class_is_complete(record);
    match record {
        replay_layer::JournalRecord::CommitRec { .. } => {
            assert(t5_r0_layer::recovery_commit_backed_by_durable_success(
                durable, record,
            ));
        },
        replay_layer::JournalRecord::FailRec { .. }
        | replay_layer::JournalRecord::UnknownRec { .. } => {},
        replay_layer::JournalRecord::Authorize { .. }
        | replay_layer::JournalRecord::Revoke { .. }
        | replay_layer::JournalRecord::Prepare { .. }
        | replay_layer::JournalRecord::Arm { .. }
        | replay_layer::JournalRecord::Start { .. }
        | replay_layer::JournalRecord::Outcome { .. } => {
            assert(false);
        },
    }
}

pub proof fn wal_recovery_decision_composes_with_history(
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
        t5_s0_layer::alpha_commit_wal(cfg, after)
            == t5_s0_layer::extend_commit_history(
                t5_s0_layer::alpha_commit_wal(cfg, before),
                t5_s0_layer::wal_commit_delta(event),
            ),
        match recovery_decision_for_event(event) {
            RecoveryDecisionClass::Commit =>
                wal_recovery_resolution_is_durably_backed(cfg, before, event),
            RecoveryDecisionClass::Fail
            | RecoveryDecisionClass::Unknown
            | RecoveryDecisionClass::NotRecovery => true,
        },
{
    wal_non_online_step_is_durable_resolution(cfg, before, event, after);
    match event {
        global_layer::GlobalEvent::WalWriteFull { record }
        | global_layer::GlobalEvent::WalFinishTorn { record } => {
            recovery_decision_class_is_complete(record);
            match record {
                replay_layer::JournalRecord::CommitRec { .. } => {
                    assert(wal_recovery_resolution_is_durably_backed(
                        cfg, before, event,
                    ));
                },
                replay_layer::JournalRecord::FailRec { .. }
                | replay_layer::JournalRecord::UnknownRec { .. } => {},
                replay_layer::JournalRecord::Authorize { .. }
                | replay_layer::JournalRecord::Revoke { .. }
                | replay_layer::JournalRecord::Prepare { .. }
                | replay_layer::JournalRecord::Arm { .. }
                | replay_layer::JournalRecord::Start { .. }
                | replay_layer::JournalRecord::Outcome { .. } => {
                    assert(false);
                },
            }
        },
        _ => {},
    }
}

pub open spec fn recovery_commit_backed_by_crash_prefix(
    crash_journal: Seq<replay_layer::JournalRecord>,
    event: global_layer::GlobalEvent,
) -> bool {
    match event {
        global_layer::GlobalEvent::WalWriteFull {
            record: replay_layer::JournalRecord::CommitRec {
                request, attempt, value, outcome_ref, ..
            },
        }
        | global_layer::GlobalEvent::WalFinishTorn {
            record: replay_layer::JournalRecord::CommitRec {
                request, attempt, value, outcome_ref, ..
            },
        } => {
            &&& replay_layer::outcome_observation(
                crash_journal, request, attempt,
            ) == Option::Some(replay_layer::Observation::Success(value))
            &&& replay_layer::outcome_lsn(
                crash_journal, request, attempt,
            ) == Option::Some(outcome_ref)
        },
        _ => true,
    }
}

pub open spec fn wal_recovery_episode_has_crash_prefix_provenance(
    execution: wal_runtime_layer::WalExecution,
    crash: nat,
    finish: nat,
) -> bool {
    forall|index: nat| crash < index && index < finish ==>
        recovery_commit_backed_by_crash_prefix(
            wal_runtime_layer::journal_view(
                execution.configs[crash as int],
            ),
            #[trigger] execution.events[index as int],
        )
}

// R1's executable trace constructor is deliberately mode-polymorphic: the
// same three WAL events append an ordinary record online and a terminal repair
// record while recovering.  The latter is the concrete path that R0 could not
// represent.
pub open spec fn r1_extend_wal_execution(
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

pub proof fn r1_extend_wal_execution_exec(
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
        cfg, r1_extend_wal_execution(cfg, execution, local),
    ),
{
    let extended = r1_extend_wal_execution(cfg, execution, local);
    let old_len = execution.events.len();
    assert(execution.configs.len() == old_len + 1);
    assert(execution.configs.last()
        == execution.configs[old_len as int]);
    wal_runtime_layer::wal_decode_encode(local);
    assert(wal_runtime_layer::wal_runtime_step(
        cfg,
        execution.configs.last(),
        wal_runtime_layer::wal_encode(local),
        wal_runtime_layer::apply(cfg, execution.configs.last(), local),
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

pub open spec fn r1_append_full_wal_execution(
    cfg: config_layer::FullConfig,
    execution: wal_runtime_layer::WalExecution,
    record: replay_layer::JournalRecord,
) -> wal_runtime_layer::WalExecution {
    let before = execution.configs.last();
    let staged = r1_extend_wal_execution(
        cfg,
        execution,
        wal_runtime_layer::WalEvent::WalStage { record },
    );
    let written = r1_extend_wal_execution(
        cfg,
        staged,
        wal_runtime_layer::WalEvent::WalWriteFull { record },
    );
    r1_extend_wal_execution(
        cfg,
        written,
        wal_runtime_layer::WalEvent::WalFlushAck {
            cut: wal_runtime_layer::journal_view(before).len() + 1,
        },
    )
}

pub proof fn r1_append_full_wal_execution_exec(
    cfg: config_layer::FullConfig,
    execution: wal_runtime_layer::WalExecution,
    record: replay_layer::JournalRecord,
)
    requires
        wal_runtime_layer::exec(cfg, execution),
        execution.configs.last().runtime.mode
            != record_layer::Mode::Crashed,
        wal_runtime_layer::wal_quiescent(execution.configs.last()),
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
            cfg, r1_append_full_wal_execution(cfg, execution, record),
        ),
        r1_append_full_wal_execution(cfg, execution, record)
            .events.len() == execution.events.len() + 3,
        r1_append_full_wal_execution(cfg, execution, record)
            .configs.last().runtime.mode
                == execution.configs.last().runtime.mode,
        wal_runtime_layer::wal_quiescent(
            r1_append_full_wal_execution(cfg, execution, record)
                .configs.last(),
        ),
        wal_runtime_layer::journal_view(
            r1_append_full_wal_execution(cfg, execution, record)
                .configs.last(),
        ) == wal_runtime_layer::journal_view(
            execution.configs.last(),
        ).push(record),
{
    let before = execution.configs.last();
    let old_journal = wal_runtime_layer::journal_view(before);
    let stage_event = wal_runtime_layer::WalEvent::WalStage { record };
    let staged = r1_extend_wal_execution(cfg, execution, stage_event);
    assert(wal_runtime_layer::admissibly_enabled(
        cfg, before, stage_event,
    ));
    r1_extend_wal_execution_exec(cfg, execution, stage_event);
    let after_stage = staged.configs.last();
    assert(after_stage == wal_runtime_layer::apply(
        cfg, before, stage_event,
    ));
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
    let written = r1_extend_wal_execution(cfg, staged, write_event);
    assert(wal_runtime_layer::admissibly_enabled(
        cfg, after_stage, write_event,
    ));
    r1_extend_wal_execution_exec(cfg, staged, write_event);
    let after_write = written.configs.last();
    assert(after_write == wal_runtime_layer::apply(
        cfg, after_stage, write_event,
    ));
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
    r1_extend_wal_execution_exec(cfg, written, flush_event);
    let after_flush = r1_append_full_wal_execution(
        cfg, execution, record,
    ).configs.last();
    assert(after_flush == wal_runtime_layer::apply(
        cfg, after_write, flush_event,
    ));
    wal_runtime_layer::full_frames_push(old_journal, record);
    assert(after_write.runtime.store.media
        == wal_runtime_layer::full_frames(old_journal.push(record)));
    assert(wal_runtime_layer::journal_view(after_flush)
        == old_journal.push(record));
}

pub proof fn recovery_resolution_preserves_outcome_queries(
    journal: Seq<replay_layer::JournalRecord>,
    record: replay_layer::JournalRecord,
    request: replay_layer::RequestId,
    attempt: replay_layer::AttemptId,
)
    requires recovery_resolution_record(record),
    ensures
        replay_layer::outcome_observation(
            journal.push(record), request, attempt,
        ) == replay_layer::outcome_observation(
            journal, request, attempt,
        ),
        replay_layer::outcome_lsn(
            journal.push(record), request, attempt,
        ) == replay_layer::outcome_lsn(journal, request, attempt),
{
    replay_layer::outcome_observation_push(
        journal, request, attempt, record,
    );
    assert(journal.push(record).drop_last() =~= journal);
    assert(journal.push(record).last() == record);
    match record {
        replay_layer::JournalRecord::CommitRec { .. }
        | replay_layer::JournalRecord::FailRec { .. }
        | replay_layer::JournalRecord::UnknownRec { .. } => {},
        replay_layer::JournalRecord::Authorize { .. }
        | replay_layer::JournalRecord::Revoke { .. }
        | replay_layer::JournalRecord::Prepare { .. }
        | replay_layer::JournalRecord::Arm { .. }
        | replay_layer::JournalRecord::Start { .. }
        | replay_layer::JournalRecord::Outcome { .. } => {
            assert(false);
        },
    }
}

pub proof fn wal_non_online_step_is_durable_resolution(
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
        t5_r0_layer::wal_linearization_is_recovery_repair(
            cfg, before, event,
        ),
        wal_recovery_resolution_is_durably_backed(cfg, before, event),
        t5_s0_layer::alpha_commit_wal(cfg, after)
            == t5_s0_layer::extend_commit_history(
                t5_s0_layer::alpha_commit_wal(cfg, before),
                t5_s0_layer::wal_commit_delta(event),
            ),
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
            t5_r0_layer::non_online_enabled_record_is_recovery_repair(
                cfg,
                wal_runtime_layer::replay_view(cfg, before),
                before.runtime.mode,
                before.runtime.slot,
                record,
            );
        },
        _ => {},
    }
}

pub proof fn wal_non_online_step_preserves_outcome_queries(
    cfg: config_layer::FullConfig,
    before: wal_runtime_layer::WalConfiguration,
    event: global_layer::GlobalEvent,
    after: wal_runtime_layer::WalConfiguration,
    request: replay_layer::RequestId,
    attempt: replay_layer::AttemptId,
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
        wal_recovery_resolution_is_durably_backed(cfg, before, event),
        replay_layer::outcome_observation(
            wal_runtime_layer::journal_view(after), request, attempt,
        ) == replay_layer::outcome_observation(
            wal_runtime_layer::journal_view(before), request, attempt,
        ),
        replay_layer::outcome_lsn(
            wal_runtime_layer::journal_view(after), request, attempt,
        ) == replay_layer::outcome_lsn(
            wal_runtime_layer::journal_view(before), request, attempt,
        ),
{
    wal_non_online_step_is_durable_resolution(cfg, before, event, after);
    t5_s0_layer::wal_step_journal_view_exact(cfg, before, event, after);
    match event {
        global_layer::GlobalEvent::WalWriteFull { record }
        | global_layer::GlobalEvent::WalFinishTorn { record } => {
            assert(wal_runtime_layer::runtime_record_enabled(
                cfg, before, record,
            ));
            assert(journal_runtime_layer::runtime_slot_update(
                cfg, wal_runtime_layer::journal_projection(before), record,
            ).is_some());
            t5_r0_layer::non_online_enabled_record_is_recovery_repair(
                cfg,
                wal_runtime_layer::replay_view(cfg, before),
                before.runtime.mode,
                before.runtime.slot,
                record,
            );
            assert(recovery_resolution_record(record)) by {
                match record {
                    replay_layer::JournalRecord::CommitRec { .. }
                    | replay_layer::JournalRecord::FailRec { .. }
                    | replay_layer::JournalRecord::UnknownRec { .. } => {},
                    replay_layer::JournalRecord::Authorize { .. }
                    | replay_layer::JournalRecord::Revoke { .. }
                    | replay_layer::JournalRecord::Prepare { .. }
                    | replay_layer::JournalRecord::Arm { .. }
                    | replay_layer::JournalRecord::Start { .. }
                    | replay_layer::JournalRecord::Outcome { .. } => {
                        assert(false);
                    },
                }
            }
            recovery_resolution_preserves_outcome_queries(
                wal_runtime_layer::journal_view(before),
                record,
                request,
                attempt,
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

pub proof fn wal_recovery_episode_preserves_outcome_queries_at(
    cfg: config_layer::FullConfig,
    execution: wal_runtime_layer::WalExecution,
    crash: nat,
    finish: nat,
    index: nat,
    request: replay_layer::RequestId,
    attempt: replay_layer::AttemptId,
)
    requires
        wal_runtime_layer::exec(cfg, execution),
        t5_r0_layer::recovery_episode(execution.events, crash, finish),
        crash < index,
        index <= finish,
    ensures
        execution.configs[index as int].runtime.mode
            != record_layer::Mode::Online,
        replay_layer::outcome_observation(
            wal_runtime_layer::journal_view(
                execution.configs[index as int],
            ),
            request,
            attempt,
        ) == replay_layer::outcome_observation(
            wal_runtime_layer::journal_view(
                execution.configs[crash as int],
            ),
            request,
            attempt,
        ),
        replay_layer::outcome_lsn(
            wal_runtime_layer::journal_view(
                execution.configs[index as int],
            ),
            request,
            attempt,
        ) == replay_layer::outcome_lsn(
            wal_runtime_layer::journal_view(
                execution.configs[crash as int],
            ),
            request,
            attempt,
        ),
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
        t5_s0_layer::wal_step_journal_view_exact(
            cfg,
            execution.configs[crash as int],
            execution.events[crash as int],
            execution.configs[index as int],
        );
    } else {
        let previous: nat = (index - 1) as nat;
        assert(crash < previous);
        assert(previous < index);
        assert(previous < finish);
        assert(index == previous + 1);
        assert(previous < execution.events.len());
        wal_recovery_episode_preserves_outcome_queries_at(
            cfg,
            execution,
            crash,
            finish,
            previous,
            request,
            attempt,
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
        t5_r0_layer::wal_non_online_non_finish_step_preserves_mode(
            cfg,
            execution.configs[previous as int],
            execution.events[previous as int],
            execution.configs[index as int],
        );
        wal_non_online_step_preserves_outcome_queries(
            cfg,
            execution.configs[previous as int],
            execution.events[previous as int],
            execution.configs[index as int],
            request,
            attempt,
        );
    }
}

pub proof fn wal_recovery_commit_has_crash_prefix_provenance_at(
    cfg: config_layer::FullConfig,
    execution: wal_runtime_layer::WalExecution,
    crash: nat,
    finish: nat,
    index: nat,
)
    requires
        wal_runtime_layer::exec(cfg, execution),
        t5_r0_layer::recovery_episode(execution.events, crash, finish),
        crash < index,
        index < finish,
    ensures recovery_commit_backed_by_crash_prefix(
        wal_runtime_layer::journal_view(
            execution.configs[crash as int],
        ),
        execution.events[index as int],
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
    match execution.events[index as int] {
        global_layer::GlobalEvent::WalWriteFull { record }
        | global_layer::GlobalEvent::WalFinishTorn { record } => {
            assert(wal_runtime_layer::runtime_record_enabled(
                cfg, execution.configs[index as int], record,
            ));
            match record {
                replay_layer::JournalRecord::CommitRec {
                    request, attempt, value, outcome_ref, ..
                } => {
                    wal_recovery_episode_preserves_outcome_queries_at(
                        cfg,
                        execution,
                        crash,
                        finish,
                        index,
                        request,
                        attempt,
                    );
                    assert(replay_layer::structural_enabled(
                        config_layer::erase_config(cfg),
                        wal_runtime_layer::journal_view(
                            execution.configs[index as int],
                        ),
                        record,
                    ));
                    assert(replay_layer::outcome_observation(
                        wal_runtime_layer::journal_view(
                            execution.configs[index as int],
                        ),
                        request,
                        attempt,
                    ) == Option::Some(
                        replay_layer::Observation::Success(value),
                    ));
                    assert(replay_layer::outcome_lsn(
                        wal_runtime_layer::journal_view(
                            execution.configs[index as int],
                        ),
                        request,
                        attempt,
                    ) == Option::Some(outcome_ref));
                },
                replay_layer::JournalRecord::Authorize { .. }
                | replay_layer::JournalRecord::Revoke { .. }
                | replay_layer::JournalRecord::Prepare { .. }
                | replay_layer::JournalRecord::Arm { .. }
                | replay_layer::JournalRecord::Start { .. }
                | replay_layer::JournalRecord::Outcome { .. }
                | replay_layer::JournalRecord::FailRec { .. }
                | replay_layer::JournalRecord::UnknownRec { .. } => {},
            }
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

pub proof fn wal_recovery_episode_crash_prefix_provenance(
    cfg: config_layer::FullConfig,
    execution: wal_runtime_layer::WalExecution,
    crash: nat,
    finish: nat,
)
    requires
        wal_runtime_layer::exec(cfg, execution),
        t5_r0_layer::recovery_episode(execution.events, crash, finish),
    ensures wal_recovery_episode_has_crash_prefix_provenance(
        execution, crash, finish,
    ),
{
    assert forall|index: nat| crash < index && index < finish implies
        recovery_commit_backed_by_crash_prefix(
            wal_runtime_layer::journal_view(
                execution.configs[crash as int],
            ),
            #[trigger] execution.events[index as int],
        ) by {
        wal_recovery_commit_has_crash_prefix_provenance_at(
            cfg, execution, crash, finish, index,
        );
    }
}

pub proof fn wal_recovery_episode_commit_history_extends(
    cfg: config_layer::FullConfig,
    execution: wal_runtime_layer::WalExecution,
    crash: nat,
    finish: nat,
)
    requires
        wal_runtime_layer::exec(cfg, execution),
        t5_r0_layer::recovery_episode(execution.events, crash, finish),
    ensures append_layer::is_prefix(
        t5_s0_layer::alpha_commit_wal(
            cfg, execution.configs[crash as int],
        ),
        t5_s0_layer::alpha_commit_wal(
            cfg, execution.configs[(finish + 1) as int],
        ),
    ),
{
    assert(crash <= finish + 1);
    assert(finish + 1 < execution.configs.len());
    t5_e0_layer::wal_execution_commit_history_monotone_between(
        cfg, execution, crash, finish + 1,
    );
}

pub proof fn t5_r1_durable_success_recovery(
    cfg: config_layer::FullConfig,
    execution: wal_runtime_layer::WalExecution,
    crash: nat,
    finish: nat,
)
    requires
        wal_runtime_layer::exec(cfg, execution),
        t5_r0_layer::recovery_episode(execution.events, crash, finish),
    ensures
        append_layer::is_prefix(
            t5_s0_layer::alpha_commit_wal(
                cfg, execution.configs[crash as int],
            ),
            t5_s0_layer::alpha_commit_wal(
                cfg, execution.configs[(finish + 1) as int],
            ),
        ),
        wal_recovery_episode_has_crash_prefix_provenance(
            execution, crash, finish,
        ),
{
    wal_recovery_episode_commit_history_extends(
        cfg, execution, crash, finish,
    );
    wal_recovery_episode_crash_prefix_provenance(
        cfg, execution, crash, finish,
    );
}

}
