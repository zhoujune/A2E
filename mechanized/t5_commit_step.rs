use vstd::prelude::*;

#[path = "t4_contextual_composition.rs"]
pub mod t4_layer;

verus! {

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
use record_layer::query_layer::c1_layer::replay_layer;
use record_layer::query_layer::c1_layer::append_layer;

// T5-S0 proves exact one-step committed-history laws. Each accepted machine
// step either stutters or appends the single CommitEntry carried by its own
// durable linearization event.

pub open spec fn record_commit_delta(
    record: replay_layer::JournalRecord,
) -> Option<replay_layer::CommitEntry> {
    match record {
        replay_layer::JournalRecord::CommitRec { request, value, .. } => {
            Option::Some(replay_layer::CommitEntry { request, value })
        },
        replay_layer::JournalRecord::Authorize { .. }
        | replay_layer::JournalRecord::Revoke { .. }
        | replay_layer::JournalRecord::Prepare { .. }
        | replay_layer::JournalRecord::Arm { .. }
        | replay_layer::JournalRecord::Start { .. }
        | replay_layer::JournalRecord::Outcome { .. }
        | replay_layer::JournalRecord::FailRec { .. }
        | replay_layer::JournalRecord::UnknownRec { .. } => Option::None,
    }
}

pub open spec fn extend_commit_history(
    history: Seq<replay_layer::CommitEntry>,
    delta: Option<replay_layer::CommitEntry>,
) -> Seq<replay_layer::CommitEntry> {
    match delta {
        Option::None => history,
        Option::Some(entry) => history.push(entry),
    }
}

pub open spec fn broker_commit_delta(
    event: global_layer::GlobalEvent,
) -> Option<replay_layer::CommitEntry> {
    match event {
        global_layer::GlobalEvent::BrokerLinearize { record } => {
            record_commit_delta(record)
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
        | global_layer::GlobalEvent::FinishRecover => Option::None,
    }
}

pub open spec fn journal_commit_delta(
    event: global_layer::GlobalEvent,
) -> Option<replay_layer::CommitEntry> {
    match event {
        global_layer::GlobalEvent::JournalAppendLinearize { record } => {
            record_commit_delta(record)
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
        | global_layer::GlobalEvent::FinishRecover => Option::None,
    }
}

pub open spec fn wal_commit_delta(
    event: global_layer::GlobalEvent,
) -> Option<replay_layer::CommitEntry> {
    match event {
        global_layer::GlobalEvent::WalWriteFull { record }
        | global_layer::GlobalEvent::WalFinishTorn { record } => {
            record_commit_delta(record)
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
        | global_layer::GlobalEvent::FinishRecover => Option::None,
    }
}

pub open spec fn wal_record_delta(
    event: global_layer::GlobalEvent,
) -> Option<replay_layer::JournalRecord> {
    match event {
        global_layer::GlobalEvent::WalWriteFull { record }
        | global_layer::GlobalEvent::WalFinishTorn { record } => {
            Option::Some(record)
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
        | global_layer::GlobalEvent::FinishRecover => Option::None,
    }
}

pub open spec fn extend_journal_view(
    journal: Seq<replay_layer::JournalRecord>,
    delta: Option<replay_layer::JournalRecord>,
) -> Seq<replay_layer::JournalRecord> {
    match delta {
        Option::None => journal,
        Option::Some(record) => journal.push(record),
    }
}

pub open spec fn alpha_commit_broker(
    state: p0_layer::State,
) -> Seq<replay_layer::CommitEntry> {
    state.core.broker.durable.commit_log
}

pub open spec fn alpha_commit_journal(
    cfg: config_layer::FullConfig,
    state: journal_runtime_layer::JournalConfiguration,
) -> Seq<replay_layer::CommitEntry> {
    journal_runtime_layer::replay_view(cfg, state).commit_log
}

pub open spec fn alpha_commit_wal(
    cfg: config_layer::FullConfig,
    state: wal_runtime_layer::WalConfiguration,
) -> Seq<replay_layer::CommitEntry> {
    wal_runtime_layer::replay_view(cfg, state).commit_log
}

pub proof fn apply_record_commit_history_exact(
    durable: replay_layer::DurableBroker,
    record: replay_layer::JournalRecord,
)
    ensures replay_layer::apply_record(durable, record).commit_log
        == extend_commit_history(
            durable.commit_log, record_commit_delta(record),
        ),
{
    match record {
        replay_layer::JournalRecord::Authorize { .. }
        | replay_layer::JournalRecord::Revoke { .. }
        | replay_layer::JournalRecord::Prepare { .. }
        | replay_layer::JournalRecord::Arm { .. }
        | replay_layer::JournalRecord::Start { .. }
        | replay_layer::JournalRecord::Outcome { .. }
        | replay_layer::JournalRecord::CommitRec { .. }
        | replay_layer::JournalRecord::FailRec { .. }
        | replay_layer::JournalRecord::UnknownRec { .. } => {},
    }
}

pub proof fn extend_commit_history_is_prefix(
    history: Seq<replay_layer::CommitEntry>,
    delta: Option<replay_layer::CommitEntry>,
)
    ensures append_layer::is_prefix(
        history, extend_commit_history(history, delta),
    ),
{
    append_layer::prefix_reflexive(history);
    match delta {
        Option::None => {},
        Option::Some(entry) => {
            append_layer::take_push_stable(
                history, entry, history.len(),
            );
            assert(history.push(entry).take(history.len() as int) == history);
        },
    }
}

pub proof fn broker_step_commit_history_exact(
    cfg: config_layer::FullConfig,
    before: p0_layer::State,
    event: global_layer::GlobalEvent,
    after: p0_layer::State,
)
    requires execution_layer::broker_step(cfg, before, event, after),
    ensures alpha_commit_broker(after) == extend_commit_history(
        alpha_commit_broker(before), broker_commit_delta(event),
    ),
{
    match global_layer::broker_decode(event) {
        Option::None => {},
        Option::Some(local) => {
            assert(p0_layer::physical_step(cfg, before, local, after));
            assert(after == p0_layer::apply(cfg, before, local));
            match local {
                p0_layer::Event::BrokerLinearize { record } => {
                    apply_record_commit_history_exact(
                        before.core.broker.durable, record,
                    );
                    match record {
                        replay_layer::JournalRecord::Authorize { .. }
                        | replay_layer::JournalRecord::Revoke { .. }
                        | replay_layer::JournalRecord::Prepare { .. }
                        | replay_layer::JournalRecord::Arm { .. }
                        | replay_layer::JournalRecord::Start { .. }
                        | replay_layer::JournalRecord::Outcome { .. }
                        | replay_layer::JournalRecord::CommitRec { .. }
                        | replay_layer::JournalRecord::FailRec { .. }
                        | replay_layer::JournalRecord::UnknownRec { .. } => {},
                    }
                },
                p0_layer::Event::JournalAppendCall { .. }
                | p0_layer::Event::JournalAppendReturn { .. }
                | p0_layer::Event::JournalDiskFull { .. }
                | p0_layer::Event::InvokeEvent { .. }
                | p0_layer::Event::DeliverEvent { .. }
                | p0_layer::Event::IgnoreStale { .. }
                | p0_layer::Event::RetryRelease { .. }
                | p0_layer::Event::Crash
                | p0_layer::Event::BeginRecover
                | p0_layer::Event::FinishRecover => {},
            }
        },
    }
}

pub proof fn broker_step_commit_history_monotone(
    cfg: config_layer::FullConfig,
    before: p0_layer::State,
    event: global_layer::GlobalEvent,
    after: p0_layer::State,
)
    requires execution_layer::broker_step(cfg, before, event, after),
    ensures append_layer::is_prefix(
        alpha_commit_broker(before), alpha_commit_broker(after),
    ),
{
    broker_step_commit_history_exact(cfg, before, event, after);
    extend_commit_history_is_prefix(
        alpha_commit_broker(before), broker_commit_delta(event),
    );
}

pub proof fn journal_step_commit_history_exact(
    cfg: config_layer::FullConfig,
    before: journal_runtime_layer::JournalConfiguration,
    event: global_layer::GlobalEvent,
    after: journal_runtime_layer::JournalConfiguration,
)
    requires journal_runtime_layer::journal_runtime_step(
        cfg, before, event, after,
    ),
    ensures alpha_commit_journal(cfg, after) == extend_commit_history(
        alpha_commit_journal(cfg, before), journal_commit_delta(event),
    ),
{
    let erased = config_layer::erase_config(cfg);
    replay_layer::replay_commit_projection(
        erased, journal_runtime_layer::journal_view(before),
    );
    replay_layer::replay_commit_projection(
        erased, journal_runtime_layer::journal_view(after),
    );
    match event {
        global_layer::GlobalEvent::JournalAppendLinearize { record } => {
            assert(journal_runtime_layer::journal_decode(event)
                == Option::Some(
                    journal_runtime_layer::JournalEvent::JournalAppendLinearize {
                        record,
                    },
                ));
            assert(after == journal_runtime_layer::apply(
                cfg,
                before,
                journal_runtime_layer::JournalEvent::JournalAppendLinearize {
                    record,
                },
            ));
            assert(journal_runtime_layer::journal_view(after)
                == journal_runtime_layer::journal_view(before).push(record));
            replay_layer::commit_projection_push(
                journal_runtime_layer::journal_view(before), record,
            );
            match record {
                replay_layer::JournalRecord::Authorize { .. }
                | replay_layer::JournalRecord::Revoke { .. }
                | replay_layer::JournalRecord::Prepare { .. }
                | replay_layer::JournalRecord::Arm { .. }
                | replay_layer::JournalRecord::Start { .. }
                | replay_layer::JournalRecord::Outcome { .. }
                | replay_layer::JournalRecord::CommitRec { .. }
                | replay_layer::JournalRecord::FailRec { .. }
                | replay_layer::JournalRecord::UnknownRec { .. } => {},
            }
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

pub proof fn journal_step_commit_history_monotone(
    cfg: config_layer::FullConfig,
    before: journal_runtime_layer::JournalConfiguration,
    event: global_layer::GlobalEvent,
    after: journal_runtime_layer::JournalConfiguration,
)
    requires journal_runtime_layer::journal_runtime_step(
        cfg, before, event, after,
    ),
    ensures append_layer::is_prefix(
        alpha_commit_journal(cfg, before),
        alpha_commit_journal(cfg, after),
    ),
{
    journal_step_commit_history_exact(cfg, before, event, after);
    extend_commit_history_is_prefix(
        alpha_commit_journal(cfg, before), journal_commit_delta(event),
    );
}

pub proof fn wal_step_journal_view_exact(
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
    ensures wal_runtime_layer::journal_view(after) == extend_journal_view(
        wal_runtime_layer::journal_view(before), wal_record_delta(event),
    ),
{
    let media = before.runtime.store.media;
    match event {
        global_layer::GlobalEvent::WalWriteFull { record } => {
            assert(wal_runtime_layer::wal_decode(event) == Option::Some(
                wal_runtime_layer::WalEvent::WalWriteFull { record },
            ));
            assert(wal_runtime_layer::admissibly_enabled(
                cfg, before,
                wal_runtime_layer::WalEvent::WalWriteFull { record },
            ));
            assert(after == wal_runtime_layer::apply(
                cfg, before,
                wal_runtime_layer::WalEvent::WalWriteFull { record },
            ));
            assert(wal_runtime_layer::no_torn(media));
            assert(media == wal_runtime_layer::full_frames(
                wal_runtime_layer::parse(media),
            ));
            wal_runtime_layer::canonical_media_facts(media);
            wal_runtime_layer::parse_push_full(
                media, media.len() + 1, record,
            );
            assert(wal_runtime_layer::journal_view(after)
                == wal_runtime_layer::journal_view(before).push(record));
        },
        global_layer::GlobalEvent::WalFinishTorn { record } => {
            assert(wal_runtime_layer::wal_decode(event) == Option::Some(
                wal_runtime_layer::WalEvent::WalFinishTorn { record },
            ));
            assert(wal_runtime_layer::admissibly_enabled(
                cfg, before,
                wal_runtime_layer::WalEvent::WalFinishTorn { record },
            ));
            assert(after == wal_runtime_layer::apply(
                cfg, before,
                wal_runtime_layer::WalEvent::WalFinishTorn { record },
            ));
            assert(media.len() > 0);
            assert(media.last() == (wal_runtime_layer::Frame::Torn {
                lsn: media.len(), record,
            }));
            assert(wal_runtime_layer::is_torn(media.last()));
            wal_runtime_layer::torn_tail_decomposition(media);
            assert(media.drop_last() == wal_runtime_layer::full_frames(
                wal_runtime_layer::parse(media.drop_last()),
            ));
            wal_runtime_layer::canonical_media_facts(media.drop_last());
            wal_runtime_layer::finish_torn_extends_parse_once(media, record);
            assert(wal_runtime_layer::journal_view(after)
                == wal_runtime_layer::journal_view(before).push(record));
        },
        global_layer::GlobalEvent::WalWriteTorn { record } => {
            assert(wal_runtime_layer::wal_decode(event) == Option::Some(
                wal_runtime_layer::WalEvent::WalWriteTorn { record },
            ));
            assert(after == wal_runtime_layer::apply(
                cfg, before,
                wal_runtime_layer::WalEvent::WalWriteTorn { record },
            ));
            wal_runtime_layer::parse_push_torn(
                media, media.len() + 1, record,
            );
        },
        global_layer::GlobalEvent::TruncateTail => {
            assert(wal_runtime_layer::wal_decode(event) == Option::Some(
                wal_runtime_layer::WalEvent::TruncateTail,
            ));
            assert(wal_runtime_layer::admissibly_enabled(
                cfg, before, wal_runtime_layer::WalEvent::TruncateTail,
            ));
            assert(after == wal_runtime_layer::apply(
                cfg, before, wal_runtime_layer::WalEvent::TruncateTail,
            ));
            assert(before.runtime.store.scan_result
                == wal_runtime_layer::journal_view(before));
            wal_runtime_layer::truncate_preserves_parse(media);
        },
        global_layer::GlobalEvent::BrokerLinearize { .. }
        | global_layer::GlobalEvent::JournalAppendCall { .. }
        | global_layer::GlobalEvent::JournalAppendLinearize { .. }
        | global_layer::GlobalEvent::JournalAppendReturn { .. }
        | global_layer::GlobalEvent::JournalDiskFull { .. }
        | global_layer::GlobalEvent::WalStage { .. }
        | global_layer::GlobalEvent::WalFlushAck { .. }
        | global_layer::GlobalEvent::WalDiskFull { .. }
        | global_layer::GlobalEvent::InvokeEvent { .. }
        | global_layer::GlobalEvent::DeliverEvent { .. }
        | global_layer::GlobalEvent::IgnoreStale { .. }
        | global_layer::GlobalEvent::RetryRelease { .. }
        | global_layer::GlobalEvent::Crash
        | global_layer::GlobalEvent::BeginScan
        | global_layer::GlobalEvent::FinishScan
        | global_layer::GlobalEvent::AbortScan
        | global_layer::GlobalEvent::BeginRecover
        | global_layer::GlobalEvent::FinishRecover => {},
    }
}

pub proof fn wal_step_commit_history_exact(
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
    ensures alpha_commit_wal(cfg, after) == extend_commit_history(
        alpha_commit_wal(cfg, before), wal_commit_delta(event),
    ),
{
    let erased = config_layer::erase_config(cfg);
    replay_layer::replay_commit_projection(
        erased, wal_runtime_layer::journal_view(before),
    );
    replay_layer::replay_commit_projection(
        erased, wal_runtime_layer::journal_view(after),
    );
    wal_step_journal_view_exact(cfg, before, event, after);
    match wal_record_delta(event) {
        Option::None => {},
        Option::Some(record) => {
            replay_layer::commit_projection_push(
                wal_runtime_layer::journal_view(before), record,
            );
            match record {
                replay_layer::JournalRecord::Authorize { .. }
                | replay_layer::JournalRecord::Revoke { .. }
                | replay_layer::JournalRecord::Prepare { .. }
                | replay_layer::JournalRecord::Arm { .. }
                | replay_layer::JournalRecord::Start { .. }
                | replay_layer::JournalRecord::Outcome { .. }
                | replay_layer::JournalRecord::CommitRec { .. }
                | replay_layer::JournalRecord::FailRec { .. }
                | replay_layer::JournalRecord::UnknownRec { .. } => {},
            }
        },
    }
}

pub proof fn wal_step_commit_history_monotone(
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
    ensures append_layer::is_prefix(
        alpha_commit_wal(cfg, before), alpha_commit_wal(cfg, after),
    ),
{
    wal_step_commit_history_exact(cfg, before, event, after);
    extend_commit_history_is_prefix(
        alpha_commit_wal(cfg, before), wal_commit_delta(event),
    );
}

} // verus!
