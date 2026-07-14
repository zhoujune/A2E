use vstd::prelude::*;

#[path = "t3_wal_event_projection.rs"]
pub mod event_layer;

verus! {

use event_layer::trace_layer;
use trace_layer::runtime_layer;
use runtime_layer::t2_layer::representation_layer::event_layer::trace_layer
    as journal_trace_layer;
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

// T3-W1 relates the independent typed WAL to the independent atomic-Journal
// runtime.  The relation is deliberately field-explicit: it does not hide a
// Journal shadow in the WAL or identify the two configurations by definition.
pub open spec fn ghost_evidence_equal(
    wal: runtime_layer::WalConfiguration,
    journal: journal_runtime_layer::JournalConfiguration,
) -> bool {
    journal.evidence.records == wal.evidence.records
        && journal.evidence.physical == wal.evidence.physical
        && journal.evidence.ack_cuts == wal.evidence.ack_cuts
        && journal.evidence.acknowledged_prefix
            == wal.evidence.acknowledged_prefix
        && journal.evidence.slot_source == wal.evidence.slot_source
        && journal.evidence.commit_source == wal.evidence.commit_source
}

pub open spec fn representation(
    wal: runtime_layer::WalConfiguration,
    journal: journal_runtime_layer::JournalConfiguration,
) -> bool {
    journal.runtime.store.journal
            == runtime_layer::parse(wal.runtime.store.media)
        && journal.runtime.mode == wal.runtime.mode
        && journal.runtime.slot == wal.runtime.slot
        && journal.runtime.append == wal.runtime.append
        && ghost_evidence_equal(wal, journal)
}

pub proof fn projection_satisfies_representation(
    wal: runtime_layer::WalConfiguration,
)
    ensures representation(wal, runtime_layer::journal_projection(wal)),
{
}

pub proof fn representation_determines_projection(
    wal: runtime_layer::WalConfiguration,
    journal: journal_runtime_layer::JournalConfiguration,
)
    requires representation(wal, journal),
    ensures journal == runtime_layer::journal_projection(wal),
{
    assert(journal.runtime.store
        == runtime_layer::journal_projection(wal).runtime.store);
    assert(journal.runtime
        == runtime_layer::journal_projection(wal).runtime);
    assert(journal.evidence
        == runtime_layer::journal_projection(wal).evidence);
}

pub proof fn representation_iff_projection(
    wal: runtime_layer::WalConfiguration,
    journal: journal_runtime_layer::JournalConfiguration,
)
    ensures representation(wal, journal) <==>
        journal == runtime_layer::journal_projection(wal),
{
    if representation(wal, journal) {
        representation_determines_projection(wal, journal);
    }
    if journal == runtime_layer::journal_projection(wal) {
        projection_satisfies_representation(wal);
    }
}

pub proof fn initial_projection(
    cfg: config_layer::FullConfig,
)
    ensures runtime_layer::journal_projection(
        runtime_layer::initial_configuration(cfg),
    ) == journal_runtime_layer::initial_configuration(cfg),
{
}

pub proof fn initial_representation(
    cfg: config_layer::FullConfig,
)
    ensures representation(
        runtime_layer::initial_configuration(cfg),
        journal_runtime_layer::initial_configuration(cfg),
    ),
{
    initial_projection(cfg);
    projection_satisfies_representation(
        runtime_layer::initial_configuration(cfg),
    );
}

pub proof fn projected_append_view(
    wal: runtime_layer::WalConfiguration,
)
    ensures journal_runtime_layer::append_view(
        runtime_layer::journal_projection(wal),
    ) == runtime_layer::append_view(wal),
{
}

pub proof fn wal_basic_implies_projected_journal_basic(
    cfg: config_layer::FullConfig,
    wal: runtime_layer::WalConfiguration,
)
    requires runtime_layer::basic_invariant(cfg, wal),
    ensures journal_runtime_layer::basic_invariant(
        cfg, runtime_layer::journal_projection(wal),
    ),
{
    projected_append_view(wal);
}

pub proof fn projected_basic_invariant(
    cfg: config_layer::FullConfig,
    wal: runtime_layer::WalConfiguration,
)
    requires runtime_layer::basic_invariant(cfg, wal),
    ensures journal_runtime_layer::basic_invariant(
        cfg, runtime_layer::journal_projection(wal),
    ),
{
    wal_basic_implies_projected_journal_basic(cfg, wal);
}

pub proof fn matched_control_enabled(
    cfg: config_layer::FullConfig,
    wal: runtime_layer::WalConfiguration,
    wal_event: runtime_layer::WalEvent,
    journal_event: journal_runtime_layer::JournalEvent,
)
    requires
        runtime_layer::control_enabled(cfg, wal, wal_event),
        event_layer::wal_local_to_journal(wal_event)
            == Option::Some(journal_event),
    ensures journal_runtime_layer::control_enabled(
        cfg, runtime_layer::journal_projection(wal), journal_event,
    ),
{
    match wal_event {
        runtime_layer::WalEvent::WalStage { .. }
        | runtime_layer::WalEvent::WalWriteFull { .. }
        | runtime_layer::WalEvent::WalFinishTorn { .. }
        | runtime_layer::WalEvent::WalFlushAck { .. }
        | runtime_layer::WalEvent::WalDiskFull { .. }
        | runtime_layer::WalEvent::InvokeEvent { .. }
        | runtime_layer::WalEvent::DeliverEvent { .. }
        | runtime_layer::WalEvent::IgnoreStale { .. }
        | runtime_layer::WalEvent::RetryRelease { .. }
        | runtime_layer::WalEvent::Crash
        | runtime_layer::WalEvent::BeginRecover
        | runtime_layer::WalEvent::FinishRecover => {},
        runtime_layer::WalEvent::WalWriteTorn { .. }
        | runtime_layer::WalEvent::BeginScan
        | runtime_layer::WalEvent::FinishScan
        | runtime_layer::WalEvent::TruncateTail
        | runtime_layer::WalEvent::AbortScan => {},
    }
}

pub proof fn matched_evidence_admissible(
    wal: runtime_layer::WalConfiguration,
    wal_event: runtime_layer::WalEvent,
    journal_event: journal_runtime_layer::JournalEvent,
)
    requires
        runtime_layer::evidence_admissible(wal, wal_event),
        event_layer::wal_local_to_journal(wal_event)
            == Option::Some(journal_event),
    ensures journal_runtime_layer::evidence_admissible(
        runtime_layer::journal_projection(wal), journal_event,
    ),
{
    match wal_event {
        runtime_layer::WalEvent::WalStage { .. }
        | runtime_layer::WalEvent::WalWriteFull { .. }
        | runtime_layer::WalEvent::WalFinishTorn { .. }
        | runtime_layer::WalEvent::WalFlushAck { .. }
        | runtime_layer::WalEvent::WalDiskFull { .. }
        | runtime_layer::WalEvent::InvokeEvent { .. }
        | runtime_layer::WalEvent::DeliverEvent { .. }
        | runtime_layer::WalEvent::IgnoreStale { .. }
        | runtime_layer::WalEvent::RetryRelease { .. }
        | runtime_layer::WalEvent::Crash
        | runtime_layer::WalEvent::BeginRecover
        | runtime_layer::WalEvent::FinishRecover => {},
        runtime_layer::WalEvent::WalWriteTorn { .. }
        | runtime_layer::WalEvent::BeginScan
        | runtime_layer::WalEvent::FinishScan
        | runtime_layer::WalEvent::TruncateTail
        | runtime_layer::WalEvent::AbortScan => {},
    }
}

pub proof fn matched_apply_commutes(
    cfg: config_layer::FullConfig,
    wal: runtime_layer::WalConfiguration,
    wal_event: runtime_layer::WalEvent,
    journal_event: journal_runtime_layer::JournalEvent,
)
    requires
        runtime_layer::basic_invariant(cfg, wal),
        runtime_layer::admissibly_enabled(cfg, wal, wal_event),
        event_layer::wal_local_to_journal(wal_event)
            == Option::Some(journal_event),
    ensures runtime_layer::journal_projection(
        runtime_layer::apply(cfg, wal, wal_event),
    ) == journal_runtime_layer::apply(
        cfg, runtime_layer::journal_projection(wal), journal_event,
    ),
{
    match wal_event {
        runtime_layer::WalEvent::WalWriteFull { record } => {
            runtime_layer::no_torn_sequential_is_canonical(
                wal.runtime.store.media,
            );
            runtime_layer::canonical_media_facts(wal.runtime.store.media);
            runtime_layer::parse_push_full(
                wal.runtime.store.media,
                wal.runtime.store.media.len() + 1,
                record,
            );
        },
        runtime_layer::WalEvent::WalFinishTorn { record } => {
            runtime_layer::torn_tail_decomposition(wal.runtime.store.media);
            runtime_layer::canonical_media_facts(
                wal.runtime.store.media.drop_last(),
            );
            runtime_layer::finish_torn_extends_parse_once(
                wal.runtime.store.media, record,
            );
        },
        runtime_layer::WalEvent::WalStage { .. }
        | runtime_layer::WalEvent::WalFlushAck { .. }
        | runtime_layer::WalEvent::WalDiskFull { .. }
        | runtime_layer::WalEvent::InvokeEvent { .. }
        | runtime_layer::WalEvent::DeliverEvent { .. }
        | runtime_layer::WalEvent::IgnoreStale { .. }
        | runtime_layer::WalEvent::RetryRelease { .. }
        | runtime_layer::WalEvent::Crash
        | runtime_layer::WalEvent::BeginRecover
        | runtime_layer::WalEvent::FinishRecover => {},
        runtime_layer::WalEvent::WalWriteTorn { .. }
        | runtime_layer::WalEvent::BeginScan
        | runtime_layer::WalEvent::FinishScan
        | runtime_layer::WalEvent::TruncateTail
        | runtime_layer::WalEvent::AbortScan => {},
    }
}

pub proof fn matched_local_step_commutes(
    cfg: config_layer::FullConfig,
    before: runtime_layer::WalConfiguration,
    wal_event: runtime_layer::WalEvent,
    journal_event: journal_runtime_layer::JournalEvent,
    after: runtime_layer::WalConfiguration,
)
    requires
        runtime_layer::basic_invariant(cfg, before),
        runtime_layer::wal_local_step(cfg, before, wal_event, after),
        event_layer::wal_local_to_journal(wal_event)
            == Option::Some(journal_event),
    ensures journal_runtime_layer::journal_local_step(
        cfg,
        runtime_layer::journal_projection(before),
        journal_event,
        runtime_layer::journal_projection(after),
    ),
{
    matched_control_enabled(cfg, before, wal_event, journal_event);
    matched_evidence_admissible(before, wal_event, journal_event);
    matched_apply_commutes(cfg, before, wal_event, journal_event);
}

pub proof fn internal_local_step_preserves_projection(
    cfg: config_layer::FullConfig,
    before: runtime_layer::WalConfiguration,
    wal_event: runtime_layer::WalEvent,
    after: runtime_layer::WalConfiguration,
)
    requires
        runtime_layer::wal_local_step(cfg, before, wal_event, after),
        event_layer::wal_local_to_journal(wal_event).is_none(),
    ensures runtime_layer::journal_projection(after)
        == runtime_layer::journal_projection(before),
{
    assert(after == runtime_layer::apply(cfg, before, wal_event));
    match wal_event {
        runtime_layer::WalEvent::WalWriteTorn { record } => {
            runtime_layer::parse_push_torn(
                before.runtime.store.media,
                before.runtime.store.media.len() + 1,
                record,
            );
        },
        runtime_layer::WalEvent::TruncateTail => {
            runtime_layer::truncate_preserves_parse(
                before.runtime.store.media,
            );
        },
        runtime_layer::WalEvent::BeginScan
        | runtime_layer::WalEvent::FinishScan
        | runtime_layer::WalEvent::AbortScan => {},
        runtime_layer::WalEvent::WalStage { .. }
        | runtime_layer::WalEvent::WalWriteFull { .. }
        | runtime_layer::WalEvent::WalFinishTorn { .. }
        | runtime_layer::WalEvent::WalFlushAck { .. }
        | runtime_layer::WalEvent::WalDiskFull { .. }
        | runtime_layer::WalEvent::InvokeEvent { .. }
        | runtime_layer::WalEvent::DeliverEvent { .. }
        | runtime_layer::WalEvent::IgnoreStale { .. }
        | runtime_layer::WalEvent::RetryRelease { .. }
        | runtime_layer::WalEvent::Crash
        | runtime_layer::WalEvent::BeginRecover
        | runtime_layer::WalEvent::FinishRecover => {},
    }
}

pub proof fn matched_runtime_step_commutes(
    cfg: config_layer::FullConfig,
    before: runtime_layer::WalConfiguration,
    source_event: global_layer::GlobalEvent,
    target_event: global_layer::GlobalEvent,
    after: runtime_layer::WalConfiguration,
)
    requires
        runtime_layer::basic_invariant(cfg, before),
        runtime_layer::wal_runtime_step(
            cfg, before, source_event, after,
        ),
        event_layer::translate_event(source_event)
            == Option::Some(target_event),
    ensures journal_runtime_layer::journal_runtime_step(
        cfg,
        runtime_layer::journal_projection(before),
        target_event,
        runtime_layer::journal_projection(after),
    ),
{
    match runtime_layer::wal_decode(source_event) {
        Option::None => {},
        Option::Some(wal_event) => {
            event_layer::translated_decoded_event(source_event, wal_event);
            match event_layer::wal_local_to_journal(wal_event) {
                Option::None => {},
                Option::Some(journal_event) => {
                    assert(target_event
                        == journal_runtime_layer::journal_encode(
                            journal_event,
                        ));
                    journal_runtime_layer::journal_decode_encode(
                        journal_event,
                    );
                    matched_local_step_commutes(
                        cfg, before, wal_event, journal_event, after,
                    );
                },
            }
        },
    }
}

pub proof fn internal_runtime_step_preserves_projection(
    cfg: config_layer::FullConfig,
    before: runtime_layer::WalConfiguration,
    source_event: global_layer::GlobalEvent,
    after: runtime_layer::WalConfiguration,
)
    requires
        runtime_layer::wal_runtime_step(
            cfg, before, source_event, after,
        ),
        event_layer::translate_event(source_event).is_none(),
    ensures runtime_layer::journal_projection(after)
        == runtime_layer::journal_projection(before),
{
    match runtime_layer::wal_decode(source_event) {
        Option::None => {},
        Option::Some(wal_event) => {
            event_layer::translated_decoded_event(source_event, wal_event);
            assert(event_layer::wal_local_to_journal(wal_event).is_none());
            internal_local_step_preserves_projection(
                cfg, before, wal_event, after,
            );
        },
    }
}

} // verus!
