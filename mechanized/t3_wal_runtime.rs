use vstd::prelude::*;

#[path = "t2_atomic_journal_simulation.rs"]
pub mod t2_layer;

verus! {

use t2_layer::representation_layer::event_layer::trace_layer::runtime_layer
    as journal_runtime_layer;
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
use c1_layer::append_layer;

// T3-W0 defines the independent typed-WAL runtime.  Its concrete state has
// typed frames and volatile recovery control, but no parsed-Journal shadow,
// replayed Broker state, or historical acknowledgment shadow.

#[derive(PartialEq, Eq)]
pub enum Frame {
    Full {
        lsn: nat,
        record: replay_layer::JournalRecord,
    },
    Torn {
        lsn: nat,
        record: replay_layer::JournalRecord,
    },
}

#[derive(PartialEq, Eq)]
pub enum ScanPhase {
    Idle,
    Scanning,
    Scanned,
    Truncated,
}

pub struct TypedWAL {
    pub cache: Seq<replay_layer::JournalRecord>,
    pub media: Seq<Frame>,
    pub acked_len: nat,
    pub scan_phase: ScanPhase,
    pub scan_result: Seq<replay_layer::JournalRecord>,
}

pub struct WalRuntime {
    pub store: TypedWAL,
    pub slot: record_layer::ExecSlot,
    pub mode: record_layer::Mode,
    pub append: append_layer::AppendControl<replay_layer::JournalRecord>,
}

pub struct WalConfiguration {
    pub runtime: WalRuntime,
    pub evidence: journal_runtime_layer::GhostEvidence,
}

pub open spec fn frame_lsn(frame: Frame) -> nat {
    match frame {
        Frame::Full { lsn, .. } | Frame::Torn { lsn, .. } => lsn,
    }
}

pub open spec fn frame_record(
    frame: Frame,
) -> replay_layer::JournalRecord {
    match frame {
        Frame::Full { record, .. } | Frame::Torn { record, .. } => record,
    }
}

pub open spec fn is_torn(frame: Frame) -> bool {
    match frame {
        Frame::Torn { .. } => true,
        Frame::Full { .. } => false,
    }
}

// Parse is deliberately LSN-sensitive.  The complete-prefix test makes a
// Torn or malformed frame stop parsing permanently, even if later frames are
// individually well formed.
pub open spec fn parse(
    media: Seq<Frame>,
) -> Seq<replay_layer::JournalRecord>
    decreases media.len()
{
    if media.len() == 0 {
        Seq::empty()
    } else {
        let prefix = media.drop_last();
        let parsed = parse(prefix);
        match media.last() {
            Frame::Full { lsn, record } => {
                if lsn == media.len() && parsed.len() == prefix.len() {
                    parsed.push(record)
                } else {
                    parsed
                }
            },
            Frame::Torn { .. } => parsed,
        }
    }
}

pub open spec fn fully_parsed(media: Seq<Frame>) -> bool {
    parse(media).len() == media.len()
}

pub open spec fn full_frames(
    records: Seq<replay_layer::JournalRecord>,
) -> Seq<Frame>
    decreases records.len()
{
    if records.len() == 0 {
        Seq::empty()
    } else {
        full_frames(records.drop_last()).push(Frame::Full {
            lsn: records.len(),
            record: records.last(),
        })
    }
}

pub open spec fn frame_records(
    media: Seq<Frame>,
) -> Seq<replay_layer::JournalRecord>
    decreases media.len()
{
    if media.len() == 0 {
        Seq::empty()
    } else {
        frame_records(media.drop_last()).push(frame_record(media.last()))
    }
}

pub open spec fn no_torn(media: Seq<Frame>) -> bool
    decreases media.len()
{
    media.len() == 0 || {
        no_torn(media.drop_last()) && !is_torn(media.last())
    }
}

pub open spec fn sequential_lsns(media: Seq<Frame>) -> bool
    decreases media.len()
{
    media.len() == 0 || {
        sequential_lsns(media.drop_last())
            && frame_lsn(media.last()) == media.len()
    }
}

// Every proper prefix is Torn-free, so a Torn frame, if present, is the
// unique final frame.
pub open spec fn torn_tail_only(media: Seq<Frame>) -> bool {
    media.len() == 0 || no_torn(media.drop_last())
}

pub open spec fn replace_torn_tail(
    media: Seq<Frame>,
    record: replay_layer::JournalRecord,
) -> Seq<Frame> {
    if media.len() == 0 {
        media
    } else {
        media.drop_last().push(Frame::Full {
            lsn: media.len(),
            record,
        })
    }
}

pub proof fn parse_len_bounded(media: Seq<Frame>)
    ensures parse(media).len() <= media.len(),
    decreases media.len(),
{
    if media.len() > 0 {
        parse_len_bounded(media.drop_last());
    }
}

pub proof fn parse_push_torn(
    media: Seq<Frame>,
    lsn: nat,
    record: replay_layer::JournalRecord,
)
    ensures parse(media.push(Frame::Torn { lsn, record })) == parse(media),
{
    let frame = Frame::Torn { lsn, record };
    assert(media.push(frame).drop_last() =~= media);
    assert(media.push(frame).last() == frame);
}

pub proof fn parse_push_full(
    media: Seq<Frame>,
    lsn: nat,
    record: replay_layer::JournalRecord,
)
    ensures parse(media.push(Frame::Full { lsn, record })) ==
        if lsn == media.len() + 1 && fully_parsed(media) {
            parse(media).push(record)
        } else {
            parse(media)
        },
{
    let frame = Frame::Full { lsn, record };
    assert(media.push(frame).drop_last() =~= media);
    assert(media.push(frame).last() == frame);
}

pub proof fn full_frames_push(
    records: Seq<replay_layer::JournalRecord>,
    record: replay_layer::JournalRecord,
)
    ensures full_frames(records.push(record)) == full_frames(records).push(
        Frame::Full { lsn: records.len() + 1, record },
    ),
{
    assert(records.push(record).drop_last() =~= records);
    assert(records.push(record).last() == record);
}

pub proof fn frame_records_push(media: Seq<Frame>, frame: Frame)
    ensures frame_records(media.push(frame))
        == frame_records(media).push(frame_record(frame)),
{
    assert(media.push(frame).drop_last() =~= media);
    assert(media.push(frame).last() == frame);
}

pub proof fn full_frames_len(records: Seq<replay_layer::JournalRecord>)
    ensures full_frames(records).len() == records.len(),
    decreases records.len(),
{
    if records.len() > 0 {
        full_frames_len(records.drop_last());
    }
}

pub proof fn frame_records_len(media: Seq<Frame>)
    ensures frame_records(media).len() == media.len(),
    decreases media.len(),
{
    if media.len() > 0 {
        frame_records_len(media.drop_last());
    }
}

pub proof fn parse_full_frames(records: Seq<replay_layer::JournalRecord>)
    ensures parse(full_frames(records)) == records,
    decreases records.len(),
{
    if records.len() > 0 {
        let prefix = records.drop_last();
        parse_full_frames(prefix);
        full_frames_len(prefix);
        records.lemma_add_last_back();
        full_frames_push(prefix, records.last());
        parse_push_full(
            full_frames(prefix), records.len(), records.last(),
        );
    }
}

pub proof fn frame_records_full_frames(
    records: Seq<replay_layer::JournalRecord>,
)
    ensures frame_records(full_frames(records)) == records,
    decreases records.len(),
{
    if records.len() > 0 {
        let prefix = records.drop_last();
        frame_records_full_frames(prefix);
        records.lemma_add_last_back();
        full_frames_push(prefix, records.last());
        frame_records_push(
            full_frames(prefix),
            Frame::Full { lsn: records.len(), record: records.last() },
        );
    }
}

pub proof fn parse_torn_tail(
    records: Seq<replay_layer::JournalRecord>,
    record: replay_layer::JournalRecord,
)
    ensures parse(full_frames(records).push(Frame::Torn {
        lsn: records.len() + 1,
        record,
    })) == records,
{
    parse_full_frames(records);
    parse_push_torn(full_frames(records), records.len() + 1, record);
}

pub proof fn truncate_preserves_parse(media: Seq<Frame>)
    ensures parse(full_frames(parse(media))) == parse(media),
{
    parse_full_frames(parse(media));
}

pub proof fn full_frames_no_torn(
    records: Seq<replay_layer::JournalRecord>,
)
    ensures no_torn(full_frames(records)),
    decreases records.len(),
{
    if records.len() > 0 {
        let prefix = records.drop_last();
        let frame = Frame::Full {
            lsn: records.len(), record: records.last(),
        };
        full_frames_no_torn(prefix);
        records.lemma_add_last_back();
        full_frames_push(prefix, records.last());
        assert(full_frames(records) == full_frames(prefix).push(frame));
        assert(full_frames(records).drop_last() =~= full_frames(prefix));
        assert(full_frames(records).last() == frame);
        assert(!is_torn(frame));
    }
}

pub proof fn full_frames_sequential(
    records: Seq<replay_layer::JournalRecord>,
)
    ensures sequential_lsns(full_frames(records)),
    decreases records.len(),
{
    if records.len() > 0 {
        let prefix = records.drop_last();
        let frame = Frame::Full {
            lsn: records.len(), record: records.last(),
        };
        full_frames_sequential(prefix);
        records.lemma_add_last_back();
        full_frames_push(prefix, records.last());
        assert(full_frames(records) == full_frames(prefix).push(frame));
        assert(full_frames(records).drop_last() =~= full_frames(prefix));
        assert(full_frames(records).last() == frame);
        assert(frame_lsn(frame) == records.len());
    }
}

pub proof fn prefix_survives_push<R>(
    prefix: Seq<R>,
    records: Seq<R>,
    record: R,
)
    requires append_layer::is_prefix(prefix, records),
    ensures append_layer::is_prefix(prefix, records.push(record)),
{
    append_layer::take_push_stable(records, record, prefix.len());
}

pub proof fn called_cache_decomposition<R>(
    cache: Seq<R>,
    parsed: Seq<R>,
    acked_len: nat,
    record: R,
)
    requires
        cache.len() == acked_len + 1,
        cache.last() == record,
        parsed == cache.take(acked_len as int),
    ensures cache == parsed.push(record),
{
    cache.lemma_add_last_back();
    assert(cache.drop_last() =~= cache.take(acked_len as int));
}

pub proof fn canonical_media_facts(media: Seq<Frame>)
    requires media == full_frames(parse(media)),
    ensures
        fully_parsed(media),
        frame_records(media) == parse(media),
        no_torn(media),
        sequential_lsns(media),
        torn_tail_only(media),
{
    let records = parse(media);
    parse_full_frames(records);
    frame_records_full_frames(records);
    full_frames_len(records);
    full_frames_no_torn(records);
    full_frames_sequential(records);
    full_frames_torn_tail_only(records);
}

pub proof fn push_full_media_shape(
    media: Seq<Frame>,
    record: replay_layer::JournalRecord,
)
    requires no_torn(media), sequential_lsns(media),
    ensures
        no_torn(media.push(Frame::Full {
            lsn: media.len() + 1, record,
        })),
        sequential_lsns(media.push(Frame::Full {
            lsn: media.len() + 1, record,
        })),
        torn_tail_only(media.push(Frame::Full {
            lsn: media.len() + 1, record,
        })),
{
    let frame = Frame::Full { lsn: media.len() + 1, record };
    assert(media.push(frame).drop_last() =~= media);
    assert(media.push(frame).last() == frame);
}

pub proof fn push_torn_media_shape(
    media: Seq<Frame>,
    record: replay_layer::JournalRecord,
)
    requires no_torn(media), sequential_lsns(media),
    ensures
        !no_torn(media.push(Frame::Torn {
            lsn: media.len() + 1, record,
        })),
        sequential_lsns(media.push(Frame::Torn {
            lsn: media.len() + 1, record,
        })),
        torn_tail_only(media.push(Frame::Torn {
            lsn: media.len() + 1, record,
        })),
{
    let frame = Frame::Torn { lsn: media.len() + 1, record };
    assert(media.push(frame).drop_last() =~= media);
    assert(media.push(frame).last() == frame);
}

pub proof fn full_frames_torn_tail_only(
    records: Seq<replay_layer::JournalRecord>,
)
    ensures torn_tail_only(full_frames(records)),
{
    if records.len() > 0 {
        let prefix = records.drop_last();
        full_frames_no_torn(prefix);
        records.lemma_add_last_back();
        full_frames_push(prefix, records.last());
        assert(full_frames(records).drop_last() =~= full_frames(prefix));
    }
}

pub proof fn no_torn_sequential_is_canonical(media: Seq<Frame>)
    requires no_torn(media), sequential_lsns(media),
    ensures
        parse(media) == frame_records(media),
        media == full_frames(parse(media)),
    decreases media.len(),
{
    if media.len() > 0 {
        let prefix = media.drop_last();
        no_torn_sequential_is_canonical(prefix);
        frame_records_len(prefix);
        match media.last() {
            Frame::Full { lsn, record } => {
                parse_push_full(prefix, lsn, record);
                full_frames_push(frame_records(prefix), record);
                frame_records_push(media.drop_last(), media.last());
                media.lemma_add_last_back();
            },
            Frame::Torn { .. } => {},
        }
    }
}

pub proof fn torn_tail_decomposition(media: Seq<Frame>)
    requires
        media.len() > 0,
        sequential_lsns(media),
        torn_tail_only(media),
        is_torn(media.last()),
    ensures
        no_torn(media.drop_last()),
        sequential_lsns(media.drop_last()),
        parse(media) == parse(media.drop_last()),
        media.drop_last() == full_frames(parse(media)),
{
    no_torn_sequential_is_canonical(media.drop_last());
    match media.last() {
        Frame::Torn { lsn, record } => {
            parse_push_torn(media.drop_last(), lsn, record);
            media.lemma_add_last_back();
        },
        Frame::Full { .. } => {},
    }
}

pub proof fn finish_torn_extends_parse_once(
    media: Seq<Frame>,
    record: replay_layer::JournalRecord,
)
    requires
        media.len() > 0,
        media.last() == (Frame::Torn { lsn: media.len(), record }),
        fully_parsed(media.drop_last()),
    ensures parse(replace_torn_tail(media, record))
        == parse(media).push(record),
{
    let prefix = media.drop_last();
    parse_push_full(prefix, media.len(), record);
    parse_push_torn(prefix, media.len(), record);
    media.lemma_add_last_back();
}

pub open spec fn initial_configuration(
    cfg: config_layer::FullConfig,
) -> WalConfiguration {
    WalConfiguration {
        runtime: WalRuntime {
            store: TypedWAL {
                cache: Seq::empty(),
                media: Seq::empty(),
                acked_len: 0,
                scan_phase: ScanPhase::Idle,
                scan_result: Seq::empty(),
            },
            slot: record_layer::ExecSlot::Idle,
            mode: record_layer::Mode::Online,
            append: append_layer::AppendControl::Idle,
        },
        evidence: journal_runtime_layer::initial_configuration(cfg).evidence,
    }
}

pub open spec fn journal_view(
    state: WalConfiguration,
) -> Seq<replay_layer::JournalRecord> {
    parse(state.runtime.store.media)
}

pub open spec fn journal_projection(
    state: WalConfiguration,
) -> journal_runtime_layer::JournalConfiguration {
    journal_runtime_layer::JournalConfiguration {
        runtime: journal_runtime_layer::ConcreteRuntime {
            store: journal_runtime_layer::AtomicJournal {
                journal: journal_view(state),
            },
            slot: state.runtime.slot,
            mode: state.runtime.mode,
            append: state.runtime.append,
        },
        evidence: state.evidence,
    }
}

pub open spec fn replay_view(
    cfg: config_layer::FullConfig,
    state: WalConfiguration,
) -> replay_layer::DurableBroker {
    replay_layer::replay(config_layer::erase_config(cfg), journal_view(state))
}

pub open spec fn runtime_record_enabled(
    cfg: config_layer::FullConfig,
    state: WalConfiguration,
    record: replay_layer::JournalRecord,
) -> bool {
    journal_runtime_layer::runtime_record_enabled(
        cfg, journal_projection(state), record,
    )
}

pub open spec fn slot_after_record(
    cfg: config_layer::FullConfig,
    state: WalConfiguration,
    record: replay_layer::JournalRecord,
) -> record_layer::ExecSlot {
    journal_runtime_layer::slot_after_record(
        cfg, journal_projection(state), record,
    )
}

pub open spec fn source_after_linearize(
    cfg: config_layer::FullConfig,
    state: WalConfiguration,
    record: replay_layer::JournalRecord,
) -> Option<p0_layer::PhysicalIndex> {
    journal_runtime_layer::source_after_linearize(
        cfg, journal_projection(state), record,
    )
}

pub open spec fn commit_source_after_linearize(
    state: WalConfiguration,
    record: replay_layer::JournalRecord,
) -> IMap<replay_layer::RequestId, Option<p0_layer::PhysicalIndex>> {
    journal_runtime_layer::commit_source_after_linearize(
        journal_projection(state), record,
    )
}

pub open spec fn wal_quiescent(state: WalConfiguration) -> bool {
    state.runtime.append is Idle
        && state.runtime.store.cache == journal_view(state)
        && state.runtime.store.acked_len == state.runtime.store.cache.len()
        && state.runtime.store.scan_phase == ScanPhase::Idle
}

pub enum WalEvent {
    WalStage { record: replay_layer::JournalRecord },
    WalWriteFull { record: replay_layer::JournalRecord },
    WalWriteTorn { record: replay_layer::JournalRecord },
    WalFinishTorn { record: replay_layer::JournalRecord },
    WalFlushAck { cut: nat },
    WalDiskFull { record: replay_layer::JournalRecord, cut: nat },
    InvokeEvent {
        request: replay_layer::RequestId,
        attempt: replay_layer::AttemptId,
        call: config_layer::CallDescriptor,
        journal_cut: nat,
        ack_cut: nat,
    },
    DeliverEvent {
        request: replay_layer::RequestId,
        attempt: replay_layer::AttemptId,
        observation: replay_layer::Observation,
        journal_cut: nat,
    },
    IgnoreStale {
        request: replay_layer::RequestId,
        attempt: replay_layer::AttemptId,
    },
    RetryRelease { request: replay_layer::RequestId },
    Crash,
    BeginScan,
    FinishScan,
    TruncateTail,
    AbortScan,
    BeginRecover,
    FinishRecover,
}

pub open spec fn wal_decode(
    event: global_layer::GlobalEvent,
) -> Option<WalEvent> {
    match event {
        global_layer::GlobalEvent::BrokerLinearize { .. }
        | global_layer::GlobalEvent::JournalAppendCall { .. }
        | global_layer::GlobalEvent::JournalAppendLinearize { .. }
        | global_layer::GlobalEvent::JournalAppendReturn { .. }
        | global_layer::GlobalEvent::JournalDiskFull { .. } => Option::None,
        global_layer::GlobalEvent::WalStage { record } => {
            Option::Some(WalEvent::WalStage { record })
        },
        global_layer::GlobalEvent::WalWriteFull { record } => {
            Option::Some(WalEvent::WalWriteFull { record })
        },
        global_layer::GlobalEvent::WalWriteTorn { record } => {
            Option::Some(WalEvent::WalWriteTorn { record })
        },
        global_layer::GlobalEvent::WalFinishTorn { record } => {
            Option::Some(WalEvent::WalFinishTorn { record })
        },
        global_layer::GlobalEvent::WalFlushAck { cut } => {
            Option::Some(WalEvent::WalFlushAck { cut })
        },
        global_layer::GlobalEvent::WalDiskFull { record, cut } => {
            Option::Some(WalEvent::WalDiskFull { record, cut })
        },
        global_layer::GlobalEvent::InvokeEvent {
            request, attempt, call, journal_cut, ack_cut,
        } => Option::Some(WalEvent::InvokeEvent {
            request, attempt, call, journal_cut, ack_cut,
        }),
        global_layer::GlobalEvent::DeliverEvent {
            request, attempt, observation, journal_cut,
        } => Option::Some(WalEvent::DeliverEvent {
            request, attempt, observation, journal_cut,
        }),
        global_layer::GlobalEvent::IgnoreStale { request, attempt } => {
            Option::Some(WalEvent::IgnoreStale { request, attempt })
        },
        global_layer::GlobalEvent::RetryRelease { request } => {
            Option::Some(WalEvent::RetryRelease { request })
        },
        global_layer::GlobalEvent::Crash => Option::Some(WalEvent::Crash),
        global_layer::GlobalEvent::BeginScan => {
            Option::Some(WalEvent::BeginScan)
        },
        global_layer::GlobalEvent::FinishScan => {
            Option::Some(WalEvent::FinishScan)
        },
        global_layer::GlobalEvent::TruncateTail => {
            Option::Some(WalEvent::TruncateTail)
        },
        global_layer::GlobalEvent::AbortScan => {
            Option::Some(WalEvent::AbortScan)
        },
        global_layer::GlobalEvent::BeginRecover => {
            Option::Some(WalEvent::BeginRecover)
        },
        global_layer::GlobalEvent::FinishRecover => {
            Option::Some(WalEvent::FinishRecover)
        },
    }
}

pub open spec fn wal_encode(event: WalEvent) -> global_layer::GlobalEvent {
    match event {
        WalEvent::WalStage { record } => global_layer::GlobalEvent::WalStage { record },
        WalEvent::WalWriteFull { record } => global_layer::GlobalEvent::WalWriteFull { record },
        WalEvent::WalWriteTorn { record } => global_layer::GlobalEvent::WalWriteTorn { record },
        WalEvent::WalFinishTorn { record } => global_layer::GlobalEvent::WalFinishTorn { record },
        WalEvent::WalFlushAck { cut } => global_layer::GlobalEvent::WalFlushAck { cut },
        WalEvent::WalDiskFull { record, cut } => global_layer::GlobalEvent::WalDiskFull { record, cut },
        WalEvent::InvokeEvent { request, attempt, call, journal_cut, ack_cut } =>
            global_layer::GlobalEvent::InvokeEvent { request, attempt, call, journal_cut, ack_cut },
        WalEvent::DeliverEvent { request, attempt, observation, journal_cut } =>
            global_layer::GlobalEvent::DeliverEvent { request, attempt, observation, journal_cut },
        WalEvent::IgnoreStale { request, attempt } =>
            global_layer::GlobalEvent::IgnoreStale { request, attempt },
        WalEvent::RetryRelease { request } => global_layer::GlobalEvent::RetryRelease { request },
        WalEvent::Crash => global_layer::GlobalEvent::Crash,
        WalEvent::BeginScan => global_layer::GlobalEvent::BeginScan,
        WalEvent::FinishScan => global_layer::GlobalEvent::FinishScan,
        WalEvent::TruncateTail => global_layer::GlobalEvent::TruncateTail,
        WalEvent::AbortScan => global_layer::GlobalEvent::AbortScan,
        WalEvent::BeginRecover => global_layer::GlobalEvent::BeginRecover,
        WalEvent::FinishRecover => global_layer::GlobalEvent::FinishRecover,
    }
}

pub open spec fn wal_constructor(event: global_layer::GlobalEvent) -> bool {
    match event {
        global_layer::GlobalEvent::BrokerLinearize { .. }
        | global_layer::GlobalEvent::JournalAppendCall { .. }
        | global_layer::GlobalEvent::JournalAppendLinearize { .. }
        | global_layer::GlobalEvent::JournalAppendReturn { .. }
        | global_layer::GlobalEvent::JournalDiskFull { .. } => false,
        global_layer::GlobalEvent::WalStage { .. }
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

pub proof fn wal_decode_classifier_exact(event: global_layer::GlobalEvent)
    ensures wal_decode(event).is_some() <==> wal_constructor(event),
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

pub proof fn wal_decode_encode(event: WalEvent)
    ensures wal_decode(wal_encode(event)) == Option::Some(event),
{
    match event {
        WalEvent::WalStage { .. }
        | WalEvent::WalWriteFull { .. }
        | WalEvent::WalWriteTorn { .. }
        | WalEvent::WalFinishTorn { .. }
        | WalEvent::WalFlushAck { .. }
        | WalEvent::WalDiskFull { .. }
        | WalEvent::InvokeEvent { .. }
        | WalEvent::DeliverEvent { .. }
        | WalEvent::IgnoreStale { .. }
        | WalEvent::RetryRelease { .. }
        | WalEvent::Crash
        | WalEvent::BeginScan
        | WalEvent::FinishScan
        | WalEvent::TruncateTail
        | WalEvent::AbortScan
        | WalEvent::BeginRecover
        | WalEvent::FinishRecover => {},
    }
}

pub open spec fn control_enabled(
    cfg: config_layer::FullConfig,
    state: WalConfiguration,
    event: WalEvent,
) -> bool {
    let durable = replay_view(cfg, state);
    let erased = config_layer::erase_config(cfg);
    match event {
        WalEvent::WalStage { record } | WalEvent::WalDiskFull { record, .. } => {
            state.runtime.mode != record_layer::Mode::Crashed
                && wal_quiescent(state)
                && runtime_record_enabled(cfg, state, record)
        },
        WalEvent::WalWriteFull { record } | WalEvent::WalWriteTorn { record } => {
            match state.runtime.append {
                append_layer::AppendControl::Called { record: called } => {
                    called == record && no_torn(state.runtime.store.media)
                        && runtime_record_enabled(cfg, state, record)
                },
                append_layer::AppendControl::Idle
                | append_layer::AppendControl::Linearized { .. } => false,
            }
        },
        WalEvent::WalFinishTorn { record } => {
            match state.runtime.append {
                append_layer::AppendControl::Called { record: called } => {
                    called == record
                        && state.runtime.store.media.len() > 0
                        && state.runtime.store.media.last() == (Frame::Torn {
                            lsn: state.runtime.store.media.len(), record,
                        })
                        && runtime_record_enabled(cfg, state, record)
                },
                append_layer::AppendControl::Idle
                | append_layer::AppendControl::Linearized { .. } => false,
            }
        },
        WalEvent::WalFlushAck { .. } => {
            state.runtime.mode != record_layer::Mode::Crashed
                && state.runtime.append is Linearized
                && state.runtime.store.cache == journal_view(state)
        },
        WalEvent::InvokeEvent { request, attempt, call, .. } => {
            state.runtime.mode == record_layer::Mode::Online
                && wal_quiescent(state)
                && state.runtime.slot == (record_layer::ExecSlot::Ready { request, attempt })
                && call == config_layer::canonical_call(cfg, request)
        },
        WalEvent::DeliverEvent { request, attempt, .. } => {
            state.runtime.mode == record_layer::Mode::Online
                && wal_quiescent(state)
                && state.runtime.slot == (record_layer::ExecSlot::InFlight { request, attempt })
        },
        WalEvent::IgnoreStale { request, attempt } => {
            state.runtime.mode == record_layer::Mode::Online
                && wal_quiescent(state)
                && state.runtime.slot != (record_layer::ExecSlot::InFlight { request, attempt })
        },
        WalEvent::RetryRelease { request } => {
            state.runtime.mode == record_layer::Mode::Online
                && wal_quiescent(state)
                && match state.runtime.slot {
                    record_layer::ExecSlot::ObservedFailure { request: observed, .. } => {
                        observed == request
                            && !query_layer::d_failure_conclusive(erased, durable, request)
                            && query_layer::d_started(durable, request) < erased.max_attempts[request]
                    },
                    record_layer::ExecSlot::Idle
                    | record_layer::ExecSlot::Ready { .. }
                    | record_layer::ExecSlot::InFlight { .. }
                    | record_layer::ExecSlot::Received { .. }
                    | record_layer::ExecSlot::ObservedSuccess { .. }
                    | record_layer::ExecSlot::ObservedUnknown { .. } => false,
                }
        },
        WalEvent::Crash => state.runtime.mode != record_layer::Mode::Crashed,
        WalEvent::BeginScan => {
            state.runtime.mode == record_layer::Mode::Crashed
                && state.runtime.store.scan_phase == ScanPhase::Idle
        },
        WalEvent::FinishScan => {
            state.runtime.mode == record_layer::Mode::Crashed
                && state.runtime.store.scan_phase == ScanPhase::Scanning
        },
        WalEvent::TruncateTail => {
            state.runtime.mode == record_layer::Mode::Crashed
                && state.runtime.store.scan_phase == ScanPhase::Scanned
                && state.runtime.store.scan_result == journal_view(state)
        },
        WalEvent::AbortScan => {
            state.runtime.mode == record_layer::Mode::Crashed
                && state.runtime.store.scan_phase != ScanPhase::Idle
        },
        WalEvent::BeginRecover => {
            state.runtime.mode == record_layer::Mode::Crashed
                && state.runtime.slot == record_layer::ExecSlot::Idle
                && state.runtime.append is Idle
                && state.runtime.store.scan_phase == ScanPhase::Truncated
                && state.runtime.store.media
                    == full_frames(state.runtime.store.scan_result)
        },
        WalEvent::FinishRecover => {
            state.runtime.mode == record_layer::Mode::Recovering
                && state.runtime.slot == record_layer::ExecSlot::Idle
                && wal_quiescent(state)
                && query_layer::recovery_complete_j(erased, journal_view(state))
        },
    }
}

pub open spec fn evidence_admissible(
    state: WalConfiguration,
    event: WalEvent,
) -> bool {
    match event {
        WalEvent::WalFlushAck { cut } | WalEvent::WalDiskFull { cut, .. } => {
            cut == journal_view(state).len()
        },
        WalEvent::InvokeEvent { request, attempt, journal_cut, ack_cut, .. } => {
            journal_cut == journal_view(state).len()
                && ack_cut == state.evidence.acknowledged_prefix.len()
                && journal_runtime_layer::start_covered_by_cut(
                    state.evidence.records, request, attempt, ack_cut,
                )
        },
        WalEvent::DeliverEvent { journal_cut, .. } => {
            journal_cut == journal_view(state).len()
        },
        WalEvent::WalStage { .. }
        | WalEvent::WalWriteFull { .. }
        | WalEvent::WalWriteTorn { .. }
        | WalEvent::WalFinishTorn { .. }
        | WalEvent::IgnoreStale { .. }
        | WalEvent::RetryRelease { .. }
        | WalEvent::Crash
        | WalEvent::BeginScan
        | WalEvent::FinishScan
        | WalEvent::TruncateTail
        | WalEvent::AbortScan
        | WalEvent::BeginRecover
        | WalEvent::FinishRecover => true,
    }
}

pub open spec fn admissibly_enabled(
    cfg: config_layer::FullConfig,
    state: WalConfiguration,
    event: WalEvent,
) -> bool {
    control_enabled(cfg, state, event) && evidence_admissible(state, event)
}

pub open spec fn linearized_configuration(
    cfg: config_layer::FullConfig,
    state: WalConfiguration,
    record: replay_layer::JournalRecord,
    media: Seq<Frame>,
) -> WalConfiguration {
    WalConfiguration {
        runtime: WalRuntime {
            store: TypedWAL { media, ..state.runtime.store },
            slot: slot_after_record(cfg, state, record),
            append: append_layer::AppendControl::Linearized { record },
            ..state.runtime
        },
        evidence: journal_runtime_layer::GhostEvidence {
            records: state.evidence.records.push(record),
            slot_source: source_after_linearize(cfg, state, record),
            commit_source: commit_source_after_linearize(state, record),
            ..state.evidence
        },
    }
}

pub open spec fn apply(
    cfg: config_layer::FullConfig,
    state: WalConfiguration,
    event: WalEvent,
) -> WalConfiguration {
    match event {
        WalEvent::WalStage { record } => WalConfiguration {
            runtime: WalRuntime {
                store: TypedWAL {
                    cache: state.runtime.store.cache.push(record),
                    ..state.runtime.store
                },
                append: append_layer::AppendControl::Called { record },
                ..state.runtime
            },
            ..state
        },
        WalEvent::WalWriteFull { record } => linearized_configuration(
            cfg,
            state,
            record,
            state.runtime.store.media.push(Frame::Full {
                lsn: state.runtime.store.media.len() + 1,
                record,
            }),
        ),
        WalEvent::WalWriteTorn { record } => WalConfiguration {
            runtime: WalRuntime {
                store: TypedWAL {
                    media: state.runtime.store.media.push(Frame::Torn {
                        lsn: state.runtime.store.media.len() + 1,
                        record,
                    }),
                    ..state.runtime.store
                },
                ..state.runtime
            },
            ..state
        },
        WalEvent::WalFinishTorn { record } => linearized_configuration(
            cfg, state, record,
            replace_torn_tail(state.runtime.store.media, record),
        ),
        WalEvent::WalFlushAck { cut } => WalConfiguration {
            runtime: WalRuntime {
                store: TypedWAL {
                    acked_len: state.runtime.store.cache.len(),
                    ..state.runtime.store
                },
                append: append_layer::AppendControl::Idle,
                ..state.runtime
            },
            evidence: journal_runtime_layer::GhostEvidence {
                ack_cuts: state.evidence.ack_cuts.push(cut),
                acknowledged_prefix: state.evidence.records,
                ..state.evidence
            },
        },
        WalEvent::WalDiskFull { .. } | WalEvent::IgnoreStale { .. } => state,
        WalEvent::InvokeEvent { request, attempt, call, journal_cut, ack_cut } =>
            WalConfiguration {
                runtime: WalRuntime {
                    slot: record_layer::ExecSlot::InFlight { request, attempt },
                    ..state.runtime
                },
                evidence: journal_runtime_layer::GhostEvidence {
                    physical: state.evidence.physical.push(p0_layer::PhysicalEvent::Invoke {
                        request, attempt, call, journal_cut, ack_cut,
                    }),
                    slot_source: Option::None,
                    ..state.evidence
                },
            },
        WalEvent::DeliverEvent { request, attempt, observation, journal_cut } =>
            WalConfiguration {
                runtime: WalRuntime {
                    slot: record_layer::ExecSlot::Received { request, attempt, observation },
                    ..state.runtime
                },
                evidence: journal_runtime_layer::GhostEvidence {
                    physical: state.evidence.physical.push(p0_layer::PhysicalEvent::Delivered {
                        request, attempt, observation, journal_cut,
                    }),
                    slot_source: Option::Some(state.evidence.physical.len()),
                    ..state.evidence
                },
            },
        WalEvent::RetryRelease { .. } => WalConfiguration {
            runtime: WalRuntime { slot: record_layer::ExecSlot::Idle, ..state.runtime },
            evidence: journal_runtime_layer::GhostEvidence {
                slot_source: Option::None,
                ..state.evidence
            },
        },
        WalEvent::Crash => WalConfiguration {
            runtime: WalRuntime {
                store: TypedWAL {
                    cache: Seq::empty(),
                    acked_len: 0,
                    scan_phase: ScanPhase::Idle,
                    scan_result: Seq::empty(),
                    ..state.runtime.store
                },
                slot: record_layer::ExecSlot::Idle,
                mode: record_layer::Mode::Crashed,
                append: append_layer::AppendControl::Idle,
            },
            evidence: journal_runtime_layer::GhostEvidence {
                slot_source: Option::None,
                ..state.evidence
            },
        },
        WalEvent::BeginScan => WalConfiguration {
            runtime: WalRuntime {
                store: TypedWAL { scan_phase: ScanPhase::Scanning, ..state.runtime.store },
                ..state.runtime
            },
            ..state
        },
        WalEvent::FinishScan => WalConfiguration {
            runtime: WalRuntime {
                store: TypedWAL {
                    scan_phase: ScanPhase::Scanned,
                    scan_result: journal_view(state),
                    ..state.runtime.store
                },
                ..state.runtime
            },
            ..state
        },
        WalEvent::TruncateTail => WalConfiguration {
            runtime: WalRuntime {
                store: TypedWAL {
                    media: full_frames(state.runtime.store.scan_result),
                    scan_phase: ScanPhase::Truncated,
                    ..state.runtime.store
                },
                ..state.runtime
            },
            ..state
        },
        WalEvent::AbortScan => WalConfiguration {
            runtime: WalRuntime {
                store: TypedWAL {
                    scan_phase: ScanPhase::Idle,
                    scan_result: Seq::empty(),
                    ..state.runtime.store
                },
                ..state.runtime
            },
            ..state
        },
        WalEvent::BeginRecover => WalConfiguration {
            runtime: WalRuntime {
                store: TypedWAL {
                    cache: state.runtime.store.scan_result,
                    acked_len: state.runtime.store.scan_result.len(),
                    scan_phase: ScanPhase::Idle,
                    scan_result: Seq::empty(),
                    ..state.runtime.store
                },
                mode: record_layer::Mode::Recovering,
                ..state.runtime
            },
            ..state
        },
        WalEvent::FinishRecover => WalConfiguration {
            runtime: WalRuntime { mode: record_layer::Mode::Online, ..state.runtime },
            ..state
        },
    }
}

pub open spec fn sequential_and_torn_tail(wal: TypedWAL) -> bool {
    sequential_lsns(wal.media) && torn_tail_only(wal.media)
}

pub open spec fn crashed_shape(
    wal: TypedWAL,
    mode: record_layer::Mode,
    append: append_layer::AppendControl<replay_layer::JournalRecord>,
) -> bool {
    mode != record_layer::Mode::Crashed || {
        wal.cache.len() == 0 && wal.acked_len == 0 && append is Idle
    }
}

pub open spec fn append_storage_shape(
    wal: TypedWAL,
    mode: record_layer::Mode,
    append: append_layer::AppendControl<replay_layer::JournalRecord>,
) -> bool {
    mode == record_layer::Mode::Crashed || match append {
        append_layer::AppendControl::Idle => {
            wal.cache == parse(wal.media) && wal.acked_len == wal.cache.len()
        },
        append_layer::AppendControl::Called { record } => {
            wal.cache.len() == wal.acked_len + 1
                && wal.cache.len() > 0
                && wal.cache.last() == record
                && parse(wal.media) == wal.cache.take(wal.acked_len as int)
        },
        append_layer::AppendControl::Linearized { record } => {
            wal.cache == parse(wal.media)
                && wal.cache.len() == wal.acked_len + 1
                && wal.cache.len() > 0
                && wal.cache.last() == record
        },
    }
}

pub open spec fn acknowledged_storage_prefix(
    wal: TypedWAL,
    mode: record_layer::Mode,
) -> bool {
    mode == record_layer::Mode::Crashed || {
        wal.acked_len <= wal.cache.len()
            && wal.acked_len <= parse(wal.media).len()
            && wal.cache.take(wal.acked_len as int)
                == parse(wal.media).take(wal.acked_len as int)
    }
}

pub open spec fn cache_media_correspondence(
    wal: TypedWAL,
    mode: record_layer::Mode,
) -> bool {
    mode == record_layer::Mode::Crashed || {
        append_layer::is_prefix(parse(wal.media), wal.cache)
            && wal.cache.len() <= parse(wal.media).len() + 1
            && append_layer::is_prefix(frame_records(wal.media), wal.cache)
    }
}

pub open spec fn scan_shape(
    wal: TypedWAL,
    mode: record_layer::Mode,
) -> bool {
    (wal.scan_phase == ScanPhase::Idle || mode == record_layer::Mode::Crashed)
        && match wal.scan_phase {
            ScanPhase::Idle | ScanPhase::Scanning => wal.scan_result.len() == 0,
            ScanPhase::Scanned | ScanPhase::Truncated => {
                wal.scan_result == parse(wal.media)
            },
        }
}

pub open spec fn canonical_media_shape(wal: TypedWAL) -> bool {
    (wal.scan_phase != ScanPhase::Truncated
        || wal.media == full_frames(wal.scan_result))
        && (!no_torn(wal.media)
            || wal.media == full_frames(parse(wal.media)))
}

pub open spec fn wal_invariant(
    cfg: config_layer::FullConfig,
    wal: TypedWAL,
    mode: record_layer::Mode,
    append: append_layer::AppendControl<replay_layer::JournalRecord>,
) -> bool {
    sequential_and_torn_tail(wal)
        && replay_layer::journal_legal(
            config_layer::erase_config(cfg), parse(wal.media),
        )
        && crashed_shape(wal, mode, append)
        && append_storage_shape(wal, mode, append)
        && acknowledged_storage_prefix(wal, mode)
        && cache_media_correspondence(wal, mode)
        && scan_shape(wal, mode)
        && canonical_media_shape(wal)
}

pub open spec fn append_view(
    state: WalConfiguration,
) -> append_layer::State<replay_layer::JournalRecord> {
    append_layer::State {
        append: state.runtime.append,
        evidence: append_layer::AppendGhost {
            records: state.evidence.records,
            ack_cuts: state.evidence.ack_cuts,
            acknowledged_prefix: state.evidence.acknowledged_prefix,
        },
    }
}

pub open spec fn append_event(
    event: WalEvent,
) -> append_layer::Event<replay_layer::JournalRecord> {
    match event {
        WalEvent::WalStage { record } => append_layer::Event::Call { record },
        WalEvent::WalWriteFull { record } | WalEvent::WalFinishTorn { record } =>
            append_layer::Event::Linearize { record },
        WalEvent::WalFlushAck { cut } => append_layer::Event::ReturnOk { cut },
        WalEvent::WalDiskFull { record, cut } => append_layer::Event::DiskFull { record, cut },
        WalEvent::Crash => append_layer::Event::Crash,
        WalEvent::WalWriteTorn { .. } => append_layer::Event::Stutter { kind: 0 },
        WalEvent::InvokeEvent { .. } => append_layer::Event::Stutter { kind: 1 },
        WalEvent::DeliverEvent { .. } => append_layer::Event::Stutter { kind: 2 },
        WalEvent::IgnoreStale { .. } => append_layer::Event::Stutter { kind: 3 },
        WalEvent::RetryRelease { .. } => append_layer::Event::Stutter { kind: 4 },
        WalEvent::BeginScan => append_layer::Event::Stutter { kind: 5 },
        WalEvent::FinishScan => append_layer::Event::Stutter { kind: 6 },
        WalEvent::TruncateTail => append_layer::Event::Stutter { kind: 7 },
        WalEvent::AbortScan => append_layer::Event::Stutter { kind: 8 },
        WalEvent::BeginRecover => append_layer::Event::Stutter { kind: 9 },
        WalEvent::FinishRecover => append_layer::Event::Stutter { kind: 10 },
    }
}

pub open spec fn basic_invariant(
    cfg: config_layer::FullConfig,
    state: WalConfiguration,
) -> bool {
    wal_invariant(cfg, state.runtime.store, state.runtime.mode, state.runtime.append)
        && state.evidence.records == journal_view(state)
        && append_layer::b1_invariant(append_view(state))
}

pub open spec fn wal_local_step(
    cfg: config_layer::FullConfig,
    before: WalConfiguration,
    event: WalEvent,
    after: WalConfiguration,
) -> bool {
    admissibly_enabled(cfg, before, event) && after == apply(cfg, before, event)
}

pub open spec fn wal_runtime_step(
    cfg: config_layer::FullConfig,
    before: WalConfiguration,
    event: global_layer::GlobalEvent,
    after: WalConfiguration,
) -> bool {
    match wal_decode(event) {
        Option::None => false,
        Option::Some(local) => wal_local_step(cfg, before, local, after),
    }
}

pub proof fn append_view_initial(cfg: config_layer::FullConfig)
    ensures append_view(initial_configuration(cfg)) == append_layer::initial_state(),
{
}

pub proof fn append_view_apply(
    cfg: config_layer::FullConfig,
    state: WalConfiguration,
    event: WalEvent,
)
    ensures append_view(apply(cfg, state, event))
        == append_layer::apply(append_view(state), append_event(event)),
{
    match event {
        WalEvent::WalStage { .. }
        | WalEvent::WalWriteFull { .. }
        | WalEvent::WalWriteTorn { .. }
        | WalEvent::WalFinishTorn { .. }
        | WalEvent::WalFlushAck { .. }
        | WalEvent::WalDiskFull { .. }
        | WalEvent::InvokeEvent { .. }
        | WalEvent::DeliverEvent { .. }
        | WalEvent::IgnoreStale { .. }
        | WalEvent::RetryRelease { .. }
        | WalEvent::Crash
        | WalEvent::BeginScan
        | WalEvent::FinishScan
        | WalEvent::TruncateTail
        | WalEvent::AbortScan
        | WalEvent::BeginRecover
        | WalEvent::FinishRecover => {},
    }
}

pub proof fn admissible_step_projects_to_append(
    cfg: config_layer::FullConfig,
    state: WalConfiguration,
    event: WalEvent,
)
    requires
        state.evidence.records == journal_view(state),
        admissibly_enabled(cfg, state, event),
    ensures append_layer::enabled(append_view(state), append_event(event)),
{
    match event {
        WalEvent::WalStage { .. }
        | WalEvent::WalWriteFull { .. }
        | WalEvent::WalWriteTorn { .. }
        | WalEvent::WalFinishTorn { .. }
        | WalEvent::WalFlushAck { .. }
        | WalEvent::WalDiskFull { .. }
        | WalEvent::InvokeEvent { .. }
        | WalEvent::DeliverEvent { .. }
        | WalEvent::IgnoreStale { .. }
        | WalEvent::RetryRelease { .. }
        | WalEvent::Crash
        | WalEvent::BeginScan
        | WalEvent::FinishScan
        | WalEvent::TruncateTail
        | WalEvent::AbortScan
        | WalEvent::BeginRecover
        | WalEvent::FinishRecover => {},
    }
}

pub proof fn initial_wal_invariant(cfg: config_layer::FullConfig)
    ensures wal_invariant(
        cfg,
        initial_configuration(cfg).runtime.store,
        initial_configuration(cfg).runtime.mode,
        initial_configuration(cfg).runtime.append,
    ),
{
    let empty_records: Seq<replay_layer::JournalRecord> = Seq::empty();
    let empty_media: Seq<Frame> = Seq::empty();
    assert(parse(empty_media) == empty_records);
    assert(full_frames(empty_records) == empty_media);
    assert(frame_records(empty_media) == empty_records);
    assert(replay_layer::journal_legal(
        config_layer::erase_config(cfg), empty_records,
    ));
    append_layer::prefix_reflexive(empty_records);
}

pub proof fn initial_basic_invariant(cfg: config_layer::FullConfig)
    ensures basic_invariant(cfg, initial_configuration(cfg)),
{
    initial_wal_invariant(cfg);
    append_view_initial(cfg);
    append_layer::initial_invariant::<replay_layer::JournalRecord>();
}

pub proof fn apply_preserves_wal_invariant(
    cfg: config_layer::FullConfig,
    before: WalConfiguration,
    event: WalEvent,
)
    requires
        wal_invariant(
            cfg, before.runtime.store, before.runtime.mode, before.runtime.append,
        ),
        admissibly_enabled(cfg, before, event),
    ensures wal_invariant(
        cfg,
        apply(cfg, before, event).runtime.store,
        apply(cfg, before, event).runtime.mode,
        apply(cfg, before, event).runtime.append,
    ),
{
    let after = apply(cfg, before, event);
    match event {
        WalEvent::WalStage { record } => {
            append_layer::take_push_stable(
                before.runtime.store.cache,
                record,
                before.runtime.store.acked_len,
            );
            append_layer::take_full(before.runtime.store.cache);
            prefix_survives_push(
                journal_view(before), before.runtime.store.cache, record,
            );
            prefix_survives_push(
                frame_records(before.runtime.store.media),
                before.runtime.store.cache,
                record,
            );
            assert(sequential_and_torn_tail(after.runtime.store));
            assert(replay_layer::journal_legal(
                config_layer::erase_config(cfg), parse(after.runtime.store.media),
            ));
            assert(crashed_shape(after.runtime.store, after.runtime.mode, after.runtime.append));
            assert(append_storage_shape(
                after.runtime.store, after.runtime.mode, after.runtime.append,
            ));
            assert(acknowledged_storage_prefix(after.runtime.store, after.runtime.mode));
            assert(cache_media_correspondence(after.runtime.store, after.runtime.mode));
            assert(scan_shape(after.runtime.store, after.runtime.mode));
            assert(canonical_media_shape(after.runtime.store));
            assert(wal_invariant(
                cfg, after.runtime.store, after.runtime.mode, after.runtime.append,
            ));
        },
        WalEvent::WalWriteFull { record } => {
            canonical_media_facts(before.runtime.store.media);
            called_cache_decomposition(
                before.runtime.store.cache,
                journal_view(before),
                before.runtime.store.acked_len,
                record,
            );
            push_full_media_shape(before.runtime.store.media, record);
            parse_push_full(
                before.runtime.store.media,
                before.runtime.store.media.len() + 1,
                record,
            );
            frame_records_push(
                before.runtime.store.media,
                Frame::Full {
                    lsn: before.runtime.store.media.len() + 1,
                    record,
                },
            );
            full_frames_push(journal_view(before), record);
            replay_layer::journal_legal_push(
                config_layer::erase_config(cfg), journal_view(before), record,
            );
            append_layer::prefix_reflexive(before.runtime.store.cache);
            assert(wal_invariant(
                cfg, after.runtime.store, after.runtime.mode, after.runtime.append,
            ));
        },
        WalEvent::WalWriteTorn { record } => {
            canonical_media_facts(before.runtime.store.media);
            called_cache_decomposition(
                before.runtime.store.cache,
                journal_view(before),
                before.runtime.store.acked_len,
                record,
            );
            push_torn_media_shape(before.runtime.store.media, record);
            parse_push_torn(
                before.runtime.store.media,
                before.runtime.store.media.len() + 1,
                record,
            );
            frame_records_push(
                before.runtime.store.media,
                Frame::Torn {
                    lsn: before.runtime.store.media.len() + 1,
                    record,
                },
            );
            append_layer::prefix_reflexive(before.runtime.store.cache);
            assert(wal_invariant(
                cfg, after.runtime.store, after.runtime.mode, after.runtime.append,
            ));
        },
        WalEvent::WalFinishTorn { record } => {
            let prefix = before.runtime.store.media.drop_last();
            torn_tail_decomposition(before.runtime.store.media);
            push_full_media_shape(prefix, record);
            called_cache_decomposition(
                before.runtime.store.cache,
                journal_view(before),
                before.runtime.store.acked_len,
                record,
            );
            finish_torn_extends_parse_once(before.runtime.store.media, record);
            full_frames_len(journal_view(before));
            full_frames_push(journal_view(before), record);
            frame_records_full_frames(journal_view(before));
            frame_records_push(
                prefix,
                Frame::Full { lsn: before.runtime.store.media.len(), record },
            );
            assert(prefix == full_frames(journal_view(before)));
            assert(prefix.len() == journal_view(before).len());
            assert(before.runtime.store.media.len() == prefix.len() + 1);
            assert(replace_torn_tail(before.runtime.store.media, record)
                == prefix.push(Frame::Full {
                    lsn: before.runtime.store.media.len(), record,
                }));
            assert(after.runtime.store.media
                == full_frames(journal_view(before).push(record)));
            assert(parse(after.runtime.store.media)
                == journal_view(before).push(record));
            canonical_media_facts(after.runtime.store.media);
            replay_layer::journal_legal_push(
                config_layer::erase_config(cfg), journal_view(before), record,
            );
            append_layer::prefix_reflexive(before.runtime.store.cache);
            assert(wal_invariant(
                cfg, after.runtime.store, after.runtime.mode, after.runtime.append,
            ));
        },
        WalEvent::TruncateTail => {
            truncate_preserves_parse(before.runtime.store.media);
            parse_full_frames(before.runtime.store.scan_result);
            frame_records_full_frames(before.runtime.store.scan_result);
            full_frames_no_torn(before.runtime.store.scan_result);
            full_frames_sequential(before.runtime.store.scan_result);
            full_frames_torn_tail_only(before.runtime.store.scan_result);
            assert(wal_invariant(
                cfg, after.runtime.store, after.runtime.mode, after.runtime.append,
            ));
        },
        WalEvent::BeginRecover => {
            canonical_media_facts(before.runtime.store.media);
            parse_full_frames(before.runtime.store.scan_result);
            frame_records_full_frames(before.runtime.store.scan_result);
            append_layer::prefix_reflexive(before.runtime.store.scan_result);
            assert(wal_invariant(
                cfg, after.runtime.store, after.runtime.mode, after.runtime.append,
            ));
        },
        WalEvent::WalFlushAck { .. }
        | WalEvent::WalDiskFull { .. }
        | WalEvent::InvokeEvent { .. }
        | WalEvent::DeliverEvent { .. }
        | WalEvent::IgnoreStale { .. }
        | WalEvent::RetryRelease { .. }
        | WalEvent::Crash
        | WalEvent::BeginScan
        | WalEvent::FinishScan
        | WalEvent::AbortScan
        | WalEvent::FinishRecover => {},
    }
    assert(wal_invariant(
        cfg, after.runtime.store, after.runtime.mode, after.runtime.append,
    ));
}

pub proof fn local_step_preserves_basic_invariant(
    cfg: config_layer::FullConfig,
    before: WalConfiguration,
    event: WalEvent,
    after: WalConfiguration,
)
    requires basic_invariant(cfg, before), wal_local_step(cfg, before, event, after),
    ensures basic_invariant(cfg, after),
{
    assert(after == apply(cfg, before, event));
    append_view_apply(cfg, before, event);
    admissible_step_projects_to_append(cfg, before, event);
    append_layer::step_preserves_invariant(append_view(before), append_event(event));
    apply_preserves_wal_invariant(cfg, before, event);
    match event {
        WalEvent::WalWriteFull { record } => {
            parse_push_full(
                before.runtime.store.media,
                before.runtime.store.media.len() + 1,
                record,
            );
        },
        WalEvent::WalFinishTorn { record } => {
            torn_tail_decomposition(before.runtime.store.media);
            finish_torn_extends_parse_once(before.runtime.store.media, record);
        },
        WalEvent::TruncateTail => truncate_preserves_parse(before.runtime.store.media),
        WalEvent::WalWriteTorn { record } => parse_push_torn(
            before.runtime.store.media,
            before.runtime.store.media.len() + 1,
            record,
        ),
        WalEvent::WalStage { .. }
        | WalEvent::WalFlushAck { .. }
        | WalEvent::WalDiskFull { .. }
        | WalEvent::InvokeEvent { .. }
        | WalEvent::DeliverEvent { .. }
        | WalEvent::IgnoreStale { .. }
        | WalEvent::RetryRelease { .. }
        | WalEvent::Crash
        | WalEvent::BeginScan
        | WalEvent::FinishScan
        | WalEvent::AbortScan
        | WalEvent::BeginRecover
        | WalEvent::FinishRecover => {},
    }
}

pub proof fn runtime_step_preserves_basic_invariant(
    cfg: config_layer::FullConfig,
    before: WalConfiguration,
    event: global_layer::GlobalEvent,
    after: WalConfiguration,
)
    requires basic_invariant(cfg, before), wal_runtime_step(cfg, before, event, after),
    ensures basic_invariant(cfg, after),
{
    match wal_decode(event) {
        Option::None => {},
        Option::Some(local) => local_step_preserves_basic_invariant(
            cfg, before, local, after,
        ),
    }
}

pub proof fn basic_invariant_acknowledged_prefix_durable(
    cfg: config_layer::FullConfig,
    state: WalConfiguration,
)
    requires basic_invariant(cfg, state),
    ensures append_layer::is_prefix(
        state.evidence.acknowledged_prefix, journal_view(state),
    ),
{
}

pub proof fn apply_parse_monotone(
    cfg: config_layer::FullConfig,
    before: WalConfiguration,
    event: WalEvent,
)
    requires
        wal_invariant(
            cfg, before.runtime.store, before.runtime.mode, before.runtime.append,
        ),
        admissibly_enabled(cfg, before, event),
    ensures append_layer::is_prefix(
        journal_view(before), journal_view(apply(cfg, before, event)),
    ),
{
    match event {
        WalEvent::WalWriteFull { record } => {
            canonical_media_facts(before.runtime.store.media);
            parse_push_full(
                before.runtime.store.media,
                before.runtime.store.media.len() + 1,
                record,
            );
            append_layer::prefix_reflexive(journal_view(before));
            prefix_survives_push(
                journal_view(before), journal_view(before), record,
            );
        },
        WalEvent::WalFinishTorn { record } => {
            torn_tail_decomposition(before.runtime.store.media);
            finish_torn_extends_parse_once(before.runtime.store.media, record);
            append_layer::prefix_reflexive(journal_view(before));
            prefix_survives_push(
                journal_view(before), journal_view(before), record,
            );
        },
        WalEvent::WalWriteTorn { record } => {
            parse_push_torn(
                before.runtime.store.media,
                before.runtime.store.media.len() + 1,
                record,
            );
            append_layer::prefix_reflexive(journal_view(before));
        },
        WalEvent::TruncateTail => {
            truncate_preserves_parse(before.runtime.store.media);
            append_layer::prefix_reflexive(journal_view(before));
        },
        WalEvent::WalStage { .. }
        | WalEvent::WalFlushAck { .. }
        | WalEvent::WalDiskFull { .. }
        | WalEvent::InvokeEvent { .. }
        | WalEvent::DeliverEvent { .. }
        | WalEvent::IgnoreStale { .. }
        | WalEvent::RetryRelease { .. }
        | WalEvent::Crash
        | WalEvent::BeginScan
        | WalEvent::FinishScan
        | WalEvent::AbortScan
        | WalEvent::BeginRecover
        | WalEvent::FinishRecover => {
            append_layer::prefix_reflexive(journal_view(before));
        },
    }
}

pub proof fn runtime_step_parse_monotone(
    cfg: config_layer::FullConfig,
    before: WalConfiguration,
    event: global_layer::GlobalEvent,
    after: WalConfiguration,
)
    requires
        wal_invariant(
            cfg, before.runtime.store, before.runtime.mode, before.runtime.append,
        ),
        wal_runtime_step(cfg, before, event, after),
    ensures append_layer::is_prefix(journal_view(before), journal_view(after)),
{
    match wal_decode(event) {
        Option::None => {},
        Option::Some(local) => {
            assert(after == apply(cfg, before, local));
            apply_parse_monotone(cfg, before, local);
        },
    }
}

pub proof fn wal_step_decodes(
    cfg: config_layer::FullConfig,
    before: WalConfiguration,
    event: global_layer::GlobalEvent,
    after: WalConfiguration,
)
    requires wal_runtime_step(cfg, before, event, after),
    ensures exists|local: WalEvent| #![auto]
        wal_decode(event) == Option::Some(local)
            && wal_local_step(cfg, before, local, after),
{
    match wal_decode(event) {
        Option::None => {},
        Option::Some(local) => {
            assert(wal_decode(event) == Option::Some(local));
        },
    }
}

pub proof fn wal_step_is_closed(
    cfg: config_layer::FullConfig,
    before: WalConfiguration,
    event: global_layer::GlobalEvent,
    after: WalConfiguration,
)
    requires wal_runtime_step(cfg, before, event, after),
    ensures wal_constructor(event),
{
    wal_step_decodes(cfg, before, event, after);
    wal_decode_classifier_exact(event);
}

pub struct WalExecution {
    pub configs: Seq<WalConfiguration>,
    pub events: Seq<global_layer::GlobalEvent>,
}

pub open spec fn exec(
    cfg: config_layer::FullConfig,
    execution: WalExecution,
) -> bool {
    execution.configs.len() == execution.events.len() + 1
        && execution.configs[0] == initial_configuration(cfg)
        && forall|index: nat| index < execution.events.len() ==>
            #[trigger] wal_runtime_step(
                cfg,
                execution.configs[index as int],
                execution.events[index as int],
                execution.configs[(index + 1) as int],
            )
}

pub open spec fn execs(
    cfg: config_layer::FullConfig,
) -> ISet<WalExecution> {
    ISet::new(|execution: WalExecution| exec(cfg, execution))
}

pub open spec fn execution_prefix(
    execution: WalExecution,
    length: nat,
) -> WalExecution {
    WalExecution {
        configs: execution.configs.take((length + 1) as int),
        events: execution.events.take(length as int),
    }
}

pub proof fn exec_prefix(
    cfg: config_layer::FullConfig,
    execution: WalExecution,
    length: nat,
)
    requires exec(cfg, execution), length <= execution.events.len(),
    ensures exec(cfg, execution_prefix(execution, length)),
{
    let prefix = execution_prefix(execution, length);
    assert(prefix.events.len() == length);
    assert(prefix.configs.len() == length + 1);
    assert(prefix.configs[0] == execution.configs[0]);
    assert forall|index: nat| index < prefix.events.len() implies
        #[trigger] wal_runtime_step(
            cfg,
            prefix.configs[index as int],
            prefix.events[index as int],
            prefix.configs[(index + 1) as int],
        ) by {
        assert(index < execution.events.len());
        assert(prefix.events[index as int] == execution.events[index as int]);
        assert(prefix.configs[index as int] == execution.configs[index as int]);
        assert(prefix.configs[(index + 1) as int]
            == execution.configs[(index + 1) as int]);
    }
}

pub open spec fn wal_trace_closed(
    events: Seq<global_layer::GlobalEvent>,
) -> bool
    decreases events.len()
{
    events.len() == 0 || {
        wal_trace_closed(events.drop_last()) && wal_constructor(events.last())
    }
}

pub proof fn exec_trace_closed(
    cfg: config_layer::FullConfig,
    execution: WalExecution,
)
    requires exec(cfg, execution),
    ensures wal_trace_closed(execution.events),
    decreases execution.events.len(),
{
    if execution.events.len() > 0 {
        let length: nat = (execution.events.len() - 1) as nat;
        let prefix = execution_prefix(execution, length);
        exec_prefix(cfg, execution, length);
        exec_trace_closed(cfg, prefix);
        assert(prefix.events =~= execution.events.drop_last());
        assert(execution.events[length as int] == execution.events.last());
        wal_step_is_closed(
            cfg,
            execution.configs[length as int],
            execution.events.last(),
            execution.configs[(length + 1) as int],
        );
    }
}

pub proof fn every_exec_configuration_is_basic(
    cfg: config_layer::FullConfig,
    execution: WalExecution,
)
    requires exec(cfg, execution),
    ensures forall|index: nat| index < execution.configs.len() ==>
        #[trigger] basic_invariant(cfg, execution.configs[index as int]),
    decreases execution.events.len(),
{
    if execution.events.len() == 0 {
        initial_basic_invariant(cfg);
    } else {
        let last_index: nat = (execution.events.len() - 1) as nat;
        let prefix = execution_prefix(execution, last_index);
        exec_prefix(cfg, execution, last_index);
        every_exec_configuration_is_basic(cfg, prefix);
        assert(prefix.configs.len() == execution.events.len());
        assert forall|index: nat| index < execution.events.len() implies
            #[trigger] basic_invariant(
                cfg, execution.configs[index as int],
            ) by {
            assert(index < prefix.configs.len());
            assert(prefix.configs[index as int]
                == execution.configs[index as int]);
        }
        assert(basic_invariant(cfg, execution.configs[last_index as int]));
        runtime_step_preserves_basic_invariant(
            cfg,
            execution.configs[last_index as int],
            execution.events[last_index as int],
            execution.configs[(last_index + 1) as int],
        );
        assert forall|index: nat| index < execution.configs.len() implies
            #[trigger] basic_invariant(cfg, execution.configs[index as int]) by {
            if index < execution.events.len() {
                assert(index < prefix.configs.len());
                assert(prefix.configs[index as int] == execution.configs[index as int]);
            } else {
                assert(index == execution.events.len());
                assert(index == last_index + 1);
            }
        }
    }
}

} // verus!
