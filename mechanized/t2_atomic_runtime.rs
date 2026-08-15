use vstd::prelude::*;

#[path = "t1_parameterized_broker_safety.rs"]
pub mod t1_layer;

verus! {

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

// T2-J0 is the independent atomic-Journal runtime.  The concrete state below
// stores the Journal and volatile executor/interface control only.  In
// particular, it has no DurableBroker, replay cache, phase map, commit log, or
// other abstract Broker shadow.  Replay is computed from the Journal when a
// transition needs a durable query.

pub struct AtomicJournal {
    pub journal: Seq<replay_layer::JournalRecord>,
}

pub struct ConcreteRuntime {
    pub store: AtomicJournal,
    pub slot: record_layer::ExecSlot,
    pub mode: record_layer::Mode,
    pub append: append_layer::AppendControl<replay_layer::JournalRecord>,
}

// Proof evidence is separate from ConcreteRuntime.  No executable control
// predicate below reads this object.  These are exactly the six fields in the
// paper's GhostEvidence definition.
pub struct GhostEvidence {
    pub records: Seq<replay_layer::JournalRecord>,
    pub physical: Seq<p0_layer::PhysicalEvent>,
    pub ack_cuts: Seq<nat>,
    pub acknowledged_prefix: Seq<replay_layer::JournalRecord>,
    pub slot_source: Option<p0_layer::PhysicalIndex>,
    pub commit_source:
        IMap<replay_layer::RequestId, Option<p0_layer::PhysicalIndex>>,
}

pub struct JournalConfiguration {
    pub runtime: ConcreteRuntime,
    pub evidence: GhostEvidence,
}

// This local alphabet contains exactly the eleven constructors accepted by
// JournalRuntimeStep.  JournalAppendLinearize is intentionally distinct from
// the Broker's BrokerLinearize label; T2 will relate those labels.
pub enum JournalEvent {
    JournalAppendCall { record: replay_layer::JournalRecord },
    JournalAppendLinearize { record: replay_layer::JournalRecord },
    JournalAppendReturn { cut: nat },
    JournalDiskFull { record: replay_layer::JournalRecord, cut: nat },
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
    BeginRecover,
    FinishRecover,
}

// Exhaustive closure over the normative global Event ADT.  There is no
// wildcard arm: adding a constructor creates a new proof obligation here.
pub open spec fn journal_decode(
    event: global_layer::GlobalEvent,
) -> Option<JournalEvent> {
    match event {
        global_layer::GlobalEvent::BrokerLinearize { .. } => Option::None,
        global_layer::GlobalEvent::JournalAppendCall { record } => {
            Option::Some(JournalEvent::JournalAppendCall { record })
        },
        global_layer::GlobalEvent::JournalAppendLinearize { record } => {
            Option::Some(JournalEvent::JournalAppendLinearize { record })
        },
        global_layer::GlobalEvent::JournalAppendReturn { cut } => {
            Option::Some(JournalEvent::JournalAppendReturn { cut })
        },
        global_layer::GlobalEvent::JournalDiskFull { record, cut } => {
            Option::Some(JournalEvent::JournalDiskFull { record, cut })
        },
        global_layer::GlobalEvent::WalStage { .. } => Option::None,
        global_layer::GlobalEvent::WalWriteFull { .. } => Option::None,
        global_layer::GlobalEvent::WalWriteTorn { .. } => Option::None,
        global_layer::GlobalEvent::WalFinishTorn { .. } => Option::None,
        global_layer::GlobalEvent::WalFlushAck { .. } => Option::None,
        global_layer::GlobalEvent::WalDiskFull { .. } => Option::None,
        global_layer::GlobalEvent::InvokeEvent {
            request, attempt, call, journal_cut, ack_cut,
        } => Option::Some(JournalEvent::InvokeEvent {
            request, attempt, call, journal_cut, ack_cut,
        }),
        global_layer::GlobalEvent::DeliverEvent {
            request, attempt, observation, journal_cut,
        } => Option::Some(JournalEvent::DeliverEvent {
            request, attempt, observation, journal_cut,
        }),
        global_layer::GlobalEvent::IgnoreStale { request, attempt } => {
            Option::Some(JournalEvent::IgnoreStale { request, attempt })
        },
        global_layer::GlobalEvent::RetryRelease { request } => {
            Option::Some(JournalEvent::RetryRelease { request })
        },
        global_layer::GlobalEvent::Crash => Option::Some(JournalEvent::Crash),
        global_layer::GlobalEvent::BeginScan => Option::None,
        global_layer::GlobalEvent::FinishScan => Option::None,
        global_layer::GlobalEvent::TruncateTail => Option::None,
        global_layer::GlobalEvent::AbortScan => Option::None,
        global_layer::GlobalEvent::BeginRecover => {
            Option::Some(JournalEvent::BeginRecover)
        },
        global_layer::GlobalEvent::FinishRecover => {
            Option::Some(JournalEvent::FinishRecover)
        },
    }
}

pub open spec fn journal_encode(event: JournalEvent)
    -> global_layer::GlobalEvent
{
    match event {
        JournalEvent::JournalAppendCall { record } => {
            global_layer::GlobalEvent::JournalAppendCall { record }
        },
        JournalEvent::JournalAppendLinearize { record } => {
            global_layer::GlobalEvent::JournalAppendLinearize { record }
        },
        JournalEvent::JournalAppendReturn { cut } => {
            global_layer::GlobalEvent::JournalAppendReturn { cut }
        },
        JournalEvent::JournalDiskFull { record, cut } => {
            global_layer::GlobalEvent::JournalDiskFull { record, cut }
        },
        JournalEvent::InvokeEvent {
            request, attempt, call, journal_cut, ack_cut,
        } => global_layer::GlobalEvent::InvokeEvent {
            request, attempt, call, journal_cut, ack_cut,
        },
        JournalEvent::DeliverEvent {
            request, attempt, observation, journal_cut,
        } => global_layer::GlobalEvent::DeliverEvent {
            request, attempt, observation, journal_cut,
        },
        JournalEvent::IgnoreStale { request, attempt } => {
            global_layer::GlobalEvent::IgnoreStale { request, attempt }
        },
        JournalEvent::RetryRelease { request } => {
            global_layer::GlobalEvent::RetryRelease { request }
        },
        JournalEvent::Crash => global_layer::GlobalEvent::Crash,
        JournalEvent::BeginRecover => global_layer::GlobalEvent::BeginRecover,
        JournalEvent::FinishRecover => global_layer::GlobalEvent::FinishRecover,
    }
}

pub open spec fn journal_constructor(
    event: global_layer::GlobalEvent,
) -> bool {
    match event {
        global_layer::GlobalEvent::BrokerLinearize { .. } => false,
        global_layer::GlobalEvent::JournalAppendCall { .. } => true,
        global_layer::GlobalEvent::JournalAppendLinearize { .. } => true,
        global_layer::GlobalEvent::JournalAppendReturn { .. } => true,
        global_layer::GlobalEvent::JournalDiskFull { .. } => true,
        global_layer::GlobalEvent::WalStage { .. } => false,
        global_layer::GlobalEvent::WalWriteFull { .. } => false,
        global_layer::GlobalEvent::WalWriteTorn { .. } => false,
        global_layer::GlobalEvent::WalFinishTorn { .. } => false,
        global_layer::GlobalEvent::WalFlushAck { .. } => false,
        global_layer::GlobalEvent::WalDiskFull { .. } => false,
        global_layer::GlobalEvent::InvokeEvent { .. } => true,
        global_layer::GlobalEvent::DeliverEvent { .. } => true,
        global_layer::GlobalEvent::IgnoreStale { .. } => true,
        global_layer::GlobalEvent::RetryRelease { .. } => true,
        global_layer::GlobalEvent::Crash => true,
        global_layer::GlobalEvent::BeginScan => false,
        global_layer::GlobalEvent::FinishScan => false,
        global_layer::GlobalEvent::TruncateTail => false,
        global_layer::GlobalEvent::AbortScan => false,
        global_layer::GlobalEvent::BeginRecover => true,
        global_layer::GlobalEvent::FinishRecover => true,
    }
}

pub open spec fn journal_decodable(
    event: global_layer::GlobalEvent,
) -> bool {
    match journal_decode(event) {
        Option::Some(_) => true,
        Option::None => false,
    }
}

pub proof fn journal_decode_classifier_exact(
    event: global_layer::GlobalEvent,
)
    ensures journal_decodable(event) <==> journal_constructor(event),
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

pub proof fn journal_decode_encode(event: JournalEvent)
    ensures journal_decode(journal_encode(event)) == Option::Some(event),
{
    match event {
        JournalEvent::JournalAppendCall { .. }
        | JournalEvent::JournalAppendLinearize { .. }
        | JournalEvent::JournalAppendReturn { .. }
        | JournalEvent::JournalDiskFull { .. }
        | JournalEvent::InvokeEvent { .. }
        | JournalEvent::DeliverEvent { .. }
        | JournalEvent::IgnoreStale { .. }
        | JournalEvent::RetryRelease { .. }
        | JournalEvent::Crash
        | JournalEvent::BeginRecover
        | JournalEvent::FinishRecover => {},
    }
}

pub open spec fn initial_configuration(
    cfg: config_layer::FullConfig,
) -> JournalConfiguration {
    JournalConfiguration {
        runtime: ConcreteRuntime {
            store: AtomicJournal { journal: Seq::empty() },
            slot: record_layer::ExecSlot::Idle,
            mode: record_layer::Mode::Online,
            append: append_layer::AppendControl::Idle,
        },
        evidence: GhostEvidence {
            records: Seq::empty(),
            physical: Seq::empty(),
            ack_cuts: Seq::empty(),
            acknowledged_prefix: Seq::empty(),
            slot_source: Option::None,
            commit_source: IMap::new(
                |_request: replay_layer::RequestId| true,
                |_request: replay_layer::RequestId| Option::None,
            ),
        },
    }
}

pub open spec fn journal_view(
    state: JournalConfiguration,
) -> Seq<replay_layer::JournalRecord> {
    state.runtime.store.journal
}

pub open spec fn replay_view(
    cfg: config_layer::FullConfig,
    state: JournalConfiguration,
) -> replay_layer::DurableBroker {
    replay_layer::replay(config_layer::erase_config(cfg), journal_view(state))
}

pub open spec fn runtime_slot_update(
    cfg: config_layer::FullConfig,
    state: JournalConfiguration,
    record: replay_layer::JournalRecord,
) -> Option<record_layer::ExecSlot> {
    record_layer::durable_slot_update(
        config_layer::erase_config(cfg),
        replay_view(cfg, state),
        state.runtime.mode,
        state.runtime.slot,
        record,
    )
}

pub open spec fn runtime_record_enabled(
    cfg: config_layer::FullConfig,
    state: JournalConfiguration,
    record: replay_layer::JournalRecord,
) -> bool {
    replay_layer::structural_enabled(
        config_layer::erase_config(cfg), journal_view(state), record,
    ) && runtime_slot_update(cfg, state, record).is_some()
}

// Executable control reads only immutable configuration and ConcreteRuntime.
// Reading Replay(journal) is allowed; there is no replay result stored in the
// runtime and no branch reads GhostEvidence.
pub open spec fn control_enabled(
    cfg: config_layer::FullConfig,
    state: JournalConfiguration,
    event: JournalEvent,
) -> bool {
    let durable = replay_view(cfg, state);
    let erased = config_layer::erase_config(cfg);
    match event {
        JournalEvent::JournalAppendCall { record } => {
            state.runtime.append is Idle
                && runtime_record_enabled(cfg, state, record)
        },
        JournalEvent::JournalAppendLinearize { record } => {
            match state.runtime.append {
                append_layer::AppendControl::Called { record: called } => {
                    called == record
                        && runtime_record_enabled(cfg, state, record)
                },
                append_layer::AppendControl::Idle
                | append_layer::AppendControl::Linearized { .. } => false,
            }
        },
        JournalEvent::JournalAppendReturn { .. } => {
            state.runtime.mode != record_layer::Mode::Crashed
                && state.runtime.append is Linearized
        },
        JournalEvent::JournalDiskFull { record, .. } => {
            state.runtime.append is Idle
                && runtime_record_enabled(cfg, state, record)
        },
        JournalEvent::InvokeEvent { request, attempt, call, .. } => {
            state.runtime.mode == record_layer::Mode::Online
                && state.runtime.append is Idle
                && state.runtime.slot
                    == (record_layer::ExecSlot::Ready { request, attempt })
                && call == config_layer::canonical_call(cfg, request)
        },
        JournalEvent::DeliverEvent { request, attempt, .. } => {
            state.runtime.mode == record_layer::Mode::Online
                && state.runtime.append is Idle
                && state.runtime.slot
                    == (record_layer::ExecSlot::InFlight { request, attempt })
        },
        JournalEvent::IgnoreStale { request, attempt } => {
            state.runtime.mode == record_layer::Mode::Online
                && state.runtime.append is Idle
                && state.runtime.slot
                    != (record_layer::ExecSlot::InFlight { request, attempt })
        },
        JournalEvent::RetryRelease { request } => {
            state.runtime.mode == record_layer::Mode::Online
                && state.runtime.append is Idle
                && match state.runtime.slot {
                    record_layer::ExecSlot::ObservedFailure {
                        request: observed, ..
                    } => observed == request
                        && !query_layer::d_failure_conclusive(
                            erased, durable, request,
                        )
                        && query_layer::d_started(durable, request)
                            < erased.max_attempts[request],
                    record_layer::ExecSlot::Idle
                    | record_layer::ExecSlot::Ready { .. }
                    | record_layer::ExecSlot::InFlight { .. }
                    | record_layer::ExecSlot::Received { .. }
                    | record_layer::ExecSlot::ObservedSuccess { .. }
                    | record_layer::ExecSlot::ObservedUnknown { .. } => false,
                }
        },
        JournalEvent::Crash => state.runtime.mode != record_layer::Mode::Crashed,
        JournalEvent::BeginRecover => {
            state.runtime.mode == record_layer::Mode::Crashed
                && state.runtime.slot == record_layer::ExecSlot::Idle
                && state.runtime.append is Idle
        },
        JournalEvent::FinishRecover => {
            state.runtime.mode == record_layer::Mode::Recovering
                && state.runtime.slot == record_layer::ExecSlot::Idle
                && state.runtime.append is Idle
                && query_layer::recovery_complete_j(erased, journal_view(state))
        },
    }
}

// Shared formulation used by both atomic and WAL runtimes: the full durable
// history contains the matching Start at an LSN covered by the acknowledged
// cut.  T2-R exports the bridge to membership in the acknowledged prefix.
pub open spec fn start_covered_by_cut(
    records: Seq<replay_layer::JournalRecord>,
    request: replay_layer::RequestId,
    attempt: replay_layer::AttemptId,
    cut: nat,
) -> bool {
    match replay_layer::start_lsn(records, request, attempt) {
        Option::None => false,
        Option::Some(start) => 1 <= start && start <= cut,
    }
}

// Proof/trace evidence is checked separately.  In particular, cuts and source
// indices do not influence executable control.
pub open spec fn evidence_admissible(
    state: JournalConfiguration,
    event: JournalEvent,
) -> bool {
    match event {
        JournalEvent::JournalAppendCall { .. }
        | JournalEvent::JournalAppendLinearize { .. }
        | JournalEvent::IgnoreStale { .. }
        | JournalEvent::RetryRelease { .. }
        | JournalEvent::Crash
        | JournalEvent::BeginRecover
        | JournalEvent::FinishRecover => true,
        JournalEvent::JournalAppendReturn { cut }
        | JournalEvent::JournalDiskFull { cut, .. } => {
            cut == journal_view(state).len()
        },
        JournalEvent::InvokeEvent {
            request, attempt, journal_cut, ack_cut, ..
        } => {
            journal_cut == journal_view(state).len()
                && ack_cut == state.evidence.acknowledged_prefix.len()
                && start_covered_by_cut(
                    state.evidence.records, request, attempt, ack_cut,
                )
        },
        JournalEvent::DeliverEvent { journal_cut, .. } => {
            journal_cut == journal_view(state).len()
        },
    }
}

pub open spec fn admissibly_enabled(
    cfg: config_layer::FullConfig,
    state: JournalConfiguration,
    event: JournalEvent,
) -> bool {
    control_enabled(cfg, state, event)
        && evidence_admissible(state, event)
}

pub open spec fn slot_after_record(
    cfg: config_layer::FullConfig,
    state: JournalConfiguration,
    record: replay_layer::JournalRecord,
) -> record_layer::ExecSlot {
    match runtime_slot_update(cfg, state, record) {
        Option::Some(slot) => slot,
        Option::None => state.runtime.slot,
    }
}

pub open spec fn slot_carries_source(slot: record_layer::ExecSlot) -> bool {
    match slot {
        record_layer::ExecSlot::Received { .. }
        | record_layer::ExecSlot::ObservedSuccess { .. }
        | record_layer::ExecSlot::ObservedFailure { .. }
        | record_layer::ExecSlot::ObservedUnknown { .. } => true,
        record_layer::ExecSlot::Idle
        | record_layer::ExecSlot::Ready { .. }
        | record_layer::ExecSlot::InFlight { .. } => false,
    }
}

pub open spec fn source_after_linearize(
    cfg: config_layer::FullConfig,
    state: JournalConfiguration,
    record: replay_layer::JournalRecord,
) -> Option<p0_layer::PhysicalIndex> {
    if slot_carries_source(slot_after_record(cfg, state, record)) {
        state.evidence.slot_source
    } else {
        Option::None
    }
}

pub open spec fn commit_source_after_linearize(
    state: JournalConfiguration,
    record: replay_layer::JournalRecord,
) -> IMap<replay_layer::RequestId, Option<p0_layer::PhysicalIndex>> {
    match record {
        replay_layer::JournalRecord::CommitRec {
            request, attempt, value, ..
        } => {
            state.evidence.commit_source.insert(
                request,
                p0_layer::delivery_source(
                    state.evidence.physical,
                    request,
                    attempt,
                    replay_layer::Observation::Success(value),
                ),
            )
        },
        replay_layer::JournalRecord::Authorize { .. }
        | replay_layer::JournalRecord::Revoke { .. }
        | replay_layer::JournalRecord::Prepare { .. }
        | replay_layer::JournalRecord::Arm { .. }
        | replay_layer::JournalRecord::Start { .. }
        | replay_layer::JournalRecord::Outcome { .. }
        | replay_layer::JournalRecord::FailRec { .. }
        | replay_layer::JournalRecord::UnknownRec { .. } => {
            state.evidence.commit_source
        },
    }
}

// Direct atomic-runtime transformer.  This definition deliberately does not
// call BrokerStep, p0_layer::apply, or record_layer::apply.
pub open spec fn apply(
    cfg: config_layer::FullConfig,
    state: JournalConfiguration,
    event: JournalEvent,
) -> JournalConfiguration {
    match event {
        JournalEvent::JournalAppendCall { record } => JournalConfiguration {
            runtime: ConcreteRuntime {
                append: append_layer::AppendControl::Called { record },
                ..state.runtime
            },
            ..state
        },
        JournalEvent::JournalAppendLinearize { record } => JournalConfiguration {
            runtime: ConcreteRuntime {
                store: AtomicJournal {
                    journal: journal_view(state).push(record),
                },
                slot: slot_after_record(cfg, state, record),
                append: append_layer::AppendControl::Linearized { record },
                ..state.runtime
            },
            evidence: GhostEvidence {
                records: state.evidence.records.push(record),
                slot_source: source_after_linearize(cfg, state, record),
                commit_source: commit_source_after_linearize(state, record),
                ..state.evidence
            },
        },
        JournalEvent::JournalAppendReturn { cut } => JournalConfiguration {
            runtime: ConcreteRuntime {
                append: append_layer::AppendControl::Idle,
                ..state.runtime
            },
            evidence: GhostEvidence {
                ack_cuts: state.evidence.ack_cuts.push(cut),
                acknowledged_prefix: state.evidence.records,
                ..state.evidence
            },
        },
        JournalEvent::JournalDiskFull { .. }
        | JournalEvent::IgnoreStale { .. } => state,
        JournalEvent::InvokeEvent {
            request, attempt, call, journal_cut, ack_cut,
        } => JournalConfiguration {
            runtime: ConcreteRuntime {
                slot: record_layer::ExecSlot::InFlight { request, attempt },
                ..state.runtime
            },
            evidence: GhostEvidence {
                physical: state.evidence.physical.push(
                    p0_layer::PhysicalEvent::Invoke {
                        request, attempt, call, journal_cut, ack_cut,
                    },
                ),
                slot_source: Option::None,
                ..state.evidence
            },
        },
        JournalEvent::DeliverEvent {
            request, attempt, observation, journal_cut,
        } => JournalConfiguration {
            runtime: ConcreteRuntime {
                slot: record_layer::ExecSlot::Received {
                    request, attempt, observation,
                },
                ..state.runtime
            },
            evidence: GhostEvidence {
                physical: state.evidence.physical.push(
                    p0_layer::PhysicalEvent::Delivered {
                        request, attempt, observation, journal_cut,
                    },
                ),
                slot_source: Option::Some(state.evidence.physical.len()),
                ..state.evidence
            },
        },
        JournalEvent::RetryRelease { .. } => JournalConfiguration {
            runtime: ConcreteRuntime {
                slot: record_layer::ExecSlot::Idle,
                ..state.runtime
            },
            evidence: GhostEvidence {
                slot_source: Option::None,
                ..state.evidence
            },
        },
        JournalEvent::Crash => JournalConfiguration {
            runtime: ConcreteRuntime {
                slot: record_layer::ExecSlot::Idle,
                mode: record_layer::Mode::Crashed,
                append: append_layer::AppendControl::Idle,
                ..state.runtime
            },
            evidence: GhostEvidence {
                slot_source: Option::None,
                ..state.evidence
            },
        },
        JournalEvent::BeginRecover => JournalConfiguration {
            runtime: ConcreteRuntime {
                mode: record_layer::Mode::Recovering,
                ..state.runtime
            },
            ..state
        },
        JournalEvent::FinishRecover => JournalConfiguration {
            runtime: ConcreteRuntime {
                mode: record_layer::Mode::Online,
                ..state.runtime
            },
            ..state
        },
    }
}

pub open spec fn journal_local_step(
    cfg: config_layer::FullConfig,
    before: JournalConfiguration,
    event: JournalEvent,
    after: JournalConfiguration,
) -> bool {
    admissibly_enabled(cfg, before, event)
        && after == apply(cfg, before, event)
}

pub open spec fn journal_runtime_step(
    cfg: config_layer::FullConfig,
    before: JournalConfiguration,
    event: global_layer::GlobalEvent,
    after: JournalConfiguration,
) -> bool {
    match journal_decode(event) {
        Option::None => false,
        Option::Some(local) => journal_local_step(cfg, before, local, after),
    }
}

pub struct JournalExecution {
    pub configs: Seq<JournalConfiguration>,
    pub events: Seq<global_layer::GlobalEvent>,
}

pub open spec fn journal_init(
    cfg: config_layer::FullConfig,
    state: JournalConfiguration,
) -> bool {
    state == initial_configuration(cfg)
}

pub open spec fn exec(
    cfg: config_layer::FullConfig,
    execution: JournalExecution,
) -> bool {
    execution.configs.len() == execution.events.len() + 1
        && journal_init(cfg, execution.configs[0])
        && forall|index: nat| index < execution.events.len() ==>
            #[trigger] journal_runtime_step(
                cfg,
                execution.configs[index as int],
                execution.events[index as int],
                execution.configs[(index + 1) as int],
            )
}

pub open spec fn execs(
    cfg: config_layer::FullConfig,
) -> ISet<JournalExecution> {
    ISet::new(|execution: JournalExecution| exec(cfg, execution))
}

pub open spec fn execution_prefix(
    execution: JournalExecution,
    length: nat,
) -> JournalExecution {
    JournalExecution {
        configs: execution.configs.take((length + 1) as int),
        events: execution.events.take(length as int),
    }
}

pub open spec fn append_view(
    state: JournalConfiguration,
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
    event: JournalEvent,
) -> append_layer::Event<replay_layer::JournalRecord> {
    match event {
        JournalEvent::JournalAppendCall { record } => {
            append_layer::Event::Call { record }
        },
        JournalEvent::JournalAppendLinearize { record } => {
            append_layer::Event::Linearize { record }
        },
        JournalEvent::JournalAppendReturn { cut } => {
            append_layer::Event::ReturnOk { cut }
        },
        JournalEvent::JournalDiskFull { record, cut } => {
            append_layer::Event::DiskFull { record, cut }
        },
        JournalEvent::Crash => append_layer::Event::Crash,
        JournalEvent::IgnoreStale { .. } => {
            append_layer::Event::Stutter { kind: 0 }
        },
        JournalEvent::RetryRelease { .. } => {
            append_layer::Event::Stutter { kind: 1 }
        },
        JournalEvent::BeginRecover => {
            append_layer::Event::Stutter { kind: 2 }
        },
        JournalEvent::FinishRecover => {
            append_layer::Event::Stutter { kind: 3 }
        },
        JournalEvent::InvokeEvent { .. } => {
            append_layer::Event::Stutter { kind: 4 }
        },
        JournalEvent::DeliverEvent { .. } => {
            append_layer::Event::Stutter { kind: 5 }
        },
    }
}

pub open spec fn storage_agreement(state: JournalConfiguration) -> bool {
    state.evidence.records == journal_view(state)
}

pub open spec fn basic_invariant(
    cfg: config_layer::FullConfig,
    state: JournalConfiguration,
) -> bool {
    storage_agreement(state)
        && replay_layer::journal_legal(
            config_layer::erase_config(cfg), journal_view(state),
        )
        && append_layer::b1_invariant(append_view(state))
}

pub proof fn journal_step_decodes(
    cfg: config_layer::FullConfig,
    before: JournalConfiguration,
    event: global_layer::GlobalEvent,
    after: JournalConfiguration,
)
    requires journal_runtime_step(cfg, before, event, after),
    ensures exists|local: JournalEvent| #![auto]
        journal_decode(event) == Option::Some(local)
            && journal_local_step(cfg, before, local, after),
{
    match journal_decode(event) {
        Option::None => {},
        Option::Some(local) => {
            assert(journal_decode(event) == Option::Some(local));
        },
    }
}

pub proof fn journal_step_is_closed(
    cfg: config_layer::FullConfig,
    before: JournalConfiguration,
    event: global_layer::GlobalEvent,
    after: JournalConfiguration,
)
    requires journal_runtime_step(cfg, before, event, after),
    ensures journal_constructor(event),
{
    journal_step_decodes(cfg, before, event, after);
    journal_decode_classifier_exact(event);
}

pub proof fn append_view_initial(cfg: config_layer::FullConfig)
    ensures append_view(initial_configuration(cfg))
        == append_layer::initial_state(),
{
}

pub proof fn append_view_apply(
    cfg: config_layer::FullConfig,
    state: JournalConfiguration,
    event: JournalEvent,
)
    ensures append_view(apply(cfg, state, event))
        == append_layer::apply(append_view(state), append_event(event)),
{
    match event {
        JournalEvent::JournalAppendCall { .. }
        | JournalEvent::JournalAppendLinearize { .. }
        | JournalEvent::JournalAppendReturn { .. }
        | JournalEvent::JournalDiskFull { .. }
        | JournalEvent::InvokeEvent { .. }
        | JournalEvent::DeliverEvent { .. }
        | JournalEvent::IgnoreStale { .. }
        | JournalEvent::RetryRelease { .. }
        | JournalEvent::Crash
        | JournalEvent::BeginRecover
        | JournalEvent::FinishRecover => {},
    }
}

pub proof fn admissible_step_projects_to_append(
    cfg: config_layer::FullConfig,
    state: JournalConfiguration,
    event: JournalEvent,
)
    requires
        storage_agreement(state),
        admissibly_enabled(cfg, state, event),
    ensures append_layer::enabled(append_view(state), append_event(event)),
{
    match event {
        JournalEvent::JournalAppendCall { .. }
        | JournalEvent::JournalAppendLinearize { .. }
        | JournalEvent::JournalAppendReturn { .. }
        | JournalEvent::JournalDiskFull { .. }
        | JournalEvent::InvokeEvent { .. }
        | JournalEvent::DeliverEvent { .. }
        | JournalEvent::IgnoreStale { .. }
        | JournalEvent::RetryRelease { .. }
        | JournalEvent::Crash
        | JournalEvent::BeginRecover
        | JournalEvent::FinishRecover => {},
    }
}

pub proof fn initial_basic_invariant(cfg: config_layer::FullConfig)
    ensures basic_invariant(cfg, initial_configuration(cfg)),
{
    append_layer::initial_invariant::<replay_layer::JournalRecord>();
}

pub proof fn local_step_preserves_basic_invariant(
    cfg: config_layer::FullConfig,
    before: JournalConfiguration,
    event: JournalEvent,
    after: JournalConfiguration,
)
    requires
        basic_invariant(cfg, before),
        journal_local_step(cfg, before, event, after),
    ensures basic_invariant(cfg, after),
{
    assert(after == apply(cfg, before, event));
    append_view_apply(cfg, before, event);
    admissible_step_projects_to_append(cfg, before, event);
    append_layer::step_preserves_invariant(append_view(before), append_event(event));
    match event {
        JournalEvent::JournalAppendLinearize { record } => {
            replay_layer::journal_legal_push(
                config_layer::erase_config(cfg), journal_view(before), record,
            );
        },
        JournalEvent::JournalAppendCall { .. }
        | JournalEvent::JournalAppendReturn { .. }
        | JournalEvent::JournalDiskFull { .. }
        | JournalEvent::InvokeEvent { .. }
        | JournalEvent::DeliverEvent { .. }
        | JournalEvent::IgnoreStale { .. }
        | JournalEvent::RetryRelease { .. }
        | JournalEvent::Crash
        | JournalEvent::BeginRecover
        | JournalEvent::FinishRecover => {},
    }
}

pub proof fn runtime_step_preserves_basic_invariant(
    cfg: config_layer::FullConfig,
    before: JournalConfiguration,
    event: global_layer::GlobalEvent,
    after: JournalConfiguration,
)
    requires
        basic_invariant(cfg, before),
        journal_runtime_step(cfg, before, event, after),
    ensures basic_invariant(cfg, after),
{
    match journal_decode(event) {
        Option::None => {},
        Option::Some(local) => {
            local_step_preserves_basic_invariant(
                cfg, before, local, after,
            );
        },
    }
}

pub proof fn exec_prefix(
    cfg: config_layer::FullConfig,
    execution: JournalExecution,
    length: nat,
)
    requires
        exec(cfg, execution),
        length <= execution.events.len(),
    ensures exec(cfg, execution_prefix(execution, length)),
{
    let prefix = execution_prefix(execution, length);
    assert(prefix.events.len() == length);
    assert(prefix.configs.len() == length + 1);
    assert(prefix.configs[0] == execution.configs[0]);
    assert forall|index: nat| index < prefix.events.len() implies
        #[trigger] journal_runtime_step(
            cfg,
            prefix.configs[index as int],
            prefix.events[index as int],
            prefix.configs[(index + 1) as int],
        ) by {
        assert(index < execution.events.len());
        assert(index + 1 < execution.configs.len());
        assert(prefix.events[index as int] == execution.events[index as int]);
        assert(prefix.configs[index as int] == execution.configs[index as int]);
        assert(prefix.configs[(index + 1) as int]
            == execution.configs[(index + 1) as int]);
    }
}

pub open spec fn journal_trace_closed(
    events: Seq<global_layer::GlobalEvent>,
) -> bool
    decreases events.len()
{
    events.len() == 0 || {
        journal_trace_closed(events.drop_last())
            && journal_constructor(events.last())
    }
}

pub proof fn exec_trace_closed(
    cfg: config_layer::FullConfig,
    execution: JournalExecution,
)
    requires exec(cfg, execution),
    ensures journal_trace_closed(execution.events),
    decreases execution.events.len(),
{
    if execution.events.len() > 0 {
        let length: nat = (execution.events.len() - 1) as nat;
        let prefix = execution_prefix(execution, length);
        exec_prefix(cfg, execution, length);
        exec_trace_closed(cfg, prefix);
        assert(prefix.events =~= execution.events.drop_last());
        assert(length < execution.events.len());
        assert(execution.events[length as int] == execution.events.last());
        journal_step_is_closed(
            cfg,
            execution.configs[length as int],
            execution.events.last(),
            execution.configs[(length + 1) as int],
        );
    }
}

pub proof fn every_exec_configuration_is_basic(
    cfg: config_layer::FullConfig,
    execution: JournalExecution,
)
    requires exec(cfg, execution),
    ensures forall|index: nat| index < execution.configs.len() ==>
        #[trigger] basic_invariant(cfg, execution.configs[index as int]),
    decreases execution.events.len(),
{
    if execution.events.len() == 0 {
        assert(execution.configs.len() == 1);
        assert(execution.configs[0] == initial_configuration(cfg));
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
        assert(last_index < execution.events.len());
        assert(basic_invariant(
            cfg, execution.configs[last_index as int],
        ));
        runtime_step_preserves_basic_invariant(
            cfg,
            execution.configs[last_index as int],
            execution.events[last_index as int],
            execution.configs[(last_index + 1) as int],
        );
        assert forall|index: nat| index < execution.configs.len() implies
            #[trigger] basic_invariant(
                cfg, execution.configs[index as int],
            ) by {
            if index < execution.events.len() {
            } else {
                assert(index == execution.events.len());
                assert(index == last_index + 1);
            }
        }
    }
}

} // verus!
