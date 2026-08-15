use vstd::prelude::*;

#[path = "t1_durable_queries.rs"]
pub mod query_layer;

verus! {

use query_layer::c1_layer;
use c1_layer::replay_layer;
use c1_layer::append_layer;

// B2-R is the record-side Broker fragment.  It includes the complete durable
// slot transformer and crash/recovery control, but intentionally has no
// Invoke/Deliver labels or physical/source histories.  Its Event ADT is local
// to this fragment; closure over the paper's global Event ADT is deferred.

#[derive(PartialEq, Eq)]
pub enum Mode {
    Online,
    Crashed,
    Recovering,
}

#[derive(PartialEq, Eq)]
pub enum ExecSlot {
    Idle,
    Ready {
        request: replay_layer::RequestId,
        attempt: replay_layer::AttemptId,
    },
    InFlight {
        request: replay_layer::RequestId,
        attempt: replay_layer::AttemptId,
    },
    Received {
        request: replay_layer::RequestId,
        attempt: replay_layer::AttemptId,
        observation: replay_layer::Observation,
    },
    ObservedSuccess {
        request: replay_layer::RequestId,
        attempt: replay_layer::AttemptId,
        value: replay_layer::Value,
    },
    ObservedFailure {
        request: replay_layer::RequestId,
        attempt: replay_layer::AttemptId,
    },
    ObservedUnknown {
        request: replay_layer::RequestId,
        attempt: replay_layer::AttemptId,
        reason: replay_layer::UnknownReason,
    },
}

pub struct BrokerState {
    pub durable: replay_layer::DurableBroker,
    pub slot: ExecSlot,
    pub mode: Mode,
    pub append: append_layer::AppendControl<replay_layer::JournalRecord>,
}

pub struct GhostEvidence {
    pub records: Seq<replay_layer::JournalRecord>,
    pub ack_cuts: Seq<nat>,
    pub acknowledged_prefix: Seq<replay_layer::JournalRecord>,
}

pub struct State {
    pub broker: BrokerState,
    pub evidence: GhostEvidence,
}

pub enum Event {
    JournalAppendCall { record: replay_layer::JournalRecord },
    BrokerLinearize { record: replay_layer::JournalRecord },
    JournalAppendReturn { cut: nat },
    JournalDiskFull { record: replay_layer::JournalRecord, cut: nat },
    IgnoreStale {
        request: replay_layer::RequestId,
        attempt: replay_layer::AttemptId,
    },
    RetryRelease { request: replay_layer::RequestId },
    Crash,
    BeginRecover,
    FinishRecover,
}

pub open spec fn durable_slot_update(
    cfg: replay_layer::Config,
    durable: replay_layer::DurableBroker,
    mode: Mode,
    slot: ExecSlot,
    record: replay_layer::JournalRecord,
) -> Option<ExecSlot> {
    match record {
        replay_layer::JournalRecord::Authorize { .. }
        | replay_layer::JournalRecord::Revoke { .. }
        | replay_layer::JournalRecord::Prepare { .. }
        | replay_layer::JournalRecord::Arm { .. } => {
            if mode == Mode::Online { Option::Some(slot) } else { Option::None }
        },
        replay_layer::JournalRecord::Start { request, attempt, .. } => {
            if mode == Mode::Online && slot == ExecSlot::Idle {
                Option::Some(ExecSlot::Ready { request, attempt })
            } else {
                Option::None
            }
        },
        replay_layer::JournalRecord::Outcome {
            request, attempt, observation, ..
        } => {
            if mode == Mode::Online
                && slot == (ExecSlot::Received {
                    request,
                    attempt,
                    observation,
                })
            {
                match observation {
                    replay_layer::Observation::Success(value) => {
                        Option::Some(ExecSlot::ObservedSuccess {
                            request, attempt, value,
                        })
                    },
                    replay_layer::Observation::Failure => {
                        Option::Some(ExecSlot::ObservedFailure { request, attempt })
                    },
                    replay_layer::Observation::Ambiguous => {
                        if cfg.request_class[request]
                            == replay_layer::RetryClass::Uncontrolled
                        {
                            Option::Some(ExecSlot::ObservedUnknown {
                                request,
                                attempt,
                                reason: replay_layer::UnknownReason::AmbiguousOutcome,
                            })
                        } else {
                            Option::Some(ExecSlot::Idle)
                        }
                    },
                    replay_layer::Observation::InvalidResult(_) => {
                        if cfg.request_class[request]
                            == replay_layer::RetryClass::Uncontrolled
                        {
                            Option::Some(ExecSlot::ObservedUnknown {
                                request,
                                attempt,
                                reason: replay_layer::UnknownReason::InvalidResultReason,
                            })
                        } else {
                            Option::Some(ExecSlot::Idle)
                        }
                    },
                }
            } else {
                Option::None
            }
        },
        replay_layer::JournalRecord::CommitRec {
            request, attempt, value, ..
        } => {
            if (mode == Mode::Online
                    && slot == (ExecSlot::ObservedSuccess { request, attempt, value }))
                || ((mode == Mode::Online || mode == Mode::Recovering)
                    && slot == ExecSlot::Idle
                    && query_layer::d_outcome(durable, request, attempt)
                        == Option::Some(
                            replay_layer::Observation::Success(value),
                        ))
            {
                Option::Some(ExecSlot::Idle)
            } else {
                Option::None
            }
        },
        replay_layer::JournalRecord::FailRec { request, attempt, .. } => {
            if query_layer::d_failure_conclusive(cfg, durable, request)
                && ((mode == Mode::Online
                        && slot == (ExecSlot::ObservedFailure { request, attempt }))
                    || (mode == Mode::Recovering && slot == ExecSlot::Idle))
            {
                Option::Some(ExecSlot::Idle)
            } else {
                Option::None
            }
        },
        replay_layer::JournalRecord::UnknownRec {
            request, attempt, reason, ..
        } => {
            if mode == Mode::Online {
                match attempt {
                    Option::None => Option::None,
                    Option::Some(a) => {
                        let accepted = match reason {
                            replay_layer::UnknownReason::AmbiguousOutcome => {
                                slot == (ExecSlot::ObservedUnknown {
                                    request,
                                    attempt: a,
                                    reason: replay_layer::UnknownReason::AmbiguousOutcome,
                                })
                            },
                            replay_layer::UnknownReason::InvalidResultReason => {
                                slot == (ExecSlot::ObservedUnknown {
                                    request,
                                    attempt: a,
                                    reason: replay_layer::UnknownReason::InvalidResultReason,
                                })
                            },
                            replay_layer::UnknownReason::NonConclusiveFailure => {
                                slot == (ExecSlot::ObservedFailure { request, attempt: a })
                            },
                            replay_layer::UnknownReason::Exhausted => {
                                slot == ExecSlot::Idle
                                    && query_layer::d_started(durable, request)
                                        == cfg.max_attempts[request]
                                    && query_layer::d_uncertain(durable, request)
                            },
                            replay_layer::UnknownReason::Recovery => false,
                        };
                        if accepted { Option::Some(ExecSlot::Idle) }
                        else { Option::None }
                    },
                }
            } else if mode == Mode::Recovering
                && slot == ExecSlot::Idle
                && reason == replay_layer::UnknownReason::Recovery
                && query_layer::unsafe_uncontrolled_d(cfg, durable, request)
            {
                Option::Some(ExecSlot::Idle)
            } else {
                Option::None
            }
        },
    }
}

pub open spec fn slot_update_or_same(
    cfg: replay_layer::Config,
    broker: BrokerState,
    record: replay_layer::JournalRecord,
) -> ExecSlot {
    match durable_slot_update(cfg, broker.durable, broker.mode, broker.slot, record) {
        Option::Some(slot) => slot,
        Option::None => broker.slot,
    }
}

pub open spec fn abstract_enabled(
    cfg: replay_layer::Config,
    broker: BrokerState,
    record: replay_layer::JournalRecord,
) -> bool {
    query_layer::abstract_record_enabled(cfg, broker.durable, record)
        && durable_slot_update(cfg, broker.durable, broker.mode, broker.slot, record).is_some()
}

pub open spec fn initial_state(cfg: replay_layer::Config) -> State {
    State {
        broker: BrokerState {
            durable: replay_layer::initial_durable(cfg),
            slot: ExecSlot::Idle,
            mode: Mode::Online,
            append: append_layer::AppendControl::Idle,
        },
        evidence: GhostEvidence {
            records: Seq::empty(),
            ack_cuts: Seq::empty(),
            acknowledged_prefix: Seq::empty(),
        },
    }
}

pub open spec fn append_view(state: State)
    -> append_layer::State<replay_layer::JournalRecord>
{
    append_layer::State {
        append: state.broker.append,
        evidence: append_layer::AppendGhost {
            records: state.evidence.records,
            ack_cuts: state.evidence.ack_cuts,
            acknowledged_prefix: state.evidence.acknowledged_prefix,
        },
    }
}

pub open spec fn append_event(event: Event)
    -> append_layer::Event<replay_layer::JournalRecord>
{
    match event {
        Event::JournalAppendCall { record } => append_layer::Event::Call { record },
        Event::BrokerLinearize { record } => append_layer::Event::Linearize { record },
        Event::JournalAppendReturn { cut } => append_layer::Event::ReturnOk { cut },
        Event::JournalDiskFull { record, cut } => {
            append_layer::Event::DiskFull { record, cut }
        },
        Event::IgnoreStale { .. } => append_layer::Event::Stutter { kind: 0 },
        Event::RetryRelease { .. } => append_layer::Event::Stutter { kind: 1 },
        Event::BeginRecover => append_layer::Event::Stutter { kind: 2 },
        Event::FinishRecover => append_layer::Event::Stutter { kind: 3 },
        Event::Crash => append_layer::Event::Crash,
    }
}

// This predicate is the executable/control half: it reads Broker state only.
// Exact references and Journal cuts are deliberately absent.
pub open spec fn control_enabled(
    cfg: replay_layer::Config,
    state: State,
    event: Event,
) -> bool {
    match event {
        Event::JournalAppendCall { record } => {
            state.broker.append is Idle && abstract_enabled(cfg, state.broker, record)
        },
        Event::BrokerLinearize { record } => {
            match state.broker.append {
                append_layer::AppendControl::Called { record: called } => {
                    called == record && abstract_enabled(cfg, state.broker, record)
                },
                append_layer::AppendControl::Idle
                | append_layer::AppendControl::Linearized { .. } => false,
            }
        },
        Event::JournalAppendReturn { .. } => {
            state.broker.mode != Mode::Crashed && state.broker.append is Linearized
        },
        Event::JournalDiskFull { record, .. } => {
            state.broker.append is Idle && abstract_enabled(cfg, state.broker, record)
        },
        Event::IgnoreStale { request, attempt } => {
            state.broker.mode == Mode::Online
                && state.broker.append is Idle
                && state.broker.slot
                    != (ExecSlot::InFlight { request, attempt })
        },
        Event::RetryRelease { request } => {
            state.broker.mode == Mode::Online
                && state.broker.append is Idle
                && match state.broker.slot {
                    ExecSlot::ObservedFailure { request: r, .. } => {
                        r == request
                            && !query_layer::d_failure_conclusive(
                                cfg, state.broker.durable, request,
                            )
                            && query_layer::d_started(state.broker.durable, request)
                                < cfg.max_attempts[request]
                    },
                    ExecSlot::Idle
                    | ExecSlot::Ready { .. }
                    | ExecSlot::InFlight { .. }
                    | ExecSlot::Received { .. }
                    | ExecSlot::ObservedSuccess { .. }
                    | ExecSlot::ObservedUnknown { .. } => false,
                }
        },
        Event::Crash => state.broker.mode != Mode::Crashed,
        Event::BeginRecover => {
            state.broker.mode == Mode::Crashed
                && state.broker.slot == ExecSlot::Idle
                && state.broker.append is Idle
        },
        Event::FinishRecover => {
            state.broker.mode == Mode::Recovering
                && state.broker.slot == ExecSlot::Idle
                && state.broker.append is Idle
                && query_layer::recovery_complete_d(cfg, state.broker.durable)
        },
    }
}

// This predicate is proof/trace admissibility.  It is the only guard that
// inspects GhostEvidence.
pub open spec fn evidence_admissible(
    cfg: replay_layer::Config,
    state: State,
    event: Event,
) -> bool {
    match event {
        Event::JournalAppendCall { record }
        | Event::BrokerLinearize { record } => {
            replay_layer::structural_enabled(cfg, state.evidence.records, record)
        },
        Event::JournalAppendReturn { cut } => cut == state.evidence.records.len(),
        Event::JournalDiskFull { record, cut } => {
            cut == state.evidence.records.len()
                && replay_layer::structural_enabled(
                    cfg, state.evidence.records, record,
                )
        },
        Event::IgnoreStale { .. }
        | Event::RetryRelease { .. }
        | Event::Crash
        | Event::BeginRecover
        | Event::FinishRecover => true,
    }
}

pub open spec fn admissibly_enabled(
    cfg: replay_layer::Config,
    state: State,
    event: Event,
) -> bool {
    control_enabled(cfg, state, event) && evidence_admissible(cfg, state, event)
}

pub open spec fn apply(
    cfg: replay_layer::Config,
    state: State,
    event: Event,
) -> State {
    match event {
        Event::JournalAppendCall { record } => State {
            broker: BrokerState {
                append: append_layer::AppendControl::Called { record },
                ..state.broker
            },
            ..state
        },
        Event::BrokerLinearize { record } => State {
            broker: BrokerState {
                durable: replay_layer::apply_record(state.broker.durable, record),
                slot: slot_update_or_same(cfg, state.broker, record),
                append: append_layer::AppendControl::Linearized { record },
                ..state.broker
            },
            evidence: GhostEvidence {
                records: state.evidence.records.push(record),
                ..state.evidence
            },
        },
        Event::JournalAppendReturn { cut } => State {
            broker: BrokerState {
                append: append_layer::AppendControl::Idle,
                ..state.broker
            },
            evidence: GhostEvidence {
                ack_cuts: state.evidence.ack_cuts.push(cut),
                acknowledged_prefix: state.evidence.records,
                ..state.evidence
            },
        },
        Event::JournalDiskFull { .. } | Event::IgnoreStale { .. } => state,
        Event::RetryRelease { .. } => State {
            broker: BrokerState { slot: ExecSlot::Idle, ..state.broker },
            ..state
        },
        Event::Crash => State {
            broker: BrokerState {
                slot: ExecSlot::Idle,
                mode: Mode::Crashed,
                append: append_layer::AppendControl::Idle,
                ..state.broker
            },
            ..state
        },
        Event::BeginRecover => State {
            broker: BrokerState { mode: Mode::Recovering, ..state.broker },
            ..state
        },
        Event::FinishRecover => State {
            broker: BrokerState { mode: Mode::Online, ..state.broker },
            ..state
        },
    }
}

pub open spec fn broker_record_step(
    cfg: replay_layer::Config,
    before: State,
    event: Event,
    after: State,
) -> bool {
    admissibly_enabled(cfg, before, event) && after == apply(cfg, before, event)
}

pub open spec fn called_shape(
    cfg: replay_layer::Config,
    state: State,
) -> bool {
    match state.broker.append {
        append_layer::AppendControl::Called { record } => {
            replay_layer::structural_enabled(cfg, state.evidence.records, record)
                && abstract_enabled(cfg, state.broker, record)
        },
        append_layer::AppendControl::Idle
        | append_layer::AppendControl::Linearized { .. } => true,
    }
}

pub open spec fn linearized_shape(
    cfg: replay_layer::Config,
    state: State,
) -> bool {
    match state.broker.append {
        append_layer::AppendControl::Linearized { record } => {
            exists|records0: Seq<replay_layer::JournalRecord>, slot0: ExecSlot|
                state.evidence.records == records0.push(record)
                    && replay_layer::structural_enabled(cfg, records0, record)
                    && state.broker.durable
                        == replay_layer::apply_record(
                            replay_layer::replay(cfg, records0), record,
                        )
                    && durable_slot_update(
                        cfg,
                        replay_layer::replay(cfg, records0),
                        state.broker.mode,
                        slot0,
                        record,
                    ) == Option::Some(state.broker.slot)
        },
        append_layer::AppendControl::Idle
        | append_layer::AppendControl::Called { .. } => true,
    }
}

pub open spec fn is_start_record(
    record: replay_layer::JournalRecord,
    request: replay_layer::RequestId,
    attempt: replay_layer::AttemptId,
) -> bool {
    match record {
        replay_layer::JournalRecord::Start {
            request: r, attempt: a, ..
        } => r == request && a == attempt,
        replay_layer::JournalRecord::Authorize { .. }
        | replay_layer::JournalRecord::Revoke { .. }
        | replay_layer::JournalRecord::Prepare { .. }
        | replay_layer::JournalRecord::Arm { .. }
        | replay_layer::JournalRecord::Outcome { .. }
        | replay_layer::JournalRecord::CommitRec { .. }
        | replay_layer::JournalRecord::FailRec { .. }
        | replay_layer::JournalRecord::UnknownRec { .. } => false,
    }
}

pub open spec fn ready_release_agreement(state: State) -> bool {
    match state.broker.slot {
        ExecSlot::Ready { request, attempt } => {
            match replay_layer::start_lsn(
                state.evidence.records, request, attempt,
            ) {
                Option::None => false,
                Option::Some(start) => {
                    1 <= start && start <= state.evidence.records.len()
                        && (start <= state.evidence.acknowledged_prefix.len()
                            || match state.broker.append {
                                append_layer::AppendControl::Linearized { record } => {
                                    is_start_record(record, request, attempt)
                                        && start == state.evidence.records.len()
                                        && state.evidence.records[(start - 1) as int]
                                            == record
                                },
                                append_layer::AppendControl::Idle
                                | append_layer::AppendControl::Called { .. } => false,
                            })
                },
            }
        },
        ExecSlot::Idle
        | ExecSlot::InFlight { .. }
        | ExecSlot::Received { .. }
        | ExecSlot::ObservedSuccess { .. }
        | ExecSlot::ObservedFailure { .. }
        | ExecSlot::ObservedUnknown { .. } => true,
    }
}

pub open spec fn recovery_agreement(
    cfg: replay_layer::Config,
    state: State,
) -> bool {
    query_layer::recovery_complete_d(cfg, state.broker.durable)
        <==> query_layer::recovery_complete_j(cfg, state.evidence.records)
}

pub open spec fn durable_slot_agreement(
    cfg: replay_layer::Config,
    durable: replay_layer::DurableBroker,
    slot: ExecSlot,
) -> bool {
    match slot {
        ExecSlot::Idle => true,
        ExecSlot::Ready { request, attempt }
        | ExecSlot::InFlight { request, attempt }
        | ExecSlot::Received { request, attempt, .. } => {
            durable.phase[request] == replay_layer::Phase::Armed
                && query_layer::d_latest(durable, request) == Option::Some(attempt)
                && query_layer::d_outcome(durable, request, attempt).is_none()
        },
        ExecSlot::ObservedSuccess { request, attempt, value } => {
            durable.phase[request] == replay_layer::Phase::Armed
                && query_layer::d_latest(durable, request) == Option::Some(attempt)
                && query_layer::d_outcome(durable, request, attempt)
                    == Option::Some(replay_layer::Observation::Success(value))
        },
        ExecSlot::ObservedFailure { request, attempt } => {
            durable.phase[request] == replay_layer::Phase::Armed
                && query_layer::d_latest(durable, request) == Option::Some(attempt)
                && query_layer::d_outcome(durable, request, attempt)
                    == Option::Some(replay_layer::Observation::Failure)
        },
        ExecSlot::ObservedUnknown { request, attempt, reason } => {
            durable.phase[request] == replay_layer::Phase::Armed
                && query_layer::d_latest(durable, request) == Option::Some(attempt)
                && cfg.request_class[request]
                    == replay_layer::RetryClass::Uncontrolled
                && match reason {
                    replay_layer::UnknownReason::AmbiguousOutcome => {
                        query_layer::d_outcome(durable, request, attempt)
                            == Option::Some(replay_layer::Observation::Ambiguous)
                    },
                    replay_layer::UnknownReason::InvalidResultReason => {
                        exists|bad: replay_layer::InvalidValue| #![auto]
                            query_layer::d_outcome(durable, request, attempt)
                                == Option::Some(
                                    replay_layer::Observation::InvalidResult(bad),
                                )
                    },
                    replay_layer::UnknownReason::Exhausted
                    | replay_layer::UnknownReason::Recovery
                    | replay_layer::UnknownReason::NonConclusiveFailure => false,
                }
        },
    }
}

pub open spec fn b2_record_invariant(
    cfg: replay_layer::Config,
    state: State,
) -> bool {
    state.broker.durable == replay_layer::replay(cfg, state.evidence.records)
        && replay_layer::journal_legal(cfg, state.evidence.records)
        && replay_layer::r1_replay_invariant(cfg, state.evidence.records)
        && append_layer::b1_invariant(append_view(state))
        && append_layer::legal_control_shape(c1_layer::c1_eligibility(cfg), append_view(state))
        && called_shape(cfg, state)
        && linearized_shape(cfg, state)
        && ready_release_agreement(state)
        && recovery_agreement(cfg, state)
        && durable_slot_agreement(cfg, state.broker.durable, state.broker.slot)
        && (state.broker.mode != Mode::Online ==> state.broker.slot == ExecSlot::Idle)
        && (state.broker.mode == Mode::Crashed ==> state.broker.append is Idle)
}

pub open spec fn project(events: Seq<Event>)
    -> Seq<append_layer::Event<replay_layer::JournalRecord>>
    decreases events.len()
{
    if events.len() == 0 {
        Seq::empty()
    } else {
        project(events.drop_last()).push(append_event(events.last()))
    }
}

pub open spec fn run(cfg: replay_layer::Config, events: Seq<Event>) -> State
    decreases events.len()
{
    if events.len() == 0 {
        initial_state(cfg)
    } else {
        apply(cfg, run(cfg, events.drop_last()), events.last())
    }
}

pub open spec fn admissibly_executable(
    cfg: replay_layer::Config,
    events: Seq<Event>,
) -> bool
    decreases events.len()
{
    events.len() == 0 || {
        let prefix = events.drop_last();
        admissibly_executable(cfg, prefix)
            && admissibly_enabled(cfg, run(cfg, prefix), events.last())
    }
}

pub open spec fn record_trace_agreement(
    cfg: replay_layer::Config,
    state: State,
    events: Seq<Event>,
) -> bool {
    append_view(state) == append_layer::run(project(events))
        && state.evidence.records == append_layer::pi_journal(project(events))
        && state.evidence.ack_cuts == append_layer::pi_ack(project(events))
        && state.evidence.acknowledged_prefix
            == append_layer::acknowledged_prefix_for(
                append_layer::pi_journal(project(events)),
                append_layer::pi_ack(project(events)),
            )
        && state.broker.append
            == append_layer::append_control_witness(project(events))
        && state.broker.durable
            == replay_layer::replay(cfg, append_layer::pi_journal(project(events)))
}

pub open spec fn checkpoint(
    cfg: replay_layer::Config,
    events: Seq<Event>,
) -> bool {
    let state = run(cfg, events);
    b2_record_invariant(cfg, state)
        && record_trace_agreement(cfg, state, events)
        && c1_layer::c1_checkpoint(cfg, project(events))
}

pub proof fn project_push(events: Seq<Event>, event: Event)
    ensures project(events.push(event)) == project(events).push(append_event(event)),
{
    assert(events.push(event).drop_last() =~= events);
    assert(events.push(event).last() == event);
}

pub proof fn append_view_initial(cfg: replay_layer::Config)
    ensures append_view(initial_state(cfg)) == append_layer::initial_state(),
{
}

pub proof fn append_view_apply(
    cfg: replay_layer::Config,
    state: State,
    event: Event,
)
    ensures
        append_view(apply(cfg, state, event))
            == append_layer::apply(append_view(state), append_event(event)),
{
    match event {
        Event::JournalAppendCall { .. }
        | Event::BrokerLinearize { .. }
        | Event::JournalAppendReturn { .. }
        | Event::JournalDiskFull { .. }
        | Event::IgnoreStale { .. }
        | Event::RetryRelease { .. }
        | Event::Crash
        | Event::BeginRecover
        | Event::FinishRecover => {},
    }
}

pub proof fn admissible_projects(
    cfg: replay_layer::Config,
    state: State,
    event: Event,
)
    requires admissibly_enabled(cfg, state, event),
    ensures
        append_layer::enabled(append_view(state), append_event(event)),
        append_layer::record_eligible(
            c1_layer::c1_eligibility(cfg), append_view(state), append_event(event),
        ),
{
    match event {
        Event::JournalAppendCall { .. }
        | Event::BrokerLinearize { .. }
        | Event::JournalAppendReturn { .. }
        | Event::JournalDiskFull { .. }
        | Event::IgnoreStale { .. }
        | Event::RetryRelease { .. }
        | Event::Crash
        | Event::BeginRecover
        | Event::FinishRecover => {},
    }
}

pub proof fn initial_invariant(cfg: replay_layer::Config)
    requires replay_layer::config_wf(cfg),
    ensures b2_record_invariant(cfg, initial_state(cfg)),
{
    append_layer::initial_invariant::<replay_layer::JournalRecord>();
    replay_layer::r1_typed_journal_replay_safety(
        cfg, Seq::<replay_layer::JournalRecord>::empty(),
    );
    query_layer::replay_recovery_predicates_exact(
        cfg, Seq::<replay_layer::JournalRecord>::empty(),
    );
}

pub proof fn step_preserves_replay_half(
    cfg: replay_layer::Config,
    state: State,
    event: Event,
)
    requires
        replay_layer::config_wf(cfg),
        state.broker.durable == replay_layer::replay(cfg, state.evidence.records),
        replay_layer::journal_legal(cfg, state.evidence.records),
        replay_layer::r1_replay_invariant(cfg, state.evidence.records),
        recovery_agreement(cfg, state),
        admissibly_enabled(cfg, state, event),
    ensures
        apply(cfg, state, event).broker.durable
            == replay_layer::replay(
                cfg, apply(cfg, state, event).evidence.records,
            ),
        replay_layer::journal_legal(
            cfg, apply(cfg, state, event).evidence.records,
        ),
        replay_layer::r1_replay_invariant(
            cfg, apply(cfg, state, event).evidence.records,
        ),
        recovery_agreement(cfg, apply(cfg, state, event)),
{
    match event {
        Event::BrokerLinearize { record } => {
            replay_layer::r1_legal_extension(cfg, state.evidence.records, record);
            replay_layer::replay_push(cfg, state.evidence.records, record);
            query_layer::replay_recovery_predicates_exact(
                cfg, state.evidence.records.push(record),
            );
        },
        Event::JournalAppendCall { .. }
        | Event::JournalAppendReturn { .. }
        | Event::JournalDiskFull { .. }
        | Event::IgnoreStale { .. }
        | Event::RetryRelease { .. }
        | Event::Crash
        | Event::BeginRecover
        | Event::FinishRecover => {},
    }
}

pub proof fn step_preserves_mode_shape(
    cfg: replay_layer::Config,
    state: State,
    event: Event,
)
    requires
        (state.broker.mode != Mode::Online ==> state.broker.slot == ExecSlot::Idle),
        (state.broker.mode == Mode::Crashed ==> state.broker.append is Idle),
        admissibly_enabled(cfg, state, event),
    ensures
        (apply(cfg, state, event).broker.mode != Mode::Online
            ==> apply(cfg, state, event).broker.slot == ExecSlot::Idle),
        (apply(cfg, state, event).broker.mode == Mode::Crashed
            ==> apply(cfg, state, event).broker.append is Idle),
{
    match event {
        Event::JournalAppendCall { record }
        | Event::BrokerLinearize { record }
        | Event::JournalDiskFull { record, .. } => {
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
        Event::JournalAppendReturn { .. }
        | Event::IgnoreStale { .. }
        | Event::RetryRelease { .. }
        | Event::Crash
        | Event::BeginRecover
        | Event::FinishRecover => {},
    }
}

pub proof fn step_preserves_called_shape(
    cfg: replay_layer::Config,
    state: State,
    event: Event,
)
    requires
        called_shape(cfg, state),
        admissibly_enabled(cfg, state, event),
    ensures called_shape(cfg, apply(cfg, state, event)),
{
    match event {
        Event::JournalAppendCall { .. }
        | Event::BrokerLinearize { .. }
        | Event::JournalAppendReturn { .. }
        | Event::JournalDiskFull { .. }
        | Event::IgnoreStale { .. }
        | Event::RetryRelease { .. }
        | Event::Crash
        | Event::BeginRecover
        | Event::FinishRecover => {},
    }
}

pub proof fn step_preserves_linearized_shape(
    cfg: replay_layer::Config,
    state: State,
    event: Event,
)
    requires
        state.broker.durable == replay_layer::replay(cfg, state.evidence.records),
        linearized_shape(cfg, state),
        admissibly_enabled(cfg, state, event),
    ensures linearized_shape(cfg, apply(cfg, state, event)),
{
    match event {
        Event::BrokerLinearize { record } => {
            assert(durable_slot_update(
                cfg,
                state.broker.durable,
                state.broker.mode,
                state.broker.slot,
                record,
            ).is_some());
            let next_slot = slot_update_or_same(cfg, state.broker, record);
            assert(durable_slot_update(
                cfg,
                replay_layer::replay(cfg, state.evidence.records),
                state.broker.mode,
                state.broker.slot,
                record,
            ) == Option::Some(next_slot));
            assert(exists|records0: Seq<replay_layer::JournalRecord>, slot0: ExecSlot|
                apply(cfg, state, event).evidence.records == records0.push(record)
                    && replay_layer::structural_enabled(cfg, records0, record)
                    && apply(cfg, state, event).broker.durable
                        == replay_layer::apply_record(
                            replay_layer::replay(cfg, records0), record,
                        )
                    && durable_slot_update(
                        cfg,
                        replay_layer::replay(cfg, records0),
                        apply(cfg, state, event).broker.mode,
                        slot0,
                        record,
                    ) == Option::Some(apply(cfg, state, event).broker.slot)) by {
                let records0 = state.evidence.records;
                let slot0 = state.broker.slot;
                assert(apply(cfg, state, event).evidence.records
                    == records0.push(record));
            }
        },
        Event::JournalAppendCall { .. }
        | Event::JournalAppendReturn { .. }
        | Event::JournalDiskFull { .. }
        | Event::IgnoreStale { .. }
        | Event::RetryRelease { .. }
        | Event::Crash
        | Event::BeginRecover
        | Event::FinishRecover => {},
    }
}

pub proof fn step_preserves_ready_release(
    cfg: replay_layer::Config,
    state: State,
    event: Event,
)
    requires
        ready_release_agreement(state),
        append_layer::b1_invariant(append_view(state)),
        admissibly_enabled(cfg, state, event),
    ensures ready_release_agreement(apply(cfg, state, event)),
{
    match event {
        Event::BrokerLinearize { record } => {
            match record {
                replay_layer::JournalRecord::Start { request, attempt, .. } => {
                    let records1 = state.evidence.records.push(record);
                    assert(records1.drop_last() =~= state.evidence.records);
                    assert(records1.last() == record);
                    assert(records1.len() == state.evidence.records.len() + 1);
                    assert(durable_slot_update(
                        cfg,
                        state.broker.durable,
                        state.broker.mode,
                        state.broker.slot,
                        record,
                    ).is_some());
                    assert(state.broker.mode == Mode::Online);
                    assert(state.broker.slot == ExecSlot::Idle);
                    assert(slot_update_or_same(cfg, state.broker, record)
                        == (ExecSlot::Ready { request, attempt }));
                    assert(replay_layer::start_lsn(records1, request, attempt)
                        == Option::Some(records1.len()));
                    assert(records1[(records1.len() - 1) as int] == record);
                },
                replay_layer::JournalRecord::Authorize { .. }
                | replay_layer::JournalRecord::Revoke { .. }
                | replay_layer::JournalRecord::Prepare { .. }
                | replay_layer::JournalRecord::Arm { .. } => {
                    let records1 = state.evidence.records.push(record);
                    assert(records1.drop_last() =~= state.evidence.records);
                    assert(records1.last() == record);
                    match state.broker.slot {
                        ExecSlot::Ready { request, attempt } => {
                            assert(state.broker.append is Called);
                            match replay_layer::start_lsn(
                                state.evidence.records, request, attempt,
                            ) {
                                Option::Some(start) => {
                                    assert(start
                                        <= state.evidence.acknowledged_prefix.len());
                                    assert(replay_layer::start_lsn(
                                        records1, request, attempt,
                                    ) == Option::Some(start));
                                },
                                Option::None => {},
                            }
                        },
                        ExecSlot::Idle
                        | ExecSlot::InFlight { .. }
                        | ExecSlot::Received { .. }
                        | ExecSlot::ObservedSuccess { .. }
                        | ExecSlot::ObservedFailure { .. }
                        | ExecSlot::ObservedUnknown { .. } => {},
                    }
                },
                replay_layer::JournalRecord::Outcome { .. }
                | replay_layer::JournalRecord::CommitRec { .. }
                | replay_layer::JournalRecord::FailRec { .. }
                | replay_layer::JournalRecord::UnknownRec { .. } => {},
            }
        },
        Event::JournalAppendCall { .. }
        | Event::JournalAppendReturn { .. }
        | Event::JournalDiskFull { .. }
        | Event::IgnoreStale { .. }
        | Event::RetryRelease { .. }
        | Event::Crash
        | Event::BeginRecover
        | Event::FinishRecover => {},
    }
}

pub proof fn start_linearize_preserves_durable_slot_agreement(
    cfg: replay_layer::Config,
    state: State,
    record: replay_layer::JournalRecord,
)
    requires
        record is Start,
        replay_layer::config_wf(cfg),
        state.broker.durable == replay_layer::replay(cfg, state.evidence.records),
        replay_layer::journal_legal(cfg, state.evidence.records),
        replay_layer::r1_replay_invariant(cfg, state.evidence.records),
        durable_slot_agreement(cfg, state.broker.durable, state.broker.slot),
        admissibly_enabled(cfg, state, Event::BrokerLinearize { record }),
    ensures
        durable_slot_agreement(
            cfg,
            apply(cfg, state, Event::BrokerLinearize { record }).broker.durable,
            apply(cfg, state, Event::BrokerLinearize { record }).broker.slot,
        ),
{
    match record {
        replay_layer::JournalRecord::Start { request, attempt, .. } => {
            replay_layer::replay_attempt_shape(cfg, state.evidence.records);
            replay_layer::replay_outcome_shape(cfg, state.evidence.records);
            assert(replay_layer::replay_attempt_shape_ok(
                cfg, state.evidence.records,
            ));
            assert(attempt
                == replay_layer::started_count(state.evidence.records, request) + 1);
            assert(replay_layer::outcome_count(
                state.evidence.records, request, attempt,
            ) == 0) by {
                assert(replay_layer::outcome_count(
                    state.evidence.records, request, attempt,
                ) <= 1);
                assert(replay_layer::outcome_count(
                    state.evidence.records, request, attempt,
                ) == 1 ==> attempt
                    <= replay_layer::started_count(state.evidence.records, request));
            }
            query_layer::outcome_count_zero_implies_no_observation(
                state.evidence.records, request, attempt,
            );
            query_layer::replay_d_outcome_exact(
                cfg, state.evidence.records, request, attempt,
            );
            let entry = replay_layer::AttemptEntry {
                request,
                attempt,
                knowledge: replay_layer::AttemptKnowledge::Started,
            };
            query_layer::attempt_log_started_push(
                state.broker.durable.attempt_log, request, entry,
            );
            query_layer::attempt_log_outcome_push(
                state.broker.durable.attempt_log, request, attempt, entry,
            );
        },
        replay_layer::JournalRecord::Authorize { .. }
        | replay_layer::JournalRecord::Revoke { .. }
        | replay_layer::JournalRecord::Prepare { .. }
        | replay_layer::JournalRecord::Arm { .. }
        | replay_layer::JournalRecord::Outcome { .. }
        | replay_layer::JournalRecord::CommitRec { .. }
        | replay_layer::JournalRecord::FailRec { .. }
        | replay_layer::JournalRecord::UnknownRec { .. } => {},
    }
}

pub proof fn outcome_linearize_preserves_durable_slot_agreement(
    cfg: replay_layer::Config,
    state: State,
    record: replay_layer::JournalRecord,
)
    requires
        record is Outcome,
        state.broker.durable == replay_layer::replay(cfg, state.evidence.records),
        durable_slot_agreement(cfg, state.broker.durable, state.broker.slot),
        admissibly_enabled(cfg, state, Event::BrokerLinearize { record }),
    ensures
        durable_slot_agreement(
            cfg,
            apply(cfg, state, Event::BrokerLinearize { record }).broker.durable,
            apply(cfg, state, Event::BrokerLinearize { record }).broker.slot,
        ),
{
    match record {
        replay_layer::JournalRecord::Outcome {
            request, attempt, observation, ..
        } => {
            assert(state.broker.mode == Mode::Online);
            assert(state.broker.slot == (ExecSlot::Received {
                request, attempt, observation,
            }));
            assert(state.broker.durable.phase[request]
                == replay_layer::Phase::Armed);
            assert(query_layer::d_latest(state.broker.durable, request)
                == Option::Some(attempt));
            assert(query_layer::d_started(state.broker.durable, request)
                == attempt);
            let entry = replay_layer::AttemptEntry {
                request,
                attempt,
                knowledge: replay_layer::AttemptKnowledge::Recorded(observation),
            };
            query_layer::attempt_log_started_push(
                state.broker.durable.attempt_log, request, entry,
            );
            query_layer::attempt_log_outcome_push(
                state.broker.durable.attempt_log, request, attempt, entry,
            );
            let durable1 = replay_layer::apply_record(state.broker.durable, record);
            assert(durable1.phase == state.broker.durable.phase);
            assert(query_layer::d_started(durable1, request)
                == query_layer::d_started(state.broker.durable, request));
            assert(query_layer::d_outcome(durable1, request, attempt)
                == Option::Some(observation));
            assert(durable1.phase[request] == replay_layer::Phase::Armed);
            assert(query_layer::d_latest(durable1, request)
                == Option::Some(attempt));
            match observation {
                replay_layer::Observation::Success(value) => {
                    assert(slot_update_or_same(cfg, state.broker, record)
                        == (ExecSlot::ObservedSuccess {
                            request, attempt, value,
                        }));
                    assert(durable_slot_agreement(
                        cfg,
                        durable1,
                        ExecSlot::ObservedSuccess { request, attempt, value },
                    ));
                },
                replay_layer::Observation::Failure => {
                    assert(slot_update_or_same(cfg, state.broker, record)
                        == (ExecSlot::ObservedFailure { request, attempt }));
                    assert(durable_slot_agreement(
                        cfg,
                        durable1,
                        ExecSlot::ObservedFailure { request, attempt },
                    ));
                },
                replay_layer::Observation::Ambiguous => {
                    if cfg.request_class[request]
                        == replay_layer::RetryClass::Uncontrolled
                    {
                        assert(slot_update_or_same(cfg, state.broker, record)
                            == (ExecSlot::ObservedUnknown {
                                request,
                                attempt,
                                reason: replay_layer::UnknownReason::AmbiguousOutcome,
                            }));
                        assert(durable_slot_agreement(
                            cfg,
                            durable1,
                            ExecSlot::ObservedUnknown {
                                request,
                                attempt,
                                reason: replay_layer::UnknownReason::AmbiguousOutcome,
                            },
                        ));
                    } else {
                        assert(slot_update_or_same(cfg, state.broker, record)
                            == ExecSlot::Idle);
                    }
                },
                replay_layer::Observation::InvalidResult(bad) => {
                    if cfg.request_class[request]
                        == replay_layer::RetryClass::Uncontrolled
                    {
                        assert(slot_update_or_same(cfg, state.broker, record)
                            == (ExecSlot::ObservedUnknown {
                                request,
                                attempt,
                                reason: replay_layer::UnknownReason::InvalidResultReason,
                            }));
                        assert(durable_slot_agreement(
                            cfg,
                            durable1,
                            ExecSlot::ObservedUnknown {
                                request,
                                attempt,
                                reason: replay_layer::UnknownReason::InvalidResultReason,
                            },
                        )) by {
                            assert(exists|witness: replay_layer::InvalidValue| #![auto]
                                query_layer::d_outcome(durable1, request, attempt)
                                    == Option::Some(
                                        replay_layer::Observation::InvalidResult(witness),
                                    )) by {
                                let witness = bad;
                            }
                        }
                    } else {
                        assert(slot_update_or_same(cfg, state.broker, record)
                            == ExecSlot::Idle);
                    }
                },
            }
        },
        replay_layer::JournalRecord::Authorize { .. }
        | replay_layer::JournalRecord::Revoke { .. }
        | replay_layer::JournalRecord::Prepare { .. }
        | replay_layer::JournalRecord::Arm { .. }
        | replay_layer::JournalRecord::Start { .. }
        | replay_layer::JournalRecord::CommitRec { .. }
        | replay_layer::JournalRecord::FailRec { .. }
        | replay_layer::JournalRecord::UnknownRec { .. } => {},
    }
}

pub proof fn admin_linearize_preserves_durable_slot_agreement(
    cfg: replay_layer::Config,
    state: State,
    record: replay_layer::JournalRecord,
)
    requires
        record is Authorize || record is Revoke || record is Prepare || record is Arm,
        durable_slot_agreement(cfg, state.broker.durable, state.broker.slot),
        admissibly_enabled(cfg, state, Event::BrokerLinearize { record }),
    ensures
        durable_slot_agreement(
            cfg,
            apply(cfg, state, Event::BrokerLinearize { record }).broker.durable,
            apply(cfg, state, Event::BrokerLinearize { record }).broker.slot,
        ),
{
    match record {
        replay_layer::JournalRecord::Authorize { request, .. }
        | replay_layer::JournalRecord::Prepare { request, .. }
        | replay_layer::JournalRecord::Arm { request, .. } => {
            match state.broker.slot {
                ExecSlot::Idle => {},
                ExecSlot::Ready { request: active, .. }
                | ExecSlot::InFlight { request: active, .. }
                | ExecSlot::Received { request: active, .. }
                | ExecSlot::ObservedSuccess { request: active, .. }
                | ExecSlot::ObservedFailure { request: active, .. }
                | ExecSlot::ObservedUnknown { request: active, .. } => {
                    assert(active != request);
                },
            }
        },
        replay_layer::JournalRecord::Revoke { .. } => {},
        replay_layer::JournalRecord::Start { .. }
        | replay_layer::JournalRecord::Outcome { .. }
        | replay_layer::JournalRecord::CommitRec { .. }
        | replay_layer::JournalRecord::FailRec { .. }
        | replay_layer::JournalRecord::UnknownRec { .. } => {},
    }
}

pub proof fn terminal_linearize_preserves_durable_slot_agreement(
    cfg: replay_layer::Config,
    state: State,
    record: replay_layer::JournalRecord,
)
    requires
        record is CommitRec || record is FailRec || record is UnknownRec,
        admissibly_enabled(cfg, state, Event::BrokerLinearize { record }),
    ensures
        durable_slot_agreement(
            cfg,
            apply(cfg, state, Event::BrokerLinearize { record }).broker.durable,
            apply(cfg, state, Event::BrokerLinearize { record }).broker.slot,
        ),
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
        | replay_layer::JournalRecord::Outcome { .. } => {},
    }
}

pub proof fn step_preserves_durable_slot_agreement(
    cfg: replay_layer::Config,
    state: State,
    event: Event,
)
    requires
        replay_layer::config_wf(cfg),
        state.broker.durable == replay_layer::replay(cfg, state.evidence.records),
        replay_layer::journal_legal(cfg, state.evidence.records),
        replay_layer::r1_replay_invariant(cfg, state.evidence.records),
        durable_slot_agreement(cfg, state.broker.durable, state.broker.slot),
        admissibly_enabled(cfg, state, event),
    ensures
        durable_slot_agreement(
            cfg,
            apply(cfg, state, event).broker.durable,
            apply(cfg, state, event).broker.slot,
        ),
{
    match event {
        Event::BrokerLinearize { record } => {
            match record {
                replay_layer::JournalRecord::Start { .. } => {
                    start_linearize_preserves_durable_slot_agreement(
                        cfg, state, record,
                    );
                },
                replay_layer::JournalRecord::Outcome { .. } => {
                    outcome_linearize_preserves_durable_slot_agreement(
                        cfg, state, record,
                    );
                },
                replay_layer::JournalRecord::Authorize { .. }
                | replay_layer::JournalRecord::Revoke { .. }
                | replay_layer::JournalRecord::Prepare { .. }
                | replay_layer::JournalRecord::Arm { .. } => {
                    admin_linearize_preserves_durable_slot_agreement(
                        cfg, state, record,
                    );
                },
                replay_layer::JournalRecord::CommitRec { .. }
                | replay_layer::JournalRecord::FailRec { .. }
                | replay_layer::JournalRecord::UnknownRec { .. } => {
                    terminal_linearize_preserves_durable_slot_agreement(
                        cfg, state, record,
                    );
                },
            }
        },
        Event::JournalAppendCall { .. }
        | Event::JournalAppendReturn { .. }
        | Event::JournalDiskFull { .. }
        | Event::IgnoreStale { .. }
        | Event::RetryRelease { .. }
        | Event::Crash
        | Event::BeginRecover
        | Event::FinishRecover => {},
    }
}

pub proof fn step_preserves_invariant(
    cfg: replay_layer::Config,
    state: State,
    event: Event,
)
    requires
        replay_layer::config_wf(cfg),
        b2_record_invariant(cfg, state),
        admissibly_enabled(cfg, state, event),
    ensures b2_record_invariant(cfg, apply(cfg, state, event)),
{
    admissible_projects(cfg, state, event);
    step_preserves_replay_half(cfg, state, event);
    step_preserves_mode_shape(cfg, state, event);
    step_preserves_called_shape(cfg, state, event);
    step_preserves_linearized_shape(cfg, state, event);
    step_preserves_ready_release(cfg, state, event);
    step_preserves_durable_slot_agreement(cfg, state, event);
    append_layer::step_preserves_invariant(append_view(state), append_event(event));
    append_layer::step_preserves_legal_control(
        c1_layer::c1_eligibility(cfg), append_view(state), append_event(event),
    );
    append_view_apply(cfg, state, event);
    match event {
        Event::BrokerLinearize { .. }
        | Event::JournalAppendCall { .. }
        | Event::JournalAppendReturn { .. }
        | Event::JournalDiskFull { .. }
        | Event::IgnoreStale { .. }
        | Event::RetryRelease { .. }
        | Event::Crash
        | Event::BeginRecover
        | Event::FinishRecover => {},
    }
}

pub proof fn run_projects(cfg: replay_layer::Config, events: Seq<Event>)
    ensures append_view(run(cfg, events)) == append_layer::run(project(events)),
    decreases events.len(),
{
    if events.len() == 0 {
        append_view_initial(cfg);
    } else {
        let prefix = events.drop_last();
        let event = events.last();
        run_projects(cfg, prefix);
        project_push(prefix, event);
        append_view_apply(cfg, run(cfg, prefix), event);
        assert(prefix.push(event) =~= events);
        assert(run(cfg, events) == apply(cfg, run(cfg, prefix), event));
        assert(project(events).drop_last() =~= project(prefix));
        assert(project(events).last() == append_event(event));
        assert(append_layer::run(project(events))
            == append_layer::apply(
                append_layer::run(project(prefix)), append_event(event),
            ));
    }
}

pub proof fn executable_projects(cfg: replay_layer::Config, events: Seq<Event>)
    requires admissibly_executable(cfg, events),
    ensures c1_layer::c1_admissibly_executable(cfg, project(events)),
    decreases events.len(),
{
    if events.len() > 0 {
        let prefix = events.drop_last();
        let event = events.last();
        executable_projects(cfg, prefix);
        run_projects(cfg, prefix);
        admissible_projects(cfg, run(cfg, prefix), event);
        project_push(prefix, event);
        assert(prefix.push(event) =~= events);
        assert(project(events).len() > 0);
        assert(project(events).drop_last() =~= project(prefix));
        assert(project(events).last() == append_event(event));
        assert(c1_layer::c1_admissibly_executable(cfg, project(events)));
    }
}

pub proof fn trace_checkpoint(cfg: replay_layer::Config, events: Seq<Event>)
    requires
        replay_layer::config_wf(cfg),
        admissibly_executable(cfg, events),
    ensures checkpoint(cfg, events),
    decreases events.len(),
{
    executable_projects(cfg, events);
    c1_layer::c1_legal_append_replay(cfg, project(events));
    run_projects(cfg, events);
    if events.len() == 0 {
        initial_invariant(cfg);
    } else {
        let prefix = events.drop_last();
        let event = events.last();
        trace_checkpoint(cfg, prefix);
        step_preserves_invariant(cfg, run(cfg, prefix), event);
        assert(prefix.push(event) =~= events);
    }
}

pub proof fn executable_prefix(
    cfg: replay_layer::Config,
    events: Seq<Event>,
    n: int,
)
    requires admissibly_executable(cfg, events), 0 <= n <= events.len(),
    ensures admissibly_executable(cfg, events.take(n)),
    decreases events.len(),
{
    if n == events.len() {
        assert(events.take(n) =~= events);
    } else if events.len() > 0 {
        let prefix = events.drop_last();
        assert(n <= prefix.len());
        executable_prefix(cfg, prefix, n);
        assert(prefix.take(n) =~= events.take(n));
    }
}

pub proof fn b2_record_side_broker_safety(
    cfg: replay_layer::Config,
    events: Seq<Event>,
)
    requires
        replay_layer::config_wf(cfg),
        admissibly_executable(cfg, events),
    ensures
        checkpoint(cfg, events),
        append_layer::append_protocol_prefix(project(events)),
        forall|n: int| 0 <= n <= events.len()
            ==> #[trigger] checkpoint(cfg, events.take(n)),
{
    trace_checkpoint(cfg, events);
    assert(c1_layer::c1_checkpoint(cfg, project(events)));
    assert forall|n: int| 0 <= n <= events.len()
        implies #[trigger] checkpoint(cfg, events.take(n)) by {
        executable_prefix(cfg, events, n);
        trace_checkpoint(cfg, events.take(n));
    }
}

pub proof fn durable_changes_only_at_linearize(
    cfg: replay_layer::Config,
    state: State,
    event: Event,
)
    requires
        apply(cfg, state, event).broker.durable != state.broker.durable,
    ensures event is BrokerLinearize,
{
    match event {
        Event::BrokerLinearize { .. } => {},
        Event::JournalAppendCall { .. }
        | Event::JournalAppendReturn { .. }
        | Event::JournalDiskFull { .. }
        | Event::IgnoreStale { .. }
        | Event::RetryRelease { .. }
        | Event::Crash
        | Event::BeginRecover
        | Event::FinishRecover => {},
    }
}

}
