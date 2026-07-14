use vstd::prelude::*;

#[path = "t1_replay_append.rs"]
pub mod c1_layer;

verus! {

// D1 composes a durable Broker projection with the atomic append interface.
// This is not the contract's full BrokerState or BrokerInvariant: the executor
// is fixed at Idle, StructuralEnabled is not yet strengthened with the
// DurableSlotUpdate caller obligations, and recovery transitions are absent.
// Physical Invoke/Deliver histories and non-Idle executor cases belong to B2.

pub enum Mode {
    Online,
    Crashed,
}

pub enum ExecSlot {
    Idle,
}

pub struct DurableBrokerProjection {
    pub durable: c1_layer::replay_layer::DurableBroker,
    pub slot: ExecSlot,
    pub mode: Mode,
    pub append:
        c1_layer::append_layer::AppendControl<c1_layer::replay_layer::JournalRecord>,
}

pub struct GhostEvidence {
    pub records: Seq<c1_layer::replay_layer::JournalRecord>,
    pub ack_cuts: Seq<nat>,
    pub acknowledged_prefix: Seq<c1_layer::replay_layer::JournalRecord>,
}

pub struct State {
    pub broker: DurableBrokerProjection,
    pub evidence: GhostEvidence,
}

pub enum Event {
    JournalAppendCall {
        record: c1_layer::replay_layer::JournalRecord,
    },
    BrokerLinearize {
        record: c1_layer::replay_layer::JournalRecord,
    },
    JournalAppendReturn {
        cut: nat,
    },
    JournalDiskFull {
        record: c1_layer::replay_layer::JournalRecord,
        cut: nat,
    },
    Crash,
}

pub open spec fn initial_state(
    cfg: c1_layer::replay_layer::Config,
) -> State {
    State {
        broker: DurableBrokerProjection {
            durable: c1_layer::replay_layer::initial_durable(cfg),
            slot: ExecSlot::Idle,
            mode: Mode::Online,
            append: c1_layer::append_layer::AppendControl::Idle,
        },
        evidence: GhostEvidence {
            records: Seq::empty(),
            ack_cuts: Seq::empty(),
            acknowledged_prefix: Seq::empty(),
        },
    }
}

pub open spec fn append_view(
    state: State,
) -> c1_layer::append_layer::State<c1_layer::replay_layer::JournalRecord> {
    c1_layer::append_layer::State {
        append: state.broker.append,
        evidence: c1_layer::append_layer::AppendGhost {
            records: state.evidence.records,
            ack_cuts: state.evidence.ack_cuts,
            acknowledged_prefix: state.evidence.acknowledged_prefix,
        },
    }
}

pub open spec fn append_event(
    event: Event,
) -> c1_layer::append_layer::Event<c1_layer::replay_layer::JournalRecord> {
    match event {
        Event::JournalAppendCall { record } =>
            c1_layer::append_layer::Event::Call { record },
        Event::BrokerLinearize { record } =>
            c1_layer::append_layer::Event::Linearize { record },
        Event::JournalAppendReturn { cut } =>
            c1_layer::append_layer::Event::ReturnOk { cut },
        Event::JournalDiskFull { record, cut } =>
            c1_layer::append_layer::Event::DiskFull { record, cut },
        Event::Crash => c1_layer::append_layer::Event::Crash,
    }
}

pub open spec fn control_enabled(state: State, event: Event) -> bool {
    match event {
        Event::JournalAppendCall { .. } => {
            state.broker.mode == Mode::Online
                && state.broker.append is Idle
        },
        Event::BrokerLinearize { record } => {
            state.broker.mode == Mode::Online
                && match state.broker.append {
                    c1_layer::append_layer::AppendControl::Called {
                        record: called,
                    } => called == record,
                    c1_layer::append_layer::AppendControl::Idle
                    | c1_layer::append_layer::AppendControl::Linearized { .. } => false,
                }
        },
        Event::JournalAppendReturn { .. } => {
            state.broker.mode == Mode::Online
                && state.broker.append is Linearized
        },
        Event::JournalDiskFull { .. } => {
            state.broker.mode == Mode::Online
                && state.broker.append is Idle
        },
        Event::Crash => state.broker.mode == Mode::Online,
    }
}

pub open spec fn evidence_admissible(
    cfg: c1_layer::replay_layer::Config,
    state: State,
    event: Event,
) -> bool {
    let records = state.evidence.records;
    match event {
        Event::JournalAppendCall { record }
        | Event::BrokerLinearize { record } => {
            c1_layer::replay_layer::structural_enabled(cfg, records, record)
        },
        Event::JournalAppendReturn { cut } => cut == records.len(),
        Event::JournalDiskFull { record, cut } => {
            cut == records.len()
                && c1_layer::replay_layer::structural_enabled(cfg, records, record)
        },
        Event::Crash => true,
    }
}

pub open spec fn admissibly_enabled(
    cfg: c1_layer::replay_layer::Config,
    state: State,
    event: Event,
) -> bool {
    control_enabled(state, event) && evidence_admissible(cfg, state, event)
}

pub open spec fn apply(
    state: State,
    event: Event,
) -> State {
    match event {
        Event::JournalAppendCall { record } => State {
            broker: DurableBrokerProjection {
                append: c1_layer::append_layer::AppendControl::Called { record },
                ..state.broker
            },
            ..state
        },
        Event::BrokerLinearize { record } => State {
            broker: DurableBrokerProjection {
                durable: c1_layer::replay_layer::apply_record(
                    state.broker.durable,
                    record,
                ),
                append: c1_layer::append_layer::AppendControl::Linearized { record },
                ..state.broker
            },
            evidence: GhostEvidence {
                records: state.evidence.records.push(record),
                ..state.evidence
            },
        },
        Event::JournalAppendReturn { cut } => State {
            broker: DurableBrokerProjection {
                append: c1_layer::append_layer::AppendControl::Idle,
                ..state.broker
            },
            evidence: GhostEvidence {
                ack_cuts: state.evidence.ack_cuts.push(cut),
                acknowledged_prefix: state.evidence.records,
                ..state.evidence
            },
        },
        Event::JournalDiskFull { .. } => state,
        Event::Crash => State {
            broker: DurableBrokerProjection {
                slot: ExecSlot::Idle,
                mode: Mode::Crashed,
                append: c1_layer::append_layer::AppendControl::Idle,
                ..state.broker
            },
            ..state
        },
    }
}

pub open spec fn durable_append_step(
    cfg: c1_layer::replay_layer::Config,
    before: State,
    event: Event,
    after: State,
) -> bool {
    // This relational checkpoint intentionally conjoins proof-side structural
    // admissibility; it is not the executable Broker guard used by full B2.
    admissibly_enabled(cfg, before, event) && after == apply(before, event)
}

pub open spec fn project(events: Seq<Event>)
    -> Seq<c1_layer::append_layer::Event<c1_layer::replay_layer::JournalRecord>>
    decreases events.len()
{
    if events.len() == 0 {
        Seq::empty()
    } else {
        project(events.drop_last()).push(append_event(events.last()))
    }
}

pub open spec fn run(
    cfg: c1_layer::replay_layer::Config,
    events: Seq<Event>,
) -> State
    decreases events.len()
{
    if events.len() == 0 {
        initial_state(cfg)
    } else {
        apply(run(cfg, events.drop_last()), events.last())
    }
}

pub open spec fn admissibly_executable(
    cfg: c1_layer::replay_layer::Config,
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

pub open spec fn d1_invariant(
    cfg: c1_layer::replay_layer::Config,
    state: State,
) -> bool {
    state.broker.slot == ExecSlot::Idle
        && (state.broker.mode == Mode::Crashed
            ==> state.broker.append is Idle)
        && state.broker.durable
            == c1_layer::replay_layer::replay(cfg, state.evidence.records)
        && c1_layer::replay_layer::journal_legal(cfg, state.evidence.records)
        && c1_layer::replay_layer::r1_replay_invariant(cfg, state.evidence.records)
        && c1_layer::append_layer::b1_invariant(append_view(state))
        && c1_layer::append_layer::legal_control_shape(
            c1_layer::c1_eligibility(cfg),
            append_view(state),
        )
}

pub open spec fn trace_agreement(
    cfg: c1_layer::replay_layer::Config,
    state: State,
    events: Seq<Event>,
) -> bool {
    append_view(state) == c1_layer::append_layer::run(project(events))
        && state.evidence.records
            == c1_layer::append_layer::pi_journal(project(events))
        && state.evidence.ack_cuts
            == c1_layer::append_layer::pi_ack(project(events))
        && state.broker.durable
            == c1_layer::replay_layer::replay(
                cfg,
                c1_layer::append_layer::pi_journal(project(events)),
            )
}

pub open spec fn checkpoint(
    cfg: c1_layer::replay_layer::Config,
    events: Seq<Event>,
) -> bool {
    let state = run(cfg, events);
    d1_invariant(cfg, state)
        && trace_agreement(cfg, state, events)
        && c1_layer::c1_checkpoint(cfg, project(events))
}

pub proof fn project_push(events: Seq<Event>, event: Event)
    ensures
        project(events.push(event)) == project(events).push(append_event(event)),
{
    assert(events.push(event).drop_last() =~= events);
    assert(events.push(event).last() == event);
}

pub proof fn append_view_initial(
    cfg: c1_layer::replay_layer::Config,
)
    ensures
        append_view(initial_state(cfg))
            == c1_layer::append_layer::initial_state(),
{
}

pub proof fn append_view_apply(state: State, event: Event)
    ensures
        append_view(apply(state, event))
            == c1_layer::append_layer::apply(
                append_view(state),
                append_event(event),
            ),
{
    match event {
        Event::JournalAppendCall { .. }
        | Event::BrokerLinearize { .. }
        | Event::JournalAppendReturn { .. }
        | Event::JournalDiskFull { .. }
        | Event::Crash => {},
    }
}

pub proof fn admissible_step_projects(
    cfg: c1_layer::replay_layer::Config,
    state: State,
    event: Event,
)
    requires
        admissibly_enabled(cfg, state, event),
    ensures
        c1_layer::append_layer::enabled(
            append_view(state),
            append_event(event),
        ),
        c1_layer::append_layer::record_eligible(
            c1_layer::c1_eligibility(cfg),
            append_view(state),
            append_event(event),
        ),
{
    match event {
        Event::JournalAppendCall { .. }
        | Event::BrokerLinearize { .. }
        | Event::JournalAppendReturn { .. }
        | Event::JournalDiskFull { .. }
        | Event::Crash => {},
    }
}

pub proof fn initial_invariant(
    cfg: c1_layer::replay_layer::Config,
)
    requires
        c1_layer::replay_layer::config_wf(cfg),
    ensures
        d1_invariant(cfg, initial_state(cfg)),
{
    c1_layer::append_layer::initial_invariant::<
        c1_layer::replay_layer::JournalRecord
    >();
    c1_layer::replay_layer::r1_typed_journal_replay_safety(
        cfg,
        Seq::<c1_layer::replay_layer::JournalRecord>::empty(),
    );
}

pub proof fn step_preserves_invariant(
    cfg: c1_layer::replay_layer::Config,
    state: State,
    event: Event,
)
    requires
        c1_layer::replay_layer::config_wf(cfg),
        d1_invariant(cfg, state),
        admissibly_enabled(cfg, state, event),
    ensures
        d1_invariant(cfg, apply(state, event)),
{
    admissible_step_projects(cfg, state, event);
    c1_layer::append_layer::step_preserves_invariant(
        append_view(state),
        append_event(event),
    );
    c1_layer::append_layer::step_preserves_legal_control(
        c1_layer::c1_eligibility(cfg),
        append_view(state),
        append_event(event),
    );
    append_view_apply(state, event);
    match event {
        Event::BrokerLinearize { record } => {
            c1_layer::replay_layer::r1_legal_extension(
                cfg,
                state.evidence.records,
                record,
            );
            c1_layer::replay_layer::replay_push(
                cfg,
                state.evidence.records,
                record,
            );
        },
        Event::JournalAppendCall { .. }
        | Event::JournalAppendReturn { .. }
        | Event::JournalDiskFull { .. }
        | Event::Crash => {},
    }
}

pub proof fn run_projects(
    cfg: c1_layer::replay_layer::Config,
    events: Seq<Event>,
)
    ensures
        append_view(run(cfg, events))
            == c1_layer::append_layer::run(project(events)),
    decreases events.len(),
{
    if events.len() == 0 {
        append_view_initial(cfg);
    } else {
        let prefix = events.drop_last();
        let event = events.last();
        run_projects(cfg, prefix);
        project_push(prefix, event);
        append_view_apply(run(cfg, prefix), event);
        assert(prefix.push(event) =~= events);
        assert(run(cfg, events) == apply(run(cfg, prefix), event));
        assert(project(events).drop_last() =~= project(prefix));
        assert(project(events).last() == append_event(event));
        assert(c1_layer::append_layer::run(project(events))
            == c1_layer::append_layer::apply(
                c1_layer::append_layer::run(project(prefix)),
                append_event(event),
            ));
    }
}

pub proof fn executable_projects(
    cfg: c1_layer::replay_layer::Config,
    events: Seq<Event>,
)
    requires
        admissibly_executable(cfg, events),
    ensures
        c1_layer::c1_admissibly_executable(cfg, project(events)),
    decreases events.len(),
{
    if events.len() > 0 {
        let prefix = events.drop_last();
        let event = events.last();
        executable_projects(cfg, prefix);
        run_projects(cfg, prefix);
        admissible_step_projects(cfg, run(cfg, prefix), event);
        project_push(prefix, event);
        assert(prefix.push(event) =~= events);
        assert(project(events).len() > 0);
        assert(project(events).drop_last() =~= project(prefix));
        assert(project(events).last() == append_event(event));
        assert(c1_layer::c1_admissibly_executable(cfg, project(events)));
    }
}

pub proof fn trace_checkpoint(
    cfg: c1_layer::replay_layer::Config,
    events: Seq<Event>,
)
    requires
        c1_layer::replay_layer::config_wf(cfg),
        admissibly_executable(cfg, events),
    ensures
        checkpoint(cfg, events),
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
    cfg: c1_layer::replay_layer::Config,
    events: Seq<Event>,
    n: int,
)
    requires
        admissibly_executable(cfg, events),
        0 <= n <= events.len(),
    ensures
        admissibly_executable(cfg, events.take(n)),
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

pub proof fn d1_durable_append_coupling(
    cfg: c1_layer::replay_layer::Config,
    events: Seq<Event>,
)
    requires
        c1_layer::replay_layer::config_wf(cfg),
        admissibly_executable(cfg, events),
    ensures
        checkpoint(cfg, events),
        c1_layer::append_layer::append_protocol_prefix(project(events)),
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

pub proof fn crash_resets_without_fabricating_ack(
    state: State,
)
    ensures
        apply(state, Event::Crash).broker.append
            == c1_layer::append_layer::AppendControl::Idle,
        apply(state, Event::Crash).broker.durable == state.broker.durable,
        apply(state, Event::Crash).evidence.records == state.evidence.records,
        apply(state, Event::Crash).evidence.ack_cuts == state.evidence.ack_cuts,
        apply(state, Event::Crash).evidence.acknowledged_prefix
            == state.evidence.acknowledged_prefix,
{
}

pub proof fn durable_update_is_exactly_linearize(state: State, event: Event)
    ensures
        apply(state, event).broker.durable == match event {
            Event::BrokerLinearize { record } => {
                c1_layer::replay_layer::apply_record(state.broker.durable, record)
            },
            Event::JournalAppendCall { .. }
            | Event::JournalAppendReturn { .. }
            | Event::JournalDiskFull { .. }
            | Event::Crash => state.broker.durable,
        },
{
}

}
