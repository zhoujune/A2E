use vstd::prelude::*;

verus! {

// B1 is parametric in the record type. It inspects records only for equality,
// so the later T1 composition can instantiate R with the full JournalRecord ADT.

pub enum AppendControl<R> {
    Idle,
    Called { record: R },
    Linearized { record: R },
}

pub enum AppendResult {
    Ok,
    Full,
}

pub enum AppendEvent<R> {
    Call { record: R },
    Linearize { record: R },
    Return { result: AppendResult, cut: nat },
}

pub enum Event<R> {
    Call { record: R },
    Linearize { record: R },
    ReturnOk { cut: nat },
    DiskFull { record: R, cut: nat },
    Crash,
    Stutter { kind: nat },
}

pub struct AppendGhost<R> {
    pub records: Seq<R>,
    pub ack_cuts: Seq<nat>,
    pub acknowledged_prefix: Seq<R>,
}

pub struct State<R> {
    pub append: AppendControl<R>,
    pub evidence: AppendGhost<R>,
}

pub open spec fn initial_state<R>() -> State<R> {
    State {
        append: AppendControl::Idle,
        evidence: AppendGhost {
            records: Seq::empty(),
            ack_cuts: Seq::empty(),
            acknowledged_prefix: Seq::empty(),
        },
    }
}

pub open spec fn last_or_zero(cuts: Seq<nat>) -> nat {
    if cuts.len() == 0 { 0nat } else { cuts.last() }
}

pub open spec fn acknowledged_prefix_for<R>(records: Seq<R>, cuts: Seq<nat>) -> Seq<R> {
    let cut = last_or_zero(cuts);
    if cut <= records.len() {
        records.take(cut as int)
    } else {
        Seq::empty()
    }
}

pub open spec fn cuts_bounded(cuts: Seq<nat>, record_len: nat) -> bool {
    forall|i: int| 0 <= i < cuts.len() ==> #[trigger] cuts[i] <= record_len
}

pub open spec fn cuts_monotone(cuts: Seq<nat>) -> bool {
    forall|i: int, j: int| 0 <= i < j < cuts.len()
        ==> #[trigger] cuts[i] <= #[trigger] cuts[j]
}

pub open spec fn is_prefix<R>(prefix: Seq<R>, whole: Seq<R>) -> bool {
    prefix.len() <= whole.len()
        && prefix == whole.take(prefix.len() as int)
}

pub open spec fn control_record_agreement<R>(state: State<R>) -> bool {
    match state.append {
        AppendControl::Linearized { record } => {
            state.evidence.records.len() > 0 && state.evidence.records.last() == record
        },
        AppendControl::Idle | AppendControl::Called { .. } => true,
    }
}

pub open spec fn b1_invariant<R>(state: State<R>) -> bool {
    cuts_bounded(state.evidence.ack_cuts, state.evidence.records.len())
        && cuts_monotone(state.evidence.ack_cuts)
        && state.evidence.acknowledged_prefix
            == acknowledged_prefix_for(state.evidence.records, state.evidence.ack_cuts)
        && is_prefix(
            state.evidence.acknowledged_prefix,
            state.evidence.records,
        )
        && state.evidence.acknowledged_prefix.len()
            == last_or_zero(state.evidence.ack_cuts)
        && control_record_agreement(state)
}

// The append layer does not define Journal legality. A later composition
// instantiates this predicate with R1's StructuralEnabled relation.
pub open spec fn record_eligible<R>(
    eligibility: spec_fn(Seq<R>, R) -> bool,
    state: State<R>,
    event: Event<R>,
) -> bool {
    match event {
        Event::Call { record }
        | Event::Linearize { record }
        | Event::DiskFull { record, .. } => {
            eligibility(state.evidence.records, record)
        },
        Event::ReturnOk { .. }
        | Event::Crash
        | Event::Stutter { .. } => true,
    }
}

pub open spec fn legal_control_shape<R>(
    eligibility: spec_fn(Seq<R>, R) -> bool,
    state: State<R>,
) -> bool {
    match state.append {
        AppendControl::Idle => true,
        AppendControl::Called { record } => {
            eligibility(state.evidence.records, record)
        },
        AppendControl::Linearized { record } => {
            state.evidence.records.len() > 0
                && state.evidence.records.last() == record
                && eligibility(state.evidence.records.drop_last(), record)
        },
    }
}

pub open spec fn enabled<R>(state: State<R>, event: Event<R>) -> bool {
    match event {
        Event::Call { .. } => state.append is Idle,
        Event::Linearize { record } => match state.append {
            AppendControl::Called { record: called } => called == record,
            AppendControl::Idle | AppendControl::Linearized { .. } => false,
        },
        Event::ReturnOk { cut } => {
            state.append is Linearized && cut == state.evidence.records.len()
        },
        Event::DiskFull { cut, .. } => {
            state.append is Idle && cut == state.evidence.records.len()
        },
        Event::Crash | Event::Stutter { .. } => true,
    }
}

pub open spec fn apply<R>(state: State<R>, event: Event<R>) -> State<R> {
    match event {
        Event::Call { record } => State {
            append: AppendControl::Called { record },
            ..state
        },
        Event::Linearize { record } => State {
            append: AppendControl::Linearized { record },
            evidence: AppendGhost {
                records: state.evidence.records.push(record),
                ..state.evidence
            },
        },
        Event::ReturnOk { cut } => State {
            append: AppendControl::Idle,
            evidence: AppendGhost {
                ack_cuts: state.evidence.ack_cuts.push(cut),
                acknowledged_prefix: state.evidence.records,
                ..state.evidence
            },
        },
        Event::DiskFull { .. } => state,
        Event::Crash => State { append: AppendControl::Idle, ..state },
        Event::Stutter { .. } => state,
    }
}

pub open spec fn append_protocol_step<R>(
    before: State<R>, event: Event<R>, after: State<R>,
) -> bool {
    enabled(before, event) && after == apply(before, event)
}

pub open spec fn pi_append<R>(events: Seq<Event<R>>) -> Seq<AppendEvent<R>>
    decreases events.len()
{
    if events.len() == 0 {
        Seq::empty()
    } else {
        let prefix = events.drop_last();
        match events.last() {
            Event::Call { record } =>
                pi_append(prefix).push(AppendEvent::Call { record }),
            Event::Linearize { record } =>
                pi_append(prefix).push(AppendEvent::Linearize { record }),
            Event::ReturnOk { cut } =>
                pi_append(prefix).push(AppendEvent::Return {
                    result: AppendResult::Ok,
                    cut,
                }),
            Event::DiskFull { record, cut } =>
                pi_append(prefix)
                    .push(AppendEvent::Call { record })
                    .push(AppendEvent::Return {
                        result: AppendResult::Full,
                        cut,
                    }),
            Event::Crash | Event::Stutter { .. } => pi_append(prefix),
        }
    }
}

pub open spec fn pi_journal<R>(events: Seq<Event<R>>) -> Seq<R>
    decreases events.len()
{
    if events.len() == 0 {
        Seq::empty()
    } else {
        let prefix = events.drop_last();
        match events.last() {
            Event::Linearize { record } => pi_journal(prefix).push(record),
            Event::Call { .. }
            | Event::ReturnOk { .. }
            | Event::DiskFull { .. }
            | Event::Crash
            | Event::Stutter { .. } => pi_journal(prefix),
        }
    }
}

pub open spec fn pi_ack<R>(events: Seq<Event<R>>) -> Seq<nat>
    decreases events.len()
{
    if events.len() == 0 {
        Seq::empty()
    } else {
        let prefix = events.drop_last();
        match events.last() {
            Event::ReturnOk { cut } => pi_ack(prefix).push(cut),
            Event::Call { .. }
            | Event::Linearize { .. }
            | Event::DiskFull { .. }
            | Event::Crash
            | Event::Stutter { .. } => pi_ack(prefix),
        }
    }
}

pub open spec fn control_after<R>(control: AppendControl<R>, event: Event<R>)
    -> AppendControl<R>
{
    match event {
        Event::Call { record } => AppendControl::Called { record },
        Event::Linearize { record } => AppendControl::Linearized { record },
        Event::ReturnOk { .. } => AppendControl::Idle,
        Event::DiskFull { .. } => control,
        Event::Crash => AppendControl::Idle,
        Event::Stutter { .. } => control,
    }
}

pub open spec fn append_control_witness<R>(events: Seq<Event<R>>) -> AppendControl<R>
    decreases events.len()
{
    if events.len() == 0 {
        AppendControl::Idle
    } else {
        control_after(append_control_witness(events.drop_last()), events.last())
    }
}

pub open spec fn history_agreement<R>(state: State<R>, events: Seq<Event<R>>) -> bool {
    state.evidence.records == pi_journal(events)
        && state.evidence.ack_cuts == pi_ack(events)
        && state.evidence.acknowledged_prefix
            == acknowledged_prefix_for(pi_journal(events), pi_ack(events))
}

pub open spec fn run<R>(events: Seq<Event<R>>) -> State<R>
    decreases events.len()
{
    if events.len() == 0 {
        initial_state()
    } else {
        apply(run(events.drop_last()), events.last())
    }
}

pub open spec fn executable<R>(events: Seq<Event<R>>) -> bool
    decreases events.len()
{
    events.len() == 0 || {
        let prefix = events.drop_last();
        executable(prefix) && enabled(run(prefix), events.last())
    }
}

pub open spec fn admissibly_executable<R>(
    eligibility: spec_fn(Seq<R>, R) -> bool,
    events: Seq<Event<R>>,
) -> bool
    decreases events.len()
{
    if events.len() == 0 {
        true
    } else {
        let prefix = events.drop_last();
        admissibly_executable(eligibility, prefix)
            && enabled(run(prefix), events.last())
            && record_eligible(eligibility, run(prefix), events.last())
    }
}

pub open spec fn eligible_append_trace<R>(
    eligibility: spec_fn(Seq<R>, R) -> bool,
    events: Seq<Event<R>>,
) -> bool
    decreases events.len()
{
    if events.len() == 0 {
        true
    } else {
        let prefix = events.drop_last();
        eligible_append_trace(eligibility, prefix)
            && match events.last() {
                Event::Call { record }
                | Event::Linearize { record }
                | Event::DiskFull { record, .. } => {
                    eligibility(pi_journal(prefix), record)
                },
                Event::ReturnOk { .. }
                | Event::Crash
                | Event::Stutter { .. } => true,
            }
    }
}

// This raw-label predicate is intentionally Crash-aware. Crash resets the
// control witness to Idle even when a Call or Linearize has not returned.
pub open spec fn append_protocol_prefix<R>(events: Seq<Event<R>>) -> bool
    decreases events.len()
{
    if events.len() == 0 {
        true
    } else {
        let prefix = events.drop_last();
        append_protocol_prefix(prefix)
            && append_protocol_step(run(prefix), events.last(), run(events))
    }
}

pub open spec fn checkpoint<R>(events: Seq<Event<R>>) -> bool {
    let state = run(events);
    b1_invariant(state)
        && history_agreement(state, events)
        && state.append == append_control_witness(events)
}

pub proof fn take_push_stable<R>(records: Seq<R>, record: R, cut: nat)
    requires
        cut <= records.len(),
    ensures
        records.push(record).take(cut as int) == records.take(cut as int),
{
    assert(records.push(record).take(cut as int) =~= records.take(cut as int));
}

pub proof fn take_full<R>(records: Seq<R>)
    ensures
        records.take(records.len() as int) == records,
{
    assert(records.take(records.len() as int) =~= records);
}

pub proof fn prefix_reflexive<R>(records: Seq<R>)
    ensures
        is_prefix(records, records),
{
    take_full(records);
}

pub proof fn last_cut_is_bounded(cuts: Seq<nat>, record_len: nat)
    requires
        cuts_bounded(cuts, record_len),
    ensures
        last_or_zero(cuts) <= record_len,
{
    if cuts.len() > 0 {
        let i = cuts.len() - 1;
        assert(cuts[i as int] <= record_len);
    }
}

pub proof fn acknowledged_prefix_properties<R>(records: Seq<R>, cuts: Seq<nat>)
    requires
        cuts_bounded(cuts, records.len()),
    ensures
        is_prefix(acknowledged_prefix_for(records, cuts), records),
        acknowledged_prefix_for(records, cuts).len() == last_or_zero(cuts),
{
    last_cut_is_bounded(cuts, records.len());
    let cut = last_or_zero(cuts);
    assert(cut <= records.len());
    assert(records.take(cut as int).len() == cut);
    assert(records.take(cut as int).take(cut as int)
        =~= records.take(cut as int));
}

pub proof fn acknowledged_prefix_survives_record_push<R>(
    records: Seq<R>, cuts: Seq<nat>, record: R,
)
    requires
        cuts_bounded(cuts, records.len()),
    ensures
        acknowledged_prefix_for(records.push(record), cuts)
            == acknowledged_prefix_for(records, cuts),
{
    last_cut_is_bounded(cuts, records.len());
    let cut = last_or_zero(cuts);
    take_push_stable(records, record, cut);
}

pub proof fn pi_append_push<R>(events: Seq<Event<R>>, event: Event<R>)
    ensures
        pi_append(events.push(event)) == match event {
            Event::Call { record } =>
                pi_append(events).push(AppendEvent::Call { record }),
            Event::Linearize { record } =>
                pi_append(events).push(AppendEvent::Linearize { record }),
            Event::ReturnOk { cut } =>
                pi_append(events).push(AppendEvent::Return {
                    result: AppendResult::Ok,
                    cut,
                }),
            Event::DiskFull { record, cut } =>
                pi_append(events)
                    .push(AppendEvent::Call { record })
                    .push(AppendEvent::Return {
                        result: AppendResult::Full,
                        cut,
                    }),
            Event::Crash | Event::Stutter { .. } => pi_append(events),
        },
{
    assert(events.push(event).len() > 0);
    assert(events.push(event).drop_last() =~= events);
    assert(events.push(event).last() == event);
}

pub proof fn pi_journal_push<R>(events: Seq<Event<R>>, event: Event<R>)
    ensures
        pi_journal(events.push(event)) == match event {
            Event::Linearize { record } => pi_journal(events).push(record),
            Event::Call { .. }
            | Event::ReturnOk { .. }
            | Event::DiskFull { .. }
            | Event::Crash
            | Event::Stutter { .. } => pi_journal(events),
        },
{
    assert(events.push(event).len() > 0);
    assert(events.push(event).drop_last() =~= events);
    assert(events.push(event).last() == event);
}

pub proof fn pi_ack_push<R>(events: Seq<Event<R>>, event: Event<R>)
    ensures
        pi_ack(events.push(event)) == match event {
            Event::ReturnOk { cut } => pi_ack(events).push(cut),
            Event::Call { .. }
            | Event::Linearize { .. }
            | Event::DiskFull { .. }
            | Event::Crash
            | Event::Stutter { .. } => pi_ack(events),
        },
{
    assert(events.push(event).len() > 0);
    assert(events.push(event).drop_last() =~= events);
    assert(events.push(event).last() == event);
}

pub proof fn append_control_witness_push<R>(events: Seq<Event<R>>, event: Event<R>)
    ensures
        append_control_witness(events.push(event))
            == control_after(append_control_witness(events), event),
{
    assert(events.push(event).len() > 0);
    assert(events.push(event).drop_last() =~= events);
    assert(events.push(event).last() == event);
}

pub proof fn initial_invariant<R>()
    ensures
        b1_invariant(initial_state::<R>()),
        history_agreement(initial_state::<R>(), Seq::<Event<R>>::empty()),
        initial_state::<R>().append
            == append_control_witness(Seq::<Event<R>>::empty()),
{
    let records = Seq::<R>::empty();
    let cuts = Seq::<nat>::empty();
    let events = Seq::<Event<R>>::empty();
    assert(cuts_bounded(cuts, 0nat));
    assert(cuts_monotone(cuts));
    assert(last_or_zero(cuts) == 0nat);
    assert(records.take(0) =~= records);
    assert(acknowledged_prefix_for(records, cuts) == records);
    acknowledged_prefix_properties(records, cuts);
    assert(pi_journal(events) == records);
    assert(pi_ack(events) == cuts);
    assert(append_control_witness(events) is Idle);
}

pub proof fn step_preserves_invariant<R>(state: State<R>, event: Event<R>)
    requires
        b1_invariant(state),
        enabled(state, event),
    ensures
        b1_invariant(apply(state, event)),
{
    match event {
        Event::Call { .. } => {},
        Event::Linearize { record } => {
            acknowledged_prefix_survives_record_push(
                state.evidence.records,
                state.evidence.ack_cuts,
                record,
            );
            assert forall|i: int| 0 <= i < state.evidence.ack_cuts.len()
                implies #[trigger] state.evidence.ack_cuts[i]
                    <= state.evidence.records.push(record).len() by {
                assert(state.evidence.ack_cuts[i] <= state.evidence.records.len());
            }
            assert(state.evidence.records.push(record).last() == record);
        },
        Event::ReturnOk { cut } => {
            assert forall|i: int| 0 <= i < state.evidence.ack_cuts.push(cut).len()
                implies #[trigger] state.evidence.ack_cuts.push(cut)[i]
                    <= state.evidence.records.len() by {
                if i == state.evidence.ack_cuts.len() {
                    assert(state.evidence.ack_cuts.push(cut)[i] == cut);
                } else {
                    assert(state.evidence.ack_cuts.push(cut)[i]
                        == state.evidence.ack_cuts[i]);
                }
            }
            assert forall|i: int, j: int|
                0 <= i < j < state.evidence.ack_cuts.push(cut).len()
                implies #[trigger] state.evidence.ack_cuts.push(cut)[i]
                    <= #[trigger] state.evidence.ack_cuts.push(cut)[j] by {
                if j == state.evidence.ack_cuts.len() {
                    assert(state.evidence.ack_cuts.push(cut)[j] == cut);
                    assert(i < state.evidence.ack_cuts.len());
                    assert(state.evidence.ack_cuts.push(cut)[i]
                        == state.evidence.ack_cuts[i]);
                    assert(state.evidence.ack_cuts[i] <= state.evidence.records.len());
                } else {
                    assert(state.evidence.ack_cuts.push(cut)[i]
                        == state.evidence.ack_cuts[i]);
                    assert(state.evidence.ack_cuts.push(cut)[j]
                        == state.evidence.ack_cuts[j]);
                }
            }
            assert(last_or_zero(state.evidence.ack_cuts.push(cut)) == cut);
            take_full(state.evidence.records);
        },
        Event::DiskFull { .. }
        | Event::Crash
        | Event::Stutter { .. } => {},
    }
    assert(cuts_bounded(
        apply(state, event).evidence.ack_cuts,
        apply(state, event).evidence.records.len(),
    ));
    acknowledged_prefix_properties(
        apply(state, event).evidence.records,
        apply(state, event).evidence.ack_cuts,
    );
}

pub proof fn step_preserves_history<R>(
    state: State<R>, events: Seq<Event<R>>, event: Event<R>,
)
    requires
        history_agreement(state, events),
        b1_invariant(state),
        enabled(state, event),
    ensures
        history_agreement(apply(state, event), events.push(event)),
{
    pi_journal_push(events, event);
    pi_ack_push(events, event);
    step_preserves_invariant(state, event);
    match event {
        Event::Linearize { record } => {
            acknowledged_prefix_survives_record_push(
                state.evidence.records,
                state.evidence.ack_cuts,
                record,
            );
        },
        Event::ReturnOk { .. } => {
            take_full(state.evidence.records);
        },
        Event::Call { .. }
        | Event::DiskFull { .. }
        | Event::Crash
        | Event::Stutter { .. } => {},
    }
}

pub proof fn step_preserves_control_witness<R>(
    state: State<R>, events: Seq<Event<R>>, event: Event<R>,
)
    requires
        state.append == append_control_witness(events),
        enabled(state, event),
    ensures
        apply(state, event).append == append_control_witness(events.push(event)),
{
    append_control_witness_push(events, event);
}

pub proof fn step_preserves_legal_control<R>(
    eligibility: spec_fn(Seq<R>, R) -> bool,
    state: State<R>,
    event: Event<R>,
)
    requires
        legal_control_shape(eligibility, state),
        enabled(state, event),
        record_eligible(eligibility, state, event),
    ensures
        legal_control_shape(eligibility, apply(state, event)),
{
    match event {
        Event::Linearize { record } => {
            assert(state.evidence.records.push(record).drop_last()
                =~= state.evidence.records);
            assert(state.evidence.records.push(record).last() == record);
        },
        Event::DiskFull { .. } => {
            assert(state.append is Idle);
        },
        Event::Call { .. }
        | Event::ReturnOk { .. }
        | Event::Crash
        | Event::Stutter { .. } => {},
    }
}

pub proof fn trace_checkpoint<R>(events: Seq<Event<R>>)
    requires
        executable(events),
    ensures
        checkpoint(events),
    decreases events.len(),
{
    if events.len() == 0 {
        initial_invariant::<R>();
    } else {
        let prefix = events.drop_last();
        let event = events.last();
        trace_checkpoint(prefix);
        step_preserves_invariant(run(prefix), event);
        step_preserves_history(run(prefix), prefix, event);
        step_preserves_control_witness(run(prefix), prefix, event);
    }
}

pub proof fn admissible_trace_checkpoint<R>(
    eligibility: spec_fn(Seq<R>, R) -> bool,
    events: Seq<Event<R>>,
)
    requires
        admissibly_executable(eligibility, events),
    ensures
        checkpoint(events),
        legal_control_shape(eligibility, run(events)),
        eligible_append_trace(eligibility, events),
    decreases events.len(),
{
    if events.len() == 0 {
        initial_invariant::<R>();
    } else {
        let prefix = events.drop_last();
        let event = events.last();
        admissible_trace_checkpoint(eligibility, prefix);
        step_preserves_legal_control(eligibility, run(prefix), event);
        step_preserves_invariant(run(prefix), event);
        step_preserves_history(run(prefix), prefix, event);
        step_preserves_control_witness(run(prefix), prefix, event);
        match event {
            Event::Call { .. }
            | Event::Linearize { .. }
            | Event::DiskFull { .. } => {
                assert(run(prefix).evidence.records == pi_journal(prefix));
            },
            Event::ReturnOk { .. }
            | Event::Crash
            | Event::Stutter { .. } => {},
        }
    }
}

pub proof fn executable_implies_protocol_prefix<R>(events: Seq<Event<R>>)
    requires
        executable(events),
    ensures
        append_protocol_prefix(events),
    decreases events.len(),
{
    if events.len() > 0 {
        let prefix = events.drop_last();
        executable_implies_protocol_prefix(prefix);
        assert(run(events) == apply(run(prefix), events.last()));
    }
}

pub proof fn admissible_implies_executable<R>(
    eligibility: spec_fn(Seq<R>, R) -> bool,
    events: Seq<Event<R>>,
)
    requires
        admissibly_executable(eligibility, events),
    ensures
        executable(events),
    decreases events.len(),
{
    if events.len() > 0 {
        admissible_implies_executable(eligibility, events.drop_last());
    }
}

pub proof fn executable_prefix<R>(events: Seq<Event<R>>, n: int)
    requires
        executable(events),
        0 <= n <= events.len(),
    ensures
        executable(events.take(n)),
    decreases events.len(),
{
    if n == events.len() {
        assert(events.take(n) =~= events);
    } else if events.len() > 0 {
        let prefix = events.drop_last();
        assert(n <= prefix.len());
        executable_prefix(prefix, n);
        assert(prefix.take(n) =~= events.take(n));
    }
}

pub proof fn admissible_executable_prefix<R>(
    eligibility: spec_fn(Seq<R>, R) -> bool,
    events: Seq<Event<R>>,
    n: int,
)
    requires
        admissibly_executable(eligibility, events),
        0 <= n <= events.len(),
    ensures
        admissibly_executable(eligibility, events.take(n)),
    decreases events.len(),
{
    if n == events.len() {
        assert(events.take(n) =~= events);
    } else if events.len() > 0 {
        let prefix = events.drop_last();
        assert(n <= prefix.len());
        admissible_executable_prefix(eligibility, prefix, n);
        assert(prefix.take(n) =~= events.take(n));
    }
}

pub proof fn b1_all_prefixes<R>(events: Seq<Event<R>>)
    requires
        executable(events),
    ensures
        forall|n: int| 0 <= n <= events.len()
            ==> #[trigger] checkpoint(events.take(n)),
{
    assert forall|n: int| 0 <= n <= events.len()
        implies #[trigger] checkpoint(events.take(n)) by {
        executable_prefix(events, n);
        trace_checkpoint(events.take(n));
    }
}

pub proof fn b1_projection_step_exact<R>(events: Seq<Event<R>>, event: Event<R>)
    ensures
        pi_append(events.push(event)) == match event {
            Event::Call { record } =>
                pi_append(events).push(AppendEvent::Call { record }),
            Event::Linearize { record } =>
                pi_append(events).push(AppendEvent::Linearize { record }),
            Event::ReturnOk { cut } =>
                pi_append(events).push(AppendEvent::Return {
                    result: AppendResult::Ok,
                    cut,
                }),
            Event::DiskFull { record, cut } =>
                pi_append(events)
                    .push(AppendEvent::Call { record })
                    .push(AppendEvent::Return {
                        result: AppendResult::Full,
                        cut,
                    }),
            Event::Crash | Event::Stutter { .. } => pi_append(events),
        },
        pi_journal(events.push(event)) == match event {
            Event::Linearize { record } => pi_journal(events).push(record),
            Event::Call { .. }
            | Event::ReturnOk { .. }
            | Event::DiskFull { .. }
            | Event::Crash
            | Event::Stutter { .. } => pi_journal(events),
        },
        pi_ack(events.push(event)) == match event {
            Event::ReturnOk { cut } => pi_ack(events).push(cut),
            Event::Call { .. }
            | Event::Linearize { .. }
            | Event::DiskFull { .. }
            | Event::Crash
            | Event::Stutter { .. } => pi_ack(events),
        },
{
    pi_append_push(events, event);
    pi_journal_push(events, event);
    pi_ack_push(events, event);
}

pub proof fn b1_disk_full_normalization<R>(
    events: Seq<Event<R>>, record: R, cut: nat,
)
    ensures
        pi_append(events.push(Event::DiskFull { record, cut }))
            == pi_append(events)
                .push(AppendEvent::Call { record })
                .push(AppendEvent::Return {
                    result: AppendResult::Full,
                    cut,
                }),
        pi_journal(events.push(Event::DiskFull { record, cut }))
            == pi_journal(events),
        pi_ack(events.push(Event::DiskFull { record, cut })) == pi_ack(events),
{
    b1_projection_step_exact(events, Event::DiskFull { record, cut });
}

pub proof fn b1_append_trace_safety<R>(events: Seq<Event<R>>)
    requires
        executable(events),
    ensures
        append_protocol_prefix(events),
        checkpoint(events),
        forall|n: int| 0 <= n <= events.len()
            ==> #[trigger] checkpoint(events.take(n)),
        forall|n: int| 0 <= n <= events.len()
            ==> #[trigger] append_protocol_prefix(events.take(n)),
{
    trace_checkpoint(events);
    executable_implies_protocol_prefix(events);
    b1_all_prefixes(events);
    assert forall|n: int| 0 <= n <= events.len()
        implies #[trigger] append_protocol_prefix(events.take(n)) by {
        executable_prefix(events, n);
        executable_implies_protocol_prefix(events.take(n));
    }
}

pub proof fn b1_append_trace_safety_with_eligibility<R>(
    eligibility: spec_fn(Seq<R>, R) -> bool,
    events: Seq<Event<R>>,
)
    requires
        admissibly_executable(eligibility, events),
    ensures
        append_protocol_prefix(events),
        checkpoint(events),
        legal_control_shape(eligibility, run(events)),
        eligible_append_trace(eligibility, events),
        forall|n: int| 0 <= n <= events.len()
            ==> #[trigger] checkpoint(events.take(n)),
        forall|n: int| 0 <= n <= events.len()
            ==> #[trigger] legal_control_shape(
                eligibility,
                run(events.take(n)),
            ),
        forall|n: int| 0 <= n <= events.len()
            ==> #[trigger] append_protocol_prefix(events.take(n)),
        forall|n: int| 0 <= n <= events.len()
            ==> #[trigger] eligible_append_trace(
                eligibility,
                events.take(n),
            ),
{
    admissible_trace_checkpoint(eligibility, events);
    admissible_implies_executable(eligibility, events);
    b1_append_trace_safety(events);
    assert forall|n: int| 0 <= n <= events.len()
        implies #[trigger] legal_control_shape(
            eligibility,
            run(events.take(n)),
        ) by {
        admissible_executable_prefix(eligibility, events, n);
        admissible_trace_checkpoint(eligibility, events.take(n));
    }
    assert forall|n: int| 0 <= n <= events.len()
        implies #[trigger] eligible_append_trace(
            eligibility,
            events.take(n),
        ) by {
        admissible_executable_prefix(eligibility, events, n);
        admissible_trace_checkpoint(eligibility, events.take(n));
    }
}

pub proof fn crash_preserves_acknowledgment<R>(state: State<R>)
    ensures
        apply(state, Event::Crash).evidence.ack_cuts == state.evidence.ack_cuts,
        apply(state, Event::Crash).evidence.acknowledged_prefix
            == state.evidence.acknowledged_prefix,
        apply(state, Event::Crash).evidence.records == state.evidence.records,
{
}

pub proof fn step_acknowledged_prefix_monotone<R>(state: State<R>, event: Event<R>)
    requires
        b1_invariant(state),
        enabled(state, event),
    ensures
        is_prefix(
            state.evidence.acknowledged_prefix,
            apply(state, event).evidence.acknowledged_prefix,
        ),
{
    match event {
        Event::ReturnOk { .. } => {
            assert(apply(state, event).evidence.acknowledged_prefix
                == state.evidence.records);
        },
        Event::Call { .. }
        | Event::Linearize { .. }
        | Event::DiskFull { .. }
        | Event::Crash
        | Event::Stutter { .. } => {
            assert(apply(state, event).evidence.acknowledged_prefix
                == state.evidence.acknowledged_prefix);
            prefix_reflexive(state.evidence.acknowledged_prefix);
        },
    }
}

pub proof fn b1_successful_cuts_safe<R>(events: Seq<Event<R>>)
    requires
        executable(events),
    ensures
        cuts_monotone(run(events).evidence.ack_cuts),
        cuts_bounded(run(events).evidence.ack_cuts, run(events).evidence.records.len()),
{
    trace_checkpoint(events);
}

pub proof fn b1_exact_projections<R>(events: Seq<Event<R>>)
    requires
        executable(events),
    ensures
        run(events).evidence.records == pi_journal(events),
        run(events).evidence.ack_cuts == pi_ack(events),
        run(events).evidence.acknowledged_prefix
            == acknowledged_prefix_for(pi_journal(events), pi_ack(events)),
        run(events).append == append_control_witness(events),
{
    trace_checkpoint(events);
}

}
