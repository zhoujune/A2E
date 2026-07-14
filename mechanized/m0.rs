use vstd::prelude::*;

verus! {

pub type RequestId = nat;
pub type CapabilityId = nat;
pub type AttemptId = nat;

#[derive(PartialEq, Eq)]
pub enum Phase {
    New,
    Authorized,
    Prepared,
    Armed,
    Committed,
    Failed,
    Unknown,
}

#[derive(PartialEq, Eq)]
pub enum Mode {
    Online,
    Crashed,
    Recovering,
}

#[derive(PartialEq, Eq)]
pub enum Record {
    Authorize { request: RequestId, capability: CapabilityId },
    Prepare { request: RequestId },
    Arm { request: RequestId },
    Start { request: RequestId, attempt: AttemptId },
    Commit { request: RequestId },
    Fail { request: RequestId },
    Unknown { request: RequestId },
}

#[derive(PartialEq, Eq)]
pub struct Invocation {
    pub request: RequestId,
    pub attempt: AttemptId,
    pub journal_cut: nat,
}

#[derive(PartialEq, Eq)]
pub enum Event {
    JournalAppend { record: Record },
    Invoke { request: RequestId, attempt: AttemptId },
    Crash,
    BeginRecover,
    FinishRecover,
}

pub struct Config {
    pub initial_budget: IMap<CapabilityId, nat>,
    pub request_capability: IMap<RequestId, CapabilityId>,
    pub matches: ISet<(RequestId, CapabilityId)>,
}

pub struct State {
    pub phase: IMap<RequestId, Phase>,
    pub remaining: IMap<CapabilityId, nat>,
    pub journal: Seq<Record>,
    pub invocations: Seq<Invocation>,
    pub commit_history: Seq<RequestId>,
    pub mode: Mode,
}

pub open spec fn config_wf(cfg: Config) -> bool {
    cfg.initial_budget.dom() == ISet::<CapabilityId>::full()
        && cfg.request_capability.dom() == ISet::<RequestId>::full()
}

pub open spec fn initial_state(cfg: Config) -> State {
    State {
        phase: IMap::new(|_r: RequestId| true, |_r: RequestId| Phase::New),
        remaining: cfg.initial_budget,
        journal: Seq::empty(),
        invocations: Seq::empty(),
        commit_history: Seq::empty(),
        mode: Mode::Online,
    }
}

pub open spec fn auth_count(journal: Seq<Record>, capability: CapabilityId) -> nat
    decreases journal.len()
{
    if journal.len() == 0 {
        0nat
    } else {
        let prefix = journal.drop_last();
        let last = journal.last();
        auth_count(prefix, capability)
            + match last {
                Record::Authorize { capability: k, .. } if k == capability => 1nat,
                _ => 0nat,
            }
    }
}

pub open spec fn terminal_count(journal: Seq<Record>, request: RequestId) -> nat
    decreases journal.len()
{
    if journal.len() == 0 {
        0nat
    } else {
        let prefix = journal.drop_last();
        let last = journal.last();
        terminal_count(prefix, request)
            + match last {
                Record::Commit { request: r } if r == request => 1nat,
                Record::Fail { request: r } if r == request => 1nat,
                Record::Unknown { request: r } if r == request => 1nat,
                _ => 0nat,
            }
    }
}

pub open spec fn commit_projection(journal: Seq<Record>) -> Seq<RequestId>
    decreases journal.len()
{
    if journal.len() == 0 {
        Seq::empty()
    } else {
        let prefix = journal.drop_last();
        match journal.last() {
            Record::Commit { request } => commit_projection(prefix).push(request),
            _ => commit_projection(prefix),
        }
    }
}

pub open spec fn has_authorize_before(
    journal: Seq<Record>,
    request: RequestId,
    capability: CapabilityId,
    cut: nat,
) -> bool {
    cut <= journal.len()
        && exists|i: int| 0 <= i < cut
            && journal[i] == Record::Authorize { request, capability }
}

pub open spec fn has_start(
    journal: Seq<Record>, request: RequestId, attempt: AttemptId,
) -> bool {
    exists|i: int| 0 <= i < journal.len()
        && journal[i] == Record::Start { request, attempt }
}

pub open spec fn terminal_phase(phase: Phase) -> bool {
    phase == Phase::Committed || phase == Phase::Failed || phase == Phase::Unknown
}

pub open spec fn authorized_phase(phase: Phase) -> bool {
    phase != Phase::New
}

pub open spec fn budget_conservation(cfg: Config, state: State) -> bool {
    forall|k: CapabilityId| #[trigger] state.remaining[k] + auth_count(state.journal, k)
        == cfg.initial_budget[k]
}

pub open spec fn phase_authorization(cfg: Config, state: State) -> bool {
    forall|r: RequestId| authorized_phase(#[trigger] state.phase[r]) ==> {
        let k = cfg.request_capability[r];
        cfg.matches.contains((r, k))
            && has_authorize_before(state.journal, r, k, state.journal.len())
    }
}

pub open spec fn invocation_authorization(cfg: Config, state: State) -> bool {
    forall|i: int| 0 <= i < state.invocations.len() ==> {
        let invocation = #[trigger] state.invocations[i];
        let k = cfg.request_capability[invocation.request];
        cfg.matches.contains((invocation.request, k))
            && has_authorize_before(
                state.journal,
                invocation.request,
                k,
                invocation.journal_cut,
            )
    }
}

pub open spec fn terminal_unique(state: State) -> bool {
    forall|r: RequestId| #[trigger] terminal_count(state.journal, r) <= 1
}

pub open spec fn phase_terminal_agreement(state: State) -> bool {
    forall|r: RequestId| {
        let count = #[trigger] terminal_count(state.journal, r);
        terminal_phase(state.phase[r]) <==> count == 1
    }
}

pub open spec fn commit_history_agreement(state: State) -> bool {
    state.commit_history == commit_projection(state.journal)
}

pub open spec fn m0_invariant(cfg: Config, state: State) -> bool {
    config_wf(cfg)
        && state.phase.dom() == ISet::<RequestId>::full()
        && state.remaining.dom() == ISet::<CapabilityId>::full()
        && budget_conservation(cfg, state)
        && phase_authorization(cfg, state)
        && invocation_authorization(cfg, state)
        && terminal_unique(state)
        && phase_terminal_agreement(state)
        && commit_history_agreement(state)
}

pub open spec fn append_enabled(cfg: Config, state: State, record: Record) -> bool {
    state.mode == Mode::Online && match record {
        Record::Authorize { request, capability } => {
            state.phase[request] == Phase::New
                && cfg.request_capability[request] == capability
                && cfg.matches.contains((request, capability))
                && state.remaining[capability] > 0
        },
        Record::Prepare { request } => state.phase[request] == Phase::Authorized,
        Record::Arm { request } => state.phase[request] == Phase::Prepared,
        Record::Start { request, attempt } => {
            state.phase[request] == Phase::Armed
                && attempt > 0
                && !has_start(state.journal, request, attempt)
        },
        Record::Commit { request }
        | Record::Fail { request }
        | Record::Unknown { request } => state.phase[request] == Phase::Armed,
    }
}

pub open spec fn enabled(cfg: Config, state: State, event: Event) -> bool {
    match event {
        Event::JournalAppend { record } => append_enabled(cfg, state, record),
        Event::Invoke { request, attempt } => {
            state.mode == Mode::Online
                && state.phase[request] == Phase::Armed
                && has_start(state.journal, request, attempt)
        },
        Event::Crash => state.mode != Mode::Crashed,
        Event::BeginRecover => state.mode == Mode::Crashed,
        Event::FinishRecover => state.mode == Mode::Recovering,
    }
}

pub open spec fn append_record(state: State, record: Record) -> State {
    let journal = state.journal.push(record);
    match record {
        Record::Authorize { request, capability } => State {
            phase: state.phase.insert(request, Phase::Authorized),
            remaining: state.remaining.insert(
                capability,
                sub(state.remaining[capability], 1nat),
            ),
            journal,
            ..state
        },
        Record::Prepare { request } => State {
            phase: state.phase.insert(request, Phase::Prepared),
            journal,
            ..state
        },
        Record::Arm { request } => State {
            phase: state.phase.insert(request, Phase::Armed),
            journal,
            ..state
        },
        Record::Start { .. } => State { journal, ..state },
        Record::Commit { request } => State {
            phase: state.phase.insert(request, Phase::Committed),
            journal,
            commit_history: state.commit_history.push(request),
            ..state
        },
        Record::Fail { request } => State {
            phase: state.phase.insert(request, Phase::Failed),
            journal,
            ..state
        },
        Record::Unknown { request } => State {
            phase: state.phase.insert(request, Phase::Unknown),
            journal,
            ..state
        },
    }
}

pub open spec fn apply(state: State, event: Event) -> State {
    match event {
        Event::JournalAppend { record } => append_record(state, record),
        Event::Invoke { request, attempt } => State {
            invocations: state.invocations.push(Invocation {
                request,
                attempt,
                journal_cut: state.journal.len(),
            }),
            ..state
        },
        Event::Crash => State { mode: Mode::Crashed, ..state },
        Event::BeginRecover => State { mode: Mode::Recovering, ..state },
        Event::FinishRecover => State { mode: Mode::Online, ..state },
    }
}

pub open spec fn executable(cfg: Config, state: State, events: Seq<Event>) -> bool
    decreases events.len()
{
    if events.len() == 0 {
        true
    } else {
        enabled(cfg, state, events.first())
            && executable(cfg, apply(state, events.first()), events.drop_first())
    }
}

pub open spec fn run(state: State, events: Seq<Event>) -> State
    decreases events.len()
{
    if events.len() == 0 {
        state
    } else {
        run(apply(state, events.first()), events.drop_first())
    }
}

pub proof fn auth_count_push(journal: Seq<Record>, capability: CapabilityId, record: Record)
    ensures
        auth_count(journal.push(record), capability)
            == auth_count(journal, capability)
                + match record {
                    Record::Authorize { capability: k, .. } if k == capability => 1nat,
                    _ => 0nat,
                },
{
    assert(journal.push(record).len() > 0);
    assert(journal.push(record).drop_last() =~= journal);
    assert(journal.push(record).last() == record);
}

pub proof fn terminal_count_push(journal: Seq<Record>, request: RequestId, record: Record)
    ensures
        terminal_count(journal.push(record), request)
            == terminal_count(journal, request)
                + match record {
                    Record::Commit { request: r } if r == request => 1nat,
                    Record::Fail { request: r } if r == request => 1nat,
                    Record::Unknown { request: r } if r == request => 1nat,
                    _ => 0nat,
                },
{
    assert(journal.push(record).len() > 0);
    assert(journal.push(record).drop_last() =~= journal);
    assert(journal.push(record).last() == record);
}

pub proof fn commit_projection_push(journal: Seq<Record>, record: Record)
    ensures
        commit_projection(journal.push(record))
            == match record {
                Record::Commit { request } => commit_projection(journal).push(request),
                _ => commit_projection(journal),
            },
{
    assert(journal.push(record).len() > 0);
    assert(journal.push(record).drop_last() =~= journal);
    assert(journal.push(record).last() == record);
}

pub proof fn authorization_survives_append(
    journal: Seq<Record>,
    request: RequestId,
    capability: CapabilityId,
    cut: nat,
    record: Record,
)
    requires
        has_authorize_before(journal, request, capability, cut),
    ensures
        has_authorize_before(journal.push(record), request, capability, cut),
{
    let i = choose|i: int| 0 <= i < cut
        && journal[i] == Record::Authorize { request, capability };
    assert(i < journal.len());
    assert(journal.push(record)[i] == journal[i]);
}

pub proof fn authorization_survives_append_at_end(
    journal: Seq<Record>,
    request: RequestId,
    capability: CapabilityId,
    record: Record,
)
    requires
        has_authorize_before(journal, request, capability, journal.len()),
    ensures
        has_authorize_before(
            journal.push(record),
            request,
            capability,
            journal.push(record).len(),
        ),
{
    let i = choose|i: int| 0 <= i < journal.len()
        && journal[i] == Record::Authorize { request, capability };
    assert(journal.push(record)[i] == journal[i]);
}

pub proof fn appended_authorize_precedes_cut(
    journal: Seq<Record>, request: RequestId, capability: CapabilityId,
)
    ensures
        has_authorize_before(
            journal.push(Record::Authorize { request, capability }),
            request,
            capability,
            journal.push(Record::Authorize { request, capability }).len(),
        ),
{
    let i = journal.len() as int;
    assert(journal.push(Record::Authorize { request, capability })[i]
        == Record::Authorize { request, capability });
}

pub proof fn initial_invariant(cfg: Config)
    requires
        config_wf(cfg),
    ensures
        m0_invariant(cfg, initial_state(cfg)),
{
    let state = initial_state(cfg);
    assert(state.phase.dom() == ISet::<RequestId>::full());
    assert(state.remaining.dom() == ISet::<CapabilityId>::full());
    assert forall|k: CapabilityId|
        #[trigger] state.remaining[k] + auth_count(state.journal, k)
            == cfg.initial_budget[k] by {
        assert(auth_count(Seq::<Record>::empty(), k) == 0nat);
    }
    assert forall|r: RequestId|
        authorized_phase(#[trigger] state.phase[r]) implies {
            let k = cfg.request_capability[r];
            cfg.matches.contains((r, k))
                && has_authorize_before(state.journal, r, k, state.journal.len())
        } by {
        assert(state.phase[r] == Phase::New);
    }
    assert forall|i: int| 0 <= i < state.invocations.len() implies {
        let invocation = #[trigger] state.invocations[i];
        let k = cfg.request_capability[invocation.request];
        cfg.matches.contains((invocation.request, k))
            && has_authorize_before(
                state.journal,
                invocation.request,
                k,
                invocation.journal_cut,
            )
    } by {
    }
    assert forall|r: RequestId| #[trigger] terminal_count(state.journal, r) <= 1 by {
        assert(terminal_count(Seq::<Record>::empty(), r) == 0nat);
    }
    assert forall|r: RequestId| {
        let count = #[trigger] terminal_count(state.journal, r);
        terminal_phase(state.phase[r]) <==> count == 1
    } by {
        assert(state.phase[r] == Phase::New);
        assert(terminal_count(Seq::<Record>::empty(), r) == 0nat);
    }
    assert(commit_projection(Seq::<Record>::empty()) == Seq::<RequestId>::empty());
}

pub proof fn step_preserves_invariant(cfg: Config, state: State, event: Event)
    requires
        m0_invariant(cfg, state),
        enabled(cfg, state, event),
    ensures
        m0_invariant(cfg, apply(state, event)),
{
    match event {
        Event::JournalAppend { record } => {
            auth_count_push(state.journal, 0, record);
            commit_projection_push(state.journal, record);
            match record {
                Record::Authorize { request, capability } => {
                    assert forall|k: CapabilityId|
                        #[trigger] apply(state, event).remaining[k]
                            + auth_count(apply(state, event).journal, k)
                            == cfg.initial_budget[k] by {
                        auth_count_push(state.journal, k, record);
                    }
                    assert forall|r: RequestId|
                        authorized_phase(#[trigger] apply(state, event).phase[r]) implies {
                            let k = cfg.request_capability[r];
                            cfg.matches.contains((r, k))
                                && has_authorize_before(
                                    apply(state, event).journal,
                                    r,
                                    k,
                                    apply(state, event).journal.len(),
                                )
                        } by {
                            if r == request {
                            appended_authorize_precedes_cut(
                                state.journal, request, capability,
                            );
                        } else {
                            assert(apply(state, event).phase[r] == state.phase[r]);
                            let k = cfg.request_capability[r];
                            assert(cfg.matches.contains((r, k)));
                            assert(has_authorize_before(
                                state.journal, r, k, state.journal.len(),
                            ));
                            authorization_survives_append_at_end(
                                state.journal, r, k, record,
                            );
                        }
                    }
                },
                Record::Prepare { .. } | Record::Arm { .. } | Record::Start { .. } => {},
                Record::Commit { request }
                | Record::Fail { request }
                | Record::Unknown { request } => {
                    terminal_count_push(state.journal, request, record);
                },
            }
            assert(apply(state, event).phase.dom() == ISet::<RequestId>::full());
            assert(apply(state, event).remaining.dom()
                == ISet::<CapabilityId>::full());
            assert forall|k: CapabilityId|
                #[trigger] apply(state, event).remaining[k]
                    + auth_count(apply(state, event).journal, k)
                    == cfg.initial_budget[k] by {
                auth_count_push(state.journal, k, record);
                match record {
                    Record::Authorize { capability, .. } => {
                        if k == capability {
                            assert(state.remaining[k] > 0);
                        }
                    },
                    _ => {},
                }
            }
            assert forall|r: RequestId|
                authorized_phase(#[trigger] apply(state, event).phase[r]) implies {
                    let k = cfg.request_capability[r];
                    cfg.matches.contains((r, k))
                        && has_authorize_before(
                            apply(state, event).journal,
                            r,
                            k,
                            apply(state, event).journal.len(),
                        )
                } by {
                match record {
                    Record::Authorize { request, capability } => {
                        if r == request {
                            appended_authorize_precedes_cut(
                                state.journal, request, capability,
                            );
                        } else {
                            assert(apply(state, event).phase[r] == state.phase[r]);
                            assert(authorized_phase(state.phase[r]));
                            let k = cfg.request_capability[r];
                            authorization_survives_append_at_end(
                                state.journal, r, k, record,
                            );
                        }
                    },
                    Record::Prepare { request }
                    | Record::Arm { request }
                    | Record::Commit { request }
                    | Record::Fail { request }
                    | Record::Unknown { request } => {
                        if r == request {
                            assert(authorized_phase(state.phase[r]));
                        } else {
                            assert(apply(state, event).phase[r] == state.phase[r]);
                            assert(authorized_phase(state.phase[r]));
                        }
                        let k = cfg.request_capability[r];
                        authorization_survives_append_at_end(
                            state.journal, r, k, record,
                        );
                    },
                    Record::Start { .. } => {
                        assert(apply(state, event).phase[r] == state.phase[r]);
                        assert(authorized_phase(state.phase[r]));
                        let k = cfg.request_capability[r];
                        authorization_survives_append_at_end(
                            state.journal, r, k, record,
                        );
                    },
                }
            }
            assert forall|i: int|
                0 <= i < apply(state, event).invocations.len() implies {
                    let invocation = #[trigger] apply(state, event).invocations[i];
                    let k = cfg.request_capability[invocation.request];
                    cfg.matches.contains((invocation.request, k))
                        && has_authorize_before(
                            apply(state, event).journal,
                            invocation.request,
                            k,
                            invocation.journal_cut,
                        )
                } by {
                assert(apply(state, event).invocations[i] == state.invocations[i]);
                let invocation = state.invocations[i];
                let k = cfg.request_capability[invocation.request];
                authorization_survives_append(
                    state.journal,
                    invocation.request,
                    k,
                    invocation.journal_cut,
                    record,
                );
            }
            assert forall|r: RequestId|
                #[trigger] terminal_count(apply(state, event).journal, r) <= 1 by {
                terminal_count_push(state.journal, r, record);
            }
            assert forall|r: RequestId| {
                let count = #[trigger] terminal_count(apply(state, event).journal, r);
                terminal_phase(apply(state, event).phase[r]) <==> count == 1
            } by {
                terminal_count_push(state.journal, r, record);
            }
            assert(apply(state, event).commit_history
                == commit_projection(apply(state, event).journal));
        },
        Event::Invoke { request, attempt } => {
            let i = state.invocations.len() as int;
            let k = cfg.request_capability[request];
            assert(has_authorize_before(state.journal, request, k, state.journal.len()));
            assert(apply(state, event).invocations[i] == Invocation {
                request,
                attempt,
                journal_cut: state.journal.len(),
            });
            assert forall|j: int| 0 <= j < apply(state, event).invocations.len() implies {
                let invocation = #[trigger] apply(state, event).invocations[j];
                let cap = cfg.request_capability[invocation.request];
                cfg.matches.contains((invocation.request, cap))
                    && has_authorize_before(
                        apply(state, event).journal,
                        invocation.request,
                        cap,
                        invocation.journal_cut,
                    )
            } by {
                if j == i {
                } else {
                    assert(j < state.invocations.len());
                    assert(state.invocations[j] == apply(state, event).invocations[j]);
                }
            }
        },
        Event::Crash | Event::BeginRecover | Event::FinishRecover => {},
    }
}

pub proof fn trace_preserves_invariant(
    cfg: Config, state: State, events: Seq<Event>,
)
    requires
        m0_invariant(cfg, state),
        executable(cfg, state, events),
    ensures
        m0_invariant(cfg, run(state, events)),
    decreases events.len(),
{
    if events.len() > 0 {
        let event = events.first();
        let next = apply(state, event);
        step_preserves_invariant(cfg, state, event);
        trace_preserves_invariant(cfg, next, events.drop_first());
    }
}

pub open spec fn administrative(event: Event) -> bool {
    event == Event::Crash
        || event == Event::BeginRecover
        || event == Event::FinishRecover
}

pub open spec fn all_administrative(events: Seq<Event>) -> bool
    decreases events.len()
{
    if events.len() == 0 {
        true
    } else {
        administrative(events.first()) && all_administrative(events.drop_first())
    }
}

pub proof fn administrative_commit_history_stutters(state: State, event: Event)
    requires
        administrative(event),
    ensures
        apply(state, event).commit_history == state.commit_history,
{
}

pub proof fn administrative_trace_stutters(state: State, events: Seq<Event>)
    requires
        all_administrative(events),
    ensures
        run(state, events).commit_history == state.commit_history,
    decreases events.len(),
{
    if events.len() > 0 {
        let event = events.first();
        let next = apply(state, event);
        administrative_commit_history_stutters(state, event);
        administrative_trace_stutters(next, events.drop_first());
    }
}

pub proof fn m0_safety(cfg: Config, events: Seq<Event>)
    requires
        config_wf(cfg),
        executable(cfg, initial_state(cfg), events),
    ensures
        m0_invariant(cfg, run(initial_state(cfg), events)),
{
    initial_invariant(cfg);
    trace_preserves_invariant(cfg, initial_state(cfg), events);
}

pub proof fn m0_authorization_before_invoke(cfg: Config, events: Seq<Event>)
    requires
        config_wf(cfg),
        executable(cfg, initial_state(cfg), events),
    ensures
        invocation_authorization(cfg, run(initial_state(cfg), events)),
{
    m0_safety(cfg, events);
}

pub proof fn m0_per_capability_budget_conservation(cfg: Config, events: Seq<Event>)
    requires
        config_wf(cfg),
        executable(cfg, initial_state(cfg), events),
    ensures
        budget_conservation(cfg, run(initial_state(cfg), events)),
{
    m0_safety(cfg, events);
}

pub proof fn m0_terminal_uniqueness(cfg: Config, events: Seq<Event>)
    requires
        config_wf(cfg),
        executable(cfg, initial_state(cfg), events),
    ensures
        terminal_unique(run(initial_state(cfg), events)),
{
    m0_safety(cfg, events);
}

}
