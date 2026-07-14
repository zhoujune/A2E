use vstd::prelude::*;

#[path = "t1_replay.rs"]
pub mod replay_layer;

#[path = "t1_append.rs"]
pub mod append_layer;

verus! {

pub open spec fn c1_eligibility(
    cfg: replay_layer::Config,
) -> spec_fn(
    Seq<replay_layer::JournalRecord>,
    replay_layer::JournalRecord,
) -> bool {
    |records: Seq<replay_layer::JournalRecord>,
     record: replay_layer::JournalRecord|
        replay_layer::structural_enabled(cfg, records, record)
}

pub open spec fn c1_admissibly_executable(
    cfg: replay_layer::Config,
    events: Seq<append_layer::Event<replay_layer::JournalRecord>>,
) -> bool {
    append_layer::admissibly_executable(
        c1_eligibility(cfg),
        events,
    )
}

pub open spec fn c1_linearizations_legal(
    cfg: replay_layer::Config,
    events: Seq<append_layer::Event<replay_layer::JournalRecord>>,
) -> bool
    decreases events.len()
{
    if events.len() == 0 {
        true
    } else {
        let prefix = events.drop_last();
        c1_linearizations_legal(cfg, prefix)
            && match events.last() {
                append_layer::Event::Linearize { record } => {
                    replay_layer::structural_enabled(
                        cfg,
                        append_layer::pi_journal(prefix),
                        record,
                    )
                },
                append_layer::Event::Call { .. }
                | append_layer::Event::ReturnOk { .. }
                | append_layer::Event::DiskFull { .. }
                | append_layer::Event::Crash
                | append_layer::Event::Stutter { .. } => true,
            }
    }
}

pub open spec fn c1_checkpoint(
    cfg: replay_layer::Config,
    events: Seq<append_layer::Event<replay_layer::JournalRecord>>,
) -> bool {
    let journal = append_layer::pi_journal(events);
    let state = append_layer::run(events);
    append_layer::checkpoint(events)
        && append_layer::append_protocol_prefix(events)
        && append_layer::legal_control_shape(c1_eligibility(cfg), state)
        && append_layer::eligible_append_trace(c1_eligibility(cfg), events)
        && c1_linearizations_legal(cfg, events)
        && replay_layer::journal_legal(cfg, journal)
        && replay_layer::r1_replay_invariant(cfg, journal)
        && state.evidence.records == journal
        && replay_layer::r1_replay_invariant(cfg, state.evidence.records)
}

pub proof fn c1_legal_append_replay(
    cfg: replay_layer::Config,
    events: Seq<append_layer::Event<replay_layer::JournalRecord>>,
)
    requires
        replay_layer::config_wf(cfg),
        c1_admissibly_executable(cfg, events),
    ensures
        c1_checkpoint(cfg, events),
        replay_layer::journal_legal(cfg, append_layer::pi_journal(events)),
        replay_layer::r1_replay_invariant(
            cfg,
            append_layer::pi_journal(events),
        ),
        c1_linearizations_legal(cfg, events),
        append_layer::run(events).evidence.records
            == append_layer::pi_journal(events),
        replay_layer::r1_replay_invariant(
            cfg,
            append_layer::run(events).evidence.records,
        ),
    decreases events.len(),
{
    append_layer::b1_append_trace_safety_with_eligibility(
        c1_eligibility(cfg),
        events,
    );
    if events.len() == 0 {
        let journal = Seq::<replay_layer::JournalRecord>::empty();
        assert(replay_layer::journal_legal(cfg, journal));
        replay_layer::r1_typed_journal_replay_safety(cfg, journal);
    } else {
        let prefix = events.drop_last();
        let event = events.last();
        assert(c1_admissibly_executable(cfg, prefix));
        c1_legal_append_replay(cfg, prefix);
        assert(prefix.push(event) =~= events);
        append_layer::pi_journal_push(prefix, event);
        match event {
            append_layer::Event::Linearize { record } => {
                assert(append_layer::eligible_append_trace(
                    c1_eligibility(cfg),
                    events,
                ));
                assert(replay_layer::structural_enabled(
                    cfg,
                    append_layer::pi_journal(prefix),
                    record,
                ));
                replay_layer::r1_legal_extension(
                    cfg,
                    append_layer::pi_journal(prefix),
                    record,
                );
            },
            append_layer::Event::Call { .. }
            | append_layer::Event::ReturnOk { .. }
            | append_layer::Event::DiskFull { .. }
            | append_layer::Event::Crash
            | append_layer::Event::Stutter { .. } => {},
        }
    }
}

pub proof fn c1_all_prefixes(
    cfg: replay_layer::Config,
    events: Seq<append_layer::Event<replay_layer::JournalRecord>>,
)
    requires
        replay_layer::config_wf(cfg),
        c1_admissibly_executable(cfg, events),
    ensures
        c1_checkpoint(cfg, events),
        forall|n: int| 0 <= n <= events.len()
            ==> #[trigger] c1_checkpoint(cfg, events.take(n)),
{
    c1_legal_append_replay(cfg, events);
    assert forall|n: int| 0 <= n <= events.len()
        implies #[trigger] c1_checkpoint(cfg, events.take(n)) by {
        append_layer::admissible_executable_prefix(
            c1_eligibility(cfg),
            events,
            n,
        );
        assert(c1_admissibly_executable(cfg, events.take(n)));
        c1_legal_append_replay(cfg, events.take(n));
    }
}

}
