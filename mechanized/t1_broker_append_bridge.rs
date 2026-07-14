use vstd::prelude::*;

#[path = "t1_broker_contract.rs"]
pub mod contract_layer;

verus! {

use contract_layer::p3_layer;
use p3_layer::p2_layer;
use p2_layer::p1_layer;
use p1_layer::p0_layer;
use p0_layer::config_layer;
use config_layer::broker_layer as record_layer;
use record_layer::query_layer::c1_layer;
use c1_layer::replay_layer;
use c1_layer::append_layer;

// B2-A lifts the append protocol through the complete local Broker contract.
// Every local label has one B1 label.  Physical and other non-append labels
// become explicit Stutter labels, so local and projected prefix indices agree.

pub open spec fn append_event(
    event: p0_layer::Event,
) -> append_layer::Event<replay_layer::JournalRecord> {
    match event {
        p0_layer::Event::JournalAppendCall { record } => {
            append_layer::Event::Call { record }
        },
        p0_layer::Event::BrokerLinearize { record } => {
            append_layer::Event::Linearize { record }
        },
        p0_layer::Event::JournalAppendReturn { cut } => {
            append_layer::Event::ReturnOk { cut }
        },
        p0_layer::Event::JournalDiskFull { record, cut } => {
            append_layer::Event::DiskFull { record, cut }
        },
        p0_layer::Event::Crash => append_layer::Event::Crash,
        p0_layer::Event::IgnoreStale { .. } => {
            append_layer::Event::Stutter { kind: 0 }
        },
        p0_layer::Event::RetryRelease { .. } => {
            append_layer::Event::Stutter { kind: 1 }
        },
        p0_layer::Event::BeginRecover => {
            append_layer::Event::Stutter { kind: 2 }
        },
        p0_layer::Event::FinishRecover => {
            append_layer::Event::Stutter { kind: 3 }
        },
        p0_layer::Event::InvokeEvent { .. } => {
            append_layer::Event::Stutter { kind: 4 }
        },
        p0_layer::Event::DeliverEvent { .. } => {
            append_layer::Event::Stutter { kind: 5 }
        },
    }
}

pub open spec fn append_project(
    events: Seq<p0_layer::Event>,
) -> Seq<append_layer::Event<replay_layer::JournalRecord>>
    decreases events.len()
{
    if events.len() == 0 {
        Seq::empty()
    } else {
        append_project(events.drop_last()).push(append_event(events.last()))
    }
}

pub open spec fn append_view(
    state: p0_layer::State,
) -> append_layer::State<replay_layer::JournalRecord> {
    record_layer::append_view(state.core)
}

pub open spec fn broker_pi_append(
    events: Seq<p0_layer::Event>,
) -> Seq<append_layer::AppendEvent<replay_layer::JournalRecord>> {
    append_layer::pi_append(append_project(events))
}

// This reverse parser recognizes zero or more complete serialized append
// transactions.  Successful transactions have Call--Linearize--ReturnOk;
// DiskFull normalization has the adjacent Call--ReturnFull shape.
pub open spec fn completed_append_io(
    io: Seq<append_layer::AppendEvent<replay_layer::JournalRecord>>,
) -> bool
    decreases io.len()
{
    if io.len() == 0 {
        true
    } else {
        match io.last() {
            append_layer::AppendEvent::Return {
                result: append_layer::AppendResult::Full, ..
            } => {
                let before_return = io.drop_last();
                before_return.len() > 0
                    && match before_return.last() {
                        append_layer::AppendEvent::Call { .. } => {
                            completed_append_io(before_return.drop_last())
                        },
                        append_layer::AppendEvent::Linearize { .. }
                        | append_layer::AppendEvent::Return { .. } => false,
                    }
            },
            append_layer::AppendEvent::Return {
                result: append_layer::AppendResult::Ok, ..
            } => {
                let before_return = io.drop_last();
                before_return.len() > 0
                    && match before_return.last() {
                        append_layer::AppendEvent::Linearize { record } => {
                            let before_linearize = before_return.drop_last();
                            before_linearize.len() > 0
                                && match before_linearize.last() {
                                    append_layer::AppendEvent::Call {
                                        record: called,
                                    } => {
                                        called == record
                                            && completed_append_io(
                                                before_linearize.drop_last(),
                                            )
                                    },
                                    append_layer::AppendEvent::Linearize { .. }
                                    | append_layer::AppendEvent::Return { .. } => false,
                                }
                        },
                        append_layer::AppendEvent::Call { .. }
                        | append_layer::AppendEvent::Return { .. } => false,
                    }
            },
            append_layer::AppendEvent::Call { .. }
            | append_layer::AppendEvent::Linearize { .. } => false,
        }
    }
}

// The suffix is determined exactly by the append control at the interval's
// right boundary: none, Call(record), or Call(record),Linearize(record).
pub open spec fn crash_free_epoch_shape(
    io: Seq<append_layer::AppendEvent<replay_layer::JournalRecord>>,
    control: append_layer::AppendControl<replay_layer::JournalRecord>,
) -> bool {
    match control {
        append_layer::AppendControl::Idle => completed_append_io(io),
        append_layer::AppendControl::Called { record } => {
            io.len() > 0
                && match io.last() {
                    append_layer::AppendEvent::Call { record: called } => {
                        called == record && completed_append_io(io.drop_last())
                    },
                    append_layer::AppendEvent::Linearize { .. }
                    | append_layer::AppendEvent::Return { .. } => false,
                }
        },
        append_layer::AppendControl::Linearized { record } => {
            io.len() > 1
                && match io.last() {
                    append_layer::AppendEvent::Linearize {
                        record: linearized,
                    } => {
                        let before_linearize = io.drop_last();
                        linearized == record
                            && match before_linearize.last() {
                                append_layer::AppendEvent::Call {
                                    record: called,
                                } => {
                                    called == record
                                        && completed_append_io(
                                            before_linearize.drop_last(),
                                        )
                                },
                                append_layer::AppendEvent::Linearize { .. }
                                | append_layer::AppendEvent::Return { .. } => false,
                            }
                    },
                    append_layer::AppendEvent::Call { .. }
                    | append_layer::AppendEvent::Return { .. } => false,
                }
        },
    }
}

// This is the append-I/O projection of the current maximal crash-free suffix.
// Stutter labels contribute no action; Crash starts a fresh empty interval.
pub open spec fn epoch_io_after(
    io: Seq<append_layer::AppendEvent<replay_layer::JournalRecord>>,
    event: append_layer::Event<replay_layer::JournalRecord>,
) -> Seq<append_layer::AppendEvent<replay_layer::JournalRecord>> {
    match event {
        append_layer::Event::Call { record } => {
            io.push(append_layer::AppendEvent::Call { record })
        },
        append_layer::Event::Linearize { record } => {
            io.push(append_layer::AppendEvent::Linearize { record })
        },
        append_layer::Event::ReturnOk { cut } => {
            io.push(append_layer::AppendEvent::Return {
                result: append_layer::AppendResult::Ok, cut,
            })
        },
        append_layer::Event::DiskFull { record, cut } => {
            io.push(append_layer::AppendEvent::Call { record })
                .push(append_layer::AppendEvent::Return {
                    result: append_layer::AppendResult::Full, cut,
                })
        },
        append_layer::Event::Crash => Seq::empty(),
        append_layer::Event::Stutter { .. } => io,
    }
}

pub open spec fn current_epoch_io(
    events: Seq<p0_layer::Event>,
) -> Seq<append_layer::AppendEvent<replay_layer::JournalRecord>>
    decreases events.len()
{
    if events.len() == 0 {
        Seq::empty()
    } else {
        epoch_io_after(
            current_epoch_io(events.drop_last()), append_event(events.last()),
        )
    }
}

pub open spec fn crash_free(events: Seq<p0_layer::Event>) -> bool
    decreases events.len()
{
    if events.len() == 0 {
        true
    } else {
        crash_free(events.drop_last())
            && match events.last() {
                p0_layer::Event::Crash => false,
                p0_layer::Event::JournalAppendCall { .. }
                | p0_layer::Event::BrokerLinearize { .. }
                | p0_layer::Event::JournalAppendReturn { .. }
                | p0_layer::Event::JournalDiskFull { .. }
                | p0_layer::Event::InvokeEvent { .. }
                | p0_layer::Event::DeliverEvent { .. }
                | p0_layer::Event::IgnoreStale { .. }
                | p0_layer::Event::RetryRelease { .. }
                | p0_layer::Event::BeginRecover
                | p0_layer::Event::FinishRecover => true,
            }
    }
}

pub open spec fn current_epoch_classified(
    cfg: config_layer::FullConfig,
    events: Seq<p0_layer::Event>,
) -> bool {
    crash_free_epoch_shape(
        current_epoch_io(events),
        append_view(p0_layer::run(cfg, events)).append,
    )
}

pub open spec fn successful_return_cuts_exact(
    events: Seq<p0_layer::Event>,
) -> bool
    decreases events.len()
{
    if events.len() == 0 {
        true
    } else {
        let prefix = events.drop_last();
        successful_return_cuts_exact(prefix)
            && match events.last() {
                p0_layer::Event::JournalAppendReturn { cut } => {
                    cut == p0_layer::pi_journal(prefix).len()
                },
                p0_layer::Event::JournalAppendCall { .. }
                | p0_layer::Event::BrokerLinearize { .. }
                | p0_layer::Event::JournalDiskFull { .. }
                | p0_layer::Event::InvokeEvent { .. }
                | p0_layer::Event::DeliverEvent { .. }
                | p0_layer::Event::IgnoreStale { .. }
                | p0_layer::Event::RetryRelease { .. }
                | p0_layer::Event::Crash
                | p0_layer::Event::BeginRecover
                | p0_layer::Event::FinishRecover => true,
            }
    }
}

pub open spec fn append_agreement_at(
    cfg: config_layer::FullConfig,
    events: Seq<p0_layer::Event>,
) -> bool {
    let state = p0_layer::run(cfg, events);
    let projected = append_project(events);
    append_view(state) == append_layer::run(projected)
        && append_layer::checkpoint(projected)
        && append_layer::append_protocol_prefix(projected)
        && append_layer::legal_control_shape(
            c1_layer::c1_eligibility(config_layer::erase_config(cfg)),
            append_layer::run(projected),
        )
        && append_layer::eligible_append_trace(
            c1_layer::c1_eligibility(config_layer::erase_config(cfg)),
            projected,
        )
        && state.core.evidence.records
            == append_layer::pi_journal(projected)
        && state.core.evidence.ack_cuts
            == append_layer::pi_ack(projected)
        && state.core.evidence.acknowledged_prefix
            == append_layer::acknowledged_prefix_for(
                append_layer::pi_journal(projected),
                append_layer::pi_ack(projected),
            )
        && state.core.broker.append
            == append_layer::append_control_witness(projected)
        && successful_return_cuts_exact(events)
}

pub open spec fn append_bridge_checkpoint(
    cfg: config_layer::FullConfig,
    events: Seq<p0_layer::Event>,
) -> bool {
    contract_layer::local_contract_checkpoint(cfg, events)
        && append_agreement_at(cfg, events)
        && current_epoch_classified(cfg, events)
}

pub proof fn append_project_push(
    events: Seq<p0_layer::Event>,
    event: p0_layer::Event,
)
    ensures append_project(events.push(event))
        == append_project(events).push(append_event(event)),
{
    assert(events.push(event).drop_last() =~= events);
    assert(events.push(event).last() == event);
}

pub proof fn completed_append_io_push_full(
    io: Seq<append_layer::AppendEvent<replay_layer::JournalRecord>>,
    record: replay_layer::JournalRecord,
    cut: nat,
)
    requires completed_append_io(io),
    ensures completed_append_io(
        io.push(append_layer::AppendEvent::Call { record })
            .push(append_layer::AppendEvent::Return {
                result: append_layer::AppendResult::Full, cut,
            }),
    ),
{
    let called = io.push(append_layer::AppendEvent::Call { record });
    let returned = called.push(append_layer::AppendEvent::Return {
        result: append_layer::AppendResult::Full, cut,
    });
    assert(returned.drop_last() =~= called);
    assert(returned.last() == append_layer::AppendEvent::Return {
        result: append_layer::AppendResult::Full, cut,
    });
    assert(called.drop_last() =~= io);
    assert(called.last() == append_layer::AppendEvent::Call { record });
}

pub proof fn completed_append_io_push_ok(
    io: Seq<append_layer::AppendEvent<replay_layer::JournalRecord>>,
    record: replay_layer::JournalRecord,
    cut: nat,
)
    requires completed_append_io(io),
    ensures completed_append_io(
        io.push(append_layer::AppendEvent::Call { record })
            .push(append_layer::AppendEvent::Linearize { record })
            .push(append_layer::AppendEvent::Return {
                result: append_layer::AppendResult::Ok, cut,
            }),
    ),
{
    let called = io.push(append_layer::AppendEvent::Call { record });
    let linearized = called.push(
        append_layer::AppendEvent::Linearize { record },
    );
    let returned = linearized.push(append_layer::AppendEvent::Return {
        result: append_layer::AppendResult::Ok, cut,
    });
    assert(returned.drop_last() =~= linearized);
    assert(returned.last() == append_layer::AppendEvent::Return {
        result: append_layer::AppendResult::Ok, cut,
    });
    assert(linearized.drop_last() =~= called);
    assert(linearized.last()
        == append_layer::AppendEvent::Linearize { record });
    assert(called.drop_last() =~= io);
    assert(called.last() == append_layer::AppendEvent::Call { record });
}

pub proof fn crash_free_epoch_shape_step(
    io: Seq<append_layer::AppendEvent<replay_layer::JournalRecord>>,
    state: append_layer::State<replay_layer::JournalRecord>,
    event: append_layer::Event<replay_layer::JournalRecord>,
)
    requires
        crash_free_epoch_shape(io, state.append),
        append_layer::enabled(state, event),
    ensures crash_free_epoch_shape(
        epoch_io_after(io, event), append_layer::apply(state, event).append,
    ),
{
    match event {
        append_layer::Event::Call { record } => {
            assert(state.append is Idle);
            assert(completed_append_io(io));
            assert(io.push(append_layer::AppendEvent::Call { record }).drop_last()
                =~= io);
            assert(io.push(append_layer::AppendEvent::Call { record }).last()
                == append_layer::AppendEvent::Call { record });
        },
        append_layer::Event::Linearize { record } => {
            match state.append {
                append_layer::AppendControl::Called { record: called } => {
                    assert(called == record);
                    assert(io.len() > 0);
                    assert(io.push(
                        append_layer::AppendEvent::Linearize { record },
                    ).drop_last() =~= io);
                    assert(io.push(
                        append_layer::AppendEvent::Linearize { record },
                    ).last() == append_layer::AppendEvent::Linearize { record });
                },
                append_layer::AppendControl::Idle
                | append_layer::AppendControl::Linearized { .. } => {},
            }
        },
        append_layer::Event::ReturnOk { cut } => {
            match state.append {
                append_layer::AppendControl::Linearized { record } => {
                    let before_linearize = io.drop_last();
                    let complete = before_linearize.drop_last();
                    assert(io.len() > 1);
                    assert(completed_append_io(complete));
                    assert(io.last()
                        == append_layer::AppendEvent::Linearize { record });
                    assert(before_linearize.last()
                        == append_layer::AppendEvent::Call { record });
                    assert(complete
                        .push(append_layer::AppendEvent::Call { record })
                        =~= before_linearize);
                    assert(before_linearize
                        .push(append_layer::AppendEvent::Linearize { record })
                        =~= io);
                    completed_append_io_push_ok(complete, record, cut);
                },
                append_layer::AppendControl::Idle
                | append_layer::AppendControl::Called { .. } => {},
            }
        },
        append_layer::Event::DiskFull { record, cut } => {
            assert(state.append is Idle);
            assert(completed_append_io(io));
            completed_append_io_push_full(io, record, cut);
        },
        append_layer::Event::Crash => {
            assert(completed_append_io(
                Seq::<append_layer::AppendEvent<replay_layer::JournalRecord>>::empty(),
            ));
        },
        append_layer::Event::Stutter { .. } => {},
    }
}

pub proof fn append_project_len(events: Seq<p0_layer::Event>)
    ensures append_project(events).len() == events.len(),
    decreases events.len(),
{
    if events.len() > 0 {
        append_project_len(events.drop_last());
    }
}

pub proof fn append_project_take(
    events: Seq<p0_layer::Event>,
    length: nat,
)
    requires length <= events.len(),
    ensures append_project(events.take(length as int))
        == append_project(events).take(length as int),
    decreases events.len() - length,
{
    if length == events.len() {
        assert(events.take(length as int) =~= events);
        append_project_len(events);
        assert(append_project(events).take(length as int) =~= append_project(events));
    } else {
        assert(length < events.len());
        append_project_take(events.drop_last(), length);
        append_project_len(events.drop_last());
        assert(events.drop_last().take(length as int)
            =~= events.take(length as int));
        assert(append_project(events).drop_last()
            =~= append_project(events.drop_last()));
        assert(append_project(events).take(length as int)
            =~= append_project(events.drop_last()).take(length as int));
    }
}

pub proof fn append_view_initial(cfg: config_layer::FullConfig)
    ensures append_view(p0_layer::initial_state(cfg))
        == append_layer::initial_state(),
{
    record_layer::append_view_initial(config_layer::erase_config(cfg));
}

pub proof fn append_view_apply(
    cfg: config_layer::FullConfig,
    state: p0_layer::State,
    event: p0_layer::Event,
)
    ensures append_view(p0_layer::apply(cfg, state, event))
        == append_layer::apply(append_view(state), append_event(event)),
{
    match event {
        p0_layer::Event::JournalAppendCall { record } => {
            record_layer::append_view_apply(
                config_layer::erase_config(cfg), state.core,
                record_layer::Event::JournalAppendCall { record },
            );
        },
        p0_layer::Event::BrokerLinearize { record } => {
            record_layer::append_view_apply(
                config_layer::erase_config(cfg), state.core,
                record_layer::Event::BrokerLinearize { record },
            );
        },
        p0_layer::Event::JournalAppendReturn { cut } => {
            record_layer::append_view_apply(
                config_layer::erase_config(cfg), state.core,
                record_layer::Event::JournalAppendReturn { cut },
            );
        },
        p0_layer::Event::JournalDiskFull { record, cut } => {
            record_layer::append_view_apply(
                config_layer::erase_config(cfg), state.core,
                record_layer::Event::JournalDiskFull { record, cut },
            );
        },
        p0_layer::Event::IgnoreStale { request, attempt } => {
            record_layer::append_view_apply(
                config_layer::erase_config(cfg), state.core,
                record_layer::Event::IgnoreStale { request, attempt },
            );
        },
        p0_layer::Event::RetryRelease { request } => {
            record_layer::append_view_apply(
                config_layer::erase_config(cfg), state.core,
                record_layer::Event::RetryRelease { request },
            );
        },
        p0_layer::Event::Crash => {
            record_layer::append_view_apply(
                config_layer::erase_config(cfg), state.core,
                record_layer::Event::Crash,
            );
        },
        p0_layer::Event::BeginRecover => {
            record_layer::append_view_apply(
                config_layer::erase_config(cfg), state.core,
                record_layer::Event::BeginRecover,
            );
        },
        p0_layer::Event::FinishRecover => {
            record_layer::append_view_apply(
                config_layer::erase_config(cfg), state.core,
                record_layer::Event::FinishRecover,
            );
        },
        p0_layer::Event::InvokeEvent { .. }
        | p0_layer::Event::DeliverEvent { .. } => {},
    }
}

pub proof fn append_step_admissible(
    cfg: config_layer::FullConfig,
    state: p0_layer::State,
    event: p0_layer::Event,
)
    requires p0_layer::admissibly_enabled(cfg, state, event),
    ensures
        append_layer::enabled(append_view(state), append_event(event)),
        append_layer::record_eligible(
            c1_layer::c1_eligibility(config_layer::erase_config(cfg)),
            append_view(state), append_event(event),
        ),
{
    match event {
        p0_layer::Event::JournalAppendCall { record } => {
            record_layer::admissible_projects(
                config_layer::erase_config(cfg), state.core,
                record_layer::Event::JournalAppendCall { record },
            );
        },
        p0_layer::Event::BrokerLinearize { record } => {
            record_layer::admissible_projects(
                config_layer::erase_config(cfg), state.core,
                record_layer::Event::BrokerLinearize { record },
            );
        },
        p0_layer::Event::JournalAppendReturn { cut } => {
            record_layer::admissible_projects(
                config_layer::erase_config(cfg), state.core,
                record_layer::Event::JournalAppendReturn { cut },
            );
        },
        p0_layer::Event::JournalDiskFull { record, cut } => {
            record_layer::admissible_projects(
                config_layer::erase_config(cfg), state.core,
                record_layer::Event::JournalDiskFull { record, cut },
            );
        },
        p0_layer::Event::IgnoreStale { request, attempt } => {
            record_layer::admissible_projects(
                config_layer::erase_config(cfg), state.core,
                record_layer::Event::IgnoreStale { request, attempt },
            );
        },
        p0_layer::Event::RetryRelease { request } => {
            record_layer::admissible_projects(
                config_layer::erase_config(cfg), state.core,
                record_layer::Event::RetryRelease { request },
            );
        },
        p0_layer::Event::Crash => {
            record_layer::admissible_projects(
                config_layer::erase_config(cfg), state.core,
                record_layer::Event::Crash,
            );
        },
        p0_layer::Event::BeginRecover => {
            record_layer::admissible_projects(
                config_layer::erase_config(cfg), state.core,
                record_layer::Event::BeginRecover,
            );
        },
        p0_layer::Event::FinishRecover => {
            record_layer::admissible_projects(
                config_layer::erase_config(cfg), state.core,
                record_layer::Event::FinishRecover,
            );
        },
        p0_layer::Event::InvokeEvent { .. }
        | p0_layer::Event::DeliverEvent { .. } => {},
    }
}

pub proof fn append_view_run(
    cfg: config_layer::FullConfig,
    events: Seq<p0_layer::Event>,
)
    ensures append_view(p0_layer::run(cfg, events))
        == append_layer::run(append_project(events)),
    decreases events.len(),
{
    if events.len() == 0 {
        append_view_initial(cfg);
    } else {
        let prefix = events.drop_last();
        let event = events.last();
        append_view_run(cfg, prefix);
        append_project_push(prefix, event);
        append_view_apply(cfg, p0_layer::run(cfg, prefix), event);
        assert(prefix.push(event) =~= events);
        assert(p0_layer::run(cfg, events)
            == p0_layer::apply(cfg, p0_layer::run(cfg, prefix), event));
        assert(append_project(events).drop_last() =~= append_project(prefix));
        assert(append_project(events).last() == append_event(event));
        assert(append_layer::run(append_project(events))
            == append_layer::apply(
                append_layer::run(append_project(prefix)),
                append_event(event),
            ));
    }
}

pub proof fn current_epoch_shape_for_run(
    cfg: config_layer::FullConfig,
    events: Seq<p0_layer::Event>,
)
    requires p0_layer::admissibly_executable(cfg, events),
    ensures current_epoch_classified(cfg, events),
    decreases events.len(),
{
    if events.len() == 0 {
        append_view_initial(cfg);
        assert(completed_append_io(
            Seq::<append_layer::AppendEvent<replay_layer::JournalRecord>>::empty(),
        ));
    } else {
        let prefix = events.drop_last();
        let event = events.last();
        assert(p0_layer::admissibly_executable(cfg, prefix));
        current_epoch_shape_for_run(cfg, prefix);
        append_view_run(cfg, prefix);
        append_step_admissible(cfg, p0_layer::run(cfg, prefix), event);
        crash_free_epoch_shape_step(
            current_epoch_io(prefix),
            append_view(p0_layer::run(cfg, prefix)),
            append_event(event),
        );
        append_view_apply(cfg, p0_layer::run(cfg, prefix), event);
        assert(prefix.push(event) =~= events);
        assert(p0_layer::run(cfg, events)
            == p0_layer::apply(cfg, p0_layer::run(cfg, prefix), event));
    }
}

pub proof fn all_prefixes_current_epoch_classified(
    cfg: config_layer::FullConfig,
    events: Seq<p0_layer::Event>,
)
    requires p0_layer::admissibly_executable(cfg, events),
    ensures forall|length: nat| length <= events.len() ==>
        #[trigger] current_epoch_classified(
            cfg, events.take(length as int),
        ),
{
    assert forall|length: nat| length <= events.len() implies
        #[trigger] current_epoch_classified(
            cfg, events.take(length as int),
        ) by {
        p0_layer::executable_prefix(cfg, events, length);
        current_epoch_shape_for_run(cfg, events.take(length as int));
    }
}

pub proof fn append_admissibly_executable(
    cfg: config_layer::FullConfig,
    events: Seq<p0_layer::Event>,
)
    requires p0_layer::admissibly_executable(cfg, events),
    ensures c1_layer::c1_admissibly_executable(
        config_layer::erase_config(cfg), append_project(events),
    ),
    decreases events.len(),
{
    if events.len() > 0 {
        let prefix = events.drop_last();
        let event = events.last();
        append_admissibly_executable(cfg, prefix);
        append_view_run(cfg, prefix);
        append_step_admissible(cfg, p0_layer::run(cfg, prefix), event);
        append_project_push(prefix, event);
        assert(prefix.push(event) =~= events);
        assert(append_project(events).drop_last() =~= append_project(prefix));
        assert(append_project(events).last() == append_event(event));
    }
}

pub proof fn broker_pi_journal_exact(events: Seq<p0_layer::Event>)
    ensures append_layer::pi_journal(append_project(events))
        == p0_layer::pi_journal(events),
    decreases events.len(),
{
    if events.len() > 0 {
        let prefix = events.drop_last();
        let event = events.last();
        broker_pi_journal_exact(prefix);
        append_project_push(prefix, event);
        append_layer::pi_journal_push(append_project(prefix), append_event(event));
        assert(prefix.push(event) =~= events);
        match event {
            p0_layer::Event::JournalAppendCall { .. }
            | p0_layer::Event::BrokerLinearize { .. }
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
    }
}

pub proof fn broker_pi_ack_exact(events: Seq<p0_layer::Event>)
    ensures append_layer::pi_ack(append_project(events))
        == p0_layer::pi_ack(events),
    decreases events.len(),
{
    if events.len() > 0 {
        let prefix = events.drop_last();
        let event = events.last();
        broker_pi_ack_exact(prefix);
        append_project_push(prefix, event);
        append_layer::pi_ack_push(append_project(prefix), append_event(event));
        assert(prefix.push(event) =~= events);
        match event {
            p0_layer::Event::JournalAppendCall { .. }
            | p0_layer::Event::BrokerLinearize { .. }
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
    }
}

pub proof fn current_epoch_io_is_crash_free_projection(
    events: Seq<p0_layer::Event>,
)
    requires crash_free(events),
    ensures current_epoch_io(events) == broker_pi_append(events),
    decreases events.len(),
{
    if events.len() > 0 {
        let prefix = events.drop_last();
        let event = events.last();
        assert(crash_free(prefix));
        current_epoch_io_is_crash_free_projection(prefix);
        append_project_push(prefix, event);
        append_layer::pi_append_push(
            append_project(prefix), append_event(event),
        );
        assert(prefix.push(event) =~= events);
        match event {
            p0_layer::Event::Crash => {
                assert(false);
            },
            p0_layer::Event::JournalAppendCall { .. }
            | p0_layer::Event::BrokerLinearize { .. }
            | p0_layer::Event::JournalAppendReturn { .. }
            | p0_layer::Event::JournalDiskFull { .. }
            | p0_layer::Event::InvokeEvent { .. }
            | p0_layer::Event::DeliverEvent { .. }
            | p0_layer::Event::IgnoreStale { .. }
            | p0_layer::Event::RetryRelease { .. }
            | p0_layer::Event::BeginRecover
            | p0_layer::Event::FinishRecover => {},
        }
    }
}

pub proof fn successful_return_cuts_exact_for_run(
    cfg: config_layer::FullConfig,
    events: Seq<p0_layer::Event>,
)
    requires
        config_layer::full_config_wf(cfg),
        p0_layer::admissibly_executable(cfg, events),
    ensures successful_return_cuts_exact(events),
    decreases events.len(),
{
    if events.len() > 0 {
        let prefix = events.drop_last();
        let event = events.last();
        successful_return_cuts_exact_for_run(cfg, prefix);
        assert(p0_layer::admissibly_executable(cfg, prefix));
        p0_layer::run_history_agreement(cfg, prefix);
        assert(prefix.push(event) =~= events);
        match event {
            p0_layer::Event::JournalAppendReturn { cut } => {
                assert(p0_layer::evidence_admissible(
                    cfg, p0_layer::run(cfg, prefix), event,
                ));
                assert(cut == p0_layer::run(cfg, prefix).core.evidence.records.len());
                assert(p0_layer::run(cfg, prefix).core.evidence.records
                    == p0_layer::pi_journal(prefix));
            },
            p0_layer::Event::JournalAppendCall { .. }
            | p0_layer::Event::BrokerLinearize { .. }
            | p0_layer::Event::JournalDiskFull { .. }
            | p0_layer::Event::InvokeEvent { .. }
            | p0_layer::Event::DeliverEvent { .. }
            | p0_layer::Event::IgnoreStale { .. }
            | p0_layer::Event::RetryRelease { .. }
            | p0_layer::Event::Crash
            | p0_layer::Event::BeginRecover
            | p0_layer::Event::FinishRecover => {},
        }
    }
}

pub proof fn append_agreement_for_run(
    cfg: config_layer::FullConfig,
    events: Seq<p0_layer::Event>,
)
    requires
        config_layer::full_config_wf(cfg),
        p0_layer::admissibly_executable(cfg, events),
    ensures append_agreement_at(cfg, events),
{
    let erased = config_layer::erase_config(cfg);
    let projected = append_project(events);
    append_admissibly_executable(cfg, events);
    append_layer::b1_append_trace_safety_with_eligibility(
        c1_layer::c1_eligibility(erased), projected,
    );
    append_view_run(cfg, events);
    broker_pi_journal_exact(events);
    broker_pi_ack_exact(events);
    successful_return_cuts_exact_for_run(cfg, events);
    assert(append_layer::checkpoint(projected));
    assert(append_layer::run(projected).evidence.records
        == append_layer::pi_journal(projected));
    assert(append_layer::run(projected).evidence.ack_cuts
        == append_layer::pi_ack(projected));
    assert(append_layer::run(projected).evidence.acknowledged_prefix
        == append_layer::acknowledged_prefix_for(
            append_layer::pi_journal(projected),
            append_layer::pi_ack(projected),
        ));
    assert(append_layer::run(projected).append
        == append_layer::append_control_witness(projected));
}

// At every local prefix, current_epoch_io is precisely the append-I/O word
// since the latest Crash.  Its shape therefore classifies every completed
// maximal crash-free interval and the possibly pending final interval.
pub proof fn b2_crash_free_epoch_language(
    cfg: config_layer::FullConfig,
    events: Seq<p0_layer::Event>,
)
    requires p0_layer::admissibly_executable(cfg, events),
    ensures
        current_epoch_classified(cfg, events),
        forall|length: nat| length <= events.len() ==>
            #[trigger] current_epoch_classified(
                cfg, events.take(length as int),
            ),
{
    current_epoch_shape_for_run(cfg, events);
    all_prefixes_current_epoch_classified(cfg, events);
}

pub proof fn b2_append_protocol_bridge_safety(
    cfg: config_layer::FullConfig,
    events: Seq<p0_layer::Event>,
)
    requires
        config_layer::full_config_wf(cfg),
        p0_layer::admissibly_executable(cfg, events),
    ensures
        append_bridge_checkpoint(cfg, events),
        c1_layer::c1_admissibly_executable(
            config_layer::erase_config(cfg), append_project(events),
        ),
        append_layer::append_protocol_prefix(append_project(events)),
        append_layer::pi_journal(append_project(events))
            == p0_layer::pi_journal(events),
        append_layer::pi_ack(append_project(events))
            == p0_layer::pi_ack(events),
        forall|length: nat| length <= events.len() ==>
            #[trigger] append_bridge_checkpoint(
                cfg, events.take(length as int),
            ),
{
    contract_layer::b2_local_broker_contract_safety(cfg, events);
    append_agreement_for_run(cfg, events);
    b2_crash_free_epoch_language(cfg, events);
    append_admissibly_executable(cfg, events);
    broker_pi_journal_exact(events);
    broker_pi_ack_exact(events);
    assert forall|length: nat| length <= events.len() implies
        #[trigger] append_bridge_checkpoint(
            cfg, events.take(length as int),
        ) by {
        p0_layer::executable_prefix(cfg, events, length);
        contract_layer::b2_local_broker_contract_safety(
            cfg, events.take(length as int),
        );
        append_agreement_for_run(cfg, events.take(length as int));
        current_epoch_shape_for_run(cfg, events.take(length as int));
    }
}

} // verus!
