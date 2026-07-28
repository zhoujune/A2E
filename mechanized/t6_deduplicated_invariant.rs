use vstd::prelude::*;

#[path = "t6_deduplicated_operational.rs"]
pub mod t6_dd0_layer;

verus! {

use t6_dd0_layer::*;
use t6_dd0_layer::t6_ro0_layer;
use t6_ro0_layer::t6_x0_layer;
use t6_x0_layer::*;
use t6_x0_layer::t6_p0_layer;
use t6_p0_layer::t6_m0_layer;
use t6_m0_layer::*;
use t6_m0_layer::t6_a1_layer;
use t6_a1_layer::*;
use t6_a1_layer::t6_a0_layer;
use t6_a0_layer::*;
use t6_a0_layer::t6_s0_layer;
use t6_s0_layer::t6_c0_layer;
use t6_c0_layer::t6_e0_layer;
use t6_e0_layer::t6_d0_layer;
use t6_d0_layer::*;
use t6_d0_layer::t5_c0_layer;
use t5_c0_layer::t5_r0_layer;
use t5_r0_layer::t5_e0_layer;
use t5_e0_layer::t5_s0_layer;
use t5_s0_layer::t4_layer;
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
use contract_layer::p3_layer;
use p3_layer::p2_layer;
use p2_layer::p1_layer;
use p1_layer::p0_layer;
use p0_layer::config_layer;
use config_layer::broker_layer as record_layer;
use record_layer::query_layer;
use query_layer::c1_layer;
use c1_layer::append_layer;
use c1_layer::replay_layer;

// T6-DD1 proves the inductive safety boundary of DD0's memoizing service.
// A service decision is unique, is backed by an invocation at its recorded
// history cut, determines the protected slot, and classifies every delivered
// response. These facts derive both the Deduplicated class law and the generic
// AdapterRely predicate from executions of the operational machine.

pub open spec fn dd1_decision_values_allowed(
    decisions: Seq<DDDecisionRecord>,
) -> bool {
    forall|index: int| 0 <= index < decisions.len() ==>
        match #[trigger] decisions[index].decision {
            DDDecision::Applied { value } => value.id == 1,
            DDDecision::Rejected => true,
        }
}

pub open spec fn dd1_observation_matches_decision(
    decisions: Seq<DDDecisionRecord>,
    observation: replay_layer::Observation,
) -> bool {
    match observation {
        replay_layer::Observation::Success(value) => {
            dd_has_applied(decisions, value)
        },
        replay_layer::Observation::Failure => {
            dd_has_rejected(decisions)
        },
        replay_layer::Observation::Ambiguous
        | replay_layer::Observation::InvalidResult(_) => false,
    }
}

pub open spec fn dd1_history_classified(state: DDAdapterState) -> bool {
    forall|index: int| 0 <= index < state.history.len() ==>
        match #[trigger] state.history[index] {
            p0_layer::PhysicalEvent::Invoke { .. } => true,
            p0_layer::PhysicalEvent::Delivered { observation, .. } => {
                dd1_observation_matches_decision(
                    state.decisions, observation,
                )
            },
        }
}

pub open spec fn dd1_machine_invariant(state: DDAdapterState) -> bool {
    let cfg = dd_full_config();
    &&& state.history
        == projection_layer::pi_adapter(state.globals, state.request)
    &&& request_local_history(state.history, state.request)
    &&& canonical_invocations(cfg, state.history, state.request)
    &&& positive_attempt_identifiers(state.history)
    &&& p1_layer::physical_unique(state.history)
    &&& p1_layer::physical_ordered(state.history)
    &&& dd_decisions_well_formed(state.decisions)
    &&& dd1_decision_values_allowed(state.decisions)
    &&& dd_decisions_have_history_provenance(
        state.history, state.request, state.decisions,
    )
    &&& dd_post_state_factored(dd_external_run(state))
    &&& dd1_history_classified(state)
    &&& match state.active {
        Option::None => true,
        Option::Some(attempt) => {
            p1_layer::invoke_count(
                state.history, state.request, attempt,
            ) == 1
                && p1_layer::delivery_count(
                    state.history, state.request, attempt,
                ) == 0
        },
    }
}

pub open spec fn dd1_execution_invariant(
    request: replay_layer::RequestId,
    initial_slot: Option<replay_layer::Value>,
    state: DDAdapterState,
) -> bool {
    state.request == request
        && state.initial_slot == initial_slot
        && dd1_machine_invariant(state)
}

proof fn dd1_single_decision_index_is_zero(
    decisions: Seq<DDDecisionRecord>,
    index: int,
)
    requires
        dd_decisions_well_formed(decisions),
        0 <= index < decisions.len(),
    ensures index == 0,
{
}

proof fn dd1_applied_values_equal(
    decisions: Seq<DDDecisionRecord>,
    left: replay_layer::Value,
    right: replay_layer::Value,
)
    requires
        dd_decisions_well_formed(decisions),
        dd_has_applied(decisions, left),
        dd_has_applied(decisions, right),
    ensures left == right,
{
    let left_index = choose|index: int| 0 <= index < decisions.len()
        && decisions[index].decision == DDDecision::Applied { value: left };
    let right_index = choose|index: int| 0 <= index < decisions.len()
        && decisions[index].decision == DDDecision::Applied { value: right };
    dd1_single_decision_index_is_zero(decisions, left_index);
    dd1_single_decision_index_is_zero(decisions, right_index);
    assert(decisions[left_index].decision
        == DDDecision::Applied { value: left });
    assert(decisions[right_index].decision
        == DDDecision::Applied { value: right });
}

proof fn dd1_applied_excludes_rejected(
    decisions: Seq<DDDecisionRecord>,
    value: replay_layer::Value,
)
    requires
        dd_decisions_well_formed(decisions),
        dd_has_applied(decisions, value),
    ensures !dd_has_rejected(decisions),
{
    if dd_has_rejected(decisions) {
        let applied_index = choose|index: int| 0 <= index < decisions.len()
            && decisions[index].decision
                == DDDecision::Applied { value };
        let rejected_index = choose|index: int| 0 <= index < decisions.len()
            && decisions[index].decision == DDDecision::Rejected;
        dd1_single_decision_index_is_zero(decisions, applied_index);
        dd1_single_decision_index_is_zero(decisions, rejected_index);
        assert(false);
    }
}

proof fn dd1_rejected_excludes_applied(
    decisions: Seq<DDDecisionRecord>,
)
    requires
        dd_decisions_well_formed(decisions),
        dd_has_rejected(decisions),
    ensures !dd_has_any_applied(decisions),
{
    if dd_has_any_applied(decisions) {
        let applied_index = choose|index: int| 0 <= index < decisions.len()
            && decisions[index].decision is Applied;
        let rejected_index = choose|index: int| 0 <= index < decisions.len()
            && decisions[index].decision == DDDecision::Rejected;
        dd1_single_decision_index_is_zero(decisions, applied_index);
        dd1_single_decision_index_is_zero(decisions, rejected_index);
        assert(false);
    }
}

proof fn dd1_applied_value_is_allowed(
    decisions: Seq<DDDecisionRecord>,
    value: replay_layer::Value,
)
    requires
        dd1_decision_values_allowed(decisions),
        dd_has_applied(decisions, value),
    ensures value.id == 1,
{
    let index = choose|index: int| 0 <= index < decisions.len()
        && decisions[index].decision == DDDecision::Applied { value };
    assert(match decisions[index].decision {
        DDDecision::Applied { value: selected } => selected.id == 1,
        DDDecision::Rejected => true,
    });
}

proof fn dd1_has_applied_implies_any(
    decisions: Seq<DDDecisionRecord>,
    value: replay_layer::Value,
)
    requires dd_has_applied(decisions, value),
    ensures dd_has_any_applied(decisions),
{
    let index = choose|index: int| 0 <= index < decisions.len()
        && decisions[index].decision == DDDecision::Applied { value };
    assert(exists|selected: int| 0 <= selected < decisions.len()
        && (#[trigger] decisions[selected].decision) is Applied) by {
        let selected = index;
    }
}

proof fn dd1_applied_run_has_one_effect(
    request: replay_layer::RequestId,
    value: replay_layer::Value,
    run: ExternalRun<Option<replay_layer::Value>, DedupWitness>,
)
    requires
        dd_post_state_factored(run),
        dd_has_applied(run.interference.decisions, value),
    ensures
        dd_one_effect(request, run),
        dd_result_spec(request, value, run),
{
    dd1_has_applied_implies_any(run.interference.decisions, value);
    assert(exists|selected: replay_layer::Value| {
        &&& #[trigger] dd_has_applied(
            run.interference.decisions, selected,
        )
        &&& run.post == Option::<replay_layer::Value>::Some(selected)
    });
    let selected = choose|selected: replay_layer::Value| {
        &&& dd_has_applied(run.interference.decisions, selected)
        &&& run.post == Option::<replay_layer::Value>::Some(selected)
    };
    assert(dd_one_effect(request, run)) by {
        let witness = selected;
    }
}

proof fn dd1_rejected_run_has_zero_effect(
    request: replay_layer::RequestId,
    run: ExternalRun<Option<replay_layer::Value>, DedupWitness>,
)
    requires
        dd_decisions_well_formed(run.interference.decisions),
        dd_post_state_factored(run),
        dd_has_rejected(run.interference.decisions),
    ensures dd_zero_effect(request, run),
{
    dd1_rejected_excludes_applied(run.interference.decisions);
    assert(run.post == run.pre);
}

proof fn dd1_factored_run_has_zero_or_one_effect(
    request: replay_layer::RequestId,
    run: ExternalRun<Option<replay_layer::Value>, DedupWitness>,
)
    requires dd_post_state_factored(run),
    ensures dd_zero_effect(request, run) || dd_one_effect(request, run),
{
    if dd_has_any_applied(run.interference.decisions) {
        assert(exists|selected: replay_layer::Value| {
            &&& #[trigger] dd_has_applied(
                run.interference.decisions, selected,
            )
            &&& run.post == Option::<replay_layer::Value>::Some(selected)
        });
        let selected = choose|selected: replay_layer::Value| {
            &&& dd_has_applied(run.interference.decisions, selected)
            &&& run.post == Option::<replay_layer::Value>::Some(selected)
        };
        assert(dd_one_effect(request, run)) by {
            let witness = selected;
        }
    } else {
        assert(run.post == run.pre);
        assert(dd_zero_effect(request, run));
    }
}

proof fn dd1_selected_delivery_is_classified(
    cfg: config_layer::FullConfig,
    history: Seq<p0_layer::PhysicalEvent>,
    request: replay_layer::RequestId,
    attempt: replay_layer::AttemptId,
    observation: replay_layer::Observation,
    run: ExternalRun<Option<replay_layer::Value>, DedupWitness>,
)
    requires
        p1_layer::physical_unique(history),
        delivered_observations_classified(
            cfg, dd_adapter(), history, request, run,
        ),
        delivery(history, request, attempt) == Option::Some(observation),
    ensures
        dd_classification_ok(request, attempt, observation, run),
        match observation {
            replay_layer::Observation::Success(value) => {
                cfg.valid_results.contains((request, value))
            },
            replay_layer::Observation::Failure
            | replay_layer::Observation::Ambiguous
            | replay_layer::Observation::InvalidResult(_) => true,
        },
{
    t6_c0_layer::selected_delivery_has_witness(
        history, request, attempt, observation,
    );
    assert(dd_classification_ok(request, attempt, observation, run));
}

pub proof fn dd_adapter_is_verified()
    ensures adapter_verified(dd_paper()),
{
    let paper = dd_paper();
    let cfg = dd_full_config();
    t1_layer::paper_broker_config_is_broker(paper);
    assert(t1_layer::paper_broker_config(paper) == cfg);
    assert forall|request: replay_layer::RequestId,
                  records: Seq<replay_layer::JournalRecord>,
                  history: Seq<p0_layer::PhysicalEvent>,
                  run: ExternalRun<
                      Option<replay_layer::Value>, DedupWitness,
                  >,
                  outcome: TerminalOutcome| #![auto] {
        &&& replay_layer::journal_legal(
            config_layer::erase_config(cfg), records,
        )
        &&& adapter_rely_trace(paper, request, history, run)
        &&& outcome_evidence(cfg, records, request, history, outcome)
        &&& broker_outcome_compatible(
            cfg, records, request, history, outcome,
        )
    } implies refines(paper, request, history, run, outcome) by {
        let adapter = dd_adapter();
        assert(cfg.request[request].retry_class
            == replay_layer::RetryClass::Deduplicated);
        assert(adapter_rely_trace(
            paper, request, history, run,
        ));
        assert((adapter.env_rely)(request, history, run));
        assert(dd_env_rely(request, history, run));
        assert(dd_decisions_well_formed(
            run.interference.decisions,
        ));
        assert(dd_post_state_factored(run));
        assert(delivered_observations_classified(
            cfg, adapter, history, request, run,
        ));
        assert(p1_layer::physical_unique(history));
        match outcome {
            TerminalOutcome::Commit { attempt, value } => {
                assert(delivery(history, request, attempt)
                    == Option::Some(
                        replay_layer::Observation::Success(value),
                    ));
                dd1_selected_delivery_is_classified(
                    cfg,
                    history,
                    request,
                    attempt,
                    replay_layer::Observation::Success(value),
                    run,
                );
                assert(dd_has_applied(
                    run.interference.decisions, value,
                ));
                dd1_applied_run_has_one_effect(request, value, run);
            },
            TerminalOutcome::Fail { attempt } => {
                assert(delivery(history, request, attempt)
                    == Option::Some(
                        replay_layer::Observation::Failure,
                    ));
                dd1_selected_delivery_is_classified(
                    cfg,
                    history,
                    request,
                    attempt,
                    replay_layer::Observation::Failure,
                    run,
                );
                assert(dd_has_rejected(run.interference.decisions));
                dd1_rejected_run_has_zero_effect(request, run);
            },
            TerminalOutcome::UnknownOutcome { .. } => {
                dd1_factored_run_has_zero_or_one_effect(request, run);
            },
        }
    }
}

proof fn dd1_invoked_attempt_is_positive(
    history: Seq<p0_layer::PhysicalEvent>,
    request: replay_layer::RequestId,
    attempt: replay_layer::AttemptId,
)
    requires
        positive_attempt_identifiers(history),
        invoked(history, request, attempt),
    ensures attempt > 0,
{
    p1_layer::invoke_index_sound(history, request, attempt);
    match p1_layer::invoke_index(history, request, attempt) {
        Option::None => {
            assert(p1_layer::invoke_count(history, request, attempt) == 0);
            assert(false);
        },
        Option::Some(index) => {
            assert(index < history.len());
            assert(p1_layer::is_invoke_for(
                history[index as int], request, attempt,
            ));
            match history[index as int] {
                p0_layer::PhysicalEvent::Invoke {
                    attempt: recorded_attempt, ..
                } => {
                    assert(recorded_attempt == attempt);
                    assert(recorded_attempt > 0);
                },
                p0_layer::PhysicalEvent::Delivered { .. } => {
                    assert(false);
                },
            }
        },
    }
}

proof fn dd1_append_history_shape(
    state: DDAdapterState,
    physical: p0_layer::PhysicalEvent,
)
    requires
        request_local_history(state.history, state.request),
        canonical_invocations(
            dd_full_config(), state.history, state.request,
        ),
        positive_attempt_identifiers(state.history),
        event_is_for_request(physical, state.request),
        match physical {
            p0_layer::PhysicalEvent::Invoke { call, attempt, .. } => {
                call == config_layer::canonical_call(
                    dd_full_config(), state.request,
                ) && attempt > 0
            },
            p0_layer::PhysicalEvent::Delivered { attempt, .. } => attempt > 0,
        },
    ensures
        request_local_history(state.history.push(physical), state.request),
        canonical_invocations(
            dd_full_config(),
            state.history.push(physical),
            state.request,
        ),
        positive_attempt_identifiers(state.history.push(physical)),
{
    assert forall|index: int| 0 <= index < state.history.push(physical).len()
        implies event_is_for_request(
            #[trigger] state.history.push(physical)[index], state.request,
        ) by {
        if index < state.history.len() {
            assert(state.history.push(physical)[index] == state.history[index]);
        } else {
            assert(index == state.history.len());
            assert(state.history.push(physical)[index] == physical);
        }
    }
    assert forall|index: int| 0 <= index < state.history.push(physical).len()
        implies match #[trigger] state.history.push(physical)[index] {
            p0_layer::PhysicalEvent::Invoke { call, .. } => {
                call == config_layer::canonical_call(
                    dd_full_config(), state.request,
                )
            },
            p0_layer::PhysicalEvent::Delivered { .. } => true,
        } by {
        if index < state.history.len() {
            assert(state.history.push(physical)[index] == state.history[index]);
        } else {
            assert(index == state.history.len());
            assert(state.history.push(physical)[index] == physical);
        }
    }
    assert forall|index: int| 0 <= index < state.history.push(physical).len()
        implies match #[trigger] state.history.push(physical)[index] {
            p0_layer::PhysicalEvent::Invoke { attempt, .. }
            | p0_layer::PhysicalEvent::Delivered { attempt, .. } => attempt > 0,
        } by {
        if index < state.history.len() {
            assert(state.history.push(physical)[index] == state.history[index]);
        } else {
            assert(index == state.history.len());
            assert(state.history.push(physical)[index] == physical);
        }
    }
}

proof fn dd1_decisions_history_push(
    history: Seq<p0_layer::PhysicalEvent>,
    physical: p0_layer::PhysicalEvent,
    request: replay_layer::RequestId,
    decisions: Seq<DDDecisionRecord>,
)
    requires dd_decisions_have_history_provenance(
        history, request, decisions,
    ),
    ensures dd_decisions_have_history_provenance(
        history.push(physical), request, decisions,
    ),
{
    assert forall|index: int| 0 <= index < decisions.len() implies {
        let record = #[trigger] decisions[index];
        &&& record.history_cut <= history.push(physical).len()
        &&& invoked(
            history.push(physical).take(record.history_cut as int),
            request, record.attempt,
        )
        &&& p1_layer::delivery_count(
            history.push(physical).take(record.history_cut as int),
            request, record.attempt,
        ) == 0
    } by {
        let record = decisions[index];
        assert(record.history_cut <= history.len());
        append_layer::take_push_stable(
            history, physical, record.history_cut,
        );
        if record.history_cut < history.len() {
            assert(history.push(physical).take(record.history_cut as int)
                =~= history.take(record.history_cut as int));
        } else {
            assert(record.history_cut == history.len());
            assert(history.push(physical).take(record.history_cut as int)
                =~= history);
        }
    }
}

proof fn dd1_history_classified_push(
    history: Seq<p0_layer::PhysicalEvent>,
    decisions: Seq<DDDecisionRecord>,
    physical: p0_layer::PhysicalEvent,
)
    requires
        forall|index: int| 0 <= index < history.len() ==>
            match #[trigger] history[index] {
                p0_layer::PhysicalEvent::Invoke { .. } => true,
                p0_layer::PhysicalEvent::Delivered { observation, .. } => {
                    dd1_observation_matches_decision(decisions, observation)
                },
            },
        match physical {
            p0_layer::PhysicalEvent::Invoke { .. } => true,
            p0_layer::PhysicalEvent::Delivered { observation, .. } => {
                dd1_observation_matches_decision(decisions, observation)
            },
        },
    ensures forall|index: int| 0 <= index < history.push(physical).len() ==>
        match #[trigger] history.push(physical)[index] {
            p0_layer::PhysicalEvent::Invoke { .. } => true,
            p0_layer::PhysicalEvent::Delivered { observation, .. } => {
                dd1_observation_matches_decision(decisions, observation)
            },
        },
{
    assert forall|index: int| 0 <= index < history.push(physical).len()
        implies match #[trigger] history.push(physical)[index] {
            p0_layer::PhysicalEvent::Invoke { .. } => true,
            p0_layer::PhysicalEvent::Delivered { observation, .. } => {
                dd1_observation_matches_decision(decisions, observation)
            },
        } by {
        if index < history.len() {
            assert(history.push(physical)[index] == history[index]);
        } else {
            assert(index == history.len());
            assert(history.push(physical)[index] == physical);
        }
    }
}

pub proof fn dd1_initial_state_satisfies_invariant(
    request: replay_layer::RequestId,
    initial_slot: Option<replay_layer::Value>,
)
    ensures dd1_execution_invariant(
        request,
        initial_slot,
        dd_initial_state(request, initial_slot),
    ),
{
    reveal_with_fuel(projection_layer::adapter_from_physical, 1);
    reveal_with_fuel(projection_layer::pi_physical, 1);
    reveal_with_fuel(p1_layer::physical_unique, 1);
    reveal_with_fuel(p1_layer::physical_ordered, 1);
}

proof fn dd1_service_decide_preserves_invariant(
    before: DDAdapterState,
    decision: DDDecision,
)
    requires
        dd1_machine_invariant(before),
        dd_enabled(before, DDAdapterEvent::ServiceDecide { decision }),
    ensures dd1_machine_invariant(dd_apply(
        before, DDAdapterEvent::ServiceDecide { decision },
    )),
{
    let after = dd_apply(
        before, DDAdapterEvent::ServiceDecide { decision },
    );
    reveal(dd_enabled);
    assert(dd_enabled(
        before, DDAdapterEvent::ServiceDecide { decision },
    ));
    let attempt = before.active.unwrap();
    let record = DDDecisionRecord {
        attempt,
        decision,
        history_cut: before.history.len(),
    };
    assert(before.decisions.len() == 0);
    assert(after.decisions =~= before.decisions.push(record));
    assert(after.decisions.len() == 1);
    assert(after.decisions[0] == record);
    assert(invoked(before.history, before.request, attempt));
    dd1_invoked_attempt_is_positive(
        before.history, before.request, attempt,
    );
    assert forall|index: int| 0 <= index < after.decisions.len()
        implies #[trigger] after.decisions[index].attempt > 0 by {
        assert(index == 0);
        assert(after.decisions[index] == record);
    }
    assert(dd_decisions_well_formed(after.decisions));
    assert(before.history.take(before.history.len() as int)
        =~= before.history);
    assert forall|index: int| 0 <= index < after.decisions.len()
        implies {
            let current = #[trigger] after.decisions[index];
            &&& current.history_cut <= after.history.len()
            &&& invoked(
                after.history.take(current.history_cut as int),
                after.request, current.attempt,
            )
            &&& p1_layer::delivery_count(
                after.history.take(current.history_cut as int),
                after.request, current.attempt,
            ) == 0
        } by {
        assert(index == 0);
        assert(after.history == before.history);
        assert(after.request == before.request);
    }
    assert(dd_decisions_have_history_provenance(
        after.history, after.request, after.decisions,
    ));
    assert forall|index: int| 0 <= index < after.decisions.len()
        implies match #[trigger] after.decisions[index].decision {
            DDDecision::Applied { value } => value.id == 1,
            DDDecision::Rejected => true,
        } by {
        assert(index == 0);
        match decision {
            DDDecision::Applied { value } => {},
            DDDecision::Rejected => {},
        }
    }
    assert(dd1_decision_values_allowed(after.decisions));
    match decision {
        DDDecision::Applied { value } => {
            assert(dd_has_applied(after.decisions, value)) by {
                reveal(dd_has_applied);
                let index: int = 0;
                assert(0 <= index < after.decisions.len());
                assert(after.decisions[index] == record);
                assert(record.decision == DDDecision::Applied { value });
            }
            assert(dd_has_any_applied(after.decisions)) by {
                let index: int = 0;
            }
            assert(after.slot == Option::Some(value));
            assert(dd_post_state_factored(dd_external_run(after))) by {
                let selected = value;
            }
        },
        DDDecision::Rejected => {
            assert(!dd_has_any_applied(after.decisions)) by {
                if dd_has_any_applied(after.decisions) {
                    let index = choose|index: int|
                        0 <= index < after.decisions.len()
                            && after.decisions[index].decision is Applied;
                    assert(index == 0);
                    assert(false);
                }
            }
            assert(!dd_has_any_applied(before.decisions));
            assert(before.slot == before.initial_slot);
            assert(after.slot == before.slot);
            assert(dd_post_state_factored(dd_external_run(after)));
        },
    }
    assert(after.history == before.history);
    assert(after.globals == before.globals);
    assert(dd1_history_classified(after)) by {
        assert(after.decisions.len() == 1);
        assert forall|index: int| 0 <= index < after.history.len()
            implies match #[trigger] after.history[index] {
                p0_layer::PhysicalEvent::Invoke { .. } => true,
                p0_layer::PhysicalEvent::Delivered { observation, .. } => {
                    dd1_observation_matches_decision(
                        after.decisions, observation,
                    )
                },
            } by {
            match before.history[index] {
                p0_layer::PhysicalEvent::Invoke { .. } => {},
                p0_layer::PhysicalEvent::Delivered {
                    observation: replay_layer::Observation::Success(value), ..
                } => {
                    assert(dd_has_applied(before.decisions, value));
                    assert(false);
                },
                p0_layer::PhysicalEvent::Delivered {
                    observation: replay_layer::Observation::Failure, ..
                } => {
                    assert(dd_has_rejected(before.decisions));
                    assert(false);
                },
                p0_layer::PhysicalEvent::Delivered { .. } => {
                    assert(false);
                },
            }
        }
    }
}

proof fn dd1_observe_preserves_invariant(
    before: DDAdapterState,
    event: global_layer::GlobalEvent,
)
    requires
        dd1_machine_invariant(before),
        dd_observe_enabled(before, event),
    ensures dd1_machine_invariant(dd_apply_observe(before, event)),
{
    let after = dd_apply_observe(before, event);
    let request = before.request;
    let cfg = dd_full_config();
    a1_pi_adapter_push(before.globals, event, request);
    match event {
        global_layer::GlobalEvent::InvokeEvent {
            request: event_request,
            attempt,
            call,
            journal_cut,
            ack_cut,
        } if event_request == request => {
            let physical = p0_layer::PhysicalEvent::Invoke {
                request: event_request,
                attempt,
                call,
                journal_cut,
                ack_cut,
            };
            assert(after.history == before.history.push(physical));
            dd1_append_history_shape(before, physical);
            dd1_decisions_history_push(
                before.history, physical, request, before.decisions,
            );
            dd1_history_classified_push(
                before.history, before.decisions, physical,
            );
            p1_layer::unique_push_invoke(
                before.history, physical, request, attempt,
            );
            p1_layer::ordered_push_invoke(before.history, physical);
            p1_layer::invoke_count_push(
                before.history, physical, request, attempt,
            );
            p1_layer::delivery_count_push(
                before.history, physical, request, attempt,
            );
            assert(after.decisions == before.decisions);
            assert(after.slot == before.slot);
            assert(after.initial_slot == before.initial_slot);
            assert(after.history
                == projection_layer::pi_adapter(after.globals, request));
            assert(dd_decisions_have_history_provenance(
                after.history, request, after.decisions,
            ));
            assert(dd1_history_classified(after));
            assert(dd_post_state_factored(dd_external_run(after)));
            assert(after.active == Option::Some(attempt));
            assert(p1_layer::invoke_count(
                after.history, request, attempt,
            ) == 1);
            assert(p1_layer::delivery_count(
                after.history, request, attempt,
            ) == 0);
        },
        global_layer::GlobalEvent::DeliverEvent {
            request: event_request,
            attempt,
            observation,
            journal_cut,
        } if event_request == request => {
            let physical = p0_layer::PhysicalEvent::Delivered {
                request: event_request,
                attempt,
                observation,
                journal_cut,
            };
            assert(after.history == before.history.push(physical));
            dd1_append_history_shape(before, physical);
            dd1_decisions_history_push(
                before.history, physical, request, before.decisions,
            );
            assert(dd1_observation_matches_decision(
                before.decisions, observation,
            ));
            dd1_history_classified_push(
                before.history, before.decisions, physical,
            );
            p1_layer::unique_push_delivery(
                before.history, physical, request, attempt,
            );
            p1_layer::ordered_push_delivery(
                before.history, physical, request, attempt,
            );
            p1_layer::invoke_count_push(
                before.history, physical, request, attempt,
            );
            p1_layer::delivery_count_push(
                before.history, physical, request, attempt,
            );
            assert(after.decisions == before.decisions);
            assert(after.slot == before.slot);
            assert(after.initial_slot == before.initial_slot);
            assert(after.history
                == projection_layer::pi_adapter(after.globals, request));
            assert(dd_decisions_have_history_provenance(
                after.history, request, after.decisions,
            ));
            assert(dd1_history_classified(after));
            assert(dd_post_state_factored(dd_external_run(after)));
            assert(after.active == Option::None);
        },
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
        | global_layer::GlobalEvent::FinishRecover => {
            assert(after.history == before.history);
            assert(after.decisions == before.decisions);
            assert(after.slot == before.slot);
            assert(after.initial_slot == before.initial_slot);
            assert(after.history
                == projection_layer::pi_adapter(after.globals, request));
            assert(dd1_history_classified(after));
            assert(dd_decisions_have_history_provenance(
                after.history, request, after.decisions,
            ));
            assert(dd_post_state_factored(dd_external_run(after)));
            match after.active {
                Option::None => {},
                Option::Some(active) => {
                    assert(before.active == Option::Some(active));
                    assert(p1_layer::invoke_count(
                        after.history, request, active,
                    ) == 1);
                    assert(p1_layer::delivery_count(
                        after.history, request, active,
                    ) == 0);
                },
            }
        },
    }
}

pub proof fn dd1_step_preserves_invariant(
    request: replay_layer::RequestId,
    initial_slot: Option<replay_layer::Value>,
    before: DDAdapterState,
    event: DDAdapterEvent,
)
    requires
        dd1_execution_invariant(request, initial_slot, before),
        dd_enabled(before, event),
    ensures dd1_execution_invariant(
        request, initial_slot, dd_apply(before, event),
    ),
{
    match event {
        DDAdapterEvent::Observe { event } => {
            dd1_observe_preserves_invariant(before, event);
        },
        DDAdapterEvent::ServiceDecide { decision } => {
            dd1_service_decide_preserves_invariant(before, decision);
        },
    }
}

pub proof fn dd1_exec_prefix(
    request: replay_layer::RequestId,
    initial_slot: Option<replay_layer::Value>,
    execution: DDAdapterExecution,
    length: nat,
)
    requires
        dd_exec(request, initial_slot, execution),
        length <= execution.events.len(),
    ensures dd_exec(
        request,
        initial_slot,
        dd_execution_prefix(execution, length),
    ),
{
    let prefix = dd_execution_prefix(execution, length);
    assert(prefix.events.len() == length);
    assert(prefix.configs.len() == length + 1);
    assert(prefix.configs[0] == execution.configs[0]);
    assert forall|index: nat| index < prefix.events.len() implies
        #[trigger] dd_step(
            prefix.configs[index as int],
            prefix.events[index as int],
            prefix.configs[(index + 1) as int],
        ) by {
        assert(index < execution.events.len());
        assert(prefix.events[index as int]
            == execution.events[index as int]);
        assert(prefix.configs[index as int]
            == execution.configs[index as int]);
        assert(prefix.configs[(index + 1) as int]
            == execution.configs[(index + 1) as int]);
    }
}

pub proof fn dd1_every_exec_configuration_satisfies_invariant(
    request: replay_layer::RequestId,
    initial_slot: Option<replay_layer::Value>,
    execution: DDAdapterExecution,
)
    requires dd_exec(request, initial_slot, execution),
    ensures forall|index: nat| index < execution.configs.len() ==>
        #[trigger] dd1_execution_invariant(
            request,
            initial_slot,
            execution.configs[index as int],
        ),
    decreases execution.events.len(),
{
    if execution.events.len() == 0 {
        dd1_initial_state_satisfies_invariant(request, initial_slot);
    } else {
        let last_index: nat = (execution.events.len() - 1) as nat;
        let prefix = dd_execution_prefix(execution, last_index);
        dd1_exec_prefix(request, initial_slot, execution, last_index);
        dd1_every_exec_configuration_satisfies_invariant(
            request, initial_slot, prefix,
        );
        assert(prefix.configs.len() == execution.events.len());
        assert forall|index: nat| index < execution.events.len() implies
            #[trigger] dd1_execution_invariant(
                request,
                initial_slot,
                execution.configs[index as int],
            ) by {
            assert(index < prefix.configs.len());
            assert(prefix.configs[index as int]
                == execution.configs[index as int]);
        }
        let before = execution.configs[last_index as int];
        let event = execution.events[last_index as int];
        let after = execution.configs[(last_index + 1) as int];
        assert(dd1_execution_invariant(request, initial_slot, before));
        assert(dd_step(before, event, after));
        dd1_step_preserves_invariant(
            request, initial_slot, before, event,
        );
        assert(after == dd_apply(before, event));
        assert forall|index: nat| index < execution.configs.len() implies
            #[trigger] dd1_execution_invariant(
                request,
                initial_slot,
                execution.configs[index as int],
            ) by {
            if index < execution.events.len() {
                assert(index < prefix.configs.len());
            } else {
                assert(index == execution.events.len());
                assert(index == last_index + 1);
            }
        }
    }
}

proof fn dd1_global_trace_push(
    events: Seq<DDAdapterEvent>,
    event: DDAdapterEvent,
)
    ensures dd_global_trace(events.push(event)) == match event {
        DDAdapterEvent::Observe { event: global } => {
            dd_global_trace(events).push(global)
        },
        DDAdapterEvent::ServiceDecide { .. } => dd_global_trace(events),
    },
{
    assert(events.push(event).drop_last() =~= events);
    assert(events.push(event).last() == event);
}

pub proof fn dd1_exec_final_globals_are_projected(
    request: replay_layer::RequestId,
    initial_slot: Option<replay_layer::Value>,
    execution: DDAdapterExecution,
)
    requires dd_exec(request, initial_slot, execution),
    ensures execution.configs[execution.events.len() as int].globals
        == dd_global_trace(execution.events),
    decreases execution.events.len(),
{
    if execution.events.len() == 0 {
        assert(execution.configs[0]
            == dd_initial_state(request, initial_slot));
    } else {
        let last_index: nat = (execution.events.len() - 1) as nat;
        let prefix = dd_execution_prefix(execution, last_index);
        dd1_exec_prefix(request, initial_slot, execution, last_index);
        dd1_exec_final_globals_are_projected(
            request, initial_slot, prefix,
        );
        assert(prefix.events =~= execution.events.drop_last());
        assert(prefix.configs.len() == execution.events.len());
        let before = execution.configs[last_index as int];
        let event = execution.events[last_index as int];
        let after = execution.configs[(last_index + 1) as int];
        assert(dd_step(before, event, after));
        assert(after == dd_apply(before, event));
        dd1_global_trace_push(prefix.events, event);
        assert(execution.events =~= prefix.events.push(event));
        match event {
            DDAdapterEvent::Observe { event: global } => {
                assert(after.globals == before.globals.push(global));
            },
            DDAdapterEvent::ServiceDecide { .. } => {
                assert(after.globals == before.globals);
            },
        }
    }
}

pub proof fn dd1_invariant_implies_dedup_consistency(
    state: DDAdapterState,
)
    requires dd1_machine_invariant(state),
    ensures deduplicated_observations_consistent(
        state.history, state.request,
    ),
{
    assert forall|left: int, right: int|
        0 <= left < state.history.len()
            && 0 <= right < state.history.len()
        implies {
            match (
                #[trigger] state.history[left],
                #[trigger] state.history[right],
            ) {
                (
                    p0_layer::PhysicalEvent::Delivered {
                        request: left_request,
                        observation: left_observation,
                        ..
                    },
                    p0_layer::PhysicalEvent::Delivered {
                        request: right_request,
                        observation: right_observation,
                        ..
                    },
                ) if left_request == state.request
                    && right_request == state.request => {
                    observations_dedup_compatible(
                        left_observation, right_observation,
                    )
                },
                _ => true,
            }
        } by {
        match (state.history[left], state.history[right]) {
            (
                p0_layer::PhysicalEvent::Delivered {
                    observation: replay_layer::Observation::Success(left_value),
                    ..
                },
                p0_layer::PhysicalEvent::Delivered {
                    observation: replay_layer::Observation::Success(right_value),
                    ..
                },
            ) => {
                assert(dd_has_applied(state.decisions, left_value));
                assert(dd_has_applied(state.decisions, right_value));
                dd1_applied_values_equal(
                    state.decisions, left_value, right_value,
                );
            },
            (
                p0_layer::PhysicalEvent::Delivered {
                    observation: replay_layer::Observation::Success(value), ..
                },
                p0_layer::PhysicalEvent::Delivered {
                    observation: replay_layer::Observation::Failure, ..
                },
            ) => {
                assert(dd_has_applied(state.decisions, value));
                assert(dd_has_rejected(state.decisions));
                dd1_applied_excludes_rejected(state.decisions, value);
                assert(false);
            },
            (
                p0_layer::PhysicalEvent::Delivered {
                    observation: replay_layer::Observation::Failure, ..
                },
                p0_layer::PhysicalEvent::Delivered {
                    observation: replay_layer::Observation::Success(value), ..
                },
            ) => {
                assert(dd_has_rejected(state.decisions));
                assert(dd_has_applied(state.decisions, value));
                dd1_applied_excludes_rejected(state.decisions, value);
                assert(false);
            },
            (
                p0_layer::PhysicalEvent::Delivered {
                    observation: replay_layer::Observation::Ambiguous, ..
                },
                _,
            )
            | (
                p0_layer::PhysicalEvent::Delivered {
                    observation: replay_layer::Observation::InvalidResult(_), ..
                },
                _,
            )
            | (
                _,
                p0_layer::PhysicalEvent::Delivered {
                    observation: replay_layer::Observation::Ambiguous, ..
                },
            )
            | (
                _,
                p0_layer::PhysicalEvent::Delivered {
                    observation: replay_layer::Observation::InvalidResult(_), ..
                },
            ) => {
                assert(false);
            },
            _ => {},
        }
    }
}

pub proof fn dd1_invariant_implies_adapter_rely_trace(
    state: DDAdapterState,
)
    requires dd1_machine_invariant(state),
    ensures adapter_rely_trace(
        dd_paper(),
        state.request,
        state.history,
        dd_external_run(state),
    ),
{
    let cfg = dd_full_config();
    let paper = dd_paper();
    let run = dd_external_run(state);
    t1_layer::paper_broker_config_is_broker(paper);
    assert(t1_layer::paper_broker_config(paper) == cfg);
    assert(dd_env_rely(state.request, state.history, run));
    assert(delivered_observations_classified(
        cfg, dd_adapter(), state.history, state.request, run,
    )) by {
        assert forall|index: int| 0 <= index < state.history.len()
            implies match #[trigger] state.history[index] {
                p0_layer::PhysicalEvent::Invoke { .. } => true,
                p0_layer::PhysicalEvent::Delivered {
                    attempt, observation, ..
                } => {
                    &&& dd_classification_ok(
                        state.request, attempt, observation, run,
                    )
                    &&& match observation {
                        replay_layer::Observation::Success(value) => {
                            cfg.valid_results.contains((state.request, value))
                        },
                        _ => true,
                    }
                },
            } by {
            match state.history[index] {
                p0_layer::PhysicalEvent::Invoke { .. } => {},
                p0_layer::PhysicalEvent::Delivered {
                    observation: replay_layer::Observation::Success(value), ..
                } => {
                    assert(dd_has_applied(state.decisions, value));
                    dd1_applied_value_is_allowed(state.decisions, value);
                    assert(cfg.valid_results.contains((state.request, value)));
                },
                p0_layer::PhysicalEvent::Delivered {
                    observation: replay_layer::Observation::Failure, ..
                } => {
                    assert(dd_has_rejected(state.decisions));
                },
                p0_layer::PhysicalEvent::Delivered { .. } => {
                    assert(false);
                },
            }
        }
    }
    assert(dd_service_law(
        state.request,
        cfg.request[state.request].adapter_namespace,
        cfg.request[state.request].stable_key.unwrap(),
        state.history,
        run,
    )) by {
        assert forall|index: int| 0 <= index < state.history.len()
            implies match #[trigger] state.history[index] {
                p0_layer::PhysicalEvent::Delivered {
                    request: event_request, observation, ..
                } if event_request == state.request => match observation {
                    replay_layer::Observation::Success(value) => {
                        dd_has_applied(state.decisions, value)
                    },
                    replay_layer::Observation::Failure => {
                        dd_has_rejected(state.decisions)
                    },
                    _ => false,
                },
                _ => true,
            } by {
        }
    }
    assert(cfg.request[state.request].retry_class
        == replay_layer::RetryClass::Deduplicated);
    assert(cfg.request[state.request].stable_key
        == Option::Some(replay_layer::StableKey { id: state.request.id }));
    assert(adapter_class_law(
        cfg, dd_adapter(), state.history, state.request, run,
    ));
    dd1_invariant_implies_dedup_consistency(state);
}

pub proof fn dd1_exec_derives_adapter_rely(
    request: replay_layer::RequestId,
    initial_slot: Option<replay_layer::Value>,
    execution: DDAdapterExecution,
)
    requires dd_exec(request, initial_slot, execution),
    ensures
        adapter_rely(
            dd_paper(),
            dd_global_trace(execution.events),
            request,
            dd_external_run(
                execution.configs[execution.events.len() as int],
            ),
        ),
        dd1_execution_invariant(
            request,
            initial_slot,
            execution.configs[execution.events.len() as int],
        ),
{
    dd1_every_exec_configuration_satisfies_invariant(
        request, initial_slot, execution,
    );
    let final_state = execution.configs[execution.events.len() as int];
    assert(dd1_execution_invariant(request, initial_slot, final_state));
    dd1_invariant_implies_adapter_rely_trace(final_state);
    dd1_exec_final_globals_are_projected(
        request, initial_slot, execution,
    );
    assert(final_state.request == request);
    assert(final_state.globals == dd_global_trace(execution.events));
    adapter_rely_is_projected_rely(
        dd_paper(),
        dd_global_trace(execution.events),
        request,
        dd_external_run(final_state),
    );
}

} // verus!
