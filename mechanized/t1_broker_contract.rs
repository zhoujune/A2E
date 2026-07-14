use vstd::prelude::*;

#[path = "t1_broker_terminal_provenance.rs"]
pub mod p3_layer;

verus! {

use p3_layer::p2_layer;
use p2_layer::p1_layer;
use p1_layer::p0_layer;
use p0_layer::config_layer;
use config_layer::broker_layer as record_layer;
use record_layer::query_layer;
use record_layer::query_layer::c1_layer::replay_layer;

// B2-L packages the local Broker safety contract proved by B2-R through
// B2-P3.  It introduces no new state, transition guard, or event alphabet.
// In particular, this is not yet the global Event/Exec lifting required by T1.

pub open spec fn auth_log_capability_count(
    log: Seq<replay_layer::AuthEntry>,
    capability: replay_layer::CapabilityId,
) -> nat
    decreases log.len()
{
    if log.len() == 0 {
        0
    } else {
        auth_log_capability_count(log.drop_last(), capability)
            + if log.last().capability == capability { 1nat } else { 0nat }
    }
}

pub open spec fn rich_scope_confinement(
    cfg: config_layer::FullConfig,
    state: p0_layer::State,
) -> bool {
    let erased = config_layer::erase_config(cfg);
    let records = state.core.evidence.records;
    let durable = state.core.broker.durable;
    forall|request: replay_layer::RequestId| #![auto]
        !config_layer::matches(cfg, request, cfg.request[request].capability)
            ==> {
                &&& durable.phase[request] == replay_layer::Phase::New
                &&& replay_layer::authorize_count_for_request(records, request) == 0
                &&& replay_layer::started_count(records, request) == 0
                &&& replay_layer::terminal_count(records, request) == 0
                &&& p2_layer::request_invoke_count(
                    state.physical.physical, request,
                ) == 0
                &&& replay_layer::commit_log_request_count(
                    durable.commit_log, request,
                ) == 0
                &&& state.physical.commit_source[request].is_none()
            }
}

pub open spec fn replay_agreement_clause(
    cfg: config_layer::FullConfig,
    state: p0_layer::State,
) -> bool {
    let erased = config_layer::erase_config(cfg);
    state.core.broker.durable
            == replay_layer::replay(erased, state.core.evidence.records)
        && replay_layer::journal_legal(erased, state.core.evidence.records)
}

pub open spec fn budget_conservation_clause(
    cfg: config_layer::FullConfig,
    state: p0_layer::State,
) -> bool {
    let erased = config_layer::erase_config(cfg);
    let durable = state.core.broker.durable;
    forall|capability: replay_layer::CapabilityId|
        #[trigger] durable.remaining[capability]
            + auth_log_capability_count(durable.auth_log, capability)
            == erased.initial_budget[capability]
}

pub open spec fn authorization_soundness_clause(
    cfg: config_layer::FullConfig,
    state: p0_layer::State,
) -> bool {
    let erased = config_layer::erase_config(cfg);
    let records = state.core.evidence.records;
    replay_layer::replay_authorization_ok(erased, records)
        && replay_layer::authorization_phase_count_ok(erased, records)
        && replay_layer::authorization_prefix_valid(erased, records)
}

pub open spec fn attempt_shape_clause(
    cfg: config_layer::FullConfig,
    state: p0_layer::State,
) -> bool {
    replay_layer::replay_attempt_shape_ok(
        config_layer::erase_config(cfg), state.core.evidence.records,
    )
        && outcome_references_strictly_prior_start(
            state.core.evidence.records,
        )
}

pub open spec fn outcome_references_strictly_prior_start(
    records: Seq<replay_layer::JournalRecord>,
) -> bool {
    forall|index: int| 0 <= index < records.len() ==> {
        let prefix = records.take(index);
        match #[trigger] records[index] {
            replay_layer::JournalRecord::Outcome {
                request, attempt, start_ref, ..
            } => {
                replay_layer::start_at(
                    prefix, start_ref, request, attempt,
                )
                    && 1 <= start_ref
                    && start_ref <= prefix.len()
            },
            _ => true,
        }
    }
}

pub open spec fn physical_causality_clause(
    cfg: config_layer::FullConfig,
    state: p0_layer::State,
) -> bool {
    let records = state.core.evidence.records;
    let history = state.physical.physical;
    p1_layer::physical_unique(history)
        && p1_layer::physical_ordered(history)
        && p1_layer::physical_cuts_valid(
            cfg, records, state.core.evidence.ack_cuts, history,
        )
        && p2_layer::acknowledged_invocation_refinement(cfg, records, history)
        && p2_layer::durable_outcomes_follow_deliveries(records, history)
        && delivered_outcome_order(records, history)
}

pub open spec fn delivered_outcome_order(
    records: Seq<replay_layer::JournalRecord>,
    history: Seq<p0_layer::PhysicalEvent>,
) -> bool {
    forall|index: nat| index < history.len() ==> match #[trigger] history[index as int] {
        p0_layer::PhysicalEvent::Delivered {
            request, attempt, observation, journal_cut,
        } => match replay_layer::outcome_lsn(records, request, attempt) {
            Option::None => true,
            Option::Some(lsn) => {
                replay_layer::outcome_observation(records, request, attempt)
                        == Option::Some(observation)
                    && journal_cut < lsn
            },
        },
        p0_layer::PhysicalEvent::Invoke { .. } => true,
    }
}

pub open spec fn retry_discipline_clause(
    cfg: config_layer::FullConfig,
    state: p0_layer::State,
) -> bool {
    let erased = config_layer::erase_config(cfg);
    let records = state.core.evidence.records;
    replay_layer::start_prefix_discipline_ok(erased, records)
        && replay_layer::uncontrolled_single_attempt(erased, records)
        && p2_layer::aggregate_retry_bounds(cfg, state)
}

pub open spec fn exact_delivery_exists(
    history: Seq<p0_layer::PhysicalEvent>,
    request: replay_layer::RequestId,
    attempt: replay_layer::AttemptId,
    observation: replay_layer::Observation,
) -> bool {
    exists|index: nat, journal_cut: nat| #![auto] {
        &&& index < history.len()
        &&& history[index as int]
            == (p0_layer::PhysicalEvent::Delivered {
                request, attempt, observation, journal_cut,
            })
    }
}

pub open spec fn slot_case_agreement(
    cfg: config_layer::FullConfig,
    state: p0_layer::State,
) -> bool {
    let erased = config_layer::erase_config(cfg);
    let durable = state.core.broker.durable;
    let records = state.core.evidence.records;
    let history = state.physical.physical;
    match state.core.broker.slot {
        record_layer::ExecSlot::Idle => true,
        record_layer::ExecSlot::Ready { request, attempt } => {
            durable.phase[request] == replay_layer::Phase::Armed
                && query_layer::d_latest(durable, request)
                    == Option::Some(attempt)
                && query_layer::d_outcome(durable, request, attempt).is_none()
                && replay_layer::start_lsn(records, request, attempt).is_some()
                && p1_layer::invoke_count(history, request, attempt) == 0
                && p1_layer::delivery_count(history, request, attempt) == 0
        },
        record_layer::ExecSlot::InFlight { request, attempt } => {
            durable.phase[request] == replay_layer::Phase::Armed
                && query_layer::d_latest(durable, request)
                    == Option::Some(attempt)
                && query_layer::d_outcome(durable, request, attempt).is_none()
                && replay_layer::start_lsn(records, request, attempt).is_some()
                && p1_layer::invoke_count(history, request, attempt) == 1
                && p1_layer::delivery_count(history, request, attempt) == 0
        },
        record_layer::ExecSlot::Received {
            request, attempt, observation,
        } => {
            durable.phase[request] == replay_layer::Phase::Armed
                && query_layer::d_latest(durable, request)
                    == Option::Some(attempt)
                && query_layer::d_outcome(durable, request, attempt).is_none()
                && replay_layer::start_lsn(records, request, attempt).is_some()
                && p1_layer::invoke_count(history, request, attempt) == 1
                && p1_layer::delivery_count(history, request, attempt) == 1
                && exact_delivery_exists(
                    history, request, attempt, observation,
                )
        },
        record_layer::ExecSlot::ObservedSuccess {
            request, attempt, value,
        } => {
            durable.phase[request] == replay_layer::Phase::Armed
                && query_layer::d_latest(durable, request)
                    == Option::Some(attempt)
                && query_layer::d_outcome(durable, request, attempt)
                    == Option::Some(replay_layer::Observation::Success(value))
                && replay_layer::start_lsn(records, request, attempt).is_some()
        },
        record_layer::ExecSlot::ObservedFailure { request, attempt } => {
            durable.phase[request] == replay_layer::Phase::Armed
                && query_layer::d_latest(durable, request)
                    == Option::Some(attempt)
                && query_layer::d_outcome(durable, request, attempt)
                    == Option::Some(replay_layer::Observation::Failure)
                && replay_layer::start_lsn(records, request, attempt).is_some()
        },
        record_layer::ExecSlot::ObservedUnknown {
            request, attempt, reason,
        } => {
            durable.phase[request] == replay_layer::Phase::Armed
                && query_layer::d_latest(durable, request)
                    == Option::Some(attempt)
                && erased.request_class[request]
                    == replay_layer::RetryClass::Uncontrolled
                && replay_layer::start_lsn(records, request, attempt).is_some()
                && match reason {
                    replay_layer::UnknownReason::AmbiguousOutcome => {
                        query_layer::d_outcome(durable, request, attempt)
                            == Option::Some(
                                replay_layer::Observation::Ambiguous,
                            )
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

pub open spec fn slot_agreement_clause(
    cfg: config_layer::FullConfig,
    state: p0_layer::State,
) -> bool {
    slot_case_agreement(cfg, state)
}

pub open spec fn terminal_uniqueness_clause(
    cfg: config_layer::FullConfig,
    state: p0_layer::State,
) -> bool {
    let erased = config_layer::erase_config(cfg);
    let records = state.core.evidence.records;
    replay_layer::replay_phase_unique_ok(erased, records)
        && replay_layer::replay_terminal_fields_ok(erased, records)
        && replay_layer::replay_commit_unique_ok(records)
        && replay_layer::replay_commit_log_unique_ok(erased, records)
}

pub open spec fn value_provenance_clause(
    cfg: config_layer::FullConfig,
    state: p0_layer::State,
) -> bool {
    state.physical.commit_source.dom()
            == ISet::<replay_layer::RequestId>::full()
        && replay_layer::replay_terminal_provenance_ok(
        config_layer::erase_config(cfg), state.core.evidence.records,
    )
        && p3_layer::commit_source_agreement(cfg, state)
}

pub open spec fn failure_provenance_clause(
    cfg: config_layer::FullConfig,
    state: p0_layer::State,
) -> bool {
    p3_layer::failed_physical_provenance(cfg, state)
}

pub open spec fn crash_shape_clause(state: p0_layer::State) -> bool {
    (state.core.broker.mode != record_layer::Mode::Online
        ==> state.core.broker.slot == record_layer::ExecSlot::Idle
            && state.physical.slot_source.is_none())
        && (state.core.broker.mode == record_layer::Mode::Crashed
            ==> state.core.broker.append is Idle)
}

pub open spec fn append_interface_shape_clause(
    cfg: config_layer::FullConfig,
    state: p0_layer::State,
) -> bool {
    let erased = config_layer::erase_config(cfg);
    record_layer::called_shape(erased, state.core)
        && record_layer::linearized_shape(erased, state.core)
        && record_layer::ready_release_agreement(state.core)
}

// The conjunction follows the numbering of BrokerInvariant clauses 1--13 in
// formal/mechanization-contract.md.  It is intentionally independent of the
// stronger inductive P3 predicate; local_inductive_invariant packages both.
pub open spec fn broker_contract_invariant(
    cfg: config_layer::FullConfig,
    state: p0_layer::State,
) -> bool {
    replay_agreement_clause(cfg, state)                        // 1
        && budget_conservation_clause(cfg, state)              // 2
        && authorization_soundness_clause(cfg, state)          // 3
        && rich_scope_confinement(cfg, state)                  // 4
        && attempt_shape_clause(cfg, state)                    // 5
        && physical_causality_clause(cfg, state)               // 6
        && retry_discipline_clause(cfg, state)                 // 7
        && slot_agreement_clause(cfg, state)                   // 8
        && terminal_uniqueness_clause(cfg, state)              // 9
        && value_provenance_clause(cfg, state)                 // 10
        && failure_provenance_clause(cfg, state)               // 11
        && crash_shape_clause(state)                           // 12
        && append_interface_shape_clause(cfg, state)           // 13
}

pub open spec fn local_inductive_invariant(
    cfg: config_layer::FullConfig,
    state: p0_layer::State,
) -> bool {
    p3_layer::p3_invariant(cfg, state)
        && broker_contract_invariant(cfg, state)
}

pub proof fn auth_log_capability_count_push(
    log: Seq<replay_layer::AuthEntry>,
    entry: replay_layer::AuthEntry,
    capability: replay_layer::CapabilityId,
)
    ensures auth_log_capability_count(log.push(entry), capability)
        == auth_log_capability_count(log, capability)
            + if entry.capability == capability { 1nat } else { 0nat },
{
    assert(log.push(entry).drop_last() =~= log);
    assert(log.push(entry).last() == entry);
}

pub proof fn auth_projection_capability_count(
    records: Seq<replay_layer::JournalRecord>,
    capability: replay_layer::CapabilityId,
)
    ensures auth_log_capability_count(
        replay_layer::auth_projection(records), capability,
    ) == replay_layer::authorize_count_for_cap(records, capability),
    decreases records.len(),
{
    if records.len() > 0 {
        let prefix = records.drop_last();
        let record = records.last();
        auth_projection_capability_count(prefix, capability);
        match record {
            replay_layer::JournalRecord::Authorize {
                request, capability: record_capability, ..
            } => {
                auth_log_capability_count_push(
                    replay_layer::auth_projection(prefix),
                    replay_layer::AuthEntry {
                        request,
                        capability: record_capability,
                    },
                    capability,
                );
            },
            _ => {},
        }
    }
}

pub proof fn replay_budget_implies_exact_auth_log_budget(
    cfg: config_layer::FullConfig,
    state: p0_layer::State,
)
    requires
        state.core.broker.durable
            == replay_layer::replay(
                config_layer::erase_config(cfg),
                state.core.evidence.records,
            ),
        replay_layer::replay_budget_ok(
            config_layer::erase_config(cfg),
            state.core.evidence.records,
        ),
        replay_layer::replay_authorization_ok(
            config_layer::erase_config(cfg),
            state.core.evidence.records,
        ),
    ensures budget_conservation_clause(cfg, state),
{
    let records = state.core.evidence.records;
    let durable = state.core.broker.durable;
    assert(durable.auth_log == replay_layer::auth_projection(records));
    assert forall|capability: replay_layer::CapabilityId|
        #[trigger] durable.remaining[capability]
            + auth_log_capability_count(durable.auth_log, capability)
            == config_layer::erase_config(cfg).initial_budget[capability] by {
        auth_projection_capability_count(records, capability);
    }
}

pub proof fn start_lsn_is_start_at(
    records: Seq<replay_layer::JournalRecord>,
    request: replay_layer::RequestId,
    attempt: replay_layer::AttemptId,
    lsn: replay_layer::Lsn,
)
    requires replay_layer::start_lsn(records, request, attempt)
        == Option::Some(lsn),
    ensures replay_layer::start_at(records, lsn, request, attempt),
    decreases records.len(),
{
    let prefix = records.drop_last();
    match records.last() {
        replay_layer::JournalRecord::Start {
            request: r, attempt: a, ..
        } => {
            if r == request && a == attempt {
                assert(lsn == records.len());
                assert(records[(lsn - 1) as int] == records.last());
            } else {
                start_lsn_is_start_at(
                    prefix, request, attempt, lsn,
                );
                assert(prefix[(lsn - 1) as int]
                    == records[(lsn - 1) as int]);
            }
        },
        _ => {
            start_lsn_is_start_at(prefix, request, attempt, lsn);
            assert(prefix[(lsn - 1) as int]
                == records[(lsn - 1) as int]);
        },
    }
}

pub proof fn journal_legal_implies_outcome_start_references(
    erased: replay_layer::Config,
    records: Seq<replay_layer::JournalRecord>,
)
    requires replay_layer::journal_legal(erased, records),
    ensures outcome_references_strictly_prior_start(records),
{
    assert forall|index: int| 0 <= index < records.len() implies {
        let prefix = records.take(index);
        match #[trigger] records[index] {
            replay_layer::JournalRecord::Outcome {
                request, attempt, start_ref, ..
            } => {
                replay_layer::start_at(
                    prefix, start_ref, request, attempt,
                )
                    && 1 <= start_ref
                    && start_ref <= prefix.len()
            },
            _ => true,
        }
    } by {
        let prefix = records.take(index);
        let record = records[index];
        assert(replay_layer::structural_enabled(erased, prefix, record));
        match record {
            replay_layer::JournalRecord::Outcome {
                request, attempt, start_ref, ..
            } => {
                assert(replay_layer::ref_is(
                    start_ref,
                    replay_layer::start_lsn(prefix, request, attempt),
                ));
                assert(replay_layer::start_lsn(
                    prefix, request, attempt,
                ) == Option::Some(start_ref));
                start_lsn_is_start_at(
                    prefix, request, attempt, start_ref,
                );
            },
            _ => {},
        }
    }
}

pub proof fn latest_started_attempt_has_start_lsn(
    erased: replay_layer::Config,
    records: Seq<replay_layer::JournalRecord>,
    request: replay_layer::RequestId,
)
    requires
        replay_layer::journal_legal(erased, records),
        replay_layer::started_count(records, request) > 0,
    ensures replay_layer::start_lsn(
        records, request, replay_layer::started_count(records, request),
    ).is_some(),
    decreases records.len(),
{
    let prefix = records.drop_last();
    let record = records.last();
    replay_layer::journal_legal_drop_last(erased, records);
    replay_layer::started_count_push(prefix, request, record);
    match record {
        replay_layer::JournalRecord::Start {
            request: r, attempt, ..
        } => {
            if r == request {
                assert(records.len() > 0);
                assert(records[(records.len() - 1) as int] == record);
                assert(records.take((records.len() - 1) as int) =~= prefix);
                assert(replay_layer::structural_enabled(
                    erased, prefix, record,
                ));
                assert(attempt
                    == replay_layer::started_count(prefix, request) + 1);
                assert(replay_layer::started_count(records, request)
                    == replay_layer::started_count(prefix, request) + 1);
                assert(replay_layer::start_lsn(
                    records,
                    request,
                    replay_layer::started_count(records, request),
                ) == Option::Some(records.len()));
            } else {
                assert(replay_layer::started_count(records, request)
                    == replay_layer::started_count(prefix, request));
                latest_started_attempt_has_start_lsn(
                    erased, prefix, request,
                );
            }
        },
        _ => {
            assert(replay_layer::started_count(records, request)
                == replay_layer::started_count(prefix, request));
            latest_started_attempt_has_start_lsn(
                erased, prefix, request,
            );
        },
    }
}

pub proof fn latest_slot_attempt_has_start(
    erased: replay_layer::Config,
    records: Seq<replay_layer::JournalRecord>,
    request: replay_layer::RequestId,
    attempt: replay_layer::AttemptId,
)
    requires
        replay_layer::journal_legal(erased, records),
        query_layer::d_latest(
            replay_layer::replay(erased, records), request,
        ) == Option::Some(attempt),
    ensures replay_layer::start_lsn(records, request, attempt).is_some(),
{
    query_layer::replay_d_latest_exact(erased, records, request);
    assert(replay_layer::latest_attempt(records, request)
        == Option::Some(attempt));
    assert(replay_layer::started_count(records, request) > 0);
    assert(attempt == replay_layer::started_count(records, request));
    latest_started_attempt_has_start_lsn(erased, records, request);
}

pub proof fn source_delivery_implies_exact_delivery_exists(
    history: Seq<p0_layer::PhysicalEvent>,
    source: Option<p0_layer::PhysicalIndex>,
    request: replay_layer::RequestId,
    attempt: replay_layer::AttemptId,
    observation: replay_layer::Observation,
)
    requires p1_layer::source_is_delivery(
        history, source, request, attempt, observation,
    ),
    ensures exact_delivery_exists(
        history, request, attempt, observation,
    ),
{
    match source {
        Option::Some(index) => {
            assert(index < history.len());
            match history[index as int] {
                p0_layer::PhysicalEvent::Delivered {
                    request: r,
                    attempt: a,
                    observation: o,
                    journal_cut,
                } => {
                    assert(r == request && a == attempt && o == observation);
                    assert(exists|witness_index: nat, witness_cut: nat| #![auto] {
                        &&& witness_index < history.len()
                        &&& history[witness_index as int]
                            == (p0_layer::PhysicalEvent::Delivered {
                                request,
                                attempt,
                                observation,
                                journal_cut: witness_cut,
                            })
                    }) by {
                        assert(history[index as int]
                            == (p0_layer::PhysicalEvent::Delivered {
                                request,
                                attempt,
                                observation,
                                journal_cut,
                            }));
                    }
                },
                p0_layer::PhysicalEvent::Invoke { .. } => {},
            }
        },
        Option::None => {},
    }
}

pub proof fn p3_implies_slot_case_agreement(
    cfg: config_layer::FullConfig,
    state: p0_layer::State,
)
    requires
        config_layer::full_config_wf(cfg),
        p3_layer::p3_invariant(cfg, state),
    ensures slot_case_agreement(cfg, state),
{
    let erased = config_layer::erase_config(cfg);
    let records = state.core.evidence.records;
    config_layer::erasure_is_replay_well_formed(cfg);
    assert(record_layer::b2_record_invariant(erased, state.core));
    assert(replay_layer::r1_replay_invariant(erased, records));
    assert(state.core.broker.durable == replay_layer::replay(erased, records));
    assert(record_layer::durable_slot_agreement(
        erased, state.core.broker.durable, state.core.broker.slot,
    ));
    assert(p1_layer::physical_slot_agreement(state));
    match state.core.broker.slot {
        record_layer::ExecSlot::Idle => {},
        record_layer::ExecSlot::Ready { request, attempt }
        | record_layer::ExecSlot::InFlight { request, attempt } => {
            assert(query_layer::d_latest(
                state.core.broker.durable, request,
            ) == Option::Some(attempt));
            latest_slot_attempt_has_start(
                erased, records, request, attempt,
            );
        },
        record_layer::ExecSlot::Received {
            request, attempt, observation,
        } => {
            assert(query_layer::d_latest(
                state.core.broker.durable, request,
            ) == Option::Some(attempt));
            latest_slot_attempt_has_start(
                erased, records, request, attempt,
            );
            assert(p1_layer::source_is_delivery(
                state.physical.physical,
                state.physical.slot_source,
                request,
                attempt,
                observation,
            ));
            source_delivery_implies_exact_delivery_exists(
                state.physical.physical,
                state.physical.slot_source,
                request,
                attempt,
                observation,
            );
        },
        record_layer::ExecSlot::ObservedSuccess { request, attempt, .. }
        | record_layer::ExecSlot::ObservedFailure { request, attempt }
        | record_layer::ExecSlot::ObservedUnknown { request, attempt, .. } => {
            assert(query_layer::d_latest(
                state.core.broker.durable, request,
            ) == Option::Some(attempt));
            latest_slot_attempt_has_start(
                erased, records, request, attempt,
            );
        },
    }
}

pub proof fn unmatched_request_has_rich_scope_confinement(
    cfg: config_layer::FullConfig,
    state: p0_layer::State,
    request: replay_layer::RequestId,
)
    requires
        config_layer::full_config_wf(cfg),
        p3_layer::p3_invariant(cfg, state),
        !config_layer::matches(
            cfg, request, cfg.request[request].capability,
        ),
    ensures {
        let records = state.core.evidence.records;
        let durable = state.core.broker.durable;
        &&& durable.phase[request] == replay_layer::Phase::New
        &&& replay_layer::authorize_count_for_request(records, request) == 0
        &&& replay_layer::started_count(records, request) == 0
        &&& replay_layer::terminal_count(records, request) == 0
        &&& p2_layer::request_invoke_count(
            state.physical.physical, request,
        ) == 0
        &&& replay_layer::commit_log_request_count(
            durable.commit_log, request,
        ) == 0
        &&& state.physical.commit_source[request].is_none()
    },
{
    let erased = config_layer::erase_config(cfg);
    let records = state.core.evidence.records;
    let durable = state.core.broker.durable;
    let capability = cfg.request[request].capability;
    config_layer::erasure_is_exact(cfg);
    config_layer::erasure_is_replay_well_formed(cfg);
    assert(durable == replay_layer::replay(erased, records));
    assert(replay_layer::r1_replay_invariant(erased, records));
    assert(erased.request_capability[request] == capability);
    assert(!erased.matches.contains((request, capability)));
    assert(durable.phase[request] == replay_layer::Phase::New);
    assert(replay_layer::authorize_count_for_request(records, request) == 0);
    assert(replay_layer::started_count(records, request) == 0);
    assert(replay_layer::terminal_count(records, request) == 0);

    assert(p2_layer::invocation_accounting(state));
    assert(p2_layer::request_invoke_count(
        state.physical.physical, request,
    ) + p2_layer::ready_credit(state.core.broker.slot, request) <= 0);
    assert(p2_layer::request_invoke_count(
        state.physical.physical, request,
    ) == 0);

    replay_layer::commit_count_le_terminal_count(records, request);
    replay_layer::commit_projection_count(records, request);
    assert(replay_layer::commit_count(records, request) == 0);
    assert(durable.commit_log == replay_layer::commit_projection(records));
    assert(replay_layer::commit_log_request_count(
        durable.commit_log, request,
    ) == 0);

    assert(replay_layer::replay_terminal_fields_ok(erased, records));
    assert(durable.committed[request].is_none());
    assert(p3_layer::commit_source_agreement(cfg, state));
    assert(state.physical.commit_source[request].is_none());
}

pub proof fn p3_implies_rich_scope_confinement(
    cfg: config_layer::FullConfig,
    state: p0_layer::State,
)
    requires
        config_layer::full_config_wf(cfg),
        p3_layer::p3_invariant(cfg, state),
    ensures rich_scope_confinement(cfg, state),
{
    let records = state.core.evidence.records;
    let durable = state.core.broker.durable;
    assert forall|request: replay_layer::RequestId| #![auto]
        !config_layer::matches(cfg, request, cfg.request[request].capability)
            implies {
                &&& durable.phase[request] == replay_layer::Phase::New
                &&& replay_layer::authorize_count_for_request(records, request) == 0
                &&& replay_layer::started_count(records, request) == 0
                &&& replay_layer::terminal_count(records, request) == 0
                &&& p2_layer::request_invoke_count(
                    state.physical.physical, request,
                ) == 0
                &&& replay_layer::commit_log_request_count(
                    durable.commit_log, request,
                ) == 0
                &&& state.physical.commit_source[request].is_none()
            } by {
        unmatched_request_has_rich_scope_confinement(cfg, state, request);
    }
}

pub proof fn delivery_at_implies_count_positive(
    history: Seq<p0_layer::PhysicalEvent>,
    request: replay_layer::RequestId,
    attempt: replay_layer::AttemptId,
    index: nat,
)
    requires
        index < history.len(),
        p1_layer::is_delivery_for(
            history[index as int], request, attempt,
        ),
    ensures p1_layer::delivery_count(history, request, attempt) > 0,
    decreases history.len(),
{
    let prefix = history.drop_last();
    if index < prefix.len() {
        assert(prefix[index as int] == history[index as int]);
        delivery_at_implies_count_positive(
            prefix, request, attempt, index,
        );
    } else {
        assert(index == history.len() - 1);
        assert(history[index as int] == history.last());
    }
}

pub proof fn unique_delivery_indices(
    history: Seq<p0_layer::PhysicalEvent>,
    request: replay_layer::RequestId,
    attempt: replay_layer::AttemptId,
    left: nat,
    right: nat,
)
    requires
        p1_layer::physical_unique(history),
        left < history.len(),
        right < history.len(),
        p1_layer::is_delivery_for(
            history[left as int], request, attempt,
        ),
        p1_layer::is_delivery_for(
            history[right as int], request, attempt,
        ),
    ensures left == right,
    decreases history.len(),
{
    let prefix = history.drop_last();
    if left < prefix.len() {
        assert(prefix[left as int] == history[left as int]);
        if right < prefix.len() {
            assert(prefix[right as int] == history[right as int]);
            unique_delivery_indices(
                prefix, request, attempt, left, right,
            );
        } else {
            assert(right == history.len() - 1);
            assert(history[right as int] == history.last());
            assert(p1_layer::is_delivery_for(
                history.last(), request, attempt,
            ));
            assert(p1_layer::delivery_count(prefix, request, attempt) == 0);
            delivery_at_implies_count_positive(
                prefix, request, attempt, left,
            );
        }
    } else {
        assert(left == history.len() - 1);
        assert(history[left as int] == history.last());
        if right < prefix.len() {
            assert(prefix[right as int] == history[right as int]);
            assert(p1_layer::is_delivery_for(
                history.last(), request, attempt,
            ));
            assert(p1_layer::delivery_count(prefix, request, attempt) == 0);
            delivery_at_implies_count_positive(
                prefix, request, attempt, right,
            );
        } else {
            assert(right == history.len() - 1);
        }
    }
}

pub proof fn outcome_lsn_has_observation(
    records: Seq<replay_layer::JournalRecord>,
    request: replay_layer::RequestId,
    attempt: replay_layer::AttemptId,
    lsn: replay_layer::Lsn,
)
    requires replay_layer::outcome_lsn(records, request, attempt)
        == Option::Some(lsn),
    ensures exists|observation: replay_layer::Observation|
        replay_layer::outcome_observation(records, request, attempt)
            == Option::Some(observation),
    decreases records.len(),
{
    let prefix = records.drop_last();
    match records.last() {
        replay_layer::JournalRecord::Outcome {
            request: r, attempt: a, observation, ..
        } => {
            if r == request && a == attempt {
                assert(replay_layer::outcome_observation(
                    records, request, attempt,
                ) == Option::Some(observation));
            } else {
                outcome_lsn_has_observation(
                    prefix, request, attempt, lsn,
                );
            }
        },
        _ => {
            outcome_lsn_has_observation(
                prefix, request, attempt, lsn,
            );
        },
    }
}

pub proof fn p2_implies_delivered_outcome_order(
    cfg: config_layer::FullConfig,
    state: p0_layer::State,
)
    requires p2_layer::p2_invariant(cfg, state),
    ensures delivered_outcome_order(
        state.core.evidence.records, state.physical.physical,
    ),
{
    let records = state.core.evidence.records;
    let history = state.physical.physical;
    assert(p1_layer::physical_unique(history));
    assert(p2_layer::durable_outcomes_follow_deliveries(records, history));
    assert forall|index: nat| index < history.len() implies
        match #[trigger] history[index as int] {
            p0_layer::PhysicalEvent::Delivered {
                request, attempt, observation, journal_cut,
            } => match replay_layer::outcome_lsn(records, request, attempt) {
                Option::None => true,
                Option::Some(lsn) => {
                    replay_layer::outcome_observation(
                        records, request, attempt,
                    ) == Option::Some(observation)
                        && journal_cut < lsn
                },
            },
            p0_layer::PhysicalEvent::Invoke { .. } => true,
        } by {
        match history[index as int] {
            p0_layer::PhysicalEvent::Delivered {
                request, attempt, observation, journal_cut,
            } => {
                match replay_layer::outcome_lsn(
                    records, request, attempt,
                ) {
                    Option::None => {},
                    Option::Some(lsn) => {
                        outcome_lsn_has_observation(
                            records, request, attempt, lsn,
                        );
                        let recorded = choose|recorded: replay_layer::Observation|
                            replay_layer::outcome_observation(
                                records, request, attempt,
                            ) == Option::Some(recorded);
                        p2_layer::outcome_projection_has_delivery(
                            records, history, request, attempt, recorded, lsn,
                        );
                        let witness_index = choose|witness_index: nat|
                            exists|delivery_cut: nat| {
                                &&& witness_index < history.len()
                                &&& #[trigger] history[witness_index as int]
                                    == (p0_layer::PhysicalEvent::Delivered {
                                        request,
                                        attempt,
                                        observation: recorded,
                                        journal_cut: delivery_cut,
                                    })
                                &&& delivery_cut < lsn
                            };
                        let delivery_cut = choose|delivery_cut: nat| {
                            &&& witness_index < history.len()
                            &&& #[trigger] history[witness_index as int]
                                == (p0_layer::PhysicalEvent::Delivered {
                                    request,
                                    attempt,
                                    observation: recorded,
                                    journal_cut: delivery_cut,
                                })
                            &&& delivery_cut < lsn
                        };
                        assert(p1_layer::is_delivery_for(
                            history[index as int], request, attempt,
                        ));
                        assert(p1_layer::is_delivery_for(
                            history[witness_index as int], request, attempt,
                        ));
                        unique_delivery_indices(
                            history, request, attempt, index, witness_index,
                        );
                        assert(history[index as int]
                            == history[witness_index as int]);
                        assert(recorded == observation);
                        assert(delivery_cut == journal_cut);
                    },
                }
            },
            p0_layer::PhysicalEvent::Invoke { .. } => {},
        }
    }
}

pub proof fn p3_implies_broker_contract_invariant(
    cfg: config_layer::FullConfig,
    state: p0_layer::State,
)
    requires
        config_layer::full_config_wf(cfg),
        p3_layer::p3_invariant(cfg, state),
    ensures broker_contract_invariant(cfg, state),
{
    let erased = config_layer::erase_config(cfg);
    let records = state.core.evidence.records;
    assert(p2_layer::p2_invariant(cfg, state));
    assert(p1_layer::p1_invariant(cfg, state));
    assert(p0_layer::p0_invariant(cfg, state));
    assert(record_layer::b2_record_invariant(erased, state.core));
    assert(replay_layer::r1_replay_invariant(erased, records));
    replay_budget_implies_exact_auth_log_budget(cfg, state);
    journal_legal_implies_outcome_start_references(erased, records);
    p2_layer::accounting_implies_aggregate_retry_bounds(cfg, state);
    p2_implies_delivered_outcome_order(cfg, state);
    p3_layer::p2_implies_durable_terminal_provenance(cfg, state);
    p3_layer::p2_implies_failed_physical_provenance(cfg, state);
    p3_implies_slot_case_agreement(cfg, state);
    p3_implies_rich_scope_confinement(cfg, state);
}

pub open spec fn local_contract_checkpoint(
    cfg: config_layer::FullConfig,
    events: Seq<p0_layer::Event>,
) -> bool {
    let state = p0_layer::run(cfg, events);
    p3_layer::p3_checkpoint(cfg, events)
        && broker_contract_invariant(cfg, state)
}

pub proof fn b2_local_broker_contract_safety(
    cfg: config_layer::FullConfig,
    events: Seq<p0_layer::Event>,
)
    requires
        config_layer::full_config_wf(cfg),
        p0_layer::admissibly_executable(cfg, events),
    ensures
        local_contract_checkpoint(cfg, events),
        forall|length: nat| length <= events.len() ==>
            #[trigger] local_contract_checkpoint(
                cfg, events.take(length as int),
            ),
{
    p3_layer::b2_p3_terminal_provenance_safety(cfg, events);
    p3_implies_broker_contract_invariant(
        cfg, p0_layer::run(cfg, events),
    );
    assert forall|length: nat| length <= events.len() implies
        #[trigger] local_contract_checkpoint(
            cfg, events.take(length as int),
        ) by {
        p0_layer::executable_prefix(cfg, events, length);
        p3_layer::b2_p3_terminal_provenance_safety(
            cfg, events.take(length as int),
        );
        p3_implies_broker_contract_invariant(
            cfg, p0_layer::run(cfg, events.take(length as int)),
        );
    }
}

} // verus!
