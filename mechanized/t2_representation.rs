use vstd::prelude::*;

#[path = "t2_event_projection.rs"]
pub mod event_layer;

verus! {

use event_layer::trace_layer;
use trace_layer::runtime_layer;
use runtime_layer::t1_layer;
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

// T2-R is the proof boundary between the independent atomic-Journal runtime
// and the abstract Broker.  ConcreteRuntime remains free of Broker durable
// state: this function is a proof-only abstraction computed from the Journal.
pub open spec fn abstract_broker_state(
    cfg: config_layer::FullConfig,
    concrete: runtime_layer::JournalConfiguration,
) -> p0_layer::State {
    p0_layer::State {
        core: record_layer::State {
            broker: record_layer::BrokerState {
                durable: runtime_layer::replay_view(cfg, concrete),
                slot: concrete.runtime.slot,
                mode: concrete.runtime.mode,
                append: concrete.runtime.append,
            },
            evidence: record_layer::GhostEvidence {
                records: concrete.evidence.records,
                ack_cuts: concrete.evidence.ack_cuts,
                acknowledged_prefix: concrete.evidence.acknowledged_prefix,
            },
        },
        physical: p0_layer::PhysicalEvidence {
            physical: concrete.evidence.physical,
            slot_source: concrete.evidence.slot_source,
            commit_source: concrete.evidence.commit_source,
        },
    }
}

pub open spec fn invoke_names_acknowledged_start(
    evidence: runtime_layer::GhostEvidence,
    event: p0_layer::PhysicalEvent,
) -> bool {
    match event {
        p0_layer::PhysicalEvent::Invoke {
            request, attempt, ack_cut, ..
        } => {
            p1_layer::nat_occurs(evidence.ack_cuts, ack_cut)
                && match replay_layer::start_lsn(
                    evidence.records.take(ack_cut as int), request, attempt,
                ) {
                    Option::None => false,
                    Option::Some(start) => 1 <= start && start <= ack_cut,
                }
        },
        p0_layer::PhysicalEvent::Delivered { .. } => true,
    }
}

// Named bridge for T3: the operational full-history guard is exactly strong
// enough to place the same Start witness in the prefix named by the cut.
pub proof fn start_covered_by_cut_implies_prefix_start(
    records: Seq<replay_layer::JournalRecord>,
    request: replay_layer::RequestId,
    attempt: replay_layer::AttemptId,
    cut: nat,
)
    requires
        runtime_layer::start_covered_by_cut(
            records, request, attempt, cut,
        ),
        cut <= records.len(),
    ensures exists|start: replay_layer::Lsn| {
        &&& replay_layer::start_lsn(records, request, attempt)
            == Option::Some(start)
        &&& 1 <= start && start <= cut
        &&& replay_layer::start_lsn(
            records.take(cut as int), request, attempt,
        ) == Option::Some(start)
    },
{
    match replay_layer::start_lsn(records, request, attempt) {
        Option::None => {},
        Option::Some(start) => {
            p1_layer::start_lsn_take_cover(
                records, request, attempt, cut, start,
            );
            assert(exists|witness: replay_layer::Lsn| {
                &&& replay_layer::start_lsn(records, request, attempt)
                    == Option::Some(witness)
                &&& 1 <= witness && witness <= cut
                &&& replay_layer::start_lsn(
                    records.take(cut as int), request, attempt,
                ) == Option::Some(witness)
            }) by {
                let witness = start;
            }
        },
    }
}

// This is the exact InvocationsAcknowledged clause from the paper contract:
// the acknowledged prefix is a real record prefix, every recorded cut is
// bounded, and every Invoke names an occurring cut that already contains its
// matching Start.  No canonical-call or authorization premise is folded in.
pub open spec fn invocations_acknowledged(
    evidence: runtime_layer::GhostEvidence,
) -> bool {
    append_layer::is_prefix(
        evidence.acknowledged_prefix, evidence.records,
    )
        && append_layer::cuts_bounded(
            evidence.ack_cuts, evidence.records.len(),
        )
        && forall|index: nat| index < evidence.physical.len() ==>
            #[trigger] invoke_names_acknowledged_start(
                evidence, evidence.physical[index as int],
            )
}

pub open spec fn observed_slot_source_agreement(
    runtime: runtime_layer::ConcreteRuntime,
    evidence: runtime_layer::GhostEvidence,
) -> bool {
    let records = evidence.records;
    let history = evidence.physical;
    let source = evidence.slot_source;
    match runtime.slot {
        record_layer::ExecSlot::Idle
        | record_layer::ExecSlot::Ready { .. }
        | record_layer::ExecSlot::InFlight { .. } => source.is_none(),
        record_layer::ExecSlot::Received {
            request, attempt, observation,
        } => p1_layer::source_is_delivery(
            history, source, request, attempt, observation,
        ),
        record_layer::ExecSlot::ObservedSuccess {
            request, attempt, value,
        } => {
            let observation = replay_layer::Observation::Success(value);
            p1_layer::source_is_delivery(
                history, source, request, attempt, observation,
            ) && replay_layer::outcome_observation(records, request, attempt)
                == Option::Some(observation)
        },
        record_layer::ExecSlot::ObservedFailure { request, attempt } => {
            let observation = replay_layer::Observation::Failure;
            p1_layer::source_is_delivery(
                history, source, request, attempt, observation,
            ) && replay_layer::outcome_observation(records, request, attempt)
                == Option::Some(observation)
        },
        record_layer::ExecSlot::ObservedUnknown {
            request, attempt, reason,
        } => match reason {
            replay_layer::UnknownReason::AmbiguousOutcome => {
                let observation = replay_layer::Observation::Ambiguous;
                p1_layer::source_is_delivery(
                    history, source, request, attempt, observation,
                ) && replay_layer::outcome_observation(
                    records, request, attempt,
                ) == Option::Some(observation)
            },
            replay_layer::UnknownReason::InvalidResultReason => {
                // The same bad value witnesses the physical delivery and
                // durable Outcome; two unrelated existentials are unsound.
                exists|bad: replay_layer::InvalidValue|
                    #[trigger] p1_layer::source_is_delivery(
                        history,
                        source,
                        request,
                        attempt,
                        replay_layer::Observation::InvalidResult(bad),
                    )
                        && replay_layer::outcome_observation(
                            records, request, attempt,
                        ) == Option::Some(
                            replay_layer::Observation::InvalidResult(bad),
                        )
            },
            replay_layer::UnknownReason::Exhausted
            | replay_layer::UnknownReason::Recovery
            | replay_layer::UnknownReason::NonConclusiveFailure => false,
        },
    }
}

pub open spec fn terminal_source_agreement(
    cfg: config_layer::FullConfig,
    runtime: runtime_layer::ConcreteRuntime,
    evidence: runtime_layer::GhostEvidence,
) -> bool {
    let durable = replay_layer::replay(
        config_layer::erase_config(cfg), runtime.store.journal,
    );
    evidence.commit_source.dom()
            == ISet::<replay_layer::RequestId>::full()
        && forall|request: replay_layer::RequestId| {
            let source = #[trigger] evidence.commit_source[request];
            match durable.committed[request] {
                Option::None => source.is_none(),
                Option::Some(committed) => p1_layer::source_is_delivery(
                    evidence.physical,
                    source,
                    request,
                    committed.attempt,
                    replay_layer::Observation::Success(committed.value),
                ),
            }
        }
}

// Exact SourceAgreement(C,G): transient slot sources and persistent commit
// sources are both accounted for.  This predicate does not include the
// stronger result-validity clause from BrokerInvariant.
pub open spec fn source_agreement(
    cfg: config_layer::FullConfig,
    runtime: runtime_layer::ConcreteRuntime,
    evidence: runtime_layer::GhostEvidence,
) -> bool {
    observed_slot_source_agreement(runtime, evidence)
        && terminal_source_agreement(cfg, runtime, evidence)
}

pub open spec fn broker_ghost_equals(
    broker: p0_layer::State,
    evidence: runtime_layer::GhostEvidence,
) -> bool {
    broker.core.evidence.records == evidence.records
        && broker.core.evidence.ack_cuts == evidence.ack_cuts
        && broker.core.evidence.acknowledged_prefix
            == evidence.acknowledged_prefix
        && broker.physical.physical == evidence.physical
        && broker.physical.slot_source == evidence.slot_source
        && broker.physical.commit_source == evidence.commit_source
}

// Representation is stated field-by-field as the paper relation.  It is not
// an alias for P3 or LocalInductiveInvariant, and it does not embed a Broker
// state inside the concrete runtime.
pub open spec fn representation(
    cfg: config_layer::FullConfig,
    concrete: runtime_layer::JournalConfiguration,
    broker: p0_layer::State,
) -> bool {
    concrete.evidence.records == runtime_layer::journal_view(concrete)
        && broker.core.broker.durable
            == replay_layer::replay(
                config_layer::erase_config(cfg), concrete.evidence.records,
            )
        && broker.core.broker.slot == concrete.runtime.slot
        && broker.core.broker.mode == concrete.runtime.mode
        && broker.core.broker.append == concrete.runtime.append
        && broker_ghost_equals(broker, concrete.evidence)
        && contract_layer::broker_contract_invariant(cfg, broker)
        && invocations_acknowledged(concrete.evidence)
        && source_agreement(cfg, concrete.runtime, concrete.evidence)
}

pub proof fn abstract_initial_is_broker_initial(
    cfg: config_layer::FullConfig,
)
    ensures abstract_broker_state(
        cfg, runtime_layer::initial_configuration(cfg),
    ) == p0_layer::initial_state(cfg),
{
}

pub proof fn outcome_observation_some_implies_lsn_some(
    records: Seq<replay_layer::JournalRecord>,
    request: replay_layer::RequestId,
    attempt: replay_layer::AttemptId,
)
    requires replay_layer::outcome_observation(
        records, request, attempt,
    ).is_some(),
    ensures replay_layer::outcome_lsn(records, request, attempt).is_some(),
    decreases records.len(),
{
    if records.len() > 0 {
        let prefix = records.drop_last();
        match records.last() {
            replay_layer::JournalRecord::Outcome {
                request: found_request,
                attempt: found_attempt,
                ..
            } => {
                if found_request != request || found_attempt != attempt {
                    outcome_observation_some_implies_lsn_some(
                        prefix, request, attempt,
                    );
                }
            },
            _ => outcome_observation_some_implies_lsn_some(
                prefix, request, attempt,
            ),
        }
    }
}

pub proof fn source_and_durable_outcome_are_equal(
    records: Seq<replay_layer::JournalRecord>,
    history: Seq<p0_layer::PhysicalEvent>,
    source: Option<p0_layer::PhysicalIndex>,
    request: replay_layer::RequestId,
    attempt: replay_layer::AttemptId,
    observation: replay_layer::Observation,
)
    requires
        p1_layer::source_is_delivery(
            history, source, request, attempt, observation,
        ),
        contract_layer::delivered_outcome_order(records, history),
        replay_layer::outcome_observation(
            records, request, attempt,
        ).is_some(),
    ensures replay_layer::outcome_observation(
        records, request, attempt,
    ) == Option::Some(observation),
{
    outcome_observation_some_implies_lsn_some(
        records, request, attempt,
    );
    match source {
        Option::None => {},
        Option::Some(index) => {
            assert(index < history.len());
            assert(history[index as int]
                == (p0_layer::PhysicalEvent::Delivered {
                    request, attempt, observation,
                    journal_cut: match history[index as int] {
                        p0_layer::PhysicalEvent::Delivered { journal_cut, .. } => {
                            journal_cut
                        },
                        p0_layer::PhysicalEvent::Invoke { .. } => 0,
                    },
                }));
            match replay_layer::outcome_lsn(records, request, attempt) {
                Option::None => {},
                Option::Some(_lsn) => {},
            }
        },
    }
}

pub proof fn physical_cuts_valid_at(
    cfg: config_layer::FullConfig,
    records: Seq<replay_layer::JournalRecord>,
    cuts: Seq<nat>,
    history: Seq<p0_layer::PhysicalEvent>,
    index: nat,
)
    requires
        p1_layer::physical_cuts_valid(cfg, records, cuts, history),
        index < history.len(),
    ensures match history[index as int] {
        p0_layer::PhysicalEvent::Invoke {
            request, attempt, ack_cut, ..
        } => {
            ack_cut <= records.len()
                && p1_layer::nat_occurs(cuts, ack_cut)
                && replay_layer::start_lsn(
                    records.take(ack_cut as int), request, attempt,
                ).is_some()
        },
        p0_layer::PhysicalEvent::Delivered { .. } => true,
    },
    decreases history.len(),
{
    let prefix = history.drop_last();
    if index < prefix.len() {
        assert(prefix[index as int] == history[index as int]);
        physical_cuts_valid_at(cfg, records, cuts, prefix, index);
    } else {
        assert(index == history.len() - 1);
        assert(history[index as int] == history.last());
    }
}

pub proof fn physical_cut_implies_acknowledged_invoke(
    cfg: config_layer::FullConfig,
    evidence: runtime_layer::GhostEvidence,
    index: nat,
)
    requires
        p1_layer::physical_cuts_valid(
            cfg,
            evidence.records,
            evidence.ack_cuts,
            evidence.physical,
        ),
        index < evidence.physical.len(),
    ensures invoke_names_acknowledged_start(
        evidence, evidence.physical[index as int],
    ),
{
    physical_cuts_valid_at(
        cfg,
        evidence.records,
        evidence.ack_cuts,
        evidence.physical,
        index,
    );
    match evidence.physical[index as int] {
        p0_layer::PhysicalEvent::Invoke {
            request, attempt, ack_cut, ..
        } => {
            assert(ack_cut <= evidence.records.len());
            assert(evidence.records.take(ack_cut as int).len() == ack_cut);
            replay_layer::start_lsn_is_in_bounds(
                evidence.records.take(ack_cut as int), request, attempt,
            );
            match replay_layer::start_lsn(
                evidence.records.take(ack_cut as int), request, attempt,
            ) {
                Option::None => {},
                Option::Some(start) => {
                    assert(start <= evidence.records.take(ack_cut as int).len());
                },
            }
        },
        p0_layer::PhysicalEvent::Delivered { .. } => {},
    }
}

pub proof fn all_physical_invokes_are_acknowledged(
    cfg: config_layer::FullConfig,
    evidence: runtime_layer::GhostEvidence,
    bound: nat,
)
    requires
        p1_layer::physical_cuts_valid(
            cfg,
            evidence.records,
            evidence.ack_cuts,
            evidence.physical,
        ),
        bound <= evidence.physical.len(),
    ensures forall|index: nat| index < bound ==>
        #[trigger] invoke_names_acknowledged_start(
            evidence, evidence.physical[index as int],
        ),
    decreases bound,
{
    if bound > 0 {
        let last: nat = (bound - 1) as nat;
        all_physical_invokes_are_acknowledged(cfg, evidence, last);
        physical_cut_implies_acknowledged_invoke(cfg, evidence, last);
        assert forall|index: nat| index < bound implies
            #[trigger] invoke_names_acknowledged_start(
                evidence, evidence.physical[index as int],
            ) by {
            if index < last {
            } else {
                assert(index == last);
            }
        }
    }
}

pub proof fn append_invariant_implies_acknowledgment_shape(
    concrete: runtime_layer::JournalConfiguration,
)
    requires append_layer::b1_invariant(runtime_layer::append_view(concrete)),
    ensures
        append_layer::is_prefix(
            concrete.evidence.acknowledged_prefix,
            concrete.evidence.records,
        ),
        append_layer::cuts_bounded(
            concrete.evidence.ack_cuts,
            concrete.evidence.records.len(),
        ),
{
    assert(append_layer::cuts_bounded(
        concrete.evidence.ack_cuts,
        concrete.evidence.records.len(),
    ));
    append_layer::acknowledged_prefix_properties(
        concrete.evidence.records, concrete.evidence.ack_cuts,
    );
}

pub proof fn local_invariant_implies_invocations_acknowledged(
    cfg: config_layer::FullConfig,
    concrete: runtime_layer::JournalConfiguration,
    broker: p0_layer::State,
)
    requires
        broker == abstract_broker_state(cfg, concrete),
        contract_layer::local_inductive_invariant(cfg, broker),
    ensures invocations_acknowledged(concrete.evidence),
{
    assert(p3_layer::p3_invariant(cfg, broker));
    assert(p2_layer::p2_invariant(cfg, broker));
    assert(p1_layer::p1_invariant(cfg, broker));
    assert(append_layer::b1_invariant(
        record_layer::append_view(broker.core),
    ));
    assert(runtime_layer::append_view(concrete)
        == record_layer::append_view(broker.core));
    append_invariant_implies_acknowledgment_shape(concrete);
    assert(p1_layer::physical_cuts_valid(
        cfg,
        concrete.evidence.records,
        concrete.evidence.ack_cuts,
        concrete.evidence.physical,
    ));
    all_physical_invokes_are_acknowledged(
        cfg, concrete.evidence, concrete.evidence.physical.len(),
    );
}

pub proof fn local_invariant_implies_source_agreement(
    cfg: config_layer::FullConfig,
    concrete: runtime_layer::JournalConfiguration,
    broker: p0_layer::State,
)
    requires
        broker == abstract_broker_state(cfg, concrete),
        contract_layer::local_inductive_invariant(cfg, broker),
    ensures source_agreement(cfg, concrete.runtime, concrete.evidence),
{
    let erased = config_layer::erase_config(cfg);
    let records = concrete.evidence.records;
    let history = concrete.evidence.physical;
    assert(p3_layer::p3_invariant(cfg, broker));
    assert(p2_layer::p2_invariant(cfg, broker));
    assert(p1_layer::p1_invariant(cfg, broker));
    assert(p1_layer::physical_slot_agreement(broker));
    assert(record_layer::b2_record_invariant(erased, broker.core));
    assert(record_layer::durable_slot_agreement(
        erased, broker.core.broker.durable, broker.core.broker.slot,
    ));
    assert(contract_layer::broker_contract_invariant(cfg, broker));
    assert(contract_layer::delivered_outcome_order(records, history));

    match concrete.runtime.slot {
        record_layer::ExecSlot::ObservedSuccess {
            request, attempt, value,
        } => {
            query_layer::replay_d_outcome_exact(
                erased, records, request, attempt,
            );
            source_and_durable_outcome_are_equal(
                records,
                history,
                concrete.evidence.slot_source,
                request,
                attempt,
                replay_layer::Observation::Success(value),
            );
        },
        record_layer::ExecSlot::ObservedFailure { request, attempt } => {
            query_layer::replay_d_outcome_exact(
                erased, records, request, attempt,
            );
            source_and_durable_outcome_are_equal(
                records,
                history,
                concrete.evidence.slot_source,
                request,
                attempt,
                replay_layer::Observation::Failure,
            );
        },
        record_layer::ExecSlot::ObservedUnknown {
            request, attempt, reason,
        } => match reason {
            replay_layer::UnknownReason::AmbiguousOutcome => {
                query_layer::replay_d_outcome_exact(
                    erased, records, request, attempt,
                );
                source_and_durable_outcome_are_equal(
                    records,
                    history,
                    concrete.evidence.slot_source,
                    request,
                    attempt,
                    replay_layer::Observation::Ambiguous,
                );
            },
            replay_layer::UnknownReason::InvalidResultReason => {
                let bad = choose|bad: replay_layer::InvalidValue|
                    #[trigger] p1_layer::source_is_delivery(
                        history,
                        concrete.evidence.slot_source,
                        request,
                        attempt,
                        replay_layer::Observation::InvalidResult(bad),
                    );
                query_layer::replay_d_outcome_exact(
                    erased, records, request, attempt,
                );
                source_and_durable_outcome_are_equal(
                    records,
                    history,
                    concrete.evidence.slot_source,
                    request,
                    attempt,
                    replay_layer::Observation::InvalidResult(bad),
                );
            },
            replay_layer::UnknownReason::Exhausted
            | replay_layer::UnknownReason::Recovery
            | replay_layer::UnknownReason::NonConclusiveFailure => {},
        },
        record_layer::ExecSlot::Idle
        | record_layer::ExecSlot::Ready { .. }
        | record_layer::ExecSlot::InFlight { .. }
        | record_layer::ExecSlot::Received { .. } => {},
    }

    assert(p3_layer::commit_source_agreement(cfg, broker));
    assert(concrete.evidence.commit_source.dom()
        == ISet::<replay_layer::RequestId>::full());
    assert forall|request: replay_layer::RequestId| {
        let source = #[trigger] concrete.evidence.commit_source[request];
        match replay_layer::replay(
            erased, concrete.runtime.store.journal,
        ).committed[request] {
            Option::None => source.is_none(),
            Option::Some(committed) => p1_layer::source_is_delivery(
                concrete.evidence.physical,
                source,
                request,
                committed.attempt,
                replay_layer::Observation::Success(committed.value),
            ),
        }
    } by {
        assert(broker.core.broker.durable
            == replay_layer::replay(
                erased, concrete.runtime.store.journal,
            ));
    }
}

pub proof fn local_inductive_invariant_implies_representation(
    cfg: config_layer::FullConfig,
    concrete: runtime_layer::JournalConfiguration,
    broker: p0_layer::State,
)
    requires
        runtime_layer::storage_agreement(concrete),
        broker == abstract_broker_state(cfg, concrete),
        contract_layer::local_inductive_invariant(cfg, broker),
    ensures representation(cfg, concrete, broker),
{
    local_invariant_implies_invocations_acknowledged(cfg, concrete, broker);
    local_invariant_implies_source_agreement(cfg, concrete, broker);
}

pub proof fn initial_representation(cfg: config_layer::FullConfig)
    requires config_layer::full_config_wf(cfg),
    ensures representation(
        cfg,
        runtime_layer::initial_configuration(cfg),
        p0_layer::initial_state(cfg),
    ),
{
    runtime_layer::initial_basic_invariant(cfg);
    execution_layer::initial_preserves_local_inductive_invariant(cfg);
    abstract_initial_is_broker_initial(cfg);
    local_inductive_invariant_implies_representation(
        cfg,
        runtime_layer::initial_configuration(cfg),
        p0_layer::initial_state(cfg),
    );
}

} // verus!
