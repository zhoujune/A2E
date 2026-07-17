use vstd::prelude::*;

#[path = "t1_broker_execution.rs"]
pub mod execution_layer;

verus! {

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

// T1 is parametric in the adapter interpretation.  The adapter component is
// deliberately opaque to Broker safety: this layer neither inspects it nor
// uses an adapter-effect premise.  Later adapter-refinement theorems may open
// their own interpretation while reusing the Broker theorem below.
pub struct PaperConfig<A> {
    pub broker: config_layer::FullConfig,
    pub adapter: A,
}

pub closed spec fn paper_broker_config<A>(cfg: PaperConfig<A>)
    -> config_layer::FullConfig
{
    cfg.broker
}

pub proof fn paper_broker_config_is_broker<A>(cfg: PaperConfig<A>)
    ensures paper_broker_config(cfg) == cfg.broker,
{
}

pub open spec fn paper_config_wf<A>(cfg: PaperConfig<A>) -> bool {
    config_layer::full_config_wf(paper_broker_config(cfg))
}

pub open spec fn prefix_events(
    execution: execution_layer::BrokerExecution,
    length: nat,
) -> Seq<global_layer::GlobalEvent> {
    execution.events.take(length as int)
}

pub open spec fn successful_return_cuts_exact(
    events: Seq<global_layer::GlobalEvent>,
) -> bool {
    forall|index: nat| index < events.len() ==> match #[trigger] events[index as int] {
        global_layer::GlobalEvent::JournalAppendReturn { cut }
        | global_layer::GlobalEvent::WalFlushAck { cut } => {
            cut == projection_layer::pi_journal(
                events.take(index as int),
            ).len()
        },
        global_layer::GlobalEvent::BrokerLinearize { .. }
        | global_layer::GlobalEvent::JournalAppendCall { .. }
        | global_layer::GlobalEvent::JournalAppendLinearize { .. }
        | global_layer::GlobalEvent::JournalDiskFull { .. }
        | global_layer::GlobalEvent::WalStage { .. }
        | global_layer::GlobalEvent::WalWriteFull { .. }
        | global_layer::GlobalEvent::WalWriteTorn { .. }
        | global_layer::GlobalEvent::WalFinishTorn { .. }
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
        | global_layer::GlobalEvent::FinishRecover => true,
    }
}

// Exact agreement for one relational execution prefix.  This is intentionally
// stated against the global projections, rather than against a decoded local
// trace, so it is the paper-level TraceAgreement predicate.
pub open spec fn trace_agreement_at(
    cfg: config_layer::FullConfig,
    execution: execution_layer::BrokerExecution,
    length: nat,
) -> bool {
    length <= execution.events.len()
        && length < execution.configs.len()
        && {
            let events = prefix_events(execution, length);
            let state = execution.configs[length as int];
            let records = projection_layer::pi_journal(events);
            let physical = projection_layer::pi_physical(events);
            let cuts = projection_layer::pi_ack(events);
            &&& state.core.evidence.records == records
            &&& state.physical.physical == physical
            &&& state.core.evidence.ack_cuts == cuts
            &&& append_layer::cuts_bounded(cuts, records.len())
            &&& append_layer::cuts_monotone(cuts)
            &&& state.core.evidence.acknowledged_prefix
                == append_layer::acknowledged_prefix_for(records, cuts)
            &&& state.core.evidence.acknowledged_prefix.len()
                == append_layer::last_or_zero(cuts)
            &&& append_layer::is_prefix(
                state.core.evidence.acknowledged_prefix, records,
            )
            &&& successful_return_cuts_exact(events)
        }
}

pub open spec fn prefix_trace_agreement(
    cfg: config_layer::FullConfig,
    execution: execution_layer::BrokerExecution,
) -> bool {
    forall|length: nat| length <= execution.events.len() ==>
        #[trigger] trace_agreement_at(cfg, execution, length)
}

// TraceAgreement also fixes the proof cuts carried by each Invoke at the
// exact pre-step prefix.  The stronger authorization and prior-return facts
// remain exposed separately by invoke_temporal_safety below.
pub open spec fn invoke_cut_agreement_at(
    execution: execution_layer::BrokerExecution,
    index: nat,
) -> bool {
    index < execution.events.len() && match execution.events[index as int] {
        global_layer::GlobalEvent::InvokeEvent {
            journal_cut, ack_cut, ..
        } => {
            let events = execution.events.take(index as int);
            let state = execution.configs[index as int];
            journal_cut == projection_layer::pi_journal(events).len()
                && ack_cut
                    == state.core.evidence.acknowledged_prefix.len()
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
        | global_layer::GlobalEvent::DeliverEvent { .. }
        | global_layer::GlobalEvent::IgnoreStale { .. }
        | global_layer::GlobalEvent::RetryRelease { .. }
        | global_layer::GlobalEvent::Crash
        | global_layer::GlobalEvent::BeginScan
        | global_layer::GlobalEvent::FinishScan
        | global_layer::GlobalEvent::TruncateTail
        | global_layer::GlobalEvent::AbortScan
        | global_layer::GlobalEvent::BeginRecover
        | global_layer::GlobalEvent::FinishRecover => true,
    }
}

pub open spec fn invoke_cut_agreement(
    execution: execution_layer::BrokerExecution,
) -> bool {
    forall|index: nat| index < execution.events.len() ==>
        #[trigger] invoke_cut_agreement_at(execution, index)
}

pub open spec fn trace_agreement(
    cfg: config_layer::FullConfig,
    execution: execution_layer::BrokerExecution,
) -> bool {
    prefix_trace_agreement(cfg, execution)
        && invoke_cut_agreement(execution)
}

// The label-indexed temporal fact rules out retroactive authorization.  The
// current cuts are exact, the call is canonical, the acknowledged prefix has
// a valid Authorize/Start ancestry, and a successful return carrying this
// exact cut occurs strictly before the Invoke label.
pub open spec fn invoke_temporal_at(
    cfg: config_layer::FullConfig,
    execution: execution_layer::BrokerExecution,
    index: nat,
) -> bool {
    index < execution.events.len() && match execution.events[index as int] {
        global_layer::GlobalEvent::InvokeEvent {
            request, attempt, call, journal_cut, ack_cut,
        } => {
            let events = execution.events.take(index as int);
            let state = execution.configs[index as int];
            let records = projection_layer::pi_journal(events);
            let cuts = projection_layer::pi_ack(events);
            &&& journal_cut == records.len()
            &&& ack_cut == state.core.evidence.acknowledged_prefix.len()
            &&& ack_cut == append_layer::last_or_zero(cuts)
            &&& 1 <= ack_cut
            &&& ack_cut <= journal_cut
            &&& call == config_layer::canonical_call(cfg, request)
            &&& p2_layer::acknowledged_start_authorized(
                cfg, records.take(ack_cut as int), request, attempt,
            )
            &&& replay_layer::authorize_count_for_request(
                records.take(ack_cut as int), request,
            ) == 1
            &&& replay_layer::start_count(
                records.take(ack_cut as int), request, attempt,
            ) == 1
            &&& exists|return_index: nat| {
                &&& return_index < index
                &&& execution.events[return_index as int]
                    == global_layer::GlobalEvent::JournalAppendReturn {
                        cut: ack_cut,
                    }
            }
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
        | global_layer::GlobalEvent::DeliverEvent { .. }
        | global_layer::GlobalEvent::IgnoreStale { .. }
        | global_layer::GlobalEvent::RetryRelease { .. }
        | global_layer::GlobalEvent::Crash
        | global_layer::GlobalEvent::BeginScan
        | global_layer::GlobalEvent::FinishScan
        | global_layer::GlobalEvent::TruncateTail
        | global_layer::GlobalEvent::AbortScan
        | global_layer::GlobalEvent::BeginRecover
        | global_layer::GlobalEvent::FinishRecover => true,
    }
}

pub open spec fn invoke_temporal_safety(
    cfg: config_layer::FullConfig,
    execution: execution_layer::BrokerExecution,
) -> bool {
    forall|index: nat| index < execution.events.len() ==>
        #[trigger] invoke_temporal_at(cfg, execution, index)
}

pub open spec fn all_configurations_safe(
    cfg: config_layer::FullConfig,
    execution: execution_layer::BrokerExecution,
) -> bool {
    forall|index: nat| index < execution.configs.len() ==>
        #[trigger] contract_layer::broker_contract_invariant(
            cfg, execution.configs[index as int],
        )
        && contract_layer::local_inductive_invariant(
            cfg, execution.configs[index as int],
        )
}

pub open spec fn no_crash_between(
    events: Seq<global_layer::GlobalEvent>,
    left: nat,
    right: nat,
) -> bool {
    forall|index: nat| left <= index && index < right ==>
        !(#[trigger] events[index as int] is Crash)
}

// [left,right) is maximal: it starts at trace origin or immediately after a
// Crash, and ends at trace end or immediately before a Crash.
pub open spec fn maximal_crash_free_interval(
    events: Seq<global_layer::GlobalEvent>,
    left: nat,
    right: nat,
) -> bool {
    left <= right
        && right <= events.len()
        && no_crash_between(events, left, right)
        && (left == 0 || events[(left - 1) as int] is Crash)
        && (right == events.len() || events[right as int] is Crash)
}

pub open spec fn interval_append_projection(
    events: Seq<global_layer::GlobalEvent>,
    left: nat,
    right: nat,
) -> Seq<append_layer::AppendEvent<replay_layer::JournalRecord>> {
    projection_layer::pi_append(
        events.subrange(left as int, right as int),
    )
}

pub open spec fn crash_free_interval_classified_at(
    cfg: config_layer::FullConfig,
    execution: execution_layer::BrokerExecution,
    left: nat,
    right: nat,
) -> bool {
    maximal_crash_free_interval(execution.events, left, right) ==>
        bridge_layer::crash_free_epoch_shape(
            interval_append_projection(execution.events, left, right),
            bridge_layer::append_view(
                execution.configs[right as int],
            ).append,
        )
}

pub open spec fn crash_free_intervals_classified(
    cfg: config_layer::FullConfig,
    execution: execution_layer::BrokerExecution,
) -> bool {
    forall|left: nat, right: nat|
        #[trigger] crash_free_interval_classified_at(
            cfg, execution, left, right,
        )
}

pub open spec fn recovery_obligation_at(
    cfg: config_layer::FullConfig,
    execution: execution_layer::BrokerExecution,
    index: nat,
) -> bool {
    index < execution.events.len() && {
        let before = execution.configs[index as int];
        let after = execution.configs[(index + 1) as int];
        match execution.events[index as int] {
            global_layer::GlobalEvent::BrokerLinearize { record } => {
                before.core.broker.mode == record_layer::Mode::Recovering ==>
                    p3_layer::recovery_repair_record(
                        cfg, before.core.broker.durable, record,
                    )
                    && after.physical.commit_source
                        == before.physical.commit_source
            },
            global_layer::GlobalEvent::Crash => {
                &&& after.physical.commit_source
                    == before.physical.commit_source
                &&& after.physical.physical == before.physical.physical
                &&& after.core.evidence.records
                    == before.core.evidence.records
                &&& after.core.evidence.ack_cuts
                    == before.core.evidence.ack_cuts
                &&& after.core.evidence.acknowledged_prefix
                    == before.core.evidence.acknowledged_prefix
            },
            global_layer::GlobalEvent::FinishRecover => {
                let erased = config_layer::erase_config(cfg);
                &&& before.core.broker.mode == record_layer::Mode::Recovering
                &&& before.core.broker.append is Idle
                &&& query_layer::recovery_complete_d(
                    erased, before.core.broker.durable,
                )
                &&& query_layer::recovery_complete_j(
                    erased, before.core.evidence.records,
                )
                &&& after.core.broker.mode == record_layer::Mode::Online
                &&& after.core.broker.durable
                    == before.core.broker.durable
                &&& after.core.evidence.records
                    == before.core.evidence.records
            },
            global_layer::GlobalEvent::JournalAppendCall { .. }
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
            | global_layer::GlobalEvent::BeginScan
            | global_layer::GlobalEvent::FinishScan
            | global_layer::GlobalEvent::TruncateTail
            | global_layer::GlobalEvent::AbortScan
            | global_layer::GlobalEvent::BeginRecover => true,
        }
    }
}

pub open spec fn recovery_transition_obligations(
    cfg: config_layer::FullConfig,
    execution: execution_layer::BrokerExecution,
) -> bool {
    forall|index: nat| index < execution.events.len() ==>
        #[trigger] recovery_obligation_at(cfg, execution, index)
}

pub open spec fn global_uncontrolled_invocations_bounded(
    cfg: config_layer::FullConfig,
    events: Seq<global_layer::GlobalEvent>,
) -> bool {
    forall|request: replay_layer::RequestId|
        config_layer::erase_config(cfg).request_class[request]
                == replay_layer::RetryClass::Uncontrolled
            ==> #[trigger] p2_layer::request_invoke_count(
                projection_layer::pi_physical(events), request,
            ) <= 1
}

pub open spec fn global_terminal_uniqueness(
    events: Seq<global_layer::GlobalEvent>,
) -> bool {
    projection_layer::pi_logical(events)
            == projection_layer::logical_records(
                projection_layer::pi_journal(events),
            )
        && forall|request: replay_layer::RequestId|
            #[trigger] replay_layer::terminal_count(
                projection_layer::pi_journal(events), request,
            ) <= 1
}

pub open spec fn commit_provenance_at(
    cfg: config_layer::FullConfig,
    execution: execution_layer::BrokerExecution,
    request: replay_layer::RequestId,
) -> bool {
    let final_state = execution.configs[execution.events.len() as int];
    match final_state.core.broker.durable.committed[request] {
        Option::None => final_state.physical.commit_source[request].is_none(),
        Option::Some(committed) => {
            &&& config_layer::erase_config(cfg).valid_results
                .contains((request, committed.value))
            &&& exists|source: nat, journal_cut: nat| #![auto] {
                &&& final_state.physical.commit_source[request]
                    == Option::Some(source)
                &&& source < projection_layer::pi_physical(
                    execution.events,
                ).len()
                &&& projection_layer::pi_physical(
                    execution.events,
                )[source as int]
                    == p0_layer::PhysicalEvent::Delivered {
                        request,
                        attempt: committed.attempt,
                        observation: replay_layer::Observation::Success(
                            committed.value,
                        ),
                        journal_cut,
                    }
            }
        },
    }
}

pub open spec fn global_commit_provenance(
    cfg: config_layer::FullConfig,
    execution: execution_layer::BrokerExecution,
) -> bool {
    let final_state = execution.configs[execution.events.len() as int];
    final_state.core.evidence.records
            == projection_layer::pi_journal(execution.events)
        && final_state.physical.physical
            == projection_layer::pi_physical(execution.events)
        && p3_layer::commit_source_agreement(cfg, final_state)
        && forall|request: replay_layer::RequestId|
            #[trigger] commit_provenance_at(cfg, execution, request)
}

pub open spec fn t1_global_corollaries(
    cfg: config_layer::FullConfig,
    execution: execution_layer::BrokerExecution,
) -> bool {
    invoke_temporal_safety(cfg, execution)
        && global_uncontrolled_invocations_bounded(cfg, execution.events)
        && global_terminal_uniqueness(execution.events)
        && global_commit_provenance(cfg, execution)
}

pub open spec fn t1_parameterized_safety_statement(
    cfg: config_layer::FullConfig,
    execution: execution_layer::BrokerExecution,
) -> bool {
    &&& trace_agreement(cfg, execution)
    &&& projection_layer::global_append_protocol_prefix(execution.events)
    &&& all_configurations_safe(cfg, execution)
    &&& crash_free_intervals_classified(cfg, execution)
    &&& recovery_transition_obligations(cfg, execution)
    &&& t1_global_corollaries(cfg, execution)
}

pub proof fn broker_encode_trace_index(
    events: Seq<p0_layer::Event>,
    index: nat,
)
    requires index < events.len(),
    ensures projection_layer::broker_encode_trace(events)[index as int]
        == global_layer::broker_encode(events[index as int]),
    decreases events.len(),
{
    let prefix = events.drop_last();
    let event = events.last();
    projection_layer::broker_encode_trace_push(prefix, event);
    projection_layer::broker_encode_trace_len(prefix);
    assert(prefix.push(event) =~= events);
    if index < prefix.len() {
        broker_encode_trace_index(prefix, index);
        assert(projection_layer::broker_encode_trace(events)[index as int]
            == projection_layer::broker_encode_trace(prefix)[index as int]);
        assert(events[index as int] == prefix[index as int]);
    } else {
        assert(index == prefix.len());
        assert(events[index as int] == event);
        assert(projection_layer::broker_encode_trace(events)[index as int]
            == global_layer::broker_encode(event));
    }
}

pub proof fn decoded_event_at(
    globals: Seq<global_layer::GlobalEvent>,
    locals: Seq<p0_layer::Event>,
    index: nat,
)
    requires
        projection_layer::broker_decode_trace(globals)
            == Option::Some(locals),
        index < globals.len(),
    ensures
        index < locals.len(),
        globals[index as int]
            == global_layer::broker_encode(locals[index as int]),
        global_layer::broker_decode(globals[index as int])
            == Option::Some(locals[index as int]),
{
    projection_layer::broker_decode_trace_inverse(globals, locals);
    broker_encode_trace_index(locals, index);
    global_layer::broker_decode_encode_round_trip(locals[index as int]);
}

pub proof fn decoded_prefix_exact(
    globals: Seq<global_layer::GlobalEvent>,
    locals: Seq<p0_layer::Event>,
    length: nat,
)
    requires
        projection_layer::broker_decode_trace(globals)
            == Option::Some(locals),
        length <= globals.len(),
    ensures globals.take(length as int)
        == projection_layer::broker_encode_trace(
            locals.take(length as int),
        ),
{
    projection_layer::broker_decode_trace_inverse(globals, locals);
    projection_layer::broker_encode_trace_take(locals, length);
}

pub proof fn successful_return_cuts_exact_for_exec(
    cfg: config_layer::FullConfig,
    execution: execution_layer::BrokerExecution,
    locals: Seq<p0_layer::Event>,
)
    requires
        config_layer::full_config_wf(cfg),
        execution_layer::exec(cfg, execution),
        projection_layer::broker_decode_trace(execution.events)
            == Option::Some(locals),
    ensures successful_return_cuts_exact(execution.events),
{
    execution_layer::decoded_exec_refines_local_run(
        cfg, execution, locals,
    );
    execution_layer::exact_config_run_correspondence(
        cfg, execution, locals,
    );
    assert forall|index: nat| index < execution.events.len() implies
        match #[trigger] execution.events[index as int] {
            global_layer::GlobalEvent::JournalAppendReturn { cut }
            | global_layer::GlobalEvent::WalFlushAck { cut } => {
                cut == projection_layer::pi_journal(
                    execution.events.take(index as int),
                ).len()
            },
            _ => true,
        } by {
        decoded_event_at(execution.events, locals, index);
        decoded_prefix_exact(execution.events, locals, index);
        let global = execution.events[index as int];
        let local = locals[index as int];
        let before = execution.configs[index as int];
        let after = execution.configs[(index + 1) as int];
        assert(execution_layer::broker_step(
            cfg, before, global, after,
        ));
        execution_layer::broker_step_is_local_apply(
            cfg, before, global, local, after,
        );
        assert(before == p0_layer::run(
            cfg, locals.take(index as int),
        ));
        p0_layer::executable_prefix(cfg, locals, index);
        p0_layer::run_history_agreement(
            cfg, locals.take(index as int),
        );
        projection_layer::encoded_pi_journal(
            locals.take(index as int),
        );
        match global {
            global_layer::GlobalEvent::JournalAppendReturn { cut } => {
                match local {
                    p0_layer::Event::JournalAppendReturn { cut: local_cut } => {
                        assert(local_cut == cut);
                        assert(p0_layer::evidence_admissible(
                            cfg, before, local,
                        ));
                        assert(cut == before.core.evidence.records.len());
                        assert(before.core.evidence.records
                            == p0_layer::pi_journal(
                                locals.take(index as int),
                            ));
                    },
                    _ => { assert(false); },
                }
            },
            global_layer::GlobalEvent::WalFlushAck { .. } => {
                assert(global_layer::broker_decode(global).is_none());
                assert(false);
            },
            _ => {},
        }
    }
}

pub proof fn successful_return_cuts_exact_prefix(
    events: Seq<global_layer::GlobalEvent>,
    length: nat,
)
    requires
        successful_return_cuts_exact(events),
        length <= events.len(),
    ensures successful_return_cuts_exact(events.take(length as int)),
{
    let prefix = events.take(length as int);
    assert forall|index: nat| index < prefix.len() implies
        match #[trigger] prefix[index as int] {
            global_layer::GlobalEvent::JournalAppendReturn { cut }
            | global_layer::GlobalEvent::WalFlushAck { cut } => {
                cut == projection_layer::pi_journal(
                    prefix.take(index as int),
                ).len()
            },
            _ => true,
        } by {
        assert(index < events.len());
        assert(prefix[index as int] == events[index as int]);
        assert(prefix.take(index as int) =~= events.take(index as int));
    }
}

pub proof fn prefix_trace_agreement_for_exec(
    cfg: config_layer::FullConfig,
    execution: execution_layer::BrokerExecution,
    locals: Seq<p0_layer::Event>,
)
    requires
        config_layer::full_config_wf(cfg),
        execution_layer::exec(cfg, execution),
        projection_layer::broker_decode_trace(execution.events)
            == Option::Some(locals),
    ensures prefix_trace_agreement(cfg, execution),
{
    execution_layer::decoded_exec_refines_local_run(
        cfg, execution, locals,
    );
    execution_layer::exact_config_run_correspondence(
        cfg, execution, locals,
    );
    successful_return_cuts_exact_for_exec(cfg, execution, locals);
    assert forall|length: nat| length <= execution.events.len() implies
        #[trigger] trace_agreement_at(cfg, execution, length) by {
        let globals = execution.events.take(length as int);
        let local_prefix = locals.take(length as int);
        let state = execution.configs[length as int];
        assert(length < execution.configs.len());
        p0_layer::executable_prefix(cfg, locals, length);
        assert(p0_layer::admissibly_executable(cfg, local_prefix));
        p0_layer::run_history_agreement(cfg, local_prefix);
        bridge_layer::b2_append_protocol_bridge_safety(
            cfg, local_prefix,
        );
        decoded_prefix_exact(execution.events, locals, length);
        projection_layer::encoded_pi_journal(local_prefix);
        projection_layer::encoded_pi_physical(local_prefix);
        projection_layer::encoded_pi_ack(local_prefix);
        successful_return_cuts_exact_prefix(execution.events, length);
        assert(state == p0_layer::run(cfg, local_prefix));
        let projected = bridge_layer::append_project(local_prefix);
        assert(bridge_layer::append_agreement_at(cfg, local_prefix));
        assert(append_layer::checkpoint(projected));
        assert(bridge_layer::append_view(state)
            == append_layer::run(projected));
        assert(state.core.evidence.records
            == append_layer::pi_journal(projected));
        assert(state.core.evidence.ack_cuts
            == append_layer::pi_ack(projected));
        assert(append_layer::b1_invariant(
            append_layer::run(projected),
        ));
        assert(append_layer::cuts_bounded(
            state.core.evidence.ack_cuts,
            state.core.evidence.records.len(),
        ));
        assert(append_layer::cuts_monotone(
            state.core.evidence.ack_cuts,
        ));
    }
}

pub proof fn authorize_at_implies_count_positive(
    records: Seq<replay_layer::JournalRecord>,
    lsn: replay_layer::Lsn,
    request: replay_layer::RequestId,
)
    requires replay_layer::authorize_at(records, lsn, request),
    ensures replay_layer::authorize_count_for_request(records, request) > 0,
    decreases records.len(),
{
    let prefix = records.drop_last();
    let record = records.last();
    assert(prefix.push(record) =~= records);
    replay_layer::authorize_request_count_push(prefix, request, record);
    if lsn < records.len() {
        assert(replay_layer::authorize_at(prefix, lsn, request));
        authorize_at_implies_count_positive(prefix, lsn, request);
    } else {
        assert(lsn == records.len());
        match record {
            replay_layer::JournalRecord::Authorize { request: r, .. } => {
                assert(r == request);
            },
            _ => { assert(false); },
        }
    }
}

pub proof fn acknowledged_ancestry_has_unique_counts(
    cfg: config_layer::FullConfig,
    records: Seq<replay_layer::JournalRecord>,
    request: replay_layer::RequestId,
    attempt: replay_layer::AttemptId,
)
    requires
        config_layer::full_config_wf(cfg),
        replay_layer::journal_legal(
            config_layer::erase_config(cfg), records,
        ),
        p2_layer::acknowledged_start_authorized(
            cfg, records, request, attempt,
        ),
    ensures
        replay_layer::authorize_count_for_request(records, request) == 1,
        replay_layer::start_count(records, request, attempt) == 1,
{
    config_layer::erasure_is_replay_well_formed(cfg);
    replay_layer::replay_authorization(
        config_layer::erase_config(cfg), records,
    );
    replay_layer::replay_start_exact(
        config_layer::erase_config(cfg), records,
    );
    match replay_layer::start_lsn(records, request, attempt) {
        Option::Some(start) => {
            let auth = choose|auth: replay_layer::Lsn|
                #[trigger] p2_layer::valid_authorize_at(
                    cfg, records, auth, request,
                )
                    && auth < start
                    && attempt <= config_layer::erase_config(cfg)
                        .max_attempts[request]
                    && (config_layer::erase_config(cfg)
                            .request_class[request]
                            == replay_layer::RetryClass::Uncontrolled
                        ==> attempt == 1)
                    && !replay_layer::failure_conclusive(
                        config_layer::erase_config(cfg),
                        records.take((start - 1) as int), request,
                    );
            assert(p2_layer::valid_authorize_at(
                cfg, records, auth, request,
            ));
            authorize_at_implies_count_positive(records, auth, request);
            p1_layer::start_lsn_some_implies_count_positive(
                records, request, attempt,
            );
            assert(replay_layer::authorize_count_for_request(
                records, request,
            ) <= 1);
            assert(replay_layer::authorize_count_for_request(
                records, request,
            ) == 1);
            assert(replay_layer::start_count(
                records, request, attempt,
            ) == 1);
        },
        Option::None => { assert(false); },
    }
}

pub proof fn local_invoke_step_facts(
    cfg: config_layer::FullConfig,
    before: p0_layer::State,
    request: replay_layer::RequestId,
    attempt: replay_layer::AttemptId,
    call: config_layer::CallDescriptor,
    journal_cut: nat,
    ack_cut: nat,
)
    requires
        config_layer::full_config_wf(cfg),
        contract_layer::local_inductive_invariant(cfg, before),
        p0_layer::admissibly_enabled(
            cfg,
            before,
            p0_layer::Event::InvokeEvent {
                request, attempt, call, journal_cut, ack_cut,
            },
        ),
    ensures
        journal_cut == before.core.evidence.records.len(),
        ack_cut == before.core.evidence.acknowledged_prefix.len(),
        1 <= ack_cut,
        ack_cut <= journal_cut,
        call == config_layer::canonical_call(cfg, request),
        p2_layer::acknowledged_start_authorized(
            cfg,
            before.core.evidence.records.take(ack_cut as int),
            request,
            attempt,
        ),
        replay_layer::authorize_count_for_request(
            before.core.evidence.records.take(ack_cut as int), request,
        ) == 1,
        replay_layer::start_count(
            before.core.evidence.records.take(ack_cut as int),
            request,
            attempt,
        ) == 1,
{
    assert(p1_layer::p1_invariant(cfg, before));
    let local = p0_layer::Event::InvokeEvent {
        request, attempt, call, journal_cut, ack_cut,
    };
    p2_layer::invoke_event_has_refinement_witness(cfg, before, local);
    let records = before.core.evidence.records;
    let acknowledged = records.take(ack_cut as int);
    assert(p2_layer::invoke_refinement_witness(
        cfg,
        records,
        p0_layer::PhysicalEvent::Invoke {
            request, attempt, call, journal_cut, ack_cut,
        },
    ));
    assert(p2_layer::acknowledged_start_authorized(
        cfg, acknowledged, request, attempt,
    ));
    assert(replay_layer::journal_legal(
        config_layer::erase_config(cfg), records,
    ));
    replay_layer::journal_legal_take(
        config_layer::erase_config(cfg), records, ack_cut,
    );
    acknowledged_ancestry_has_unique_counts(
        cfg, acknowledged, request, attempt,
    );
}

pub proof fn current_ack_has_strict_prior_journal_return(
    cfg: config_layer::FullConfig,
    execution: execution_layer::BrokerExecution,
    locals: Seq<p0_layer::Event>,
    index: nat,
    ack_cut: nat,
)
    requires
        projection_layer::broker_decode_trace(execution.events)
            == Option::Some(locals),
        index < execution.events.len(),
        trace_agreement_at(cfg, execution, index),
        ack_cut
            == execution.configs[index as int]
                .core.evidence.acknowledged_prefix.len(),
        1 <= ack_cut,
    ensures exists|return_index: nat| {
        &&& return_index < index
        &&& execution.events[return_index as int]
            == global_layer::GlobalEvent::JournalAppendReturn { cut: ack_cut }
    },
{
    let globals = execution.events.take(index as int);
    let cuts = projection_layer::pi_ack(globals);
    assert(ack_cut == append_layer::last_or_zero(cuts));
    assert(cuts.len() > 0) by {
        if cuts.len() == 0 {
            assert(append_layer::last_or_zero(cuts) == 0);
        }
    }
    let ack_index: int = cuts.len() - 1;
    assert(0 <= ack_index < cuts.len());
    assert(cuts[ack_index] == ack_cut);
    projection_layer::pi_ack_has_successful_return_source(
        globals, ack_index,
    );
    let source = choose|source: int|
        0 <= source < globals.len()
            && #[trigger] projection_layer::successful_return_cut(
                globals[source],
            ) == Option::Some(ack_cut);
    assert(source < index);
    match globals[source] {
        global_layer::GlobalEvent::JournalAppendReturn { cut } => {
            assert(cut == ack_cut);
            let return_index: nat = source as nat;
            assert(exists|witness: nat| {
                &&& witness < index
                &&& execution.events[witness as int]
                    == global_layer::GlobalEvent::JournalAppendReturn {
                        cut: ack_cut,
                    }
            }) by {
                assert(execution.events[return_index as int]
                    == global_layer::GlobalEvent::JournalAppendReturn {
                        cut: ack_cut,
                    });
            }
        },
        global_layer::GlobalEvent::WalFlushAck { .. } => {
            let source_nat: nat = source as nat;
            decoded_event_at(execution.events, locals, source_nat);
            assert(global_layer::broker_decode(
                execution.events[source],
            ).is_none());
            assert(false);
        },
        _ => { assert(false); },
    }
}

pub proof fn invoke_temporal_at_for_exec(
    cfg: config_layer::FullConfig,
    execution: execution_layer::BrokerExecution,
    locals: Seq<p0_layer::Event>,
    index: nat,
)
    requires
        config_layer::full_config_wf(cfg),
        execution_layer::exec(cfg, execution),
        projection_layer::broker_decode_trace(execution.events)
            == Option::Some(locals),
        index < execution.events.len(),
    ensures invoke_temporal_at(cfg, execution, index),
{
    execution_layer::decoded_exec_refines_local_run(
        cfg, execution, locals,
    );
    execution_layer::exact_config_run_correspondence(
        cfg, execution, locals,
    );
    execution_layer::every_exec_config_preserves_local_inductive_invariant(
        cfg, execution,
    );
    prefix_trace_agreement_for_exec(cfg, execution, locals);
    decoded_event_at(execution.events, locals, index);
    let global = execution.events[index as int];
    let local = locals[index as int];
    let before = execution.configs[index as int];
    let after = execution.configs[(index + 1) as int];
    match global {
            global_layer::GlobalEvent::InvokeEvent {
                request, attempt, call, journal_cut, ack_cut,
            } => {
                match local {
                    p0_layer::Event::InvokeEvent {
                        request: local_request,
                        attempt: local_attempt,
                        call: local_call,
                        journal_cut: local_journal_cut,
                        ack_cut: local_ack_cut,
                    } => {
                        assert(local_request == request);
                        assert(local_attempt == attempt);
                        assert(local_call == call);
                        assert(local_journal_cut == journal_cut);
                        assert(local_ack_cut == ack_cut);
                    },
                    _ => { assert(false); },
                }
                assert(execution_layer::broker_step(
                    cfg, before, global, after,
                ));
                execution_layer::broker_step_is_local_apply(
                    cfg, before, global, local, after,
                );
                assert(contract_layer::local_inductive_invariant(cfg, before));
                let globals = execution.events.take(index as int);
                let records = projection_layer::pi_journal(globals);
                assert(trace_agreement_at(cfg, execution, index));
                assert(before.core.evidence.records == records);
                local_invoke_step_facts(
                    cfg,
                    before,
                    request,
                    attempt,
                    call,
                    journal_cut,
                    ack_cut,
                );
                let acknowledged = records.take(ack_cut as int);
                assert(p2_layer::acknowledged_start_authorized(
                    cfg, acknowledged, request, attempt,
                ));
                assert(replay_layer::authorize_count_for_request(
                    acknowledged, request,
                ) == 1);
                assert(replay_layer::start_count(
                    acknowledged, request, attempt,
                ) == 1);
                current_ack_has_strict_prior_journal_return(
                    cfg, execution, locals, index, ack_cut,
                );
            },
        _ => {},
    }
}

pub proof fn invoke_temporal_safety_for_exec(
    cfg: config_layer::FullConfig,
    execution: execution_layer::BrokerExecution,
    locals: Seq<p0_layer::Event>,
)
    requires
        config_layer::full_config_wf(cfg),
        execution_layer::exec(cfg, execution),
        projection_layer::broker_decode_trace(execution.events)
            == Option::Some(locals),
    ensures invoke_temporal_safety(cfg, execution),
{
    assert forall|index: nat| index < execution.events.len() implies
        #[trigger] invoke_temporal_at(cfg, execution, index) by {
        invoke_temporal_at_for_exec(cfg, execution, locals, index);
    }
}

pub proof fn invoke_temporal_implies_cut_agreement_at(
    cfg: config_layer::FullConfig,
    execution: execution_layer::BrokerExecution,
    index: nat,
)
    requires invoke_temporal_at(cfg, execution, index),
    ensures invoke_cut_agreement_at(execution, index),
{
    match execution.events[index as int] {
        global_layer::GlobalEvent::InvokeEvent { .. } => {},
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

pub proof fn trace_agreement_for_exec(
    cfg: config_layer::FullConfig,
    execution: execution_layer::BrokerExecution,
    locals: Seq<p0_layer::Event>,
)
    requires
        config_layer::full_config_wf(cfg),
        execution_layer::exec(cfg, execution),
        projection_layer::broker_decode_trace(execution.events)
            == Option::Some(locals),
    ensures trace_agreement(cfg, execution),
{
    prefix_trace_agreement_for_exec(cfg, execution, locals);
    invoke_temporal_safety_for_exec(cfg, execution, locals);
    assert forall|index: nat| index < execution.events.len() implies
        #[trigger] invoke_cut_agreement_at(execution, index) by {
        invoke_temporal_implies_cut_agreement_at(cfg, execution, index);
    }
}

pub proof fn epoch_after_non_crash_is_append_after(
    output: Seq<append_layer::AppendEvent<replay_layer::JournalRecord>>,
    event: global_layer::GlobalEvent,
)
    requires !(event is Crash),
    ensures projection_layer::global_epoch_io_after(output, event)
        == projection_layer::append_after(output, event),
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
        | global_layer::GlobalEvent::BeginScan
        | global_layer::GlobalEvent::FinishScan
        | global_layer::GlobalEvent::TruncateTail
        | global_layer::GlobalEvent::AbortScan
        | global_layer::GlobalEvent::BeginRecover
        | global_layer::GlobalEvent::FinishRecover => {},
        global_layer::GlobalEvent::Crash => { assert(false); },
    }
}

pub proof fn global_subrange_succ_push(
    events: Seq<global_layer::GlobalEvent>,
    left: nat,
    right: nat,
)
    requires left < right, right <= events.len(),
    ensures events.subrange(left as int, right as int)
        == events.subrange(left as int, (right - 1) as int).push(
            events[(right - 1) as int],
        ),
{
    let whole = events.subrange(left as int, right as int);
    let prior = events.subrange(left as int, (right - 1) as int);
    let appended = prior.push(events[(right - 1) as int]);
    assert(whole.len() == right - left);
    assert(prior.len() == right - 1 - left);
    assert(appended.len() == whole.len());
    assert forall|index: int| 0 <= index < whole.len() implies
        whole[index] == appended[index] by {
        if index < prior.len() {
            assert(whole[index] == events[left as int + index]);
            assert(prior[index] == events[left as int + index]);
        } else {
            assert(index == prior.len());
            assert(left + index == right - 1);
            assert(appended[index] == events[(right - 1) as int]);
            assert(whole[index] == events[(right - 1) as int]);
        }
    }
    assert(whole =~= appended);
}

pub proof fn current_epoch_empty_at_boundary(
    events: Seq<global_layer::GlobalEvent>,
    left: nat,
)
    requires
        left <= events.len(),
        left == 0 || events[(left - 1) as int] is Crash,
    ensures projection_layer::global_current_epoch_io(
        events.take(left as int),
    ) == Seq::<append_layer::AppendEvent<replay_layer::JournalRecord>>::empty(),
{
    if left == 0 {
        assert(events.take(0) =~=
            Seq::<global_layer::GlobalEvent>::empty());
    } else {
        let prior = events.take((left - 1) as int);
        let crash = events[(left - 1) as int];
        assert(crash is Crash);
        assert(events.take(left as int) =~= prior.push(crash));
        projection_layer::global_current_epoch_io_push(prior, crash);
    }
}

pub proof fn global_current_epoch_is_interval_append(
    events: Seq<global_layer::GlobalEvent>,
    left: nat,
    right: nat,
)
    requires
        left <= right,
        right <= events.len(),
        no_crash_between(events, left, right),
        left == 0 || events[(left - 1) as int] is Crash,
    ensures projection_layer::global_current_epoch_io(
        events.take(right as int),
    ) == interval_append_projection(events, left, right),
    decreases right - left,
{
    if right == left {
        current_epoch_empty_at_boundary(events, left);
        assert(events.subrange(left as int, right as int) =~=
            Seq::<global_layer::GlobalEvent>::empty());
    } else {
        let prior_right: nat = (right - 1) as nat;
        let event = events[prior_right as int];
        assert(left <= prior_right);
        assert(no_crash_between(events, left, prior_right)) by {
            assert forall|index: nat|
                left <= index && index < prior_right implies
                    !(#[trigger] events[index as int] is Crash) by {}
        }
        assert(!(event is Crash));
        global_current_epoch_is_interval_append(
            events, left, prior_right,
        );
        global_subrange_succ_push(events, left, right);
        let prior_events = events.take(prior_right as int);
        assert(events.take(right as int) =~= prior_events.push(event));
        projection_layer::global_current_epoch_io_push(
            prior_events, event,
        );
        projection_layer::pi_append_push(
            events.subrange(left as int, prior_right as int), event,
        );
        epoch_after_non_crash_is_append_after(
            projection_layer::pi_append(
                events.subrange(left as int, prior_right as int),
            ),
            event,
        );
    }
}

pub proof fn crash_free_interval_classified_at_for_exec(
    cfg: config_layer::FullConfig,
    execution: execution_layer::BrokerExecution,
    locals: Seq<p0_layer::Event>,
    left: nat,
    right: nat,
)
    requires
        config_layer::full_config_wf(cfg),
        execution_layer::exec(cfg, execution),
        projection_layer::broker_decode_trace(execution.events)
            == Option::Some(locals),
    ensures crash_free_interval_classified_at(
        cfg, execution, left, right,
    ),
{
    if maximal_crash_free_interval(execution.events, left, right) {
        execution_layer::decoded_exec_refines_local_run(
            cfg, execution, locals,
        );
        execution_layer::exact_config_run_correspondence_at(
            cfg, execution, locals, right,
        );
        let global_prefix = execution.events.take(right as int);
        let local_prefix = locals.take(right as int);
        p0_layer::executable_prefix(cfg, locals, right);
        bridge_layer::current_epoch_shape_for_run(cfg, local_prefix);
        decoded_prefix_exact(execution.events, locals, right);
        projection_layer::encoded_current_epoch_io(local_prefix);
        global_current_epoch_is_interval_append(
            execution.events, left, right,
        );
        assert(projection_layer::global_current_epoch_io(global_prefix)
            == bridge_layer::current_epoch_io(local_prefix));
        assert(execution.configs[right as int]
            == p0_layer::run(cfg, local_prefix));
        assert(bridge_layer::current_epoch_classified(
            cfg, local_prefix,
        ));
    }
}

pub proof fn crash_free_intervals_classified_for_exec(
    cfg: config_layer::FullConfig,
    execution: execution_layer::BrokerExecution,
    locals: Seq<p0_layer::Event>,
)
    requires
        config_layer::full_config_wf(cfg),
        execution_layer::exec(cfg, execution),
        projection_layer::broker_decode_trace(execution.events)
            == Option::Some(locals),
    ensures crash_free_intervals_classified(cfg, execution),
{
    assert forall|left: nat, right: nat|
        #[trigger] crash_free_interval_classified_at(
            cfg, execution, left, right,
        ) by {
        crash_free_interval_classified_at_for_exec(
            cfg, execution, locals, left, right,
        );
    }
}

pub proof fn all_configurations_safe_for_exec(
    cfg: config_layer::FullConfig,
    execution: execution_layer::BrokerExecution,
)
    requires
        config_layer::full_config_wf(cfg),
        execution_layer::exec(cfg, execution),
    ensures all_configurations_safe(cfg, execution),
{
    execution_layer::every_exec_config_preserves_local_inductive_invariant(
        cfg, execution,
    );
    assert forall|index: nat| index < execution.configs.len() implies
        #[trigger] contract_layer::broker_contract_invariant(
            cfg, execution.configs[index as int],
        )
        && contract_layer::local_inductive_invariant(
            cfg, execution.configs[index as int],
        ) by {
        assert(contract_layer::local_inductive_invariant(
            cfg, execution.configs[index as int],
        ));
    }
}

pub proof fn global_append_protocol_for_exec(
    cfg: config_layer::FullConfig,
    execution: execution_layer::BrokerExecution,
    locals: Seq<p0_layer::Event>,
)
    requires
        config_layer::full_config_wf(cfg),
        execution_layer::exec(cfg, execution),
        projection_layer::broker_decode_trace(execution.events)
            == Option::Some(locals),
    ensures projection_layer::global_append_protocol_prefix(
        execution.events,
    ),
{
    execution_layer::decoded_exec_refines_local_run(
        cfg, execution, locals,
    );
    bridge_layer::b2_append_protocol_bridge_safety(cfg, locals);
    projection_layer::broker_decode_trace_inverse(
        execution.events, locals,
    );
    projection_layer::encoded_global_append_project(locals);
}

pub proof fn recovery_obligation_at_for_exec(
    cfg: config_layer::FullConfig,
    execution: execution_layer::BrokerExecution,
    locals: Seq<p0_layer::Event>,
    index: nat,
)
    requires
        config_layer::full_config_wf(cfg),
        execution_layer::exec(cfg, execution),
        projection_layer::broker_decode_trace(execution.events)
            == Option::Some(locals),
        index < execution.events.len(),
    ensures recovery_obligation_at(cfg, execution, index),
{
    execution_layer::decoded_exec_refines_local_run(
        cfg, execution, locals,
    );
    execution_layer::every_exec_config_preserves_local_inductive_invariant(
        cfg, execution,
    );
    decoded_event_at(execution.events, locals, index);
    let global = execution.events[index as int];
    let local = locals[index as int];
    let before = execution.configs[index as int];
    let after = execution.configs[(index + 1) as int];
    assert(execution_layer::broker_step(cfg, before, global, after));
    execution_layer::broker_step_is_local_apply(
        cfg, before, global, local, after,
    );
    assert(contract_layer::local_inductive_invariant(cfg, before));
    assert(p3_layer::p3_invariant(cfg, before));
    assert(p2_layer::p2_invariant(cfg, before));
    match global {
            global_layer::GlobalEvent::BrokerLinearize { record } => {
                match local {
                    p0_layer::Event::BrokerLinearize {
                        record: local_record,
                    } => {
                        assert(local_record == record);
                        if before.core.broker.mode
                            == record_layer::Mode::Recovering
                        {
                            p3_layer::recovering_linearize_is_source_preserving_repair(
                                cfg, before, record,
                            );
                        }
                    },
                    _ => { assert(false); },
                }
            },
            global_layer::GlobalEvent::Crash => {
                match local {
                    p0_layer::Event::Crash => {
                        p3_layer::crash_preserves_commit_sources(cfg, before);
                    },
                    _ => { assert(false); },
                }
            },
            global_layer::GlobalEvent::FinishRecover => {
                match local {
                    p0_layer::Event::FinishRecover => {
                        assert(p0_layer::control_enabled(
                            cfg, before, local,
                        ));
                        assert(record_layer::recovery_agreement(
                            config_layer::erase_config(cfg), before.core,
                        ));
                    },
                    _ => { assert(false); },
                }
            },
        _ => {},
    }
}

pub proof fn recovery_transition_obligations_for_exec(
    cfg: config_layer::FullConfig,
    execution: execution_layer::BrokerExecution,
    locals: Seq<p0_layer::Event>,
)
    requires
        config_layer::full_config_wf(cfg),
        execution_layer::exec(cfg, execution),
        projection_layer::broker_decode_trace(execution.events)
            == Option::Some(locals),
    ensures recovery_transition_obligations(cfg, execution),
{
    assert forall|index: nat| index < execution.events.len() implies
        #[trigger] recovery_obligation_at(cfg, execution, index) by {
        recovery_obligation_at_for_exec(cfg, execution, locals, index);
    }
}

pub proof fn global_uncontrolled_invocations_bounded_for_exec(
    cfg: config_layer::FullConfig,
    execution: execution_layer::BrokerExecution,
    locals: Seq<p0_layer::Event>,
)
    requires
        config_layer::full_config_wf(cfg),
        execution_layer::exec(cfg, execution),
        projection_layer::broker_decode_trace(execution.events)
            == Option::Some(locals),
    ensures global_uncontrolled_invocations_bounded(
        cfg, execution.events,
    ),
{
    execution_layer::decoded_exec_refines_local_run(
        cfg, execution, locals,
    );
    execution_layer::every_exec_config_preserves_local_inductive_invariant(
        cfg, execution,
    );
    p0_layer::run_history_agreement(cfg, locals);
    projection_layer::decoded_broker_projection_agreement(
        execution.events, locals,
    );
    let length = execution.events.len();
    let final_state = execution.configs[length as int];
    assert(execution.configs.len() == length + 1);
    assert(final_state == execution.configs.last());
    assert(final_state == p0_layer::run(cfg, locals));
    assert(contract_layer::local_inductive_invariant(cfg, final_state));
    assert(contract_layer::broker_contract_invariant(cfg, final_state));
    assert(contract_layer::retry_discipline_clause(cfg, final_state));
    assert(p2_layer::aggregate_retry_bounds(cfg, final_state));
    assert forall|request: replay_layer::RequestId|
        config_layer::erase_config(cfg).request_class[request]
                == replay_layer::RetryClass::Uncontrolled
            implies #[trigger] p2_layer::request_invoke_count(
                projection_layer::pi_physical(execution.events), request,
            ) <= 1 by {
        assert(final_state.physical.physical
            == projection_layer::pi_physical(execution.events));
        assert(p2_layer::request_invoke_count(
            final_state.physical.physical, request,
        ) <= 1);
    }
}

pub proof fn global_terminal_uniqueness_for_exec(
    cfg: config_layer::FullConfig,
    execution: execution_layer::BrokerExecution,
    locals: Seq<p0_layer::Event>,
)
    requires
        config_layer::full_config_wf(cfg),
        execution_layer::exec(cfg, execution),
        projection_layer::broker_decode_trace(execution.events)
            == Option::Some(locals),
    ensures global_terminal_uniqueness(execution.events),
{
    execution_layer::decoded_exec_refines_local_run(
        cfg, execution, locals,
    );
    execution_layer::every_exec_config_preserves_local_inductive_invariant(
        cfg, execution,
    );
    p0_layer::run_history_agreement(cfg, locals);
    projection_layer::decoded_broker_projection_agreement(
        execution.events, locals,
    );
    let length = execution.events.len();
    let final_state = execution.configs[length as int];
    assert(execution.configs.len() == length + 1);
    assert(final_state == execution.configs.last());
    assert(final_state == p0_layer::run(cfg, locals));
    assert(contract_layer::local_inductive_invariant(cfg, final_state));
    assert(contract_layer::broker_contract_invariant(cfg, final_state));
    assert(contract_layer::terminal_uniqueness_clause(cfg, final_state));
    projection_layer::pi_logical_is_journal_projection(execution.events);
    assert forall|request: replay_layer::RequestId|
        #[trigger] replay_layer::terminal_count(
            projection_layer::pi_journal(execution.events), request,
        ) <= 1 by {
        assert(replay_layer::replay_phase_unique_ok(
            config_layer::erase_config(cfg),
            final_state.core.evidence.records,
        ));
        assert(final_state.core.evidence.records
            == projection_layer::pi_journal(execution.events));
    }
}

pub proof fn commit_provenance_for_request(
    cfg: config_layer::FullConfig,
    execution: execution_layer::BrokerExecution,
    request: replay_layer::RequestId,
)
    requires
        execution.configs.len() == execution.events.len() + 1,
        {
            let final_state = execution.configs[
                execution.events.len() as int
            ];
            &&& final_state.physical.physical
                == projection_layer::pi_physical(execution.events)
            &&& p3_layer::commit_source_agreement(cfg, final_state)
            &&& final_state.physical.commit_source.dom()
                == ISet::<replay_layer::RequestId>::full()
        },
    ensures commit_provenance_at(cfg, execution, request),
{
    let final_state = execution.configs[execution.events.len() as int];
    let history = final_state.physical.physical;
    assert(final_state.physical.commit_source.dom().contains(request));
    match final_state.core.broker.durable.committed[request] {
        Option::None => {},
        Option::Some(committed) => {
            let source = final_state.physical.commit_source[request];
            assert(config_layer::erase_config(cfg).valid_results
                .contains((request, committed.value)));
            assert(p1_layer::source_is_delivery(
                history,
                source,
                request,
                committed.attempt,
                replay_layer::Observation::Success(committed.value),
            ));
            match source {
                Option::Some(index) => {
                    match history[index as int] {
                        p0_layer::PhysicalEvent::Delivered {
                            request: delivered_request,
                            attempt: delivered_attempt,
                            observation,
                            journal_cut,
                        } => {
                            assert(delivered_request == request);
                            assert(delivered_attempt == committed.attempt);
                            assert(observation
                                == replay_layer::Observation::Success(
                                    committed.value,
                                ));
                            assert(exists|witness: nat, cut: nat| #![auto] {
                                &&& final_state.physical.commit_source[request]
                                    == Option::Some(witness)
                                &&& witness < projection_layer::pi_physical(
                                    execution.events,
                                ).len()
                                &&& projection_layer::pi_physical(
                                    execution.events,
                                )[witness as int]
                                    == p0_layer::PhysicalEvent::Delivered {
                                        request,
                                        attempt: committed.attempt,
                                        observation:
                                            replay_layer::Observation::Success(
                                                committed.value,
                                            ),
                                        journal_cut: cut,
                                    }
                            }) by {
                                assert(final_state.physical.commit_source[request]
                                    == Option::Some(index));
                                assert(index < projection_layer::pi_physical(
                                    execution.events,
                                ).len());
                                assert(history[index as int]
                                    == projection_layer::pi_physical(
                                        execution.events,
                                    )[index as int]);
                                assert(projection_layer::pi_physical(
                                    execution.events,
                                )[index as int]
                                    == p0_layer::PhysicalEvent::Delivered {
                                        request,
                                        attempt: committed.attempt,
                                        observation:
                                            replay_layer::Observation::Success(
                                                committed.value,
                                            ),
                                        journal_cut,
                                    });
                            }
                        },
                        p0_layer::PhysicalEvent::Invoke { .. } => {
                            assert(false);
                        },
                    }
                },
                Option::None => { assert(false); },
            }
        },
    }
}

pub proof fn global_commit_provenance_for_exec(
    cfg: config_layer::FullConfig,
    execution: execution_layer::BrokerExecution,
    locals: Seq<p0_layer::Event>,
)
    requires
        config_layer::full_config_wf(cfg),
        execution_layer::exec(cfg, execution),
        projection_layer::broker_decode_trace(execution.events)
            == Option::Some(locals),
    ensures global_commit_provenance(cfg, execution),
{
    execution_layer::decoded_exec_refines_local_run(
        cfg, execution, locals,
    );
    execution_layer::every_exec_config_preserves_local_inductive_invariant(
        cfg, execution,
    );
    p0_layer::run_history_agreement(cfg, locals);
    projection_layer::decoded_broker_projection_agreement(
        execution.events, locals,
    );
    let length = execution.events.len();
    let final_state = execution.configs[length as int];
    assert(execution.configs.len() == length + 1);
    assert(final_state == execution.configs.last());
    assert(final_state == p0_layer::run(cfg, locals));
    assert(final_state.core.evidence.records
        == projection_layer::pi_journal(execution.events));
    assert(final_state.physical.physical
        == projection_layer::pi_physical(execution.events));
    assert(contract_layer::local_inductive_invariant(cfg, final_state));
    assert(p3_layer::p3_invariant(cfg, final_state));
    assert(p2_layer::p2_invariant(cfg, final_state));
    assert(p1_layer::p1_invariant(cfg, final_state));
    assert(p0_layer::p0_invariant(cfg, final_state));
    assert(p3_layer::commit_source_agreement(cfg, final_state));
    assert(final_state.physical.commit_source.dom()
        == ISet::<replay_layer::RequestId>::full());
    assert forall|request: replay_layer::RequestId|
        #[trigger] commit_provenance_at(cfg, execution, request) by {
        commit_provenance_for_request(cfg, execution, request);
    }
}

pub proof fn t1_global_corollaries_for_exec(
    cfg: config_layer::FullConfig,
    execution: execution_layer::BrokerExecution,
    locals: Seq<p0_layer::Event>,
)
    requires
        config_layer::full_config_wf(cfg),
        execution_layer::exec(cfg, execution),
        projection_layer::broker_decode_trace(execution.events)
            == Option::Some(locals),
    ensures t1_global_corollaries(cfg, execution),
{
    invoke_temporal_safety_for_exec(cfg, execution, locals);
    global_uncontrolled_invocations_bounded_for_exec(
        cfg, execution, locals,
    );
    global_terminal_uniqueness_for_exec(cfg, execution, locals);
    global_commit_provenance_for_exec(cfg, execution, locals);
}

// The non-generic core is convenient for later refinement layers.  Its only
// semantic premises are configuration well-formedness and membership in the
// exact relational Broker execution relation.
pub proof fn t1_parameterized_broker_safety_core(
    cfg: config_layer::FullConfig,
    execution: execution_layer::BrokerExecution,
)
    requires
        config_layer::full_config_wf(cfg),
        execution_layer::exec(cfg, execution),
    ensures t1_parameterized_safety_statement(cfg, execution),
{
    execution_layer::every_exec_decodes_to_admissible_local_trace(
        cfg, execution,
    );
    match projection_layer::broker_decode_trace(execution.events) {
        Option::None => {},
        Option::Some(locals) => {
            trace_agreement_for_exec(cfg, execution, locals);
            global_append_protocol_for_exec(cfg, execution, locals);
            all_configurations_safe_for_exec(cfg, execution);
            crash_free_intervals_classified_for_exec(
                cfg, execution, locals,
            );
            recovery_transition_obligations_for_exec(
                cfg, execution, locals,
            );
            t1_global_corollaries_for_exec(cfg, execution, locals);
        },
    }
}

// Exported paper theorem.  A remains completely parametric: T1 establishes
// Broker safety before any adapter-specific rely or effect interpretation is
// selected.
pub proof fn t1_parameterized_broker_safety<A>(
    cfg: PaperConfig<A>,
    execution: execution_layer::BrokerExecution,
)
    requires
        paper_config_wf(cfg),
        execution_layer::exec(paper_broker_config(cfg), execution),
    ensures t1_parameterized_safety_statement(
        paper_broker_config(cfg), execution,
    ),
{
    t1_parameterized_broker_safety_core(
        paper_broker_config(cfg), execution,
    );
}

// Prefix closure is exported separately so downstream simulations can cite
// the exact relational prefix, its T1 theorem, and the original execution's
// agreement/configuration at the same label boundary.
pub proof fn t1_prefix_trace_agreement(
    cfg: config_layer::FullConfig,
    execution: execution_layer::BrokerExecution,
    length: nat,
)
    requires
        config_layer::full_config_wf(cfg),
        execution_layer::exec(cfg, execution),
        length <= execution.events.len(),
    ensures
        execution_layer::exec(
            cfg, execution_layer::execution_prefix(execution, length),
        ),
        t1_parameterized_safety_statement(
            cfg, execution_layer::execution_prefix(execution, length),
        ),
        trace_agreement_at(cfg, execution, length),
        contract_layer::broker_contract_invariant(
            cfg, execution.configs[length as int],
        ),
{
    t1_parameterized_broker_safety_core(cfg, execution);
    execution_layer::exec_prefix(cfg, execution, length);
    t1_parameterized_broker_safety_core(
        cfg, execution_layer::execution_prefix(execution, length),
    );
    assert(trace_agreement(cfg, execution));
    assert(all_configurations_safe(cfg, execution));
    assert(length < execution.configs.len());
}

} // verus!
