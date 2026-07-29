use vstd::prelude::*;

#[path = "t6_deduplicated_invariant.rs"]
pub mod t6_dd1_layer;

verus! {

use t6_dd1_layer::*;
use t6_dd1_layer::t6_dd0_layer;
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

// T6-DD2 makes DD1's universal safety theorem operationally non-vacuous.
// Attempt 1 is invoked and silently decides the stable key as Applied. A
// crash loses its reply before any Outcome is durable. Recovery starts
// attempt 2 with the same key; the service replays the memoized Success, and
// the Broker durably records Outcome and Commit for attempt 2. The adapter's
// one silent decision is the only event erased by the global projection.

proof fn dd2_global_trace_push(
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

pub open spec fn dd2_zero_adapter_execution(
    request: replay_layer::RequestId,
    initial_slot: Option<replay_layer::Value>,
) -> DDAdapterExecution {
    DDAdapterExecution {
        configs: Seq::empty().push(dd_initial_state(request, initial_slot)),
        events: Seq::empty(),
    }
}

pub open spec fn dd2_extend_adapter_execution(
    execution: DDAdapterExecution,
    event: DDAdapterEvent,
) -> DDAdapterExecution {
    let before = execution.configs.last();
    DDAdapterExecution {
        configs: execution.configs.push(dd_apply(before, event)),
        events: execution.events.push(event),
    }
}

pub proof fn dd2_zero_adapter_execution_exec(
    request: replay_layer::RequestId,
    initial_slot: Option<replay_layer::Value>,
)
    ensures dd_exec(
        request,
        initial_slot,
        dd2_zero_adapter_execution(request, initial_slot),
    ),
{
}

pub proof fn dd2_extend_adapter_execution_exec(
    request: replay_layer::RequestId,
    initial_slot: Option<replay_layer::Value>,
    execution: DDAdapterExecution,
    event: DDAdapterEvent,
)
    requires
        dd_exec(request, initial_slot, execution),
        dd_enabled(execution.configs.last(), event),
    ensures
        dd_exec(
            request,
            initial_slot,
            dd2_extend_adapter_execution(execution, event),
        ),
        dd2_extend_adapter_execution(execution, event).events.len()
            == execution.events.len() + 1,
        dd_global_trace(
            dd2_extend_adapter_execution(execution, event).events,
        ) == match event {
            DDAdapterEvent::Observe { event: global } => {
                dd_global_trace(execution.events).push(global)
            },
            DDAdapterEvent::ServiceDecide { .. } => {
                dd_global_trace(execution.events)
            },
        },
{
    let extended = dd2_extend_adapter_execution(execution, event);
    let old_len = execution.events.len();
    assert(execution.configs.len() == old_len + 1);
    assert(execution.configs.last() == execution.configs[old_len as int]);
    assert forall|index: nat| index < extended.events.len() implies
        #[trigger] dd_step(
            extended.configs[index as int],
            extended.events[index as int],
            extended.configs[(index + 1) as int],
        ) by {
        if index < old_len {
            assert(extended.events[index as int]
                == execution.events[index as int]);
            assert(extended.configs[index as int]
                == execution.configs[index as int]);
            assert(extended.configs[(index + 1) as int]
                == execution.configs[(index + 1) as int]);
        } else {
            assert(index == old_len);
            assert(extended.events[index as int] == event);
            assert(extended.configs[index as int]
                == execution.configs.last());
            assert(extended.configs[(index + 1) as int]
                == dd_apply(execution.configs.last(), event));
        }
    }
    dd2_global_trace_push(execution.events, event);
}

pub open spec fn dd2_observe_full_append(
    execution: DDAdapterExecution,
    record: replay_layer::JournalRecord,
    cut: nat,
) -> DDAdapterExecution {
    let staged = dd2_extend_adapter_execution(
        execution,
        DDAdapterEvent::Observe {
            event: global_layer::GlobalEvent::WalStage { record },
        },
    );
    let written = dd2_extend_adapter_execution(
        staged,
        DDAdapterEvent::Observe {
            event: global_layer::GlobalEvent::WalWriteFull { record },
        },
    );
    dd2_extend_adapter_execution(
        written,
        DDAdapterEvent::Observe {
            event: global_layer::GlobalEvent::WalFlushAck { cut },
        },
    )
}

pub proof fn dd2_observe_full_append_exec(
    request: replay_layer::RequestId,
    initial_slot: Option<replay_layer::Value>,
    execution: DDAdapterExecution,
    record: replay_layer::JournalRecord,
    cut: nat,
)
    requires dd_exec(request, initial_slot, execution),
    ensures
        dd_exec(
            request,
            initial_slot,
            dd2_observe_full_append(execution, record, cut),
        ),
        dd2_observe_full_append(execution, record, cut).events.len()
            == execution.events.len() + 3,
        dd_global_trace(
            dd2_observe_full_append(execution, record, cut).events,
        ) == dd_global_trace(execution.events)
            .push(global_layer::GlobalEvent::WalStage { record })
            .push(global_layer::GlobalEvent::WalWriteFull { record })
            .push(global_layer::GlobalEvent::WalFlushAck { cut }),
{
    let stage = DDAdapterEvent::Observe {
        event: global_layer::GlobalEvent::WalStage { record },
    };
    let staged = dd2_extend_adapter_execution(execution, stage);
    assert(dd_enabled(execution.configs.last(), stage));
    dd2_extend_adapter_execution_exec(
        request, initial_slot, execution, stage,
    );
    let write = DDAdapterEvent::Observe {
        event: global_layer::GlobalEvent::WalWriteFull { record },
    };
    let written = dd2_extend_adapter_execution(staged, write);
    assert(dd_enabled(staged.configs.last(), write));
    dd2_extend_adapter_execution_exec(
        request, initial_slot, staged, write,
    );
    let flush = DDAdapterEvent::Observe {
        event: global_layer::GlobalEvent::WalFlushAck { cut },
    };
    assert(dd_enabled(written.configs.last(), flush));
    dd2_extend_adapter_execution_exec(
        request, initial_slot, written, flush,
    );
}

pub proof fn dd2_observe_full_append_preserves_service_state(
    execution: DDAdapterExecution,
    record: replay_layer::JournalRecord,
    cut: nat,
)
    ensures
        dd2_observe_full_append(execution, record, cut)
            .configs.last().mode == execution.configs.last().mode,
        dd2_observe_full_append(execution, record, cut)
            .configs.last().active == execution.configs.last().active,
        dd2_observe_full_append(execution, record, cut)
            .configs.last().slot == execution.configs.last().slot,
        dd2_observe_full_append(execution, record, cut)
            .configs.last().decisions == execution.configs.last().decisions,
        dd2_observe_full_append(execution, record, cut)
            .configs.last().history == execution.configs.last().history,
        dd2_observe_full_append(execution, record, cut)
            .configs.last().failed_attempts
                == execution.configs.last().failed_attempts,
{
}

pub open spec fn dd2_observe_wal_event(
    execution: DDAdapterExecution,
    local: wal_runtime_layer::WalEvent,
) -> DDAdapterExecution {
    dd2_extend_adapter_execution(
        execution,
        DDAdapterEvent::Observe {
            event: wal_runtime_layer::wal_encode(local),
        },
    )
}

pub proof fn dd2_observe_wal_event_exec(
    request: replay_layer::RequestId,
    initial_slot: Option<replay_layer::Value>,
    execution: DDAdapterExecution,
    local: wal_runtime_layer::WalEvent,
)
    requires
        dd_exec(request, initial_slot, execution),
        dd_enabled(
            execution.configs.last(),
            DDAdapterEvent::Observe {
                event: wal_runtime_layer::wal_encode(local),
            },
        ),
    ensures
        dd_exec(
            request,
            initial_slot,
            dd2_observe_wal_event(execution, local),
        ),
        dd2_observe_wal_event(execution, local).events.len()
            == execution.events.len() + 1,
        dd_global_trace(dd2_observe_wal_event(execution, local).events)
            == dd_global_trace(execution.events).push(
                wal_runtime_layer::wal_encode(local),
            ),
{
    dd2_extend_adapter_execution_exec(
        request,
        initial_slot,
        execution,
        DDAdapterEvent::Observe {
            event: wal_runtime_layer::wal_encode(local),
        },
    );
}

proof fn dd2_observe_wal_event_preserves_decisions(
    execution: DDAdapterExecution,
    local: wal_runtime_layer::WalEvent,
)
    ensures
        dd2_observe_wal_event(execution, local).configs.last().decisions
            == execution.configs.last().decisions,
{
}

pub open spec fn dd2_observe_recovery(
    execution: DDAdapterExecution,
) -> DDAdapterExecution {
    let crashed = dd2_extend_adapter_execution(
        execution,
        DDAdapterEvent::Observe {
            event: global_layer::GlobalEvent::Crash,
        },
    );
    let scanning = dd2_extend_adapter_execution(
        crashed,
        DDAdapterEvent::Observe {
            event: global_layer::GlobalEvent::BeginScan,
        },
    );
    let scanned = dd2_extend_adapter_execution(
        scanning,
        DDAdapterEvent::Observe {
            event: global_layer::GlobalEvent::FinishScan,
        },
    );
    let truncated = dd2_extend_adapter_execution(
        scanned,
        DDAdapterEvent::Observe {
            event: global_layer::GlobalEvent::TruncateTail,
        },
    );
    let recovering = dd2_extend_adapter_execution(
        truncated,
        DDAdapterEvent::Observe {
            event: global_layer::GlobalEvent::BeginRecover,
        },
    );
    dd2_extend_adapter_execution(
        recovering,
        DDAdapterEvent::Observe {
            event: global_layer::GlobalEvent::FinishRecover,
        },
    )
}

pub proof fn dd2_observe_recovery_exec(
    request: replay_layer::RequestId,
    initial_slot: Option<replay_layer::Value>,
    execution: DDAdapterExecution,
)
    requires
        dd_exec(request, initial_slot, execution),
        execution.configs.last().mode == DDAdapterMode::Online,
    ensures
        dd_exec(
            request,
            initial_slot,
            dd2_observe_recovery(execution),
        ),
        dd2_observe_recovery(execution).configs.last().mode
            == DDAdapterMode::Online,
        dd2_observe_recovery(execution).configs.last().active.is_none(),
        dd2_observe_recovery(execution).configs.last().slot
            == execution.configs.last().slot,
        dd2_observe_recovery(execution).configs.last().decisions
            == execution.configs.last().decisions,
        dd2_observe_recovery(execution).configs.last().history
            == execution.configs.last().history,
        dd2_observe_recovery(execution).events.len()
            == execution.events.len() + 6,
        dd_global_trace(dd2_observe_recovery(execution).events)
            == dd_global_trace(execution.events)
                .push(global_layer::GlobalEvent::Crash)
                .push(global_layer::GlobalEvent::BeginScan)
                .push(global_layer::GlobalEvent::FinishScan)
                .push(global_layer::GlobalEvent::TruncateTail)
                .push(global_layer::GlobalEvent::BeginRecover)
                .push(global_layer::GlobalEvent::FinishRecover),
{
    let crash = DDAdapterEvent::Observe {
        event: global_layer::GlobalEvent::Crash,
    };
    let crashed = dd2_extend_adapter_execution(execution, crash);
    assert(dd_enabled(execution.configs.last(), crash));
    dd2_extend_adapter_execution_exec(
        request, initial_slot, execution, crash,
    );
    let begin_scan = DDAdapterEvent::Observe {
        event: global_layer::GlobalEvent::BeginScan,
    };
    let scanning = dd2_extend_adapter_execution(crashed, begin_scan);
    assert(dd_enabled(crashed.configs.last(), begin_scan));
    dd2_extend_adapter_execution_exec(
        request, initial_slot, crashed, begin_scan,
    );
    let finish_scan = DDAdapterEvent::Observe {
        event: global_layer::GlobalEvent::FinishScan,
    };
    let scanned = dd2_extend_adapter_execution(scanning, finish_scan);
    assert(dd_enabled(scanning.configs.last(), finish_scan));
    dd2_extend_adapter_execution_exec(
        request, initial_slot, scanning, finish_scan,
    );
    let truncate = DDAdapterEvent::Observe {
        event: global_layer::GlobalEvent::TruncateTail,
    };
    let truncated = dd2_extend_adapter_execution(scanned, truncate);
    assert(dd_enabled(scanned.configs.last(), truncate));
    dd2_extend_adapter_execution_exec(
        request, initial_slot, scanned, truncate,
    );
    let begin_recover = DDAdapterEvent::Observe {
        event: global_layer::GlobalEvent::BeginRecover,
    };
    let recovering = dd2_extend_adapter_execution(
        truncated, begin_recover,
    );
    assert(dd_enabled(truncated.configs.last(), begin_recover));
    dd2_extend_adapter_execution_exec(
        request, initial_slot, truncated, begin_recover,
    );
    let finish_recover = DDAdapterEvent::Observe {
        event: global_layer::GlobalEvent::FinishRecover,
    };
    assert(dd_enabled(recovering.configs.last(), finish_recover));
    dd2_extend_adapter_execution_exec(
        request, initial_slot, recovering, finish_recover,
    );
}

pub open spec fn dd2_value() -> replay_layer::Value {
    replay_layer::Value { id: 1 }
}

pub open spec fn dd2_key() -> replay_layer::StableKey {
    replay_layer::StableKey { id: 0 }
}

proof fn dd2_singleton_applied_facts(
    decisions: Seq<DDDecisionRecord>,
)
    requires decisions == Seq::empty().push(DDDecisionRecord {
        attempt: 1,
        decision: DDDecision::Applied { value: dd2_value() },
        history_cut: 1,
    }),
    ensures
        dd_has_applied(decisions, dd2_value()),
        dd_has_any_applied(decisions),
{
    assert(decisions.len() == 1);
    assert(decisions[0].decision
        == (DDDecision::Applied { value: dd2_value() }));
    assert(exists|index: int| 0 <= index < decisions.len()
        && #[trigger] decisions[index].decision
            == (DDDecision::Applied { value: dd2_value() })) by {
        let index = 0int;
    }
    assert(exists|index: int| 0 <= index < decisions.len()
        && (#[trigger] decisions[index].decision) is Applied) by {
        let index = 0int;
    }
}

pub open spec fn dd2_authorize_record()
    -> replay_layer::JournalRecord
{
    replay_layer::JournalRecord::Authorize {
        request: dd_request_zero(),
        capability: replay_layer::CapabilityId { id: 0 },
        digest: replay_layer::Digest { id: 0 },
    }
}

pub open spec fn dd2_prepare_record()
    -> replay_layer::JournalRecord
{
    replay_layer::JournalRecord::Prepare {
        request: dd_request_zero(),
        class: replay_layer::RetryClass::Deduplicated,
        digest: replay_layer::Digest { id: 0 },
        key: Option::Some(dd2_key()),
        auth_ref: 1,
    }
}

pub open spec fn dd2_arm_record() -> replay_layer::JournalRecord {
    replay_layer::JournalRecord::Arm {
        request: dd_request_zero(),
        digest: replay_layer::Digest { id: 0 },
        key: Option::Some(dd2_key()),
        prepare_ref: 2,
    }
}

pub open spec fn dd2_start_one_record()
    -> replay_layer::JournalRecord
{
    replay_layer::JournalRecord::Start {
        request: dd_request_zero(),
        attempt: 1,
        digest: replay_layer::Digest { id: 0 },
        key: Option::Some(dd2_key()),
        arm_ref: 3,
    }
}

pub open spec fn dd2_start_two_record()
    -> replay_layer::JournalRecord
{
    replay_layer::JournalRecord::Start {
        request: dd_request_zero(),
        attempt: 2,
        digest: replay_layer::Digest { id: 0 },
        key: Option::Some(dd2_key()),
        arm_ref: 3,
    }
}

pub open spec fn dd2_success_outcome_record()
    -> replay_layer::JournalRecord
{
    replay_layer::JournalRecord::Outcome {
        request: dd_request_zero(),
        attempt: 2,
        observation: replay_layer::Observation::Success(dd2_value()),
        digest: replay_layer::Digest { id: 0 },
        key: Option::Some(dd2_key()),
        start_ref: 5,
    }
}

pub open spec fn dd2_commit_record()
    -> replay_layer::JournalRecord
{
    replay_layer::JournalRecord::CommitRec {
        request: dd_request_zero(),
        attempt: 2,
        value: dd2_value(),
        digest: replay_layer::Digest { id: 0 },
        key: Option::Some(dd2_key()),
        outcome_ref: 6,
    }
}

pub open spec fn dd2_records() -> Seq<replay_layer::JournalRecord> {
    Seq::empty()
        .push(dd2_authorize_record())
        .push(dd2_prepare_record())
        .push(dd2_arm_record())
        .push(dd2_start_one_record())
        .push(dd2_start_two_record())
        .push(dd2_success_outcome_record())
        .push(dd2_commit_record())
}

pub open spec fn dd2_precrash_records()
    -> Seq<replay_layer::JournalRecord>
{
    Seq::empty()
        .push(dd2_authorize_record())
        .push(dd2_prepare_record())
        .push(dd2_arm_record())
        .push(dd2_start_one_record())
}

pub open spec fn dd2_retry_started_records()
    -> Seq<replay_layer::JournalRecord>
{
    dd2_precrash_records().push(dd2_start_two_record())
}

pub open spec fn dd2_success_records()
    -> Seq<replay_layer::JournalRecord>
{
    dd2_retry_started_records().push(dd2_success_outcome_record())
}

pub open spec fn dd2_invoke_one_wal_event()
    -> wal_runtime_layer::WalEvent
{
    wal_runtime_layer::WalEvent::InvokeEvent {
        request: dd_request_zero(),
        attempt: 1,
        call: config_layer::canonical_call(
            dd_full_config(), dd_request_zero(),
        ),
        journal_cut: 4,
        ack_cut: 4,
    }
}

pub open spec fn dd2_invoke_two_wal_event()
    -> wal_runtime_layer::WalEvent
{
    wal_runtime_layer::WalEvent::InvokeEvent {
        request: dd_request_zero(),
        attempt: 2,
        call: config_layer::canonical_call(
            dd_full_config(), dd_request_zero(),
        ),
        journal_cut: 5,
        ack_cut: 5,
    }
}

pub open spec fn dd2_success_two_wal_event()
    -> wal_runtime_layer::WalEvent
{
    wal_runtime_layer::WalEvent::DeliverEvent {
        request: dd_request_zero(),
        attempt: 2,
        observation: replay_layer::Observation::Success(dd2_value()),
        journal_cut: 5,
    }
}

pub open spec fn dd2_retry_history()
    -> Seq<p0_layer::PhysicalEvent>
{
    let cfg = dd_full_config();
    let request = dd_request_zero();
    Seq::empty()
        .push(p0_layer::PhysicalEvent::Invoke {
            request,
            attempt: 1,
            call: config_layer::canonical_call(cfg, request),
            journal_cut: 4,
            ack_cut: 4,
        })
        .push(p0_layer::PhysicalEvent::Invoke {
            request,
            attempt: 2,
            call: config_layer::canonical_call(cfg, request),
            journal_cut: 5,
            ack_cut: 5,
        })
        .push(p0_layer::PhysicalEvent::Delivered {
            request,
            attempt: 2,
            observation: replay_layer::Observation::Success(dd2_value()),
            journal_cut: 5,
        })
}

pub open spec fn dd2_wal_pre_crash_execution()
    -> wal_runtime_layer::WalExecution
{
    let cfg = dd_full_config();
    let e0 = t6_a0_zero_wal_execution(cfg);
    let e1 = t6_a0_append_full_wal_execution(
        cfg, e0, dd2_authorize_record(),
    );
    let e2 = t6_a0_append_full_wal_execution(
        cfg, e1, dd2_prepare_record(),
    );
    let e3 = t6_a0_append_full_wal_execution(
        cfg, e2, dd2_arm_record(),
    );
    let e4 = t6_a0_append_full_wal_execution(
        cfg, e3, dd2_start_one_record(),
    );
    t6_a0_extend_wal_execution(cfg, e4, dd2_invoke_one_wal_event())
}

pub open spec fn dd2_wal_recovered_execution()
    -> wal_runtime_layer::WalExecution
{
    let cfg = dd_full_config();
    let e5 = dd2_wal_pre_crash_execution();
    let e6 = t6_a0_extend_wal_execution(
        cfg, e5, wal_runtime_layer::WalEvent::Crash,
    );
    let e7 = t6_a0_extend_wal_execution(
        cfg, e6, wal_runtime_layer::WalEvent::BeginScan,
    );
    let e8 = t6_a0_extend_wal_execution(
        cfg, e7, wal_runtime_layer::WalEvent::FinishScan,
    );
    let e9 = t6_a0_extend_wal_execution(
        cfg, e8, wal_runtime_layer::WalEvent::TruncateTail,
    );
    let e10 = t6_a0_extend_wal_execution(
        cfg, e9, wal_runtime_layer::WalEvent::BeginRecover,
    );
    t6_a0_extend_wal_execution(
        cfg, e10, wal_runtime_layer::WalEvent::FinishRecover,
    )
}

pub open spec fn dd2_wal_retry_observed_execution()
    -> wal_runtime_layer::WalExecution
{
    let cfg = dd_full_config();
    let e11 = dd2_wal_recovered_execution();
    let e12 = t6_a0_append_full_wal_execution(
        cfg, e11, dd2_start_two_record(),
    );
    let e13 = t6_a0_extend_wal_execution(
        cfg, e12, dd2_invoke_two_wal_event(),
    );
    t6_a0_extend_wal_execution(
        cfg, e13, dd2_success_two_wal_event(),
    )
}

pub open spec fn dd2_wal_success_outcome_execution()
    -> wal_runtime_layer::WalExecution
{
    t6_a0_append_full_wal_execution(
        dd_full_config(),
        dd2_wal_retry_observed_execution(),
        dd2_success_outcome_record(),
    )
}

pub open spec fn dd2_wal_execution()
    -> wal_runtime_layer::WalExecution
{
    t6_a0_append_full_wal_execution(
        dd_full_config(),
        dd2_wal_success_outcome_execution(),
        dd2_commit_record(),
    )
}

pub open spec fn dd2_adapter_pre_crash_execution()
    -> DDAdapterExecution
{
    let request = dd_request_zero();
    let cfg = dd_full_config();
    let w0 = t6_a0_zero_wal_execution(cfg);
    let a0 = dd2_zero_adapter_execution(request, Option::None);
    let a1 = dd2_observe_full_append(
        a0,
        dd2_authorize_record(),
        wal_runtime_layer::journal_view(w0.configs.last()).len() + 1,
    );
    let w1 = t6_a0_append_full_wal_execution(
        cfg, w0, dd2_authorize_record(),
    );
    let a2 = dd2_observe_full_append(
        a1,
        dd2_prepare_record(),
        wal_runtime_layer::journal_view(w1.configs.last()).len() + 1,
    );
    let w2 = t6_a0_append_full_wal_execution(
        cfg, w1, dd2_prepare_record(),
    );
    let a3 = dd2_observe_full_append(
        a2,
        dd2_arm_record(),
        wal_runtime_layer::journal_view(w2.configs.last()).len() + 1,
    );
    let w3 = t6_a0_append_full_wal_execution(
        cfg, w2, dd2_arm_record(),
    );
    let a4 = dd2_observe_full_append(
        a3,
        dd2_start_one_record(),
        wal_runtime_layer::journal_view(w3.configs.last()).len() + 1,
    );
    let a5 = dd2_observe_wal_event(a4, dd2_invoke_one_wal_event());
    dd2_extend_adapter_execution(
        a5,
        DDAdapterEvent::ServiceDecide {
            decision: DDDecision::Applied { value: dd2_value() },
        },
    )
}

pub open spec fn dd2_adapter_recovered_execution()
    -> DDAdapterExecution
{
    dd2_observe_recovery(dd2_adapter_pre_crash_execution())
}

pub open spec fn dd2_adapter_retry_observed_execution()
    -> DDAdapterExecution
{
    let w11 = dd2_wal_recovered_execution();
    let a12 = dd2_adapter_recovered_execution();
    let a13 = dd2_observe_full_append(
        a12,
        dd2_start_two_record(),
        wal_runtime_layer::journal_view(w11.configs.last()).len() + 1,
    );
    let a14 = dd2_observe_wal_event(a13, dd2_invoke_two_wal_event());
    dd2_observe_wal_event(a14, dd2_success_two_wal_event())
}

pub open spec fn dd2_adapter_success_outcome_execution()
    -> DDAdapterExecution
{
    let w14 = dd2_wal_retry_observed_execution();
    dd2_observe_full_append(
        dd2_adapter_retry_observed_execution(),
        dd2_success_outcome_record(),
        wal_runtime_layer::journal_view(w14.configs.last()).len() + 1,
    )
}

pub open spec fn dd2_adapter_execution()
    -> DDAdapterExecution
{
    let w15 = dd2_wal_success_outcome_execution();
    dd2_observe_full_append(
        dd2_adapter_success_outcome_execution(),
        dd2_commit_record(),
        wal_runtime_layer::journal_view(w15.configs.last()).len() + 1,
    )
}

pub open spec fn dd2_retry_run()
    -> ExternalRun<Option<replay_layer::Value>, DedupWitness>
{
    dd_external_run(dd2_adapter_execution().configs.last())
}

pub open spec fn dd2_terminal_outcome() -> TerminalOutcome {
    TerminalOutcome::Commit { attempt: 2, value: dd2_value() }
}

pub open spec fn dd2_broker_execution()
    -> execution_layer::BrokerExecution
{
    t4_c0_layer::canonical_target_execution(
        dd_full_config(), dd2_wal_execution(),
    )
}

pub open spec fn dd2_final_broker() -> p0_layer::State {
    let target = dd2_broker_execution();
    target.configs[target.events.len() as int]
}

pub open spec fn dd2_explicit_crash_retry_trace_shape(
    events: Seq<global_layer::GlobalEvent>,
) -> bool {
    &&& events.len() == 30
    &&& events[12] == wal_runtime_layer::wal_encode(
        dd2_invoke_one_wal_event(),
    )
    &&& events[13] == global_layer::GlobalEvent::Crash
    &&& events[14] == global_layer::GlobalEvent::BeginScan
    &&& events[15] == global_layer::GlobalEvent::FinishScan
    &&& events[16] == global_layer::GlobalEvent::TruncateTail
    &&& events[17] == global_layer::GlobalEvent::BeginRecover
    &&& events[18] == global_layer::GlobalEvent::FinishRecover
    &&& events[22] == wal_runtime_layer::wal_encode(
        dd2_invoke_two_wal_event(),
    )
    &&& events[23] == wal_runtime_layer::wal_encode(
        dd2_success_two_wal_event(),
    )
}

pub proof fn dd2_authorize_is_runtime_enabled()
    ensures wal_runtime_layer::runtime_record_enabled(
        dd_full_config(),
        wal_runtime_layer::initial_configuration(dd_full_config()),
        dd2_authorize_record(),
    ),
{
}

pub proof fn dd2_wal_pre_crash_execution_exec()
    ensures
        wal_runtime_layer::exec(
            dd_full_config(), dd2_wal_pre_crash_execution(),
        ),
        dd2_wal_pre_crash_execution().events.len() == 13,
        dd2_wal_pre_crash_execution().configs.last().runtime.mode
            == record_layer::Mode::Online,
        dd2_wal_pre_crash_execution().configs.last().runtime.slot
            == (record_layer::ExecSlot::InFlight {
                request: dd_request_zero(), attempt: 1,
            }),
        wal_runtime_layer::wal_quiescent(
            dd2_wal_pre_crash_execution().configs.last(),
        ),
        wal_runtime_layer::journal_view(
            dd2_wal_pre_crash_execution().configs.last(),
        ) == dd2_precrash_records(),
        dd2_wal_pre_crash_execution().configs.last().evidence.physical
            == dd2_retry_history().take(1),
{
    let cfg = dd_full_config();
    let request = dd_request_zero();
    dd_full_config_is_well_formed();
    reveal_with_fuel(replay_layer::replay, 8);
    reveal_with_fuel(replay_layer::authorize_lsn, 8);
    reveal_with_fuel(replay_layer::prepare_lsn, 8);
    reveal_with_fuel(replay_layer::arm_lsn, 8);
    reveal_with_fuel(replay_layer::start_lsn, 8);
    reveal_with_fuel(replay_layer::started_count, 8);
    reveal_with_fuel(replay_layer::outcome_count, 8);
    reveal_with_fuel(replay_layer::outcome_observation, 8);
    let e0 = t6_a0_zero_wal_execution(cfg);
    t6_a0_zero_wal_execution_exec(cfg);
    dd2_authorize_is_runtime_enabled();
    let e1 = t6_a0_append_full_wal_execution(
        cfg, e0, dd2_authorize_record(),
    );
    t6_a0_append_full_wal_execution_exec(
        cfg, e0, dd2_authorize_record(),
    );
    assert(wal_runtime_layer::runtime_record_enabled(
        cfg, e1.configs.last(), dd2_prepare_record(),
    ));
    let e2 = t6_a0_append_full_wal_execution(
        cfg, e1, dd2_prepare_record(),
    );
    t6_a0_append_full_wal_execution_exec(
        cfg, e1, dd2_prepare_record(),
    );
    assert(wal_runtime_layer::runtime_record_enabled(
        cfg, e2.configs.last(), dd2_arm_record(),
    ));
    let e3 = t6_a0_append_full_wal_execution(
        cfg, e2, dd2_arm_record(),
    );
    t6_a0_append_full_wal_execution_exec(
        cfg, e2, dd2_arm_record(),
    );
    assert(wal_runtime_layer::runtime_record_enabled(
        cfg, e3.configs.last(), dd2_start_one_record(),
    ));
    let e4 = t6_a0_append_full_wal_execution(
        cfg, e3, dd2_start_one_record(),
    );
    t6_a0_append_full_wal_execution_exec(
        cfg, e3, dd2_start_one_record(),
    );
    assert(e4.configs.last().runtime.slot
        == record_layer::ExecSlot::Ready { request, attempt: 1 });
    let invoke1 = dd2_invoke_one_wal_event();
    assert(wal_runtime_layer::admissibly_enabled(
        cfg, e4.configs.last(), invoke1,
    ));
    t6_a0_extend_wal_execution_exec(cfg, e4, invoke1);
    let e5 = t6_a0_extend_wal_execution(cfg, e4, invoke1);
    assert(e5 == dd2_wal_pre_crash_execution());
    assert(e5.configs.last().runtime.slot
        == record_layer::ExecSlot::InFlight { request, attempt: 1 });
    assert(wal_runtime_layer::journal_view(e5.configs.last())
        == dd2_precrash_records());
    assert(e5.configs.last().evidence.physical
        == dd2_retry_history().take(1));
}

proof fn dd2_precrash_recovery_complete()
    ensures query_layer::recovery_complete_j(
        config_layer::erase_config(dd_full_config()),
        dd2_precrash_records(),
    ),
{
    let cfg = dd_full_config();
    let erased = config_layer::erase_config(cfg);
    let journal = dd2_precrash_records();
    dd_full_config_is_well_formed();
    reveal_with_fuel(replay_layer::replay, 8);
    reveal_with_fuel(replay_layer::started_count, 8);
    reveal_with_fuel(replay_layer::outcome_count, 8);
    reveal_with_fuel(replay_layer::outcome_observation, 8);
    reveal_with_fuel(replay_layer::arm_lsn, 8);
    assert forall|request: replay_layer::RequestId|
        !#[trigger] query_layer::unsafe_uncontrolled_j(
            erased, journal, request,
        )
        && !(replay_layer::replay(erased, journal).phase[request]
            == replay_layer::Phase::Armed
            && replay_layer::failure_conclusive(
                erased, journal, request,
            )) by {
        assert(erased.request_class[request]
            == replay_layer::RetryClass::Deduplicated);
        assert(!query_layer::unsafe_uncontrolled_j(
            erased, journal, request,
        ));
        if request == dd_request_zero() {
            assert(replay_layer::replay(erased, journal).phase[request]
                == replay_layer::Phase::Armed);
            assert(replay_layer::outcome_count(journal, request, 1) == 0);
            query_layer::outcome_count_zero_implies_no_observation(
                journal, request, 1,
            );
            assert(replay_layer::outcome_observation(
                journal, request, 1,
            ).is_none());
            assert(!replay_layer::failure_conclusive(
                erased, journal, request,
            ));
        } else {
            assert(replay_layer::replay(erased, journal).phase[request]
                == replay_layer::Phase::New);
        }
    }
}

proof fn dd2_start_two_runtime_enabled(
    cfg: config_layer::FullConfig,
    state: wal_runtime_layer::WalConfiguration,
)
    requires
        cfg == dd_full_config(),
        state.runtime.mode == record_layer::Mode::Online,
        state.runtime.slot == record_layer::ExecSlot::Idle,
        wal_runtime_layer::journal_view(state) == dd2_precrash_records(),
    ensures wal_runtime_layer::runtime_record_enabled(
        cfg, state, dd2_start_two_record(),
    ),
{
    let request = dd_request_zero();
    let erased = config_layer::erase_config(cfg);
    let journal = dd2_precrash_records();
    dd_full_config_is_well_formed();
    reveal_with_fuel(replay_layer::replay, 8);
    reveal_with_fuel(replay_layer::started_count, 8);
    reveal_with_fuel(replay_layer::outcome_count, 8);
    reveal_with_fuel(replay_layer::outcome_observation, 8);
    reveal_with_fuel(replay_layer::arm_lsn, 8);
    assert(replay_layer::replay(erased, journal).phase[request]
        == replay_layer::Phase::Armed);
    assert(replay_layer::started_count(journal, request) == 1);
    assert(replay_layer::outcome_count(journal, request, 1) == 0);
    query_layer::outcome_count_zero_implies_no_observation(
        journal, request, 1,
    );
    assert(replay_layer::outcome_observation(journal, request, 1)
        == Option::None);
    assert(!replay_layer::failure_conclusive(erased, journal, request));
    assert(replay_layer::request_fields_match(
        erased,
        request,
        replay_layer::Digest { id: 0 },
        Option::Some(dd2_key()),
    ));
    assert(replay_layer::arm_lsn(journal, request)
        == Option::Some(3));
    assert(replay_layer::ref_is(
        3, replay_layer::arm_lsn(journal, request),
    ));
    assert(2 <= erased.max_attempts[request]);
    assert(erased.request_class[request]
        != replay_layer::RetryClass::Uncontrolled);
    assert(replay_layer::structural_enabled(
        erased, journal, dd2_start_two_record(),
    ));
    assert(record_layer::durable_slot_update(
        erased,
        replay_layer::replay(erased, journal),
        record_layer::Mode::Online,
        record_layer::ExecSlot::Idle,
        dd2_start_two_record(),
    ).is_some());
}

pub proof fn dd2_wal_recovered_execution_exec()
    ensures
        wal_runtime_layer::exec(
            dd_full_config(), dd2_wal_recovered_execution(),
        ),
        dd2_wal_recovered_execution().events.len() == 19,
        dd2_wal_recovered_execution().configs.last().runtime.mode
            == record_layer::Mode::Online,
        dd2_wal_recovered_execution().configs.last().runtime.slot
            == record_layer::ExecSlot::Idle,
        wal_runtime_layer::wal_quiescent(
            dd2_wal_recovered_execution().configs.last(),
        ),
        wal_runtime_layer::journal_view(
            dd2_wal_recovered_execution().configs.last(),
        ) == dd2_precrash_records(),
        dd2_wal_recovered_execution().configs.last().evidence.physical
            == dd2_retry_history().take(1),
{
    let cfg = dd_full_config();
    let e5 = dd2_wal_pre_crash_execution();
    dd2_wal_pre_crash_execution_exec();
    let crash = wal_runtime_layer::WalEvent::Crash;
    let e6 = t6_a0_extend_wal_execution(cfg, e5, crash);
    assert(wal_runtime_layer::admissibly_enabled(
        cfg, e5.configs.last(), crash,
    ));
    t6_a0_extend_wal_execution_exec(cfg, e5, crash);
    assert(e6.configs.last().runtime.mode == record_layer::Mode::Crashed);
    assert(e6.configs.last().runtime.slot == record_layer::ExecSlot::Idle);
    let begin_scan = wal_runtime_layer::WalEvent::BeginScan;
    let e7 = t6_a0_extend_wal_execution(cfg, e6, begin_scan);
    assert(wal_runtime_layer::admissibly_enabled(
        cfg, e6.configs.last(), begin_scan,
    ));
    t6_a0_extend_wal_execution_exec(cfg, e6, begin_scan);
    let finish_scan = wal_runtime_layer::WalEvent::FinishScan;
    let e8 = t6_a0_extend_wal_execution(cfg, e7, finish_scan);
    assert(wal_runtime_layer::admissibly_enabled(
        cfg, e7.configs.last(), finish_scan,
    ));
    t6_a0_extend_wal_execution_exec(cfg, e7, finish_scan);
    let truncate = wal_runtime_layer::WalEvent::TruncateTail;
    let e9 = t6_a0_extend_wal_execution(cfg, e8, truncate);
    assert(wal_runtime_layer::admissibly_enabled(
        cfg, e8.configs.last(), truncate,
    ));
    t6_a0_extend_wal_execution_exec(cfg, e8, truncate);
    wal_runtime_layer::parse_full_frames(dd2_precrash_records());
    let begin_recover = wal_runtime_layer::WalEvent::BeginRecover;
    let e10 = t6_a0_extend_wal_execution(cfg, e9, begin_recover);
    assert(wal_runtime_layer::admissibly_enabled(
        cfg, e9.configs.last(), begin_recover,
    ));
    t6_a0_extend_wal_execution_exec(cfg, e9, begin_recover);
    let finish_recover = wal_runtime_layer::WalEvent::FinishRecover;
    dd2_precrash_recovery_complete();
    assert(wal_runtime_layer::admissibly_enabled(
        cfg, e10.configs.last(), finish_recover,
    ));
    t6_a0_extend_wal_execution_exec(cfg, e10, finish_recover);
    let e11 = t6_a0_extend_wal_execution(cfg, e10, finish_recover);
    assert(e11 == dd2_wal_recovered_execution());
    assert(e11.configs.last().runtime.mode == record_layer::Mode::Online);
    assert(e11.configs.last().runtime.slot == record_layer::ExecSlot::Idle);
    assert(wal_runtime_layer::journal_view(e11.configs.last())
        == dd2_precrash_records());
    assert(e11.configs.last().evidence.physical
        == dd2_retry_history().take(1));
}

pub proof fn dd2_wal_retry_observed_execution_exec()
    ensures
        wal_runtime_layer::exec(
            dd_full_config(), dd2_wal_retry_observed_execution(),
        ),
        dd2_wal_retry_observed_execution().events.len() == 24,
        dd2_wal_retry_observed_execution().configs.last().runtime.mode
            == record_layer::Mode::Online,
        dd2_wal_retry_observed_execution().configs.last().runtime.slot
            == (record_layer::ExecSlot::Received {
                request: dd_request_zero(),
                attempt: 2,
                observation: replay_layer::Observation::Success(
                    dd2_value(),
                ),
            }),
        wal_runtime_layer::wal_quiescent(
            dd2_wal_retry_observed_execution().configs.last(),
        ),
        wal_runtime_layer::journal_view(
            dd2_wal_retry_observed_execution().configs.last(),
        ) == dd2_retry_started_records(),
        dd2_wal_retry_observed_execution().configs.last()
            .runtime.store.media
            == wal_runtime_layer::full_frames(dd2_retry_started_records()),
        dd2_wal_retry_observed_execution().configs.last().evidence.records
            == dd2_retry_started_records(),
        dd2_wal_retry_observed_execution().configs.last()
            .evidence.acknowledged_prefix == dd2_retry_started_records(),
        dd2_wal_retry_observed_execution().configs.last().evidence.physical
            == dd2_retry_history(),
{
    let cfg = dd_full_config();
    let request = dd_request_zero();
    let e11 = dd2_wal_recovered_execution();
    dd2_wal_recovered_execution_exec();
    dd2_start_two_runtime_enabled(cfg, e11.configs.last());
    let e12 = t6_a0_append_full_wal_execution(
        cfg, e11, dd2_start_two_record(),
    );
    t6_a0_append_full_wal_execution_exec(
        cfg, e11, dd2_start_two_record(),
    );
    assert(e12.configs.last().runtime.slot
        == record_layer::ExecSlot::Ready { request, attempt: 2 });
    let invoke2 = dd2_invoke_two_wal_event();
    assert(wal_runtime_layer::admissibly_enabled(
        cfg, e12.configs.last(), invoke2,
    ));
    t6_a0_extend_wal_execution_exec(cfg, e12, invoke2);
    let e13 = t6_a0_extend_wal_execution(cfg, e12, invoke2);
    assert(e13.configs.last().runtime.slot
        == record_layer::ExecSlot::InFlight { request, attempt: 2 });
    let success2 = dd2_success_two_wal_event();
    assert(wal_runtime_layer::admissibly_enabled(
        cfg, e13.configs.last(), success2,
    ));
    t6_a0_extend_wal_execution_exec(cfg, e13, success2);
    let e14 = t6_a0_extend_wal_execution(cfg, e13, success2);
    assert(e14 == dd2_wal_retry_observed_execution());
    assert(e14.configs.last().runtime.slot
        == record_layer::ExecSlot::Received {
            request,
            attempt: 2,
            observation: replay_layer::Observation::Success(dd2_value()),
        });
    assert(e14.configs.last().runtime.mode == record_layer::Mode::Online);
    assert(wal_runtime_layer::wal_quiescent(e14.configs.last()));
    assert(wal_runtime_layer::journal_view(e14.configs.last())
        == dd2_retry_started_records());
    assert(e14.configs.last().runtime.store.media
        == wal_runtime_layer::full_frames(dd2_retry_started_records()));
    assert(e14.configs.last().evidence.records
        == dd2_retry_started_records());
    assert(e14.configs.last().evidence.acknowledged_prefix
        == dd2_retry_started_records());
    assert(e14.configs.last().evidence.physical == dd2_retry_history());
}

proof fn dd2_success_outcome_runtime_enabled(
    cfg: config_layer::FullConfig,
    state: wal_runtime_layer::WalConfiguration,
)
    requires
        cfg == dd_full_config(),
        state.runtime.mode == record_layer::Mode::Online,
        state.runtime.slot == (record_layer::ExecSlot::Received {
            request: dd_request_zero(),
            attempt: 2,
            observation: replay_layer::Observation::Success(dd2_value()),
        }),
        wal_runtime_layer::journal_view(state)
            == dd2_retry_started_records(),
    ensures wal_runtime_layer::runtime_record_enabled(
        cfg, state, dd2_success_outcome_record(),
    ),
{
    let request = dd_request_zero();
    let erased = config_layer::erase_config(cfg);
    let journal = dd2_retry_started_records();
    dd_full_config_is_well_formed();
    reveal_with_fuel(replay_layer::replay, 9);
    reveal_with_fuel(replay_layer::started_count, 9);
    reveal_with_fuel(replay_layer::outcome_count, 9);
    reveal_with_fuel(replay_layer::start_lsn, 9);
    assert(replay_layer::replay(erased, journal).phase[request]
        == replay_layer::Phase::Armed);
    assert(replay_layer::started_count(journal, request) == 2);
    assert(replay_layer::outcome_count(journal, request, 2) == 0);
    assert(replay_layer::start_lsn(journal, request, 2)
        == Option::Some(5));
    assert(replay_layer::request_fields_match(
        erased,
        request,
        replay_layer::Digest { id: 0 },
        Option::Some(dd2_key()),
    ));
    assert(erased.valid_results.contains((request, dd2_value())));
    assert(replay_layer::structural_enabled(
        erased, journal, dd2_success_outcome_record(),
    ));
    assert(record_layer::durable_slot_update(
        erased,
        replay_layer::replay(erased, journal),
        record_layer::Mode::Online,
        state.runtime.slot,
        dd2_success_outcome_record(),
    ).is_some());
}

pub proof fn dd2_wal_success_outcome_execution_exec()
    ensures
        wal_runtime_layer::exec(
            dd_full_config(), dd2_wal_success_outcome_execution(),
        ),
        dd2_wal_success_outcome_execution().events.len() == 27,
        dd2_wal_success_outcome_execution().configs.last().runtime.mode
            == record_layer::Mode::Online,
        dd2_wal_success_outcome_execution().configs.last().runtime.slot
            == (record_layer::ExecSlot::ObservedSuccess {
                request: dd_request_zero(),
                attempt: 2,
                value: dd2_value(),
            }),
        wal_runtime_layer::wal_quiescent(
            dd2_wal_success_outcome_execution().configs.last(),
        ),
        wal_runtime_layer::journal_view(
            dd2_wal_success_outcome_execution().configs.last(),
        ) == dd2_success_records(),
        dd2_wal_success_outcome_execution().configs.last()
            .runtime.store.media
            == wal_runtime_layer::full_frames(dd2_success_records()),
        dd2_wal_success_outcome_execution().configs.last().evidence.records
            == dd2_success_records(),
        dd2_wal_success_outcome_execution().configs.last()
            .evidence.acknowledged_prefix == dd2_success_records(),
        dd2_wal_success_outcome_execution().configs.last().evidence.physical
            == dd2_retry_history(),
{
    let cfg = dd_full_config();
    let e14 = dd2_wal_retry_observed_execution();
    dd2_wal_retry_observed_execution_exec();
    dd2_success_outcome_runtime_enabled(cfg, e14.configs.last());
    t6_a0_append_full_wal_execution_exec(
        cfg, e14, dd2_success_outcome_record(),
    );
    let e15 = dd2_wal_success_outcome_execution();
    assert(e15.configs.last().runtime.mode == record_layer::Mode::Online);
    assert(e15.configs.last().runtime.slot
        == record_layer::ExecSlot::ObservedSuccess {
            request: dd_request_zero(),
            attempt: 2,
            value: dd2_value(),
        });
    assert(wal_runtime_layer::wal_quiescent(e15.configs.last()));
    assert(wal_runtime_layer::journal_view(e15.configs.last())
        == dd2_success_records());
    assert(e15.configs.last().runtime.store.media
        == wal_runtime_layer::full_frames(dd2_success_records()));
    assert(e15.configs.last().evidence.records == dd2_success_records());
    assert(e15.configs.last().evidence.acknowledged_prefix
        == dd2_success_records());
    assert(e15.configs.last().evidence.physical == dd2_retry_history());
}

proof fn dd2_commit_runtime_enabled(
    cfg: config_layer::FullConfig,
    state: wal_runtime_layer::WalConfiguration,
)
    requires
        cfg == dd_full_config(),
        state.runtime.mode == record_layer::Mode::Online,
        state.runtime.slot == (record_layer::ExecSlot::ObservedSuccess {
            request: dd_request_zero(),
            attempt: 2,
            value: dd2_value(),
        }),
        wal_runtime_layer::journal_view(state) == dd2_success_records(),
    ensures wal_runtime_layer::runtime_record_enabled(
        cfg, state, dd2_commit_record(),
    ),
{
    let request = dd_request_zero();
    let erased = config_layer::erase_config(cfg);
    let journal = dd2_success_records();
    dd_full_config_is_well_formed();
    reveal_with_fuel(replay_layer::replay, 10);
    reveal_with_fuel(replay_layer::started_count, 10);
    reveal_with_fuel(replay_layer::outcome_count, 10);
    reveal_with_fuel(replay_layer::outcome_observation, 10);
    reveal_with_fuel(replay_layer::outcome_lsn, 10);
    assert(replay_layer::replay(erased, journal).phase[request]
        == replay_layer::Phase::Armed);
    assert(replay_layer::started_count(journal, request) == 2);
    assert(replay_layer::outcome_observation(journal, request, 2)
        == Option::Some(
            replay_layer::Observation::Success(dd2_value()),
        ));
    assert(replay_layer::outcome_lsn(journal, request, 2)
        == Option::Some(6));
    assert(replay_layer::request_fields_match(
        erased,
        request,
        replay_layer::Digest { id: 0 },
        Option::Some(dd2_key()),
    ));
    assert(replay_layer::structural_enabled(
        erased, journal, dd2_commit_record(),
    ));
    assert(record_layer::durable_slot_update(
        erased,
        replay_layer::replay(erased, journal),
        record_layer::Mode::Online,
        state.runtime.slot,
        dd2_commit_record(),
    ).is_some());
}

pub proof fn dd2_wal_execution_exec()
    ensures
        wal_runtime_layer::exec(dd_full_config(), dd2_wal_execution()),
        dd2_wal_execution().events.len() == 30,
        dd2_wal_execution().configs.len() == 31,
        dd2_wal_execution().configs.last().runtime.mode
            == record_layer::Mode::Online,
        dd2_wal_execution().configs.last().runtime.slot
            == record_layer::ExecSlot::Idle,
        wal_runtime_layer::wal_quiescent(
            dd2_wal_execution().configs.last(),
        ),
        wal_runtime_layer::journal_view(
            dd2_wal_execution().configs.last(),
        ) == dd2_records(),
        dd2_wal_execution().configs.last().runtime.store.media
            == wal_runtime_layer::full_frames(dd2_records()),
        dd2_wal_execution().configs.last().evidence.records
            == dd2_records(),
        dd2_wal_execution().configs.last().evidence.physical
            == dd2_retry_history(),
{
    let cfg = dd_full_config();
    let e15 = dd2_wal_success_outcome_execution();
    dd2_wal_success_outcome_execution_exec();
    dd2_commit_runtime_enabled(cfg, e15.configs.last());
    t6_a0_append_full_wal_execution_exec(
        cfg, e15, dd2_commit_record(),
    );
    let e16 = dd2_wal_execution();
    assert(e16.configs.last().runtime.slot == record_layer::ExecSlot::Idle);
    assert(wal_runtime_layer::wal_quiescent(e16.configs.last()));
    assert(wal_runtime_layer::journal_view(e16.configs.last())
        == dd2_records());
    assert(e16.configs.last().runtime.store.media
        == wal_runtime_layer::full_frames(dd2_records()));
    assert(e16.configs.last().evidence.records == dd2_records());
    assert(e16.configs.last().evidence.physical == dd2_retry_history());
}

pub proof fn dd2_adapter_pre_crash_execution_exec()
    ensures
        dd_exec(
            dd_request_zero(),
            Option::None,
            dd2_adapter_pre_crash_execution(),
        ),
        dd2_adapter_pre_crash_execution().events.len() == 14,
        dd_global_trace(dd2_adapter_pre_crash_execution().events)
            == dd2_wal_pre_crash_execution().events,
        dd2_adapter_pre_crash_execution().configs.last().mode
            == DDAdapterMode::Online,
        dd2_adapter_pre_crash_execution().configs.last().active
            == Option::Some(1),
        dd2_adapter_pre_crash_execution().configs.last().slot
            == Option::Some(dd2_value()),
        dd2_adapter_pre_crash_execution().configs.last().history
            == dd2_retry_history().take(1),
        dd2_adapter_pre_crash_execution().configs.last().decisions
            == Seq::empty().push(DDDecisionRecord {
                attempt: 1,
                decision: DDDecision::Applied { value: dd2_value() },
                history_cut: 1,
            }),
{
    let request = dd_request_zero();
    let initial = Option::<replay_layer::Value>::None;
    let cfg = dd_full_config();
    let w0 = t6_a0_zero_wal_execution(cfg);
    let a0 = dd2_zero_adapter_execution(request, initial);
    dd2_zero_adapter_execution_exec(request, initial);
    let cut1 = wal_runtime_layer::journal_view(
        w0.configs.last(),
    ).len() + 1;
    let a1 = dd2_observe_full_append(
        a0, dd2_authorize_record(), cut1,
    );
    let w1 = t6_a0_append_full_wal_execution(
        cfg, w0, dd2_authorize_record(),
    );
    dd2_observe_full_append_exec(
        request, initial, a0, dd2_authorize_record(), cut1,
    );
    assert(dd_global_trace(a1.events) == w1.events);
    let cut2 = wal_runtime_layer::journal_view(
        w1.configs.last(),
    ).len() + 1;
    let a2 = dd2_observe_full_append(
        a1, dd2_prepare_record(), cut2,
    );
    let w2 = t6_a0_append_full_wal_execution(
        cfg, w1, dd2_prepare_record(),
    );
    dd2_observe_full_append_exec(
        request, initial, a1, dd2_prepare_record(), cut2,
    );
    assert(dd_global_trace(a2.events) == w2.events);
    let cut3 = wal_runtime_layer::journal_view(
        w2.configs.last(),
    ).len() + 1;
    let a3 = dd2_observe_full_append(
        a2, dd2_arm_record(), cut3,
    );
    let w3 = t6_a0_append_full_wal_execution(
        cfg, w2, dd2_arm_record(),
    );
    dd2_observe_full_append_exec(
        request, initial, a2, dd2_arm_record(), cut3,
    );
    assert(dd_global_trace(a3.events) == w3.events);
    let cut4 = wal_runtime_layer::journal_view(
        w3.configs.last(),
    ).len() + 1;
    let a4 = dd2_observe_full_append(
        a3, dd2_start_one_record(), cut4,
    );
    let w4 = t6_a0_append_full_wal_execution(
        cfg, w3, dd2_start_one_record(),
    );
    dd2_observe_full_append_exec(
        request, initial, a3, dd2_start_one_record(), cut4,
    );
    assert(dd_global_trace(a4.events) == w4.events);
    let invoke1 = dd2_invoke_one_wal_event();
    let observe1 = DDAdapterEvent::Observe {
        event: wal_runtime_layer::wal_encode(invoke1),
    };
    assert(dd_enabled(a4.configs.last(), observe1));
    dd2_observe_wal_event_exec(request, initial, a4, invoke1);
    let a5 = dd2_observe_wal_event(a4, invoke1);
    let w5 = t6_a0_extend_wal_execution(cfg, w4, invoke1);
    assert(dd_global_trace(a5.events) == w5.events);
    dd1_every_exec_configuration_satisfies_invariant(
        request, initial, a5,
    );
    assert(a5.configs.last().active == Option::Some(1));
    assert(a5.configs.last().history == dd2_retry_history().take(1));
    reveal_with_fuel(p1_layer::invoke_count, 5);
    reveal_with_fuel(p1_layer::delivery_count, 5);
    assert(invoked(a5.configs.last().history, request, 1));
    assert(p1_layer::delivery_count(
        a5.configs.last().history, request, 1,
    ) == 0);
    let decide = DDAdapterEvent::ServiceDecide {
        decision: DDDecision::Applied { value: dd2_value() },
    };
    assert(dd_enabled(a5.configs.last(), decide));
    dd2_extend_adapter_execution_exec(
        request, initial, a5, decide,
    );
    let a6 = dd2_extend_adapter_execution(a5, decide);
    assert(a6 == dd2_adapter_pre_crash_execution());
    assert(dd_global_trace(a6.events) == w5.events);
    assert(a6.configs.last().slot == Option::Some(dd2_value()));
    assert(a6.configs.last().decisions
        == Seq::empty().push(DDDecisionRecord {
            attempt: 1,
            decision: DDDecision::Applied { value: dd2_value() },
            history_cut: 1,
        }));
}

pub proof fn dd2_adapter_recovered_execution_exec()
    ensures
        dd_exec(
            dd_request_zero(),
            Option::None,
            dd2_adapter_recovered_execution(),
        ),
        dd2_adapter_recovered_execution().events.len() == 20,
        dd_global_trace(dd2_adapter_recovered_execution().events)
            == dd2_wal_recovered_execution().events,
        dd2_adapter_recovered_execution().configs.last().mode
            == DDAdapterMode::Online,
        dd2_adapter_recovered_execution().configs.last().active.is_none(),
        dd2_adapter_recovered_execution().configs.last().slot
            == Option::Some(dd2_value()),
        dd2_adapter_recovered_execution().configs.last().history
            == dd2_retry_history().take(1),
        dd2_adapter_recovered_execution().configs.last().decisions
            == dd2_adapter_pre_crash_execution().configs.last().decisions,
{
    let before = dd2_adapter_pre_crash_execution();
    dd2_adapter_pre_crash_execution_exec();
    dd2_observe_recovery_exec(
        dd_request_zero(), Option::None, before,
    );
    assert(dd_global_trace(dd2_adapter_recovered_execution().events)
        == dd2_wal_recovered_execution().events);
}

pub proof fn dd2_adapter_retry_observed_execution_exec()
    ensures
        dd_exec(
            dd_request_zero(),
            Option::None,
            dd2_adapter_retry_observed_execution(),
        ),
        dd2_adapter_retry_observed_execution().events.len() == 25,
        dd_global_trace(dd2_adapter_retry_observed_execution().events)
            == dd2_wal_retry_observed_execution().events,
        dd2_adapter_retry_observed_execution().configs.last().active
            .is_none(),
        dd2_adapter_retry_observed_execution().configs.last().slot
            == Option::Some(dd2_value()),
        dd2_adapter_retry_observed_execution().configs.last().history
            == dd2_retry_history(),
        dd2_adapter_retry_observed_execution().configs.last().decisions
            == dd2_adapter_pre_crash_execution().configs.last().decisions,
{
    let request = dd_request_zero();
    let initial = Option::<replay_layer::Value>::None;
    let w11 = dd2_wal_recovered_execution();
    let a12 = dd2_adapter_recovered_execution();
    dd2_adapter_recovered_execution_exec();
    let cut5 = wal_runtime_layer::journal_view(
        w11.configs.last(),
    ).len() + 1;
    let a13 = dd2_observe_full_append(
        a12, dd2_start_two_record(), cut5,
    );
    dd2_observe_full_append_exec(
        request, initial, a12, dd2_start_two_record(), cut5,
    );
    dd2_observe_full_append_preserves_service_state(
        a12, dd2_start_two_record(), cut5,
    );
    reveal_with_fuel(p1_layer::invoke_count, 5);
    reveal_with_fuel(p1_layer::delivery_count, 5);
    assert(p1_layer::invoke_count(
        a13.configs.last().history, request, 2,
    ) == 0);
    assert(p1_layer::delivery_count(
        a13.configs.last().history, request, 2,
    ) == 0);
    let invoke2 = dd2_invoke_two_wal_event();
    let observe2 = DDAdapterEvent::Observe {
        event: wal_runtime_layer::wal_encode(invoke2),
    };
    assert(dd_enabled(a13.configs.last(), observe2));
    dd2_observe_wal_event_exec(request, initial, a13, invoke2);
    dd2_observe_wal_event_preserves_decisions(a13, invoke2);
    let a14 = dd2_observe_wal_event(a13, invoke2);
    assert(a14.configs.last().active == Option::Some(2));
    assert(a12.configs.last().decisions
        == dd2_adapter_pre_crash_execution().configs.last().decisions);
    assert(dd2_adapter_pre_crash_execution().configs.last().decisions
        == Seq::empty().push(DDDecisionRecord {
            attempt: 1,
            decision: DDDecision::Applied { value: dd2_value() },
            history_cut: 1,
        }));
    assert(a13.configs.last().decisions == a12.configs.last().decisions);
    assert(a14.configs.last().decisions == a13.configs.last().decisions);
    dd2_singleton_applied_facts(a14.configs.last().decisions);
    let success2 = dd2_success_two_wal_event();
    let deliver2 = DDAdapterEvent::Observe {
        event: wal_runtime_layer::wal_encode(success2),
    };
    assert(dd_enabled(a14.configs.last(), deliver2));
    dd2_observe_wal_event_exec(request, initial, a14, success2);
    dd2_observe_wal_event_preserves_decisions(a14, success2);
    let a15 = dd2_observe_wal_event(a14, success2);
    assert(a15 == dd2_adapter_retry_observed_execution());
    assert(a15.configs.last().history == dd2_retry_history());
    assert(dd_global_trace(a15.events)
        == dd2_wal_retry_observed_execution().events);
}

pub proof fn dd2_adapter_execution_exec()
    ensures
        dd_exec(
            dd_request_zero(), Option::None, dd2_adapter_execution(),
        ),
        dd2_adapter_execution().events.len() == 31,
        dd_global_trace(dd2_adapter_execution().events)
            == dd2_wal_execution().events,
        dd2_adapter_execution().configs.last().slot
            == Option::Some(dd2_value()),
        dd2_adapter_execution().configs.last().history
            == dd2_retry_history(),
        dd2_adapter_execution().configs.last().decisions
            == dd2_adapter_pre_crash_execution().configs.last().decisions,
{
    let request = dd_request_zero();
    let initial = Option::<replay_layer::Value>::None;
    let a15 = dd2_adapter_retry_observed_execution();
    let w14 = dd2_wal_retry_observed_execution();
    dd2_adapter_retry_observed_execution_exec();
    let cut6 = wal_runtime_layer::journal_view(
        w14.configs.last(),
    ).len() + 1;
    let a16 = dd2_observe_full_append(
        a15, dd2_success_outcome_record(), cut6,
    );
    dd2_observe_full_append_exec(
        request, initial, a15, dd2_success_outcome_record(), cut6,
    );
    dd2_observe_full_append_preserves_service_state(
        a15, dd2_success_outcome_record(), cut6,
    );
    assert(a16 == dd2_adapter_success_outcome_execution());
    let w15 = dd2_wal_success_outcome_execution();
    let cut7 = wal_runtime_layer::journal_view(
        w15.configs.last(),
    ).len() + 1;
    let a17 = dd2_observe_full_append(
        a16, dd2_commit_record(), cut7,
    );
    dd2_observe_full_append_exec(
        request, initial, a16, dd2_commit_record(), cut7,
    );
    dd2_observe_full_append_preserves_service_state(
        a16, dd2_commit_record(), cut7,
    );
    assert(a17 == dd2_adapter_execution());
    assert(dd_global_trace(a17.events) == dd2_wal_execution().events);
}

pub proof fn dd2_records_select_terminal_commit()
    ensures terminal_from_records(
        dd2_records(), dd_request_zero(),
    ) == Option::Some(dd2_terminal_outcome()),
{
    reveal_with_fuel(replay_layer::terminal_count, 10);
    reveal_with_fuel(latest_terminal_record, 10);
    assert(dd2_records().len() == 7);
    assert(dd2_records().last() == dd2_commit_record());
    assert(terminal_outcome_of_record(
        dd2_commit_record(), dd_request_zero(),
    ) == Option::Some(dd2_terminal_outcome()));
}

pub proof fn dd2_wal_trace_shape()
    ensures
        projection_layer::pi_journal(dd2_wal_execution().events)
            == dd2_records(),
        projection_layer::pi_physical(dd2_wal_execution().events)
            == dd2_retry_history(),
        projection_layer::pi_adapter(
            dd2_wal_execution().events, dd_request_zero(),
        ) == dd2_retry_history(),
        terminal(
            dd2_wal_execution().events, dd_request_zero(),
        ) == Option::Some(dd2_terminal_outcome()),
        dd2_explicit_crash_retry_trace_shape(
            dd2_wal_execution().events,
        ),
{
    let cfg = dd_full_config();
    let source = dd2_wal_execution();
    let length = source.events.len();
    let final_state = source.configs[length as int];
    dd2_wal_execution_exec();
    wal_trace_layer::trace_agreement_for_exec(cfg, source);
    assert(wal_trace_layer::trace_agreement_at(cfg, source, length));
    assert(wal_trace_layer::prefix_events(source, length)
        == source.events);
    assert(final_state.evidence.records
        == projection_layer::pi_journal(source.events));
    assert(final_state.evidence.physical
        == projection_layer::pi_physical(source.events));
    reveal_with_fuel(projection_layer::adapter_from_physical, 5);
    assert(projection_layer::pi_adapter(
        source.events, dd_request_zero(),
    ) == dd2_retry_history());
    dd2_records_select_terminal_commit();
    assert(dd2_explicit_crash_retry_trace_shape(source.events));
}

pub proof fn dd2_concrete_decision_and_effect()
    ensures
        dd2_retry_run().interference.decisions
            == Seq::empty().push(DDDecisionRecord {
                attempt: 1,
                decision: DDDecision::Applied { value: dd2_value() },
                history_cut: 1,
            }),
        dd2_retry_run().pre == Option::None,
        dd2_retry_run().post == Option::Some(dd2_value()),
        dd_has_applied(
            dd2_retry_run().interference.decisions, dd2_value(),
        ),
        dd_one_effect(dd_request_zero(), dd2_retry_run()),
        !dd_zero_effect(dd_request_zero(), dd2_retry_run()),
        delivery(dd2_retry_history(), dd_request_zero(), 1).is_none(),
        delivery(dd2_retry_history(), dd_request_zero(), 2)
            == Option::Some(
                replay_layer::Observation::Success(dd2_value()),
            ),
{
    let adapter = dd2_adapter_execution();
    let final_state = adapter.configs[adapter.events.len() as int];
    dd2_adapter_pre_crash_execution_exec();
    dd2_adapter_execution_exec();
    assert(final_state == adapter.configs.last());
    assert(dd2_retry_run() == dd_external_run(final_state));
    assert(adapter.configs.last().decisions
        == dd2_adapter_pre_crash_execution().configs.last().decisions);
    assert(dd2_adapter_pre_crash_execution().configs.last().decisions
        == Seq::empty().push(DDDecisionRecord {
            attempt: 1,
            decision: DDDecision::Applied { value: dd2_value() },
            history_cut: 1,
        }));
    assert(final_state.decisions
        == Seq::empty().push(DDDecisionRecord {
            attempt: 1,
            decision: DDDecision::Applied { value: dd2_value() },
            history_cut: 1,
        }));
    dd2_singleton_applied_facts(final_state.decisions);
    assert(dd2_retry_run().interference.decisions
        == final_state.decisions);
    assert(final_state.slot == Option::Some(dd2_value()));
    assert(dd2_retry_run().post == Option::Some(dd2_value()));
    assert(dd_one_effect(dd_request_zero(), dd2_retry_run())) by {
        let value = dd2_value();
    }
    assert(!dd_zero_effect(dd_request_zero(), dd2_retry_run()));
    reveal_with_fuel(p1_layer::delivery_count, 5);
    reveal_with_fuel(latest_delivery_observation, 5);
    assert(delivery(dd2_retry_history(), dd_request_zero(), 1).is_none());
    assert(delivery(dd2_retry_history(), dd_request_zero(), 2)
        == Option::Some(
            replay_layer::Observation::Success(dd2_value()),
        ));
}

pub proof fn dd2_wal_closed_representation()
    ensures
        t1_layer::paper_config_wf(dd_paper()),
        wal_runtime_layer::exec(dd_full_config(), dd2_wal_execution()),
        wal_trace_layer::admissible_wal_trace(
            dd_full_config(), dd2_wal_execution(),
        ),
        wal_trace_layer::trace_agreement(
            dd_full_config(), dd2_wal_execution(),
        ),
        t4_c0_layer::wal_broker_representation(
            dd_full_config(),
            dd2_wal_execution().configs[
                dd2_wal_execution().events.len() as int
            ],
            dd2_final_broker(),
        ),
        terminal(dd2_wal_execution().events, dd_request_zero())
            == Option::Some(dd2_terminal_outcome()),
{
    dd_full_config_is_well_formed();
    dd2_wal_execution_exec();
    dd2_wal_trace_shape();
    wal_trace_layer::exec_implies_admissible_wal_trace(
        dd_full_config(), dd2_wal_execution(),
    );
    wal_trace_layer::trace_agreement_for_exec(
        dd_full_config(), dd2_wal_execution(),
    );
    t4_c0_layer::canonical_closed_wal_broker_composition(
        dd_full_config(), dd2_wal_execution(),
    );
}

pub proof fn dd2_adapter_rely_on_wal()
    ensures adapter_rely(
        dd_paper(),
        dd2_wal_execution().events,
        dd_request_zero(),
        dd2_retry_run(),
    ),
{
    let adapter = dd2_adapter_execution();
    let request = dd_request_zero();
    let final_adapter = adapter.configs[adapter.events.len() as int];
    dd2_adapter_execution_exec();
    dd1_exec_derives_adapter_rely(request, Option::None, adapter);
    dd1_exec_final_globals_are_projected(request, Option::None, adapter);
    assert(final_adapter == adapter.configs.last());
    assert(dd2_retry_run() == dd_external_run(final_adapter));
    assert(dd_global_trace(adapter.events) == dd2_wal_execution().events);
}

pub proof fn dd2_wal_terminal_refines()
    ensures
        terminal(dd2_wal_execution().events, dd_request_zero())
            == Option::Some(dd2_terminal_outcome()),
        refines(
            dd_paper(),
            dd_request_zero(),
            projection_layer::pi_adapter(
                dd2_wal_execution().events, dd_request_zero(),
            ),
            dd2_retry_run(),
            dd2_terminal_outcome(),
        ),
        per_request_effect_refinement(
            dd_paper(),
            dd2_wal_execution().events,
            dd_request_zero(),
            dd2_retry_run(),
        ),
{
    let paper = dd_paper();
    let cfg = dd_full_config();
    let wal = dd2_wal_execution();
    let broker = dd2_final_broker();
    let request = dd_request_zero();
    let run = dd2_retry_run();
    let outcome = dd2_terminal_outcome();
    let final_wal = wal.configs[wal.events.len() as int];
    dd2_wal_closed_representation();
    dd_adapter_is_verified();
    dd2_adapter_rely_on_wal();
    t1_layer::paper_broker_config_is_broker(paper);
    assert(t1_layer::paper_broker_config(paper) == cfg);
    assert(t1_layer::paper_config_wf(paper));
    assert(adapter_verified(paper));
    assert(wal_runtime_layer::exec(cfg, wal));
    assert(wal_trace_layer::admissible_wal_trace(cfg, wal));
    assert(wal_trace_layer::trace_agreement(cfg, wal));
    assert(final_wal == wal.configs.last());
    assert(t4_c0_layer::wal_broker_representation(
        cfg, final_wal, broker,
    ));
    assert(adapter_rely(paper, wal.events, request, run));
    assert(terminal(wal.events, request) == Option::Some(outcome));
    wal_terminal_outcome_refines(
        paper, wal, broker, request, run, outcome,
    );
}

pub closed spec fn dd2_executable_crash_retry_operational_package()
    -> bool
{
    let adapter = dd2_adapter_execution();
    let wal = dd2_wal_execution();
    &&& dd_exec(dd_request_zero(), Option::None, adapter)
    &&& wal_runtime_layer::exec(dd_full_config(), wal)
    &&& adapter.events.len() == 31
    &&& wal.events.len() == 30
    &&& dd_global_trace(adapter.events) == wal.events
    &&& projection_layer::pi_physical(wal.events) == dd2_retry_history()
    &&& wal.configs.last().evidence.records == dd2_records()
    &&& dd2_explicit_crash_retry_trace_shape(wal.events)
}

pub closed spec fn dd2_executable_crash_retry_semantic_package()
    -> bool
{
    let wal = dd2_wal_execution();
    let request = dd_request_zero();
    &&& terminal(wal.events, request)
        == Option::Some(dd2_terminal_outcome())
    &&& adapter_rely(dd_paper(), wal.events, request, dd2_retry_run())
    &&& refines(
        dd_paper(),
        request,
        projection_layer::pi_adapter(wal.events, request),
        dd2_retry_run(),
        dd2_terminal_outcome(),
    )
    &&& per_request_effect_refinement(
        dd_paper(), wal.events, request, dd2_retry_run(),
    )
    &&& dd_one_effect(request, dd2_retry_run())
    &&& !dd_zero_effect(request, dd2_retry_run())
    &&& delivery(dd2_retry_history(), request, 1).is_none()
    &&& delivery(dd2_retry_history(), request, 2)
        == Option::Some(replay_layer::Observation::Success(dd2_value()))
}

pub closed spec fn dd2_executable_crash_retry_package() -> bool {
    dd2_executable_crash_retry_operational_package()
        && dd2_executable_crash_retry_semantic_package()
}

pub proof fn dd2_concrete_operational_package()
    ensures dd2_executable_crash_retry_operational_package(),
{
    let adapter = dd2_adapter_execution();
    let wal = dd2_wal_execution();
    dd2_adapter_execution_exec();
    dd2_wal_execution_exec();
    dd2_wal_trace_shape();
    reveal(dd2_executable_crash_retry_operational_package);
}

pub proof fn dd2_concrete_semantic_package()
    ensures dd2_executable_crash_retry_semantic_package(),
{
    dd2_wal_terminal_refines();
    dd2_adapter_rely_on_wal();
    dd2_concrete_decision_and_effect();
    reveal(dd2_executable_crash_retry_semantic_package);
}

pub proof fn t6_dd2_executable_crash_retry_nonvacuity()
    ensures dd2_executable_crash_retry_package(),
{
    dd2_concrete_operational_package();
    dd2_concrete_semantic_package();
    reveal(dd2_executable_crash_retry_package);
}

} // verus!
