use vstd::prelude::*;

#[path = "t6_adapter_semantic_closure.rs"]
pub mod t6_a0_layer;

verus! {

use t6_a0_layer::*;
use t6_a0_layer::t6_s0_layer;
use t6_s0_layer::t6_c0_layer;
use t6_c0_layer::t6_e0_layer;
use t6_e0_layer::t6_d0_layer;
use t6_d0_layer::t5_c0_layer;
use t5_c0_layer::t5_r1_layer;
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
use contract_layer::p3_layer::p2_layer::p1_layer::p0_layer;
use p0_layer::config_layer;
use config_layer::broker_layer as record_layer;
use record_layer::query_layer;
use query_layer::c1_layer;
use c1_layer::replay_layer;
use c1_layer::append_layer;

// The existing T6-A0 success execution has 20 events.  Its first 17 events
// end immediately after the successful Outcome flush; the final three are the
// ordinary online Commit append that this witness replaces with crash-time
// recovery.
pub open spec fn h2_durable_outcome_prefix()
    -> wal_runtime_layer::WalExecution
{
    wal_runtime_layer::execution_prefix(
        ensure_member_wal_execution(), 17,
    )
}

pub open spec fn h2_recovery_commit_execution()
    -> wal_runtime_layer::WalExecution
{
    let cfg = ensure_member_full_config();
    let e0 = h2_durable_outcome_prefix();
    let e1 = t5_r1_layer::r1_extend_wal_execution(
        cfg, e0, wal_runtime_layer::WalEvent::Crash,
    );
    let e2 = t5_r1_layer::r1_extend_wal_execution(
        cfg, e1, wal_runtime_layer::WalEvent::BeginScan,
    );
    let e3 = t5_r1_layer::r1_extend_wal_execution(
        cfg, e2, wal_runtime_layer::WalEvent::FinishScan,
    );
    let e4 = t5_r1_layer::r1_extend_wal_execution(
        cfg, e3, wal_runtime_layer::WalEvent::TruncateTail,
    );
    let e5 = t5_r1_layer::r1_extend_wal_execution(
        cfg, e4, wal_runtime_layer::WalEvent::BeginRecover,
    );
    let e6 = t5_r1_layer::r1_append_full_wal_execution(
        cfg, e5, ensure_member_commit_record(),
    );
    t5_r1_layer::r1_extend_wal_execution(
        cfg, e6, wal_runtime_layer::WalEvent::FinishRecover,
    )
}

pub open spec fn h2_journal_execution()
    -> journal_runtime_layer::JournalExecution
{
    t3_layer::compressed_execution(h2_recovery_commit_execution())
}

pub open spec fn h2_broker_execution()
    -> execution_layer::BrokerExecution
{
    t4_c0_layer::canonical_target_execution(
        ensure_member_full_config(), h2_recovery_commit_execution(),
    )
}

pub proof fn h2_durable_success_recovery_witness()
    ensures
        config_layer::full_config_wf(ensure_member_full_config()),
        wal_runtime_layer::exec(
            ensure_member_full_config(), h2_recovery_commit_execution(),
        ),
        journal_runtime_layer::exec(
            ensure_member_full_config(), h2_journal_execution(),
        ),
        execution_layer::exec(
            ensure_member_full_config(), h2_broker_execution(),
        ),
        h2_recovery_commit_execution().events.len() == 26,
        h2_recovery_commit_execution().events[17]
            == global_layer::GlobalEvent::Crash,
        h2_recovery_commit_execution().events[23]
            == (global_layer::GlobalEvent::WalWriteFull {
                record: ensure_member_commit_record(),
            }),
        h2_recovery_commit_execution().events[25]
            == global_layer::GlobalEvent::FinishRecover,
        t5_r0_layer::recovery_episode(
            h2_recovery_commit_execution().events, 17, 25,
        ),
        !t5_r0_layer::commit_stuttering_recovery_episode(
            h2_recovery_commit_execution().events, 17, 25,
        ),
        t5_r1_layer::wal_recovery_episode_has_crash_prefix_provenance(
            h2_recovery_commit_execution(), 17, 25,
        ),
        append_layer::is_prefix(
            t5_s0_layer::alpha_commit_wal(
                ensure_member_full_config(),
                h2_recovery_commit_execution().configs[17],
            ),
            t5_s0_layer::alpha_commit_wal(
                ensure_member_full_config(),
                h2_recovery_commit_execution().configs[26],
            ),
        ),
        t5_s0_layer::alpha_commit_wal(
            ensure_member_full_config(),
            h2_recovery_commit_execution().configs[17],
        ).len() == 0,
        t5_s0_layer::alpha_commit_wal(
            ensure_member_full_config(),
            h2_recovery_commit_execution().configs[26],
        ).len() == 1,
{
    let cfg = ensure_member_full_config();
    let commit = ensure_member_commit_record();
    let full = ensure_member_wal_execution();
    let e0 = h2_durable_outcome_prefix();

    ensure_member_full_config_is_well_formed();
    ensure_member_wal_execution_exec();
    wal_runtime_layer::exec_prefix(cfg, full, 17);
    wal_runtime_layer::every_exec_configuration_is_basic(cfg, full);
    assert(wal_runtime_layer::exec(cfg, e0));
    assert(e0.events.len() == 17);
    assert(e0.configs.len() == 18);
    assert(e0.configs.last() == full.configs[17]);
    assert(full.events[17]
        == (global_layer::GlobalEvent::WalStage { record: commit }));
    assert(full.events[18]
        == (global_layer::GlobalEvent::WalWriteFull { record: commit }));
    assert(full.events[19] is WalFlushAck);
    assert(wal_runtime_layer::wal_runtime_step(
        cfg, full.configs[17], full.events[17], full.configs[18],
    ));
    assert(wal_runtime_layer::wal_runtime_step(
        cfg, full.configs[18], full.events[18], full.configs[19],
    ));
    assert(wal_runtime_layer::wal_runtime_step(
        cfg, full.configs[19], full.events[19], full.configs[20],
    ));
    assert(wal_runtime_layer::wal_decode(full.events[17])
        == Option::Some(wal_runtime_layer::WalEvent::WalStage {
            record: commit,
        }));
    assert(wal_runtime_layer::wal_decode(full.events[18])
        == Option::Some(wal_runtime_layer::WalEvent::WalWriteFull {
            record: commit,
        }));
    assert(wal_runtime_layer::admissibly_enabled(
        cfg,
        full.configs[17],
        wal_runtime_layer::WalEvent::WalStage { record: commit },
    ));
    assert(wal_runtime_layer::admissibly_enabled(
        cfg,
        full.configs[18],
        wal_runtime_layer::WalEvent::WalWriteFull { record: commit },
    ));
    assert(e0.configs.last().runtime.mode == record_layer::Mode::Online);
    assert(wal_runtime_layer::wal_quiescent(e0.configs.last()));
    assert(full.configs[18] == wal_runtime_layer::apply(
        cfg,
        full.configs[17],
        wal_runtime_layer::WalEvent::WalStage { record: commit },
    ));
    assert(full.configs[18].runtime.store.media
        == full.configs[17].runtime.store.media);
    assert(wal_runtime_layer::no_torn(
        full.configs[18].runtime.store.media,
    ));
    assert(wal_runtime_layer::basic_invariant(cfg, full.configs[17]));
    assert(wal_runtime_layer::basic_invariant(cfg, full.configs[18]));
    assert(wal_runtime_layer::basic_invariant(cfg, full.configs[19]));
    assert(wal_runtime_layer::wal_invariant(
        cfg,
        full.configs[17].runtime.store,
        full.configs[17].runtime.mode,
        full.configs[17].runtime.append,
    ));
    assert(wal_runtime_layer::wal_invariant(
        cfg,
        full.configs[18].runtime.store,
        full.configs[18].runtime.mode,
        full.configs[18].runtime.append,
    ));
    assert(wal_runtime_layer::wal_invariant(
        cfg,
        full.configs[19].runtime.store,
        full.configs[19].runtime.mode,
        full.configs[19].runtime.append,
    ));
    assert(e0.configs.last().runtime.store.media
        == wal_runtime_layer::full_frames(
            wal_runtime_layer::journal_view(e0.configs.last()),
        ));
    t5_s0_layer::wal_step_journal_view_exact(
        cfg, full.configs[17], full.events[17], full.configs[18],
    );
    t5_s0_layer::wal_step_journal_view_exact(
        cfg, full.configs[18], full.events[18], full.configs[19],
    );
    t5_s0_layer::wal_step_journal_view_exact(
        cfg, full.configs[19], full.events[19], full.configs[20],
    );
    assert(wal_runtime_layer::journal_view(e0.configs.last())
        == ensure_member_records().drop_last());
    assert(wal_runtime_layer::runtime_record_enabled(
        cfg, e0.configs.last(), commit,
    ));

    let crash = wal_runtime_layer::WalEvent::Crash;
    assert(wal_runtime_layer::admissibly_enabled(
        cfg, e0.configs.last(), crash,
    ));
    t5_r1_layer::r1_extend_wal_execution_exec(cfg, e0, crash);
    let e1 = t5_r1_layer::r1_extend_wal_execution(cfg, e0, crash);
    assert(e1.configs.last().runtime.mode == record_layer::Mode::Crashed);

    let begin_scan = wal_runtime_layer::WalEvent::BeginScan;
    assert(wal_runtime_layer::admissibly_enabled(
        cfg, e1.configs.last(), begin_scan,
    ));
    t5_r1_layer::r1_extend_wal_execution_exec(cfg, e1, begin_scan);
    let e2 = t5_r1_layer::r1_extend_wal_execution(
        cfg, e1, begin_scan,
    );

    let finish_scan = wal_runtime_layer::WalEvent::FinishScan;
    assert(wal_runtime_layer::admissibly_enabled(
        cfg, e2.configs.last(), finish_scan,
    ));
    t5_r1_layer::r1_extend_wal_execution_exec(cfg, e2, finish_scan);
    let e3 = t5_r1_layer::r1_extend_wal_execution(
        cfg, e2, finish_scan,
    );

    let truncate = wal_runtime_layer::WalEvent::TruncateTail;
    assert(wal_runtime_layer::admissibly_enabled(
        cfg, e3.configs.last(), truncate,
    ));
    t5_r1_layer::r1_extend_wal_execution_exec(cfg, e3, truncate);
    let e4 = t5_r1_layer::r1_extend_wal_execution(
        cfg, e3, truncate,
    );

    let begin_recover = wal_runtime_layer::WalEvent::BeginRecover;
    assert(wal_runtime_layer::admissibly_enabled(
        cfg, e4.configs.last(), begin_recover,
    ));
    t5_r1_layer::r1_extend_wal_execution_exec(
        cfg, e4, begin_recover,
    );
    let e5 = t5_r1_layer::r1_extend_wal_execution(
        cfg, e4, begin_recover,
    );
    assert(e5.configs.last().runtime.mode
        == record_layer::Mode::Recovering);
    assert(e5.configs.last().runtime.slot == record_layer::ExecSlot::Idle);
    assert(wal_runtime_layer::wal_quiescent(e5.configs.last()));
    assert(e5.configs.last().runtime.store.media
        == wal_runtime_layer::full_frames(
            wal_runtime_layer::journal_view(e5.configs.last()),
        ));
    assert(wal_runtime_layer::journal_view(e5.configs.last())
        == wal_runtime_layer::journal_view(e0.configs.last()));

    query_layer::replay_d_outcome_exact(
        config_layer::erase_config(cfg),
        wal_runtime_layer::journal_view(e5.configs.last()),
        ensure_member_request_zero(),
        1,
    );
    assert(query_layer::d_outcome(
        wal_runtime_layer::replay_view(cfg, e5.configs.last()),
        ensure_member_request_zero(),
        1,
    ) == Option::Some(replay_layer::Observation::Success(
        ensure_member_success_value(),
    )));
    assert(wal_runtime_layer::runtime_record_enabled(
        cfg, e5.configs.last(), commit,
    ));
    t5_r1_layer::r1_append_full_wal_execution_exec(
        cfg, e5, commit,
    );
    let e6 = t5_r1_layer::r1_append_full_wal_execution(
        cfg, e5, commit,
    );
    assert(e6.configs.last().runtime.mode
        == record_layer::Mode::Recovering);
    assert(wal_runtime_layer::journal_view(e6.configs.last())
        == ensure_member_records());

    reveal_with_fuel(replay_layer::replay, 8);
    assert forall|request: replay_layer::RequestId|
        #[trigger] replay_layer::replay(
            config_layer::erase_config(cfg),
            wal_runtime_layer::journal_view(e6.configs.last()),
        ).phase[request] != replay_layer::Phase::Armed by {
        if request == ensure_member_request_zero() {
        } else {
        }
    }
    assert(query_layer::recovery_complete_j(
        config_layer::erase_config(cfg),
        wal_runtime_layer::journal_view(e6.configs.last()),
    ));
    let finish = wal_runtime_layer::WalEvent::FinishRecover;
    assert(wal_runtime_layer::admissibly_enabled(
        cfg, e6.configs.last(), finish,
    ));
    t5_r1_layer::r1_extend_wal_execution_exec(cfg, e6, finish);
    let execution = h2_recovery_commit_execution();
    assert(wal_runtime_layer::exec(cfg, execution));
    assert(execution.events.len() == 26);
    assert(execution.configs.len() == 27);
    assert(execution.events[17] == global_layer::GlobalEvent::Crash);
    assert(execution.events[23]
        == (global_layer::GlobalEvent::WalWriteFull { record: commit }));
    assert(execution.events[25]
        == global_layer::GlobalEvent::FinishRecover);
    assert(t5_r0_layer::recovery_episode(execution.events, 17, 25));
    assert(t5_r0_layer::recovery_commit_linearization(
        execution.events[23],
    ));
    assert(!t5_r0_layer::commit_stuttering_recovery_episode(
        execution.events, 17, 25,
    ));

    t5_r1_layer::t5_r1_durable_success_recovery(
        cfg, execution, 17, 25,
    );
    assert(t5_s0_layer::alpha_commit_wal(
        cfg, execution.configs[17],
    ).len() == 0);
    assert(t5_s0_layer::alpha_commit_wal(
        cfg, execution.configs[26],
    ).len() == 1);

    t3_layer::canonical_typed_wal_simulation(cfg, execution);
    assert(journal_runtime_layer::exec(
        cfg, h2_journal_execution(),
    ));
    t4_c0_layer::canonical_closed_wal_broker_composition(
        cfg, execution,
    );
    assert(execution_layer::exec(cfg, h2_broker_execution()));
}

} // verus!
