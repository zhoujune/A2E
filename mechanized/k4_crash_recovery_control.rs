use vstd::prelude::*;

#[path = "k4_terminal_recovery_bridge.rs"]
pub mod k4_a3_layer;

verus! {

use k4_a3_layer::*;
use k4_a3_layer::k4_a2_layer::{
    k4_a2_journal_push_view, k4_a2_terminal_state,
    KJournalRecord, KKernelState, KManifestBinding, KManifestConfig, KObservation, KPhase,
    KRetryClass,
};
use k4_a3_layer::k4_a2_layer::k4_a1_layer::k4_a1_expected_record_exec;
use k4_a3_layer::k4_a2_layer::k4_a1_layer::k4_a0_layer::{
    k4_a0_manifest_profile, k4_a0_manifest_records_legal, k4_a0_records,
};
use k4_a3_layer::k4_a2_layer::k4_a1_layer::k4_a0_layer::k4_r7_layer::k4_r6_layer::k4_r5_layer::k4_r4_layer::k4_r3_layer::k4_r2_layer::k4_r1_layer::k4_r0_layer::k4_layer::{
    k4_idempotent_manifest, k_manifest_binding_lookup,
    k_manifest_config_view, k_manifest_wf,
};
use k4_a3_layer::k4_a2_layer::k4_a1_layer::k4_a0_layer::k4_r7_layer::k4_r6_layer::k4_r5_layer::k4_r4_layer::k4_r3_layer::k4_r2_layer::k4_r1_layer::k4_r0_layer::k_manifest_find_binding;
use k4_a3_layer::k4_a2_layer::k4_a1_layer::k4_a0_layer::k4_r7_layer::k4_r6_layer::k4_r5_layer::k4_r4_layer::k4_r3_layer::k4_r2_layer::k4_r1_layer::k4_r0_layer::k4_layer::k3_layer;
use k3_layer::{
    k3_control_exact, k_append_view, k_journal_record_view,
    k_journal_seq_view, KAppendControl,
};
use k3_layer::k2_record_layer::k2_guard_layer::k1_layer::query_layer;
use k3_layer::k2_record_layer::k_update_inv;
use k3_layer::k2_record_layer::k2_guard_layer::k1_layer::{
    k_durable_inv, k_phase_view, k_request_entry_couples, k_request_id,
};
use query_layer::c1_layer;
use c1_layer::{append_layer, replay_layer};

// K4-A4 makes crash/recovery an explicit executable control boundary around
// the K4-A3 typed-record kernel.  The journal, durable summaries, and
// acknowledgement cuts survive a crash; only the in-flight append control is
// discarded.  Recovery may append only durable-evidence-backed terminal
// decisions until no request is left in the Armed phase, after which the
// kernel can return Online.

#[derive(PartialEq, Eq, Clone, Copy)]
pub enum KRecoveryMode {
    Online,
    Crashed,
    Recovering,
}

pub struct KRecoveryKernel {
    pub core: KKernelState,
    pub mode: KRecoveryMode,
}

pub open spec fn k4_a4_terminal_record(record: KJournalRecord) -> bool {
    match record {
        KJournalRecord::Commit { .. }
        | KJournalRecord::Fail { .. }
        | KJournalRecord::Unknown { .. } => true,
        KJournalRecord::Revoke { .. }
        | KJournalRecord::Authorize { .. }
        | KJournalRecord::Prepare { .. }
        | KJournalRecord::Arm { .. }
        | KJournalRecord::Start { .. }
        | KJournalRecord::Outcome { .. } => false,
    }
}

pub fn k4_a4_terminal_record_exec(record: &KJournalRecord) -> (terminal: bool)
    ensures
        terminal == k4_a4_terminal_record(*record),
{
    match *record {
        KJournalRecord::Commit { .. }
        | KJournalRecord::Fail { .. }
        | KJournalRecord::Unknown { .. } => true,
        KJournalRecord::Revoke { .. }
        | KJournalRecord::Authorize { .. }
        | KJournalRecord::Prepare { .. }
        | KJournalRecord::Arm { .. }
        | KJournalRecord::Start { .. }
        | KJournalRecord::Outcome { .. } => false,
    }
}

pub open spec fn k4_a4_inv(
    config: KManifestConfig,
    state: KRecoveryKernel,
) -> bool {
    k4_a3_inv(config, state.core)
}

pub fn k4_a4_initial(config: &KManifestConfig) -> (state: KRecoveryKernel)
    requires
        k_manifest_wf(*config),
    ensures
        k4_a4_inv(*config, state),
        state.mode == KRecoveryMode::Online,
        state.core.append is Idle,
        k_append_view(state.core)
            == append_layer::initial_state::<replay_layer::JournalRecord>(),
{
    KRecoveryKernel {
        core: k4_a3_initial(config),
        mode: KRecoveryMode::Online,
    }
}

pub open spec fn k4_a4_preview_expected(
    config: KManifestConfig,
    state: KRecoveryKernel,
    record: KJournalRecord,
) -> bool {
    &&& (state.mode == KRecoveryMode::Online
        || (state.mode == KRecoveryMode::Recovering
            && k4_a4_terminal_record(record)))
    &&& state.core.append is Idle
    &&& k4_a3_call_expected(config, state.core, record)
}

pub fn k4_a4_preview(
    config: &KManifestConfig,
    state: &mut KRecoveryKernel,
    record: KJournalRecord,
) -> (accepted: bool)
    requires
        k4_a4_inv(*config, *old(state)),
    ensures
        k4_a4_inv(*config, *final(state)),
        accepted ==> {
            final(state).core.append == KAppendControl::Called { record }
        },
        !accepted ==> *final(state) == *old(state),
{
    if state.mode == KRecoveryMode::Crashed {
        return false;
    }
    if state.mode == KRecoveryMode::Recovering
        && !k4_a4_terminal_record_exec(&record)
    {
        return false;
    }
    if !matches!(state.core.append, KAppendControl::Idle) {
        return false;
    }
    let accepted = k4_a3_try_call(config, &mut state.core, record);
    accepted
}

pub open spec fn k4_a4_commit_expected(
    config: KManifestConfig,
    state: KRecoveryKernel,
    record: KJournalRecord,
) -> bool {
    &&& state.mode != KRecoveryMode::Crashed
    &&& (state.mode == KRecoveryMode::Online
        || (state.mode == KRecoveryMode::Recovering
            && k4_a4_terminal_record(record)))
    &&& k4_a3_linearize_expected(state.core, record)
}

pub fn k4_a4_commit_after_wal(
    config: &KManifestConfig,
    state: &mut KRecoveryKernel,
    record: KJournalRecord,
) -> (cut: Option<u64>)
    requires
        k4_a4_inv(*config, *old(state)),
    ensures
        k4_a4_inv(*config, *final(state)),
        match cut {
            Option::None => *final(state) == *old(state),
            Option::Some(value) => {
                &&& final(state).mode == old(state).mode
                &&& final(state).core.journal@ == old(state).core.journal@.push(record)
                &&& final(state).core.ack_cuts@ == old(state).core.ack_cuts@.push(value)
                &&& final(state).core.append is Idle
                &&& value as nat == old(state).core.journal@.len() + 1
            },
        },
{
    let ghost before = *state;
    if state.mode == KRecoveryMode::Crashed {
        return Option::None;
    }
    if state.mode == KRecoveryMode::Recovering
        && !k4_a4_terminal_record_exec(&record)
    {
        return Option::None;
    }
    let linearized = k4_a3_linearize(config, &mut state.core, record);
    let lsn = match linearized {
        Option::Some(value) => value,
        Option::None => {
            return Option::None;
        },
    };
    let returned = k4_a3_return(config, &mut state.core);
    match returned {
        Option::Some(cut) => {
            proof {
                assert(cut == lsn);
            }
            Option::Some(cut)
        },
        Option::None => {
            proof { assert(false); }
            Option::None
        },
    }
}

pub fn k4_a4_crash(
    config: &KManifestConfig,
    state: &mut KRecoveryKernel,
)
    requires
        k4_a4_inv(*config, *old(state)),
    ensures
        k4_a4_inv(*config, *final(state)),
        final(state).mode == KRecoveryMode::Crashed,
        final(state).core.durable == old(state).core.durable,
        final(state).core.journal@ == old(state).core.journal@,
        final(state).core.ack_cuts@ == old(state).core.ack_cuts@,
        final(state).core.append is Idle,
{
    let ghost before = *state;
    let ghost before_view = k_append_view(before.core);
    let ghost crash_event = append_layer::Event::Crash;
    state.core.append = KAppendControl::Idle;
    state.mode = KRecoveryMode::Crashed;
    proof {
        append_layer::step_preserves_invariant(before_view, crash_event);
        append_layer::step_preserves_legal_control(
            k4_a3_layer::k4_a2_layer::k4_a1_layer::k4_a0_layer::k4_r7_layer::k4_r6_layer::k4_r5_layer::k4_r4_layer::k4_r3_layer::k4_r2_layer::k4_r1_layer::k4_r0_layer::k4_layer::k3_layer::k2_record_layer::k2_guard_layer::k1_layer::query_layer::c1_layer::c1_eligibility(
                k_manifest_config_view(*config),
            ),
            before_view,
            crash_event,
        );
        assert(k_append_view(state.core)
            == append_layer::apply(before_view, crash_event));
        assert(k3_control_exact(state.core));
    }
}

pub fn k4_a4_begin_recovery(
    config: &KManifestConfig,
    state: &mut KRecoveryKernel,
) -> (started: bool)
    requires
        k4_a4_inv(*config, *old(state)),
    ensures
        k4_a4_inv(*config, *final(state)),
        final(state).core == old(state).core,
        started == (old(state).mode == KRecoveryMode::Crashed),
        started ==> {
            final(state).mode == KRecoveryMode::Recovering
        },
        !started ==> *final(state) == *old(state),
{
    match state.mode {
        KRecoveryMode::Crashed => {
            state.mode = KRecoveryMode::Recovering;
            true
        },
        KRecoveryMode::Online | KRecoveryMode::Recovering => false,
    }
}

pub open spec fn k4_a4_recovery_complete(state: KRecoveryKernel) -> bool {
    forall|index: int|
        0 <= index < state.core.durable.requests@.len()
            ==> state.core.durable.requests@[index].phase != KPhase::Armed
}

pub fn k4_a4_phase_is_not_armed(phase: KPhase) -> (clear: bool)
    ensures
        clear == (phase != KPhase::Armed),
{
    match phase {
        KPhase::Armed => false,
        KPhase::New
        | KPhase::Authorized
        | KPhase::Prepared
        | KPhase::Committed
        | KPhase::Failed
        | KPhase::Unknown => true,
    }
}

pub fn k4_a4_recovery_complete_exec(
    config: &KManifestConfig,
    state: &KRecoveryKernel,
) -> (complete: bool)
    requires
        k4_a4_inv(*config, *state),
    ensures
        complete == k4_a4_recovery_complete(*state),
{
    let mut index: usize = 0;
    while index < state.core.durable.requests.len()
        invariant
            index <= state.core.durable.requests@.len(),
            forall|prior: int|
                0 <= prior < index
                    ==> state.core.durable.requests@[prior].phase != KPhase::Armed,
        decreases state.core.durable.requests.len() - index,
    {
        let phase = state.core.durable.requests[index].phase;
        let clear = k4_a4_phase_is_not_armed(phase);
        if !clear {
            proof {
                assert(phase == KPhase::Armed);
                assert(state.core.durable.requests@[index as int].phase
                    == KPhase::Armed);
                assert(!k4_a4_recovery_complete(*state));
            }
            return false;
        }
        proof {
            assert(state.core.durable.requests@[index as int].phase == phase);
            assert(clear);
            assert(phase != KPhase::Armed);
        }
        index = index + 1;
    }
    proof {
        assert forall|entry: int|
            0 <= entry < state.core.durable.requests@.len()
                implies state.core.durable.requests@[entry].phase
                    != KPhase::Armed by {
            assert(entry < index);
        }
        assert(k4_a4_recovery_complete(*state));
    }
    true
}

pub fn k4_a4_finish_recovery(
    config: &KManifestConfig,
    state: &mut KRecoveryKernel,
) -> (finished: bool)
    requires
        k4_a4_inv(*config, *old(state)),
    ensures
        k4_a4_inv(*config, *final(state)),
        final(state).core == old(state).core,
        finished == (old(state).mode == KRecoveryMode::Recovering
            && k4_a4_recovery_complete(*old(state))),
        finished ==> final(state).mode == KRecoveryMode::Online,
        !finished ==> *final(state) == *old(state),
{
    match state.mode {
        KRecoveryMode::Recovering => {
            if !k4_a4_recovery_complete_exec(config, state) {
                return false;
            }
            state.mode = KRecoveryMode::Online;
            true
        },
        KRecoveryMode::Online | KRecoveryMode::Crashed => false,
    }
}

pub open spec fn k4_a4_binding_allows_resume(
    request: u64,
    started: nat,
    binding: KManifestBinding,
) -> bool {
    &&& binding.request == request
    &&& match binding.class {
        KRetryClass::Idempotent | KRetryClass::Deduplicated => true,
        KRetryClass::ReadOnly | KRetryClass::Uncontrolled =>
            started == 0,
    }
}

pub open spec fn k4_a4_request_allows_resume(
    config: KManifestConfig,
    request: u64,
    started: nat,
) -> bool {
    exists|index: int|
        0 <= index < config.bindings@.len()
            && k4_a4_binding_allows_resume(
                request, started, #[trigger] config.bindings@[index],
            )
}

pub fn k4_a4_request_allows_resume_exec(
    config: &KManifestConfig,
    request: u64,
    started: usize,
) -> (allowed: bool)
    requires
        k_manifest_wf(*config),
    ensures
        allowed == k4_a4_request_allows_resume(
            *config, request, started as nat,
        ),
{
    let found = k_manifest_find_binding(config, request);
    match found {
        Option::Some(index) => {
            let binding = config.bindings[index];
            let allowed = match binding.class {
                KRetryClass::Idempotent | KRetryClass::Deduplicated => true,
                KRetryClass::ReadOnly | KRetryClass::Uncontrolled =>
                    started == 0,
            };
            proof {
                if allowed {
                    assert(k4_a4_binding_allows_resume(
                        request, started as nat, binding,
                    ));
                    assert(k4_a4_request_allows_resume(
                        *config, request, started as nat,
                    ));
                } else {
                    assert forall|other: int|
                        0 <= other < config.bindings@.len()
                            && config.bindings@[other].request == request
                            implies other == index as int by {
                        assert(config.bindings@[index as int].request
                            == request);
                    }
                    assert forall|other: int|
                        0 <= other < config.bindings@.len()
                            implies !k4_a4_binding_allows_resume(
                                request,
                                started as nat,
                                #[trigger] config.bindings@[other],
                            ) by {
                        if config.bindings@[other].request == request {
                            assert(other == index as int);
                            assert(config.bindings@[other] == binding);
                        }
                    }
                    assert(!k4_a4_request_allows_resume(
                        *config, request, started as nat,
                    ));
                }
            }
            allowed
        },
        Option::None => {
            proof {
                assert forall|index: int|
                    0 <= index < config.bindings@.len()
                        implies !k4_a4_binding_allows_resume(
                            request,
                            started as nat,
                            #[trigger] config.bindings@[index],
                        ) by {
                    assert(config.bindings@[index].request != request);
                }
                assert(!k4_a4_request_allows_resume(
                    *config, request, started as nat,
                ));
            }
            false
        },
    }
}

pub open spec fn k4_a4_entry_allows_resume(
    config: KManifestConfig,
    phase: KPhase,
    request: u64,
    started: nat,
) -> bool {
    phase != KPhase::Armed
        || k4_a4_request_allows_resume(config, request, started)
}

pub fn k4_a4_entry_allows_resume_exec(
    config: &KManifestConfig,
    phase: KPhase,
    request: u64,
    started: usize,
) -> (allowed: bool)
    requires
        k_manifest_wf(*config),
    ensures
        allowed == k4_a4_entry_allows_resume(
            *config, phase, request, started as nat,
        ),
{
    match phase {
        KPhase::Armed => k4_a4_request_allows_resume_exec(
            config, request, started,
        ),
        KPhase::New
        | KPhase::Authorized
        | KPhase::Prepared
        | KPhase::Committed
        | KPhase::Failed
        | KPhase::Unknown => true,
    }
}

pub open spec fn k4_a4_recovery_resumable(
    config: KManifestConfig,
    state: KRecoveryKernel,
) -> bool {
    forall|index: int|
        0 <= index < state.core.durable.requests@.len()
            ==> k4_a4_entry_allows_resume(
                config,
                #[trigger] state.core.durable.requests@[index].phase,
                state.core.durable.requests@[index].request,
                state.core.durable.requests@[index].outcomes@.len(),
            )
}

pub fn k4_a4_recovery_resumable_exec(
    config: &KManifestConfig,
    state: &KRecoveryKernel,
) -> (resumable: bool)
    requires
        k_manifest_wf(*config),
        k4_a4_inv(*config, *state),
    ensures
        resumable == k4_a4_recovery_resumable(*config, *state),
{
    let mut index: usize = 0;
    while index < state.core.durable.requests.len()
        invariant
            k_manifest_wf(*config),
            k4_a4_inv(*config, *state),
            index <= state.core.durable.requests@.len(),
            forall|prior: int| 0 <= prior < index ==>
                k4_a4_entry_allows_resume(
                    *config,
                    #[trigger] state.core.durable.requests@[prior].phase,
                    state.core.durable.requests@[prior].request,
                    state.core.durable.requests@[prior].outcomes@.len(),
                ),
        decreases state.core.durable.requests.len() - index,
    {
        let phase = state.core.durable.requests[index].phase;
        let request = state.core.durable.requests[index].request;
        let started = state.core.durable.requests[index].outcomes.len();
        proof {
            assert(state.core.durable.requests@[index as int].phase == phase);
            assert(state.core.durable.requests@[index as int].request == request);
            assert(state.core.durable.requests@[index as int].outcomes@.len()
                == started);
        }
        let allowed = k4_a4_entry_allows_resume_exec(
            config, phase, request, started,
        );
        if !allowed {
            proof {
                assert(!k4_a4_entry_allows_resume(
                    *config,
                    state.core.durable.requests@[index as int].phase,
                    state.core.durable.requests@[index as int].request,
                    state.core.durable.requests@[index as int].outcomes@.len(),
                ));
                assert(!k4_a4_recovery_resumable(*config, *state)) by {
                    if k4_a4_recovery_resumable(*config, *state) {
                        assert(k4_a4_entry_allows_resume(
                            *config,
                            state.core.durable.requests@[index as int].phase,
                            state.core.durable.requests@[index as int].request,
                            state.core.durable.requests@[index as int].outcomes@.len(),
                        ));
                    }
                }
            }
            return false;
        }
        proof {
            assert(k4_a4_entry_allows_resume(
                *config,
                state.core.durable.requests@[index as int].phase,
                state.core.durable.requests@[index as int].request,
                state.core.durable.requests@[index as int].outcomes@.len(),
            ));
        }
        index = index + 1;
    }
    proof {
        assert forall|entry: int|
            0 <= entry < state.core.durable.requests@.len()
                implies k4_a4_entry_allows_resume(
                    *config,
                    #[trigger] state.core.durable.requests@[entry].phase,
                    state.core.durable.requests@[entry].request,
                    state.core.durable.requests@[entry].outcomes@.len(),
                ) by {
            assert(entry < index);
        }
        assert(k4_a4_recovery_resumable(*config, *state));
    }
    true
}

/// Leaves recovery without changing durable state only when every Armed
/// request is safe to resume: retry-safe classes may continue, while
/// Uncontrolled/ReadOnly requests must not yet contain a durable Start slot.
pub fn k4_a4_resume_recovery(
    config: &KManifestConfig,
    state: &mut KRecoveryKernel,
) -> (resumed: bool)
    requires
        k_manifest_wf(*config),
        k4_a4_inv(*config, *old(state)),
    ensures
        k4_a4_inv(*config, *final(state)),
        final(state).core == old(state).core,
        resumed == (old(state).mode == KRecoveryMode::Recovering
            && k4_a4_recovery_resumable(*config, *old(state))),
        resumed ==> final(state).mode == KRecoveryMode::Online,
        !resumed ==> *final(state) == *old(state),
{
    match state.mode {
        KRecoveryMode::Recovering => {
            if !k4_a4_recovery_resumable_exec(config, state) {
                return false;
            }
            state.mode = KRecoveryMode::Online;
            true
        },
        KRecoveryMode::Online | KRecoveryMode::Crashed => false,
    }
}

pub fn k4_a4_recovery_append_one(
    config: &KManifestConfig,
    state: &mut KRecoveryKernel,
    record: KJournalRecord,
) -> (cut: u64)
    requires
        k4_a4_inv(*config, *old(state)),
        old(state).mode == KRecoveryMode::Recovering,
        old(state).core.append is Idle,
        old(state).core.journal@.len() < 0xffff_ffff_ffff_ffff,
        k4_a4_terminal_record(record),
        k4_a3_supported(record),
        replay_layer::structural_enabled(
            k_manifest_config_view(*config),
            k_journal_seq_view(old(state).core.journal@),
            k_journal_record_view(record),
        ),
    ensures
        k4_a4_inv(*config, *final(state)),
        final(state).mode == KRecoveryMode::Recovering,
        final(state).core.journal@ == old(state).core.journal@.push(record),
        final(state).core.ack_cuts@ == old(state).core.ack_cuts@.push(cut),
        final(state).core.append is Idle,
        cut as nat == old(state).core.journal@.len() + 1,
{
    k4_a3_append_one(config, &mut state.core, record)
}

pub fn k4_a4_durable_success_recovery_witness()
    -> (result: (KManifestConfig, KRecoveryKernel))
    ensures
        k4_a0_manifest_profile(result.0),
        k4_a4_inv(result.0, result.1),
        result.1.mode == KRecoveryMode::Online,
        result.1.core.append is Idle,
        k_journal_seq_view(result.1.core.journal@) == k4_a0_records(),
        result.1.core.ack_cuts@.len() == 6,
        exists|index: int| {
            &&& 0 <= index < result.1.core.durable.requests@.len()
            &&& result.1.core.durable.requests@[index].request == 1
            &&& result.1.core.durable.requests@[index].phase
                == KPhase::Committed
            &&& result.1.core.durable.requests@[index].outcomes@.len() == 1
            &&& result.1.core.durable.requests@[index].outcomes@[0]
                == Option::Some(KObservation::Success { value: 1 })
        },
{
    let config = k4_idempotent_manifest();
    let mut state = k4_a4_initial(&config);
    proof {
        assert(k4_a0_manifest_profile(config));
        k4_a0_manifest_records_legal(config);
    }

    let first = k4_a1_expected_record_exec(1);
    proof {
        assert(k_journal_record_view(first) == k4_a0_records()[0]);
        replay_layer::journal_legal_take(
            k_manifest_config_view(config), k4_a0_records(), 1nat,
        );
        replay_layer::journal_legal_last(
            k_manifest_config_view(config), k4_a0_records().take(1),
        );
    }
    let ghost before_first = state.core;
    let cut1 = k4_a3_append_one(&config, &mut state.core, first);
    proof {
        k4_a2_journal_push_view(before_first, state.core, first);
        assert(k_journal_seq_view(state.core.journal@)
            == k4_a0_records().take(1));
        assert(cut1 == 1u64);
    }

    let second = k4_a1_expected_record_exec(2);
    proof {
        assert(k_journal_record_view(second) == k4_a0_records()[1]);
        replay_layer::journal_legal_take(
            k_manifest_config_view(config), k4_a0_records(), 2nat,
        );
        replay_layer::journal_legal_last(
            k_manifest_config_view(config), k4_a0_records().take(2),
        );
    }
    let ghost before_second = state.core;
    let cut2 = k4_a3_append_one(&config, &mut state.core, second);
    proof {
        k4_a2_journal_push_view(before_second, state.core, second);
        assert(k_journal_seq_view(state.core.journal@)
            == k4_a0_records().take(2));
        assert(cut2 == 2u64);
    }

    let third = k4_a1_expected_record_exec(3);
    proof {
        assert(k_journal_record_view(third) == k4_a0_records()[2]);
        replay_layer::journal_legal_take(
            k_manifest_config_view(config), k4_a0_records(), 3nat,
        );
        replay_layer::journal_legal_last(
            k_manifest_config_view(config), k4_a0_records().take(3),
        );
    }
    let ghost before_third = state.core;
    let cut3 = k4_a3_append_one(&config, &mut state.core, third);
    proof {
        k4_a2_journal_push_view(before_third, state.core, third);
        assert(k_journal_seq_view(state.core.journal@)
            == k4_a0_records().take(3));
        assert(cut3 == 3u64);
    }

    let fourth = k4_a1_expected_record_exec(4);
    proof {
        assert(k_journal_record_view(fourth) == k4_a0_records()[3]);
        replay_layer::journal_legal_take(
            k_manifest_config_view(config), k4_a0_records(), 4nat,
        );
        replay_layer::journal_legal_last(
            k_manifest_config_view(config), k4_a0_records().take(4),
        );
    }
    let ghost before_fourth = state.core;
    let cut4 = k4_a3_append_one(&config, &mut state.core, fourth);
    proof {
        k4_a2_journal_push_view(before_fourth, state.core, fourth);
        assert(k_journal_seq_view(state.core.journal@)
            == k4_a0_records().take(4));
        assert(cut4 == 4u64);
    }

    let fifth = k4_a1_expected_record_exec(5);
    proof {
        assert(k_journal_record_view(fifth) == k4_a0_records()[4]);
        replay_layer::journal_legal_take(
            k_manifest_config_view(config), k4_a0_records(), 5nat,
        );
        replay_layer::journal_legal_last(
            k_manifest_config_view(config), k4_a0_records().take(5),
        );
    }
    let ghost before_fifth = state.core;
    let cut5 = k4_a3_append_one(&config, &mut state.core, fifth);
    proof {
        k4_a2_journal_push_view(before_fifth, state.core, fifth);
        assert(k_journal_seq_view(state.core.journal@)
            == k4_a0_records().take(5));
        assert(cut5 == 5u64);
    }

    k4_a4_crash(&config, &mut state);
    assert(state.mode == KRecoveryMode::Crashed);
    let started = k4_a4_begin_recovery(&config, &mut state);
    proof { assert(started); }
    assert(state.mode == KRecoveryMode::Recovering);

    let sixth = k4_a1_expected_record_exec(6);
    proof {
        assert(k_journal_record_view(sixth) == k4_a0_records()[5]);
        replay_layer::journal_legal_last(
            k_manifest_config_view(config), k4_a0_records(),
        );
        assert(k4_a4_terminal_record(sixth));
    }
    let ghost before_sixth = state.core;
    let cut6 = k4_a4_recovery_append_one(
        &config, &mut state, sixth,
    );
    proof {
        k4_a2_journal_push_view(before_sixth, state.core, sixth);
        assert(k_journal_seq_view(state.core.journal@)
            == k4_a0_records());
        assert(cut6 == 6u64);
    }

    proof {
        let cfg = k_manifest_config_view(config);
        let journal = k_journal_seq_view(state.core.journal@);
        let durable = replay_layer::replay(cfg, journal);
        assert(k4_a3_inv(config, state.core));
        assert(k_update_inv(state.core.durable, cfg, durable));
        assert(k_durable_inv(state.core.durable, cfg, durable));
        reveal_with_fuel(replay_layer::replay, 8);
        assert forall|index: int|
            0 <= index < state.core.durable.requests@.len()
                implies state.core.durable.requests@[index].phase
                    != KPhase::Armed by {
            let entry = state.core.durable.requests@[index];
            assert(k_request_entry_couples(entry, durable));
            if entry.request == 1 {
                assert(durable.phase[k_request_id(entry.request)]
                    == replay_layer::Phase::Committed);
            } else {
                assert(durable.phase[k_request_id(entry.request)]
                    == replay_layer::Phase::New);
            }
            assert(k_phase_view(entry.phase)
                != replay_layer::Phase::Armed);
            match entry.phase {
                KPhase::Armed => assert(false),
                KPhase::New
                | KPhase::Authorized
                | KPhase::Prepared
                | KPhase::Committed
                | KPhase::Failed
                | KPhase::Unknown => {},
            }
        }
        assert(k4_a4_recovery_complete(state));
    }
    let finished = k4_a4_finish_recovery(&config, &mut state);
    proof { assert(finished); }
    assert(state.mode == KRecoveryMode::Online);
    proof {
        k4_a2_terminal_state(config, state.core);
    }
    (config, state)
}

}
