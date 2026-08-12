use vstd::prelude::*;

#[path = "k4_manifest_append_certificate.rs"]
pub mod k4_a0_layer;

verus! {

use k4_a0_layer::*;
use k4_a0_layer::k4_r7_layer::{
    k_manifest_apply_commit, k_manifest_commit_enabled,
};
use k4_a0_layer::k4_r7_layer::k4_r6_layer::{
    k_manifest_apply_outcome, k_manifest_outcome_enabled,
};
use k4_a0_layer::k4_r7_layer::k4_r6_layer::k4_r5_layer::{
    k_manifest_apply_start,
};
use k4_a0_layer::k4_r7_layer::k4_r6_layer::k4_r5_layer::k4_r4_layer::{
    k_manifest_apply_arm, k_manifest_arm_enabled,
};
use k4_a0_layer::k4_r7_layer::k4_r6_layer::k4_r5_layer::k4_r4_layer::k4_r3_layer::{
    k_manifest_apply_prepare,
};
use k4_a0_layer::k4_r7_layer::k4_r6_layer::k4_r5_layer::k4_r4_layer::k4_r3_layer::k4_r2_layer::{
    k_manifest_apply_authorize,
};
use k4_a0_layer::k4_r7_layer::k4_r6_layer::k4_r5_layer::k4_r4_layer::k4_r3_layer::k4_r2_layer::k4_r1_layer::k4_r0_layer::k4_layer::k3_layer;
use k4_a0_layer::k4_r7_layer::k4_r6_layer::k4_r5_layer::k4_r4_layer::k4_r3_layer::k4_r2_layer::k4_r1_layer::k4_r0_layer::k4_layer::{
    k4_idempotent_manifest, k_manifest_config_is_well_formed,
    k_manifest_config_view, k_manifest_wf, KManifestConfig,
};
use k4_a0_layer::k4_r7_layer::k4_r6_layer::k4_r5_layer::k4_r4_layer::k4_r3_layer::k4_r2_layer::k4_r1_layer::{
    k_manifest_prepare_enabled, k_manifest_start_enabled,
};
use k4_a0_layer::k4_r7_layer::k4_r6_layer::k4_r5_layer::k4_r4_layer::k4_r3_layer::k4_r2_layer::k4_r1_layer::k4_r0_layer::k_manifest_authorize_enabled;
use k3_layer::*;
use k3_layer::k2_record_layer::{
    k_default_cap_delta_preserves_update_inv,
    k_default_request_delta_preserves_update_inv,
    k_initial_satisfies_update_inv, k_push_default_capability,
    k_push_default_request, k_update_inv,
    k_update_inv_lifts_through_replay_push,
};
use k3_layer::k2_record_layer::k2_guard_layer::k1_layer::{
    k_capability_id, k_durable_inv, k_find_capability, k_find_request,
    k_initial, k_observation_view, k_outcome_view, k_phase_view,
    k_request_entry_couples, k_request_id, k_tracks_capability,
    k_tracks_request, KDurable, KPhase,
};
use k3_layer::k2_record_layer::k2_guard_layer::k1_layer::query_layer;
use query_layer::c1_layer;
use query_layer::c1_layer::{append_layer, replay_layer};

// K4-A1 threads the finite M4 manifest through the concrete K3 append state.
// The bridge is intentionally bounded to the six-record Idempotent profile;
// other K3 record variants remain outside this checkpoint.

pub open spec fn k4_a1_inv(
    config: KManifestConfig,
    state: KKernelState,
) -> bool {
    let cfg = k_manifest_config_view(config);
    let journal = k_journal_seq_view(state.journal@);
    let view = k_append_view(state);
    &&& state.journal@.len() <= 0xffff_ffff_ffff_ffff
    &&& k_manifest_wf(config)
    &&& replay_layer::config_wf(cfg)
    &&& replay_layer::journal_legal(cfg, journal)
    &&& k_update_inv(
        state.durable,
        cfg,
        replay_layer::replay(cfg, journal),
    )
    &&& append_layer::b1_invariant(view)
    &&& append_layer::legal_control_shape(
        c1_layer::c1_eligibility(cfg), view,
    )
    &&& k3_control_exact(state)
}

pub open spec fn k4_a1_expected_record(index: u64) -> KJournalRecord {
    match index {
        1 => KJournalRecord::Authorize {
            request: 1, capability: 1, digest: 1,
        },
        2 => KJournalRecord::Prepare {
            request: 1, class: KRetryClass::Idempotent, digest: 1,
            key_present: false, key: 0, auth_ref: 1,
        },
        3 => KJournalRecord::Arm {
            request: 1, digest: 1, key_present: false, key: 0,
            prepare_ref: 2,
        },
        4 => KJournalRecord::Start {
            request: 1, attempt: 1, digest: 1, key_present: false,
            key: 0, arm_ref: 3,
        },
        5 => KJournalRecord::Outcome {
            request: 1, attempt: 1,
            observation: KObservation::Success { value: 1 },
            digest: 1, key_present: false, key: 0, start_ref: 4,
        },
        _ => KJournalRecord::Commit {
            request: 1, attempt: 1, value: 1, digest: 1,
            key_present: false, key: 0, outcome_ref: 5,
        },
    }
}

pub fn k4_a1_expected_record_exec(index: u64) -> (record: KJournalRecord)
    requires
        1 <= index <= 6,
    ensures
        record == k4_a1_expected_record(index),
{
    match index {
        1 => KJournalRecord::Authorize {
            request: 1, capability: 1, digest: 1,
        },
        2 => KJournalRecord::Prepare {
            request: 1, class: KRetryClass::Idempotent, digest: 1,
            key_present: false, key: 0, auth_ref: 1,
        },
        3 => KJournalRecord::Arm {
            request: 1, digest: 1, key_present: false, key: 0,
            prepare_ref: 2,
        },
        4 => KJournalRecord::Start {
            request: 1, attempt: 1, digest: 1, key_present: false,
            key: 0, arm_ref: 3,
        },
        5 => KJournalRecord::Outcome {
            request: 1, attempt: 1,
            observation: KObservation::Success { value: 1 },
            digest: 1, key_present: false, key: 0, start_ref: 4,
        },
        _ => KJournalRecord::Commit {
            request: 1, attempt: 1, value: 1, digest: 1,
            key_present: false, key: 0, outcome_ref: 5,
        },
    }
}

pub open spec fn k4_a1_profile_state(
    config: KManifestConfig,
    state: KKernelState,
) -> bool {
    &&& k4_a1_inv(config, state)
    &&& k4_a0_manifest_profile(config)
    &&& state.journal@.len() <= 6
    &&& state.durable.requests@.len()
        == if state.journal@.len() == 0 { 0nat } else { 1nat }
    &&& state.durable.caps@.len()
        == if state.journal@.len() == 0 { 0nat } else { 1nat }
    &&& k_journal_seq_view(state.journal@)
        == k4_a0_records().take(state.journal@.len() as int)
    &&& match state.append {
        KAppendControl::Idle => {
            k_ack_seq_view(state.ack_cuts@)
                == k4_a0_cuts(state.journal@.len())
        },
        KAppendControl::Called { record } => {
            &&& state.journal@.len() < 6
            &&& k_journal_record_view(record)
                == k4_a0_records()[state.journal@.len() as int]
            &&& k_ack_seq_view(state.ack_cuts@)
                == k4_a0_cuts(state.journal@.len())
        },
        KAppendControl::Linearized { record, .. } => {
            &&& state.journal@.len() > 0
            &&& k_journal_record_view(record)
                == k4_a0_records()[state.journal@.len() as int - 1]
            &&& k_ack_seq_view(state.ack_cuts@)
                == k4_a0_cuts((state.journal@.len() - 1) as nat)
        },
    }
}

pub open spec fn k4_a1_call_expected(
    state: KKernelState,
    record: KJournalRecord,
) -> bool {
    &&& state.journal@.len() < 6
    &&& record == k4_a1_expected_record(
        (state.journal@.len() + 1) as u64,
    )
}

pub open spec fn k4_a1_linearize_expected(
    state: KKernelState,
    record: KJournalRecord,
) -> bool {
    &&& state.append is Called
    &&& state.journal@.len() < 6
    &&& record == k4_a1_expected_record(
        (state.journal@.len() + 1) as u64,
    )
    &&& match state.append {
        KAppendControl::Called { record: called } => called == record,
        KAppendControl::Idle | KAppendControl::Linearized { .. } => false,
    }
}

pub fn k4_a1_initial(config: &KManifestConfig) -> (state: KKernelState)
    requires
        k4_a0_manifest_profile(*config),
    ensures
        k4_a1_inv(*config, state),
        k4_a1_profile_state(*config, state),
        k_append_view(state)
            == append_layer::initial_state::<replay_layer::JournalRecord>(),
{
    let state = KKernelState {
        durable: KDurable {
            requests: Vec::new(),
            caps: Vec::new(),
        },
        journal: Vec::new(),
        ack_cuts: Vec::new(),
        append: KAppendControl::Idle,
    };
    proof {
        k_manifest_config_is_well_formed(*config);
        k_initial_satisfies_update_inv(
            state.durable,
            k_manifest_config_view(*config),
        );
        append_layer::initial_invariant::<replay_layer::JournalRecord>();
        assert(k_journal_seq_view(state.journal@) =~= Seq::empty());
        assert(k_ack_seq_view(state.ack_cuts@) =~= Seq::empty());
        reveal_with_fuel(k4_a0_cuts, 2);
        assert(k4_a0_records().take(0) =~= Seq::empty());
        assert(state.durable.requests@.len() == 0);
        assert(state.durable.caps@.len() == 0);
        assert(k_append_view(state)
            == append_layer::initial_state::<replay_layer::JournalRecord>());
        assert(append_layer::legal_control_shape(
            c1_layer::c1_eligibility(k_manifest_config_view(*config)),
            k_append_view(state),
        ));
    }
    state
}

pub fn k4_a1_try_call(
    config: &KManifestConfig,
    state: &mut KKernelState,
    record: KJournalRecord,
) -> (accepted: bool)
    requires
        k4_a1_profile_state(*config, *old(state)),
        old(state).append is Idle,
    ensures
        k4_a1_inv(*config, *final(state)),
        k4_a1_profile_state(*config, *final(state)),
        accepted == k4_a1_call_expected(*old(state), record),
        accepted ==> {
            &&& final(state).durable == old(state).durable
            &&& final(state).journal@ == old(state).journal@
            &&& final(state).ack_cuts@ == old(state).ack_cuts@
            &&& final(state).append == KAppendControl::Called { record }
            &&& k_append_view(*final(state))
                == append_layer::apply(
                    k_append_view(*old(state)),
                    append_layer::Event::Call {
                        record: k_journal_record_view(record),
                    },
                )
        },
        !accepted ==> *final(state) == *old(state),
{
    let journal_len = state.journal.len() as u64;
    if journal_len >= 6u64 {
        proof { assert(!k4_a1_call_expected(*state, record)); }
        return false;
    }
    let expected = k4_a1_expected_record_exec(journal_len + 1);
    if !k_journal_record_equal(record, expected) {
        proof { assert(!k4_a1_call_expected(*state, record)); }
        return false;
    }

    let ghost before = *state;
    let ghost before_view = k_append_view(before);
    let ghost cfg = k_manifest_config_view(*config);
    let ghost event = append_layer::Event::Call {
        record: k_journal_record_view(record),
    };
    proof {
        k4_a0_manifest_records_legal(*config);
        reveal_with_fuel(k4_a0_cuts, 8);
        assert(journal_len as nat == before.journal@.len());
        assert(journal_len < 6);
        assert(k4_a0_records().take(journal_len as int)
            == k_journal_seq_view(before.journal@));
        assert(k4_a0_records()[journal_len as int]
            == k_journal_record_view(record));
        assert(replay_layer::structural_enabled(
            cfg,
            k_journal_seq_view(before.journal@),
            k_journal_record_view(record),
        ));
        assert(append_layer::enabled(before_view, event));
        assert(append_layer::record_eligible(
            c1_layer::c1_eligibility(cfg), before_view, event,
        ));
        append_layer::step_preserves_invariant(before_view, event);
        append_layer::step_preserves_legal_control(
            c1_layer::c1_eligibility(cfg), before_view, event,
        );
    }
    state.append = KAppendControl::Called { record };
    proof {
        assert(k_append_view(*state)
            == append_layer::apply(before_view, event));
        assert(k3_control_exact(*state));
        assert(k_journal_record_view(record)
            == k4_a0_records()[state.journal@.len() as int]);
    }
    proof { assert(k4_a1_call_expected(before, record)); }
    true
}

pub fn k4_a1_return(
    config: &KManifestConfig,
    state: &mut KKernelState,
) -> (returned: Option<u64>)
    requires
        k4_a1_profile_state(*config, *old(state)),
    ensures
        k4_a1_inv(*config, *final(state)),
        k4_a1_profile_state(*config, *final(state)),
        returned.is_some() <==> old(state).append is Linearized,
        match returned {
            Option::None => *final(state) == *old(state),
            Option::Some(cut) => {
                &&& final(state).durable == old(state).durable
                &&& final(state).journal@ == old(state).journal@
                &&& final(state).ack_cuts@ == old(state).ack_cuts@.push(cut)
                &&& final(state).append == KAppendControl::Idle
                &&& cut as nat == old(state).journal@.len()
                &&& k_append_view(*final(state))
                    == append_layer::apply(
                        k_append_view(*old(state)),
                        append_layer::Event::ReturnOk {
                            cut: cut as nat,
                        },
                    )
            },
        },
{
    let (stored_record, stored_lsn) = match state.append {
        KAppendControl::Linearized { record, lsn } => (record, lsn),
        KAppendControl::Idle | KAppendControl::Called { .. } => {
            return Option::None;
        },
    };

    let cut = state.journal.len() as u64;
    let ghost before = *state;
    let ghost before_view = k_append_view(before);
    let ghost event = append_layer::Event::ReturnOk { cut: cut as nat };
    proof {
        assert(before.append == KAppendControl::Linearized {
            record: stored_record, lsn: stored_lsn,
        });
        assert(cut == stored_lsn);
        k_journal_seq_view_len(before.journal@);
        assert(before_view.evidence.records.len() == cut as nat);
        assert(before_view.append
            == append_layer::AppendControl::Linearized {
                record: k_journal_record_view(stored_record),
            });
        assert(append_layer::enabled(before_view, event));
        assert(append_layer::record_eligible(
            c1_layer::c1_eligibility(k_manifest_config_view(*config)),
            before_view, event,
        ));
        append_layer::step_preserves_invariant(before_view, event);
        append_layer::step_preserves_legal_control(
            c1_layer::c1_eligibility(k_manifest_config_view(*config)),
            before_view, event,
        );
        append_layer::take_full(before_view.evidence.records);
    }
    state.ack_cuts.push(cut);
    state.append = KAppendControl::Idle;
    proof {
        k_ack_seq_view_push(before.ack_cuts@, cut);
        reveal_with_fuel(k4_a0_cuts, 8);
        assert(cut as nat == before.journal@.len());
        assert(k_ack_seq_view(before.ack_cuts@)
            == k4_a0_cuts((before.journal@.len() - 1) as nat));
        assert(k4_a0_cuts(before.journal@.len())
            == k4_a0_cuts((before.journal@.len() - 1) as nat)
                .push(before.journal@.len()));
        assert(k_append_view(*state)
            == append_layer::apply(before_view, event));
        assert(k3_control_exact(*state));
    }
    Option::Some(cut)
}

pub fn k4_a1_linearize(
    config: &KManifestConfig,
    state: &mut KKernelState,
    record: KJournalRecord,
) -> (linearized: Option<u64>)
    requires
        k4_a1_profile_state(*config, *old(state)),
    ensures
        k4_a1_inv(*config, *final(state)),
        linearized.is_some() == k4_a1_linearize_expected(*old(state), record),
        match linearized {
            Option::None => *final(state) == *old(state),
            Option::Some(lsn) => {
                &&& final(state).journal@ == old(state).journal@.push(record)
                &&& final(state).ack_cuts@ == old(state).ack_cuts@
                &&& final(state).append
                    == KAppendControl::Linearized { record, lsn }
                &&& lsn as nat == old(state).journal@.len() + 1
                &&& k_append_view(*final(state))
                    == append_layer::apply(
                        k_append_view(*old(state)),
                        append_layer::Event::Linearize {
                            record: k_journal_record_view(record),
                        },
                    )
            },
        },
        linearized.is_some() ==> k4_a1_profile_state(*config, *final(state)),
{
    let called = match state.append {
        KAppendControl::Called { record: called } => called,
        KAppendControl::Idle | KAppendControl::Linearized { .. } => {
            proof { assert(!k4_a1_linearize_expected(*state, record)); }
            return Option::None;
        },
    };
    if !k_journal_record_equal(called, record) {
        proof { assert(!k4_a1_linearize_expected(*state, record)); }
        return Option::None;
    }
    let next = state.journal.len() as u64 + 1;
    if next > 6u64 {
        proof { assert(!k4_a1_linearize_expected(*state, record)); }
        return Option::None;
    }
    let expected = k4_a1_expected_record_exec(next);
    if !k_journal_record_equal(record, expected) {
        proof { assert(!k4_a1_linearize_expected(*state, record)); }
        return Option::None;
    }

    let ghost before = *state;
    let ghost before_journal = k_journal_seq_view(before.journal@);
    let ghost cfg = k_manifest_config_view(*config);
    let ghost durable = replay_layer::replay(cfg, before_journal);
    let ghost spec_record = k_journal_record_view(record);
    let ghost before_view = k_append_view(before);
    let ghost event = append_layer::Event::Linearize {
        record: spec_record,
    };

    proof {
        assert(called == record);
        assert(record == expected);
        assert(before.append == KAppendControl::Called { record });
        assert(before_journal == k4_a0_records().take(
            before.journal@.len() as int,
        ));
        assert(k4_a0_records()[before.journal@.len() as int]
            == spec_record);
        k4_a0_manifest_records_legal(*config);
        assert(replay_layer::structural_enabled(
            cfg, before_journal, spec_record,
        ));
        query_layer::structural_enabled_implies_abstract_record_enabled(
            cfg, before_journal, spec_record,
        );
        assert(append_layer::enabled(before_view, event));
        assert(append_layer::record_eligible(
            c1_layer::c1_eligibility(cfg), before_view, event,
        ));
        append_layer::step_preserves_invariant(before_view, event);
        append_layer::step_preserves_legal_control(
            c1_layer::c1_eligibility(cfg), before_view, event,
        );
        append_layer::acknowledged_prefix_survives_record_push(
            before_view.evidence.records,
            before_view.evidence.ack_cuts,
            spec_record,
        );
    }
    proof { assert(k4_a1_linearize_expected(before, record)); }

    match next {
        1 => {
            let request_index = k_push_default_request(&mut state.durable, 1);
            let ghost after_request = state.durable;
            let cap_index = k_push_default_capability(&mut state.durable, 1);
            proof {
                assert(before.durable.requests@.len() == 0);
                assert(before.durable.caps@.len() == 0);
                assert(!k_tracks_request(before.durable, 1nat));
                assert(!k_tracks_capability(before.durable, 1nat));
                assert(cfg.max_attempts[k_request_id(1)] > 0nat);
                k_default_request_delta_preserves_update_inv(
                    before.durable, after_request,
                    cfg, durable, 1,
                );
                assert(!k_tracks_capability(after_request, 1nat));
                k_default_cap_delta_preserves_update_inv(
                    after_request, state.durable,
                    cfg, durable, 1,
                );
            }
            let decision = k_manifest_authorize_enabled(
                config, &state.durable, 1, 1, 1, Ghost(durable),
            );
            proof { assert(decision); }
            k_manifest_apply_authorize(
                config, &mut state.durable, request_index, cap_index,
                1, 1, 1, Ghost(durable),
            );
        },
        2 => {
            let request_index = match k_find_request(&state.durable, 1) {
                Option::Some(index) => index,
                Option::None => return Option::None,
            };
            let decision = k_manifest_prepare_enabled(
                config, &state.durable, 1, KRetryClass::Idempotent,
                1, false, 0, Ghost(durable),
            );
            proof { assert(decision); }
            k_manifest_apply_prepare(
                config, &mut state.durable, request_index, 1,
                KRetryClass::Idempotent, 1, false, 0, 1,
                Ghost(durable),
            );
        },
        3 => {
            let request_index = match k_find_request(&state.durable, 1) {
                Option::Some(index) => index,
                Option::None => return Option::None,
            };
            let decision = k_manifest_arm_enabled(
                config, &state.durable, 1, 1, false, 0, Ghost(durable),
            );
            proof { assert(decision); }
            k_manifest_apply_arm(
                config, &mut state.durable, request_index, 1,
                1, false, 0, 2, Ghost(durable),
            );
        },
        4 => {
            let request_index = match k_find_request(&state.durable, 1) {
                Option::Some(index) => index,
                Option::None => return Option::None,
            };
            let decision = k_manifest_start_enabled(
                config, &state.durable, 1, 1, 1, false, 0,
                Ghost(durable),
            );
            proof { assert(decision); }
            k_manifest_apply_start(
                config, &mut state.durable, request_index, 1,
                1, 1, false, 0, 3, Ghost(durable),
            );
        },
        5 => {
            let request_index = match k_find_request(&state.durable, 1) {
                Option::Some(index) => index,
                Option::None => return Option::None,
            };
            let observation = KObservation::Success { value: 1 };
            let decision = k_manifest_outcome_enabled(
                config, &state.durable, 1, 1, observation,
                1, false, 0, Ghost(durable),
            );
            proof { assert(decision); }
            k_manifest_apply_outcome(
                config, &mut state.durable, request_index, 1, 1,
                observation, 1, false, 0, 4, Ghost(durable),
            );
        },
        6 => {
            let request_index = match k_find_request(&state.durable, 1) {
                Option::Some(index) => index,
                Option::None => return Option::None,
            };
            let decision = k_manifest_commit_enabled(
                config, &state.durable, 1, 1, 1, 1,
                false, 0, Ghost(durable),
            );
            proof { assert(decision); }
            k_manifest_apply_commit(
                config, &mut state.durable, request_index, 1, 1, 1,
                1, false, 0, 5, Ghost(durable),
            );
        },
        _ => return Option::None,
    }

    proof {
        assert(state.journal@ == before.journal@);
        assert(state.ack_cuts@ == before.ack_cuts@);
        assert(state.append == before.append);
        assert(state.durable.requests@.len() == 1);
        assert(state.durable.caps@.len() == 1);
    }
    let old_len = state.journal.len();
    let lsn = old_len as u64 + 1;
    state.journal.push(record);
    state.append = KAppendControl::Linearized { record, lsn };
    proof {
        k_journal_seq_view_push(before.journal@, record);
        k_journal_seq_view_len(before.journal@);
        assert(k4_a0_records().take(before.journal@.len() as int)
            == before_journal);
        k_update_inv_lifts_through_replay_push(
            state.durable, cfg, before_journal, spec_record,
        );
        assert(k_journal_seq_view(state.journal@)
            == before_journal.push(spec_record));
        assert(k4_a0_records().take(
            before.journal@.len() as int + 1,
        ) =~= k4_a0_records().take(
            before.journal@.len() as int,
        ).push(k4_a0_records()[before.journal@.len() as int]));
        assert(k_journal_seq_view(state.journal@)
            == k4_a0_records().take(state.journal@.len() as int));
        assert(k_ack_seq_view(state.ack_cuts@)
            == k4_a0_cuts((state.journal@.len() - 1) as nat));
        assert(k_append_view(*state)
            == append_layer::apply(before_view, event));
        assert(state.journal@.last() == record);
        assert(lsn as nat == state.journal@.len());
        assert(k3_control_exact(*state));
    }
    Option::Some(lsn)
}

pub fn k4_a1_append_one(
    config: &KManifestConfig,
    state: &mut KKernelState,
    record: KJournalRecord,
) -> (cut: u64)
    requires
        k4_a1_profile_state(*config, *old(state)),
        old(state).append is Idle,
        old(state).journal@.len() < 6,
        record == k4_a1_expected_record(
            (old(state).journal@.len() + 1) as u64,
        ),
    ensures
        k4_a1_profile_state(*config, *final(state)),
        final(state).append is Idle,
        final(state).journal@ == old(state).journal@.push(record),
        final(state).ack_cuts@ == old(state).ack_cuts@.push(cut),
        cut as nat == old(state).journal@.len() + 1,
{
    let old_len = state.journal.len();
    let accepted = k4_a1_try_call(config, state, record);
    proof { assert(accepted); }
    let linearized = k4_a1_linearize(config, state, record);
    let lsn = match linearized {
        Option::Some(value) => value,
        Option::None => 0,
    };
    proof { assert(linearized.is_some()); }
    let returned = k4_a1_return(config, state);
    let returned_cut = match returned {
        Option::Some(value) => value,
        Option::None => 0,
    };
    proof {
        assert(returned.is_some());
        assert(lsn as nat == old_len + 1);
        assert(returned_cut == lsn);
    }
    returned_cut
}

pub fn k4_a1_manifest_append_witness()
    -> (result: (bool, usize, usize, u64, usize))
    ensures
        result == (true, 6usize, 6usize, 6u64, 1usize),
{
    let config = k4_idempotent_manifest();
    let mut state = k4_a1_initial(&config);

    let first = k4_a1_expected_record_exec(1);
    let cut1 = k4_a1_append_one(&config, &mut state, first);
    proof { assert(cut1 == 1u64); }
    let second = k4_a1_expected_record_exec(2);
    let cut2 = k4_a1_append_one(&config, &mut state, second);
    proof { assert(cut2 == 2u64); }
    let third = k4_a1_expected_record_exec(3);
    let cut3 = k4_a1_append_one(&config, &mut state, third);
    proof { assert(cut3 == 3u64); }
    let fourth = k4_a1_expected_record_exec(4);
    let cut4 = k4_a1_append_one(&config, &mut state, fourth);
    proof { assert(cut4 == 4u64); }
    let fifth = k4_a1_expected_record_exec(5);
    let cut5 = k4_a1_append_one(&config, &mut state, fifth);
    proof { assert(cut5 == 5u64); }
    let sixth = k4_a1_expected_record_exec(6);
    let cut6 = k4_a1_append_one(&config, &mut state, sixth);
    proof { assert(cut6 == 6u64); }

    let request_count = state.durable.requests.len();
    let journal_count = state.journal.len();
    let ack_count = state.ack_cuts.len();
    proof {
        k4_a1_terminal_state(config, state);
    }
    let phase_committed = match state.durable.requests.first() {
        Option::Some(entry) => match entry.phase {
            KPhase::Committed => true,
            _ => false,
        },
        Option::None => false,
    };
    let attempt_count = match state.durable.requests.first() {
        Option::Some(entry) => entry.outcomes.len(),
        Option::None => 0,
    };
    proof {
        assert(request_count == 1);
        assert(journal_count == 6);
        assert(ack_count == 6);
        assert(phase_committed);
        assert(attempt_count == 1);
    }
    (phase_committed, journal_count, ack_count, cut6, attempt_count)
}

pub proof fn k4_a1_terminal_state(
    config: KManifestConfig,
    state: KKernelState,
)
    requires
        k4_a1_profile_state(config, state),
        state.append is Idle,
        state.journal@.len() == 6,
    ensures
        replay_layer::replay(
            k_manifest_config_view(config), k4_a0_records(),
        ).phase[k4_a0_request()] == replay_layer::Phase::Committed,
        state.durable.requests@.len() == 1,
        state.durable.requests@[0].phase == KPhase::Committed,
        state.durable.requests@[0].outcomes@.len() == 1,
        state.durable.requests@[0].outcomes@[0]
            == Option::Some(KObservation::Success { value: 1 }),
{
    let cfg = k_manifest_config_view(config);
    let journal = k_journal_seq_view(state.journal@);
    let durable = replay_layer::replay(cfg, journal);
    k4_a0_manifest_append_certificate(config);
    assert(journal == k4_a0_records());
    assert(durable == replay_layer::replay(cfg, k4_a0_records()));
    assert(durable.phase[k4_a0_request()]
        == replay_layer::Phase::Committed);
    assert(state.durable.requests@.len() == 1);
    let entry = state.durable.requests@[0];
    assert(k_request_entry_couples(entry, durable));
    assert(k_phase_view(entry.phase)
        == replay_layer::Phase::Committed);
    match entry.phase {
        KPhase::Committed => {},
        KPhase::New
        | KPhase::Authorized
        | KPhase::Prepared
        | KPhase::Armed
        | KPhase::Failed
        | KPhase::Unknown => { assert(false); },
    }
    query_layer::replay_d_started_exact(
        cfg, k4_a0_records(), k4_a0_request(),
    );
    reveal_with_fuel(replay_layer::started_count, 8);
    assert(query_layer::d_started(
        durable, k4_a0_request(),
    ) == 1nat);
    assert(entry.outcomes@.len() == 1);
    query_layer::replay_d_outcome_exact(
        cfg, k4_a0_records(), k4_a0_request(), 1nat,
    );
    reveal_with_fuel(replay_layer::outcome_observation, 8);
    assert(query_layer::d_outcome(
        durable, k4_a0_request(), 1nat,
    ) == Option::Some(
        replay_layer::Observation::Success(k4_a0_value()),
    ));
    assert(k_outcome_view(entry.outcomes@[0])
        == Option::Some(
            replay_layer::Observation::Success(k4_a0_value()),
        ));
    assert(entry.outcomes@[0]
        == Option::Some(KObservation::Success { value: 1 }));
}

} // verus!
