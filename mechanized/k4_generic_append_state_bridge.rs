use vstd::prelude::*;

#[path = "k4_manifest_append_state_bridge.rs"]
pub mod k4_a1_layer;

verus! {

use k4_a1_layer::*;
use k4_a1_layer::k4_a0_layer::k4_r7_layer::{
    k_manifest_apply_commit, k_manifest_commit_enabled,
};
use k4_a1_layer::k4_a0_layer::{
    k4_a0_manifest_append_certificate, k4_a0_manifest_profile,
    k4_a0_manifest_records_legal, k4_a0_records, k4_a0_request,
    k4_a0_value,
};
use k4_a1_layer::k4_a0_layer::k4_r7_layer::k4_r6_layer::{
    k_manifest_apply_outcome, k_manifest_outcome_enabled,
};
use k4_a1_layer::k4_a0_layer::k4_r7_layer::k4_r6_layer::k4_r5_layer::{
    k_manifest_apply_start,
};
use k4_a1_layer::k4_a0_layer::k4_r7_layer::k4_r6_layer::k4_r5_layer::k4_r4_layer::{
    k_manifest_apply_arm, k_manifest_arm_enabled,
};
use k4_a1_layer::k4_a0_layer::k4_r7_layer::k4_r6_layer::k4_r5_layer::k4_r4_layer::k4_r3_layer::{
    k_manifest_apply_prepare,
};
use k4_a1_layer::k4_a0_layer::k4_r7_layer::k4_r6_layer::k4_r5_layer::k4_r4_layer::k4_r3_layer::k4_r2_layer::{
    k_manifest_apply_authorize,
};
use k4_a1_layer::k4_a0_layer::k4_r7_layer::k4_r6_layer::k4_r5_layer::k4_r4_layer::k4_r3_layer::k4_r2_layer::k4_r1_layer::{
    k_manifest_attempt_profile, k_manifest_prepare_enabled,
    k_manifest_start_enabled,
};
use k4_a1_layer::k4_a0_layer::k4_r7_layer::k4_r6_layer::k4_r5_layer::k4_r4_layer::k4_r3_layer::k4_r2_layer::k4_r1_layer::k4_r0_layer::{
    k_manifest_authorize_enabled, k_manifest_capability_ids_unique,
    k_manifest_capability_lookup_hit, k_manifest_capability_lookup_none,
    k_manifest_find_capability,
};
use k4_a1_layer::k4_a0_layer::k4_r7_layer::k4_r6_layer::k4_r5_layer::k4_r4_layer::k4_r3_layer::k4_r2_layer::k4_r1_layer::k4_r0_layer::k4_layer::{
    k4_idempotent_manifest, k_manifest_capability_lookup,
    k_manifest_config_is_well_formed, k_manifest_config_view,
    k_manifest_wf,
};
use k4_a1_layer::k4_a0_layer::k4_r7_layer::k4_r6_layer::k4_r5_layer::k4_r4_layer::k4_r3_layer::k4_r2_layer::k4_r1_layer::k4_r0_layer::k4_layer::k3_layer;
use k3_layer::*;
use k3_layer::k2_record_layer::{
    k_default_request_delta, k_default_request_delta_preserves_update_inv,
    k_initial_satisfies_update_inv, k_no_future_outcomes,
    k_push_default_request, k_update_inv,
    k_update_inv_lifts_through_replay_push,
};
use k3_layer::k2_record_layer::k2_guard_layer::k1_layer::{
    k_capability_id, k_durable_inv, k_find_capability, k_find_request,
    k_observation_view, k_outcome_view, k_phase_view,
    k_request_entry_couples, k_request_id, k_tracks_capability,
    k_tracks_request, KCapEntry, KDurable,
};
use k3_layer::k2_record_layer::k2_guard_layer::k1_layer::query_layer;
use query_layer::c1_layer;
use query_layer::c1_layer::{append_layer, replay_layer};

// Public type surface for the proof-erased integration harness. These are
// representation types only; the Verus obligations remain in this module.
pub use k4_a1_layer::k4_a0_layer::k4_r7_layer::k4_r6_layer::k4_r5_layer::k4_r4_layer::k4_r3_layer::k4_r2_layer::k4_r1_layer::k4_r0_layer::k4_layer::{
    KManifestBinding, KManifestCapability, KManifestConfig,
};
pub use k3_layer::{
    KJournalRecord, KKernelState, KObservation, KRetryClass,
};
pub use k3_layer::k2_record_layer::k2_guard_layer::k1_layer::KPhase;

// K4-A2 removes A1's exact six-record restriction. It accepts every
// structurally legal Authorize/Prepare/Arm/Start/Outcome/Commit record under
// an arbitrary well-formed manifest. Revoke, Fail, and Unknown remain outside
// this checkpoint.

pub open spec fn k4_a2_supported(record: KJournalRecord) -> bool {
    match record {
        KJournalRecord::Authorize { .. }
        | KJournalRecord::Prepare { .. }
        | KJournalRecord::Arm { .. }
        | KJournalRecord::Start { .. }
        | KJournalRecord::Outcome { .. }
        | KJournalRecord::Commit { .. } => true,
        KJournalRecord::Revoke { .. }
        | KJournalRecord::Fail { .. }
        | KJournalRecord::Unknown { .. } => false,
    }
}

pub fn k4_a2_supported_exec(record: &KJournalRecord) -> (supported: bool)
    ensures
        supported == k4_a2_supported(*record),
{
    match *record {
        KJournalRecord::Authorize { .. }
        | KJournalRecord::Prepare { .. }
        | KJournalRecord::Arm { .. }
        | KJournalRecord::Start { .. }
        | KJournalRecord::Outcome { .. }
        | KJournalRecord::Commit { .. } => true,
        KJournalRecord::Revoke { .. }
        | KJournalRecord::Fail { .. }
        | KJournalRecord::Unknown { .. } => false,
    }
}

pub open spec fn k4_a2_inv(
    config: KManifestConfig,
    state: KKernelState,
) -> bool {
    k4_a1_inv(config, state)
}

pub open spec fn k4_a2_manifest_cap_delta(
    before: KDurable,
    after: KDurable,
    capability: u64,
    budget: u64,
) -> bool {
    &&& after.requests@ == before.requests@
    &&& after.caps@.len() == before.caps@.len() + 1
    &&& after.caps@.drop_last() == before.caps@
    &&& after.caps@.last().capability == capability
    &&& after.caps@.last().remaining == budget
    &&& !after.caps@.last().revoked
}

pub fn k4_a2_push_manifest_capability(
    kd: &mut KDurable,
    capability: u64,
    budget: u64,
) -> (index: usize)
    ensures
        index as int == old(kd).caps@.len(),
        k4_a2_manifest_cap_delta(
            *old(kd), *final(kd), capability, budget,
        ),
{
    let index = kd.caps.len();
    let ghost before = kd.caps@;
    kd.caps.push(KCapEntry {
        capability,
        remaining: budget,
        revoked: false,
    });
    proof {
        assert(kd.caps@.drop_last() =~= before);
    }
    index
}

pub proof fn k4_a2_manifest_cap_delta_preserves_update_inv(
    before: KDurable,
    after: KDurable,
    cfg: replay_layer::Config,
    durable: replay_layer::DurableBroker,
    capability: u64,
    budget: u64,
)
    requires
        k_update_inv(before, cfg, durable),
        k4_a2_manifest_cap_delta(before, after, capability, budget),
        !k_tracks_capability(before, capability as nat),
        cfg.initial_budget[k_capability_id(capability)] == budget as nat,
    ensures
        k_update_inv(after, cfg, durable),
{
    let new_index = before.caps@.len() as int;
    let new_entry = after.caps@[new_index];
    assert(after.caps@.len() > 0);
    assert(new_index == after.caps@.len() - 1);
    assert(after.caps@ =~= before.caps@.push(new_entry));

    assert forall|index: int| 0 <= index < before.caps@.len() implies
        #[trigger] before.caps@[index].capability != capability by {
        if before.caps@[index].capability == capability {
            assert(exists|witness: int|
                0 <= witness < before.caps@.len()
                    && #[trigger] before.caps@[witness].capability as nat
                        == capability as nat) by {
                assert(before.caps@[index].capability as nat
                    == capability as nat);
            }
            assert(k_tracks_capability(before, capability as nat));
        }
    }
    assert forall|index: int| 0 <= index < before.caps@.len() implies
        #[trigger] after.caps@[index] == before.caps@[index] by {
    }
    assert(k_tracks_capability(after, capability as nat)) by {
        assert(new_entry.capability == capability);
        assert(exists|witness: int|
            0 <= witness < after.caps@.len()
                && #[trigger] after.caps@[witness].capability as nat
                    == capability as nat) by {
            assert(after.caps@[new_index].capability as nat
                == capability as nat);
        }
    }

    assert forall|left: int, right: int|
        0 <= left < after.caps@.len()
            && 0 <= right < after.caps@.len()
            && #[trigger] after.caps@[left].capability
                == #[trigger] after.caps@[right].capability
        implies left == right by {
        if left < before.caps@.len() && right < before.caps@.len() {
            assert(after.caps@[left] == before.caps@[left]);
            assert(after.caps@[right] == before.caps@[right]);
        } else if left < before.caps@.len() {
            assert(right == new_index);
            assert(after.caps@[right].capability == capability);
            assert(before.caps@[left].capability != capability);
        } else if right < before.caps@.len() {
            assert(left == new_index);
            assert(after.caps@[left].capability == capability);
            assert(before.caps@[right].capability != capability);
        } else {
            assert(left == new_index);
            assert(right == new_index);
        }
    }

    assert forall|index: int| 0 <= index < after.caps@.len() implies {
        let entry = #[trigger] after.caps@[index];
        &&& durable.remaining[k_capability_id(entry.capability)]
            == entry.remaining as nat
        &&& durable.revoked.contains(k_capability_id(entry.capability))
            == entry.revoked
    } by {
        let entry = after.caps@[index];
        if index < before.caps@.len() {
            assert(entry == before.caps@[index]);
        } else {
            assert(index == new_index);
            assert(entry == new_entry);
            assert(entry.capability == capability);
            assert(entry.remaining == budget);
            assert(!entry.revoked);
            let spec_capability = k_capability_id(capability);
            assert(durable.remaining[spec_capability]
                == cfg.initial_budget[spec_capability]);
            assert(durable.remaining[spec_capability] == entry.remaining as nat);
            assert(!durable.revoked.contains(spec_capability));
        }
    }

    assert forall|id: nat| k_tracks_capability(before, id) implies
        #[trigger] k_tracks_capability(after, id) by {
        let witness = choose|witness: int|
            0 <= witness < before.caps@.len()
                && #[trigger] before.caps@[witness].capability as nat == id;
        assert(after.caps@[witness] == before.caps@[witness]);
    }
    assert forall|id: nat| !k_tracks_capability(after, id) implies {
        &&& #[trigger] durable.remaining[replay_layer::CapabilityId { id }]
            == cfg.initial_budget[replay_layer::CapabilityId { id }]
        &&& !durable.revoked.contains(replay_layer::CapabilityId { id })
    } by {
        assert(!k_tracks_capability(before, id));
    }

    assert(after.requests@ == before.requests@);
    assert(k_durable_inv(after, cfg, durable));
    assert(k_no_future_outcomes(durable));
}

pub fn k4_a2_ensure_request(
    config: &KManifestConfig,
    kd: &mut KDurable,
    request: u64,
    Ghost(durable): Ghost<replay_layer::DurableBroker>,
) -> (index: usize)
    requires
        k_manifest_wf(*config),
        k_update_inv(
            *old(kd), k_manifest_config_view(*config), durable,
        ),
    ensures
        index < final(kd).requests@.len(),
        final(kd).requests@[index as int].request == request,
        k_update_inv(
            *final(kd), k_manifest_config_view(*config), durable,
        ),
        k_tracks_request(*old(kd), request as nat) ==>
            *final(kd) == *old(kd),
        !k_tracks_request(*old(kd), request as nat) ==>
            k_default_request_delta(*old(kd), *final(kd), request),
{
    match k_find_request(kd, request) {
        Option::Some(index) => {
            proof {
                assert(k_tracks_request(*kd, request as nat)) by {
                    assert(exists|witness: int|
                        0 <= witness < kd.requests@.len()
                            && #[trigger] kd.requests@[witness].request as nat
                                == request as nat) by {
                        assert(kd.requests@[index as int].request as nat
                            == request as nat);
                    }
                }
            }
            index
        },
        Option::None => {
            let ghost before = *kd;
            proof {
                assert(!k_tracks_request(before, request as nat));
            }
            let index = k_push_default_request(kd, request);
            proof {
                k_manifest_config_is_well_formed(*config);
                assert(k_manifest_config_view(*config).max_attempts[
                    k_request_id(request)
                ] > 0);
                k_default_request_delta_preserves_update_inv(
                    before,
                    *kd,
                    k_manifest_config_view(*config),
                    durable,
                    request,
                );
            }
            index
        },
    }
}

pub fn k4_a2_ensure_capability(
    config: &KManifestConfig,
    kd: &mut KDurable,
    capability: u64,
    Ghost(durable): Ghost<replay_layer::DurableBroker>,
) -> (index: usize)
    requires
        k_manifest_wf(*config),
        k_update_inv(
            *old(kd), k_manifest_config_view(*config), durable,
        ),
        durable.remaining[k_capability_id(capability)] > 0,
    ensures
        index < final(kd).caps@.len(),
        final(kd).caps@[index as int].capability == capability,
        k_update_inv(
            *final(kd), k_manifest_config_view(*config), durable,
        ),
        k_tracks_capability(*old(kd), capability as nat) ==>
            *final(kd) == *old(kd),
        !k_tracks_capability(*old(kd), capability as nat) ==>
            k4_a2_manifest_cap_delta(
                *old(kd), *final(kd), capability,
                final(kd).caps@[index as int].remaining,
            ),
{
    match k_find_capability(kd, capability) {
        Option::Some(index) => {
            proof {
                assert(k_tracks_capability(*kd, capability as nat)) by {
                    assert(exists|witness: int|
                        0 <= witness < kd.caps@.len()
                            && #[trigger] kd.caps@[witness].capability as nat
                                == capability as nat) by {
                        assert(kd.caps@[index as int].capability as nat
                            == capability as nat);
                    }
                }
            }
            index
        },
        Option::None => {
            let ghost before = *kd;
            proof {
                assert(!k_tracks_capability(before, capability as nat));
                assert(durable.remaining[k_capability_id(capability)]
                    == k_manifest_config_view(*config).initial_budget[
                        k_capability_id(capability)
                    ]);
                assert(k_manifest_config_view(*config).initial_budget[
                    k_capability_id(capability)
                ] > 0);
            }
            let found = k_manifest_find_capability(config, capability);
            let manifest_index = match found {
                Option::Some(index) => index,
                Option::None => {
                    proof {
                        assert forall|index: int|
                            0 <= index < config.capabilities@.len() implies
                                #[trigger] config.capabilities@[index].capability
                                    as nat != capability as nat by {
                        }
                        k_manifest_capability_lookup_none(
                            config.capabilities@, capability as nat,
                        );
                        assert(k_manifest_capability_lookup(
                            config.capabilities@, capability as nat,
                        ).is_none());
                        assert(k_manifest_config_view(*config).initial_budget[
                            k_capability_id(capability)
                        ] == 0nat);
                        assert(false);
                    }
                    return 0;
                },
            };
            let budget = config.capabilities[manifest_index].initial_budget;
            let index = k4_a2_push_manifest_capability(
                kd, capability, budget,
            );
            proof {
                assert(k_manifest_capability_ids_unique(
                    config.capabilities@,
                ));
                k_manifest_capability_lookup_hit(
                    config.capabilities@,
                    capability as nat,
                    manifest_index as int,
                );
                assert(k_manifest_capability_lookup(
                    config.capabilities@, capability as nat,
                ) == Option::Some(config.capabilities@[manifest_index as int]));
                assert(k_manifest_config_view(*config).initial_budget[
                    k_capability_id(capability)
                ] == budget as nat);
                k4_a2_manifest_cap_delta_preserves_update_inv(
                    before,
                    *kd,
                    k_manifest_config_view(*config),
                    durable,
                    capability,
                    budget,
                );
            }
            index
        },
    }
}

pub fn k4_a2_semantic_record_enabled(
    config: &KManifestConfig,
    durable: &KDurable,
    record: &KJournalRecord,
    Ghost(abstract_durable): Ghost<replay_layer::DurableBroker>,
) -> (enabled: bool)
    requires
        k_manifest_wf(*config),
        k_durable_inv(
            *durable, k_manifest_config_view(*config), abstract_durable,
        ),
    ensures
        enabled == (
            k4_a2_supported(*record)
                && query_layer::abstract_record_enabled(
                    k_manifest_config_view(*config),
                    abstract_durable,
                    k_journal_record_view(*record),
                )
        ),
{
    match *record {
        KJournalRecord::Authorize { request, capability, digest } =>
            k_manifest_authorize_enabled(
                config, durable, request, capability, digest,
                Ghost(abstract_durable),
            ),
        KJournalRecord::Prepare {
            request, class, digest, key_present, key, ..
        } => k_manifest_prepare_enabled(
            config, durable, request, class, digest, key_present, key,
            Ghost(abstract_durable),
        ),
        KJournalRecord::Arm {
            request, digest, key_present, key, ..
        } => k_manifest_arm_enabled(
            config, durable, request, digest, key_present, key,
            Ghost(abstract_durable),
        ),
        KJournalRecord::Start {
            request, attempt, digest, key_present, key, ..
        } => {
            if attempt < 0xffff_ffff_ffff_ffffu64 {
                k_manifest_start_enabled(
                    config, durable, request, attempt, digest,
                    key_present, key, Ghost(abstract_durable),
                )
            } else {
                let profile = k_manifest_attempt_profile(config, request);
                proof {
                    assert(profile.2 == 1 || profile.2 == 3);
                    assert(profile.2 as nat
                        == k_manifest_config_view(*config).max_attempts[
                            k_request_id(request)
                        ]);
                    assert(attempt as nat
                        > k_manifest_config_view(*config).max_attempts[
                            k_request_id(request)
                        ]);
                    assert(!query_layer::abstract_record_enabled(
                        k_manifest_config_view(*config),
                        abstract_durable,
                        k_journal_record_view(*record),
                    ));
                }
                false
            }
        },
        KJournalRecord::Outcome {
            request, attempt, observation, digest, key_present, key, ..
        } => k_manifest_outcome_enabled(
            config, durable, request, attempt, observation, digest,
            key_present, key, Ghost(abstract_durable),
        ),
        KJournalRecord::Commit {
            request, attempt, value, digest, key_present, key, ..
        } => k_manifest_commit_enabled(
            config, durable, request, attempt, value, digest,
            key_present, key, Ghost(abstract_durable),
        ),
        KJournalRecord::Revoke { .. }
        | KJournalRecord::Fail { .. }
        | KJournalRecord::Unknown { .. } => false,
    }
}

pub fn k4_a2_exact_references_enabled(
    journal: &Vec<KJournalRecord>,
    record: &KJournalRecord,
) -> (enabled: bool)
    requires
        journal@.len() <= 0xffff_ffff_ffff_ffff,
    ensures
        enabled == (
            k4_a2_supported(*record)
                && k_exact_references(
                    k_journal_seq_view(journal@),
                    k_journal_record_view(*record),
                )
        ),
{
    match *record {
        KJournalRecord::Authorize { .. } => true,
        KJournalRecord::Prepare { request, auth_ref, .. } => {
            let found = k_find_latest_reference(
                journal, KReferenceKind::Authorize, request, 0,
            );
            proof {
                k_latest_reference_view_exact(
                    journal@, KReferenceKind::Authorize, request, 0,
                );
            }
            found == Option::Some(auth_ref)
        },
        KJournalRecord::Arm { request, prepare_ref, .. } => {
            let found = k_find_latest_reference(
                journal, KReferenceKind::Prepare, request, 0,
            );
            proof {
                k_latest_reference_view_exact(
                    journal@, KReferenceKind::Prepare, request, 0,
                );
            }
            found == Option::Some(prepare_ref)
        },
        KJournalRecord::Start { request, arm_ref, .. } => {
            let found = k_find_latest_reference(
                journal, KReferenceKind::Arm, request, 0,
            );
            proof {
                k_latest_reference_view_exact(
                    journal@, KReferenceKind::Arm, request, 0,
                );
            }
            found == Option::Some(arm_ref)
        },
        KJournalRecord::Outcome {
            request, attempt, start_ref, ..
        } => {
            let found = k_find_latest_reference(
                journal, KReferenceKind::Start, request, attempt,
            );
            proof {
                k_latest_reference_view_exact(
                    journal@, KReferenceKind::Start, request, attempt,
                );
            }
            found == Option::Some(start_ref)
        },
        KJournalRecord::Commit {
            request, attempt, outcome_ref, ..
        } => {
            let found = k_find_latest_reference(
                journal, KReferenceKind::Outcome, request, attempt,
            );
            proof {
                k_latest_reference_view_exact(
                    journal@, KReferenceKind::Outcome, request, attempt,
                );
            }
            found == Option::Some(outcome_ref)
        },
        KJournalRecord::Revoke { .. }
        | KJournalRecord::Fail { .. }
        | KJournalRecord::Unknown { .. } => false,
    }
}

pub fn k4_a2_structural_record_enabled(
    config: &KManifestConfig,
    durable: &KDurable,
    journal: &Vec<KJournalRecord>,
    record: &KJournalRecord,
) -> (enabled: bool)
    requires
        journal@.len() < 0xffff_ffff_ffff_ffff,
        k_manifest_wf(*config),
        replay_layer::config_wf(k_manifest_config_view(*config)),
        replay_layer::journal_legal(
            k_manifest_config_view(*config),
            k_journal_seq_view(journal@),
        ),
        k_update_inv(
            *durable,
            k_manifest_config_view(*config),
            replay_layer::replay(
                k_manifest_config_view(*config),
                k_journal_seq_view(journal@),
            ),
        ),
    ensures
        enabled == (
            k4_a2_supported(*record)
                && replay_layer::structural_enabled(
                    k_manifest_config_view(*config),
                    k_journal_seq_view(journal@),
                    k_journal_record_view(*record),
                )
        ),
{
    let ghost cfg = k_manifest_config_view(*config);
    let ghost records = k_journal_seq_view(journal@);
    let ghost abstract_durable = replay_layer::replay(cfg, records);
    let semantic = k4_a2_semantic_record_enabled(
        config, durable, record, Ghost(abstract_durable),
    );
    if semantic {
        let exact = k4_a2_exact_references_enabled(journal, record);
        proof {
            k_abstract_exact_is_structural(
                cfg, records, k_journal_record_view(*record),
            );
        }
        exact
    } else {
        proof {
            k_abstract_exact_is_structural(
                cfg, records, k_journal_record_view(*record),
            );
        }
        false
    }
}

pub fn k4_a2_initial(config: &KManifestConfig) -> (state: KKernelState)
    requires
        k_manifest_wf(*config),
    ensures
        k4_a2_inv(*config, state),
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
            state.durable, k_manifest_config_view(*config),
        );
        append_layer::initial_invariant::<replay_layer::JournalRecord>();
        assert(k_journal_seq_view(state.journal@) =~= Seq::empty());
        assert(k_ack_seq_view(state.ack_cuts@) =~= Seq::empty());
        assert(k_append_view(state)
            == append_layer::initial_state::<replay_layer::JournalRecord>());
        assert(append_layer::legal_control_shape(
            c1_layer::c1_eligibility(k_manifest_config_view(*config)),
            k_append_view(state),
        ));
    }
    state
}

pub open spec fn k4_a2_call_expected(
    config: KManifestConfig,
    state: KKernelState,
    record: KJournalRecord,
) -> bool {
    &&& state.journal@.len() < 0xffff_ffff_ffff_ffff
    &&& k4_a2_supported(record)
    &&& replay_layer::structural_enabled(
        k_manifest_config_view(config),
        k_journal_seq_view(state.journal@),
        k_journal_record_view(record),
    )
}

pub fn k4_a2_try_call(
    config: &KManifestConfig,
    state: &mut KKernelState,
    record: KJournalRecord,
) -> (accepted: bool)
    requires
        k4_a2_inv(*config, *old(state)),
        old(state).append is Idle,
    ensures
        k4_a2_inv(*config, *final(state)),
        accepted == k4_a2_call_expected(*config, *old(state), record),
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
    if journal_len == 0xffff_ffff_ffff_ffffu64 {
        proof { assert(!k4_a2_call_expected(*config, *state, record)); }
        return false;
    }
    let enabled = k4_a2_structural_record_enabled(
        config, &state.durable, &state.journal, &record,
    );
    if !enabled {
        proof { assert(!k4_a2_call_expected(*config, *state, record)); }
        return false;
    }

    let ghost before = *state;
    let ghost before_view = k_append_view(before);
    let ghost cfg = k_manifest_config_view(*config);
    let ghost event = append_layer::Event::Call {
        record: k_journal_record_view(record),
    };
    proof {
        assert(k4_a2_supported(record));
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
        assert(k4_a2_call_expected(*config, before, record));
    }
    true
}

pub open spec fn k4_a2_linearize_expected(
    state: KKernelState,
    record: KJournalRecord,
) -> bool {
    &&& k4_a2_supported(record)
    &&& match state.append {
        KAppendControl::Called { record: called } => called == record,
        KAppendControl::Idle | KAppendControl::Linearized { .. } => false,
    }
}

pub fn k4_a2_linearize(
    config: &KManifestConfig,
    state: &mut KKernelState,
    record: KJournalRecord,
) -> (linearized: Option<u64>)
    requires
        k4_a2_inv(*config, *old(state)),
    ensures
        k4_a2_inv(*config, *final(state)),
        linearized.is_some()
            == k4_a2_linearize_expected(*old(state), record),
        match linearized {
            Option::None => *final(state) == *old(state),
            Option::Some(lsn) => {
                &&& final(state).journal@
                    == old(state).journal@.push(record)
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
{
    let called = match state.append {
        KAppendControl::Called { record: called } => called,
        KAppendControl::Idle | KAppendControl::Linearized { .. } => {
            proof {
                assert(!k4_a2_linearize_expected(*state, record));
            }
            return Option::None;
        },
    };
    if !k_journal_record_equal(called, record) {
        proof {
            assert(called != record);
            assert(!k4_a2_linearize_expected(*state, record));
        }
        return Option::None;
    }
    let supported = k4_a2_supported_exec(&record);
    if !supported {
        proof {
            assert(!k4_a2_supported(record));
            assert(!k4_a2_linearize_expected(*state, record));
        }
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
        assert(before.append == KAppendControl::Called { record });
        assert(before_view.append
            == append_layer::AppendControl::Called {
                record: spec_record,
            });
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
        assert(k4_a2_linearize_expected(before, record));
    }

    match record {
        KJournalRecord::Authorize { request, capability, digest } => {
            let request_index = k4_a2_ensure_request(
                config, &mut state.durable, request, Ghost(durable),
            );
            proof {
                assert(query_layer::abstract_record_enabled(
                    cfg, durable, spec_record,
                ));
                assert(durable.remaining[k_capability_id(capability)] > 0);
            }
            let cap_index = k4_a2_ensure_capability(
                config, &mut state.durable, capability, Ghost(durable),
            );
            k_manifest_apply_authorize(
                config, &mut state.durable, request_index, cap_index,
                request, capability, digest, Ghost(durable),
            );
        },
        KJournalRecord::Prepare {
            request, class, digest, key_present, key, auth_ref,
        } => {
            let request_index = k4_a2_ensure_request(
                config, &mut state.durable, request, Ghost(durable),
            );
            k_manifest_apply_prepare(
                config, &mut state.durable, request_index, request,
                class, digest, key_present, key, auth_ref, Ghost(durable),
            );
        },
        KJournalRecord::Arm {
            request, digest, key_present, key, prepare_ref,
        } => {
            let request_index = k4_a2_ensure_request(
                config, &mut state.durable, request, Ghost(durable),
            );
            k_manifest_apply_arm(
                config, &mut state.durable, request_index, request,
                digest, key_present, key, prepare_ref, Ghost(durable),
            );
        },
        KJournalRecord::Start {
            request, attempt, digest, key_present, key, arm_ref,
        } => {
            let request_index = k4_a2_ensure_request(
                config, &mut state.durable, request, Ghost(durable),
            );
            k_manifest_apply_start(
                config, &mut state.durable, request_index, request,
                attempt, digest, key_present, key, arm_ref, Ghost(durable),
            );
        },
        KJournalRecord::Outcome {
            request, attempt, observation, digest,
            key_present, key, start_ref,
        } => {
            let request_index = k4_a2_ensure_request(
                config, &mut state.durable, request, Ghost(durable),
            );
            k_manifest_apply_outcome(
                config, &mut state.durable, request_index, request,
                attempt, observation, digest, key_present, key,
                start_ref, Ghost(durable),
            );
        },
        KJournalRecord::Commit {
            request, attempt, value, digest,
            key_present, key, outcome_ref,
        } => {
            let request_index = k4_a2_ensure_request(
                config, &mut state.durable, request, Ghost(durable),
            );
            k_manifest_apply_commit(
                config, &mut state.durable, request_index, request,
                attempt, value, digest, key_present, key,
                outcome_ref, Ghost(durable),
            );
        },
        KJournalRecord::Revoke { .. }
        | KJournalRecord::Fail { .. }
        | KJournalRecord::Unknown { .. } => {
            proof { assert(false); }
            return Option::None;
        },
    }

    proof {
        assert(state.journal@ == before.journal@);
        assert(state.ack_cuts@ == before.ack_cuts@);
        assert(state.append == before.append);
    }
    let old_len = state.journal.len();
    let lsn = old_len as u64 + 1;
    state.journal.push(record);
    state.append = KAppendControl::Linearized { record, lsn };
    proof {
        k_journal_seq_view_push(before.journal@, record);
        k_journal_seq_view_len(before.journal@);
        k_update_inv_lifts_through_replay_push(
            state.durable, cfg, before_journal, spec_record,
        );
        assert(k_journal_seq_view(state.journal@)
            == before_journal.push(spec_record));
        assert(k_append_view(*state)
            == append_layer::apply(before_view, event));
        assert(state.journal@.last() == record);
        assert(lsn as nat == state.journal@.len());
        assert(k3_control_exact(*state));
    }
    Option::Some(lsn)
}

pub fn k4_a2_return(
    config: &KManifestConfig,
    state: &mut KKernelState,
) -> (returned: Option<u64>)
    requires
        k4_a2_inv(*config, *old(state)),
    ensures
        k4_a2_inv(*config, *final(state)),
        returned.is_some() <==> old(state).append is Linearized,
        match returned {
            Option::None => *final(state) == *old(state),
            Option::Some(cut) => {
                &&& final(state).durable == old(state).durable
                &&& final(state).journal@ == old(state).journal@
                &&& final(state).ack_cuts@
                    == old(state).ack_cuts@.push(cut)
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
    let ghost cfg = k_manifest_config_view(*config);
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
            c1_layer::c1_eligibility(cfg), before_view, event,
        ));
        append_layer::step_preserves_invariant(before_view, event);
        append_layer::step_preserves_legal_control(
            c1_layer::c1_eligibility(cfg), before_view, event,
        );
        append_layer::take_full(before_view.evidence.records);
    }
    state.ack_cuts.push(cut);
    state.append = KAppendControl::Idle;
    proof {
        k_ack_seq_view_push(before.ack_cuts@, cut);
        assert(k_append_view(*state)
            == append_layer::apply(before_view, event));
        assert(k3_control_exact(*state));
    }
    Option::Some(cut)
}

pub fn k4_a2_append_one(
    config: &KManifestConfig,
    state: &mut KKernelState,
    record: KJournalRecord,
) -> (cut: u64)
    requires
        k4_a2_inv(*config, *old(state)),
        old(state).append is Idle,
        old(state).journal@.len() < 0xffff_ffff_ffff_ffff,
        k4_a2_supported(record),
        replay_layer::structural_enabled(
            k_manifest_config_view(*config),
            k_journal_seq_view(old(state).journal@),
            k_journal_record_view(record),
        ),
    ensures
        k4_a2_inv(*config, *final(state)),
        final(state).append is Idle,
        final(state).journal@ == old(state).journal@.push(record),
        final(state).ack_cuts@ == old(state).ack_cuts@.push(cut),
        cut as nat == old(state).journal@.len() + 1,
{
    let old_len = state.journal.len();
    let accepted = k4_a2_try_call(config, state, record);
    proof { assert(accepted); }
    let linearized = k4_a2_linearize(config, state, record);
    let lsn = match linearized {
        Option::Some(value) => value,
        Option::None => 0,
    };
    proof { assert(linearized.is_some()); }
    let returned = k4_a2_return(config, state);
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

pub proof fn k4_a2_journal_push_view(
    before: KKernelState,
    after: KKernelState,
    record: KJournalRecord,
)
    requires
        after.journal@ == before.journal@.push(record),
    ensures
        k_journal_seq_view(after.journal@)
            == k_journal_seq_view(before.journal@).push(
                k_journal_record_view(record),
            ),
{
    k_journal_seq_view_push(before.journal@, record);
    assert(after.journal@ =~= before.journal@.push(record));
}

pub proof fn k4_a2_committed_reflects(
    config: KManifestConfig,
    state: KKernelState,
    request: u64,
)
    requires
        k4_a2_inv(config, state),
        replay_layer::replay(
            k_manifest_config_view(config),
            k_journal_seq_view(state.journal@),
        ).phase[k_request_id(request)] == replay_layer::Phase::Committed,
    ensures
        exists|index: int| {
            &&& 0 <= index < state.durable.requests@.len()
            &&& state.durable.requests@[index].request == request
            &&& state.durable.requests@[index].phase == KPhase::Committed
        },
{
    let cfg = k_manifest_config_view(config);
    let journal = k_journal_seq_view(state.journal@);
    let durable = replay_layer::replay(cfg, journal);
    assert(k_tracks_request(state.durable, request as nat)) by {
        if !k_tracks_request(state.durable, request as nat) {
            assert(durable.phase[k_request_id(request)]
                == replay_layer::Phase::New);
            assert(false);
        }
    }
    let index = choose|index: int|
        0 <= index < state.durable.requests@.len()
            && #[trigger] state.durable.requests@[index].request as nat
                == request as nat;
    let entry = state.durable.requests@[index];
    assert(entry.request == request);
    assert(k_request_entry_couples(entry, durable));
    assert(k_phase_view(entry.phase) == replay_layer::Phase::Committed);
    match entry.phase {
        KPhase::Committed => {},
        KPhase::New
        | KPhase::Authorized
        | KPhase::Prepared
        | KPhase::Armed
        | KPhase::Failed
        | KPhase::Unknown => { assert(false); },
    }
    assert(exists|candidate: int| {
        &&& 0 <= candidate < state.durable.requests@.len()
        &&& state.durable.requests@[candidate].request == request
        &&& state.durable.requests@[candidate].phase == KPhase::Committed
    }) by {
        assert(0 <= index < state.durable.requests@.len());
    }
}

pub proof fn k4_a2_terminal_state(
    config: KManifestConfig,
    state: KKernelState,
)
    requires
        k4_a2_inv(config, state),
        k4_a0_manifest_profile(config),
        state.append is Idle,
        k_journal_seq_view(state.journal@) == k4_a0_records(),
    ensures
        exists|index: int| {
            &&& 0 <= index < state.durable.requests@.len()
            &&& state.durable.requests@[index].request == 1
            &&& state.durable.requests@[index].phase == KPhase::Committed
            &&& state.durable.requests@[index].outcomes@.len() == 1
            &&& state.durable.requests@[index].outcomes@[0]
                == Option::Some(KObservation::Success { value: 1 })
        },
{
    let cfg = k_manifest_config_view(config);
    let journal = k_journal_seq_view(state.journal@);
    let durable = replay_layer::replay(cfg, journal);
    k4_a0_manifest_append_certificate(config);
    assert(journal == k4_a0_records());
    assert(durable == replay_layer::replay(cfg, k4_a0_records()));
    assert(durable.phase[k4_a0_request()]
        == replay_layer::Phase::Committed);
    k4_a2_committed_reflects(config, state, 1);
    assert(k_tracks_request(state.durable, 1nat));
    let index = choose|index: int|
        0 <= index < state.durable.requests@.len()
            && #[trigger] state.durable.requests@[index].request as nat == 1nat;
    let entry = state.durable.requests@[index];
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
    assert(exists|candidate: int| {
        &&& 0 <= candidate < state.durable.requests@.len()
        &&& state.durable.requests@[candidate].request == 1
        &&& state.durable.requests@[candidate].phase == KPhase::Committed
        &&& state.durable.requests@[candidate].outcomes@.len() == 1
        &&& state.durable.requests@[candidate].outcomes@[0]
            == Option::Some(KObservation::Success { value: 1 })
    }) by {
        assert(0 <= index < state.durable.requests@.len());
    }
}

// A1 remains a premise-free nonvacuity witness for A2's generic operations.
// This wrapper verifies that the unrestricted implementation accepts the same
// six-record profile from an empty manifest-derived state.
pub fn k4_a2_manifest_append_witness()
    -> (result: (usize, usize, u64))
    ensures
        result == (6usize, 6usize, 6u64),
        exists|config: KManifestConfig, state: KKernelState| {
            &&& k4_a0_manifest_profile(config)
            &&& k4_a2_inv(config, state)
            &&& state.append is Idle
            &&& k_journal_seq_view(state.journal@) == k4_a0_records()
            &&& exists|index: int| {
                &&& 0 <= index < state.durable.requests@.len()
                &&& state.durable.requests@[index].request == 1
                &&& state.durable.requests@[index].phase
                    == KPhase::Committed
                &&& state.durable.requests@[index].outcomes@.len() == 1
                &&& state.durable.requests@[index].outcomes@[0]
                    == Option::Some(
                        KObservation::Success { value: 1 },
                    )
            }
        },
{
    let config = k4_idempotent_manifest();
    let mut state = k4_a2_initial(&config);
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
    let ghost before_first = state;
    let cut1 = k4_a2_append_one(&config, &mut state, first);
    proof {
        k4_a2_journal_push_view(before_first, state, first);
        assert(k_journal_seq_view(state.journal@)
            == k4_a0_records().take(1));
    }
    proof { assert(cut1 == 1u64); }
    let second = k4_a1_expected_record_exec(2);
    proof {
        assert(k_journal_seq_view(state.journal@)
            == k4_a0_records().take(1));
        assert(k_journal_record_view(second) == k4_a0_records()[1]);
        replay_layer::journal_legal_take(
            k_manifest_config_view(config), k4_a0_records(), 2nat,
        );
        replay_layer::journal_legal_last(
            k_manifest_config_view(config), k4_a0_records().take(2),
        );
    }
    let ghost before_second = state;
    let cut2 = k4_a2_append_one(&config, &mut state, second);
    proof {
        k4_a2_journal_push_view(before_second, state, second);
        assert(k_journal_seq_view(state.journal@)
            == k4_a0_records().take(2));
    }
    proof { assert(cut2 == 2u64); }
    let third = k4_a1_expected_record_exec(3);
    proof {
        assert(k_journal_seq_view(state.journal@)
            == k4_a0_records().take(2));
        assert(k_journal_record_view(third) == k4_a0_records()[2]);
        replay_layer::journal_legal_take(
            k_manifest_config_view(config), k4_a0_records(), 3nat,
        );
        replay_layer::journal_legal_last(
            k_manifest_config_view(config), k4_a0_records().take(3),
        );
    }
    let ghost before_third = state;
    let cut3 = k4_a2_append_one(&config, &mut state, third);
    proof {
        k4_a2_journal_push_view(before_third, state, third);
        assert(k_journal_seq_view(state.journal@)
            == k4_a0_records().take(3));
    }
    proof { assert(cut3 == 3u64); }
    let fourth = k4_a1_expected_record_exec(4);
    proof {
        assert(k_journal_seq_view(state.journal@)
            == k4_a0_records().take(3));
        assert(k_journal_record_view(fourth) == k4_a0_records()[3]);
        replay_layer::journal_legal_take(
            k_manifest_config_view(config), k4_a0_records(), 4nat,
        );
        replay_layer::journal_legal_last(
            k_manifest_config_view(config), k4_a0_records().take(4),
        );
    }
    let ghost before_fourth = state;
    let cut4 = k4_a2_append_one(&config, &mut state, fourth);
    proof {
        k4_a2_journal_push_view(before_fourth, state, fourth);
        assert(k_journal_seq_view(state.journal@)
            == k4_a0_records().take(4));
    }
    proof { assert(cut4 == 4u64); }
    let fifth = k4_a1_expected_record_exec(5);
    proof {
        assert(k_journal_seq_view(state.journal@)
            == k4_a0_records().take(4));
        assert(k_journal_record_view(fifth) == k4_a0_records()[4]);
        replay_layer::journal_legal_take(
            k_manifest_config_view(config), k4_a0_records(), 5nat,
        );
        replay_layer::journal_legal_last(
            k_manifest_config_view(config), k4_a0_records().take(5),
        );
    }
    let ghost before_fifth = state;
    let cut5 = k4_a2_append_one(&config, &mut state, fifth);
    proof {
        k4_a2_journal_push_view(before_fifth, state, fifth);
        assert(k_journal_seq_view(state.journal@)
            == k4_a0_records().take(5));
    }
    proof { assert(cut5 == 5u64); }
    let sixth = k4_a1_expected_record_exec(6);
    proof {
        assert(k_journal_seq_view(state.journal@)
            == k4_a0_records().take(5));
        assert(k_journal_record_view(sixth) == k4_a0_records()[5]);
        replay_layer::journal_legal_last(
            k_manifest_config_view(config), k4_a0_records(),
        );
    }
    let ghost before_sixth = state;
    let cut6 = k4_a2_append_one(&config, &mut state, sixth);
    proof {
        k4_a2_journal_push_view(before_sixth, state, sixth);
        assert(k_journal_seq_view(state.journal@) == k4_a0_records());
    }
    proof { assert(cut6 == 6u64); }

    proof {
        assert(k_journal_seq_view(state.journal@) == k4_a0_records());
        k4_a2_terminal_state(config, state);
    }
    proof {
        assert(state.journal@.len() == 6);
        assert(state.ack_cuts@.len() == 6);
        assert(exists|candidate_config: KManifestConfig,
                       candidate_state: KKernelState| {
            &&& k4_a0_manifest_profile(candidate_config)
            &&& k4_a2_inv(candidate_config, candidate_state)
            &&& candidate_state.append is Idle
            &&& k_journal_seq_view(candidate_state.journal@)
                == k4_a0_records()
            &&& exists|index: int| {
                &&& 0 <= index < candidate_state.durable.requests@.len()
                &&& candidate_state.durable.requests@[index].request == 1
                &&& candidate_state.durable.requests@[index].phase
                    == KPhase::Committed
                &&& candidate_state.durable.requests@[index].outcomes@.len()
                    == 1
                &&& candidate_state.durable.requests@[index].outcomes@[0]
                    == Option::Some(
                        KObservation::Success { value: 1 },
                    )
            }
        }) by {
            assert(k4_a0_manifest_profile(config));
        }
    }
    (state.journal.len(), state.ack_cuts.len(), cut6)
}

} // verus!
