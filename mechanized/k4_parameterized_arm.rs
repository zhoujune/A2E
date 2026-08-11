use vstd::prelude::*;

#[path = "k4_parameterized_prepare_mutation.rs"]
pub mod k4_r3_layer;

verus! {

use k4_r3_layer::*;
use k4_r3_layer::k4_r2_layer::*;
use k4_r3_layer::k4_r2_layer::k4_r1_layer::*;
use k4_r3_layer::k4_r2_layer::k4_r1_layer::k4_r0_layer::*;
use k4_r3_layer::k4_r2_layer::k4_r1_layer::k4_r0_layer::k4_layer::*;
use k4_r3_layer::k4_r2_layer::k4_r1_layer::k4_r0_layer::k4_layer::k3_layer::KRetryClass;
use k4_r3_layer::k4_r2_layer::k4_r1_layer::k4_r0_layer::k4_layer::k3_layer::k2_record_layer::{
    k_default_cap_delta_preserves_update_inv,
    k_default_request_delta_preserves_update_inv, k_initial_cap_budget,
    k_initial_satisfies_update_inv, k_phase_delta,
    k_phase_record_delta_refines_apply_record, k_phase_record_shape,
    k_push_default_capability, k_push_default_request, k_set_request_phase,
    k_update_inv,
};
use k4_r3_layer::k4_r2_layer::k4_r1_layer::k4_r0_layer::k4_layer::k3_layer::k2_record_layer::k2_guard_layer::{
    k_key_view, k_phase_view_reflects, k_retry_class_view,
};
use k4_r3_layer::k4_r2_layer::k4_r1_layer::k4_r0_layer::k4_layer::k3_layer::k2_record_layer::k2_guard_layer::k1_layer::{
    k_capability_id, k_digest_id, k_durable_inv, k_find_request, k_initial,
    k_phase_view, k_request_entry_couples, k_request_id,
    k_tracks_capability, k_tracks_request, KDurable, KPhase,
};
use k4_r3_layer::k4_r2_layer::k4_r1_layer::k4_r0_layer::k4_layer::k3_layer::k2_record_layer::k2_guard_layer::k1_layer::query_layer;
use query_layer::c1_layer::replay_layer;

// K4-R4 fills the Arm gap between the parameterized Prepare and Start layers.
// Start's attempt-log mutation remains the next checkpoint.

pub fn k_manifest_arm_enabled(
    config: &KManifestConfig,
    kd: &KDurable,
    request: u64,
    digest: u64,
    key_present: bool,
    key: u64,
    Ghost(durable): Ghost<replay_layer::DurableBroker>,
) -> (decision: bool)
    requires
        k_manifest_wf(*config),
        k_durable_inv(
            *kd,
            k_manifest_config_view(*config),
            durable,
        ),
    ensures
        decision == query_layer::abstract_record_enabled(
            k_manifest_config_view(*config),
            durable,
            replay_layer::JournalRecord::Arm {
                request: k_request_id(request),
                digest: k_digest_id(digest),
                key: k_key_view(key_present, key),
                prepare_ref: 0,
            },
        ),
{
    let fields_match = k_manifest_fields_match(
        config, request, digest, key_present, key,
    );
    match k_find_request(kd, request) {
        Option::Some(index) => {
            let entry = &kd.requests[index];
            let phase_prepared = match entry.phase {
                KPhase::Prepared => true,
                _ => false,
            };
            proof {
                let spec_request = k_request_id(request);
                assert(k_request_entry_couples(
                    kd.requests@[index as int], durable,
                ));
                assert(k_phase_view(entry.phase) == durable.phase[spec_request]);
                k_phase_view_reflects(entry.phase, durable.phase[spec_request]);
                assert(phase_prepared == (
                    durable.phase[spec_request] == replay_layer::Phase::Prepared
                ));
            }
            phase_prepared && fields_match
        },
        Option::None => {
            proof {
                let spec_request = k_request_id(request);
                assert(!k_tracks_request(*kd, request as nat));
                assert(durable.phase[spec_request] == replay_layer::Phase::New);
            }
            false
        },
    }
}

pub fn k_manifest_apply_arm(
    config: &KManifestConfig,
    kd: &mut KDurable,
    request_index: usize,
    request: u64,
    digest: u64,
    key_present: bool,
    key: u64,
    prepare_ref: u64,
    Ghost(durable): Ghost<replay_layer::DurableBroker>,
)
    requires
        k_manifest_wf(*config),
        k_update_inv(
            *old(kd),
            k_manifest_config_view(*config),
            durable,
        ),
        request_index < old(kd).requests@.len(),
        old(kd).requests@[request_index as int].request == request,
        query_layer::abstract_record_enabled(
            k_manifest_config_view(*config),
            durable,
            replay_layer::JournalRecord::Arm {
                request: k_request_id(request),
                digest: k_digest_id(digest),
                key: k_key_view(key_present, key),
                prepare_ref: prepare_ref as nat,
            },
        ),
    ensures
        k_phase_delta(
            *old(kd),
            *final(kd),
            request_index as int,
            KPhase::Armed,
        ),
        k_update_inv(
            *final(kd),
            k_manifest_config_view(*config),
            replay_layer::apply_record(
                durable,
                replay_layer::JournalRecord::Arm {
                    request: k_request_id(request),
                    digest: k_digest_id(digest),
                    key: k_key_view(key_present, key),
                    prepare_ref: prepare_ref as nat,
                },
            ),
        ),
{
    let ghost record = replay_layer::JournalRecord::Arm {
        request: k_request_id(request),
        digest: k_digest_id(digest),
        key: k_key_view(key_present, key),
        prepare_ref: prepare_ref as nat,
    };
    let ghost before = *kd;
    k_set_request_phase(kd, request_index, KPhase::Armed);
    proof {
        assert(k_phase_record_shape(
            record,
            k_request_id(request),
            k_phase_view(KPhase::Armed),
        ));
        k_phase_record_delta_refines_apply_record(
            before,
            *kd,
            k_manifest_config_view(*config),
            durable,
            request_index as int,
            KPhase::Armed,
            record,
        );
    }
}

pub fn k4_idempotent_arm_mutation_witness()
    -> (result: (bool, bool, u64))
    ensures
        result == (true, true, 3),
{
    let config = k4_idempotent_manifest();
    let mut kd = k_initial();
    let ghost cfg = k_manifest_config_view(config);
    let ghost initial = replay_layer::initial_durable(cfg);
    proof {
        k_manifest_config_is_well_formed(config);
        k_initial_satisfies_update_inv(kd, cfg);
    }

    let ghost before_request = kd;
    let request_slot = k_push_default_request(&mut kd, 1);
    proof {
        assert(before_request.requests@.len() == 0);
        assert(!k_tracks_request(before_request, 1nat));
        assert(cfg.max_attempts[k_request_id(1)] == 3nat);
        k_default_request_delta_preserves_update_inv(
            before_request, kd, cfg, initial, 1,
        );
    }
    let ghost before_capability = kd;
    let capability_slot = k_push_default_capability(&mut kd, 1);
    proof {
        assert(before_capability.caps@.len() == 0);
        assert(!k_tracks_capability(before_capability, 1nat));
        assert(k_initial_cap_budget(1) == 4);
        assert(cfg.initial_budget[k_capability_id(1)] == 4nat);
        k_default_cap_delta_preserves_update_inv(
            before_capability, kd, cfg, initial, 1,
        );
    }

    let authorize_decision = k_manifest_authorize_enabled(
        &config, &kd, 1, 1, 1, Ghost(initial),
    );
    proof {
        assert(authorize_decision);
    }
    k_manifest_apply_authorize(
        &config,
        &mut kd,
        request_slot,
        capability_slot,
        1,
        1,
        1,
        Ghost(initial),
    );
    let ghost authorized = replay_layer::apply_record(
        initial,
        replay_layer::JournalRecord::Authorize {
            request: k_request_id(1),
            capability: k_capability_id(1),
            digest: k_digest_id(1),
        },
    );

    let prepare_decision = k_manifest_prepare_enabled(
        &config,
        &kd,
        1,
        KRetryClass::Idempotent,
        1,
        false,
        0,
        Ghost(authorized),
    );
    proof {
        assert(prepare_decision);
    }
    k_manifest_apply_prepare(
        &config,
        &mut kd,
        request_slot,
        1,
        KRetryClass::Idempotent,
        1,
        false,
        0,
        0,
        Ghost(authorized),
    );
    let ghost prepared = replay_layer::apply_record(
        authorized,
        replay_layer::JournalRecord::Prepare {
            request: k_request_id(1),
            class: k_retry_class_view(KRetryClass::Idempotent),
            digest: k_digest_id(1),
            key: k_key_view(false, 0),
            auth_ref: 0,
        },
    );

    let arm_decision = k_manifest_arm_enabled(
        &config,
        &kd,
        1,
        1,
        false,
        0,
        Ghost(prepared),
    );
    proof {
        assert(arm_decision);
    }
    k_manifest_apply_arm(
        &config,
        &mut kd,
        request_slot,
        1,
        1,
        false,
        0,
        0,
        Ghost(prepared),
    );

    let armed = match kd.requests[request_slot].phase {
        KPhase::Armed => true,
        _ => false,
    };
    let witness_matches = match kd.requests[request_slot].witness {
        Option::Some(capability) => capability == 1,
        Option::None => false,
    };
    (armed, witness_matches, kd.caps[capability_slot].remaining)
}

} // verus!
