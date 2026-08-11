use vstd::prelude::*;

#[path = "k4_parameterized_arm.rs"]
pub mod k4_r4_layer;

verus! {

use k4_r4_layer::*;
use k4_r4_layer::k4_r3_layer::*;
use k4_r4_layer::k4_r3_layer::k4_r2_layer::*;
use k4_r4_layer::k4_r3_layer::k4_r2_layer::k4_r1_layer::*;
use k4_r4_layer::k4_r3_layer::k4_r2_layer::k4_r1_layer::k4_r0_layer::*;
use k4_r4_layer::k4_r3_layer::k4_r2_layer::k4_r1_layer::k4_r0_layer::k4_layer::*;
use k4_r4_layer::k4_r3_layer::k4_r2_layer::k4_r1_layer::k4_r0_layer::k4_layer::k3_layer::KRetryClass;
use k4_r4_layer::k4_r3_layer::k4_r2_layer::k4_r1_layer::k4_r0_layer::k4_layer::k3_layer::k2_record_layer::{
    k_default_cap_delta_preserves_update_inv,
    k_default_request_delta_preserves_update_inv, k_initial_cap_budget,
    k_initial_satisfies_update_inv, k_push_default_capability,
    k_push_default_request, k_push_started, k_start_delta,
    k_start_delta_refines_apply_record, k_start_record_for, k_update_inv,
};
use k4_r4_layer::k4_r3_layer::k4_r2_layer::k4_r1_layer::k4_r0_layer::k4_layer::k3_layer::k2_record_layer::k2_guard_layer::{
    k_key_view, k_retry_class_view,
};
use k4_r4_layer::k4_r3_layer::k4_r2_layer::k4_r1_layer::k4_r0_layer::k4_layer::k3_layer::k2_record_layer::k2_guard_layer::k1_layer::{
    k_capability_id, k_digest_id, k_initial, k_phase_view, k_request_id,
    k_tracks_capability, k_tracks_request, KDurable, KPhase,
};
use k4_r4_layer::k4_r3_layer::k4_r2_layer::k4_r1_layer::k4_r0_layer::k4_layer::k3_layer::k2_record_layer::k2_guard_layer::k1_layer::query_layer;
use query_layer::c1_layer::replay_layer;

// K4-R5 parameterizes the accepted Start attempt-log mutation. Exact LSN
// ancestry and K3 append-state threading remain later checkpoints.

pub fn k_manifest_apply_start(
    config: &KManifestConfig,
    kd: &mut KDurable,
    request_index: usize,
    request: u64,
    attempt: u64,
    digest: u64,
    key_present: bool,
    key: u64,
    arm_ref: u64,
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
            replay_layer::JournalRecord::Start {
                request: k_request_id(request),
                attempt: attempt as nat,
                digest: k_digest_id(digest),
                key: k_key_view(key_present, key),
                arm_ref: arm_ref as nat,
            },
        ),
    ensures
        k_start_delta(
            *old(kd),
            *final(kd),
            request_index as int,
        ),
        k_update_inv(
            *final(kd),
            k_manifest_config_view(*config),
            replay_layer::apply_record(
                durable,
                replay_layer::JournalRecord::Start {
                    request: k_request_id(request),
                    attempt: attempt as nat,
                    digest: k_digest_id(digest),
                    key: k_key_view(key_present, key),
                    arm_ref: arm_ref as nat,
                },
            ),
        ),
{
    let ghost record = replay_layer::JournalRecord::Start {
        request: k_request_id(request),
        attempt: attempt as nat,
        digest: k_digest_id(digest),
        key: k_key_view(key_present, key),
        arm_ref: arm_ref as nat,
    };
    let ghost before = *kd;
    k_push_started(kd, request_index);
    proof {
        assert(k_start_record_for(record, k_request_id(request)));
        k_start_delta_refines_apply_record(
            before,
            *kd,
            k_manifest_config_view(*config),
            durable,
            request_index as int,
            record,
        );
    }
}

pub fn k4_idempotent_start_mutation_witness()
    -> (result: (bool, bool, usize, u64))
    ensures
        result == (true, true, 1usize, 3),
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
    let ghost armed = replay_layer::apply_record(
        prepared,
        replay_layer::JournalRecord::Arm {
            request: k_request_id(1),
            digest: k_digest_id(1),
            key: k_key_view(false, 0),
            prepare_ref: 0,
        },
    );

    let start_decision = k_manifest_start_enabled(
        &config,
        &kd,
        1,
        1,
        1,
        false,
        0,
        Ghost(armed),
    );
    proof {
        assert(start_decision);
    }
    k_manifest_apply_start(
        &config,
        &mut kd,
        request_slot,
        1,
        1,
        1,
        false,
        0,
        0,
        Ghost(armed),
    );

    let phase_armed = match kd.requests[request_slot].phase {
        KPhase::Armed => true,
        _ => false,
    };
    let pending = match kd.requests[request_slot].outcomes[0] {
        Option::None => true,
        Option::Some(_) => false,
    };
    (
        phase_armed,
        pending,
        kd.requests[request_slot].outcomes.len(),
        kd.caps[capability_slot].remaining,
    )
}

} // verus!
