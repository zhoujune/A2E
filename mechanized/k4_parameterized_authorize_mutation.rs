use vstd::prelude::*;

#[path = "k4_parameterized_prepare_start.rs"]
pub mod k4_r1_layer;

verus! {

use k4_r1_layer::*;
use k4_r1_layer::k4_r0_layer::*;
use k4_r1_layer::k4_r0_layer::k4_layer::*;
use k4_r1_layer::k4_r0_layer::k4_layer::k3_layer::k2_record_layer::{
    k_authorize_delta, k_authorize_delta_refines_apply_record,
    k_default_cap_delta_preserves_update_inv,
    k_default_request_delta_preserves_update_inv, k_initial_cap_budget,
    k_initial_satisfies_update_inv, k_push_default_capability,
    k_push_default_request, k_set_authorized, k_update_inv,
};
use k4_r1_layer::k4_r0_layer::k4_layer::k3_layer::k2_record_layer::k2_guard_layer::k1_layer::{
    k_capability_id, k_digest_id, k_initial, k_request_id, KDurable, KPhase,
};
use k4_r1_layer::k4_r0_layer::k4_layer::k3_layer::k2_record_layer::k2_guard_layer::k1_layer::query_layer;
use query_layer::c1_layer::replay_layer;

// K4-R2 parameterizes the accepted Authorize durable mutation. Request and
// capability materialization plus K3 append control remain separate later
// checkpoints.

pub fn k_manifest_apply_authorize(
    config: &KManifestConfig,
    kd: &mut KDurable,
    request_index: usize,
    cap_index: usize,
    request: u64,
    capability: u64,
    digest: u64,
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
        cap_index < old(kd).caps@.len(),
        old(kd).requests@[request_index as int].request == request,
        old(kd).caps@[cap_index as int].capability == capability,
        query_layer::abstract_record_enabled(
            k_manifest_config_view(*config),
            durable,
            replay_layer::JournalRecord::Authorize {
                request: k_request_id(request),
                capability: k_capability_id(capability),
                digest: k_digest_id(digest),
            },
        ),
    ensures
        k_authorize_delta(
            *old(kd),
            *final(kd),
            request_index as int,
            cap_index as int,
            capability,
        ),
        k_update_inv(
            *final(kd),
            k_manifest_config_view(*config),
            replay_layer::apply_record(
                durable,
                replay_layer::JournalRecord::Authorize {
                    request: k_request_id(request),
                    capability: k_capability_id(capability),
                    digest: k_digest_id(digest),
                },
            ),
        ),
{
    proof {
        let entry = old(kd).caps@[cap_index as int];
        assert(durable.remaining[k_capability_id(entry.capability)]
            == entry.remaining as nat);
        assert(durable.remaining[k_capability_id(capability)] > 0);
        assert(entry.remaining > 0);
    }
    let ghost before = *kd;
    k_set_authorized(kd, request_index, cap_index, capability);
    proof {
        k_authorize_delta_refines_apply_record(
            before,
            *kd,
            k_manifest_config_view(*config),
            durable,
            request_index as int,
            cap_index as int,
            request,
            capability,
            digest,
        );
    }
}

pub fn k4_idempotent_authorize_mutation_witness()
    -> (result: (bool, u64, bool))
    ensures
        result == (true, 3, true),
{
    let config = k4_idempotent_manifest();
    let mut kd = k_initial();
    let ghost cfg = k_manifest_config_view(config);
    let ghost durable = replay_layer::initial_durable(cfg);
    proof {
        k_manifest_config_is_well_formed(config);
        k_initial_satisfies_update_inv(kd, cfg);
    }

    let ghost before_request = kd;
    let request_index = k_push_default_request(&mut kd, 1);
    proof {
        assert(before_request.requests@.len() == 0);
        assert(!k4_r1_layer::k4_r0_layer::k4_layer::k3_layer::k2_record_layer::k2_guard_layer::k1_layer::k_tracks_request(
            before_request, 1nat,
        ));
        assert(cfg.max_attempts[k_request_id(1)] == 3nat);
        k_default_request_delta_preserves_update_inv(
            before_request,
            kd,
            cfg,
            durable,
            1,
        );
    }

    let ghost before_capability = kd;
    let cap_index = k_push_default_capability(&mut kd, 1);
    proof {
        assert(before_capability.caps@.len() == 0);
        assert(!k4_r1_layer::k4_r0_layer::k4_layer::k3_layer::k2_record_layer::k2_guard_layer::k1_layer::k_tracks_capability(
            before_capability, 1nat,
        ));
        assert(k_initial_cap_budget(1) == 4);
        assert(cfg.initial_budget[k_capability_id(1)] == 4nat);
        k_default_cap_delta_preserves_update_inv(
            before_capability,
            kd,
            cfg,
            durable,
            1,
        );
    }

    let decision = k_manifest_authorize_enabled(
        &config,
        &kd,
        1,
        1,
        1,
        Ghost(durable),
    );
    proof {
        assert(k_manifest_binding_lookup(config.bindings@, 1)
            == Option::Some(KManifestBinding {
                request: 1,
                capability: 1,
                class: k4_r1_layer::k4_r0_layer::k4_layer::k3_layer::KRetryClass::Idempotent,
                digest: 1,
                key_present: false,
                key: 0,
            }));
        assert(cfg.request_capability[k_request_id(1)] == k_capability_id(1));
        assert(cfg.request_digest[k_request_id(1)] == k_digest_id(1));
        assert(cfg.matches.contains((k_request_id(1), k_capability_id(1))));
        assert(durable.phase[k_request_id(1)] == replay_layer::Phase::New);
        assert(!durable.revoked.contains(k_capability_id(1)));
        assert(durable.remaining[k_capability_id(1)] == 4nat);
        assert(query_layer::abstract_record_enabled(
            cfg,
            durable,
            replay_layer::JournalRecord::Authorize {
                request: k_request_id(1),
                capability: k_capability_id(1),
                digest: k_digest_id(1),
            },
        ));
        assert(decision);
    }

    k_manifest_apply_authorize(
        &config,
        &mut kd,
        request_index,
        cap_index,
        1,
        1,
        1,
        Ghost(durable),
    );

    let authorized = match kd.requests[request_index].phase {
        KPhase::Authorized => true,
        _ => false,
    };
    let witness_matches = match kd.requests[request_index].witness {
        Option::Some(capability) => capability == 1,
        Option::None => false,
    };
    (authorized, kd.caps[cap_index].remaining, witness_matches)
}

} // verus!
