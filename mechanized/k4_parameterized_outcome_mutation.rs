use vstd::prelude::*;

#[path = "k4_parameterized_start_mutation.rs"]
pub mod k4_r5_layer;

verus! {

use k4_r5_layer::*;
use k4_r5_layer::k4_r4_layer::*;
use k4_r5_layer::k4_r4_layer::k4_r3_layer::*;
use k4_r5_layer::k4_r4_layer::k4_r3_layer::k4_r2_layer::*;
use k4_r5_layer::k4_r4_layer::k4_r3_layer::k4_r2_layer::k4_r1_layer::*;
use k4_r5_layer::k4_r4_layer::k4_r3_layer::k4_r2_layer::k4_r1_layer::k4_r0_layer::*;
use k4_r5_layer::k4_r4_layer::k4_r3_layer::k4_r2_layer::k4_r1_layer::k4_r0_layer::k4_layer::*;
use k4_r5_layer::k4_r4_layer::k4_r3_layer::k4_r2_layer::k4_r1_layer::k4_r0_layer::k4_layer::k3_layer::KRetryClass;
use k4_r5_layer::k4_r4_layer::k4_r3_layer::k4_r2_layer::k4_r1_layer::k4_r0_layer::k4_layer::k3_layer::k2_record_layer::{
    k_default_cap_delta_preserves_update_inv,
    k_default_request_delta_preserves_update_inv, k_initial_cap_budget,
    k_initial_satisfies_update_inv, k_outcome_delta,
    k_outcome_delta_refines_apply_record, k_outcome_record_for,
    k_push_default_capability, k_push_default_request, k_set_latest_outcome,
    k_update_inv,
};
use k4_r5_layer::k4_r4_layer::k4_r3_layer::k4_r2_layer::k4_r1_layer::k4_r0_layer::k4_layer::k3_layer::k2_record_layer::k2_guard_layer::{
    k_attempt_is_latest, k_key_view, k_latest_outcome,
    k_phase_view_reflects, k_retry_class_view,
};
use k4_r5_layer::k4_r4_layer::k4_r3_layer::k4_r2_layer::k4_r1_layer::k4_r0_layer::k4_layer::k3_layer::k2_record_layer::k2_guard_layer::k1_layer::{
    k_capability_id, k_digest_id, k_durable_inv, k_find_request, k_initial,
    k_observation_view, k_outcome_view, k_phase_view,
    k_request_entry_couples, k_request_id, k_tracks_capability,
    k_tracks_request, KDurable, KObservation, KPhase,
};
use k4_r5_layer::k4_r4_layer::k4_r3_layer::k4_r2_layer::k4_r1_layer::k4_r0_layer::k4_layer::k3_layer::k2_record_layer::k2_guard_layer::k1_layer::query_layer;
use query_layer::c1_layer::replay_layer;

// K4-R6 parameterizes the accepted Outcome guard and mutation. Exact LSN
// ancestry and K3 append-state threading remain later checkpoints.

pub fn k_manifest_outcome_enabled(
    config: &KManifestConfig,
    kd: &KDurable,
    request: u64,
    attempt: u64,
    observation: KObservation,
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
            replay_layer::JournalRecord::Outcome {
                request: k_request_id(request),
                attempt: attempt as nat,
                observation: k_observation_view(observation),
                digest: k_digest_id(digest),
                key: k_key_view(key_present, key),
                start_ref: 0,
            },
        ),
{
    let ghost cfg = k_manifest_config_view(*config);
    let ghost spec_request = k_request_id(request);
    let fields_match = k_manifest_fields_match(
        config, request, digest, key_present, key,
    );
    let profile = k_manifest_attempt_profile(config, request);
    let max_attempts = profile.2;

    match k_find_request(kd, request) {
        Option::Some(index) => {
            let entry = &kd.requests[index];
            proof {
                assert(k_request_entry_couples(
                    kd.requests@[index as int], durable,
                ));
                assert(entry.outcomes@.len()
                    <= cfg.max_attempts[spec_request]);
                assert(max_attempts as nat
                    == cfg.max_attempts[spec_request]);
                assert(max_attempts == 1 || max_attempts == 3);
                assert(entry.outcomes@.len() <= 3);
            }
            let phase_armed = match entry.phase {
                KPhase::Armed => true,
                _ => false,
            };
            let attempt_latest = k_attempt_is_latest(
                entry, attempt, Ghost(durable),
            );
            let latest_outcome = k_latest_outcome(entry);
            let outcome_missing = latest_outcome.is_none();
            proof {
                assert(k_phase_view(entry.phase)
                    == durable.phase[spec_request]);
                k_phase_view_reflects(
                    entry.phase, durable.phase[spec_request],
                );
                assert(phase_armed == (
                    durable.phase[spec_request]
                        == replay_layer::Phase::Armed
                ));
                if attempt_latest {
                    assert(attempt as nat == entry.outcomes@.len());
                    assert(entry.outcomes@.len() > 0);
                    assert(query_layer::d_outcome(
                        durable, spec_request, attempt as nat,
                    ) == k_outcome_view(latest_outcome));
                }
                assert((attempt_latest && outcome_missing) == (
                    attempt as nat > 0
                        && attempt as nat
                            == query_layer::d_started(
                                durable, spec_request,
                            )
                        && query_layer::d_outcome(
                            durable, spec_request, attempt as nat,
                        ).is_none()
                ));
                assert(cfg.valid_results.contains((
                    spec_request,
                    replay_layer::Value {
                        id: match observation {
                            KObservation::Success { value } => value as nat,
                            _ => 0nat,
                        },
                    },
                )));
                assert(replay_layer::success_is_valid(
                    cfg, spec_request, k_observation_view(observation),
                ));
            }
            phase_armed && fields_match && attempt_latest && outcome_missing
        },
        Option::None => {
            proof {
                assert(!k_tracks_request(*kd, request as nat));
                assert(durable.phase[spec_request]
                    == replay_layer::Phase::New);
            }
            false
        },
    }
}

pub fn k_manifest_apply_outcome(
    config: &KManifestConfig,
    kd: &mut KDurable,
    request_index: usize,
    request: u64,
    attempt: u64,
    observation: KObservation,
    digest: u64,
    key_present: bool,
    key: u64,
    start_ref: u64,
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
            replay_layer::JournalRecord::Outcome {
                request: k_request_id(request),
                attempt: attempt as nat,
                observation: k_observation_view(observation),
                digest: k_digest_id(digest),
                key: k_key_view(key_present, key),
                start_ref: start_ref as nat,
            },
        ),
    ensures
        k_outcome_delta(
            *old(kd),
            *final(kd),
            request_index as int,
            observation,
        ),
        k_update_inv(
            *final(kd),
            k_manifest_config_view(*config),
            replay_layer::apply_record(
                durable,
                replay_layer::JournalRecord::Outcome {
                    request: k_request_id(request),
                    attempt: attempt as nat,
                    observation: k_observation_view(observation),
                    digest: k_digest_id(digest),
                    key: k_key_view(key_present, key),
                    start_ref: start_ref as nat,
                },
            ),
        ),
{
    let ghost record = replay_layer::JournalRecord::Outcome {
        request: k_request_id(request),
        attempt: attempt as nat,
        observation: k_observation_view(observation),
        digest: k_digest_id(digest),
        key: k_key_view(key_present, key),
        start_ref: start_ref as nat,
    };
    proof {
        let entry = old(kd).requests@[request_index as int];
        assert(k_request_entry_couples(entry, durable));
        assert(query_layer::d_started(
            durable, k_request_id(request),
        ) == entry.outcomes@.len());
        assert(attempt as nat > 0);
        assert(attempt as nat == query_layer::d_started(
            durable, k_request_id(request),
        ));
        assert(entry.outcomes@.len() > 0);
    }
    let ghost before = *kd;
    k_set_latest_outcome(kd, request_index, observation);
    proof {
        assert(k_outcome_record_for(
            record, k_request_id(request), observation,
        ));
        k_outcome_delta_refines_apply_record(
            before,
            *kd,
            k_manifest_config_view(*config),
            durable,
            request_index as int,
            observation,
            record,
        );
    }
}

pub fn k4_idempotent_outcome_mutation_witness()
    -> (result: (bool, bool, u64, usize, u64))
    ensures
        result == (true, true, 1, 1usize, 3),
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
        &config, &kd, 1, 1, false, 0, Ghost(prepared),
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
        &config, &kd, 1, 1, 1, false, 0, Ghost(armed),
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
    let ghost started = replay_layer::apply_record(
        armed,
        replay_layer::JournalRecord::Start {
            request: k_request_id(1),
            attempt: 1nat,
            digest: k_digest_id(1),
            key: k_key_view(false, 0),
            arm_ref: 0,
        },
    );

    let outcome = KObservation::Success { value: 1 };
    let outcome_decision = k_manifest_outcome_enabled(
        &config,
        &kd,
        1,
        1,
        outcome,
        1,
        false,
        0,
        Ghost(started),
    );
    proof {
        assert(outcome_decision);
    }
    k_manifest_apply_outcome(
        &config,
        &mut kd,
        request_slot,
        1,
        1,
        outcome,
        1,
        false,
        0,
        0,
        Ghost(started),
    );

    let phase_armed = match kd.requests[request_slot].phase {
        KPhase::Armed => true,
        _ => false,
    };
    let recorded = match kd.requests[request_slot].outcomes[0] {
        Option::Some(KObservation::Success { .. }) => true,
        _ => false,
    };
    let value = match kd.requests[request_slot].outcomes[0] {
        Option::Some(KObservation::Success { value }) => value,
        _ => 0,
    };
    (
        phase_armed,
        recorded,
        value,
        kd.requests[request_slot].outcomes.len(),
        kd.caps[capability_slot].remaining,
    )
}

} // verus!
