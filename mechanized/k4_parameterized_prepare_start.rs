use vstd::prelude::*;

#[path = "k4_parameterized_authorize.rs"]
pub mod k4_r0_layer;

verus! {

use k4_r0_layer::*;
use k4_r0_layer::k4_layer::*;
use k4_r0_layer::k4_layer::k3_layer::{
    k_retry_class_equal, KRetryClass,
};
use k4_r0_layer::k4_layer::k3_layer::k2_record_layer::k2_guard_layer::{
    k_key_view, k_retry_class_view, k_phase_view_reflects,
};
use k4_r0_layer::k4_layer::k3_layer::k2_record_layer::k2_guard_layer::k1_layer::{
    k_durable_inv, k_failure_conclusive, k_find_request, k_phase_view,
    k_request_entry_couples, k_request_id, k_capability_id,
    k_digest_id, KDurable, KPhase,
};
use k4_r0_layer::k4_layer::k3_layer::k2_record_layer::k2_guard_layer::k1_layer::query_layer;
use query_layer::c1_layer::replay_layer;

// K4-R1 parameterizes the immutable request-field, retry-class, capability,
// and attempt-profile decisions used by Prepare and Start. Durable mutation
// and append control remain separate later checkpoints.

pub proof fn k_retry_class_view_injective(
    left: KRetryClass,
    right: KRetryClass,
)
    ensures
        (left == right)
            == (k_retry_class_view(left) == k_retry_class_view(right)),
{
    match left {
        KRetryClass::ReadOnly => match right {
            KRetryClass::ReadOnly => {},
            KRetryClass::Idempotent => {},
            KRetryClass::Deduplicated => {},
            KRetryClass::Uncontrolled => {},
        },
        KRetryClass::Idempotent => match right {
            KRetryClass::ReadOnly => {},
            KRetryClass::Idempotent => {},
            KRetryClass::Deduplicated => {},
            KRetryClass::Uncontrolled => {},
        },
        KRetryClass::Deduplicated => match right {
            KRetryClass::ReadOnly => {},
            KRetryClass::Idempotent => {},
            KRetryClass::Deduplicated => {},
            KRetryClass::Uncontrolled => {},
        },
        KRetryClass::Uncontrolled => match right {
            KRetryClass::ReadOnly => {},
            KRetryClass::Idempotent => {},
            KRetryClass::Deduplicated => {},
            KRetryClass::Uncontrolled => {},
        },
    }
}

pub fn k_manifest_fields_match(
    config: &KManifestConfig,
    request: u64,
    digest: u64,
    key_present: bool,
    key: u64,
) -> (matches: bool)
    requires
        k_manifest_wf(*config),
    ensures
        matches == replay_layer::request_fields_match(
            k_manifest_config_view(*config),
            k_request_id(request),
            k_digest_id(digest),
            k_key_view(key_present, key),
        ),
{
    let found = k_manifest_find_binding(config, request);
    let matches = match found {
        Option::Some(index) => {
            let entry = config.bindings[index];
            let key_matches = if entry.key_present {
                key_present && entry.key == key
            } else {
                !key_present
            };
            entry.digest == digest && key_matches
        },
        Option::None => digest == 0 && !key_present,
    };
    proof {
        let cfg = k_manifest_config_view(*config);
        let spec_request = k_request_id(request);
        assert(k_manifest_binding_ids_unique(config.bindings@));
        match found {
            Option::Some(index) => {
                let entry = config.bindings@[index as int];
                k_manifest_binding_lookup_hit(
                    config.bindings@,
                    request as nat,
                    index as int,
                );
                assert(k_manifest_binding_lookup(
                    config.bindings@,
                    request as nat,
                ) == Option::Some(entry));
                assert(cfg.request_digest[spec_request]
                    == k_digest_id(entry.digest));
                assert(cfg.request_key[spec_request]
                    == k_key_view(entry.key_present, entry.key));
                if entry.key_present {
                    assert((key_present && entry.key == key) == (
                        k_key_view(key_present, key)
                            == k_key_view(entry.key_present, entry.key)
                    ));
                } else {
                    assert((!key_present) == (
                        k_key_view(key_present, key)
                            == k_key_view(entry.key_present, entry.key)
                    ));
                }
            },
            Option::None => {
                assert forall|index: int|
                    0 <= index < config.bindings@.len() implies
                        #[trigger] config.bindings@[index].request != request by {
                    assert(config.bindings@[index].request != request);
                }
                k_manifest_binding_lookup_none(
                    config.bindings@,
                    request as nat,
                );
                assert(cfg.request_digest[spec_request] == k_digest_id(0));
                assert(cfg.request_key[spec_request]
                    == Option::<replay_layer::StableKey>::None);
                assert((digest == 0) == (
                    k_digest_id(digest) == k_digest_id(0)
                ));
                assert((!key_present) == (
                    k_key_view(key_present, key)
                        == Option::<replay_layer::StableKey>::None
                ));
            },
        }
    }
    matches
}

pub fn k_manifest_class_matches(
    config: &KManifestConfig,
    request: u64,
    class: KRetryClass,
) -> (matches: bool)
    requires
        k_manifest_wf(*config),
    ensures
        matches == (
            k_retry_class_view(class)
                == k_manifest_config_view(*config).request_class[
                    k_request_id(request)
                ]
        ),
{
    let found = k_manifest_find_binding(config, request);
    match found {
        Option::Some(index) => {
            let expected = config.bindings[index].class;
            let matches = k_retry_class_equal(class, expected);
            proof {
                let cfg = k_manifest_config_view(*config);
                let spec_request = k_request_id(request);
                let entry = config.bindings@[index as int];
                assert(k_manifest_binding_ids_unique(config.bindings@));
                k_manifest_binding_lookup_hit(
                    config.bindings@,
                    request as nat,
                    index as int,
                );
                assert(k_manifest_binding_lookup(
                    config.bindings@,
                    request as nat,
                ) == Option::Some(entry));
                assert(cfg.request_class[spec_request]
                    == k_retry_class_view(entry.class));
                k_retry_class_view_injective(class, entry.class);
                assert(expected == entry.class);
                assert((class == expected) == (
                    k_retry_class_view(class)
                        == k_retry_class_view(entry.class)
                ));
                assert(matches == (
                    k_retry_class_view(class)
                        == cfg.request_class[spec_request]
                ));
            }
            matches
        },
        Option::None => {
            let matches = k_retry_class_equal(class, KRetryClass::ReadOnly);
            proof {
                let cfg = k_manifest_config_view(*config);
                let spec_request = k_request_id(request);
                assert forall|index: int|
                    0 <= index < config.bindings@.len() implies
                        #[trigger] config.bindings@[index].request != request by {
                    assert(config.bindings@[index].request != request);
                }
                k_manifest_binding_lookup_none(
                    config.bindings@,
                    request as nat,
                );
                assert(cfg.request_class[spec_request]
                    == replay_layer::RetryClass::ReadOnly);
                k_retry_class_view_injective(class, KRetryClass::ReadOnly);
                assert((class == KRetryClass::ReadOnly) == (
                    k_retry_class_view(class)
                        == replay_layer::RetryClass::ReadOnly
                ));
                assert(matches == (
                    k_retry_class_view(class)
                        == cfg.request_class[spec_request]
                ));
            }
            matches
        },
    }
}

pub fn k_manifest_expected_capability(
    config: &KManifestConfig,
    request: u64,
) -> (capability: u64)
    requires
        k_manifest_wf(*config),
    ensures
        k_capability_id(capability)
            == k_manifest_config_view(*config).request_capability[
                k_request_id(request)
            ],
{
    let found = k_manifest_find_binding(config, request);
    let capability = match found {
        Option::Some(index) => config.bindings[index].capability,
        Option::None => 0,
    };
    proof {
        let cfg = k_manifest_config_view(*config);
        let spec_request = k_request_id(request);
        assert(k_manifest_binding_ids_unique(config.bindings@));
        match found {
            Option::Some(index) => {
                let entry = config.bindings@[index as int];
                k_manifest_binding_lookup_hit(
                    config.bindings@,
                    request as nat,
                    index as int,
                );
                assert(k_manifest_binding_lookup(
                    config.bindings@,
                    request as nat,
                ) == Option::Some(entry));
                assert(cfg.request_capability[spec_request]
                    == k_capability_id(entry.capability));
            },
            Option::None => {
                assert forall|index: int|
                    0 <= index < config.bindings@.len() implies
                        #[trigger] config.bindings@[index].request != request by {
                    assert(config.bindings@[index].request != request);
                }
                k_manifest_binding_lookup_none(
                    config.bindings@,
                    request as nat,
                );
                assert(cfg.request_capability[spec_request]
                    == k_capability_id(0));
            },
        }
    }
    capability
}

pub fn k_manifest_attempt_profile(
    config: &KManifestConfig,
    request: u64,
) -> (profile: (bool, bool, u64))
    requires
        k_manifest_wf(*config),
    ensures
        profile.0 == (
            k_manifest_config_view(*config).request_class[k_request_id(request)]
                == replay_layer::RetryClass::Idempotent
        ),
        profile.1 == (
            k_manifest_config_view(*config).request_class[k_request_id(request)]
                == replay_layer::RetryClass::Uncontrolled
        ),
        profile.2 as nat
            == k_manifest_config_view(*config).max_attempts[k_request_id(request)],
        profile.2 == 1 || profile.2 == 3,
{
    let found = k_manifest_find_binding(config, request);
    let profile = match found {
        Option::Some(index) => match config.bindings[index].class {
            KRetryClass::ReadOnly => (false, false, 1),
            KRetryClass::Idempotent => (true, false, 3),
            KRetryClass::Deduplicated => (false, false, 3),
            KRetryClass::Uncontrolled => (false, true, 1),
        },
        Option::None => (false, false, 1),
    };
    proof {
        let cfg = k_manifest_config_view(*config);
        let spec_request = k_request_id(request);
        assert(k_manifest_binding_ids_unique(config.bindings@));
        match found {
            Option::Some(index) => {
                let entry = config.bindings@[index as int];
                k_manifest_binding_lookup_hit(
                    config.bindings@,
                    request as nat,
                    index as int,
                );
                assert(k_manifest_binding_lookup(
                    config.bindings@,
                    request as nat,
                ) == Option::Some(entry));
                assert(cfg.request_class[spec_request]
                    == k_retry_class_view(entry.class));
                assert(cfg.max_attempts[spec_request]
                    == k_manifest_max_attempts(entry.class));
                match entry.class {
                    KRetryClass::ReadOnly => {},
                    KRetryClass::Idempotent => {},
                    KRetryClass::Deduplicated => {},
                    KRetryClass::Uncontrolled => {},
                }
            },
            Option::None => {
                assert forall|index: int|
                    0 <= index < config.bindings@.len() implies
                        #[trigger] config.bindings@[index].request != request by {
                    assert(config.bindings@[index].request != request);
                }
                k_manifest_binding_lookup_none(
                    config.bindings@,
                    request as nat,
                );
                assert(cfg.request_class[spec_request]
                    == replay_layer::RetryClass::ReadOnly);
                assert(cfg.max_attempts[spec_request] == 1nat);
            },
        }
    }
    profile
}

pub fn k_manifest_prepare_enabled(
    config: &KManifestConfig,
    kd: &KDurable,
    request: u64,
    class: KRetryClass,
    digest: u64,
    key_present: bool,
    key: u64,
    Ghost(durable): Ghost<replay_layer::DurableBroker>,
) -> (decision: bool)
    requires
        k_manifest_wf(*config),
        k_durable_inv(*kd, k_manifest_config_view(*config), durable),
    ensures
        decision == query_layer::abstract_record_enabled(
            k_manifest_config_view(*config),
            durable,
            replay_layer::JournalRecord::Prepare {
                request: k_request_id(request),
                class: k_retry_class_view(class),
                digest: k_digest_id(digest),
                key: k_key_view(key_present, key),
                auth_ref: 0,
            },
        ),
{
    let class_matches = k_manifest_class_matches(config, request, class);
    let fields_match = k_manifest_fields_match(
        config, request, digest, key_present, key,
    );
    let expected_capability = k_manifest_expected_capability(config, request);
    match k_find_request(kd, request) {
        Option::Some(index) => {
            let entry = &kd.requests[index];
            let phase_authorized = match entry.phase {
                KPhase::Authorized => true,
                _ => false,
            };
            let witness_matches = match entry.witness {
                Option::Some(capability) => capability == expected_capability,
                Option::None => false,
            };
            proof {
                let cfg = k_manifest_config_view(*config);
                let spec_request = k_request_id(request);
                assert(k_request_entry_couples(
                    kd.requests@[index as int], durable,
                ));
                assert(k_phase_view(entry.phase) == durable.phase[spec_request]);
                k_phase_view_reflects(entry.phase, durable.phase[spec_request]);
                assert(phase_authorized == (
                    durable.phase[spec_request] == replay_layer::Phase::Authorized
                ));
                assert(k_capability_id(expected_capability)
                    == cfg.request_capability[spec_request]);
                assert(witness_matches == (
                    durable.witness[spec_request]
                        == Option::Some(cfg.request_capability[spec_request])
                ));
            }
            phase_authorized && class_matches && fields_match && witness_matches
        },
        Option::None => {
            proof {
                let spec_request = k_request_id(request);
                assert(!k4_r0_layer::k4_layer::k3_layer::k2_record_layer::k2_guard_layer::k1_layer::k_tracks_request(
                    *kd, request as nat,
                ));
                assert(durable.phase[spec_request] == replay_layer::Phase::New);
            }
            false
        },
    }
}

pub fn k_manifest_start_enabled(
    config: &KManifestConfig,
    kd: &KDurable,
    request: u64,
    attempt: u64,
    digest: u64,
    key_present: bool,
    key: u64,
    Ghost(durable): Ghost<replay_layer::DurableBroker>,
) -> (decision: bool)
    requires
        k_manifest_wf(*config),
        k_durable_inv(*kd, k_manifest_config_view(*config), durable),
        attempt < 0xffff_ffff_ffff_ffff,
    ensures
        decision == query_layer::abstract_record_enabled(
            k_manifest_config_view(*config),
            durable,
            replay_layer::JournalRecord::Start {
                request: k_request_id(request),
                attempt: attempt as nat,
                digest: k_digest_id(digest),
                key: k_key_view(key_present, key),
                arm_ref: 0,
            },
        ),
{
    let ghost cfg = k_manifest_config_view(*config);
    let ghost spec_request = k_request_id(request);
    let fields_match = k_manifest_fields_match(
        config, request, digest, key_present, key,
    );
    let profile = k_manifest_attempt_profile(config, request);
    let class_is_idempotent = profile.0;
    let class_is_uncontrolled = profile.1;
    let max_attempts = profile.2;

    match k_find_request(kd, request) {
        Option::Some(index) => {
            let entry = &kd.requests[index];
            let phase_armed = match entry.phase {
                KPhase::Armed => true,
                _ => false,
            };
            let started = entry.outcomes.len();
            let attempt_is_next: bool = if started == 0 {
                attempt == 1
            } else if started == 1 {
                attempt == 2
            } else if started == 2 {
                attempt == 3
            } else {
                false
            };
            let within_limit = attempt <= max_attempts;
            proof {
                assert(k_request_entry_couples(
                    kd.requests@[index as int], durable,
                ));
                assert(entry.outcomes@.len() <= cfg.max_attempts[spec_request]);
                assert(max_attempts as nat == cfg.max_attempts[spec_request]);
                assert(max_attempts == 1 || max_attempts == 3);
                assert(entry.outcomes@.len() <= 3);
                assert(query_layer::d_started(durable, spec_request)
                    == entry.outcomes@.len());
                assert((attempt_is_next && within_limit) == (
                    attempt as nat
                        == query_layer::d_started(durable, spec_request) + 1
                    && attempt as nat <= cfg.max_attempts[spec_request]
                ));
            }
            let not_conclusive = !k_failure_conclusive(
                entry,
                class_is_idempotent,
                Ghost(cfg),
                Ghost(durable),
            );
            let uncontrolled_fresh =
                !class_is_uncontrolled || started == 0;
            proof {
                assert(k_phase_view(entry.phase) == durable.phase[spec_request]);
                k_phase_view_reflects(entry.phase, durable.phase[spec_request]);
                assert(phase_armed == (
                    durable.phase[spec_request] == replay_layer::Phase::Armed
                ));
                assert(uncontrolled_fresh == (
                    cfg.request_class[spec_request]
                        == replay_layer::RetryClass::Uncontrolled
                    ==> query_layer::d_started(durable, spec_request) == 0
                ));
            }
            phase_armed && fields_match && attempt_is_next && within_limit
                && not_conclusive && uncontrolled_fresh
        },
        Option::None => {
            proof {
                assert(!k4_r0_layer::k4_layer::k3_layer::k2_record_layer::k2_guard_layer::k1_layer::k_tracks_request(
                    *kd, request as nat,
                ));
                assert(durable.phase[spec_request] == replay_layer::Phase::New);
            }
            false
        },
    }
}

pub fn k4_idempotent_prepare_start_profile_witness()
    -> (result: (bool, bool, (bool, bool, u64)))
    ensures
        result.0,
        result.1,
        result.2 == (true, false, 3),
{
    let config = k4_idempotent_manifest();
    let fields = k_manifest_fields_match(&config, 1, 1, false, 0);
    let class = k_manifest_class_matches(
        &config, 1, KRetryClass::Idempotent,
    );
    let profile = k_manifest_attempt_profile(&config, 1);
    (fields, class, profile)
}

} // verus!
