use vstd::prelude::*;

#[path = "k4_manifest_config_refinement.rs"]
pub mod k4_layer;

verus! {

use k4_layer::*;
use k4_layer::k3_layer::KRetryClass;
use k4_layer::k3_layer::k2_record_layer::k2_guard_layer::k1_layer::{
    k_durable_inv, k_find_capability, k_find_request, k_request_entry_couples,
    k_initial, k_initial_satisfies_inv, k_request_id, k_capability_id,
    k_digest_id, KDurable,
};
use k4_layer::k3_layer::k2_record_layer::k2_guard_layer::k1_layer::query_layer;
use query_layer::c1_layer::replay_layer;

// K4-R0 is the first executable guard parameterized by the finite M4
// manifest.  The existing K1-K3 guards remain fixed-demo compatibility
// targets; this target supplies the reusable executable lookup and proof
// bridge needed to replace those constants incrementally.

pub open spec fn k_manifest_binding_ids_unique(
    bindings: Seq<KManifestBinding>,
) -> bool {
    forall|left: int, right: int|
        0 <= left < bindings.len()
            && 0 <= right < bindings.len()
            && #[trigger] bindings[left].request
                == #[trigger] bindings[right].request
            ==> left == right
}

pub open spec fn k_manifest_capability_ids_unique(
    capabilities: Seq<KManifestCapability>,
) -> bool {
    forall|left: int, right: int|
        0 <= left < capabilities.len()
            && 0 <= right < capabilities.len()
            && #[trigger] capabilities[left].capability
                == #[trigger] capabilities[right].capability
            ==> left == right
}

pub fn k_manifest_find_binding(
    config: &KManifestConfig,
    request: u64,
) -> (found: Option<usize>)
    ensures
        match found {
            Option::Some(index) => {
                &&& index < config.bindings@.len()
                &&& config.bindings@[index as int].request == request
            },
            Option::None => forall|index: int|
                0 <= index < config.bindings@.len() ==>
                    #[trigger] config.bindings@[index].request != request,
        },
{
    let mut index: usize = 0;
    while index < config.bindings.len()
        invariant
            index <= config.bindings@.len(),
            forall|scanned: int| 0 <= scanned < index ==>
                #[trigger] config.bindings@[scanned].request != request,
        decreases config.bindings@.len() - index,
    {
        if config.bindings[index].request == request {
            return Option::Some(index);
        }
        index = index + 1;
    }
    Option::None
}

pub fn k_manifest_find_capability(
    config: &KManifestConfig,
    capability: u64,
) -> (found: Option<usize>)
    ensures
        match found {
            Option::Some(index) => {
                &&& index < config.capabilities@.len()
                &&& config.capabilities@[index as int].capability == capability
            },
            Option::None => forall|index: int|
                0 <= index < config.capabilities@.len() ==>
                    #[trigger] config.capabilities@[index].capability != capability,
        },
{
    let mut index: usize = 0;
    while index < config.capabilities.len()
        invariant
            index <= config.capabilities@.len(),
            forall|scanned: int| 0 <= scanned < index ==>
                #[trigger] config.capabilities@[scanned].capability != capability,
        decreases config.capabilities@.len() - index,
    {
        if config.capabilities[index].capability == capability {
            return Option::Some(index);
        }
        index = index + 1;
    }
    Option::None
}

pub proof fn k_manifest_binding_lookup_hit(
    bindings: Seq<KManifestBinding>,
    request: nat,
    index: int,
)
    requires
        0 <= index < bindings.len(),
        bindings[index].request as nat == request,
        k_manifest_binding_ids_unique(bindings),
    ensures
        k_manifest_binding_lookup(bindings, request)
            == Option::Some(bindings[index]),
    decreases bindings.len(),
{
    let prefix = bindings.drop_last();
    let last = bindings.last();
    if bindings.len() > 0 {
        if last.request as nat != request {
            assert(index < prefix.len());
            assert(k_manifest_binding_ids_unique(prefix)) by {
                assert forall|left: int, right: int|
                    0 <= left < prefix.len()
                        && 0 <= right < prefix.len()
                        && #[trigger] prefix[left].request
                            == #[trigger] prefix[right].request
                    implies left == right by {
                    assert(prefix[left] == bindings[left]);
                    assert(prefix[right] == bindings[right]);
                }
            }
            k_manifest_binding_lookup_hit(prefix, request, index);
            assert(prefix[index] == bindings[index]);
        } else {
            let last_index: int = bindings.len() as int - 1;
            assert(0 <= last_index < bindings.len());
            assert(bindings[last_index] == last);
            assert(bindings[index].request == bindings[last_index].request);
            assert(index == last_index);
        }
    }
}

pub proof fn k_manifest_capability_lookup_hit(
    capabilities: Seq<KManifestCapability>,
    capability: nat,
    index: int,
)
    requires
        0 <= index < capabilities.len(),
        capabilities[index].capability as nat == capability,
        k_manifest_capability_ids_unique(capabilities),
    ensures
        k_manifest_capability_lookup(capabilities, capability)
            == Option::Some(capabilities[index]),
    decreases capabilities.len(),
{
    let prefix = capabilities.drop_last();
    let last = capabilities.last();
    if capabilities.len() > 0 {
        if last.capability as nat != capability {
            assert(index < prefix.len());
            assert(k_manifest_capability_ids_unique(prefix)) by {
                assert forall|left: int, right: int|
                    0 <= left < prefix.len()
                        && 0 <= right < prefix.len()
                        && #[trigger] prefix[left].capability
                            == #[trigger] prefix[right].capability
                    implies left == right by {
                    assert(prefix[left] == capabilities[left]);
                    assert(prefix[right] == capabilities[right]);
                }
            }
            k_manifest_capability_lookup_hit(prefix, capability, index);
            assert(prefix[index] == capabilities[index]);
        } else {
            let last_index: int = capabilities.len() as int - 1;
            assert(0 <= last_index < capabilities.len());
            assert(capabilities[last_index] == last);
            assert(capabilities[index].capability
                == capabilities[last_index].capability);
            assert(index == last_index);
        }
    }
}

pub proof fn k_manifest_capability_lookup_sound(
    capabilities: Seq<KManifestCapability>,
    capability: nat,
)
    ensures
        match k_manifest_capability_lookup(capabilities, capability) {
            Option::Some(entry) => {
                &&& entry.capability as nat == capability
                &&& exists|index: int| 0 <= index < capabilities.len()
                    && #[trigger] capabilities[index] == entry
            },
            Option::None => true,
        },
    decreases capabilities.len(),
{
    if capabilities.len() > 0 {
        let prefix = capabilities.drop_last();
        let last = capabilities.last();
        if last.capability as nat != capability {
            k_manifest_capability_lookup_sound(prefix, capability);
            match k_manifest_capability_lookup(prefix, capability) {
                Option::Some(entry) => {
                    let index = choose|index: int| 0 <= index < prefix.len()
                        && prefix[index] == entry;
                    assert(prefix[index] == capabilities[index]);
                },
                Option::None => {},
            }
        }
    }
}

pub proof fn k_manifest_binding_lookup_none(
    bindings: Seq<KManifestBinding>,
    request: nat,
)
    requires
        forall|index: int| 0 <= index < bindings.len() ==>
            #[trigger] bindings[index].request as nat != request,
    ensures
        k_manifest_binding_lookup(bindings, request).is_none(),
{
    match k_manifest_binding_lookup(bindings, request) {
        Option::Some(entry) => {
            k_manifest_binding_lookup_sound(bindings, request);
            let index = choose|index: int|
                0 <= index < bindings.len() && bindings[index] == entry;
            assert(bindings[index].request as nat == request);
            assert(bindings[index].request as nat != request);
        },
        Option::None => {},
    }
}

pub proof fn k_manifest_capability_lookup_none(
    capabilities: Seq<KManifestCapability>,
    capability: nat,
)
    requires
        forall|index: int| 0 <= index < capabilities.len() ==>
            #[trigger] capabilities[index].capability as nat != capability,
    ensures
        k_manifest_capability_lookup(capabilities, capability).is_none(),
{
    match k_manifest_capability_lookup(capabilities, capability) {
        Option::Some(entry) => {
            k_manifest_capability_lookup_sound(capabilities, capability);
            let index = choose|index: int|
                0 <= index < capabilities.len() && capabilities[index] == entry;
            assert(capabilities[index].capability as nat == capability);
            assert(capabilities[index].capability as nat != capability);
        },
        Option::None => {},
    }
}

pub fn k_manifest_authorize_enabled(
    config: &KManifestConfig,
    kd: &KDurable,
    request: u64,
    capability: u64,
    digest: u64,
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
            replay_layer::JournalRecord::Authorize {
                request: k_request_id(request),
                capability: k_capability_id(capability),
                digest: k_digest_id(digest),
            },
        ),
{
    let ghost cfg = k_manifest_config_view(*config);
    let ghost spec_request = k_request_id(request);
    proof {
        k_manifest_config_is_well_formed(*config);
        assert(k_manifest_binding_ids_unique(config.bindings@));
        assert(k_manifest_capability_ids_unique(config.capabilities@));
    }

    let phase_new: bool = match k_find_request(kd, request) {
        Option::Some(index) => {
            let entry_phase = kd.requests[index].phase;
            proof {
                assert(k_request_entry_couples(
                    kd.requests@[index as int], durable,
                ));
            }
            match entry_phase {
                k4_layer::k3_layer::k2_record_layer::k2_guard_layer::k1_layer::KPhase::New => true,
                _ => false,
            }
        },
        Option::None => {
            proof {
                assert(!k4_layer::k3_layer::k2_record_layer::k2_guard_layer::k1_layer::k_tracks_request(
                    *kd, request as nat,
                ));
                assert(durable.phase[spec_request]
                    == replay_layer::Phase::New);
            }
            true
        },
    };

    let binding_index = k_manifest_find_binding(config, request);
    let manifest_matches: bool = match binding_index {
        Option::Some(index) => {
            let entry = config.bindings[index];
            entry.capability == capability && entry.digest == digest
        },
        Option::None => false,
    };

    let capability_index = k_manifest_find_capability(config, capability);
    let mut unrevoked: bool;
    let mut budget_positive: bool;
    match k_find_capability(kd, capability) {
        Option::Some(index) => {
            unrevoked = !kd.caps[index].revoked;
            budget_positive = kd.caps[index].remaining > 0;
            proof {
                let entry = kd.caps@[index as int];
                assert(durable.remaining[k_capability_id(entry.capability)]
                    == entry.remaining as nat);
                assert(durable.revoked.contains(
                    k_capability_id(entry.capability),
                ) == entry.revoked);
            }
        },
        Option::None => {
            unrevoked = true;
            budget_positive = match capability_index {
                Option::Some(index) => config.capabilities[index].initial_budget > 0,
                Option::None => false,
            };
            proof {
                assert(!k4_layer::k3_layer::k2_record_layer::k2_guard_layer::k1_layer::k_tracks_capability(
                    *kd, capability as nat,
                ));
                match capability_index {
                    Option::Some(index) => {
                        let entry = config.capabilities@[index as int];
                        k_manifest_capability_lookup_hit(
                            config.capabilities@,
                            capability as nat,
                            index as int,
                        );
                        assert(k_manifest_capability_lookup(
                            config.capabilities@,
                            capability as nat,
                        ) == Option::Some(entry));
                        assert(durable.remaining[k_capability_id(capability)]
                            == entry.initial_budget as nat);
                    },
                    Option::None => {
                        assert forall|index: int|
                            0 <= index < config.capabilities@.len() implies
                                #[trigger] config.capabilities@[index].capability
                                    != capability by {
                            assert(config.capabilities@[index].capability
                                != capability);
                        }
                        k_manifest_capability_lookup_none(
                            config.capabilities@,
                            capability as nat,
                        );
                        assert(k_manifest_capability_lookup(
                            config.capabilities@,
                            capability as nat,
                        ).is_none());
                        assert(durable.remaining[k_capability_id(capability)] == 0nat);
                    },
                }
            }
        },
    }

    proof {
        match binding_index {
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
                assert(cfg.request_digest[spec_request]
                    == k_digest_id(entry.digest));
                assert(cfg.matches.contains((
                    spec_request, k_capability_id(capability),
                )) == (entry.capability == capability));
                assert(manifest_matches
                    == (cfg.request_digest[spec_request]
                        == k_digest_id(digest)
                        && cfg.matches.contains((
                            spec_request, k_capability_id(capability),
                        ))));
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
                assert(k_manifest_binding_lookup(
                    config.bindings@,
                    request as nat,
                ).is_none());
                assert(cfg.matches.contains((
                    spec_request, k_capability_id(capability),
                )) == false);
                assert(manifest_matches == false);
            },
        }
        assert(phase_new == (
            durable.phase[spec_request]
                == replay_layer::Phase::New
        ));
        assert(unrevoked == !durable.revoked.contains(
            k_capability_id(capability),
        ));
        assert(budget_positive == (
            durable.remaining[k_capability_id(capability)] > 0
        ));
        assert(manifest_matches == (
            k_digest_id(digest) == cfg.request_digest[spec_request]
                && cfg.matches.contains((
                    spec_request, k_capability_id(capability),
                ))
        ));
    }

    phase_new && manifest_matches && unrevoked && budget_positive
}

pub fn k4_idempotent_authorize_witness() -> (decision: bool)
    ensures
        decision,
{
    let config = k4_idempotent_manifest();
    let kd = k_initial();
    let ghost cfg = k_manifest_config_view(config);
    let ghost durable = replay_layer::initial_durable(cfg);
    proof {
        k_initial_satisfies_inv(kd, cfg);
        assert(k_manifest_binding_lookup(config.bindings@, 1)
            == Option::Some(KManifestBinding {
                request: 1,
                capability: 1,
                class: KRetryClass::Idempotent,
                digest: 1,
                key_present: false,
                key: 0,
            }));
        assert(cfg.request_capability[k_request_id(1)] == k_capability_id(1));
        assert(cfg.request_digest[k_request_id(1)] == k_digest_id(1));
        assert(cfg.matches.contains((k_request_id(1), k_capability_id(1))));
        assert(cfg.initial_budget[k_capability_id(1)] == 4nat);
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
    }
    k_manifest_authorize_enabled(
        &config,
        &kd,
        1,
        1,
        1,
        Ghost(durable),
    )
}

} // verus!
