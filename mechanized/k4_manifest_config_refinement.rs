use vstd::prelude::*;

#[path = "k3_append_linearization_kernel.rs"]
pub mod k3_layer;

verus! {

use k3_layer::*;
use k3_layer::k2_record_layer::k2_guard_layer::{
    k_key_view, k_retry_class_view,
};
use k3_layer::k2_record_layer::k2_guard_layer::k1_layer::{
    k_capability_id, k_digest_id,
};
use k3_layer::k2_record_layer::k2_guard_layer::k1_layer::query_layer::c1_layer::replay_layer;

broadcast use {
    vstd::imap::group_imap_lemmas,
    vstd::iset::group_iset_lemmas,
};

// K4-C0 gives the finite, executable M4 admission manifest a total formal
// Config view. Record admission remains in K3; later K4 targets thread this
// manifest through the executable guards and append state.

#[derive(PartialEq, Eq, Clone, Copy)]
pub struct KManifestCapability {
    pub capability: u64,
    pub initial_budget: u64,
}

#[derive(PartialEq, Eq, Clone, Copy)]
pub struct KManifestBinding {
    pub request: u64,
    pub capability: u64,
    pub class: KRetryClass,
    pub digest: u64,
    pub key_present: bool,
    pub key: u64,
}

pub struct KManifestConfig {
    pub capabilities: Vec<KManifestCapability>,
    pub bindings: Vec<KManifestBinding>,
}

pub open spec fn k_manifest_capability_lookup(
    capabilities: Seq<KManifestCapability>,
    capability: nat,
) -> Option<KManifestCapability>
    decreases capabilities.len(),
{
    if capabilities.len() == 0 {
        Option::None
    } else {
        let last = capabilities.last();
        if last.capability as nat == capability {
            Option::Some(last)
        } else {
            k_manifest_capability_lookup(capabilities.drop_last(), capability)
        }
    }
}

pub open spec fn k_manifest_binding_lookup(
    bindings: Seq<KManifestBinding>,
    request: nat,
) -> Option<KManifestBinding>
    decreases bindings.len(),
{
    if bindings.len() == 0 {
        Option::None
    } else {
        let last = bindings.last();
        if last.request as nat == request {
            Option::Some(last)
        } else {
            k_manifest_binding_lookup(bindings.drop_last(), request)
        }
    }
}

pub open spec fn k_manifest_max_attempts(class: KRetryClass) -> nat {
    match class {
        KRetryClass::ReadOnly | KRetryClass::Uncontrolled => 1nat,
        KRetryClass::Idempotent | KRetryClass::Deduplicated => 3nat,
    }
}

pub proof fn k_manifest_binding_lookup_sound(
    bindings: Seq<KManifestBinding>,
    request: nat,
)
    ensures
        match k_manifest_binding_lookup(bindings, request) {
            Option::Some(entry) => {
                &&& entry.request as nat == request
                &&& exists|index: int| 0 <= index < bindings.len()
                    && #[trigger] bindings[index] == entry
            },
            Option::None => true,
        },
    decreases bindings.len(),
{
    if bindings.len() > 0 {
        let prefix = bindings.drop_last();
        let last = bindings.last();
        if last.request as nat != request {
            k_manifest_binding_lookup_sound(prefix, request);
            match k_manifest_binding_lookup(prefix, request) {
                Option::Some(entry) => {
                    let index = choose|index: int| 0 <= index < prefix.len()
                        && prefix[index] == entry;
                    assert(prefix[index] == bindings[index]);
                },
                Option::None => {},
            }
        }
    }
}

pub open spec fn k_manifest_config_view(
    config: KManifestConfig,
) -> replay_layer::Config {
    replay_layer::Config {
        initial_budget: IMap::new(
            |_capability: replay_layer::CapabilityId| true,
            |capability: replay_layer::CapabilityId|
                match k_manifest_capability_lookup(
                    config.capabilities@, capability.id,
                ) {
                    Option::Some(entry) => entry.initial_budget as nat,
                    Option::None => 0nat,
                },
        ),
        request_capability: IMap::new(
            |_request: replay_layer::RequestId| true,
            |request: replay_layer::RequestId|
                match k_manifest_binding_lookup(config.bindings@, request.id) {
                    Option::Some(entry) => k_capability_id(entry.capability),
                    Option::None => k_capability_id(0),
                },
        ),
        request_class: IMap::new(
            |_request: replay_layer::RequestId| true,
            |request: replay_layer::RequestId|
                match k_manifest_binding_lookup(config.bindings@, request.id) {
                    Option::Some(entry) => k_retry_class_view(entry.class),
                    Option::None => replay_layer::RetryClass::ReadOnly,
                },
        ),
        request_digest: IMap::new(
            |_request: replay_layer::RequestId| true,
            |request: replay_layer::RequestId|
                match k_manifest_binding_lookup(config.bindings@, request.id) {
                    Option::Some(entry) => k_digest_id(entry.digest),
                    Option::None => k_digest_id(0),
                },
        ),
        request_key: IMap::new(
            |_request: replay_layer::RequestId| true,
            |request: replay_layer::RequestId|
                match k_manifest_binding_lookup(config.bindings@, request.id) {
                    Option::Some(entry) => k_key_view(entry.key_present, entry.key),
                    Option::None => Option::<replay_layer::StableKey>::None,
                },
        ),
        request_namespace: IMap::new(
            |_request: replay_layer::RequestId| true,
            |_request: replay_layer::RequestId|
                replay_layer::AdapterNamespace { id: 0 },
        ),
        max_attempts: IMap::new(
            |_request: replay_layer::RequestId| true,
            |request: replay_layer::RequestId|
                match k_manifest_binding_lookup(config.bindings@, request.id) {
                    Option::Some(entry) => k_manifest_max_attempts(entry.class),
                    Option::None => 1nat,
                },
        ),
        matches: ISet::new(
            |pair: (replay_layer::RequestId, replay_layer::CapabilityId)|
                match k_manifest_binding_lookup(config.bindings@, pair.0.id) {
                    Option::Some(entry) => pair.1 == k_capability_id(entry.capability),
                    Option::None => false,
                },
        ),
        valid_results: ISet::new(
            |_pair: (replay_layer::RequestId, replay_layer::Value)| true,
        ),
    }
}

pub open spec fn k_manifest_wf(config: KManifestConfig) -> bool {
    &&& forall|index: int| 0 <= index < config.capabilities@.len() ==>
        #[trigger] config.capabilities@[index].capability > 0
    &&& forall|left: int, right: int|
        0 <= left < config.capabilities@.len()
            && 0 <= right < config.capabilities@.len()
            && #[trigger] config.capabilities@[left].capability
                == #[trigger] config.capabilities@[right].capability
            ==> left == right
    &&& forall|index: int| 0 <= index < config.bindings@.len() ==> {
        let entry = #[trigger] config.bindings@[index];
        &&& entry.request > 0
        &&& (entry.class == KRetryClass::Deduplicated <==> entry.key_present)
        &&& k_manifest_capability_lookup(
            config.capabilities@, entry.capability as nat,
        ).is_some()
    }
    &&& forall|left: int, right: int|
        0 <= left < config.bindings@.len()
            && 0 <= right < config.bindings@.len()
            && #[trigger] config.bindings@[left].request
                == #[trigger] config.bindings@[right].request
            ==> left == right
    &&& forall|left: int, right: int|
        0 <= left < config.bindings@.len()
            && 0 <= right < config.bindings@.len()
            && #[trigger] config.bindings@[left].class == KRetryClass::Deduplicated
            && #[trigger] config.bindings@[right].class == KRetryClass::Deduplicated
            && config.bindings@[left].key == config.bindings@[right].key
            ==> config.bindings@[left].request == config.bindings@[right].request
}

pub proof fn k_manifest_config_is_well_formed(config: KManifestConfig)
    requires
        k_manifest_wf(config),
    ensures
        replay_layer::config_wf(k_manifest_config_view(config)),
{
    let cfg = k_manifest_config_view(config);
    assert(cfg.initial_budget.dom() == ISet::<replay_layer::CapabilityId>::full());
    assert(cfg.request_capability.dom() == ISet::<replay_layer::RequestId>::full());
    assert(cfg.request_class.dom() == ISet::<replay_layer::RequestId>::full());
    assert(cfg.request_digest.dom() == ISet::<replay_layer::RequestId>::full());
    assert(cfg.request_key.dom() == ISet::<replay_layer::RequestId>::full());
    assert(cfg.request_namespace.dom() == ISet::<replay_layer::RequestId>::full());
    assert(cfg.max_attempts.dom() == ISet::<replay_layer::RequestId>::full());

    assert forall|request: replay_layer::RequestId|
        #[trigger] cfg.max_attempts[request] > 0 by {
        k_manifest_binding_lookup_sound(config.bindings@, request.id);
        match k_manifest_binding_lookup(config.bindings@, request.id) {
            Option::Some(entry) => {},
            Option::None => {},
        }
    }

    assert forall|request: replay_layer::RequestId|
        (#[trigger] cfg.request_class[request] == replay_layer::RetryClass::Deduplicated
            <==> cfg.request_key[request].is_some()) by {
        k_manifest_binding_lookup_sound(config.bindings@, request.id);
        match k_manifest_binding_lookup(config.bindings@, request.id) {
            Option::Some(entry) => {
                let index = choose|index: int| 0 <= index < config.bindings@.len()
                    && config.bindings@[index] == entry;
                assert(entry.class == KRetryClass::Deduplicated <==> entry.key_present);
            },
            Option::None => {},
        }
    }

    assert forall|left: replay_layer::RequestId,
                  right: replay_layer::RequestId| #![auto]
        cfg.request_class[left] == replay_layer::RetryClass::Deduplicated
            && cfg.request_class[right] == replay_layer::RetryClass::Deduplicated
            && cfg.request_namespace[left] == cfg.request_namespace[right]
            && cfg.request_key[left] == cfg.request_key[right]
            ==> left == right by {
        if cfg.request_class[left] == replay_layer::RetryClass::Deduplicated
            && cfg.request_class[right] == replay_layer::RetryClass::Deduplicated
            && cfg.request_key[left] == cfg.request_key[right]
        {
            k_manifest_binding_lookup_sound(config.bindings@, left.id);
            k_manifest_binding_lookup_sound(config.bindings@, right.id);
            match k_manifest_binding_lookup(config.bindings@, left.id) {
                Option::Some(left_entry) => {
                    match k_manifest_binding_lookup(config.bindings@, right.id) {
                        Option::Some(right_entry) => {
                            let left_index = choose|index: int|
                                0 <= index < config.bindings@.len()
                                    && config.bindings@[index] == left_entry;
                            let right_index = choose|index: int|
                                0 <= index < config.bindings@.len()
                                    && config.bindings@[index] == right_entry;
                            assert(left_entry.key == right_entry.key);
                            assert(left_entry.request == right_entry.request);
                            assert(left.id == left_entry.request as nat);
                            assert(right.id == right_entry.request as nat);
                        },
                        Option::None => {},
                    }
                },
                Option::None => {},
            }
        }
    }
}

pub fn k4_idempotent_manifest() -> (config: KManifestConfig)
    ensures
        k_manifest_wf(config),
        replay_layer::config_wf(k_manifest_config_view(config)),
        k_manifest_binding_lookup(config.bindings@, 1)
            == Option::Some(KManifestBinding {
                request: 1,
                capability: 1,
                class: KRetryClass::Idempotent,
                digest: 1,
                key_present: false,
                key: 0,
            }),
{
    let mut capabilities = Vec::new();
    capabilities.push(KManifestCapability {
        capability: 1,
        initial_budget: 4,
    });
    let mut bindings = Vec::new();
    bindings.push(KManifestBinding {
        request: 1,
        capability: 1,
        class: KRetryClass::Idempotent,
        digest: 1,
        key_present: false,
        key: 0,
    });
    let config = KManifestConfig { capabilities, bindings };
    proof {
        assert(config.bindings@.len() == 1);
        assert forall|index: int| 0 <= index < config.bindings@.len() implies {
            let entry = #[trigger] config.bindings@[index];
            &&& entry.request > 0
            &&& (entry.class == KRetryClass::Deduplicated <==> entry.key_present)
            &&& k_manifest_capability_lookup(
                config.capabilities@, entry.capability as nat,
            ).is_some()
        } by {
            assert(index == 0);
        }
        assert forall|index: int| 0 <= index < config.capabilities@.len()
            implies #[trigger] config.capabilities@[index].capability > 0 by {
            assert(index == 0);
        }
        assert forall|left: int, right: int|
            0 <= left < config.capabilities@.len()
                && 0 <= right < config.capabilities@.len()
                && #[trigger] config.capabilities@[left].capability
                    == #[trigger] config.capabilities@[right].capability
            implies left == right by {
            assert(left == 0);
            assert(right == 0);
        }
        assert forall|left: int, right: int|
            0 <= left < config.bindings@.len()
                && 0 <= right < config.bindings@.len()
                && #[trigger] config.bindings@[left].request
                    == #[trigger] config.bindings@[right].request
                implies left == right by {
            assert(left == 0);
            assert(right == 0);
        }
        assert forall|left: int, right: int|
            0 <= left < config.bindings@.len()
                && 0 <= right < config.bindings@.len()
                && #[trigger] config.bindings@[left].class == KRetryClass::Deduplicated
                && #[trigger] config.bindings@[right].class == KRetryClass::Deduplicated
                && config.bindings@[left].key == config.bindings@[right].key
                implies config.bindings@[left].request
                    == config.bindings@[right].request by {
            assert(left == 0);
            assert(config.bindings@[left].class == KRetryClass::Idempotent);
        }
        k_manifest_config_is_well_formed(config);
    }
    config
}

} // verus!
