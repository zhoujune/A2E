use vstd::prelude::*;

#[path = "t1_broker_records.rs"]
pub mod broker_layer;

verus! {

use broker_layer::query_layer::c1_layer::replay_layer;

// B2-C enriches the immutable configuration before physical histories are
// introduced.  It deliberately erases to the already verified replay-layer
// Config, so no replay or Broker type is duplicated.

#[derive(PartialEq, Eq)]
pub struct Principal {
    pub id: nat,
}

#[derive(PartialEq, Eq)]
pub struct Tool {
    pub id: nat,
}

#[derive(PartialEq, Eq)]
pub struct Operation {
    pub id: nat,
}

#[derive(PartialEq, Eq)]
pub struct Resource {
    pub id: nat,
}

#[derive(PartialEq, Eq)]
pub struct Arguments {
    pub id: nat,
}

pub struct Request {
    pub principal: Principal,
    pub tool: Tool,
    pub operation: Operation,
    pub resource: Resource,
    pub arguments: Arguments,
    pub capability: replay_layer::CapabilityId,
    pub retry_class: replay_layer::RetryClass,
    pub digest: replay_layer::Digest,
    pub adapter_namespace: replay_layer::AdapterNamespace,
    pub stable_key: Option<replay_layer::StableKey>,
    pub max_attempts: nat,
}

pub struct Capability {
    pub principal: Principal,
    pub tool: Tool,
    pub operation: Operation,
    pub resources: ISet<Resource>,
    pub arguments: ISet<Arguments>,
    pub initial_budget: nat,
}

pub struct FullConfig {
    pub request: IMap<replay_layer::RequestId, Request>,
    pub capability: IMap<replay_layer::CapabilityId, Capability>,
    pub valid_results: ISet<(replay_layer::RequestId, replay_layer::Value)>,
}

#[derive(PartialEq, Eq)]
pub struct CallDescriptor {
    pub principal: Principal,
    pub tool: Tool,
    pub operation: Operation,
    pub resource: Resource,
    pub arguments: Arguments,
    pub digest: replay_layer::Digest,
    pub adapter_namespace: replay_layer::AdapterNamespace,
    pub key: Option<replay_layer::StableKey>,
}

pub open spec fn matches(
    cfg: FullConfig,
    request: replay_layer::RequestId,
    capability: replay_layer::CapabilityId,
) -> bool {
    let req = cfg.request[request];
    let cap = cfg.capability[capability];
    req.capability == capability
        && req.principal == cap.principal
        && req.tool == cap.tool
        && req.operation == cap.operation
        && cap.resources.contains(req.resource)
        && cap.arguments.contains(req.arguments)
}

pub open spec fn canonical_call(
    cfg: FullConfig,
    request: replay_layer::RequestId,
) -> CallDescriptor {
    let req = cfg.request[request];
    CallDescriptor {
        principal: req.principal,
        tool: req.tool,
        operation: req.operation,
        resource: req.resource,
        arguments: req.arguments,
        digest: req.digest,
        adapter_namespace: req.adapter_namespace,
        key: req.stable_key,
    }
}

pub open spec fn positive_attempt_bounds(cfg: FullConfig) -> bool {
    forall|request: replay_layer::RequestId|
        #[trigger] cfg.request[request].max_attempts > 0
}

pub open spec fn stable_key_shape(cfg: FullConfig) -> bool {
    forall|request: replay_layer::RequestId|
        (#[trigger] cfg.request[request].retry_class
                == replay_layer::RetryClass::Deduplicated
            <==> cfg.request[request].stable_key.is_some())
}

pub open spec fn stable_key_namespace_injective(cfg: FullConfig) -> bool {
    forall|left: replay_layer::RequestId, right: replay_layer::RequestId| #![auto]
        cfg.request[left].retry_class == replay_layer::RetryClass::Deduplicated
            && cfg.request[right].retry_class == replay_layer::RetryClass::Deduplicated
            && cfg.request[left].adapter_namespace
                == cfg.request[right].adapter_namespace
            && cfg.request[left].stable_key == cfg.request[right].stable_key
                ==> left == right
}

pub open spec fn full_config_wf(cfg: FullConfig) -> bool {
    cfg.request.dom() == ISet::<replay_layer::RequestId>::full()
        && cfg.capability.dom() == ISet::<replay_layer::CapabilityId>::full()
        && positive_attempt_bounds(cfg)
        && stable_key_shape(cfg)
        && stable_key_namespace_injective(cfg)
}

pub open spec fn erase_config(cfg: FullConfig) -> replay_layer::Config {
    replay_layer::Config {
        initial_budget: IMap::new(
            |_capability: replay_layer::CapabilityId| true,
            |capability: replay_layer::CapabilityId|
                cfg.capability[capability].initial_budget,
        ),
        request_capability: IMap::new(
            |_request: replay_layer::RequestId| true,
            |request: replay_layer::RequestId| cfg.request[request].capability,
        ),
        request_class: IMap::new(
            |_request: replay_layer::RequestId| true,
            |request: replay_layer::RequestId| cfg.request[request].retry_class,
        ),
        request_digest: IMap::new(
            |_request: replay_layer::RequestId| true,
            |request: replay_layer::RequestId| cfg.request[request].digest,
        ),
        request_key: IMap::new(
            |_request: replay_layer::RequestId| true,
            |request: replay_layer::RequestId| cfg.request[request].stable_key,
        ),
        request_namespace: IMap::new(
            |_request: replay_layer::RequestId| true,
            |request: replay_layer::RequestId|
                cfg.request[request].adapter_namespace,
        ),
        max_attempts: IMap::new(
            |_request: replay_layer::RequestId| true,
            |request: replay_layer::RequestId| cfg.request[request].max_attempts,
        ),
        matches: ISet::new(
            |pair: (replay_layer::RequestId, replay_layer::CapabilityId)|
                matches(cfg, pair.0, pair.1),
        ),
        valid_results: cfg.valid_results,
    }
}

pub open spec fn erasure_agreement(cfg: FullConfig) -> bool {
    let erased = erase_config(cfg);
    (forall|request: replay_layer::RequestId| {
        &&& #[trigger] erased.request_capability[request]
            == cfg.request[request].capability
        &&& #[trigger] erased.request_class[request]
            == cfg.request[request].retry_class
        &&& #[trigger] erased.request_digest[request]
            == cfg.request[request].digest
        &&& #[trigger] erased.request_key[request]
            == cfg.request[request].stable_key
        &&& #[trigger] erased.request_namespace[request]
            == cfg.request[request].adapter_namespace
        &&& #[trigger] erased.max_attempts[request]
            == cfg.request[request].max_attempts
    })
        && (forall|capability: replay_layer::CapabilityId|
            #[trigger] erased.initial_budget[capability]
                == cfg.capability[capability].initial_budget)
        && (forall|request: replay_layer::RequestId,
                    capability: replay_layer::CapabilityId|
            #[trigger] erased.matches.contains((request, capability))
                <==> matches(cfg, request, capability))
        && erased.valid_results == cfg.valid_results
}

pub open spec fn canonical_call_agreement(cfg: FullConfig) -> bool {
    forall|request: replay_layer::RequestId| {
        &&& #[trigger] canonical_call(cfg, request).principal
            == cfg.request[request].principal
        &&& canonical_call(cfg, request).tool == cfg.request[request].tool
        &&& canonical_call(cfg, request).operation == cfg.request[request].operation
        &&& canonical_call(cfg, request).resource == cfg.request[request].resource
        &&& canonical_call(cfg, request).arguments == cfg.request[request].arguments
        &&& canonical_call(cfg, request).digest == cfg.request[request].digest
        &&& canonical_call(cfg, request).adapter_namespace
            == cfg.request[request].adapter_namespace
        &&& canonical_call(cfg, request).key == cfg.request[request].stable_key
    }
}

pub open spec fn matches_scope_agreement(cfg: FullConfig) -> bool {
    forall|request: replay_layer::RequestId,
            capability: replay_layer::CapabilityId|
        #[trigger] matches(cfg, request, capability) ==> {
            let req = cfg.request[request];
            let cap = cfg.capability[capability];
            &&& req.capability == capability
            &&& req.principal == cap.principal
            &&& req.tool == cap.tool
            &&& req.operation == cap.operation
            &&& cap.resources.contains(req.resource)
            &&& cap.arguments.contains(req.arguments)
        }
}

pub open spec fn configuration_refinement(cfg: FullConfig) -> bool {
    replay_layer::config_wf(erase_config(cfg))
        && erasure_agreement(cfg)
        && stable_key_namespace_injective(cfg)
        && canonical_call_agreement(cfg)
        && matches_scope_agreement(cfg)
}

pub proof fn erasure_is_replay_well_formed(cfg: FullConfig)
    requires full_config_wf(cfg),
    ensures replay_layer::config_wf(erase_config(cfg)),
{
    assert(cfg.request.dom() == ISet::<replay_layer::RequestId>::full());
    assert(cfg.capability.dom() == ISet::<replay_layer::CapabilityId>::full());
    assert(forall|request: replay_layer::RequestId|
        #[trigger] cfg.request[request].max_attempts > 0);
    assert(forall|request: replay_layer::RequestId|
        (#[trigger] cfg.request[request].retry_class
                == replay_layer::RetryClass::Deduplicated
            <==> cfg.request[request].stable_key.is_some()));
    assert(forall|left: replay_layer::RequestId,
            right: replay_layer::RequestId| #![auto]
        cfg.request[left].retry_class == replay_layer::RetryClass::Deduplicated
            && cfg.request[right].retry_class == replay_layer::RetryClass::Deduplicated
            && cfg.request[left].adapter_namespace
                == cfg.request[right].adapter_namespace
            && cfg.request[left].stable_key == cfg.request[right].stable_key
                ==> left == right);
    assert(erase_config(cfg).initial_budget.dom()
        == ISet::<replay_layer::CapabilityId>::full());
    assert(erase_config(cfg).request_capability.dom()
        == ISet::<replay_layer::RequestId>::full());
    assert(erase_config(cfg).request_class.dom()
        == ISet::<replay_layer::RequestId>::full());
    assert(erase_config(cfg).request_digest.dom()
        == ISet::<replay_layer::RequestId>::full());
    assert(erase_config(cfg).request_key.dom()
        == ISet::<replay_layer::RequestId>::full());
    assert(erase_config(cfg).request_namespace.dom()
        == ISet::<replay_layer::RequestId>::full());
    assert(erase_config(cfg).max_attempts.dom()
        == ISet::<replay_layer::RequestId>::full());
    assert forall|request: replay_layer::RequestId|
        #[trigger] erase_config(cfg).max_attempts[request] > 0 by {
        assert(cfg.request[request].max_attempts > 0);
    }
    assert forall|request: replay_layer::RequestId|
        (#[trigger] erase_config(cfg).request_class[request]
                == replay_layer::RetryClass::Deduplicated
            <==> erase_config(cfg).request_key[request].is_some()) by {
        assert(cfg.request[request].retry_class
                == replay_layer::RetryClass::Deduplicated
            <==> cfg.request[request].stable_key.is_some());
    }
    assert forall|left: replay_layer::RequestId,
            right: replay_layer::RequestId| #![auto]
        erase_config(cfg).request_class[left]
                == replay_layer::RetryClass::Deduplicated
            && erase_config(cfg).request_class[right]
                == replay_layer::RetryClass::Deduplicated
            && erase_config(cfg).request_namespace[left]
                == erase_config(cfg).request_namespace[right]
            && erase_config(cfg).request_key[left]
                == erase_config(cfg).request_key[right]
                implies left == right by {
        assert(cfg.request[left].retry_class
                == replay_layer::RetryClass::Deduplicated);
        assert(cfg.request[right].retry_class
                == replay_layer::RetryClass::Deduplicated);
        assert(cfg.request[left].adapter_namespace
                == cfg.request[right].adapter_namespace);
        assert(cfg.request[left].stable_key == cfg.request[right].stable_key);
    }
}

pub proof fn erasure_is_exact(cfg: FullConfig)
    ensures erasure_agreement(cfg),
{
    assert forall|request: replay_layer::RequestId| {
        &&& #[trigger] erase_config(cfg).request_capability[request]
            == cfg.request[request].capability
        &&& #[trigger] erase_config(cfg).request_class[request]
            == cfg.request[request].retry_class
        &&& #[trigger] erase_config(cfg).request_digest[request]
            == cfg.request[request].digest
        &&& #[trigger] erase_config(cfg).request_key[request]
            == cfg.request[request].stable_key
        &&& #[trigger] erase_config(cfg).request_namespace[request]
            == cfg.request[request].adapter_namespace
        &&& #[trigger] erase_config(cfg).max_attempts[request]
            == cfg.request[request].max_attempts
    } by {}
    assert forall|capability: replay_layer::CapabilityId|
        #[trigger] erase_config(cfg).initial_budget[capability]
            == cfg.capability[capability].initial_budget by {}
    assert forall|request: replay_layer::RequestId,
            capability: replay_layer::CapabilityId|
        #[trigger] erase_config(cfg).matches.contains((request, capability))
            <==> matches(cfg, request, capability) by {}
}

pub proof fn stable_key_injectivity_is_preserved(cfg: FullConfig)
    requires full_config_wf(cfg),
    ensures
        stable_key_namespace_injective(cfg),
        forall|left: replay_layer::RequestId, right: replay_layer::RequestId| #![auto]
            erase_config(cfg).request_class[left]
                    == replay_layer::RetryClass::Deduplicated
                && erase_config(cfg).request_class[right]
                    == replay_layer::RetryClass::Deduplicated
                && erase_config(cfg).request_namespace[left]
                    == erase_config(cfg).request_namespace[right]
                && erase_config(cfg).request_key[left]
                    == erase_config(cfg).request_key[right]
                    ==> left == right,
{
    assert(forall|left: replay_layer::RequestId,
            right: replay_layer::RequestId| #![auto]
        cfg.request[left].retry_class == replay_layer::RetryClass::Deduplicated
            && cfg.request[right].retry_class == replay_layer::RetryClass::Deduplicated
            && cfg.request[left].adapter_namespace
                == cfg.request[right].adapter_namespace
            && cfg.request[left].stable_key == cfg.request[right].stable_key
                ==> left == right);
    assert(stable_key_namespace_injective(cfg));
    assert forall|left: replay_layer::RequestId,
            right: replay_layer::RequestId| #![auto]
        erase_config(cfg).request_class[left]
                == replay_layer::RetryClass::Deduplicated
            && erase_config(cfg).request_class[right]
                == replay_layer::RetryClass::Deduplicated
            && erase_config(cfg).request_namespace[left]
                == erase_config(cfg).request_namespace[right]
            && erase_config(cfg).request_key[left]
                == erase_config(cfg).request_key[right]
                implies left == right by {
        assert(cfg.request[left].retry_class
                == replay_layer::RetryClass::Deduplicated);
        assert(cfg.request[right].retry_class
                == replay_layer::RetryClass::Deduplicated);
        assert(cfg.request[left].adapter_namespace
                == cfg.request[right].adapter_namespace);
        assert(cfg.request[left].stable_key == cfg.request[right].stable_key);
    }
}

pub proof fn canonical_call_is_exact(
    cfg: FullConfig,
    request: replay_layer::RequestId,
)
    ensures
        canonical_call(cfg, request).principal == cfg.request[request].principal,
        canonical_call(cfg, request).tool == cfg.request[request].tool,
        canonical_call(cfg, request).operation == cfg.request[request].operation,
        canonical_call(cfg, request).resource == cfg.request[request].resource,
        canonical_call(cfg, request).arguments == cfg.request[request].arguments,
        canonical_call(cfg, request).digest == cfg.request[request].digest,
        canonical_call(cfg, request).adapter_namespace
            == cfg.request[request].adapter_namespace,
        canonical_call(cfg, request).key == cfg.request[request].stable_key,
{
}

pub proof fn matches_implies_scope_fields(
    cfg: FullConfig,
    request: replay_layer::RequestId,
    capability: replay_layer::CapabilityId,
)
    ensures
        matches(cfg, request, capability) ==> {
            let req = cfg.request[request];
            let cap = cfg.capability[capability];
            &&& req.capability == capability
            &&& req.principal == cap.principal
            &&& req.tool == cap.tool
            &&& req.operation == cap.operation
            &&& cap.resources.contains(req.resource)
            &&& cap.arguments.contains(req.arguments)
        },
{
}

pub proof fn b2_c_configuration_refinement(cfg: FullConfig)
    requires full_config_wf(cfg),
    ensures configuration_refinement(cfg),
{
    erasure_is_replay_well_formed(cfg);
    erasure_is_exact(cfg);
    stable_key_injectivity_is_preserved(cfg);
    assert forall|request: replay_layer::RequestId| {
        &&& #[trigger] canonical_call(cfg, request).principal
            == cfg.request[request].principal
        &&& canonical_call(cfg, request).tool == cfg.request[request].tool
        &&& canonical_call(cfg, request).operation == cfg.request[request].operation
        &&& canonical_call(cfg, request).resource == cfg.request[request].resource
        &&& canonical_call(cfg, request).arguments == cfg.request[request].arguments
        &&& canonical_call(cfg, request).digest == cfg.request[request].digest
        &&& canonical_call(cfg, request).adapter_namespace
            == cfg.request[request].adapter_namespace
        &&& canonical_call(cfg, request).key == cfg.request[request].stable_key
    } by {
        canonical_call_is_exact(cfg, request);
    }
    assert forall|request: replay_layer::RequestId,
            capability: replay_layer::CapabilityId|
        #[trigger] matches(cfg, request, capability) implies {
            let req = cfg.request[request];
            let cap = cfg.capability[capability];
            &&& req.capability == capability
            &&& req.principal == cap.principal
            &&& req.tool == cap.tool
            &&& req.operation == cap.operation
            &&& cap.resources.contains(req.resource)
            &&& cap.arguments.contains(req.arguments)
    } by {
        matches_implies_scope_fields(cfg, request, capability);
    }
}

} // verus!
