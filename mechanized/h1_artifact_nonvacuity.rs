use vstd::prelude::*;

#[path = "t5_commit_contextual.rs"]
pub mod t5_c0_layer;

verus! {

use t5_c0_layer::t5_r0_layer;
use t5_r0_layer::t5_e0_layer;
use t5_e0_layer::t5_s0_layer;
use t5_s0_layer::t4_layer;
use t4_layer::t4_c1_layer;
use t4_c1_layer::t4_c0_layer;
use t4_c0_layer::t3_layer;
use t3_layer::representation_layer as t3_representation_layer;
use t3_representation_layer::event_layer as t3_event_layer;
use t3_event_layer::trace_layer as wal_trace_layer;
use wal_trace_layer::runtime_layer as wal_runtime_layer;
use wal_runtime_layer::t2_layer;
use t2_layer::representation_layer as t2_representation_layer;
use t2_representation_layer::event_layer as t2_event_layer;
use t2_event_layer::trace_layer as journal_trace_layer;
use journal_trace_layer::runtime_layer as journal_runtime_layer;
use journal_runtime_layer::t1_layer;
use t1_layer::execution_layer;
use execution_layer::projection_layer;
use projection_layer::global_layer;
use global_layer::bridge_layer;
use bridge_layer::contract_layer;
use contract_layer::p3_layer::p2_layer::p1_layer::p0_layer;
use p0_layer::config_layer;
use config_layer::broker_layer as record_layer;
use record_layer::query_layer::c1_layer::replay_layer;

// H1 closes the artifact-level nonvacuity gap with a concrete, total
// configuration. Every request is uncontrolled, so the stable-key
// injectivity condition is vacuous rather than postulated.

pub open spec fn h1_request(
    _request: replay_layer::RequestId,
) -> config_layer::Request {
    config_layer::Request {
        principal: config_layer::Principal { id: 0 },
        tool: config_layer::Tool { id: 0 },
        operation: config_layer::Operation { id: 0 },
        resource: config_layer::Resource { id: 0 },
        arguments: config_layer::Arguments { id: 0 },
        capability: replay_layer::CapabilityId { id: 0 },
        retry_class: replay_layer::RetryClass::Uncontrolled,
        digest: replay_layer::Digest { id: 0 },
        adapter_namespace: replay_layer::AdapterNamespace { id: 0 },
        stable_key: Option::None,
        max_attempts: 1,
    }
}

pub open spec fn h1_capability(
    _capability: replay_layer::CapabilityId,
) -> config_layer::Capability {
    config_layer::Capability {
        principal: config_layer::Principal { id: 0 },
        tool: config_layer::Tool { id: 0 },
        operation: config_layer::Operation { id: 0 },
        resources: ISet::<config_layer::Resource>::full(),
        arguments: ISet::<config_layer::Arguments>::full(),
        initial_budget: 1,
    }
}

pub open spec fn h1_full_config() -> config_layer::FullConfig {
    config_layer::FullConfig {
        request: IMap::new(
            |_request: replay_layer::RequestId| true,
            |request: replay_layer::RequestId| h1_request(request),
        ),
        capability: IMap::new(
            |_capability: replay_layer::CapabilityId| true,
            |capability: replay_layer::CapabilityId| h1_capability(capability),
        ),
        valid_results: ISet::<(
            replay_layer::RequestId,
            replay_layer::Value,
        )>::full(),
    }
}

pub proof fn h1_full_config_is_well_formed()
    ensures
        config_layer::full_config_wf(h1_full_config()),
        h1_full_config().request.dom()
            == ISet::<replay_layer::RequestId>::full(),
        h1_full_config().capability.dom()
            == ISet::<replay_layer::CapabilityId>::full(),
        forall|request: replay_layer::RequestId|
            #[trigger] h1_full_config().request[request].retry_class
                == replay_layer::RetryClass::Uncontrolled,
        forall|request: replay_layer::RequestId|
            #[trigger] h1_full_config().request[request].stable_key
                == Option::None,
        forall|request: replay_layer::RequestId|
            #[trigger] h1_full_config().request[request].max_attempts == 1,
{
    let cfg = h1_full_config();
    assert(cfg.request.dom() == ISet::<replay_layer::RequestId>::full());
    assert(cfg.capability.dom()
        == ISet::<replay_layer::CapabilityId>::full());
    assert forall|request: replay_layer::RequestId|
        #[trigger] cfg.request[request].retry_class
            == replay_layer::RetryClass::Uncontrolled by {
    }
    assert forall|request: replay_layer::RequestId|
        #[trigger] cfg.request[request].stable_key == Option::None by {
    }
    assert forall|request: replay_layer::RequestId|
        #[trigger] cfg.request[request].max_attempts == 1 by {
    }
    assert forall|request: replay_layer::RequestId|
        #[trigger] cfg.request[request].max_attempts > 0 by {
    }
    assert forall|request: replay_layer::RequestId|
        (#[trigger] cfg.request[request].retry_class
                == replay_layer::RetryClass::Deduplicated
            <==> cfg.request[request].stable_key.is_some()) by {
    }
    assert forall|left: replay_layer::RequestId,
                  right: replay_layer::RequestId| #![auto]
        cfg.request[left].retry_class
                == replay_layer::RetryClass::Deduplicated
            && cfg.request[right].retry_class
                == replay_layer::RetryClass::Deduplicated
            && cfg.request[left].adapter_namespace
                == cfg.request[right].adapter_namespace
            && cfg.request[left].stable_key
                == cfg.request[right].stable_key
                ==> left == right by {
    }
}

pub open spec fn t5_c0_premise_conclusion_package(
    cfg: config_layer::FullConfig,
    context: t4_c1_layer::ProgramContext<nat>,
    source: t4_c1_layer::PluggedWalExecution<nat>,
    crash: nat,
    finish: nat,
) -> bool {
    &&& config_layer::full_config_wf(cfg)
    &&& t4_c1_layer::storage_parametric_context(cfg, context)
    &&& t4_c1_layer::plugged_wal_exec(cfg, context, source)
    &&& t5_r0_layer::recovery_episode(
        source.machine.events, crash, finish,
    )
    &&& t5_c0_layer::t5_c0_statement(
        cfg, context, source, crash, finish,
    )
}

pub proof fn h1_concrete_t5_c0_package()
    ensures t5_c0_premise_conclusion_package(
        h1_full_config(),
        t4_c1_layer::inert_context(h1_full_config(), 0nat),
        t5_c0_layer::minimal_contextual_recovery_execution(
            h1_full_config(), 0nat,
        ),
        0,
        5,
    ),
{
    h1_full_config_is_well_formed();
    t5_c0_layer::inert_context_has_minimal_contextual_recovery_episode(
        h1_full_config(), 0nat,
    );
}

pub proof fn h1_artifact_nonvacuity()
    ensures exists|cfg: config_layer::FullConfig,
                    context: t4_c1_layer::ProgramContext<nat>,
                    source: t4_c1_layer::PluggedWalExecution<nat>,
                    crash: nat,
                    finish: nat|
        cfg == h1_full_config()
            && crash == 0
            && finish == 5
            && t5_c0_premise_conclusion_package(
                cfg, context, source, crash, finish,
            ),
{
    h1_concrete_t5_c0_package();
    let cfg = h1_full_config();
    let context = t4_c1_layer::inert_context(cfg, 0nat);
    let source = t5_c0_layer::minimal_contextual_recovery_execution(
        cfg, 0nat,
    );
    assert(t5_c0_premise_conclusion_package(
        cfg, context, source, 0, 5,
    ));
    assert(exists|cfg: config_layer::FullConfig,
                  context: t4_c1_layer::ProgramContext<nat>,
                  source: t4_c1_layer::PluggedWalExecution<nat>,
                  crash: nat,
                  finish: nat|
        cfg == h1_full_config()
            && crash == 0
            && finish == 5
            && t5_c0_premise_conclusion_package(
                cfg, context, source, crash, finish,
            )) by {
        let cfg = h1_full_config();
        let context = t4_c1_layer::inert_context(cfg, 0nat);
        let source = t5_c0_layer::minimal_contextual_recovery_execution(
            cfg, 0nat,
        );
    }
}

} // verus!
