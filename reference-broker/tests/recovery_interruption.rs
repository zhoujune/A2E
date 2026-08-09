mod common;

use common::{config, deduplicated_spec, idempotent_spec, uncontrolled_spec, TestDirectory};
use proveai_reference_broker::adapter::Adapter;
use proveai_reference_broker::adapters::{
    DeduplicatedAdapter, IdempotentAdapter, UncontrolledAdapter,
};
use proveai_reference_broker::{
    Broker, BrokerError, CapabilityId, CrashPlan, CrashSite, RequestSpec, RetryClass,
    TerminalResult, UnknownReason,
};

enum ExampleAdapter {
    Uncontrolled(UncontrolledAdapter),
    Idempotent(IdempotentAdapter),
    Deduplicated(DeduplicatedAdapter),
}

impl ExampleAdapter {
    fn new(class: RetryClass) -> Self {
        match class {
            RetryClass::Uncontrolled => Self::Uncontrolled(UncontrolledAdapter::default()),
            RetryClass::Idempotent => Self::Idempotent(IdempotentAdapter::default()),
            RetryClass::Deduplicated => Self::Deduplicated(DeduplicatedAdapter::default()),
            RetryClass::ReadOnly => unreachable!(),
        }
    }

    fn effects(&self) -> u64 {
        match self {
            Self::Uncontrolled(adapter) => adapter.effect_count(),
            Self::Idempotent(adapter) => adapter.mutation_count(),
            Self::Deduplicated(adapter) => adapter.mutation_count(),
        }
    }
}

impl Adapter for ExampleAdapter {
    fn retry_class(&self) -> RetryClass {
        match self {
            Self::Uncontrolled(adapter) => adapter.retry_class(),
            Self::Idempotent(adapter) => adapter.retry_class(),
            Self::Deduplicated(adapter) => adapter.retry_class(),
        }
    }

    fn invoke(
        &mut self,
        invocation: proveai_reference_broker::Invocation,
    ) -> proveai_reference_broker::Delivery {
        match self {
            Self::Uncontrolled(adapter) => adapter.invoke(invocation),
            Self::Idempotent(adapter) => adapter.invoke(invocation),
            Self::Deduplicated(adapter) => adapter.invoke(invocation),
        }
    }
}

fn exercise(class: RetryClass, spec: RequestSpec) -> (TerminalResult, u64) {
    let directory = TestDirectory::new(&format!("recovery-interruption-{class:?}"));
    let mut adapter = ExampleAdapter::new(class);
    let request;
    {
        let mut broker = Broker::open(directory.wal(), config(1)).unwrap();
        request = broker.admit(CapabilityId(7), spec.digest).unwrap();
        broker.prepare(request, spec).unwrap();
        broker.set_crash_plan(Some(CrashPlan::once(CrashSite::AfterStart)));
        assert!(matches!(
            broker.run(request, class.max_attempts(), &mut adapter),
            Err(BrokerError::SimulatedCrash(CrashSite::AfterStart))
        ));
    }
    {
        let mut recovering = Broker::open(directory.wal(), config(1)).unwrap();
        recovering.set_crash_plan(Some(CrashPlan::once(CrashSite::AfterOutcome)));
        assert!(matches!(
            recovering.run(request, class.max_attempts(), &mut adapter),
            Err(BrokerError::SimulatedCrash(CrashSite::AfterOutcome))
        ));
    }
    let mut recovered = Broker::open(directory.wal(), config(1)).unwrap();
    let terminal = recovered
        .run(request, class.max_attempts(), &mut adapter)
        .unwrap();
    (terminal, adapter.effects())
}

#[test]
fn recovery_can_be_interrupted_and_resumed_for_each_adapter() {
    let (uncontrolled, uncontrolled_effects) =
        exercise(RetryClass::Uncontrolled, uncontrolled_spec());
    assert_eq!(
        uncontrolled,
        TerminalResult::Unknown {
            attempt: Some(1),
            reason: UnknownReason::AmbiguousOutcome,
        }
    );
    assert_eq!(uncontrolled_effects, 0);

    let (idempotent, idempotent_effects) = exercise(RetryClass::Idempotent, idempotent_spec());
    assert!(matches!(
        idempotent,
        TerminalResult::Committed { attempt: 2, .. }
    ));
    assert_eq!(idempotent_effects, 1);

    let (deduplicated, deduplicated_effects) =
        exercise(RetryClass::Deduplicated, deduplicated_spec());
    assert!(matches!(
        deduplicated,
        TerminalResult::Committed { attempt: 2, .. }
    ));
    assert_eq!(deduplicated_effects, 1);
}
