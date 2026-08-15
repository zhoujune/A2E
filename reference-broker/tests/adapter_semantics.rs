mod common;

use common::{config, deduplicated_spec, idempotent_spec, uncontrolled_spec, TestDirectory};
use proveai_reference_broker::adapters::{
    DeduplicatedAdapter, IdempotentAdapter, UncontrolledAdapter,
};
use proveai_reference_broker::{
    Broker, CapabilityId, Observation, RetryClass, TerminalResult, UnknownReason, Value,
};

#[test]
fn uncontrolled_ambiguity_is_not_retried() {
    let directory = TestDirectory::new("uncontrolled-ambiguous");
    let mut broker = Broker::open(directory.wal(), config(1)).unwrap();
    let request = broker
        .admit(CapabilityId(7), uncontrolled_spec().digest)
        .unwrap();
    broker.prepare(request, uncontrolled_spec()).unwrap();
    let mut adapter = UncontrolledAdapter::scripted([Observation::Ambiguous]);
    assert_eq!(
        broker
            .run(
                request,
                RetryClass::Uncontrolled.max_attempts(),
                &mut adapter
            )
            .unwrap(),
        TerminalResult::Unknown {
            attempt: Some(1),
            reason: UnknownReason::AmbiguousOutcome,
        }
    );
    assert_eq!(adapter.effect_count(), 1);
}

#[test]
fn idempotent_retry_repeats_the_call_but_not_the_effect() {
    let directory = TestDirectory::new("idempotent-retry");
    let mut broker = Broker::open(directory.wal(), config(1)).unwrap();
    let request = broker
        .admit(CapabilityId(7), idempotent_spec().digest)
        .unwrap();
    broker.prepare(request, idempotent_spec()).unwrap();
    let mut adapter = IdempotentAdapter::scripted([Observation::Ambiguous]);
    assert_eq!(
        broker.run(request, 3, &mut adapter).unwrap(),
        TerminalResult::Committed {
            attempt: 2,
            value: Value(1),
        }
    );
    assert_eq!(adapter.mutation_count(), 1);
}

#[test]
fn deduplicated_retry_reuses_the_keyed_decision() {
    let directory = TestDirectory::new("deduplicated-retry");
    let mut broker = Broker::open(directory.wal(), config(1)).unwrap();
    let spec = deduplicated_spec();
    let request = broker.admit(CapabilityId(7), spec.digest).unwrap();
    broker.prepare(request, spec).unwrap();
    let mut adapter = DeduplicatedAdapter::scripted([Observation::Ambiguous]);
    assert_eq!(
        broker.run(request, 3, &mut adapter).unwrap(),
        TerminalResult::Committed {
            attempt: 2,
            value: Value(1),
        }
    );
    assert_eq!(adapter.mutation_count(), 1);
    assert_eq!(adapter.decision(spec.key.unwrap()), Some(Value(1)));
}

#[test]
fn retry_limit_terminalizes_persistent_ambiguity() {
    let directory = TestDirectory::new("retry-exhaustion");
    let mut broker = Broker::open(directory.wal(), config(1)).unwrap();
    let request = broker
        .admit(CapabilityId(7), idempotent_spec().digest)
        .unwrap();
    broker.prepare(request, idempotent_spec()).unwrap();
    let mut adapter = IdempotentAdapter::scripted([
        Observation::Ambiguous,
        Observation::Ambiguous,
        Observation::Ambiguous,
    ]);
    assert_eq!(
        broker.run(request, 3, &mut adapter).unwrap(),
        TerminalResult::Unknown {
            attempt: Some(3),
            reason: UnknownReason::Exhausted,
        }
    );
    assert_eq!(adapter.mutation_count(), 1);
}

#[test]
fn failure_after_uncertain_idempotent_attempt_is_not_reported_as_conclusive() {
    let directory = TestDirectory::new("idempotent-non-conclusive-failure");
    let mut broker = Broker::open(directory.wal(), config(1)).unwrap();
    let request = broker
        .admit(CapabilityId(7), idempotent_spec().digest)
        .unwrap();
    broker.prepare(request, idempotent_spec()).unwrap();
    let mut adapter = IdempotentAdapter::scripted([Observation::Ambiguous, Observation::Failure]);
    assert_eq!(
        broker.run(request, 3, &mut adapter).unwrap(),
        TerminalResult::Unknown {
            attempt: Some(2),
            reason: UnknownReason::NonConclusiveFailure,
        }
    );
    assert_eq!(adapter.invocation_count(), 2);
    assert_eq!(adapter.mutation_count(), 1);
}

#[test]
fn retry_safe_invalid_result_is_retried() {
    let directory = TestDirectory::new("idempotent-invalid-result-retry");
    let mut broker = Broker::open(directory.wal(), config(1)).unwrap();
    let request = broker
        .admit(CapabilityId(7), idempotent_spec().digest)
        .unwrap();
    broker.prepare(request, idempotent_spec()).unwrap();
    let mut adapter = IdempotentAdapter::scripted([Observation::InvalidResult(Value(999))]);
    assert_eq!(
        broker.run(request, 3, &mut adapter).unwrap(),
        TerminalResult::Committed {
            attempt: 2,
            value: Value(1),
        }
    );
    assert_eq!(adapter.invocation_count(), 2);
    assert_eq!(adapter.mutation_count(), 1);
}

#[test]
fn retry_safe_adapters_normalize_scripted_success_values() {
    let directory = TestDirectory::new("normalized-idempotent-success");
    let mut broker = Broker::open(directory.wal(), config(1)).unwrap();
    let request = broker
        .admit(CapabilityId(7), idempotent_spec().digest)
        .unwrap();
    broker.prepare(request, idempotent_spec()).unwrap();
    let mut adapter = IdempotentAdapter::scripted([Observation::Success(Value(999))]);
    assert_eq!(
        broker.run(request, 3, &mut adapter).unwrap(),
        TerminalResult::Committed {
            attempt: 1,
            value: Value(1),
        }
    );

    let directory = TestDirectory::new("normalized-deduplicated-success");
    let mut broker = Broker::open(directory.wal(), config(1)).unwrap();
    let spec = deduplicated_spec();
    let request = broker.admit(CapabilityId(7), spec.digest).unwrap();
    broker.prepare(request, spec).unwrap();
    let mut adapter = DeduplicatedAdapter::scripted([Observation::Success(Value(999))]);
    assert_eq!(
        broker.run(request, 3, &mut adapter).unwrap(),
        TerminalResult::Committed {
            attempt: 1,
            value: Value(1),
        }
    );
}
