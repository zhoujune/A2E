mod common;

use common::{config, idempotent_spec, TestDirectory};
use proveai_reference_broker::adapters::IdempotentAdapter;
use proveai_reference_broker::{
    Broker, BrokerError, CapabilityId, CrashPlan, CrashSite, Delivery, JournalRecord, Observation,
    RetryClass, TerminalResult, UnknownReason,
};

#[test]
fn reopening_rejects_a_different_capability_budget() {
    let directory = TestDirectory::new("config-binding");
    drop(Broker::open(directory.wal(), config(1)).unwrap());

    assert!(matches!(
        Broker::open(directory.wal(), config(2)),
        Err(BrokerError::ConfigurationMismatch)
    ));
}

#[test]
fn run_rejects_a_caller_selected_retry_limit() {
    let directory = TestDirectory::new("retry-limit-mismatch");
    let mut broker = Broker::open(directory.wal(), config(1)).unwrap();
    let request = broker
        .admit(CapabilityId(7), idempotent_spec().digest)
        .unwrap();
    broker.prepare(request, idempotent_spec()).unwrap();
    let mut adapter = IdempotentAdapter::default();

    assert!(matches!(
        broker.run(request, 2, &mut adapter),
        Err(BrokerError::AttemptLimitMismatch {
            configured: 3,
            supplied: 2,
        })
    ));
    assert_eq!(adapter.invocation_count(), 0);
}

#[test]
fn manual_delivery_path_terminalizes_at_the_class_limit() {
    let directory = TestDirectory::new("manual-retry-limit");
    let mut broker = Broker::open(directory.wal(), config(1)).unwrap();
    let request = broker
        .admit(CapabilityId(7), idempotent_spec().digest)
        .unwrap();
    broker.prepare(request, idempotent_spec()).unwrap();

    for expected_attempt in 1..=RetryClass::Idempotent.max_attempts() {
        let invocation = broker.begin_attempt(request).unwrap();
        assert_eq!(invocation.attempt, expected_attempt);
        let terminal = broker
            .accept_delivery(Delivery {
                invocation: invocation.id,
                observation: Observation::Ambiguous,
            })
            .unwrap();
        if expected_attempt < RetryClass::Idempotent.max_attempts() {
            assert_eq!(terminal, None);
        } else {
            assert_eq!(
                terminal,
                Some(TerminalResult::Unknown {
                    attempt: Some(expected_attempt),
                    reason: UnknownReason::Exhausted,
                })
            );
        }
    }
    assert_eq!(
        broker
            .wal_records()
            .iter()
            .filter(|record| matches!(record, JournalRecord::Start { .. }))
            .count(),
        RetryClass::Idempotent.max_attempts() as usize
    );
}

#[test]
fn simulated_crash_requires_reopening_the_broker() {
    let directory = TestDirectory::new("crash-poison");
    let mut broker = Broker::open(directory.wal(), config(2)).unwrap();
    broker.set_crash_plan(Some(CrashPlan::once(CrashSite::AfterAuthorize)));
    assert!(matches!(
        broker.admit(CapabilityId(7), idempotent_spec().digest),
        Err(BrokerError::SimulatedCrash(CrashSite::AfterAuthorize))
    ));
    assert!(matches!(
        broker.admit(CapabilityId(7), idempotent_spec().digest),
        Err(BrokerError::Crashed)
    ));
}
