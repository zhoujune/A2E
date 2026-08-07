mod common;

use common::{config, uncontrolled_spec, TestDirectory};
use proveai_reference_broker::adapters::UncontrolledAdapter;
use proveai_reference_broker::{
    Broker, BrokerError, CapabilityId, Digest, JournalRecord, Phase, RequestId, TerminalResult,
    Value,
};

#[test]
fn admission_consumes_budget_and_execution_is_recoverable() {
    let directory = TestDirectory::new("normal");
    let mut broker = Broker::open(directory.wal(), config(2)).expect("open broker");

    let request = broker
        .admit(CapabilityId(7), uncontrolled_spec().digest)
        .expect("admit request");
    assert_eq!(request, RequestId(1));
    assert_eq!(broker.remaining_budget(CapabilityId(7)).unwrap(), 1);
    assert_eq!(broker.request_capability(request).unwrap(), CapabilityId(7));
    broker
        .prepare(request, uncontrolled_spec())
        .expect("prepare request");

    let mut adapter = UncontrolledAdapter::default();
    let terminal = broker.run(request, 1, &mut adapter).expect("run request");
    assert_eq!(
        terminal,
        TerminalResult::Committed {
            attempt: 1,
            value: Value(1)
        }
    );
    assert_eq!(adapter.effect_count(), 1);
    assert_eq!(broker.phase(request).unwrap(), Phase::Committed);
    assert_eq!(broker.wal_records().len(), 6);
    assert!(matches!(
        broker.wal_records()[0],
        JournalRecord::Authorize {
            request: RequestId(1),
            ..
        }
    ));
    assert!(matches!(
        broker.wal_records()[5],
        JournalRecord::Commit { outcome_ref: 5, .. }
    ));
    drop(broker);

    let recovered = Broker::open(directory.wal(), config(2)).expect("replay a complete execution");
    assert_eq!(recovered.terminal(request).unwrap(), Some(terminal));
    assert_eq!(recovered.remaining_budget(CapabilityId(7)).unwrap(), 1);
}

#[test]
fn invalid_capabilities_and_budget_exhaustion_do_not_append() {
    let directory = TestDirectory::new("budget");
    let mut broker = Broker::open(directory.wal(), config(1)).expect("open broker");
    assert!(matches!(
        broker.admit(CapabilityId(99), Digest(1)),
        Err(BrokerError::UnknownCapability(CapabilityId(99)))
    ));
    broker
        .admit(CapabilityId(7), Digest(1))
        .expect("consume the sole budget unit");
    assert!(matches!(
        broker.admit(CapabilityId(7), Digest(2)),
        Err(BrokerError::BudgetExhausted(CapabilityId(7)))
    ));
    assert_eq!(broker.wal_records().len(), 1);
}
