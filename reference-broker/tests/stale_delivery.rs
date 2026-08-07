mod common;

use common::{config, idempotent_spec, TestDirectory};
use proveai_reference_broker::{
    Broker, BrokerError, CapabilityId, Delivery, Observation, TerminalResult, Value,
};

#[test]
fn retry_rejects_the_previous_invocations_delivery() {
    let directory = TestDirectory::new("stale");
    let mut broker = Broker::open(directory.wal(), config(1)).expect("open broker");
    let request = broker
        .admit(CapabilityId(7), idempotent_spec().digest)
        .unwrap();
    broker.prepare(request, idempotent_spec()).unwrap();

    let first = broker.begin_attempt(request).expect("first attempt");
    assert_eq!(
        broker
            .accept_delivery(Delivery {
                invocation: first.id,
                observation: Observation::Ambiguous,
            })
            .unwrap(),
        None
    );
    let second = broker.begin_attempt(request).expect("retry attempt");
    assert_ne!(first.id, second.id);

    let before = broker.wal_records().len();
    assert!(matches!(
        broker.accept_delivery(Delivery {
            invocation: first.id,
            observation: Observation::Success(Value(99)),
        }),
        Err(BrokerError::StaleDelivery {
            expected: Some(expected),
            received,
        }) if expected == second.id && received == first.id
    ));
    assert_eq!(broker.wal_records().len(), before);
    assert_eq!(broker.active_invocation(), Some(second));

    assert_eq!(
        broker
            .accept_delivery(Delivery {
                invocation: second.id,
                observation: Observation::Success(Value(1)),
            })
            .unwrap(),
        Some(TerminalResult::Committed {
            attempt: 2,
            value: Value(1),
        })
    );
}
