mod common;

use common::TestDirectory;
use proveai_reference_broker::{
    AdmissionBinding, Broker, BrokerConfig, BrokerError, CapabilityId, CapabilitySpec, Digest,
    RequestId, RequestSpec,
};

fn manifest_config(spec: RequestSpec) -> BrokerConfig {
    BrokerConfig {
        capabilities: vec![CapabilitySpec {
            id: CapabilityId(7),
            budget: 2,
        }],
        admission_manifest: Some(vec![AdmissionBinding {
            request: RequestId(1),
            capability: CapabilityId(7),
            spec,
        }]),
    }
}

#[test]
fn manifest_rejects_mismatched_admission_and_prepare_without_appending() {
    let directory = TestDirectory::new("manifest-mismatch");
    let expected = RequestSpec::idempotent(Digest(101));
    let mut broker = Broker::open(directory.wal(), manifest_config(expected)).unwrap();

    assert!(matches!(
        broker.admit(CapabilityId(7), Digest(102)),
        Err(BrokerError::InvalidSpec(_))
    ));
    assert!(broker.wal_records().is_empty());

    let request = broker.admit(CapabilityId(7), expected.digest).unwrap();
    assert!(matches!(
        broker.prepare(request, RequestSpec::uncontrolled(expected.digest)),
        Err(BrokerError::InvalidSpec(_))
    ));
    assert_eq!(broker.wal_records().len(), 1);

    broker.prepare(request, expected).unwrap();
    assert_eq!(broker.wal_records().len(), 2);
}

#[test]
fn manifest_rejects_a_request_not_predeclared_by_the_profile() {
    let directory = TestDirectory::new("manifest-missing");
    let config = BrokerConfig {
        capabilities: vec![CapabilitySpec {
            id: CapabilityId(7),
            budget: 1,
        }],
        admission_manifest: Some(Vec::new()),
    };
    let mut broker = Broker::open(directory.wal(), config).unwrap();

    assert!(matches!(
        broker.admit(CapabilityId(7), Digest(101)),
        Err(BrokerError::InvalidSpec(_))
    ));
    assert!(broker.wal_records().is_empty());
}

#[test]
fn manifest_binding_is_persisted_with_the_broker_configuration() {
    let directory = TestDirectory::new("manifest-sidecar");
    let idempotent = RequestSpec::idempotent(Digest(101));
    let mut broker = Broker::open(directory.wal(), manifest_config(idempotent)).unwrap();
    broker.admit(CapabilityId(7), idempotent.digest).unwrap();
    drop(broker);

    assert!(matches!(
        Broker::open(
            directory.wal(),
            manifest_config(RequestSpec::uncontrolled(Digest(101)))
        ),
        Err(BrokerError::ConfigurationMismatch)
    ));
}
