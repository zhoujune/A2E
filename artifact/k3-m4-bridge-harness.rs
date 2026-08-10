extern crate k3_append_linearization_kernel;
extern crate proveai_reference_broker;

use std::path::{Path, PathBuf};
use std::time::{SystemTime, UNIX_EPOCH};

use k3_append_linearization_kernel::{
    k3_initial, k3_linearize, k3_return, k3_try_call, KJournalRecord, KObservation,
    KRetryClass, KUnknownReason,
};
use proveai_reference_broker::adapters::IdempotentAdapter;
use proveai_reference_broker::{
    AdmissionBinding, Broker, BrokerConfig, CapabilityId, CapabilitySpec, DedupKey, Digest,
    JournalRecord, Observation, RequestId, RequestSpec, RetryClass, TerminalResult,
    UnknownReason, Value,
};

fn retry_class_to_k3(class: RetryClass) -> KRetryClass {
    match class {
        RetryClass::ReadOnly => KRetryClass::ReadOnly,
        RetryClass::Idempotent => KRetryClass::Idempotent,
        RetryClass::Deduplicated => KRetryClass::Deduplicated,
        RetryClass::Uncontrolled => KRetryClass::Uncontrolled,
    }
}

fn observation_to_k3(observation: Observation) -> KObservation {
    match observation {
        Observation::Success(Value(value)) => KObservation::Success { value },
        Observation::Failure => KObservation::Failure,
        Observation::Ambiguous => KObservation::Ambiguous,
        Observation::InvalidResult(Value(value)) => KObservation::InvalidResult { value },
    }
}

fn unknown_reason_to_k3(reason: UnknownReason) -> KUnknownReason {
    match reason {
        UnknownReason::Exhausted => KUnknownReason::Exhausted,
        UnknownReason::Recovery => KUnknownReason::Recovery,
        UnknownReason::NonConclusiveFailure => KUnknownReason::NonConclusiveFailure,
        UnknownReason::AmbiguousOutcome => KUnknownReason::AmbiguousOutcome,
        UnknownReason::InvalidResult => KUnknownReason::InvalidResultReason,
    }
}

fn key_fields(key: Option<DedupKey>) -> (bool, u64) {
    match key {
        Some(DedupKey(value)) => (true, value),
        None => (false, 0),
    }
}

fn m4_record_to_k3(record: JournalRecord) -> KJournalRecord {
    match record {
        JournalRecord::Authorize {
            request: RequestId(request),
            capability: CapabilityId(capability),
            digest: Digest(digest),
        } => KJournalRecord::Authorize {
            request,
            capability,
            digest,
        },
        JournalRecord::Revoke {
            capability: CapabilityId(capability),
        } => KJournalRecord::Revoke { capability },
        JournalRecord::Prepare {
            request: RequestId(request),
            class,
            digest: Digest(digest),
            key,
            auth_ref,
        } => {
            let (key_present, key) = key_fields(key);
            KJournalRecord::Prepare {
                request,
                class: retry_class_to_k3(class),
                digest,
                key_present,
                key,
                auth_ref,
            }
        }
        JournalRecord::Arm {
            request: RequestId(request),
            digest: Digest(digest),
            key,
            prepare_ref,
        } => {
            let (key_present, key) = key_fields(key);
            KJournalRecord::Arm {
                request,
                digest,
                key_present,
                key,
                prepare_ref,
            }
        }
        JournalRecord::Start {
            request: RequestId(request),
            attempt,
            digest: Digest(digest),
            key,
            arm_ref,
        } => {
            let (key_present, key) = key_fields(key);
            KJournalRecord::Start {
                request,
                attempt,
                digest,
                key_present,
                key,
                arm_ref,
            }
        }
        JournalRecord::Outcome {
            request: RequestId(request),
            attempt,
            observation,
            digest: Digest(digest),
            key,
            start_ref,
        } => {
            let (key_present, key) = key_fields(key);
            KJournalRecord::Outcome {
                request,
                attempt,
                observation: observation_to_k3(observation),
                digest,
                key_present,
                key,
                start_ref,
            }
        }
        JournalRecord::Commit {
            request: RequestId(request),
            attempt,
            value: Value(value),
            digest: Digest(digest),
            key,
            outcome_ref,
        } => {
            let (key_present, key) = key_fields(key);
            KJournalRecord::Commit {
                request,
                attempt,
                value,
                digest,
                key_present,
                key,
                outcome_ref,
            }
        }
        JournalRecord::Fail {
            request: RequestId(request),
            attempt,
            digest: Digest(digest),
            key,
            outcome_ref,
        } => {
            let (key_present, key) = key_fields(key);
            KJournalRecord::Fail {
                request,
                attempt,
                digest,
                key_present,
                key,
                outcome_ref,
            }
        }
        JournalRecord::Unknown {
            request: RequestId(request),
            attempt,
            reason,
            digest: Digest(digest),
            key,
            evidence_ref,
        } => {
            let (key_present, key) = key_fields(key);
            KJournalRecord::Unknown {
                request,
                attempt_present: attempt.is_some(),
                attempt: attempt.unwrap_or(0),
                reason: unknown_reason_to_k3(reason),
                digest,
                key_present,
                key,
                evidence_ref,
            }
        }
    }
}

fn verify_certificate(records: &[JournalRecord]) {
    let mut state = k3_initial();
    for (index, record) in records.iter().copied().enumerate() {
        let k3_record = m4_record_to_k3(record);
        assert!(k3_try_call(&mut state, k3_record));
        let expected_lsn = u64::try_from(index + 1).expect("certificate LSN fits u64");
        assert_eq!(k3_linearize(&mut state, k3_record), Some(expected_lsn));
        assert_eq!(k3_return(&mut state), Some(expected_lsn));
    }
    assert_eq!(state.journal.len(), records.len());
    assert_eq!(state.ack_cuts.len(), records.len());
}

fn remove_broker_files(path: &Path) {
    let _ = std::fs::remove_file(path);
    let mut sidecar = path.as_os_str().to_os_string();
    sidecar.push(".config");
    let _ = std::fs::remove_file(PathBuf::from(sidecar));
}

fn main() {
    let serial = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("system time is after the Unix epoch")
        .as_nanos();
    let wal_path = std::env::temp_dir().join(format!(
        "proveai-k3-m4-bridge-{}-{serial}.wal",
        std::process::id()
    ));

    let records = {
        let config = BrokerConfig {
            capabilities: vec![CapabilitySpec {
                id: CapabilityId(1),
                budget: 4,
            }],
            admission_manifest: Some(vec![AdmissionBinding {
                request: RequestId(1),
                capability: CapabilityId(1),
                spec: RequestSpec::idempotent(Digest(1)),
            }]),
        };
        let mut broker = Broker::open(&wal_path, config).expect("open K3-profile broker");
        let request = broker
            .admit(CapabilityId(1), Digest(1))
            .expect("admit K3-profile request");
        assert_eq!(request, RequestId(1));
        broker
            .prepare(request, RequestSpec::idempotent(Digest(1)))
            .expect("prepare K3-profile request");
        let mut adapter = IdempotentAdapter::scripted([]);
        let terminal = broker
            .run(request, RetryClass::Idempotent.max_attempts(), &mut adapter)
            .expect("complete K3-profile request");
        assert!(matches!(terminal, TerminalResult::Committed { attempt: 1, .. }));
        broker.wal_records().to_vec()
    };

    assert_eq!(records.len(), 6);
    verify_certificate(&records);
    remove_broker_files(&wal_path);
    println!(
        "M4 K3-profile certificate passed: {} records accepted at exact LSNs",
        records.len()
    );
}
