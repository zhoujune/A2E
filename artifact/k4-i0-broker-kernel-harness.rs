//! K4-I0 executable integration checkpoint.
//!
//! This harness runs the standard-Rust reference broker, captures the durable
//! typed WAL it actually produced, and feeds every supported record through
//! the proof-erased K4-A2 append state.  It is integration evidence, not a
//! Verus implementation-refinement theorem: the Rust broker, byte WAL,
//! filesystem, crash handling, and adapter remain ordinary Rust.

extern crate k4_generic_append_state_bridge;
extern crate proveai_reference_broker;

use std::path::{Path, PathBuf};
use std::time::{SystemTime, UNIX_EPOCH};

use k4_generic_append_state_bridge::{
    k4_a2_append_one, k4_a2_initial, k4_a2_supported_exec, KJournalRecord, KKernelState,
    KManifestBinding, KManifestCapability, KManifestConfig, KPhase, KRetryClass,
};
use proveai_reference_broker::adapters::{DeduplicatedAdapter, IdempotentAdapter};
use proveai_reference_broker::{
    AdmissionBinding, Broker, BrokerConfig, BrokerError, CapabilityId, CapabilitySpec, CrashPlan,
    CrashSite, DedupKey, Digest, JournalRecord, Observation, RequestId, RequestSpec, RetryClass,
    TerminalResult, Value,
};

fn retry_class_to_k4(class: RetryClass) -> KRetryClass {
    match class {
        RetryClass::ReadOnly => KRetryClass::ReadOnly,
        RetryClass::Idempotent => KRetryClass::Idempotent,
        RetryClass::Deduplicated => KRetryClass::Deduplicated,
        RetryClass::Uncontrolled => KRetryClass::Uncontrolled,
    }
}

fn observation_to_k4(observation: Observation) -> k4_generic_append_state_bridge::KObservation {
    match observation {
        Observation::Success(Value(value)) => {
            k4_generic_append_state_bridge::KObservation::Success { value }
        }
        Observation::Failure => k4_generic_append_state_bridge::KObservation::Failure,
        Observation::Ambiguous => k4_generic_append_state_bridge::KObservation::Ambiguous,
        Observation::InvalidResult(Value(value)) => {
            k4_generic_append_state_bridge::KObservation::InvalidResult { value }
        }
    }
}

fn key_fields(key: Option<DedupKey>) -> (bool, u64) {
    match key {
        Some(DedupKey(value)) => (true, value),
        None => (false, 0),
    }
}

fn broker_record_to_k4(record: JournalRecord) -> Result<KJournalRecord, &'static str> {
    Ok(match record {
        JournalRecord::Authorize {
            request: RequestId(request),
            capability: CapabilityId(capability),
            digest: Digest(digest),
        } => KJournalRecord::Authorize {
            request,
            capability,
            digest,
        },
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
                class: retry_class_to_k4(class),
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
                observation: observation_to_k4(observation),
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
        JournalRecord::Revoke { .. }
        | JournalRecord::Fail { .. }
        | JournalRecord::Unknown { .. } => {
            return Err("K4-A2 does not support Revoke, Fail, or Unknown")
        }
    })
}

fn k4_manifest(config: &BrokerConfig) -> KManifestConfig {
    let capabilities = config
        .capabilities
        .iter()
        .map(|spec| KManifestCapability {
            capability: spec.id.0,
            initial_budget: spec.budget,
        })
        .collect();
    let bindings = config
        .admission_manifest
        .as_ref()
        .expect("K4-I0 requires an immutable admission manifest")
        .iter()
        .map(|binding| {
            let (key_present, key) = key_fields(binding.spec.key);
            KManifestBinding {
                request: binding.request.0,
                capability: binding.capability.0,
                class: retry_class_to_k4(binding.spec.class),
                digest: binding.spec.digest.0,
                key_present,
                key,
            }
        })
        .collect();
    KManifestConfig {
        capabilities,
        bindings,
    }
}

fn remove_broker_files(path: &Path) {
    let _ = std::fs::remove_file(path);
    let mut sidecar = path.as_os_str().to_os_string();
    sidecar.push(".config");
    let _ = std::fs::remove_file(PathBuf::from(sidecar));
}

struct KernelMonitor {
    manifest: KManifestConfig,
    state: KKernelState,
    synced: usize,
}

impl KernelMonitor {
    fn new(config: &BrokerConfig) -> Self {
        let manifest = k4_manifest(config);
        let state = k4_a2_initial(&manifest);
        Self {
            manifest,
            state,
            synced: 0,
        }
    }

    fn sync(&mut self, records: &[JournalRecord]) {
        assert!(self.synced <= records.len());
        for (index, record) in records.iter().copied().enumerate().take(self.synced) {
            let translated = broker_record_to_k4(record)
                .expect("K4-I0 rejects broker records outside the K4-A2 theorem boundary");
            assert!(translated == self.state.journal[index]);
        }
        for (index, record) in records.iter().copied().enumerate().skip(self.synced) {
            let translated = broker_record_to_k4(record)
                .expect("K4-I0 rejects broker records outside the K4-A2 theorem boundary");
            assert!(k4_a2_supported_exec(&translated));
            let expected_lsn = u64::try_from(index + 1).expect("K4-I0 LSN fits u64");
            let cut = k4_a2_append_one(&self.manifest, &mut self.state, translated);
            assert_eq!(cut, expected_lsn);
        }
        self.synced = records.len();
        assert_eq!(self.state.journal.len(), records.len());
        assert_eq!(self.state.ack_cuts.len(), records.len());
        for (index, cut) in self.state.ack_cuts.iter().copied().enumerate() {
            assert_eq!(cut, u64::try_from(index + 1).expect("K4-I0 cut fits u64"));
        }
    }

    fn assert_committed(&self, request: u64, attempt: usize, value: u64) {
        let entry = self
            .state
            .durable
            .requests
            .iter()
            .find(|entry| entry.request == request)
            .expect("K4-I0 kernel tracks the committed request");
        assert!(entry.phase == KPhase::Committed);
        assert_eq!(entry.outcomes.len(), attempt);
        assert!(matches!(
            entry.outcomes[attempt - 1],
            Some(k4_generic_append_state_bridge::KObservation::Success {
                value: observed,
            }) if observed == value
        ));
    }

    fn assert_budget(&self, capability: u64, remaining: u64) {
        let entry = self
            .state
            .durable
            .caps
            .iter()
            .find(|entry| entry.capability == capability)
            .expect("K4-I0 kernel tracks the capability");
        assert_eq!(entry.remaining, remaining);
        assert!(!entry.revoked);
    }
}

fn verify_records(config: &BrokerConfig, records: &[JournalRecord], attempt: usize, value: u64) {
    let mut monitor = KernelMonitor::new(config);
    monitor.sync(records);
    monitor.assert_committed(1, attempt, value);
    monitor.assert_budget(1, 3);
}

fn run_idempotent_crash_retry(path: &Path) -> (BrokerConfig, Vec<JournalRecord>) {
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
    let mut monitor = KernelMonitor::new(&config);
    let mut adapter = IdempotentAdapter::scripted([]);
    {
        let mut broker = Broker::open(path, config.clone()).expect("open idempotent broker");
        let request = broker
            .admit(CapabilityId(1), Digest(1))
            .expect("admit request");
        monitor.sync(broker.wal_records());
        broker
            .prepare(request, RequestSpec::idempotent(Digest(1)))
            .expect("prepare request");
        monitor.sync(broker.wal_records());
        broker.set_crash_plan(Some(CrashPlan::once(CrashSite::AfterInvoke)));
        assert!(matches!(
            broker.run(request, RetryClass::Idempotent.max_attempts(), &mut adapter),
            Err(BrokerError::SimulatedCrash(CrashSite::AfterInvoke))
        ));
        monitor.sync(broker.wal_records());
        assert_eq!(broker.wal_records().len(), 4);
    }
    let mut broker = Broker::open(path, config.clone()).expect("reopen idempotent broker");
    monitor.sync(broker.wal_records());
    let terminal = broker
        .run(
            RequestId(1),
            RetryClass::Idempotent.max_attempts(),
            &mut adapter,
        )
        .expect("run idempotent request");
    monitor.sync(broker.wal_records());
    assert!(matches!(
        terminal,
        TerminalResult::Committed {
            attempt: 2,
            value: Value(1),
        }
    ));
    assert_eq!(adapter.invocation_count(), 2);
    assert_eq!(adapter.mutation_count(), 1);
    assert_eq!(
        broker
            .remaining_budget(CapabilityId(1))
            .expect("read budget"),
        3
    );
    monitor.assert_committed(1, 2, 1);
    monitor.assert_budget(1, 3);
    (config, broker.wal_records().to_vec())
}

fn run_deduplicated(path: &Path) -> (BrokerConfig, Vec<JournalRecord>) {
    let config = BrokerConfig {
        capabilities: vec![CapabilitySpec {
            id: CapabilityId(1),
            budget: 4,
        }],
        admission_manifest: Some(vec![AdmissionBinding {
            request: RequestId(1),
            capability: CapabilityId(1),
            spec: RequestSpec::deduplicated(Digest(7), DedupKey(99)),
        }]),
    };
    let mut broker = Broker::open(path, config.clone()).expect("open deduplicated broker");
    let mut monitor = KernelMonitor::new(&config);
    let request = broker
        .admit(CapabilityId(1), Digest(7))
        .expect("admit request");
    monitor.sync(broker.wal_records());
    broker
        .prepare(request, RequestSpec::deduplicated(Digest(7), DedupKey(99)))
        .expect("prepare request");
    monitor.sync(broker.wal_records());
    let mut adapter = DeduplicatedAdapter::scripted([]);
    let terminal = broker
        .run(
            request,
            RetryClass::Deduplicated.max_attempts(),
            &mut adapter,
        )
        .expect("run deduplicated request");
    monitor.sync(broker.wal_records());
    assert!(matches!(
        terminal,
        TerminalResult::Committed {
            attempt: 1,
            value: Value(1),
        }
    ));
    assert_eq!(adapter.mutation_count(), 1);
    assert_eq!(
        broker
            .remaining_budget(CapabilityId(1))
            .expect("read budget"),
        3
    );
    monitor.assert_committed(1, 1, 1);
    monitor.assert_budget(1, 3);
    (config, broker.wal_records().to_vec())
}

fn main() {
    let serial = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("system time is after the Unix epoch")
        .as_nanos();
    let root = std::env::temp_dir();
    let idempotent_path = root.join(format!("proveai-k4-i0-idempotent-{serial}.wal"));
    let deduplicated_path = root.join(format!("proveai-k4-i0-deduplicated-{serial}.wal"));

    assert!(broker_record_to_k4(JournalRecord::Revoke {
        capability: CapabilityId(1),
    })
    .is_err());
    assert!(broker_record_to_k4(JournalRecord::Fail {
        request: RequestId(1),
        attempt: 1,
        digest: Digest(1),
        key: None,
        outcome_ref: 5,
    })
    .is_err());
    assert!(broker_record_to_k4(JournalRecord::Unknown {
        request: RequestId(1),
        attempt: Some(1),
        reason: proveai_reference_broker::UnknownReason::Recovery,
        digest: Digest(1),
        key: None,
        evidence_ref: 5,
    })
    .is_err());

    let (idempotent_config, idempotent_records) = run_idempotent_crash_retry(&idempotent_path);
    verify_records(&idempotent_config, &idempotent_records, 2, 1);
    assert_eq!(idempotent_records.len(), 8);
    remove_broker_files(&idempotent_path);

    let (deduplicated_config, deduplicated_records) = run_deduplicated(&deduplicated_path);
    verify_records(&deduplicated_config, &deduplicated_records, 1, 1);
    assert_eq!(deduplicated_records.len(), 6);
    remove_broker_files(&deduplicated_path);

    println!(
        "K4-I0 broker-to-kernel integration passed: idempotent={} records, deduplicated={} records",
        idempotent_records.len(),
        deduplicated_records.len()
    );
}
