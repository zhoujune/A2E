//! K4-I0 executable integration checkpoint.
//!
//! This harness runs the standard-Rust reference broker, captures the durable
//! typed WAL it actually produced, and feeds every supported record through
//! the proof-erased K4-A4 append/recovery state.  The gated executions call
//! the kernel from the broker's real append/replay path.  This is still
//! integration evidence, not a Verus implementation-refinement theorem: the
//! Rust broker, byte WAL, filesystem, crash handling, and adapter remain
//! ordinary Rust.

extern crate k4_crash_recovery_control;
extern crate proveai_reference_broker;

use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;
use std::time::{SystemTime, UNIX_EPOCH};

use k4_crash_recovery_control::k4_a3_layer::k4_a2_layer::{
    KJournalRecord, KManifestBinding, KManifestCapability, KManifestConfig, KObservation, KPhase,
    KRetryClass,
};
use k4_crash_recovery_control::k4_a3_layer::{k4_a3_supported_exec, KUnknownReason};
use k4_crash_recovery_control::{
    k4_a4_begin_recovery, k4_a4_commit_after_wal, k4_a4_crash,
    k4_a4_durable_success_recovery_witness, k4_a4_finish_recovery, k4_a4_initial, k4_a4_preview,
    k4_a4_recovery_resumable_exec, k4_a4_resume_recovery, KRecoveryKernel, KRecoveryMode,
};
use proveai_reference_broker::evaluation::{
    run_submission_evaluation, EvaluationGateEvidence, EvaluationGateFactory,
};
use proveai_reference_broker::adapters::{
    DeduplicatedAdapter, IdempotentAdapter, UncontrolledAdapter,
};
use proveai_reference_broker::{
    AdmissionBinding, AppendGate, Broker, BrokerConfig, BrokerError, CapabilityId, CapabilitySpec,
    CrashPlan, CrashSite, DedupKey, Digest, GateError, JournalRecord, Observation, RequestId,
    RequestSpec, RetryClass, TerminalResult, UnknownReason, Value,
};

fn retry_class_to_k4(class: RetryClass) -> KRetryClass {
    match class {
        RetryClass::ReadOnly => KRetryClass::ReadOnly,
        RetryClass::Idempotent => KRetryClass::Idempotent,
        RetryClass::Deduplicated => KRetryClass::Deduplicated,
        RetryClass::Uncontrolled => KRetryClass::Uncontrolled,
    }
}

fn observation_to_k4(observation: Observation) -> KObservation {
    match observation {
        Observation::Success(Value(value)) => KObservation::Success { value },
        Observation::Failure => KObservation::Failure,
        Observation::Ambiguous => KObservation::Ambiguous,
        Observation::InvalidResult(Value(value)) => KObservation::InvalidResult { value },
    }
}

fn unknown_reason_to_k4(reason: UnknownReason) -> KUnknownReason {
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
            let (attempt_present, attempt) = match attempt {
                Some(attempt) => (true, attempt),
                None => (false, 0),
            };
            let (key_present, key) = key_fields(key);
            KJournalRecord::Unknown {
                request,
                attempt_present,
                attempt,
                reason: unknown_reason_to_k4(reason),
                digest,
                key_present,
                key,
                evidence_ref,
            }
        }
        JournalRecord::Revoke { .. } => return Err("K4-A3 does not support Revoke"),
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

/// The live append gate used by the integration runs.  Unlike the earlier
/// monitor, this object is called from `Broker::append` itself: a record must
/// pass the proof-erased K4-A4 preview before the byte WAL write, and the K4
/// state is advanced only after the WAL reports its durable LSN.
struct KernelGate {
    manifest: KManifestConfig,
    state: KRecoveryKernel,
    counters: Arc<GateCounters>,
}

impl KernelGate {
    fn new(config: &BrokerConfig) -> Self {
        Self::new_with_counters(config, Arc::new(GateCounters::default()))
    }

    fn new_with_counters(config: &BrokerConfig, counters: Arc<GateCounters>) -> Self {
        let manifest = k4_manifest(config);
        let state = k4_a4_initial(&manifest);
        counters.gates_created.fetch_add(1, Ordering::Relaxed);
        Self {
            manifest,
            state,
            counters,
        }
    }

    fn translate(record: JournalRecord) -> Result<KJournalRecord, GateError> {
        broker_record_to_k4(record).map_err(GateError)
    }
}

impl AppendGate for KernelGate {
    fn preview(&mut self, record: JournalRecord) -> Result<(), GateError> {
        let translated = Self::translate(record)?;
        if k4_a4_preview(&self.manifest, &mut self.state, translated) {
            self.counters.previews.fetch_add(1, Ordering::Relaxed);
            Ok(())
        } else {
            Err(GateError("K4-A4 rejected the append preview"))
        }
    }

    fn commit_after_wal(&mut self, record: JournalRecord, lsn: u64) -> Result<(), GateError> {
        let translated = Self::translate(record)?;
        let cut = k4_a4_commit_after_wal(&self.manifest, &mut self.state, translated)
            .ok_or(GateError("K4-A4 rejected the post-WAL commit"))?;
        if cut == lsn {
            self.counters.commits.fetch_add(1, Ordering::Relaxed);
            Ok(())
        } else {
            Err(GateError("K4-A4 returned a mismatched acknowledgement cut"))
        }
    }

    fn replay(&mut self, record: JournalRecord, lsn: u64) -> Result<(), GateError> {
        self.preview(record)?;
        self.commit_after_wal(record, lsn)?;
        self.counters.replays.fetch_add(1, Ordering::Relaxed);
        Ok(())
    }

    fn on_crash(&mut self) -> Result<(), GateError> {
        k4_a4_crash(&self.manifest, &mut self.state);
        Ok(())
    }

    fn begin_recovery(&mut self) -> Result<(), GateError> {
        // A newly constructed gate represents a restarted process.  Materialize
        // the restart cut before entering the verified recovery mode.
        if self.state.mode == KRecoveryMode::Online {
            k4_a4_crash(&self.manifest, &mut self.state);
        }
        if self.state.mode == KRecoveryMode::Crashed
            && !k4_a4_begin_recovery(&self.manifest, &mut self.state)
        {
            return Err(GateError("K4-A4 refused to enter recovery"));
        }
        self.counters
            .recoveries_started
            .fetch_add(1, Ordering::Relaxed);
        Ok(())
    }

    fn finish_recovery(&mut self) -> Result<bool, GateError> {
        let finished = k4_a4_finish_recovery(&self.manifest, &mut self.state);
        if finished {
            self.counters
                .recoveries_finished
                .fetch_add(1, Ordering::Relaxed);
        }
        Ok(finished)
    }

    fn resume_recovery(&mut self) -> Result<bool, GateError> {
        let resumed = k4_a4_resume_recovery(&self.manifest, &mut self.state);
        if resumed {
            self.counters
                .recoveries_resumed
                .fetch_add(1, Ordering::Relaxed);
        }
        Ok(resumed)
    }

    fn conservative_recovery(&self) -> bool {
        !k4_a4_recovery_resumable_exec(&self.manifest, &self.state)
    }
}

#[derive(Default)]
struct GateCounters {
    gates_created: AtomicU64,
    previews: AtomicU64,
    commits: AtomicU64,
    replays: AtomicU64,
    recoveries_started: AtomicU64,
    recoveries_finished: AtomicU64,
    recoveries_resumed: AtomicU64,
}

impl GateCounters {
    fn snapshot(&self) -> EvaluationGateEvidence {
        EvaluationGateEvidence {
            gates_created: self.gates_created.load(Ordering::Relaxed),
            previews: self.previews.load(Ordering::Relaxed),
            commits: self.commits.load(Ordering::Relaxed),
            replays: self.replays.load(Ordering::Relaxed),
            recoveries_started: self.recoveries_started.load(Ordering::Relaxed),
            recoveries_finished: self.recoveries_finished.load(Ordering::Relaxed),
            recoveries_resumed: self.recoveries_resumed.load(Ordering::Relaxed),
        }
    }
}

#[derive(Default)]
struct K4SubmissionGateFactory {
    counters: Arc<GateCounters>,
}

impl EvaluationGateFactory for K4SubmissionGateFactory {
    type Gate = KernelGate;

    fn profile_name(&self) -> &'static str {
        "k4-a4-required"
    }

    fn create_gate(&mut self, config: &BrokerConfig) -> Result<Self::Gate, GateError> {
        if config.admission_manifest.is_none() {
            return Err(GateError("K4-I1 requires an immutable admission manifest"));
        }
        Ok(KernelGate::new_with_counters(
            config,
            Arc::clone(&self.counters),
        ))
    }

    fn evidence(&self) -> EvaluationGateEvidence {
        self.counters.snapshot()
    }
}

fn open_kernel_broker(path: &Path, config: BrokerConfig) -> Result<Broker, BrokerError> {
    Broker::open_with_gate(path, config.clone(), KernelGate::new(&config))
}

fn remove_broker_files(path: &Path) {
    let _ = std::fs::remove_file(path);
    let mut sidecar = path.as_os_str().to_os_string();
    sidecar.push(".config");
    let _ = std::fs::remove_file(PathBuf::from(sidecar));
}

struct KernelMonitor {
    manifest: KManifestConfig,
    state: KRecoveryKernel,
    synced: usize,
}

impl KernelMonitor {
    fn new(config: &BrokerConfig) -> Self {
        let manifest = k4_manifest(config);
        let state = k4_a4_initial(&manifest);
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
                .expect("K4-I0 rejects broker records outside the K4-A4 theorem boundary");
            assert!(translated == self.state.core.journal[index]);
        }
        for (index, record) in records.iter().copied().enumerate().skip(self.synced) {
            let translated = broker_record_to_k4(record)
                .expect("K4-I0 rejects broker records outside the K4-A4 theorem boundary");
            assert!(k4_a3_supported_exec(&translated));
            let expected_lsn = u64::try_from(index + 1).expect("K4-I0 LSN fits u64");
            assert!(k4_a4_preview(&self.manifest, &mut self.state, translated));
            let cut = k4_a4_commit_after_wal(&self.manifest, &mut self.state, translated)
                .expect("K4-A4 commits the previewed WAL record");
            assert_eq!(cut, expected_lsn);
        }
        self.synced = records.len();
        assert_eq!(self.state.core.journal.len(), records.len());
        assert_eq!(self.state.core.ack_cuts.len(), records.len());
        for (index, cut) in self.state.core.ack_cuts.iter().copied().enumerate() {
            assert_eq!(cut, u64::try_from(index + 1).expect("K4-I0 cut fits u64"));
        }
    }

    fn assert_committed(&self, request: u64, attempt: usize, value: u64) {
        let entry = self
            .state
            .core
            .durable
            .requests
            .iter()
            .find(|entry| entry.request == request)
            .expect("K4-I0 kernel tracks the committed request");
        assert!(entry.phase == KPhase::Committed);
        assert_eq!(entry.outcomes.len(), attempt);
        assert!(matches!(
            entry.outcomes[attempt - 1],
            Some(KObservation::Success { value: observed }) if observed == value
        ));
    }

    fn assert_failed(&self, request: u64, attempt: usize) {
        let entry = self
            .state
            .core
            .durable
            .requests
            .iter()
            .find(|entry| entry.request == request)
            .expect("K4-I0 kernel tracks the failed request");
        assert!(entry.phase == KPhase::Failed);
        assert_eq!(entry.outcomes.len(), attempt);
        assert!(matches!(
            entry.outcomes[attempt - 1],
            Some(KObservation::Failure)
        ));
    }

    fn assert_unknown(&self, request: u64, attempts: usize, latest: Option<KObservation>) {
        let entry = self
            .state
            .core
            .durable
            .requests
            .iter()
            .find(|entry| entry.request == request)
            .expect("K4-I0 kernel tracks the unknown request");
        assert!(entry.phase == KPhase::Unknown);
        assert_eq!(entry.outcomes.len(), attempts);
        if attempts > 0 {
            assert!(entry.outcomes[attempts - 1] == latest);
        }
    }

    fn assert_budget(&self, capability: u64, remaining: u64) {
        let entry = self
            .state
            .core
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
    let mut broker = open_kernel_broker(path, config.clone()).expect("open deduplicated broker");
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
    let records = broker.wal_records().to_vec();
    drop(broker);
    let reopened = open_kernel_broker(path, config.clone()).expect("replay deduplicated broker");
    assert_eq!(
        reopened.terminal(RequestId(1)).expect("replayed terminal"),
        Some(TerminalResult::Committed {
            attempt: 1,
            value: Value(1),
        })
    );
    (config, records)
}

fn single_request_config(spec: RequestSpec) -> BrokerConfig {
    BrokerConfig {
        capabilities: vec![CapabilitySpec {
            id: CapabilityId(1),
            budget: 4,
        }],
        admission_manifest: Some(vec![AdmissionBinding {
            request: RequestId(1),
            capability: CapabilityId(1),
            spec,
        }]),
    }
}

fn run_idempotent_failure(path: &Path) -> usize {
    let spec = RequestSpec::idempotent(Digest(11));
    let config = single_request_config(spec);
    let mut broker = open_kernel_broker(path, config.clone()).expect("open failure broker");
    let request = broker
        .admit(CapabilityId(1), spec.digest)
        .expect("admit failure request");
    broker
        .prepare(request, spec)
        .expect("prepare failure request");
    let mut adapter = IdempotentAdapter::scripted([Observation::Failure]);
    assert_eq!(
        broker
            .run(request, RetryClass::Idempotent.max_attempts(), &mut adapter)
            .expect("run failure request"),
        TerminalResult::Failed { attempt: 1 }
    );
    let mut monitor = KernelMonitor::new(&config);
    monitor.sync(broker.wal_records());
    monitor.assert_failed(1, 1);
    monitor.assert_budget(1, 3);
    broker.wal_records().len()
}

fn run_uncontrolled_unknown(path: &Path, observation: Observation, reason: UnknownReason) -> usize {
    let spec = RequestSpec::uncontrolled(Digest(12));
    let config = single_request_config(spec);
    let mut broker = open_kernel_broker(path, config.clone()).expect("open uncontrolled broker");
    let request = broker
        .admit(CapabilityId(1), spec.digest)
        .expect("admit uncontrolled request");
    broker
        .prepare(request, spec)
        .expect("prepare uncontrolled request");
    let mut adapter = UncontrolledAdapter::scripted([observation]);
    assert_eq!(
        broker
            .run(
                request,
                RetryClass::Uncontrolled.max_attempts(),
                &mut adapter,
            )
            .expect("run uncontrolled request"),
        TerminalResult::Unknown {
            attempt: Some(1),
            reason,
        }
    );
    assert_eq!(adapter.effect_count(), 1);
    let mut monitor = KernelMonitor::new(&config);
    monitor.sync(broker.wal_records());
    monitor.assert_unknown(1, 1, Some(observation_to_k4(observation)));
    monitor.assert_budget(1, 3);
    broker.wal_records().len()
}

fn run_idempotent_exhaustion(path: &Path) -> usize {
    let spec = RequestSpec::idempotent(Digest(13));
    let config = single_request_config(spec);
    let mut broker = open_kernel_broker(path, config.clone()).expect("open exhaustion broker");
    let request = broker
        .admit(CapabilityId(1), spec.digest)
        .expect("admit exhaustion request");
    broker
        .prepare(request, spec)
        .expect("prepare exhaustion request");
    let mut adapter = IdempotentAdapter::scripted([
        Observation::Ambiguous,
        Observation::Ambiguous,
        Observation::Ambiguous,
    ]);
    assert_eq!(
        broker
            .run(request, RetryClass::Idempotent.max_attempts(), &mut adapter)
            .expect("run exhaustion request"),
        TerminalResult::Unknown {
            attempt: Some(3),
            reason: UnknownReason::Exhausted,
        }
    );
    let mut monitor = KernelMonitor::new(&config);
    monitor.sync(broker.wal_records());
    monitor.assert_unknown(1, 3, Some(KObservation::Ambiguous));
    broker.wal_records().len()
}

fn run_idempotent_nonconclusive_failure(path: &Path) -> usize {
    let spec = RequestSpec::idempotent(Digest(14));
    let config = single_request_config(spec);
    let mut broker = open_kernel_broker(path, config.clone()).expect("open nonconclusive broker");
    let request = broker
        .admit(CapabilityId(1), spec.digest)
        .expect("admit nonconclusive request");
    broker
        .prepare(request, spec)
        .expect("prepare nonconclusive request");
    let mut adapter = IdempotentAdapter::scripted([Observation::Ambiguous, Observation::Failure]);
    assert_eq!(
        broker
            .run(request, RetryClass::Idempotent.max_attempts(), &mut adapter)
            .expect("run nonconclusive request"),
        TerminalResult::Unknown {
            attempt: Some(2),
            reason: UnknownReason::NonConclusiveFailure,
        }
    );
    let mut monitor = KernelMonitor::new(&config);
    monitor.sync(broker.wal_records());
    monitor.assert_unknown(1, 2, Some(KObservation::Failure));
    broker.wal_records().len()
}

fn run_uncontrolled_restart(path: &Path) -> usize {
    let spec = RequestSpec::uncontrolled(Digest(15));
    let config = single_request_config(spec);
    let mut monitor = KernelMonitor::new(&config);
    let request;
    {
        let mut broker = Broker::open(path, config.clone()).expect("open restart broker");
        request = broker
            .admit(CapabilityId(1), spec.digest)
            .expect("admit restart request");
        broker
            .prepare(request, spec)
            .expect("prepare restart request");
        broker.set_crash_plan(Some(CrashPlan::once(CrashSite::AfterInvoke)));
        let mut adapter = UncontrolledAdapter::default();
        assert!(matches!(
            broker.run(
                request,
                RetryClass::Uncontrolled.max_attempts(),
                &mut adapter,
            ),
            Err(BrokerError::SimulatedCrash(CrashSite::AfterInvoke))
        ));
        assert_eq!(adapter.effect_count(), 1);
        monitor.sync(broker.wal_records());
    }

    let mut broker = Broker::open(path, config.clone()).expect("reopen restart broker");
    monitor.sync(broker.wal_records());
    let mut unused_adapter = UncontrolledAdapter::default();
    assert_eq!(
        broker
            .run(
                request,
                RetryClass::Uncontrolled.max_attempts(),
                &mut unused_adapter,
            )
            .expect("recover restart request"),
        TerminalResult::Unknown {
            attempt: Some(1),
            reason: UnknownReason::AmbiguousOutcome,
        }
    );
    assert_eq!(unused_adapter.effect_count(), 0);
    monitor.sync(broker.wal_records());
    monitor.assert_unknown(1, 1, Some(KObservation::Ambiguous));
    broker.wal_records().len()
}

fn run_kernel_gated_restart(path: &Path) -> usize {
    let spec = RequestSpec::uncontrolled(Digest(17));
    let config = single_request_config(spec);
    let mut monitor = KernelMonitor::new(&config);
    let request;
    {
        let mut broker = open_kernel_broker(path, config.clone()).expect("open gated broker");
        request = broker
            .admit(CapabilityId(1), spec.digest)
            .expect("admit gated request");
        broker
            .prepare(request, spec)
            .expect("prepare gated request");
        broker.set_crash_plan(Some(CrashPlan::once(CrashSite::AfterInvoke)));
        let mut adapter = UncontrolledAdapter::default();
        assert!(matches!(
            broker.run(
                request,
                RetryClass::Uncontrolled.max_attempts(),
                &mut adapter,
            ),
            Err(BrokerError::SimulatedCrash(CrashSite::AfterInvoke))
        ));
        assert_eq!(adapter.effect_count(), 1);
        monitor.sync(broker.wal_records());
        assert_eq!(broker.wal_records().len(), 4);
    }

    let mut broker = open_kernel_broker(path, config.clone()).expect("reopen gated broker");
    monitor.sync(broker.wal_records());
    let mut adapter = UncontrolledAdapter::default();
    assert_eq!(
        broker
            .run(
                request,
                RetryClass::Uncontrolled.max_attempts(),
                &mut adapter,
            )
            .expect("recover gated request"),
        TerminalResult::Unknown {
            attempt: Some(1),
            reason: UnknownReason::Recovery,
        }
    );
    assert_eq!(adapter.effect_count(), 0);
    monitor.sync(broker.wal_records());
    monitor.assert_unknown(1, 1, None);
    assert_eq!(broker.wal_records().len(), 5);
    broker.wal_records().len()
}

fn run_kernel_gated_durable_success(path: &Path) -> usize {
    let spec = RequestSpec::idempotent(Digest(18));
    let config = single_request_config(spec);
    let request;
    {
        let mut broker =
            open_kernel_broker(path, config.clone()).expect("open durable-success gated broker");
        request = broker
            .admit(CapabilityId(1), spec.digest)
            .expect("admit durable-success request");
        broker
            .prepare(request, spec)
            .expect("prepare durable-success request");
        broker.set_crash_plan(Some(CrashPlan::once(CrashSite::AfterOutcome)));
        let mut adapter = IdempotentAdapter::default();
        assert!(matches!(
            broker.run(request, RetryClass::Idempotent.max_attempts(), &mut adapter,),
            Err(BrokerError::SimulatedCrash(CrashSite::AfterOutcome))
        ));
        assert_eq!(adapter.mutation_count(), 1);
        assert_eq!(broker.wal_records().len(), 5);
        assert!(matches!(
            broker.wal_records().last(),
            Some(JournalRecord::Outcome {
                observation: Observation::Success(Value(1)),
                ..
            })
        ));
    }

    let mut broker =
        open_kernel_broker(path, config.clone()).expect("reopen durable-success gated broker");
    let mut adapter = IdempotentAdapter::default();
    assert_eq!(
        broker
            .run(request, RetryClass::Idempotent.max_attempts(), &mut adapter,)
            .expect("commit durable success through K4 recovery"),
        TerminalResult::Committed {
            attempt: 1,
            value: Value(1),
        }
    );
    assert_eq!(adapter.mutation_count(), 0);
    assert_eq!(broker.wal_records().len(), 6);
    assert!(matches!(
        broker.wal_records().last(),
        Some(JournalRecord::Commit {
            attempt: 1,
            value: Value(1),
            outcome_ref: 5,
            ..
        })
    ));

    let mut monitor = KernelMonitor::new(&config);
    monitor.sync(broker.wal_records());
    monitor.assert_committed(1, 1, 1);
    broker.wal_records().len()
}

fn run_kernel_control_smoke() {
    let spec = RequestSpec::uncontrolled(Digest(16));
    let config = single_request_config(spec);
    let manifest = k4_manifest(&config);
    let mut state = k4_a4_initial(&manifest);
    k4_a4_crash(&manifest, &mut state);
    assert!(k4_a4_begin_recovery(&manifest, &mut state));
    assert!(k4_a4_finish_recovery(&manifest, &mut state));
    assert!(state.mode == KRecoveryMode::Online);
    assert!(state.core.journal.is_empty());
    assert!(state.core.ack_cuts.is_empty());

    let (_witness_config, witness_state) = k4_a4_durable_success_recovery_witness();
    assert!(witness_state.mode == KRecoveryMode::Online);
    assert_eq!(witness_state.core.journal.len(), 6);
    assert_eq!(witness_state.core.ack_cuts.len(), 6);
}

fn main() {
    let serial = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("system time is after the Unix epoch")
        .as_nanos();
    let root = std::env::temp_dir();
    let idempotent_path = root.join(format!("proveai-k4-i0-idempotent-{serial}.wal"));
    let deduplicated_path = root.join(format!("proveai-k4-i0-deduplicated-{serial}.wal"));
    let failure_path = root.join(format!("proveai-k4-i0-failure-{serial}.wal"));
    let ambiguous_path = root.join(format!("proveai-k4-i0-ambiguous-{serial}.wal"));
    let invalid_path = root.join(format!("proveai-k4-i0-invalid-{serial}.wal"));
    let exhausted_path = root.join(format!("proveai-k4-i0-exhausted-{serial}.wal"));
    let nonconclusive_path = root.join(format!("proveai-k4-i0-nonconclusive-{serial}.wal"));
    let restart_path = root.join(format!("proveai-k4-i0-restart-{serial}.wal"));
    let gated_restart_path = root.join(format!("proveai-k4-i0-gated-restart-{serial}.wal"));
    let gated_success_path = root.join(format!("proveai-k4-i0-gated-success-{serial}.wal"));

    assert!(broker_record_to_k4(JournalRecord::Revoke {
        capability: CapabilityId(1),
    })
    .is_err());
    run_kernel_control_smoke();
    let (idempotent_config, idempotent_records) = run_idempotent_crash_retry(&idempotent_path);
    verify_records(&idempotent_config, &idempotent_records, 2, 1);
    assert_eq!(idempotent_records.len(), 8);
    remove_broker_files(&idempotent_path);

    let (deduplicated_config, deduplicated_records) = run_deduplicated(&deduplicated_path);
    verify_records(&deduplicated_config, &deduplicated_records, 1, 1);
    assert_eq!(deduplicated_records.len(), 6);
    remove_broker_files(&deduplicated_path);

    let failure_records = run_idempotent_failure(&failure_path);
    assert_eq!(failure_records, 6);
    remove_broker_files(&failure_path);

    let ambiguous_records = run_uncontrolled_unknown(
        &ambiguous_path,
        Observation::Ambiguous,
        UnknownReason::AmbiguousOutcome,
    );
    assert_eq!(ambiguous_records, 6);
    remove_broker_files(&ambiguous_path);

    let invalid_records = run_uncontrolled_unknown(
        &invalid_path,
        Observation::InvalidResult(Value(99)),
        UnknownReason::InvalidResult,
    );
    assert_eq!(invalid_records, 6);
    remove_broker_files(&invalid_path);

    let exhausted_records = run_idempotent_exhaustion(&exhausted_path);
    assert_eq!(exhausted_records, 10);
    remove_broker_files(&exhausted_path);

    let nonconclusive_records = run_idempotent_nonconclusive_failure(&nonconclusive_path);
    assert_eq!(nonconclusive_records, 8);
    remove_broker_files(&nonconclusive_path);

    let restart_records = run_uncontrolled_restart(&restart_path);
    assert_eq!(restart_records, 6);
    remove_broker_files(&restart_path);

    let gated_restart_records = run_kernel_gated_restart(&gated_restart_path);
    assert_eq!(gated_restart_records, 5);
    remove_broker_files(&gated_restart_path);

    let gated_success_records = run_kernel_gated_durable_success(&gated_success_path);
    assert_eq!(gated_success_records, 6);
    remove_broker_files(&gated_success_path);

    let submission_iterations = std::env::var("PROVEAI_K4_I1_ITERATIONS")
        .ok()
        .map(|value| value.parse::<u64>().expect("valid K4-I1 iteration count"))
        .unwrap_or(10);
    let mut submission_factory = K4SubmissionGateFactory::default();
    let submission = run_submission_evaluation(submission_iterations, &mut submission_factory)
        .expect("K4-I1 submission evaluation must stay inside the K4 gate");
    assert!(submission.evaluation.rq1.all_passed);
    assert_eq!(submission.evaluation.rq1.cases.len(), 21);
    if let Ok(report_path) = std::env::var("PROVEAI_K4_I1_REPORT") {
        let report_path = PathBuf::from(report_path);
        if let Some(parent) = report_path.parent() {
            std::fs::create_dir_all(parent).expect("create K4-I1 report directory");
        }
        std::fs::write(&report_path, submission.to_json_pretty())
            .expect("write K4-I1 submission report");
    }

    println!(
        "K4-I0 broker-to-K4-A4 integration passed: commit={}/{}, fail={}, unknown={}/{}/{}/{}, restart={}/{}, recovery-commit={} records; control=online",
        idempotent_records.len(),
        deduplicated_records.len(),
        failure_records,
        ambiguous_records,
        invalid_records,
        exhausted_records,
        nonconclusive_records,
        restart_records,
        gated_restart_records,
        gated_success_records,
    );
    println!(
        "K4-I1 submission profile passed: rq1=21/21; iterations={}; opens={}; gates={}; preview/commit={}/{}; replays={}; recovery=finished:{}+resumed:{}",
        submission_iterations,
        submission.broker_opens,
        submission.gate.gates_created,
        submission.gate.previews,
        submission.gate.commits,
        submission.gate.replays,
        submission.gate.recoveries_finished,
        submission.gate.recoveries_resumed,
    );
}
