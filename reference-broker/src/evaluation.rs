use std::fmt;
use std::fmt::Write as _;
use std::fs::{File, OpenOptions};
use std::hint::black_box;
use std::io::{Read, Write};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{Instant, SystemTime, UNIX_EPOCH};

use crate::adapter::{Adapter, Delivery};
use crate::adapters::{DeduplicatedAdapter, IdempotentAdapter, UncontrolledAdapter};
use crate::broker::{Broker, BrokerConfig, BrokerError, CapabilitySpec};
use crate::fault::{CrashPlan, CrashSite};
use crate::model::{
    CapabilityId, DedupKey, Digest, Invocation, JournalRecord, Observation, Phase, RequestId,
    RequestSpec, RetryClass, TerminalResult, UnknownReason, Value,
};

pub const REPORT_SCHEMA_VERSION: u64 = 1;
const CAPABILITY: CapabilityId = CapabilityId(7);
const MAX_ATTEMPTS: u64 = 3;
const CRASH_SITES: [CrashSite; 7] = [
    CrashSite::AfterAuthorize,
    CrashSite::AfterPrepare,
    CrashSite::AfterArm,
    CrashSite::AfterStart,
    CrashSite::AfterInvoke,
    CrashSite::AfterOutcome,
    CrashSite::AfterTerminal,
];
const ADAPTER_CLASSES: [RetryClass; 3] = [
    RetryClass::Uncontrolled,
    RetryClass::Idempotent,
    RetryClass::Deduplicated,
];
static NEXT_WORKSPACE: AtomicU64 = AtomicU64::new(1);

#[derive(Debug)]
pub enum EvaluationError {
    Broker(BrokerError),
    Io(std::io::Error),
    InvalidArgument(&'static str),
    Invariant(&'static str),
}

impl fmt::Display for EvaluationError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Broker(error) => error.fmt(formatter),
            Self::Io(error) => error.fmt(formatter),
            Self::InvalidArgument(detail) => {
                write!(formatter, "invalid evaluation argument: {detail}")
            }
            Self::Invariant(detail) => write!(formatter, "evaluation invariant failed: {detail}"),
        }
    }
}

impl std::error::Error for EvaluationError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Broker(error) => Some(error),
            Self::Io(error) => Some(error),
            _ => None,
        }
    }
}

impl From<BrokerError> for EvaluationError {
    fn from(error: BrokerError) -> Self {
        Self::Broker(error)
    }
}

impl From<std::io::Error> for EvaluationError {
    fn from(error: std::io::Error) -> Self {
        Self::Io(error)
    }
}

#[derive(Clone, Debug)]
pub struct EvaluationReport {
    pub generated_unix_seconds: u64,
    pub iterations: u64,
    pub retry_iterations: u64,
    pub environment: Environment,
    pub rq1: Rq1Report,
    pub rq2: Rq2Report,
}

#[derive(Clone, Debug)]
pub struct Environment {
    pub hostname: String,
    pub target: String,
    pub rustc: String,
    pub source_revision: String,
    pub build_profile: &'static str,
    pub package_version: &'static str,
    pub logical_cpus: u64,
}

#[derive(Clone, Debug)]
pub struct Rq1Report {
    pub all_passed: bool,
    pub stale_delivery_rejected: bool,
    pub cases: Vec<CrashCaseResult>,
}

#[derive(Clone, Debug)]
pub struct CrashCaseResult {
    pub adapter: &'static str,
    pub crash_site: &'static str,
    pub terminal: &'static str,
    pub terminal_attempt: u64,
    pub physical_invocations: u64,
    pub abstract_effects: u64,
    pub terminal_records: u64,
    pub authorization_ancestry: bool,
    pub retry_bound_respected: bool,
    pub effect_oracle_satisfied: bool,
    pub passed: bool,
}

#[derive(Clone, Debug)]
pub struct Rq2Report {
    pub mediated: WorkloadMetrics,
    pub direct: WorkloadMetrics,
    pub journaled_at_least_once: WorkloadMetrics,
    pub retry_scenarios: Vec<RetryMetrics>,
}

#[derive(Clone, Debug)]
pub struct WorkloadMetrics {
    pub requests: u64,
    pub duration_ns: u64,
    pub throughput_requests_per_second: f64,
    pub latency: LatencyMetrics,
    pub wal_bytes: u64,
    pub flushes: u64,
    pub recovery_ns: u64,
    pub physical_invocations: u64,
    pub abstract_effects: u64,
}

#[derive(Clone, Copy, Debug, Default)]
pub struct LatencyMetrics {
    pub mean_ns: u64,
    pub p50_ns: u64,
    pub p95_ns: u64,
    pub p99_ns: u64,
}

#[derive(Clone, Debug)]
pub struct RetryMetrics {
    pub mechanism: &'static str,
    pub requests: u64,
    pub duration_ns: u64,
    pub latency: LatencyMetrics,
    pub physical_invocations: u64,
    pub abstract_effects: u64,
    pub extra_invocations: u64,
    pub extra_effects: u64,
    pub wal_bytes: u64,
    pub flushes: u64,
}

pub fn run_evaluation(iterations: u64) -> Result<EvaluationReport, EvaluationError> {
    if iterations == 0 {
        return Err(EvaluationError::InvalidArgument(
            "iterations must be positive",
        ));
    }
    let workspace = EvaluationWorkspace::new()?;
    let rq1 = run_rq1(&workspace)?;
    if !rq1.all_passed {
        return Err(EvaluationError::Invariant("an RQ1 case did not pass"));
    }
    let retry_iterations = (iterations / 10).clamp(1, 100);
    let rq2 = Rq2Report {
        mediated: benchmark_mediated(&workspace, iterations)?,
        direct: benchmark_direct(iterations),
        journaled_at_least_once: benchmark_journaled(&workspace, iterations)?,
        retry_scenarios: vec![
            benchmark_retry_mediated(&workspace, retry_iterations, RetryClass::Idempotent)?,
            benchmark_retry_mediated(&workspace, retry_iterations, RetryClass::Deduplicated)?,
            benchmark_retry_journaled(&workspace, retry_iterations)?,
        ],
    };
    Ok(EvaluationReport {
        generated_unix_seconds: SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map_err(|_| EvaluationError::Invariant("system clock precedes Unix epoch"))?
            .as_secs(),
        iterations,
        retry_iterations,
        environment: environment(),
        rq1,
        rq2,
    })
}

fn run_rq1(workspace: &EvaluationWorkspace) -> Result<Rq1Report, EvaluationError> {
    let mut cases = Vec::with_capacity(CRASH_SITES.len() * ADAPTER_CLASSES.len());
    for class in ADAPTER_CLASSES {
        for site in CRASH_SITES {
            cases.push(run_crash_case(workspace, class, site)?);
        }
    }
    let stale_delivery_rejected = check_stale_delivery(workspace)?;
    let all_passed = stale_delivery_rejected && cases.iter().all(|case| case.passed);
    Ok(Rq1Report {
        all_passed,
        stale_delivery_rejected,
        cases,
    })
}

fn run_crash_case(
    workspace: &EvaluationWorkspace,
    class: RetryClass,
    site: CrashSite,
) -> Result<CrashCaseResult, EvaluationError> {
    let path = workspace.path(&format!(
        "rq1-{}-{}.wal",
        class_name(class),
        site_name(site)
    ));
    let spec = request_spec(class, 1);
    let request = RequestId(1);
    let mut adapter = ExampleAdapter::new(class);
    let mut broker = Broker::open(&path, broker_config(1))?;

    if site == CrashSite::AfterAuthorize {
        broker.set_crash_plan(Some(CrashPlan::once(site)));
        expect_crash(broker.admit(CAPABILITY, spec.digest), site)?;
        drop(broker);
        broker = Broker::open(&path, broker_config(1))?;
    } else if broker.admit(CAPABILITY, spec.digest)? != request {
        return Err(EvaluationError::Invariant("generated request ID changed"));
    }

    if site == CrashSite::AfterPrepare {
        broker.set_crash_plan(Some(CrashPlan::once(site)));
        expect_crash(broker.prepare(request, spec), site)?;
        drop(broker);
        broker = Broker::open(&path, broker_config(1))?;
    } else if broker.phase(request)? == Phase::Authorized {
        broker.prepare(request, spec)?;
    }

    if !matches!(site, CrashSite::AfterAuthorize | CrashSite::AfterPrepare) {
        broker.set_crash_plan(Some(CrashPlan::once(site)));
        expect_crash(broker.run(request, MAX_ATTEMPTS, &mut adapter), site)?;
        drop(broker);
        broker = Broker::open(&path, broker_config(1))?;
    }

    let terminal = broker.run(request, MAX_ATTEMPTS, &mut adapter)?;
    let records = broker.wal_records();
    let terminal_records = records
        .iter()
        .filter(|record| is_terminal_record(record))
        .count() as u64;
    let terminal_attempt = terminal_attempt(terminal);
    let authorization_ancestry = audit_authorization_ancestry(records);
    let retry_bound_respected = terminal_attempt <= MAX_ATTEMPTS;
    let effect_oracle_satisfied = adapter.effect_oracle(site, terminal);
    let terminal_shape_satisfied = expected_terminal(class, site, terminal);
    let passed = terminal_records == 1
        && authorization_ancestry
        && retry_bound_respected
        && effect_oracle_satisfied
        && terminal_shape_satisfied;
    Ok(CrashCaseResult {
        adapter: class_name(class),
        crash_site: site_name(site),
        terminal: terminal_name(terminal),
        terminal_attempt,
        physical_invocations: adapter.invocations(),
        abstract_effects: adapter.effects(),
        terminal_records,
        authorization_ancestry,
        retry_bound_respected,
        effect_oracle_satisfied,
        passed,
    })
}

fn check_stale_delivery(workspace: &EvaluationWorkspace) -> Result<bool, EvaluationError> {
    let path = workspace.path("rq1-stale-delivery.wal");
    let spec = request_spec(RetryClass::Idempotent, 1);
    let mut broker = Broker::open(path, broker_config(1))?;
    let request = broker.admit(CAPABILITY, spec.digest)?;
    broker.prepare(request, spec)?;
    let first = broker.begin_attempt(request)?;
    let no_terminal = broker.accept_delivery(Delivery {
        invocation: first.id,
        observation: Observation::Ambiguous,
    })?;
    let second = broker.begin_attempt(request)?;
    let records_before = broker.wal_records().len();
    let stale = broker.accept_delivery(Delivery {
        invocation: first.id,
        observation: Observation::Success(Value(99)),
    });
    Ok(no_terminal.is_none()
        && first.id != second.id
        && matches!(stale, Err(BrokerError::StaleDelivery { .. }))
        && broker.wal_records().len() == records_before
        && broker.active_invocation() == Some(second))
}

fn expect_crash<T>(result: Result<T, BrokerError>, site: CrashSite) -> Result<(), EvaluationError> {
    match result {
        Err(BrokerError::SimulatedCrash(actual)) if actual == site => Ok(()),
        Err(error) => Err(EvaluationError::Broker(error)),
        Ok(_) => Err(EvaluationError::Invariant(
            "configured crash site did not fire",
        )),
    }
}

fn expected_terminal(class: RetryClass, site: CrashSite, terminal: TerminalResult) -> bool {
    if class == RetryClass::Uncontrolled
        && matches!(site, CrashSite::AfterStart | CrashSite::AfterInvoke)
    {
        matches!(
            terminal,
            TerminalResult::Unknown {
                attempt: Some(1),
                reason: UnknownReason::AmbiguousOutcome
            }
        )
    } else {
        matches!(terminal, TerminalResult::Committed { .. })
    }
}

fn audit_authorization_ancestry(records: &[JournalRecord]) -> bool {
    records.iter().enumerate().all(|(index, record)| {
        let JournalRecord::Start {
            request,
            digest,
            key,
            arm_ref,
            ..
        } = record
        else {
            return true;
        };
        let Some(JournalRecord::Arm {
            request: arm_request,
            digest: arm_digest,
            key: arm_key,
            prepare_ref,
        }) = record_at(records, *arm_ref)
        else {
            return false;
        };
        let Some(JournalRecord::Prepare {
            request: prepare_request,
            digest: prepare_digest,
            key: prepare_key,
            auth_ref,
            ..
        }) = record_at(records, *prepare_ref)
        else {
            return false;
        };
        let Some(JournalRecord::Authorize {
            request: auth_request,
            capability,
            digest: auth_digest,
        }) = record_at(records, *auth_ref)
        else {
            return false;
        };
        *arm_ref <= index as u64
            && *request == *arm_request
            && *request == *prepare_request
            && *request == *auth_request
            && *digest == *arm_digest
            && *digest == *prepare_digest
            && *digest == *auth_digest
            && *key == *arm_key
            && *key == *prepare_key
            && *capability == CAPABILITY
    })
}

fn record_at(records: &[JournalRecord], lsn: u64) -> Option<&JournalRecord> {
    usize::try_from(lsn.checked_sub(1)?)
        .ok()
        .and_then(|index| records.get(index))
}

fn is_terminal_record(record: &JournalRecord) -> bool {
    matches!(
        record,
        JournalRecord::Commit { .. } | JournalRecord::Fail { .. } | JournalRecord::Unknown { .. }
    )
}

fn terminal_attempt(terminal: TerminalResult) -> u64 {
    match terminal {
        TerminalResult::Committed { attempt, .. } | TerminalResult::Failed { attempt } => attempt,
        TerminalResult::Unknown { attempt, .. } => attempt.unwrap_or(0),
    }
}

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
            RetryClass::ReadOnly => unreachable!("RQ1 uses the three M4 adapter classes"),
        }
    }

    fn invocations(&self) -> u64 {
        match self {
            Self::Uncontrolled(adapter) => adapter.effect_count(),
            Self::Idempotent(adapter) => adapter.invocation_count(),
            Self::Deduplicated(adapter) => adapter.invocation_count(),
        }
    }

    fn effects(&self) -> u64 {
        match self {
            Self::Uncontrolled(adapter) => adapter.effect_count(),
            Self::Idempotent(adapter) => adapter.mutation_count(),
            Self::Deduplicated(adapter) => adapter.mutation_count(),
        }
    }

    fn effect_oracle(&self, site: CrashSite, terminal: TerminalResult) -> bool {
        match self {
            Self::Uncontrolled(_) => {
                let expected = u64::from(site != CrashSite::AfterStart);
                self.effects() == expected
                    && if matches!(site, CrashSite::AfterStart | CrashSite::AfterInvoke) {
                        matches!(terminal, TerminalResult::Unknown { .. })
                    } else {
                        matches!(terminal, TerminalResult::Committed { .. })
                    }
            }
            Self::Idempotent(_) | Self::Deduplicated(_) => {
                self.effects() == 1 && matches!(terminal, TerminalResult::Committed { .. })
            }
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

    fn invoke(&mut self, invocation: Invocation) -> Delivery {
        match self {
            Self::Uncontrolled(adapter) => adapter.invoke(invocation),
            Self::Idempotent(adapter) => adapter.invoke(invocation),
            Self::Deduplicated(adapter) => adapter.invoke(invocation),
        }
    }
}

fn benchmark_mediated(
    workspace: &EvaluationWorkspace,
    iterations: u64,
) -> Result<WorkloadMetrics, EvaluationError> {
    let path = workspace.path("rq2-mediated.wal");
    let mut broker = Broker::open(&path, broker_config(iterations))?;
    let mut adapter = UncontrolledAdapter::default();
    let mut latencies = Vec::with_capacity(capacity(iterations)?);
    let total_start = Instant::now();
    for index in 0..iterations {
        let request_start = Instant::now();
        let spec = RequestSpec::uncontrolled(Digest(10_000u64.saturating_add(index)));
        let request = broker.admit(CAPABILITY, spec.digest)?;
        broker.prepare(request, spec)?;
        let terminal = broker.run(request, 1, &mut adapter)?;
        if !matches!(terminal, TerminalResult::Committed { attempt: 1, .. }) {
            return Err(EvaluationError::Invariant(
                "mediated workload did not commit on attempt one",
            ));
        }
        latencies.push(elapsed_ns(request_start));
    }
    let duration_ns = elapsed_ns(total_start);
    let wal_metrics = broker.wal_metrics();
    let physical_invocations = adapter.effect_count();
    drop(broker);
    let recovery_start = Instant::now();
    let recovered = Broker::open(&path, broker_config(iterations))?;
    let recovery_ns = elapsed_ns(recovery_start);
    if recovered.request_ids().len() != capacity(iterations)? {
        return Err(EvaluationError::Invariant(
            "mediated recovery lost requests",
        ));
    }
    Ok(WorkloadMetrics {
        requests: iterations,
        duration_ns,
        throughput_requests_per_second: throughput(iterations, duration_ns),
        latency: latency_metrics(&mut latencies),
        wal_bytes: wal_metrics.bytes,
        flushes: wal_metrics.flushes,
        recovery_ns,
        physical_invocations,
        abstract_effects: adapter.effect_count(),
    })
}

fn benchmark_direct(iterations: u64) -> WorkloadMetrics {
    let mut tool = RawTool::default();
    let mut latencies = Vec::with_capacity(usize::try_from(iterations).unwrap_or(0));
    let total_start = Instant::now();
    for index in 0..iterations {
        let request_start = Instant::now();
        black_box(tool.invoke(black_box(index)));
        latencies.push(elapsed_ns(request_start));
    }
    let duration_ns = elapsed_ns(total_start);
    WorkloadMetrics {
        requests: iterations,
        duration_ns,
        throughput_requests_per_second: throughput(iterations, duration_ns),
        latency: latency_metrics(&mut latencies),
        wal_bytes: 0,
        flushes: 0,
        recovery_ns: 0,
        physical_invocations: tool.effects,
        abstract_effects: tool.effects,
    }
}

fn benchmark_journaled(
    workspace: &EvaluationWorkspace,
    iterations: u64,
) -> Result<WorkloadMetrics, EvaluationError> {
    let path = workspace.path("rq2-journaled-at-least-once.wal");
    let mut journal = AtLeastOnceJournal::create(&path)?;
    let mut tool = RawTool::default();
    let mut latencies = Vec::with_capacity(capacity(iterations)?);
    let total_start = Instant::now();
    for request in 1..=iterations {
        let request_start = Instant::now();
        journal.append(1, request, 1)?;
        black_box(tool.invoke(black_box(request)));
        journal.append(3, request, 1)?;
        latencies.push(elapsed_ns(request_start));
    }
    let duration_ns = elapsed_ns(total_start);
    let wal_bytes = journal.bytes;
    let flushes = journal.flushes;
    drop(journal);
    let recovery_start = Instant::now();
    let recovered_entries = AtLeastOnceJournal::recover(&path)?;
    let recovery_ns = elapsed_ns(recovery_start);
    if recovered_entries != iterations.saturating_mul(2) {
        return Err(EvaluationError::Invariant(
            "journaled baseline recovery lost entries",
        ));
    }
    Ok(WorkloadMetrics {
        requests: iterations,
        duration_ns,
        throughput_requests_per_second: throughput(iterations, duration_ns),
        latency: latency_metrics(&mut latencies),
        wal_bytes,
        flushes,
        recovery_ns,
        physical_invocations: tool.effects,
        abstract_effects: tool.effects,
    })
}

fn benchmark_retry_mediated(
    workspace: &EvaluationWorkspace,
    iterations: u64,
    class: RetryClass,
) -> Result<RetryMetrics, EvaluationError> {
    let mechanism = match class {
        RetryClass::Idempotent => "mediated_idempotent",
        RetryClass::Deduplicated => "mediated_deduplicated",
        _ => {
            return Err(EvaluationError::InvalidArgument(
                "retry benchmark requires a retry-safe class",
            ));
        }
    };
    let path = workspace.path(&format!("rq2-{mechanism}.wal"));
    let mut broker = Broker::open(path, broker_config(iterations))?;
    let mut latencies = Vec::with_capacity(capacity(iterations)?);
    let mut physical_invocations = 0u64;
    let mut abstract_effects = 0u64;
    let total_start = Instant::now();
    for index in 0..iterations {
        let request_start = Instant::now();
        let spec = request_spec(class, 100_000u64.saturating_add(index));
        let request = broker.admit(CAPABILITY, spec.digest)?;
        broker.prepare(request, spec)?;
        let terminal = match class {
            RetryClass::Idempotent => {
                let mut adapter = IdempotentAdapter::scripted([Observation::Ambiguous]);
                let terminal = broker.run(request, 2, &mut adapter)?;
                physical_invocations =
                    physical_invocations.saturating_add(adapter.invocation_count());
                abstract_effects = abstract_effects.saturating_add(adapter.mutation_count());
                terminal
            }
            RetryClass::Deduplicated => {
                let mut adapter = DeduplicatedAdapter::scripted([Observation::Ambiguous]);
                let terminal = broker.run(request, 2, &mut adapter)?;
                physical_invocations =
                    physical_invocations.saturating_add(adapter.invocation_count());
                abstract_effects = abstract_effects.saturating_add(adapter.mutation_count());
                terminal
            }
            _ => unreachable!("class checked before benchmark"),
        };
        if !matches!(terminal, TerminalResult::Committed { attempt: 2, .. }) {
            return Err(EvaluationError::Invariant(
                "retry-safe workload did not commit on attempt two",
            ));
        }
        latencies.push(elapsed_ns(request_start));
    }
    let duration_ns = elapsed_ns(total_start);
    let metrics = broker.wal_metrics();
    Ok(RetryMetrics {
        mechanism,
        requests: iterations,
        duration_ns,
        latency: latency_metrics(&mut latencies),
        physical_invocations,
        abstract_effects,
        extra_invocations: physical_invocations.saturating_sub(iterations),
        extra_effects: abstract_effects.saturating_sub(iterations),
        wal_bytes: metrics.bytes,
        flushes: metrics.flushes,
    })
}

fn benchmark_retry_journaled(
    workspace: &EvaluationWorkspace,
    iterations: u64,
) -> Result<RetryMetrics, EvaluationError> {
    let path = workspace.path("rq2-journaled-retry.wal");
    let mut journal = AtLeastOnceJournal::create(path)?;
    let mut tool = RawTool::default();
    let mut latencies = Vec::with_capacity(capacity(iterations)?);
    let total_start = Instant::now();
    for request in 1..=iterations {
        let request_start = Instant::now();
        journal.append(1, request, 1)?;
        black_box(tool.invoke(black_box(request)));
        journal.append(2, request, 1)?;
        journal.append(1, request, 2)?;
        black_box(tool.invoke(black_box(request)));
        journal.append(3, request, 2)?;
        latencies.push(elapsed_ns(request_start));
    }
    let duration_ns = elapsed_ns(total_start);
    Ok(RetryMetrics {
        mechanism: "journaled_at_least_once",
        requests: iterations,
        duration_ns,
        latency: latency_metrics(&mut latencies),
        physical_invocations: tool.effects,
        abstract_effects: tool.effects,
        extra_invocations: tool.effects.saturating_sub(iterations),
        extra_effects: tool.effects.saturating_sub(iterations),
        wal_bytes: journal.bytes,
        flushes: journal.flushes,
    })
}

#[derive(Default)]
struct RawTool {
    effects: u64,
}

impl RawTool {
    fn invoke(&mut self, input: u64) -> u64 {
        self.effects = self.effects.saturating_add(1);
        input ^ self.effects
    }
}

struct AtLeastOnceJournal {
    file: File,
    bytes: u64,
    flushes: u64,
}

impl AtLeastOnceJournal {
    fn create(path: impl AsRef<Path>) -> Result<Self, EvaluationError> {
        let file = OpenOptions::new()
            .create(true)
            .truncate(true)
            .write(true)
            .open(path)?;
        Ok(Self {
            file,
            bytes: 0,
            flushes: 0,
        })
    }

    fn append(&mut self, kind: u8, request: u64, attempt: u64) -> Result<(), EvaluationError> {
        let mut entry = [0u8; 21];
        entry[..4].copy_from_slice(b"ALO1");
        entry[4] = kind;
        entry[5..13].copy_from_slice(&request.to_le_bytes());
        entry[13..21].copy_from_slice(&attempt.to_le_bytes());
        self.file.write_all(&entry)?;
        self.file.flush()?;
        self.file.sync_data()?;
        self.bytes = self.bytes.saturating_add(entry.len() as u64);
        self.flushes = self.flushes.saturating_add(1);
        Ok(())
    }

    fn recover(path: impl AsRef<Path>) -> Result<u64, EvaluationError> {
        let mut file = File::open(path)?;
        let mut bytes = Vec::new();
        file.read_to_end(&mut bytes)?;
        let mut chunks = bytes.chunks_exact(21);
        let valid = chunks.all(|entry| entry[..4] == *b"ALO1" && matches!(entry[4], 1..=3));
        if !valid || !chunks.remainder().is_empty() {
            return Err(EvaluationError::Invariant(
                "journaled baseline contains an invalid entry",
            ));
        }
        Ok((bytes.len() / 21) as u64)
    }
}

fn latency_metrics(latencies: &mut [u64]) -> LatencyMetrics {
    if latencies.is_empty() {
        return LatencyMetrics::default();
    }
    latencies.sort_unstable();
    let sum = latencies.iter().fold(0u128, |total, value| {
        total.saturating_add(u128::from(*value))
    });
    LatencyMetrics {
        mean_ns: u64::try_from(sum / latencies.len() as u128).unwrap_or(u64::MAX),
        p50_ns: percentile(latencies, 50),
        p95_ns: percentile(latencies, 95),
        p99_ns: percentile(latencies, 99),
    }
}

fn percentile(sorted: &[u64], percentile: usize) -> u64 {
    let index = (sorted.len() - 1).saturating_mul(percentile) / 100;
    sorted[index]
}

fn elapsed_ns(start: Instant) -> u64 {
    u64::try_from(start.elapsed().as_nanos()).unwrap_or(u64::MAX)
}

fn throughput(requests: u64, duration_ns: u64) -> f64 {
    if duration_ns == 0 {
        0.0
    } else {
        requests as f64 * 1_000_000_000.0 / duration_ns as f64
    }
}

fn capacity(iterations: u64) -> Result<usize, EvaluationError> {
    usize::try_from(iterations)
        .map_err(|_| EvaluationError::InvalidArgument("iterations exceed address space"))
}

fn broker_config(budget: u64) -> BrokerConfig {
    BrokerConfig {
        capabilities: vec![CapabilitySpec {
            id: CAPABILITY,
            budget,
        }],
    }
}

fn request_spec(class: RetryClass, seed: u64) -> RequestSpec {
    let digest = Digest(1_000u64.saturating_add(seed));
    match class {
        RetryClass::Uncontrolled => RequestSpec::uncontrolled(digest),
        RetryClass::Idempotent => RequestSpec::idempotent(digest),
        RetryClass::Deduplicated => {
            RequestSpec::deduplicated(digest, DedupKey(1_000_000u64.saturating_add(seed)))
        }
        RetryClass::ReadOnly => unreachable!("M4 evaluation excludes ReadOnly"),
    }
}

fn class_name(class: RetryClass) -> &'static str {
    match class {
        RetryClass::Uncontrolled => "uncontrolled",
        RetryClass::Idempotent => "idempotent",
        RetryClass::Deduplicated => "deduplicated",
        RetryClass::ReadOnly => "read_only",
    }
}

fn site_name(site: CrashSite) -> &'static str {
    match site {
        CrashSite::AfterAuthorize => "after_authorize",
        CrashSite::AfterPrepare => "after_prepare",
        CrashSite::AfterArm => "after_arm",
        CrashSite::AfterStart => "after_start",
        CrashSite::AfterInvoke => "after_invoke",
        CrashSite::AfterOutcome => "after_outcome",
        CrashSite::AfterTerminal => "after_terminal",
    }
}

fn terminal_name(terminal: TerminalResult) -> &'static str {
    match terminal {
        TerminalResult::Committed { .. } => "committed",
        TerminalResult::Failed { .. } => "failed",
        TerminalResult::Unknown { .. } => "unknown",
    }
}

fn environment() -> Environment {
    let hostname = std::env::var("HOSTNAME")
        .or_else(|_| std::env::var("COMPUTERNAME"))
        .ok()
        .or_else(|| command_output("hostname", &[]))
        .unwrap_or_else(|| "unknown".to_owned());
    let rustc = command_output("rustc", &["--version"]).unwrap_or_else(|| "unknown".to_owned());
    Environment {
        hostname,
        target: format!("{}-{}", std::env::consts::ARCH, std::env::consts::OS),
        rustc,
        source_revision: std::env::var("PROVEAI_SOURCE_REVISION")
            .ok()
            .or_else(git_revision)
            .unwrap_or_else(|| "unknown".to_owned()),
        build_profile: if cfg!(debug_assertions) {
            "debug"
        } else {
            "release"
        },
        package_version: env!("CARGO_PKG_VERSION"),
        logical_cpus: std::thread::available_parallelism()
            .map(|count| count.get() as u64)
            .unwrap_or(1),
    }
}

fn git_revision() -> Option<String> {
    command_output("git", &["rev-parse", "HEAD"])
}

fn command_output(program: &str, arguments: &[&str]) -> Option<String> {
    Command::new(program)
        .args(arguments)
        .output()
        .ok()
        .filter(|output| output.status.success())
        .map(|output| String::from_utf8_lossy(&output.stdout).trim().to_owned())
}

struct EvaluationWorkspace {
    root: PathBuf,
}

impl EvaluationWorkspace {
    fn new() -> Result<Self, EvaluationError> {
        let serial = NEXT_WORKSPACE.fetch_add(1, Ordering::Relaxed);
        let root = std::env::temp_dir().join(format!(
            "proveai-evaluation-{}-{serial}",
            std::process::id()
        ));
        std::fs::create_dir(&root)?;
        Ok(Self { root })
    }

    fn path(&self, name: &str) -> PathBuf {
        self.root.join(name)
    }
}

impl Drop for EvaluationWorkspace {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.root);
    }
}

impl EvaluationReport {
    #[must_use]
    pub fn to_json_pretty(&self) -> String {
        self.to_string()
    }
}

impl fmt::Display for EvaluationReport {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(formatter, "{{")?;
        writeln!(formatter, "  \"schema_version\": {REPORT_SCHEMA_VERSION},")?;
        writeln!(
            formatter,
            "  \"generated_unix_seconds\": {},",
            self.generated_unix_seconds
        )?;
        writeln!(formatter, "  \"iterations\": {},", self.iterations)?;
        writeln!(
            formatter,
            "  \"retry_iterations\": {},",
            self.retry_iterations
        )?;
        writeln!(formatter, "  \"environment\": {{")?;
        writeln!(
            formatter,
            "    \"hostname\": {},",
            JsonString(&self.environment.hostname)
        )?;
        writeln!(
            formatter,
            "    \"target\": {},",
            JsonString(&self.environment.target)
        )?;
        writeln!(
            formatter,
            "    \"rustc\": {},",
            JsonString(&self.environment.rustc)
        )?;
        writeln!(
            formatter,
            "    \"source_revision\": {},",
            JsonString(&self.environment.source_revision)
        )?;
        writeln!(
            formatter,
            "    \"build_profile\": {},",
            JsonString(self.environment.build_profile)
        )?;
        writeln!(
            formatter,
            "    \"package_version\": {},",
            JsonString(self.environment.package_version)
        )?;
        writeln!(
            formatter,
            "    \"logical_cpus\": {}",
            self.environment.logical_cpus
        )?;
        writeln!(formatter, "  }},")?;
        write_rq1(formatter, &self.rq1)?;
        writeln!(formatter, ",")?;
        write_rq2(formatter, &self.rq2)?;
        writeln!(formatter)?;
        writeln!(formatter, "}}")
    }
}

fn write_rq1(formatter: &mut fmt::Formatter<'_>, report: &Rq1Report) -> fmt::Result {
    writeln!(formatter, "  \"rq1\": {{")?;
    writeln!(formatter, "    \"all_passed\": {},", report.all_passed)?;
    writeln!(
        formatter,
        "    \"stale_delivery_rejected\": {},",
        report.stale_delivery_rejected
    )?;
    writeln!(formatter, "    \"case_count\": {},", report.cases.len())?;
    writeln!(formatter, "    \"cases\": [")?;
    for (index, case) in report.cases.iter().enumerate() {
        writeln!(formatter, "      {{")?;
        writeln!(
            formatter,
            "        \"adapter\": {},",
            JsonString(case.adapter)
        )?;
        writeln!(
            formatter,
            "        \"crash_site\": {},",
            JsonString(case.crash_site)
        )?;
        writeln!(
            formatter,
            "        \"terminal\": {},",
            JsonString(case.terminal)
        )?;
        writeln!(
            formatter,
            "        \"terminal_attempt\": {},",
            case.terminal_attempt
        )?;
        writeln!(
            formatter,
            "        \"physical_invocations\": {},",
            case.physical_invocations
        )?;
        writeln!(
            formatter,
            "        \"abstract_effects\": {},",
            case.abstract_effects
        )?;
        writeln!(
            formatter,
            "        \"terminal_records\": {},",
            case.terminal_records
        )?;
        writeln!(
            formatter,
            "        \"authorization_ancestry\": {},",
            case.authorization_ancestry
        )?;
        writeln!(
            formatter,
            "        \"retry_bound_respected\": {},",
            case.retry_bound_respected
        )?;
        writeln!(
            formatter,
            "        \"effect_oracle_satisfied\": {},",
            case.effect_oracle_satisfied
        )?;
        writeln!(formatter, "        \"passed\": {}", case.passed)?;
        write!(formatter, "      }}")?;
        if index + 1 != report.cases.len() {
            writeln!(formatter, ",")?;
        } else {
            writeln!(formatter)?;
        }
    }
    writeln!(formatter, "    ]")?;
    write!(formatter, "  }}")
}

fn write_rq2(formatter: &mut fmt::Formatter<'_>, report: &Rq2Report) -> fmt::Result {
    writeln!(formatter, "  \"rq2\": {{")?;
    writeln!(formatter, "    \"methodology\": {{")?;
    writeln!(
        formatter,
        "      \"scope\": \"single-process local microbenchmark\","
    )?;
    writeln!(
        formatter,
        "      \"latency_clock\": \"monotonic wall clock\","
    )?;
    writeln!(
        formatter,
        "      \"mediated_flush_policy\": \"sync_data after every protocol record\","
    )?;
    writeln!(
        formatter,
        "      \"journaled_ablation\": \"sync_data after Start and result; no adapter effect contract\""
    )?;
    writeln!(formatter, "    }},")?;
    writeln!(formatter, "    \"workloads\": {{")?;
    write_workload(formatter, "mediated", &report.mediated, true)?;
    write_workload(formatter, "direct", &report.direct, true)?;
    write_workload(
        formatter,
        "journaled_at_least_once",
        &report.journaled_at_least_once,
        false,
    )?;
    writeln!(formatter, "    }},")?;
    writeln!(formatter, "    \"retry_scenarios\": [")?;
    for (index, metrics) in report.retry_scenarios.iter().enumerate() {
        write_retry_metrics(formatter, metrics)?;
        if index + 1 != report.retry_scenarios.len() {
            writeln!(formatter, ",")?;
        } else {
            writeln!(formatter)?;
        }
    }
    writeln!(formatter, "    ]")?;
    write!(formatter, "  }}")
}

fn write_workload(
    formatter: &mut fmt::Formatter<'_>,
    name: &str,
    metrics: &WorkloadMetrics,
    comma: bool,
) -> fmt::Result {
    writeln!(formatter, "      {}: {{", JsonString(name))?;
    writeln!(formatter, "        \"requests\": {},", metrics.requests)?;
    writeln!(
        formatter,
        "        \"duration_ns\": {},",
        metrics.duration_ns
    )?;
    writeln!(
        formatter,
        "        \"throughput_requests_per_second\": {:.3},",
        metrics.throughput_requests_per_second
    )?;
    write_latency(formatter, &metrics.latency, 8)?;
    writeln!(formatter, ",")?;
    writeln!(formatter, "        \"wal_bytes\": {},", metrics.wal_bytes)?;
    writeln!(formatter, "        \"flushes\": {},", metrics.flushes)?;
    writeln!(
        formatter,
        "        \"recovery_ns\": {},",
        metrics.recovery_ns
    )?;
    writeln!(
        formatter,
        "        \"physical_invocations\": {},",
        metrics.physical_invocations
    )?;
    writeln!(
        formatter,
        "        \"abstract_effects\": {}",
        metrics.abstract_effects
    )?;
    write!(formatter, "      }}")?;
    if comma {
        writeln!(formatter, ",")
    } else {
        writeln!(formatter)
    }
}

fn write_retry_metrics(formatter: &mut fmt::Formatter<'_>, metrics: &RetryMetrics) -> fmt::Result {
    writeln!(formatter, "      {{")?;
    writeln!(
        formatter,
        "        \"mechanism\": {},",
        JsonString(metrics.mechanism)
    )?;
    writeln!(formatter, "        \"requests\": {},", metrics.requests)?;
    writeln!(
        formatter,
        "        \"duration_ns\": {},",
        metrics.duration_ns
    )?;
    write_latency(formatter, &metrics.latency, 8)?;
    writeln!(formatter, ",")?;
    writeln!(
        formatter,
        "        \"physical_invocations\": {},",
        metrics.physical_invocations
    )?;
    writeln!(
        formatter,
        "        \"abstract_effects\": {},",
        metrics.abstract_effects
    )?;
    writeln!(
        formatter,
        "        \"extra_invocations\": {},",
        metrics.extra_invocations
    )?;
    writeln!(
        formatter,
        "        \"extra_effects\": {},",
        metrics.extra_effects
    )?;
    writeln!(formatter, "        \"wal_bytes\": {},", metrics.wal_bytes)?;
    writeln!(formatter, "        \"flushes\": {}", metrics.flushes)?;
    write!(formatter, "      }}")
}

fn write_latency(
    formatter: &mut fmt::Formatter<'_>,
    metrics: &LatencyMetrics,
    indent: usize,
) -> fmt::Result {
    let spaces = " ".repeat(indent);
    writeln!(formatter, "{spaces}\"latency_ns\": {{")?;
    writeln!(formatter, "{spaces}  \"mean\": {},", metrics.mean_ns)?;
    writeln!(formatter, "{spaces}  \"p50\": {},", metrics.p50_ns)?;
    writeln!(formatter, "{spaces}  \"p95\": {},", metrics.p95_ns)?;
    writeln!(formatter, "{spaces}  \"p99\": {}", metrics.p99_ns)?;
    write!(formatter, "{spaces}}}")
}

struct JsonString<'a>(&'a str);

impl fmt::Display for JsonString<'_> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("\"")?;
        for character in self.0.chars() {
            match character {
                '"' => formatter.write_str("\\\""),
                '\\' => formatter.write_str("\\\\"),
                '\n' => formatter.write_str("\\n"),
                '\r' => formatter.write_str("\\r"),
                '\t' => formatter.write_str("\\t"),
                character if character < ' ' => {
                    write!(formatter, "\\u{:04x}", u32::from(character))
                }
                character => formatter.write_char(character),
            }?;
        }
        formatter.write_str("\"")
    }
}
