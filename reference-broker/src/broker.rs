use std::collections::BTreeMap;
use std::fmt;
use std::fs::OpenOptions;
use std::io::{self, Read, Write};
use std::path::{Path, PathBuf};

use crate::adapter::{Adapter, Delivery};
use crate::fault::{CrashPlan, CrashSite};
use crate::model::{
    CapabilityId, DedupKey, Digest, Invocation, InvocationId, JournalRecord, Observation, Phase,
    RequestId, RequestSpec, RetryClass, TerminalResult, UnknownReason,
};
use crate::wal::{FileWal, RecoveryReport, WalError, WalMetrics};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CapabilitySpec {
    pub id: CapabilityId,
    pub budget: u64,
}

/// Immutable request metadata for the optional verified-profile boundary.
///
/// The typed Journal records only the capability and digest at `Authorize`; the
/// retry class and key first appear at `Prepare`. A profile binds all of those
/// fields before the first durable record so a static formal configuration can
/// describe the resulting execution.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AdmissionBinding {
    pub request: RequestId,
    pub capability: CapabilityId,
    pub spec: RequestSpec,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct BrokerConfig {
    pub capabilities: Vec<CapabilitySpec>,
    /// `None` retains the general reference-broker mode. `Some`, including an
    /// empty manifest, requires every admission to match a pre-bound request.
    pub admission_manifest: Option<Vec<AdmissionBinding>>,
}

#[derive(Debug)]
pub enum BrokerError {
    Wal(WalError),
    ConfigurationIo(io::Error),
    ConfigurationMismatch,
    InvalidConfig(&'static str),
    InvalidSpec(&'static str),
    Protocol(&'static str),
    UnknownRequest(RequestId),
    UnknownCapability(CapabilityId),
    CapabilityRevoked(CapabilityId),
    BudgetExhausted(CapabilityId),
    RequestNotPrepared(RequestId),
    RecoveryRequired(RequestId),
    ExecutorBusy(RequestId),
    StaleDelivery {
        expected: Option<InvocationId>,
        received: InvocationId,
    },
    AdapterClassMismatch {
        request: RetryClass,
        adapter: RetryClass,
    },
    AttemptsMustBePositive,
    AttemptLimitMismatch {
        configured: u64,
        supplied: u64,
    },
    AttemptLimitReached(RequestId),
    Crashed,
    SimulatedCrash(CrashSite),
}

impl fmt::Display for BrokerError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Wal(error) => error.fmt(formatter),
            Self::ConfigurationIo(error) => {
                write!(formatter, "broker configuration I/O error: {error}")
            }
            Self::ConfigurationMismatch => {
                formatter.write_str("broker configuration does not match the WAL binding")
            }
            Self::InvalidConfig(detail) => {
                write!(formatter, "invalid broker configuration: {detail}")
            }
            Self::InvalidSpec(detail) => {
                write!(formatter, "invalid request specification: {detail}")
            }
            Self::Protocol(detail) => {
                write!(formatter, "WAL violates the broker protocol: {detail}")
            }
            Self::UnknownRequest(request) => write!(formatter, "unknown request {request}"),
            Self::UnknownCapability(capability) => {
                write!(formatter, "unknown capability {capability}")
            }
            Self::CapabilityRevoked(capability) => {
                write!(formatter, "capability {capability} is revoked")
            }
            Self::BudgetExhausted(capability) => {
                write!(formatter, "capability {capability} has no remaining budget")
            }
            Self::RequestNotPrepared(request) => {
                write!(formatter, "request {request} is not prepared")
            }
            Self::RecoveryRequired(request) => write!(
                formatter,
                "request {request} has an interrupted invocation to recover"
            ),
            Self::ExecutorBusy(request) => {
                write!(formatter, "executor slot is occupied by request {request}")
            }
            Self::StaleDelivery { expected, received } => write!(
                formatter,
                "stale delivery for invocation {received}; expected {expected:?}"
            ),
            Self::AdapterClassMismatch { request, adapter } => write!(
                formatter,
                "adapter class {adapter:?} does not match request class {request:?}"
            ),
            Self::AttemptsMustBePositive => {
                formatter.write_str("maximum attempts must be positive")
            }
            Self::AttemptLimitMismatch {
                configured,
                supplied,
            } => write!(
                formatter,
                "retry limit for this request is {configured}, but caller supplied {supplied}"
            ),
            Self::AttemptLimitReached(request) => {
                write!(formatter, "request {request} has reached its retry limit")
            }
            Self::Crashed => formatter
                .write_str("broker instance is unusable after a simulated crash; reopen the WAL"),
            Self::SimulatedCrash(site) => write!(formatter, "simulated crash at {site:?}"),
        }
    }
}

impl std::error::Error for BrokerError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Wal(error) => Some(error),
            Self::ConfigurationIo(error) => Some(error),
            _ => None,
        }
    }
}

impl From<WalError> for BrokerError {
    fn from(error: WalError) -> Self {
        Self::Wal(error)
    }
}

#[derive(Clone, Debug)]
struct CapabilityState {
    remaining: u64,
    revoked: bool,
}

#[derive(Clone, Copy, Debug)]
struct PendingAttempt {
    attempt: u64,
    start_ref: u64,
}

#[derive(Clone, Copy, Debug)]
struct RecordedOutcome {
    attempt: u64,
    observation: Observation,
    outcome_ref: u64,
}

#[derive(Clone, Debug)]
struct RequestState {
    capability: CapabilityId,
    digest: Digest,
    class: Option<RetryClass>,
    key: Option<DedupKey>,
    phase: Phase,
    auth_ref: u64,
    prepare_ref: Option<u64>,
    arm_ref: Option<u64>,
    attempts: u64,
    pending: Option<PendingAttempt>,
    outcome: Option<RecordedOutcome>,
    terminal: Option<TerminalResult>,
}

#[derive(Clone, Debug)]
struct DurableState {
    capabilities: BTreeMap<CapabilityId, CapabilityState>,
    admission_manifest: Option<BTreeMap<RequestId, AdmissionBinding>>,
    requests: BTreeMap<RequestId, RequestState>,
    next_request: u64,
}

impl DurableState {
    fn from_config(config: &BrokerConfig) -> Result<Self, BrokerError> {
        let mut capabilities = BTreeMap::new();
        for capability in &config.capabilities {
            if capability.id.0 == 0 {
                return Err(BrokerError::InvalidConfig("capability ID zero is reserved"));
            }
            if capabilities
                .insert(
                    capability.id,
                    CapabilityState {
                        remaining: capability.budget,
                        revoked: false,
                    },
                )
                .is_some()
            {
                return Err(BrokerError::InvalidConfig("duplicate capability ID"));
            }
        }
        let admission_manifest = match &config.admission_manifest {
            None => None,
            Some(bindings) => {
                let mut manifest: BTreeMap<RequestId, AdmissionBinding> = BTreeMap::new();
                for binding in bindings {
                    if binding.request.0 == 0 {
                        return Err(BrokerError::InvalidConfig("request ID zero is reserved"));
                    }
                    if !capabilities.contains_key(&binding.capability) {
                        return Err(BrokerError::InvalidConfig(
                            "manifest names an unknown capability",
                        ));
                    }
                    if !binding.spec.has_valid_key_shape() {
                        return Err(BrokerError::InvalidConfig(
                            "manifest has an invalid retry-class/key shape",
                        ));
                    }
                    if binding.spec.class == RetryClass::Deduplicated
                        && manifest.values().any(|existing| {
                            existing.spec.class == RetryClass::Deduplicated
                                && existing.spec.key == binding.spec.key
                        })
                    {
                        return Err(BrokerError::InvalidConfig(
                            "manifest reuses a Deduplicated key",
                        ));
                    }
                    if manifest.insert(binding.request, *binding).is_some() {
                        return Err(BrokerError::InvalidConfig(
                            "manifest contains a duplicate request ID",
                        ));
                    }
                }
                Some(manifest)
            }
        };
        Ok(Self {
            capabilities,
            admission_manifest,
            requests: BTreeMap::new(),
            next_request: 1,
        })
    }

    fn replay(config: &BrokerConfig, records: &[JournalRecord]) -> Result<Self, BrokerError> {
        let mut state = Self::from_config(config)?;
        for (index, record) in records.iter().copied().enumerate() {
            let lsn = u64::try_from(index)
                .ok()
                .and_then(|index| index.checked_add(1))
                .ok_or(BrokerError::Protocol("LSN space exhausted"))?;
            state.apply(record, lsn)?;
        }
        Ok(state)
    }

    fn apply(&mut self, record: JournalRecord, lsn: u64) -> Result<(), BrokerError> {
        match record {
            JournalRecord::Authorize {
                request,
                capability,
                digest,
            } => {
                if request.0 != self.next_request {
                    return Err(BrokerError::Protocol("request IDs are not contiguous"));
                }
                if let Some(binding) = self.admission_binding(request) {
                    if binding.capability != capability || binding.spec.digest != digest {
                        return Err(BrokerError::Protocol(
                            "Authorize does not match the immutable admission manifest",
                        ));
                    }
                }
                let capability_state =
                    self.capabilities
                        .get_mut(&capability)
                        .ok_or(BrokerError::Protocol(
                            "Authorize names an unknown capability",
                        ))?;
                if capability_state.revoked {
                    return Err(BrokerError::Protocol("Authorize uses a revoked capability"));
                }
                if capability_state.remaining == 0 {
                    return Err(BrokerError::Protocol("Authorize exceeds capability budget"));
                }
                capability_state.remaining -= 1;
                self.requests.insert(
                    request,
                    RequestState {
                        capability,
                        digest,
                        class: None,
                        key: None,
                        phase: Phase::Authorized,
                        auth_ref: lsn,
                        prepare_ref: None,
                        arm_ref: None,
                        attempts: 0,
                        pending: None,
                        outcome: None,
                        terminal: None,
                    },
                );
                self.next_request = self
                    .next_request
                    .checked_add(1)
                    .ok_or(BrokerError::Protocol("request ID space exhausted"))?;
            }
            JournalRecord::Revoke { capability } => {
                let capability_state = self
                    .capabilities
                    .get_mut(&capability)
                    .ok_or(BrokerError::Protocol("Revoke names an unknown capability"))?;
                if capability_state.revoked {
                    return Err(BrokerError::Protocol("capability is revoked twice"));
                }
                capability_state.revoked = true;
            }
            JournalRecord::Prepare {
                request,
                class,
                digest,
                key,
                auth_ref,
            } => {
                let binding = self.admission_binding(request);
                let request_state = self.request_mut(request)?;
                if request_state.phase != Phase::Authorized
                    || request_state.class.is_some()
                    || request_state.digest != digest
                    || request_state.auth_ref != auth_ref
                    || (matches!(class, RetryClass::Deduplicated) != key.is_some())
                    || binding.is_some_and(|binding| {
                        binding.spec.digest != digest
                            || binding.spec.class != class
                            || binding.spec.key != key
                    })
                {
                    return Err(BrokerError::Protocol("invalid Prepare record"));
                }
                request_state.class = Some(class);
                request_state.key = key;
                request_state.phase = Phase::Prepared;
                request_state.prepare_ref = Some(lsn);
            }
            JournalRecord::Arm {
                request,
                digest,
                key,
                prepare_ref,
            } => {
                let request_state = self.request_mut(request)?;
                if request_state.phase != Phase::Prepared
                    || request_state.digest != digest
                    || request_state.key != key
                    || request_state.prepare_ref != Some(prepare_ref)
                {
                    return Err(BrokerError::Protocol("invalid Arm record"));
                }
                request_state.phase = Phase::Armed;
                request_state.arm_ref = Some(lsn);
            }
            JournalRecord::Start {
                request,
                attempt,
                digest,
                key,
                arm_ref,
            } => {
                if self
                    .requests
                    .iter()
                    .any(|(other, state)| *other != request && state.pending.is_some())
                {
                    return Err(BrokerError::Protocol(
                        "more than one durable invocation is pending",
                    ));
                }
                let request_state = self.request_mut(request)?;
                let retry_allowed = matches!(
                    request_state.outcome,
                    Some(RecordedOutcome {
                        observation: Observation::Ambiguous,
                        ..
                    })
                ) && request_state.class != Some(RetryClass::Uncontrolled);
                if request_state.phase != Phase::Armed
                    || request_state.digest != digest
                    || request_state.key != key
                    || request_state.arm_ref != Some(arm_ref)
                    || request_state.pending.is_some()
                    || (request_state.attempts == 0 && request_state.outcome.is_some())
                    || (request_state.attempts > 0 && !retry_allowed)
                    || attempt != request_state.attempts.saturating_add(1)
                {
                    return Err(BrokerError::Protocol("invalid Start record"));
                }
                request_state.attempts = attempt;
                request_state.outcome = None;
                request_state.pending = Some(PendingAttempt {
                    attempt,
                    start_ref: lsn,
                });
            }
            JournalRecord::Outcome {
                request,
                attempt,
                observation,
                digest,
                key,
                start_ref,
            } => {
                let request_state = self.request_mut(request)?;
                let expected = request_state.pending;
                if request_state.phase != Phase::Armed
                    || request_state.digest != digest
                    || request_state.key != key
                    || expected.map(|pending| pending.attempt) != Some(attempt)
                    || expected.map(|pending| pending.start_ref) != Some(start_ref)
                    || request_state.outcome.is_some()
                {
                    return Err(BrokerError::Protocol("invalid Outcome record"));
                }
                request_state.pending = None;
                request_state.outcome = Some(RecordedOutcome {
                    attempt,
                    observation,
                    outcome_ref: lsn,
                });
            }
            JournalRecord::Commit {
                request,
                attempt,
                value,
                digest,
                key,
                outcome_ref,
            } => {
                let request_state = self.request_mut(request)?;
                let expected = request_state.outcome;
                if request_state.phase != Phase::Armed
                    || request_state.digest != digest
                    || request_state.key != key
                    || expected.map(|outcome| outcome.attempt) != Some(attempt)
                    || expected.map(|outcome| outcome.outcome_ref) != Some(outcome_ref)
                    || expected.map(|outcome| outcome.observation)
                        != Some(Observation::Success(value))
                {
                    return Err(BrokerError::Protocol("invalid Commit record"));
                }
                request_state.phase = Phase::Committed;
                request_state.outcome = None;
                request_state.terminal = Some(TerminalResult::Committed { attempt, value });
            }
            JournalRecord::Fail {
                request,
                attempt,
                digest,
                key,
                outcome_ref,
            } => {
                let request_state = self.request_mut(request)?;
                let expected = request_state.outcome;
                if request_state.phase != Phase::Armed
                    || request_state.digest != digest
                    || request_state.key != key
                    || expected.map(|outcome| outcome.attempt) != Some(attempt)
                    || expected.map(|outcome| outcome.outcome_ref) != Some(outcome_ref)
                    || expected.map(|outcome| outcome.observation) != Some(Observation::Failure)
                {
                    return Err(BrokerError::Protocol("invalid Fail record"));
                }
                request_state.phase = Phase::Failed;
                request_state.outcome = None;
                request_state.terminal = Some(TerminalResult::Failed { attempt });
            }
            JournalRecord::Unknown {
                request,
                attempt,
                reason,
                digest,
                key,
                evidence_ref,
            } => {
                let request_state = self.request_mut(request)?;
                let expected = request_state.outcome;
                if request_state.phase != Phase::Armed
                    || request_state.digest != digest
                    || request_state.key != key
                    || expected.map(|outcome| outcome.attempt) != attempt
                    || expected.map(|outcome| outcome.outcome_ref) != Some(evidence_ref)
                {
                    return Err(BrokerError::Protocol("invalid Unknown record"));
                }
                request_state.phase = Phase::Unknown;
                request_state.outcome = None;
                request_state.terminal = Some(TerminalResult::Unknown { attempt, reason });
            }
        }
        Ok(())
    }

    fn request(&self, request: RequestId) -> Result<&RequestState, BrokerError> {
        self.requests
            .get(&request)
            .ok_or(BrokerError::UnknownRequest(request))
    }

    fn request_mut(&mut self, request: RequestId) -> Result<&mut RequestState, BrokerError> {
        self.requests
            .get_mut(&request)
            .ok_or(BrokerError::Protocol("record names an unknown request"))
    }

    fn admission_binding(&self, request: RequestId) -> Option<AdmissionBinding> {
        self.admission_manifest
            .as_ref()
            .and_then(|manifest| manifest.get(&request).copied())
    }
}

pub struct Broker {
    wal: FileWal,
    state: DurableState,
    active: Option<Invocation>,
    crash_plan: Option<CrashPlan>,
    recovery: RecoveryReport,
    crashed: bool,
}

impl Broker {
    pub fn open(path: impl AsRef<Path>, config: BrokerConfig) -> Result<Self, BrokerError> {
        let path = path.as_ref();
        let _ = DurableState::from_config(&config)?;
        bind_configuration(path, &config)?;
        let (wal, recovery) = FileWal::open(path)?;
        let state = DurableState::replay(&config, wal.records())?;
        Ok(Self {
            wal,
            state,
            active: None,
            crash_plan: None,
            recovery,
            crashed: false,
        })
    }

    pub fn set_crash_plan(&mut self, plan: Option<CrashPlan>) {
        self.crash_plan = plan;
    }

    #[must_use]
    pub const fn recovery_report(&self) -> RecoveryReport {
        self.recovery
    }

    #[must_use]
    pub fn wal_records(&self) -> &[JournalRecord] {
        self.wal.records()
    }

    #[must_use]
    pub const fn wal_metrics(&self) -> WalMetrics {
        self.wal.metrics()
    }

    #[must_use]
    pub const fn active_invocation(&self) -> Option<Invocation> {
        self.active
    }

    #[must_use]
    pub fn request_ids(&self) -> Vec<RequestId> {
        self.state.requests.keys().copied().collect()
    }

    pub fn remaining_budget(&self, capability: CapabilityId) -> Result<u64, BrokerError> {
        self.state
            .capabilities
            .get(&capability)
            .map(|state| state.remaining)
            .ok_or(BrokerError::UnknownCapability(capability))
    }

    pub fn phase(&self, request: RequestId) -> Result<Phase, BrokerError> {
        self.state.request(request).map(|state| state.phase)
    }

    pub fn request_capability(&self, request: RequestId) -> Result<CapabilityId, BrokerError> {
        self.state.request(request).map(|state| state.capability)
    }

    pub fn terminal(&self, request: RequestId) -> Result<Option<TerminalResult>, BrokerError> {
        self.state.request(request).map(|state| state.terminal)
    }

    pub fn admit(
        &mut self,
        capability: CapabilityId,
        digest: Digest,
    ) -> Result<RequestId, BrokerError> {
        self.ensure_operational()?;
        let capability_state = self
            .state
            .capabilities
            .get(&capability)
            .ok_or(BrokerError::UnknownCapability(capability))?;
        if capability_state.revoked {
            return Err(BrokerError::CapabilityRevoked(capability));
        }
        if capability_state.remaining == 0 {
            return Err(BrokerError::BudgetExhausted(capability));
        }
        let request = RequestId(self.state.next_request);
        if let Some(binding) = self.state.admission_binding(request) {
            if binding.capability != capability || binding.spec.digest != digest {
                return Err(BrokerError::InvalidSpec(
                    "admission does not match the immutable request manifest",
                ));
            }
        } else if self.state.admission_manifest.is_some() {
            return Err(BrokerError::InvalidSpec(
                "request is absent from the immutable admission manifest",
            ));
        }
        self.append(JournalRecord::Authorize {
            request,
            capability,
            digest,
        })?;
        self.crash(CrashSite::AfterAuthorize)?;
        Ok(request)
    }

    pub fn prepare(&mut self, request: RequestId, spec: RequestSpec) -> Result<(), BrokerError> {
        self.ensure_operational()?;
        if !spec.has_valid_key_shape() {
            return Err(BrokerError::InvalidSpec(
                "a key is required exactly for Deduplicated requests",
            ));
        }
        let request_state = self.state.request(request)?;
        if request_state.phase != Phase::Authorized || request_state.digest != spec.digest {
            return Err(BrokerError::InvalidSpec(
                "Prepare must match an authorized request and digest",
            ));
        }
        if let Some(binding) = self.state.admission_binding(request) {
            if binding.spec != spec {
                return Err(BrokerError::InvalidSpec(
                    "Prepare does not match the immutable request manifest",
                ));
            }
        }
        let auth_ref = request_state.auth_ref;
        self.append(JournalRecord::Prepare {
            request,
            class: spec.class,
            digest: spec.digest,
            key: spec.key,
            auth_ref,
        })?;
        self.crash(CrashSite::AfterPrepare)
    }

    pub fn revoke(&mut self, capability: CapabilityId) -> Result<(), BrokerError> {
        self.ensure_operational()?;
        let state = self
            .state
            .capabilities
            .get(&capability)
            .ok_or(BrokerError::UnknownCapability(capability))?;
        if state.revoked {
            return Err(BrokerError::CapabilityRevoked(capability));
        }
        self.append(JournalRecord::Revoke { capability })?;
        Ok(())
    }

    pub fn begin_attempt(&mut self, request: RequestId) -> Result<Invocation, BrokerError> {
        self.ensure_operational()?;
        if let Some(active) = self.active {
            return Err(BrokerError::ExecutorBusy(active.request));
        }
        if let Some(interrupted) = self.interrupted_request() {
            return Err(BrokerError::RecoveryRequired(interrupted));
        }
        let class = self
            .state
            .request(request)?
            .class
            .ok_or(BrokerError::RequestNotPrepared(request))?;
        self.resolve_recorded_outcome(request, Some(class.max_attempts()))?;
        if let Some(terminal) = self.terminal(request)? {
            return Err(BrokerError::Protocol(match terminal {
                TerminalResult::Committed { .. } => "committed request cannot start",
                TerminalResult::Failed { .. } => "failed request cannot start",
                TerminalResult::Unknown { .. } => "unknown request cannot start",
            }));
        }
        self.arm_if_needed(request)?;

        let request_state = self.state.request(request)?;
        if class == RetryClass::ReadOnly {
            return Err(BrokerError::InvalidSpec(
                "M4 provides no ReadOnly reference adapter",
            ));
        }
        let retry_limit = class.max_attempts();
        let attempt = request_state
            .attempts
            .checked_add(1)
            .ok_or(BrokerError::Protocol("attempt space exhausted"))?;
        if attempt > retry_limit {
            return Err(BrokerError::AttemptLimitReached(request));
        }
        let digest = request_state.digest;
        let key = request_state.key;
        let arm_ref = request_state
            .arm_ref
            .ok_or(BrokerError::Protocol("armed request lacks Arm reference"))?;
        let record = JournalRecord::Start {
            request,
            attempt,
            digest,
            key,
            arm_ref,
        };
        let start_ref = self.append(record)?;
        let invocation = Invocation {
            id: InvocationId(start_ref),
            request,
            attempt,
            digest,
            key,
        };
        self.active = Some(invocation);
        self.crash(CrashSite::AfterStart)?;
        Ok(invocation)
    }

    pub fn accept_delivery(
        &mut self,
        delivery: Delivery,
    ) -> Result<Option<TerminalResult>, BrokerError> {
        self.ensure_operational()?;
        self.accept_delivery_with_limit(delivery, None)
    }

    pub fn run<A: Adapter>(
        &mut self,
        request: RequestId,
        max_attempts: u64,
        adapter: &mut A,
    ) -> Result<TerminalResult, BrokerError> {
        self.ensure_operational()?;
        if max_attempts == 0 {
            return Err(BrokerError::AttemptsMustBePositive);
        }
        let request_class = self
            .state
            .request(request)?
            .class
            .ok_or(BrokerError::RequestNotPrepared(request))?;
        let configured_limit = request_class.max_attempts();
        if max_attempts != configured_limit {
            return Err(BrokerError::AttemptLimitMismatch {
                configured: configured_limit,
                supplied: max_attempts,
            });
        }
        if request_class != adapter.retry_class() {
            return Err(BrokerError::AdapterClassMismatch {
                request: request_class,
                adapter: adapter.retry_class(),
            });
        }

        loop {
            if let Some(terminal) = self.terminal(request)? {
                return Ok(terminal);
            }
            self.recover_interrupted(request, max_attempts)?;
            if let Some(terminal) = self.resolve_recorded_outcome(request, Some(max_attempts))? {
                return Ok(terminal);
            }

            let invocation = match self.active {
                Some(active) if active.request == request => active,
                Some(active) => return Err(BrokerError::ExecutorBusy(active.request)),
                None => self.begin_attempt(request)?,
            };
            let delivery = adapter.invoke(invocation);
            self.crash(CrashSite::AfterInvoke)?;
            if let Some(terminal) = self.accept_delivery_with_limit(delivery, Some(max_attempts))? {
                return Ok(terminal);
            }
        }
    }

    fn arm_if_needed(&mut self, request: RequestId) -> Result<(), BrokerError> {
        let request_state = self.state.request(request)?;
        match request_state.phase {
            Phase::Prepared => {
                let digest = request_state.digest;
                let key = request_state.key;
                let prepare_ref = request_state.prepare_ref.ok_or(BrokerError::Protocol(
                    "prepared request lacks Prepare reference",
                ))?;
                let record = JournalRecord::Arm {
                    request,
                    digest,
                    key,
                    prepare_ref,
                };
                self.append(record)?;
                self.crash(CrashSite::AfterArm)
            }
            Phase::Armed => Ok(()),
            _ => Err(BrokerError::RequestNotPrepared(request)),
        }
    }

    fn accept_delivery_with_limit(
        &mut self,
        delivery: Delivery,
        max_attempts: Option<u64>,
    ) -> Result<Option<TerminalResult>, BrokerError> {
        let expected = self.active;
        if expected.map(|invocation| invocation.id) != Some(delivery.invocation) {
            return Err(BrokerError::StaleDelivery {
                expected: expected.map(|invocation| invocation.id),
                received: delivery.invocation,
            });
        }
        let invocation = expected.expect("delivery ID matched an active invocation");
        let class = self
            .state
            .request(invocation.request)?
            .class
            .ok_or(BrokerError::RequestNotPrepared(invocation.request))?;
        let configured_limit = class.max_attempts();
        let max_attempts = max_attempts.or(Some(configured_limit));
        let request_state = self.state.request(invocation.request)?;
        let start_ref = request_state
            .pending
            .map(|pending| pending.start_ref)
            .ok_or(BrokerError::Protocol(
                "active invocation lacks durable Start",
            ))?;
        self.append(JournalRecord::Outcome {
            request: invocation.request,
            attempt: invocation.attempt,
            observation: delivery.observation,
            digest: invocation.digest,
            key: invocation.key,
            start_ref,
        })?;
        self.active = None;
        self.crash(CrashSite::AfterOutcome)?;
        self.resolve_recorded_outcome(invocation.request, max_attempts)
    }

    fn recover_interrupted(
        &mut self,
        request: RequestId,
        max_attempts: u64,
    ) -> Result<(), BrokerError> {
        let Some(interrupted) = self.interrupted_request() else {
            return Ok(());
        };
        if interrupted != request {
            return Err(BrokerError::ExecutorBusy(interrupted));
        }
        let request_state = self.state.request(request)?;
        let pending = request_state
            .pending
            .ok_or(BrokerError::Protocol("interrupted request lacks Start"))?;
        let digest = request_state.digest;
        let key = request_state.key;
        self.append(JournalRecord::Outcome {
            request,
            attempt: pending.attempt,
            observation: Observation::Ambiguous,
            digest,
            key,
            start_ref: pending.start_ref,
        })?;
        self.crash(CrashSite::AfterOutcome)?;
        let _ = self.resolve_recorded_outcome(request, Some(max_attempts))?;
        Ok(())
    }

    fn resolve_recorded_outcome(
        &mut self,
        request: RequestId,
        max_attempts: Option<u64>,
    ) -> Result<Option<TerminalResult>, BrokerError> {
        if let Some(terminal) = self.terminal(request)? {
            return Ok(Some(terminal));
        }
        let request_state = self.state.request(request)?;
        let Some(outcome) = request_state.outcome else {
            return Ok(None);
        };
        let class = request_state
            .class
            .ok_or(BrokerError::RequestNotPrepared(request))?;
        let digest = request_state.digest;
        let key = request_state.key;
        match outcome.observation {
            Observation::Success(value) => {
                self.append(JournalRecord::Commit {
                    request,
                    attempt: outcome.attempt,
                    value,
                    digest,
                    key,
                    outcome_ref: outcome.outcome_ref,
                })?;
            }
            Observation::Failure => {
                self.append(JournalRecord::Fail {
                    request,
                    attempt: outcome.attempt,
                    digest,
                    key,
                    outcome_ref: outcome.outcome_ref,
                })?;
            }
            Observation::InvalidResult(_) => {
                self.append(JournalRecord::Unknown {
                    request,
                    attempt: Some(outcome.attempt),
                    reason: UnknownReason::InvalidResult,
                    digest,
                    key,
                    evidence_ref: outcome.outcome_ref,
                })?;
            }
            Observation::Ambiguous => {
                let exhausted = max_attempts.is_some_and(|limit| outcome.attempt >= limit);
                if class == RetryClass::Uncontrolled || exhausted {
                    self.append(JournalRecord::Unknown {
                        request,
                        attempt: Some(outcome.attempt),
                        reason: if class == RetryClass::Uncontrolled {
                            UnknownReason::AmbiguousOutcome
                        } else {
                            UnknownReason::Exhausted
                        },
                        digest,
                        key,
                        evidence_ref: outcome.outcome_ref,
                    })?;
                } else {
                    return Ok(None);
                }
            }
        }
        self.crash(CrashSite::AfterTerminal)?;
        self.terminal(request)
    }

    fn append(&mut self, record: JournalRecord) -> Result<u64, BrokerError> {
        let next_lsn = u64::try_from(self.wal.records().len())
            .ok()
            .and_then(|length| length.checked_add(1))
            .ok_or(BrokerError::Protocol("LSN space exhausted"))?;
        let mut next_state = self.state.clone();
        next_state.apply(record, next_lsn)?;
        let actual_lsn = self.wal.append(record)?;
        if actual_lsn != next_lsn {
            return Err(BrokerError::Protocol("WAL returned an unexpected LSN"));
        }
        self.state = next_state;
        Ok(actual_lsn)
    }

    fn interrupted_request(&self) -> Option<RequestId> {
        self.state
            .requests
            .iter()
            .find_map(|(request, state)| state.pending.map(|_| *request))
    }

    fn crash(&mut self, site: CrashSite) -> Result<(), BrokerError> {
        if self.crash_plan.as_mut().is_some_and(|plan| plan.hit(site)) {
            self.crashed = true;
            Err(BrokerError::SimulatedCrash(site))
        } else {
            Ok(())
        }
    }

    fn ensure_operational(&self) -> Result<(), BrokerError> {
        if self.crashed {
            Err(BrokerError::Crashed)
        } else {
            Ok(())
        }
    }
}

fn bind_configuration(path: &Path, config: &BrokerConfig) -> Result<(), BrokerError> {
    let mut capabilities = config.capabilities.clone();
    capabilities.sort_by_key(|spec| spec.id);
    let mut expected = b"PROVEAI-BROKER-CONFIG-V2\n".to_vec();
    expected.extend_from_slice(
        &u64::try_from(capabilities.len())
            .map_err(|_| BrokerError::InvalidConfig("capability count exceeds u64"))?
            .to_le_bytes(),
    );
    for capability in capabilities {
        expected.extend_from_slice(&capability.id.0.to_le_bytes());
        expected.extend_from_slice(&capability.budget.to_le_bytes());
    }
    match &config.admission_manifest {
        None => expected.push(0),
        Some(bindings) => {
            expected.push(1);
            let mut bindings = bindings.clone();
            bindings.sort_by_key(|binding| binding.request);
            expected.extend_from_slice(
                &u64::try_from(bindings.len())
                    .map_err(|_| BrokerError::InvalidConfig("manifest count exceeds u64"))?
                    .to_le_bytes(),
            );
            for binding in bindings {
                expected.extend_from_slice(&binding.request.0.to_le_bytes());
                expected.extend_from_slice(&binding.capability.0.to_le_bytes());
                expected.extend_from_slice(&binding.spec.digest.0.to_le_bytes());
                expected.push(match binding.spec.class {
                    RetryClass::ReadOnly => 0,
                    RetryClass::Idempotent => 1,
                    RetryClass::Deduplicated => 2,
                    RetryClass::Uncontrolled => 3,
                });
                match binding.spec.key {
                    Some(key) => {
                        expected.push(1);
                        expected.extend_from_slice(&key.0.to_le_bytes());
                    }
                    None => {
                        expected.push(0);
                        expected.extend_from_slice(&0u64.to_le_bytes());
                    }
                }
            }
        }
    }
    let mut sidecar = path.as_os_str().to_os_string();
    sidecar.push(".config");
    let sidecar = PathBuf::from(sidecar);
    match OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(&sidecar)
    {
        Ok(mut file) => file
            .write_all(&expected)
            .and_then(|_| file.sync_all())
            .map_err(BrokerError::ConfigurationIo),
        Err(error) if error.kind() == io::ErrorKind::AlreadyExists => {
            let mut actual = Vec::new();
            std::fs::File::open(&sidecar)
                .and_then(|mut file| file.read_to_end(&mut actual))
                .map_err(BrokerError::ConfigurationIo)?;
            if actual == expected {
                Ok(())
            } else {
                Err(BrokerError::ConfigurationMismatch)
            }
        }
        Err(error) => Err(BrokerError::ConfigurationIo(error)),
    }
}
