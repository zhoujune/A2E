mod common;

use std::cell::RefCell;
use std::rc::Rc;

use common::{config, TestDirectory};
use proveai_reference_broker::adapters::{IdempotentAdapter, UncontrolledAdapter};
use proveai_reference_broker::{
    AppendGate, Broker, BrokerError, CapabilityId, CrashPlan, CrashSite, Digest, GateError,
    JournalRecord, Observation, RecoveryDecision, RequestSpec, RetryClass, TerminalResult,
    UnknownReason, Value,
};

#[derive(Clone, Debug, PartialEq, Eq)]
enum GateEvent {
    BeginRecovery,
    FinishRecovery,
    Preview(JournalRecord),
    Commit(JournalRecord, u64),
}

struct RecordingGate {
    events: Rc<RefCell<Vec<GateEvent>>>,
}

impl AppendGate for RecordingGate {
    fn preview(&mut self, record: JournalRecord) -> Result<(), GateError> {
        self.events.borrow_mut().push(GateEvent::Preview(record));
        Ok(())
    }

    fn commit_after_wal(&mut self, record: JournalRecord, lsn: u64) -> Result<(), GateError> {
        self.events
            .borrow_mut()
            .push(GateEvent::Commit(record, lsn));
        Ok(())
    }

    fn begin_recovery(&mut self) -> Result<(), GateError> {
        self.events.borrow_mut().push(GateEvent::BeginRecovery);
        Ok(())
    }

    fn finish_recovery(&mut self) -> Result<bool, GateError> {
        self.events.borrow_mut().push(GateEvent::FinishRecovery);
        Ok(true)
    }
}

struct CommitFailingGate;

impl AppendGate for CommitFailingGate {
    fn preview(&mut self, _record: JournalRecord) -> Result<(), GateError> {
        Ok(())
    }

    fn commit_after_wal(&mut self, _record: JournalRecord, _lsn: u64) -> Result<(), GateError> {
        Err(GateError("test commit failure"))
    }
}

struct ConservativeGate;

impl AppendGate for ConservativeGate {
    fn preview(&mut self, _record: JournalRecord) -> Result<(), GateError> {
        Ok(())
    }

    fn commit_after_wal(&mut self, _record: JournalRecord, _lsn: u64) -> Result<(), GateError> {
        Ok(())
    }

    fn conservative_recovery(&self) -> bool {
        true
    }
}

struct RetrySafeResumeGate;

impl AppendGate for RetrySafeResumeGate {
    fn preview(&mut self, _record: JournalRecord) -> Result<(), GateError> {
        Ok(())
    }

    fn commit_after_wal(&mut self, _record: JournalRecord, _lsn: u64) -> Result<(), GateError> {
        Ok(())
    }

    fn finish_recovery(&mut self) -> Result<bool, GateError> {
        Ok(true)
    }

    fn resume_recovery(&mut self) -> Result<bool, GateError> {
        Ok(true)
    }
}

#[test]
fn append_gate_observes_preview_wal_commit_and_replay() {
    let directory = TestDirectory::new("append-gate-order");
    let events = Rc::new(RefCell::new(Vec::new()));
    let mut broker = Broker::open_with_gate(
        directory.wal(),
        config(2),
        RecordingGate {
            events: Rc::clone(&events),
        },
    )
    .expect("open gated broker");
    events.borrow_mut().clear();

    broker
        .admit(CapabilityId(7), proveai_reference_broker::Digest(1))
        .expect("admit through gate");
    let after_admit = events.borrow().clone();
    assert_eq!(after_admit.len(), 2);
    assert!(matches!(
        &after_admit[0],
        GateEvent::Preview(JournalRecord::Authorize { .. })
    ));
    assert!(matches!(
        &after_admit[1],
        GateEvent::Commit(JournalRecord::Authorize { .. }, 1)
    ));
    drop(broker);

    let replay_events = Rc::new(RefCell::new(Vec::new()));
    let reopened = Broker::open_with_gate(
        directory.wal(),
        config(2),
        RecordingGate {
            events: Rc::clone(&replay_events),
        },
    )
    .expect("replay through gate");
    assert_eq!(reopened.wal_records().len(), 1);
    let replay = replay_events.borrow();
    assert!(matches!(
        &replay[0],
        GateEvent::Preview(JournalRecord::Authorize { .. })
    ));
    assert!(matches!(
        &replay[1],
        GateEvent::Commit(JournalRecord::Authorize { .. }, 1)
    ));
    assert!(matches!(&replay[2], GateEvent::BeginRecovery));
    assert!(matches!(&replay[3], GateEvent::FinishRecovery));
}

#[test]
fn post_wal_gate_failure_poisoned_the_broker() {
    let directory = TestDirectory::new("append-gate-failure");
    let mut broker = Broker::open_with_gate(directory.wal(), config(2), CommitFailingGate)
        .expect("open failing gate");
    assert!(matches!(
        broker.admit(CapabilityId(7), proveai_reference_broker::Digest(1)),
        Err(BrokerError::AppendGate(GateError("test commit failure")))
    ));
    assert_eq!(broker.wal_records().len(), 1);
    assert!(matches!(
        broker.admit(CapabilityId(7), proveai_reference_broker::Digest(2)),
        Err(BrokerError::Crashed)
    ));
}

#[test]
fn conservative_gate_terminalizes_a_restarted_attempt() {
    let directory = TestDirectory::new("append-gate-recovery");
    let spec = RequestSpec::uncontrolled(proveai_reference_broker::Digest(9));
    let request;
    {
        let mut broker = Broker::open_with_gate(directory.wal(), config(2), ConservativeGate)
            .expect("open conservative broker");
        request = broker
            .admit(CapabilityId(7), spec.digest)
            .expect("admit request");
        broker.prepare(request, spec).expect("prepare request");
        broker.set_crash_plan(Some(CrashPlan::once(CrashSite::AfterInvoke)));
        let mut adapter = UncontrolledAdapter::default();
        assert!(matches!(
            broker.run(
                request,
                RetryClass::Uncontrolled.max_attempts(),
                &mut adapter
            ),
            Err(BrokerError::SimulatedCrash(CrashSite::AfterInvoke))
        ));
        assert_eq!(adapter.effect_count(), 1);
    }

    let mut broker = Broker::open_with_gate(directory.wal(), config(2), ConservativeGate)
        .expect("reopen conservative broker");
    assert_eq!(
        broker
            .recovery_decision(request, RetryClass::Uncontrolled.max_attempts())
            .expect("classify interrupted uncontrolled request"),
        RecoveryDecision::Unknown {
            attempt: Some(1),
            reason: UnknownReason::Recovery,
            evidence_ref: 4,
        }
    );
    let mut adapter = UncontrolledAdapter::default();
    assert_eq!(
        broker
            .run(
                request,
                RetryClass::Uncontrolled.max_attempts(),
                &mut adapter
            )
            .expect("recover request"),
        TerminalResult::Unknown {
            attempt: Some(1),
            reason: UnknownReason::Recovery,
        }
    );
    assert_eq!(adapter.effect_count(), 0);
}

#[test]
fn durable_success_precedes_conservative_unknown_recovery() {
    let directory = TestDirectory::new("append-gate-durable-success");
    let spec = RequestSpec::idempotent(Digest(10));
    let request;
    {
        let mut broker = Broker::open_with_gate(directory.wal(), config(2), ConservativeGate)
            .expect("open conservative broker");
        request = broker
            .admit(CapabilityId(7), spec.digest)
            .expect("admit request");
        broker.prepare(request, spec).expect("prepare request");
        broker.set_crash_plan(Some(CrashPlan::once(CrashSite::AfterOutcome)));
        let mut adapter = IdempotentAdapter::default();
        assert!(matches!(
            broker.run(request, RetryClass::Idempotent.max_attempts(), &mut adapter,),
            Err(BrokerError::SimulatedCrash(CrashSite::AfterOutcome))
        ));
        assert_eq!(adapter.mutation_count(), 1);
        assert!(matches!(
            broker.wal_records().last(),
            Some(JournalRecord::Outcome { .. })
        ));
    }

    let mut broker = Broker::open_with_gate(directory.wal(), config(2), ConservativeGate)
        .expect("reopen conservative broker");
    assert_eq!(
        broker
            .recovery_decision(request, RetryClass::Idempotent.max_attempts())
            .expect("classify durable success"),
        RecoveryDecision::Commit {
            attempt: 1,
            value: Value(1),
            outcome_ref: 5,
        }
    );
    let mut adapter = IdempotentAdapter::default();
    assert_eq!(
        broker
            .run(request, RetryClass::Idempotent.max_attempts(), &mut adapter,)
            .expect("resolve durable success"),
        TerminalResult::Committed {
            attempt: 1,
            value: Value(1),
        }
    );
    assert_eq!(adapter.mutation_count(), 0);
    assert!(matches!(
        broker.wal_records().last(),
        Some(JournalRecord::Commit { outcome_ref: 5, .. })
    ));
}

#[test]
fn conclusive_failure_precedes_conservative_unknown_recovery() {
    let directory = TestDirectory::new("append-gate-durable-failure");
    let spec = RequestSpec::uncontrolled(Digest(12));
    let request;
    {
        let mut broker = Broker::open_with_gate(directory.wal(), config(2), ConservativeGate)
            .expect("open conservative broker");
        request = broker
            .admit(CapabilityId(7), spec.digest)
            .expect("admit request");
        broker.prepare(request, spec).expect("prepare request");
        broker.set_crash_plan(Some(CrashPlan::once(CrashSite::AfterOutcome)));
        let mut adapter = UncontrolledAdapter::scripted([Observation::Failure]);
        assert!(matches!(
            broker.run(
                request,
                RetryClass::Uncontrolled.max_attempts(),
                &mut adapter
            ),
            Err(BrokerError::SimulatedCrash(CrashSite::AfterOutcome))
        ));
        assert_eq!(adapter.effect_count(), 1);
    }

    let mut broker = Broker::open_with_gate(directory.wal(), config(2), ConservativeGate)
        .expect("reopen conservative broker");
    assert_eq!(
        broker
            .recovery_decision(request, RetryClass::Uncontrolled.max_attempts())
            .expect("classify durable failure"),
        RecoveryDecision::Fail {
            attempt: 1,
            outcome_ref: 5,
        }
    );
    let mut adapter = UncontrolledAdapter::default();
    assert_eq!(
        broker
            .run(
                request,
                RetryClass::Uncontrolled.max_attempts(),
                &mut adapter
            )
            .expect("resolve durable failure"),
        TerminalResult::Failed { attempt: 1 }
    );
    assert_eq!(adapter.effect_count(), 0);
    assert!(matches!(
        broker.wal_records().last(),
        Some(JournalRecord::Fail { outcome_ref: 5, .. })
    ));
}

#[test]
fn nonconclusive_failure_precedes_conservative_unknown_recovery() {
    let directory = TestDirectory::new("append-gate-nonconclusive-failure");
    let spec = RequestSpec::idempotent(Digest(13));
    let request;
    {
        let mut broker = Broker::open_with_gate(directory.wal(), config(2), ConservativeGate)
            .expect("open conservative broker");
        request = broker
            .admit(CapabilityId(7), spec.digest)
            .expect("admit request");
        broker.prepare(request, spec).expect("prepare request");
        broker.set_crash_plan(Some(CrashPlan::on_occurrence(CrashSite::AfterOutcome, 2)));
        let mut adapter =
            IdempotentAdapter::scripted([Observation::Ambiguous, Observation::Failure]);
        assert!(matches!(
            broker.run(request, RetryClass::Idempotent.max_attempts(), &mut adapter),
            Err(BrokerError::SimulatedCrash(CrashSite::AfterOutcome))
        ));
        assert_eq!(adapter.invocation_count(), 2);
        assert_eq!(adapter.mutation_count(), 1);
    }

    let mut broker = Broker::open_with_gate(directory.wal(), config(2), ConservativeGate)
        .expect("reopen conservative broker");
    assert_eq!(
        broker
            .recovery_decision(request, RetryClass::Idempotent.max_attempts())
            .expect("classify nonconclusive failure"),
        RecoveryDecision::Unknown {
            attempt: Some(2),
            reason: UnknownReason::NonConclusiveFailure,
            evidence_ref: 7,
        }
    );
    let mut adapter = IdempotentAdapter::default();
    assert_eq!(
        broker
            .run(request, RetryClass::Idempotent.max_attempts(), &mut adapter)
            .expect("resolve nonconclusive failure"),
        TerminalResult::Unknown {
            attempt: Some(2),
            reason: UnknownReason::NonConclusiveFailure,
        }
    );
    assert_eq!(adapter.invocation_count(), 0);
    assert_eq!(adapter.mutation_count(), 0);
    assert!(matches!(
        broker.wal_records().last(),
        Some(JournalRecord::Unknown {
            reason: UnknownReason::NonConclusiveFailure,
            evidence_ref: 7,
            ..
        })
    ));
}

#[test]
fn retry_safe_gate_resumes_and_repairs_an_interrupted_attempt() {
    let directory = TestDirectory::new("append-gate-retry-safe-resume");
    let spec = RequestSpec::idempotent(Digest(11));
    let request;
    let mut adapter = IdempotentAdapter::default();
    {
        let mut broker = Broker::open_with_gate(directory.wal(), config(2), RetrySafeResumeGate)
            .expect("open retry-safe broker");
        request = broker
            .admit(CapabilityId(7), spec.digest)
            .expect("admit request");
        broker.prepare(request, spec).expect("prepare request");
        broker.set_crash_plan(Some(CrashPlan::once(CrashSite::AfterInvoke)));
        assert!(matches!(
            broker.run(request, RetryClass::Idempotent.max_attempts(), &mut adapter),
            Err(BrokerError::SimulatedCrash(CrashSite::AfterInvoke))
        ));
        assert_eq!(adapter.invocation_count(), 1);
        assert_eq!(adapter.mutation_count(), 1);
    }

    let mut broker = Broker::open_with_gate(directory.wal(), config(2), RetrySafeResumeGate)
        .expect("reopen retry-safe broker");
    assert_eq!(
        broker
            .recovery_decision(request, RetryClass::Idempotent.max_attempts())
            .expect("classify interrupted retry-safe request"),
        RecoveryDecision::Retry { next_attempt: 2 }
    );
    assert_eq!(
        broker
            .run(request, RetryClass::Idempotent.max_attempts(), &mut adapter)
            .expect("resume request"),
        TerminalResult::Committed {
            attempt: 2,
            value: Value(1),
        }
    );
    assert_eq!(adapter.invocation_count(), 2);
    assert_eq!(adapter.mutation_count(), 1);
    assert!(matches!(
        broker.wal_records().get(4),
        Some(JournalRecord::Outcome {
            observation: proveai_reference_broker::Observation::Ambiguous,
            ..
        })
    ));
}
