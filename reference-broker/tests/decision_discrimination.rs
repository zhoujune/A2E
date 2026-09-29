//! Separate service process; broker crashes use fault injection, not OS kills.
mod common;
use common::{config, idempotent_spec, TestDirectory};
use proveai_reference_broker::{
    Adapter, Broker, BrokerError, CapabilityId, CrashPlan, CrashSite, Delivery, Invocation,
    JournalRecord, Observation, RetryClass, TerminalResult, UnknownReason, Value,
};
use std::{
    fs::{self, OpenOptions},
    io::Write,
    path::PathBuf,
    process::Command,
};

#[test]
fn service_worker() {
    let Some(path) = std::env::var_os("PROVEAI_TEST_SERVICE_MARKER") else {
        return;
    };
    if std::env::var("PROVEAI_TEST_SERVICE_ACTION").unwrap() == "apply" {
        match OpenOptions::new().write(true).create_new(true).open(path) {
            Ok(mut f) => {
                f.write_all(b"member-present").unwrap();
                f.sync_all().unwrap();
            }
            Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => (),
            Err(e) => panic!("service write: {e}"),
        }
    }
}

struct Service {
    marker: PathBuf,
    reject: bool,
    calls: usize,
}
impl Adapter for Service {
    fn retry_class(&self) -> RetryClass {
        RetryClass::Idempotent
    }
    fn invoke(&mut self, invocation: Invocation) -> Delivery {
        self.calls += 1;
        let output = Command::new(std::env::current_exe().unwrap())
            .args(["--exact", "service_worker", "--nocapture"])
            .env("PROVEAI_TEST_SERVICE_MARKER", &self.marker)
            .env(
                "PROVEAI_TEST_SERVICE_ACTION",
                if self.reject { "reject" } else { "apply" },
            )
            .output()
            .unwrap();
        assert!(output.status.success(), "service failed: {:?}", output);
        Delivery {
            invocation: invocation.id,
            observation: if self.reject {
                Observation::Failure
            } else {
                Observation::Success(Value(1))
            },
        }
    }
}
fn effects(service: &Service) -> u8 {
    match fs::read(&service.marker) {
        Ok(bytes) => {
            assert_eq!(bytes, b"member-present");
            1
        }
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => 0,
        Err(e) => panic!("oracle read: {e}"),
    }
}
fn last_response(records: &[JournalRecord]) -> Observation {
    records
        .iter()
        .rev()
        .find_map(|r| match r {
            JournalRecord::Outcome { observation, .. } => Some(*observation),
            _ => None,
        })
        .expect("retained response")
}

fn interrupted(site: CrashSite) -> (Vec<JournalRecord>, Vec<JournalRecord>, TerminalResult, u8) {
    let dir = TestDirectory::new("decision-discrimination");
    let mut service = Service {
        marker: dir.wal().with_file_name("service.state"),
        reject: false,
        calls: 0,
    };
    let mut broker = Broker::open(dir.wal(), config(1)).unwrap();
    let spec = idempotent_spec();
    let request = broker.admit(CapabilityId(7), spec.digest).unwrap();
    broker.prepare(request, spec).unwrap();
    broker.set_crash_plan(Some(CrashPlan::once(site)));
    assert!(
        matches!(broker.run(request, 3, &mut service), Err(BrokerError::SimulatedCrash(s)) if s == site)
    );
    let prefix = broker.wal_records().to_vec();
    drop(broker);
    let expected = u8::from(site == CrashSite::AfterInvoke);
    assert_eq!(effects(&service), expected);
    // Reconstruct the client; the child-owned state survives independently.
    let mut service = Service {
        marker: service.marker,
        reject: true,
        calls: 0,
    };
    let mut broker = Broker::open(dir.wal(), config(1)).unwrap();
    // Recovery first records Ambiguous for the interrupted attempt.
    broker.set_crash_plan(Some(CrashPlan::on_occurrence(CrashSite::AfterOutcome, 2)));
    assert!(matches!(
        broker.run(request, 3, &mut service),
        Err(BrokerError::SimulatedCrash(CrashSite::AfterOutcome))
    ));
    let decision_prefix = broker.wal_records().to_vec();
    assert_eq!(last_response(&decision_prefix), Observation::Failure);
    drop(broker);
    let mut broker = Broker::open(dir.wal(), config(1)).unwrap();
    let terminal = broker.run(request, 3, &mut service).unwrap();
    assert_eq!(service.calls, 1);
    assert_eq!(effects(&service), expected);
    (prefix, decision_prefix, terminal, expected)
}

#[test]
fn identical_evidence_with_zero_and_one_effect_rejects_last_response_wins() {
    let zero = interrupted(CrashSite::AfterStart);
    let one = interrupted(CrashSite::AfterInvoke);
    assert_eq!(zero.0, one.0, "same initial durable prefix");
    assert_eq!(
        zero.1, one.1,
        "same pre-terminal evidence after rejected retry"
    );
    assert_eq!(zero.3, 0);
    assert_eq!(one.3, 1);
    let expected = TerminalResult::Unknown {
        attempt: Some(2),
        reason: UnknownReason::NonConclusiveFailure,
    };
    assert_eq!(zero.2, expected);
    assert_eq!(one.2, expected);
    // A response-only Fail is unsafe in the second run (the marker exists).
    assert_eq!(last_response(&one.1), Observation::Failure);
    assert_ne!(one.3, 0, "counterexample to response-only Fail");
    println!("DISCRIMINATION|uninvoked_then_rejected|0|Unknown|Fail");
    println!("DISCRIMINATION|effect_then_rejected|1|Unknown|Fail");
}

#[test]
fn conclusive_controls_do_not_degenerate_to_always_unknown() {
    for reject in [false, true] {
        let dir = TestDirectory::new("decision-controls");
        let mut service = Service {
            marker: dir.wal().with_file_name("service.state"),
            reject,
            calls: 0,
        };
        let mut broker = Broker::open(dir.wal(), config(1)).unwrap();
        let spec = idempotent_spec();
        let request = broker.admit(CapabilityId(7), spec.digest).unwrap();
        broker.prepare(request, spec).unwrap();
        let terminal = broker.run(request, 3, &mut service).unwrap();
        let expected = if reject {
            TerminalResult::Failed { attempt: 1 }
        } else {
            TerminalResult::Committed {
                attempt: 1,
                value: Value(1),
            }
        };
        assert_eq!(terminal, expected);
        assert_eq!(effects(&service), u8::from(!reject));
        assert_eq!(service.calls, 1);
        drop(broker);
        let mut reopened = Broker::open(dir.wal(), config(1)).unwrap();
        assert_eq!(reopened.run(request, 3, &mut service).unwrap(), expected);
        assert_eq!(service.calls, 1);
        println!(
            "DISCRIMINATION|{}|{}|{}|{}",
            if reject {
                "conclusive_failure"
            } else {
                "success"
            },
            effects(&service),
            if reject { "Fail" } else { "Commit" },
            if reject { "Fail" } else { "Commit" }
        );
    }
}
