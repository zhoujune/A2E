mod common;

use common::{config, deduplicated_spec, idempotent_spec, uncontrolled_spec, TestDirectory};
use proveai_reference_broker::adapter::Adapter;
use proveai_reference_broker::adapters::{
    DeduplicatedAdapter, IdempotentAdapter, UncontrolledAdapter,
};
use proveai_reference_broker::{
    Broker, BrokerError, CapabilityId, CrashPlan, CrashSite, JournalRecord, RequestId, RequestSpec,
    RetryClass, TerminalResult, UnknownReason,
};

const SITES: [CrashSite; 7] = [
    CrashSite::AfterAuthorize,
    CrashSite::AfterPrepare,
    CrashSite::AfterArm,
    CrashSite::AfterStart,
    CrashSite::AfterInvoke,
    CrashSite::AfterOutcome,
    CrashSite::AfterTerminal,
];

fn assert_crash(error: BrokerError, site: CrashSite) {
    assert!(matches!(error, BrokerError::SimulatedCrash(actual) if actual == site));
}

fn exercise<A: Adapter>(site: CrashSite, spec: RequestSpec, adapter: &mut A) -> TerminalResult {
    let directory = TestDirectory::new(&format!("matrix-{site:?}-{:?}", spec.class));
    let request = RequestId(1);

    let mut broker = Broker::open(directory.wal(), config(1)).unwrap();
    if site == CrashSite::AfterAuthorize {
        broker.set_crash_plan(Some(CrashPlan::once(site)));
        assert_crash(
            broker
                .admit(CapabilityId(7), spec.digest)
                .expect_err("admission crash"),
            site,
        );
        drop(broker);
        broker = Broker::open(directory.wal(), config(1)).unwrap();
    } else {
        assert_eq!(broker.admit(CapabilityId(7), spec.digest).unwrap(), request);
    }

    if site == CrashSite::AfterPrepare {
        broker.set_crash_plan(Some(CrashPlan::once(site)));
        assert_crash(
            broker.prepare(request, spec).expect_err("Prepare crash"),
            site,
        );
        drop(broker);
        broker = Broker::open(directory.wal(), config(1)).unwrap();
    } else if broker.phase(request).unwrap() == proveai_reference_broker::Phase::Authorized {
        broker.prepare(request, spec).unwrap();
    }

    if !matches!(site, CrashSite::AfterAuthorize | CrashSite::AfterPrepare) {
        broker.set_crash_plan(Some(CrashPlan::once(site)));
        assert_crash(
            broker
                .run(request, spec.class.max_attempts(), adapter)
                .expect_err("execution crash"),
            site,
        );
        drop(broker);
        broker = Broker::open(directory.wal(), config(1)).unwrap();
    }

    let terminal = broker
        .run(request, spec.class.max_attempts(), adapter)
        .expect("recover and finish");
    assert_eq!(broker.terminal(request).unwrap(), Some(terminal));
    assert_eq!(
        broker
            .wal_records()
            .iter()
            .filter(|record| matches!(
                record,
                JournalRecord::Commit { .. }
                    | JournalRecord::Fail { .. }
                    | JournalRecord::Unknown { .. }
            ))
            .count(),
        1,
        "exactly one terminal record"
    );
    terminal
}

#[test]
fn uncontrolled_crash_matrix_is_conservative() {
    for site in SITES {
        let mut adapter = UncontrolledAdapter::default();
        let terminal = exercise(site, uncontrolled_spec(), &mut adapter);
        if matches!(site, CrashSite::AfterStart | CrashSite::AfterInvoke) {
            assert_eq!(
                terminal,
                TerminalResult::Unknown {
                    attempt: Some(1),
                    reason: UnknownReason::AmbiguousOutcome,
                }
            );
        } else {
            assert!(matches!(terminal, TerminalResult::Committed { .. }));
        }
        let expected_effects = u64::from(site != CrashSite::AfterStart);
        assert_eq!(adapter.effect_count(), expected_effects);
    }
}

#[test]
fn idempotent_crash_matrix_never_duplicates_the_effect() {
    for site in SITES {
        let mut adapter = IdempotentAdapter::default();
        let terminal = exercise(site, idempotent_spec(), &mut adapter);
        assert!(matches!(terminal, TerminalResult::Committed { .. }));
        assert_eq!(adapter.mutation_count(), 1);
    }
}

#[test]
fn deduplicated_crash_matrix_never_duplicates_the_decision() {
    for site in SITES {
        let spec = deduplicated_spec();
        let mut adapter = DeduplicatedAdapter::default();
        let terminal = exercise(site, spec, &mut adapter);
        assert!(matches!(terminal, TerminalResult::Committed { .. }));
        assert_eq!(adapter.mutation_count(), 1);
        assert!(adapter.decision(spec.key.unwrap()).is_some());
    }
}

#[test]
fn matrix_covers_every_required_adapter_class() {
    assert_eq!(uncontrolled_spec().class, RetryClass::Uncontrolled);
    assert_eq!(idempotent_spec().class, RetryClass::Idempotent);
    assert_eq!(deduplicated_spec().class, RetryClass::Deduplicated);
}
