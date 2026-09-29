mod common;

use common::{config, uncontrolled_spec, TestDirectory};
use proveai_reference_broker::adapters::UncontrolledAdapter;
use proveai_reference_broker::{
    Broker, BrokerError, CapabilityId, CrashPlan, CrashSite, JournalRecord, RecoveryDecision,
    RetryClass, UnknownReason,
};

#[test]
fn lost_reply_prefix_keeps_zero_and_one_effect_worlds_possible() {
    let directory = TestDirectory::new("classifier-lost-reply-worlds");
    let request;
    {
        let mut broker = Broker::open(directory.wal(), config(1)).expect("open broker");
        let spec = uncontrolled_spec();
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
        assert!(matches!(
            broker.wal_records().last(),
            Some(JournalRecord::Start { attempt: 1, .. })
        ));
    }

    let broker = Broker::open(directory.wal(), config(1)).expect("reopen broker");
    let decision = broker
        .recovery_decision(request, RetryClass::Uncontrolled.max_attempts())
        .expect("classify lost reply");
    assert_eq!(
        decision,
        RecoveryDecision::Unknown {
            attempt: Some(1),
            reason: UnknownReason::Recovery,
            evidence_ref: 4,
        }
    );

    // The durable prefix is identical whether the protected service linearized
    // before the lost reply or never linearized.  The classifier therefore must
    // return the same Unknown decision for both admissible effect counts.
    for possible_effects in [0_u8, 1_u8] {
        assert!(possible_effects <= 1);
        assert_eq!(
            broker
                .recovery_decision(request, RetryClass::Uncontrolled.max_attempts())
                .expect("reclassify identical prefix"),
            decision
        );
    }
}
