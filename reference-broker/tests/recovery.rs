mod common;

use common::{config, idempotent_spec, TestDirectory};
use proveai_reference_broker::adapters::IdempotentAdapter;
use proveai_reference_broker::wal::FileWal;
use proveai_reference_broker::{
    Broker, BrokerError, CapabilityId, CrashPlan, CrashSite, DedupKey, Digest, JournalRecord,
    Observation, RequestId, RetryClass, TerminalResult, UnknownReason, Value,
};

#[test]
fn torn_final_frame_is_discarded_and_file_is_reusable() {
    let directory = TestDirectory::new("torn-tail");
    let wal_path = directory.wal();
    let authorize = JournalRecord::Authorize {
        request: RequestId(1),
        capability: CapabilityId(7),
        digest: Digest(5),
    };
    let mut wal = FileWal::open(&wal_path).unwrap().0;
    wal.append(authorize).unwrap();
    let full_length = wal
        .append_torn_frame(
            JournalRecord::Revoke {
                capability: CapabilityId(7),
            },
            11,
        )
        .unwrap();
    drop(wal);

    let (mut recovered, report) = FileWal::open(&wal_path).expect("repair torn tail");
    assert_eq!(recovered.records(), &[authorize]);
    assert_eq!(report.records, 1);
    assert_eq!(report.discarded_tail_bytes, 11);
    assert!(full_length > report.discarded_tail_bytes as usize);
    recovered
        .append(JournalRecord::Revoke {
            capability: CapabilityId(7),
        })
        .expect("append after repair");
    drop(recovered);
    assert_eq!(FileWal::open(&wal_path).unwrap().0.records().len(), 2);
}

#[test]
fn all_nine_record_variants_round_trip_exactly() {
    let directory = TestDirectory::new("record-codec");
    let records = [
        JournalRecord::Authorize {
            request: RequestId(1),
            capability: CapabilityId(7),
            digest: Digest(10),
        },
        JournalRecord::Revoke {
            capability: CapabilityId(7),
        },
        JournalRecord::Prepare {
            request: RequestId(1),
            class: RetryClass::Deduplicated,
            digest: Digest(10),
            key: Some(DedupKey(20)),
            auth_ref: 1,
        },
        JournalRecord::Arm {
            request: RequestId(1),
            digest: Digest(10),
            key: Some(DedupKey(20)),
            prepare_ref: 3,
        },
        JournalRecord::Start {
            request: RequestId(1),
            attempt: 1,
            digest: Digest(10),
            key: Some(DedupKey(20)),
            arm_ref: 4,
        },
        JournalRecord::Outcome {
            request: RequestId(1),
            attempt: 1,
            observation: Observation::InvalidResult(Value(30)),
            digest: Digest(10),
            key: Some(DedupKey(20)),
            start_ref: 5,
        },
        JournalRecord::Commit {
            request: RequestId(1),
            attempt: 1,
            value: Value(30),
            digest: Digest(10),
            key: Some(DedupKey(20)),
            outcome_ref: 6,
        },
        JournalRecord::Fail {
            request: RequestId(1),
            attempt: 1,
            digest: Digest(10),
            key: Some(DedupKey(20)),
            outcome_ref: 6,
        },
        JournalRecord::Unknown {
            request: RequestId(1),
            attempt: Some(1),
            reason: UnknownReason::InvalidResult,
            digest: Digest(10),
            key: Some(DedupKey(20)),
            evidence_ref: 6,
        },
    ];
    let mut wal = FileWal::open(directory.wal()).unwrap().0;
    for record in records {
        wal.append(record).unwrap();
    }
    drop(wal);
    assert_eq!(
        FileWal::open(directory.wal()).unwrap().0.records(),
        &records
    );
}

#[test]
fn terminal_append_survives_lost_return() {
    let directory = TestDirectory::new("terminal-replay");
    let request;
    {
        let mut broker = Broker::open(directory.wal(), config(1)).unwrap();
        request = broker
            .admit(CapabilityId(7), idempotent_spec().digest)
            .unwrap();
        broker.prepare(request, idempotent_spec()).unwrap();
        broker.set_crash_plan(Some(CrashPlan::once(CrashSite::AfterTerminal)));
        let mut adapter = IdempotentAdapter::default();
        assert!(matches!(
            broker.run(request, 2, &mut adapter),
            Err(BrokerError::SimulatedCrash(CrashSite::AfterTerminal))
        ));
        assert_eq!(adapter.mutation_count(), 1);
    }

    let mut recovered = Broker::open(directory.wal(), config(1)).unwrap();
    let expected = TerminalResult::Committed {
        attempt: 1,
        value: Value(1),
    };
    assert_eq!(recovered.terminal(request).unwrap(), Some(expected));
    let mut unused_adapter = IdempotentAdapter::default();
    assert_eq!(
        recovered.run(request, 2, &mut unused_adapter).unwrap(),
        expected
    );
    assert_eq!(unused_adapter.mutation_count(), 0);
}
