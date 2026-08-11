use vstd::prelude::*;

#[path = "k4_parameterized_commit_mutation.rs"]
pub mod k4_r7_layer;

verus! {

use k4_r7_layer::*;
use k4_r7_layer::k4_r6_layer::k4_r5_layer::k4_r4_layer::k4_r3_layer::k4_r2_layer::k4_r1_layer::k4_r0_layer::k4_layer::{
    k4_idempotent_manifest, k_manifest_config_is_well_formed,
    k_manifest_config_view, k_manifest_wf, KManifestConfig,
};
use k4_r7_layer::k4_r6_layer::k4_r5_layer::k4_r4_layer::k4_r3_layer::k4_r2_layer::k4_r1_layer::k4_r0_layer::k4_layer::k3_layer;
use k4_r7_layer::k4_r6_layer::k4_r5_layer::k4_r4_layer::k4_r3_layer::k4_r2_layer::k4_r1_layer::k4_r0_layer::k4_layer::k3_layer::k2_record_layer::k2_guard_layer::k1_layer::query_layer::c1_layer;
use c1_layer::{append_layer, replay_layer};

// K4-A0 carries the finite manifest view through a bounded append certificate.
// K3's executable append loop remains a fixed-demo compatibility layer; this
// target proves the corresponding manifest trace at the generic B1/C1 boundary.

pub open spec fn k4_a0_request() -> replay_layer::RequestId {
    replay_layer::RequestId { id: 1nat }
}

pub open spec fn k4_a0_capability() -> replay_layer::CapabilityId {
    replay_layer::CapabilityId { id: 1nat }
}

pub open spec fn k4_a0_digest() -> replay_layer::Digest {
    replay_layer::Digest { id: 1nat }
}

pub open spec fn k4_a0_key() -> Option<replay_layer::StableKey> {
    Option::None
}

pub open spec fn k4_a0_value() -> replay_layer::Value {
    replay_layer::Value { id: 1nat }
}

pub open spec fn k4_a0_authorize_record() -> replay_layer::JournalRecord {
    replay_layer::JournalRecord::Authorize {
        request: k4_a0_request(),
        capability: k4_a0_capability(),
        digest: k4_a0_digest(),
    }
}

pub open spec fn k4_a0_prepare_record() -> replay_layer::JournalRecord {
    replay_layer::JournalRecord::Prepare {
        request: k4_a0_request(),
        class: replay_layer::RetryClass::Idempotent,
        digest: k4_a0_digest(),
        key: k4_a0_key(),
        auth_ref: 1nat,
    }
}

pub open spec fn k4_a0_arm_record() -> replay_layer::JournalRecord {
    replay_layer::JournalRecord::Arm {
        request: k4_a0_request(),
        digest: k4_a0_digest(),
        key: k4_a0_key(),
        prepare_ref: 2nat,
    }
}

pub open spec fn k4_a0_start_record() -> replay_layer::JournalRecord {
    replay_layer::JournalRecord::Start {
        request: k4_a0_request(),
        attempt: 1nat,
        digest: k4_a0_digest(),
        key: k4_a0_key(),
        arm_ref: 3nat,
    }
}

pub open spec fn k4_a0_outcome_record() -> replay_layer::JournalRecord {
    replay_layer::JournalRecord::Outcome {
        request: k4_a0_request(),
        attempt: 1nat,
        observation: replay_layer::Observation::Success(k4_a0_value()),
        digest: k4_a0_digest(),
        key: k4_a0_key(),
        start_ref: 4nat,
    }
}

pub open spec fn k4_a0_commit_record() -> replay_layer::JournalRecord {
    replay_layer::JournalRecord::CommitRec {
        request: k4_a0_request(),
        attempt: 1nat,
        value: k4_a0_value(),
        digest: k4_a0_digest(),
        key: k4_a0_key(),
        outcome_ref: 5nat,
    }
}

pub open spec fn k4_a0_records() -> Seq<replay_layer::JournalRecord> {
    Seq::empty()
        .push(k4_a0_authorize_record())
        .push(k4_a0_prepare_record())
        .push(k4_a0_arm_record())
        .push(k4_a0_start_record())
        .push(k4_a0_outcome_record())
        .push(k4_a0_commit_record())
}

pub fn k4_a0_exact_kernel_records()
    -> (records: Vec<k3_layer::KJournalRecord>)
    ensures
        records@.len() == 6nat,
        k3_layer::k_journal_seq_view(records@) == k4_a0_records(),
{
    let mut records = Vec::new();
    records.push(k3_layer::KJournalRecord::Authorize {
        request: 1,
        capability: 1,
        digest: 1,
    });
    records.push(k3_layer::KJournalRecord::Prepare {
        request: 1,
        class: k3_layer::KRetryClass::Idempotent,
        digest: 1,
        key_present: false,
        key: 0,
        auth_ref: 1,
    });
    records.push(k3_layer::KJournalRecord::Arm {
        request: 1,
        digest: 1,
        key_present: false,
        key: 0,
        prepare_ref: 2,
    });
    records.push(k3_layer::KJournalRecord::Start {
        request: 1,
        attempt: 1,
        digest: 1,
        key_present: false,
        key: 0,
        arm_ref: 3,
    });
    records.push(k3_layer::KJournalRecord::Outcome {
        request: 1,
        attempt: 1,
        observation: k3_layer::KObservation::Success { value: 1 },
        digest: 1,
        key_present: false,
        key: 0,
        start_ref: 4,
    });
    records.push(k3_layer::KJournalRecord::Commit {
        request: 1,
        attempt: 1,
        value: 1,
        digest: 1,
        key_present: false,
        key: 0,
        outcome_ref: 5,
    });
    proof {
        reveal_with_fuel(k3_layer::k_journal_seq_view, 8);
    }
    records
}

pub open spec fn k4_a0_append_encode(
    records: Seq<replay_layer::JournalRecord>,
) -> Seq<append_layer::Event<replay_layer::JournalRecord>>
    decreases records.len(),
{
    if records.len() == 0 {
        Seq::empty()
    } else {
        let prefix = records.drop_last();
        let record = records.last();
        k4_a0_append_encode(prefix)
            .push(append_layer::Event::Call { record })
            .push(append_layer::Event::Linearize { record })
            .push(append_layer::Event::ReturnOk { cut: records.len() })
    }
}

pub open spec fn k4_a0_cuts(length: nat) -> Seq<nat>
    decreases length,
{
    if length == 0 {
        Seq::empty()
    } else {
        k4_a0_cuts((length - 1) as nat).push(length)
    }
}

pub open spec fn k4_a0_events()
    -> Seq<append_layer::Event<replay_layer::JournalRecord>>
{
    k4_a0_append_encode(k4_a0_records())
}

pub open spec fn k4_a0_manifest_profile(config: KManifestConfig) -> bool {
    let cfg = k_manifest_config_view(config);
    &&& k_manifest_wf(config)
    &&& cfg.request_capability[k4_a0_request()] == k4_a0_capability()
    &&& cfg.request_class[k4_a0_request()]
        == replay_layer::RetryClass::Idempotent
    &&& cfg.request_digest[k4_a0_request()] == k4_a0_digest()
    &&& cfg.request_key[k4_a0_request()] == k4_a0_key()
    &&& cfg.max_attempts[k4_a0_request()] == 3nat
    &&& cfg.initial_budget[k4_a0_capability()] == 4nat
    &&& cfg.matches.contains((k4_a0_request(), k4_a0_capability()))
    &&& cfg.valid_results.contains((k4_a0_request(), k4_a0_value()))
}

pub proof fn k4_a0_run_push(
    events: Seq<append_layer::Event<replay_layer::JournalRecord>>,
    event: append_layer::Event<replay_layer::JournalRecord>,
)
    ensures
        append_layer::run(events.push(event))
            == append_layer::apply(append_layer::run(events), event),
{
    assert(events.push(event).len() > 0);
    assert(events.push(event).drop_last() =~= events);
    assert(events.push(event).last() == event);
}

pub proof fn k4_a0_append_encode_shape(
    records: Seq<replay_layer::JournalRecord>,
)
    ensures
        append_layer::pi_journal(k4_a0_append_encode(records)) == records,
        append_layer::pi_ack(k4_a0_append_encode(records))
            == k4_a0_cuts(records.len()),
        append_layer::run(k4_a0_append_encode(records)).evidence.records
            == records,
        append_layer::run(k4_a0_append_encode(records)).evidence.ack_cuts
            == k4_a0_cuts(records.len()),
        append_layer::run(k4_a0_append_encode(records)).append is Idle,
    decreases records.len(),
{
    if records.len() == 0 {
        assert(records =~= Seq::empty());
    } else {
        let prefix = records.drop_last();
        let record = records.last();
        let base = k4_a0_append_encode(prefix);
        let call = append_layer::Event::Call { record };
        let linearize = append_layer::Event::Linearize { record };
        let returned = append_layer::Event::ReturnOk {
            cut: records.len(),
        };
        let called = base.push(call);
        let linearized = called.push(linearize);
        let completed = linearized.push(returned);

        k4_a0_append_encode_shape(prefix);
        assert(records =~= prefix.push(record));
        assert(k4_a0_append_encode(records) == completed);

        append_layer::pi_journal_push(base, call);
        append_layer::pi_journal_push(called, linearize);
        append_layer::pi_journal_push(linearized, returned);
        append_layer::pi_ack_push(base, call);
        append_layer::pi_ack_push(called, linearize);
        append_layer::pi_ack_push(linearized, returned);

        k4_a0_run_push(base, call);
        k4_a0_run_push(called, linearize);
        k4_a0_run_push(linearized, returned);
        assert(append_layer::run(called).evidence.records == prefix);
        assert(append_layer::run(linearized).evidence.records
            == prefix.push(record));
        assert(append_layer::run(completed).evidence.records
            == prefix.push(record));
        assert(append_layer::run(completed).append is Idle);
    }
}

pub proof fn k4_a0_admissible_push(
    cfg: replay_layer::Config,
    events: Seq<append_layer::Event<replay_layer::JournalRecord>>,
    event: append_layer::Event<replay_layer::JournalRecord>,
)
    requires
        c1_layer::c1_admissibly_executable(cfg, events),
        append_layer::enabled(append_layer::run(events), event),
        append_layer::record_eligible(
            c1_layer::c1_eligibility(cfg),
            append_layer::run(events),
            event,
        ),
    ensures
        c1_layer::c1_admissibly_executable(cfg, events.push(event)),
{
    assert(events.push(event).len() > 0);
    assert(events.push(event).drop_last() =~= events);
    assert(events.push(event).last() == event);
}

pub proof fn k4_a0_legal_records_encode_admissibly(
    cfg: replay_layer::Config,
    records: Seq<replay_layer::JournalRecord>,
)
    requires
        replay_layer::journal_legal(cfg, records),
    ensures
        c1_layer::c1_admissibly_executable(
            cfg, k4_a0_append_encode(records),
        ),
    decreases records.len(),
{
    if records.len() > 0 {
        let prefix = records.drop_last();
        let record = records.last();
        let base = k4_a0_append_encode(prefix);
        let call = append_layer::Event::Call { record };
        let linearize = append_layer::Event::Linearize { record };
        let returned = append_layer::Event::ReturnOk {
            cut: records.len(),
        };
        let called = base.push(call);
        let linearized = called.push(linearize);
        let completed = linearized.push(returned);

        replay_layer::journal_legal_drop_last(cfg, records);
        replay_layer::journal_legal_last(cfg, records);
        k4_a0_legal_records_encode_admissibly(cfg, prefix);
        k4_a0_append_encode_shape(prefix);
        assert(records =~= prefix.push(record));
        assert(k4_a0_append_encode(records) == completed);

        assert(append_layer::run(base).append is Idle);
        assert(append_layer::enabled(append_layer::run(base), call));
        assert(append_layer::record_eligible(
            c1_layer::c1_eligibility(cfg),
            append_layer::run(base),
            call,
        ));
        k4_a0_admissible_push(cfg, base, call);

        k4_a0_run_push(base, call);
        assert(append_layer::run(called).append is Called);
        assert(append_layer::enabled(
            append_layer::run(called), linearize,
        ));
        assert(append_layer::record_eligible(
            c1_layer::c1_eligibility(cfg),
            append_layer::run(called),
            linearize,
        ));
        k4_a0_admissible_push(cfg, called, linearize);

        k4_a0_run_push(called, linearize);
        assert(append_layer::run(linearized).evidence.records
            == prefix.push(record));
        assert(append_layer::enabled(
            append_layer::run(linearized), returned,
        ));
        assert(append_layer::record_eligible(
            c1_layer::c1_eligibility(cfg),
            append_layer::run(linearized),
            returned,
        ));
        k4_a0_admissible_push(cfg, linearized, returned);
    }
}

pub proof fn k4_a0_manifest_records_legal(config: KManifestConfig)
    requires
        k4_a0_manifest_profile(config),
    ensures
        replay_layer::journal_legal(
            k_manifest_config_view(config), k4_a0_records(),
        ),
{
    let cfg = k_manifest_config_view(config);
    let journal0 = Seq::<replay_layer::JournalRecord>::empty();
    let journal1 = journal0.push(k4_a0_authorize_record());
    let journal2 = journal1.push(k4_a0_prepare_record());
    let journal3 = journal2.push(k4_a0_arm_record());
    let journal4 = journal3.push(k4_a0_start_record());
    let journal5 = journal4.push(k4_a0_outcome_record());

    k_manifest_config_is_well_formed(config);
    reveal_with_fuel(replay_layer::replay, 8);
    reveal_with_fuel(replay_layer::authorize_lsn, 8);
    reveal_with_fuel(replay_layer::prepare_lsn, 8);
    reveal_with_fuel(replay_layer::arm_lsn, 8);
    reveal_with_fuel(replay_layer::start_lsn, 8);
    reveal_with_fuel(replay_layer::outcome_lsn, 8);
    reveal_with_fuel(replay_layer::started_count, 8);
    reveal_with_fuel(replay_layer::outcome_count, 8);
    reveal_with_fuel(replay_layer::outcome_observation, 8);
    assert(replay_layer::journal_legal(cfg, journal0));

    assert(replay_layer::structural_enabled(
        cfg, journal0, k4_a0_authorize_record(),
    ));
    replay_layer::journal_legal_push(
        cfg, journal0, k4_a0_authorize_record(),
    );

    assert(replay_layer::structural_enabled(
        cfg, journal1, k4_a0_prepare_record(),
    ));
    replay_layer::journal_legal_push(
        cfg, journal1, k4_a0_prepare_record(),
    );

    assert(replay_layer::structural_enabled(
        cfg, journal2, k4_a0_arm_record(),
    ));
    replay_layer::journal_legal_push(
        cfg, journal2, k4_a0_arm_record(),
    );

    replay_layer::replay_domains(cfg, journal3);
    assert(replay_layer::replay(cfg, journal3).phase[k4_a0_request()]
        == replay_layer::Phase::Armed);
    assert(replay_layer::request_fields_match(
        cfg, k4_a0_request(), k4_a0_digest(), k4_a0_key(),
    ));
    assert(replay_layer::started_count(journal3, k4_a0_request()) == 0nat);
    assert(!replay_layer::failure_conclusive(
        cfg, journal3, k4_a0_request(),
    ));
    assert(replay_layer::arm_lsn(journal3, k4_a0_request())
        == Option::Some(3nat));
    assert(replay_layer::structural_enabled(
        cfg, journal3, k4_a0_start_record(),
    ));
    replay_layer::journal_legal_push(
        cfg, journal3, k4_a0_start_record(),
    );

    replay_layer::replay_domains(cfg, journal4);
    assert(replay_layer::replay(cfg, journal4).phase[k4_a0_request()]
        == replay_layer::Phase::Armed);
    assert(replay_layer::started_count(journal4, k4_a0_request()) == 1nat);
    assert(replay_layer::outcome_count(
        journal4, k4_a0_request(), 1nat,
    ) == 0nat);
    assert(replay_layer::start_lsn(
        journal4, k4_a0_request(), 1nat,
    ) == Option::Some(4nat));
    assert(replay_layer::success_is_valid(
        cfg,
        k4_a0_request(),
        replay_layer::Observation::Success(k4_a0_value()),
    ));
    assert(replay_layer::structural_enabled(
        cfg, journal4, k4_a0_outcome_record(),
    ));
    replay_layer::journal_legal_push(
        cfg, journal4, k4_a0_outcome_record(),
    );

    replay_layer::replay_domains(cfg, journal5);
    assert(replay_layer::replay(cfg, journal5).phase[k4_a0_request()]
        == replay_layer::Phase::Armed);
    assert(replay_layer::started_count(journal5, k4_a0_request()) == 1nat);
    assert(replay_layer::outcome_observation(
        journal5, k4_a0_request(), 1nat,
    ) == Option::Some(
        replay_layer::Observation::Success(k4_a0_value()),
    ));
    assert(replay_layer::outcome_lsn(
        journal5, k4_a0_request(), 1nat,
    ) == Option::Some(5nat));
    assert(replay_layer::structural_enabled(
        cfg, journal5, k4_a0_commit_record(),
    ));
    replay_layer::journal_legal_push(
        cfg, journal5, k4_a0_commit_record(),
    );
    assert(k4_a0_records()
        == journal5.push(k4_a0_commit_record()));
}

pub proof fn k4_a0_manifest_admissible(config: KManifestConfig)
    requires
        k4_a0_manifest_profile(config),
    ensures
        c1_layer::c1_admissibly_executable(
            k_manifest_config_view(config),
            k4_a0_events(),
        ),
{
    k_manifest_config_is_well_formed(config);
    k4_a0_manifest_records_legal(config);
    k4_a0_legal_records_encode_admissibly(
        k_manifest_config_view(config),
        k4_a0_records(),
    );
}

pub proof fn k4_a0_manifest_append_certificate(config: KManifestConfig)
    requires
        k4_a0_manifest_profile(config),
    ensures
        c1_layer::c1_checkpoint(
            k_manifest_config_view(config),
            k4_a0_events(),
        ),
        c1_layer::c1_admissibly_executable(
            k_manifest_config_view(config),
            k4_a0_events(),
        ),
        replay_layer::journal_legal(
            k_manifest_config_view(config),
            k4_a0_records(),
        ),
        append_layer::pi_journal(k4_a0_events()) == k4_a0_records(),
        append_layer::pi_ack(k4_a0_events())
            == Seq::empty().push(1nat).push(2nat).push(3nat)
                .push(4nat).push(5nat).push(6nat),
        append_layer::run(k4_a0_events()).evidence.records
            == k4_a0_records(),
        replay_layer::replay(
            k_manifest_config_view(config), k4_a0_records(),
        ).phase[k4_a0_request()] == replay_layer::Phase::Committed,
        replay_layer::replay(
            k_manifest_config_view(config), k4_a0_records(),
        ).committed[k4_a0_request()]
            == Option::Some(replay_layer::CommittedValue {
                attempt: 1nat,
                value: k4_a0_value(),
            }),
{
    k_manifest_config_is_well_formed(config);
    k4_a0_manifest_admissible(config);
    c1_layer::c1_legal_append_replay(
        k_manifest_config_view(config),
        k4_a0_events(),
    );
    k4_a0_append_encode_shape(k4_a0_records());
    reveal_with_fuel(k4_a0_cuts, 8);
    reveal_with_fuel(replay_layer::replay, 8);
    assert(append_layer::pi_journal(k4_a0_events()) == k4_a0_records());
    assert(append_layer::pi_ack(k4_a0_events())
        == Seq::empty().push(1nat).push(2nat).push(3nat)
            .push(4nat).push(5nat).push(6nat));
    assert(append_layer::run(k4_a0_events()).evidence.records
        == append_layer::pi_journal(k4_a0_events()));
}

pub proof fn k4_a0_manifest_all_prefixes(config: KManifestConfig)
    requires
        k4_a0_manifest_profile(config),
    ensures
        forall|length: int| 0 <= length <= k4_a0_events().len()
            ==> #[trigger] c1_layer::c1_checkpoint(
                k_manifest_config_view(config),
                k4_a0_events().take(length),
            ),
{
    k_manifest_config_is_well_formed(config);
    k4_a0_manifest_admissible(config);
    c1_layer::c1_all_prefixes(
        k_manifest_config_view(config),
        k4_a0_events(),
    );
}

pub fn k4_a0_manifest_append_witness()
    -> (result: (bool, bool, u64, usize, u64, usize, u64))
    ensures
        result == (true, true, 1u64, 1usize, 3u64, 6usize, 6u64),
        exists|config: KManifestConfig|
            k4_a0_manifest_profile(config)
                && c1_layer::c1_checkpoint(
                    k_manifest_config_view(config), k4_a0_events(),
                )
                && replay_layer::replay(
                    k_manifest_config_view(config), k4_a0_records(),
                ).phase[k4_a0_request()] == replay_layer::Phase::Committed,
{
    let config = k4_idempotent_manifest();
    let mutation = k4_idempotent_commit_mutation_witness();
    let records = k4_a0_exact_kernel_records();
    proof {
        assert(k4_a0_manifest_profile(config));
        k4_a0_manifest_append_certificate(config);
        assert(exists|candidate: KManifestConfig|
            k4_a0_manifest_profile(candidate)
                && c1_layer::c1_checkpoint(
                    k_manifest_config_view(candidate), k4_a0_events(),
                )
                && replay_layer::replay(
                    k_manifest_config_view(candidate), k4_a0_records(),
                ).phase[k4_a0_request()] == replay_layer::Phase::Committed);
    }
    (
        mutation.0,
        mutation.1,
        mutation.2,
        mutation.3,
        mutation.4,
        records.len(),
        6u64,
    )
}

} // verus!
