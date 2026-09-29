use vstd::prelude::*;

#[path = "k4_generic_append_state_bridge.rs"]
pub mod k4_a2_layer;

verus! {

use k4_a2_layer::*;
use k4_a2_layer::k4_a1_layer::k4_a0_layer::{
    k4_a0_manifest_profile, k4_a0_manifest_records_legal,
    k4_a0_records, k4_a0_request,
};
use k4_a2_layer::k4_a1_layer::k4_a0_layer::k4_r7_layer::k4_r6_layer::k4_r5_layer::k4_r4_layer::k4_r3_layer::k4_r2_layer::k4_r1_layer::{
    k_manifest_attempt_profile, k_manifest_fields_match,
};
use k4_a2_layer::k4_a1_layer::k4_a0_layer::k4_r7_layer::k4_r6_layer::k4_r5_layer::k4_r4_layer::k4_r3_layer::k4_r2_layer::k4_r1_layer::k4_r0_layer::k4_layer::{
    k_manifest_binding_lookup, k_manifest_capability_lookup,
    k_manifest_config_is_well_formed, k_manifest_config_view,
    k_manifest_wf,
};
use k4_a2_layer::k4_a1_layer::k4_a0_layer::k4_r7_layer::k4_r6_layer::k4_r5_layer::k4_r4_layer::k4_r3_layer::k4_r2_layer::k4_r1_layer::k4_r0_layer::k4_layer::k3_layer;
use k3_layer::*;
use k3_layer::k2_record_layer::{
    k_phase_delta, k_phase_record_delta_refines_apply_record,
    k_phase_record_shape, k_set_request_phase, k_update_inv,
    k_update_inv_lifts_through_replay_push,
};
use k3_layer::k2_record_layer::k2_guard_layer::{
    k_attempt_is_latest, k_attempt_view, k_key_view, k_latest_outcome,
    k_phase_view_reflects, k_uncertain, k_unknown_reason_view,
};
use k3_layer::k2_record_layer::k2_guard_layer::k1_layer::{
    k_digest_id, k_durable_inv, k_failure_conclusive, k_find_request,
    k_outcome_view, k_phase_view, k_request_entry_couples, k_request_id,
    k_tracks_request, k_has_durable_success_couples, k_has_durable_success_exec,
    KDurable, KPhase, KRequestEntry,
};
use k3_layer::k2_record_layer::k2_guard_layer::k1_layer::query_layer;
use query_layer::c1_layer;
use query_layer::c1_layer::{append_layer, replay_layer};

pub use k3_layer::KUnknownReason;

// K4-A3 extends A2 with the terminal records whose guards encode the
// recovery classification. Concrete crash/restart control remains an A4
// obligation; Recovery here is the durable Unknown terminal reason.
pub open spec fn k4_a3_supported(record: KJournalRecord) -> bool {
    match record {
        KJournalRecord::Revoke { .. } => false,
        KJournalRecord::Authorize { .. }
        | KJournalRecord::Prepare { .. }
        | KJournalRecord::Arm { .. }
        | KJournalRecord::Start { .. }
        | KJournalRecord::Outcome { .. }
        | KJournalRecord::Commit { .. }
        | KJournalRecord::Fail { .. }
        | KJournalRecord::Unknown { .. } => true,
    }
}

pub fn k4_a3_supported_exec(record: &KJournalRecord) -> (supported: bool)
    ensures
        supported == k4_a3_supported(*record),
{
    match *record {
        KJournalRecord::Revoke { .. } => false,
        KJournalRecord::Authorize { .. }
        | KJournalRecord::Prepare { .. }
        | KJournalRecord::Arm { .. }
        | KJournalRecord::Start { .. }
        | KJournalRecord::Outcome { .. }
        | KJournalRecord::Commit { .. }
        | KJournalRecord::Fail { .. }
        | KJournalRecord::Unknown { .. } => true,
    }
}

pub open spec fn k4_a3_inv(
    config: KManifestConfig,
    state: KKernelState,
) -> bool {
    k4_a2_inv(config, state)
}

pub open spec fn k4_a3_fail_outcome_record()
    -> replay_layer::JournalRecord
{
    replay_layer::JournalRecord::Outcome {
        request: k4_a0_request(),
        attempt: 1nat,
        observation: replay_layer::Observation::Failure,
        digest: replay_layer::Digest { id: 1nat },
        key: Option::None,
        start_ref: 4nat,
    }
}

pub open spec fn k4_a3_fail_record() -> replay_layer::JournalRecord {
    replay_layer::JournalRecord::FailRec {
        request: k4_a0_request(),
        attempt: 1nat,
        digest: replay_layer::Digest { id: 1nat },
        key: Option::None,
        outcome_ref: 5nat,
    }
}

pub open spec fn k4_a3_fail_records()
    -> Seq<replay_layer::JournalRecord>
{
    k4_a0_records().take(4)
        .push(k4_a3_fail_outcome_record())
        .push(k4_a3_fail_record())
}

pub open spec fn k4_a3_uncontrolled_profile(
    config: KManifestConfig,
) -> bool {
    let cfg = k_manifest_config_view(config);
    let request = replay_layer::RequestId { id: 1nat };
    let capability = replay_layer::CapabilityId { id: 1nat };
    &&& k_manifest_wf(config)
    &&& cfg.request_capability[request] == capability
    &&& cfg.request_class[request]
        == replay_layer::RetryClass::Uncontrolled
    &&& cfg.request_digest[request] == replay_layer::Digest { id: 1nat }
    &&& cfg.request_key[request]
        == Option::<replay_layer::StableKey>::None
    &&& cfg.max_attempts[request] == 1nat
    &&& cfg.initial_budget[capability] == 1nat
    &&& cfg.matches.contains((request, capability))
}

pub fn k4_a3_uncontrolled_manifest() -> (config: KManifestConfig)
    ensures
        k4_a3_uncontrolled_profile(config),
        replay_layer::config_wf(k_manifest_config_view(config)),
        k_manifest_capability_lookup(config.capabilities@, 1)
            == Option::Some(KManifestCapability {
                capability: 1,
                initial_budget: 1,
            }),
        k_manifest_binding_lookup(config.bindings@, 1)
            == Option::Some(KManifestBinding {
                request: 1,
                capability: 1,
                class: KRetryClass::Uncontrolled,
                digest: 1,
                key_present: false,
                key: 0,
            }),
{
    let mut capabilities = Vec::new();
    capabilities.push(KManifestCapability {
        capability: 1,
        initial_budget: 1,
    });
    let mut bindings = Vec::new();
    bindings.push(KManifestBinding {
        request: 1,
        capability: 1,
        class: KRetryClass::Uncontrolled,
        digest: 1,
        key_present: false,
        key: 0,
    });
    let config = KManifestConfig { capabilities, bindings };
    proof {
        assert(config.bindings@.len() == 1);
        assert forall|index: int|
            0 <= index < config.bindings@.len() implies {
                let entry = #[trigger] config.bindings@[index];
                &&& entry.request > 0
                &&& (entry.class == KRetryClass::Deduplicated
                    <==> entry.key_present)
                &&& k_manifest_capability_lookup(
                    config.capabilities@, entry.capability as nat,
                ).is_some()
            } by {
            assert(index == 0);
        }
        assert forall|index: int|
            0 <= index < config.capabilities@.len()
                implies #[trigger]
                    config.capabilities@[index].capability > 0 by {
            assert(index == 0);
        }
        assert forall|left: int, right: int|
            0 <= left < config.capabilities@.len()
                && 0 <= right < config.capabilities@.len()
                && #[trigger] config.capabilities@[left].capability
                    == #[trigger] config.capabilities@[right].capability
            implies left == right by {
            assert(left == 0);
            assert(right == 0);
        }
        assert forall|left: int, right: int|
            0 <= left < config.bindings@.len()
                && 0 <= right < config.bindings@.len()
                && #[trigger] config.bindings@[left].request
                    == #[trigger] config.bindings@[right].request
            implies left == right by {
            assert(left == 0);
            assert(right == 0);
        }
        assert forall|left: int, right: int|
            0 <= left < config.bindings@.len()
                && 0 <= right < config.bindings@.len()
                && #[trigger] config.bindings@[left].class
                    == KRetryClass::Deduplicated
                && #[trigger] config.bindings@[right].class
                    == KRetryClass::Deduplicated
                && config.bindings@[left].key
                    == config.bindings@[right].key
            implies config.bindings@[left].request
                == config.bindings@[right].request by {
            assert(left == 0);
            assert(config.bindings@[left].class
                == KRetryClass::Uncontrolled);
        }
        assert(k_manifest_wf(config));
        k_manifest_config_is_well_formed(config);
        assert(k4_a3_uncontrolled_profile(config));
    }
    config
}

pub open spec fn k4_a3_recovery_authorize_record()
    -> replay_layer::JournalRecord
{
    replay_layer::JournalRecord::Authorize {
        request: replay_layer::RequestId { id: 1nat },
        capability: replay_layer::CapabilityId { id: 1nat },
        digest: replay_layer::Digest { id: 1nat },
    }
}

pub open spec fn k4_a3_recovery_prepare_record()
    -> replay_layer::JournalRecord
{
    replay_layer::JournalRecord::Prepare {
        request: replay_layer::RequestId { id: 1nat },
        class: replay_layer::RetryClass::Uncontrolled,
        digest: replay_layer::Digest { id: 1nat },
        key: Option::None,
        auth_ref: 1nat,
    }
}

pub open spec fn k4_a3_recovery_arm_record()
    -> replay_layer::JournalRecord
{
    replay_layer::JournalRecord::Arm {
        request: replay_layer::RequestId { id: 1nat },
        digest: replay_layer::Digest { id: 1nat },
        key: Option::None,
        prepare_ref: 2nat,
    }
}

pub open spec fn k4_a3_recovery_start_record()
    -> replay_layer::JournalRecord
{
    replay_layer::JournalRecord::Start {
        request: replay_layer::RequestId { id: 1nat },
        attempt: 1nat,
        digest: replay_layer::Digest { id: 1nat },
        key: Option::None,
        arm_ref: 3nat,
    }
}

pub open spec fn k4_a3_recovery_unknown_record()
    -> replay_layer::JournalRecord
{
    replay_layer::JournalRecord::UnknownRec {
        request: replay_layer::RequestId { id: 1nat },
        attempt: Option::Some(1nat),
        reason: replay_layer::UnknownReason::Recovery,
        digest: replay_layer::Digest { id: 1nat },
        key: Option::None,
        evidence_ref: 4nat,
    }
}

pub open spec fn k4_a3_recovery_records()
    -> Seq<replay_layer::JournalRecord>
{
    Seq::empty()
        .push(k4_a3_recovery_authorize_record())
        .push(k4_a3_recovery_prepare_record())
        .push(k4_a3_recovery_arm_record())
        .push(k4_a3_recovery_start_record())
        .push(k4_a3_recovery_unknown_record())
}

// The four-record prefix is the durable view after an armed invocation whose
// reply was lost.  The Journal cannot distinguish a service that linearized
// from one that did not, so the abstract effect cardinality intentionally has
// both interpretations.
pub open spec fn k4_a3_lost_reply_prefix()
    -> Seq<replay_layer::JournalRecord>
{
    k4_a3_recovery_records().take(4)
}

pub open spec fn k4_a3_lost_reply_effect_worlds() -> Seq<nat> {
    Seq::empty().push(0nat).push(1nat)
}

pub open spec fn k4_a3_unknown_effect_cardinality_allowed(
    effect_count: nat,
) -> bool {
    effect_count == 0nat || effect_count == 1nat
}

pub proof fn k4_a3_lost_reply_indistinguishable_worlds(
    config: KManifestConfig,
)
    requires
        k4_a3_uncontrolled_profile(config),
    ensures
        replay_layer::journal_legal(
            k_manifest_config_view(config), k4_a3_lost_reply_prefix(),
        ),
        replay_layer::replay(
            k_manifest_config_view(config), k4_a3_lost_reply_prefix(),
        ).phase[k4_a0_request()] == replay_layer::Phase::Armed,
        replay_layer::evidence_complete_decision(
            k_manifest_config_view(config), k4_a3_lost_reply_prefix(),
            k4_a0_request(),
        ) == replay_layer::EvidenceDecision::Unknown,
        k4_a3_lost_reply_effect_worlds().len() == 2,
        k4_a3_lost_reply_effect_worlds()[0] == 0,
        k4_a3_lost_reply_effect_worlds()[1] == 1,
        k4_a3_unknown_effect_cardinality_allowed(
            k4_a3_lost_reply_effect_worlds()[0],
        ),
        k4_a3_unknown_effect_cardinality_allowed(
            k4_a3_lost_reply_effect_worlds()[1],
        ),
        k4_a3_lost_reply_effect_worlds()[0]
            != k4_a3_lost_reply_effect_worlds()[1],
{
    let cfg = k_manifest_config_view(config);
    let prefix = k4_a3_lost_reply_prefix();
    k4_a3_recovery_records_legal(config);
    replay_layer::journal_legal_take(
        cfg, k4_a3_recovery_records(), 4nat,
    );
    reveal_with_fuel(replay_layer::replay, 8);
    reveal_with_fuel(replay_layer::started_count, 8);
    reveal_with_fuel(replay_layer::outcome_observation, 8);
    reveal(replay_layer::all_attempts_failed);
    reveal(replay_layer::failure_conclusive);
    reveal(replay_layer::has_durable_success);
    reveal(replay_layer::evidence_complete_decision);
    assert(prefix == k4_a3_recovery_records().take(4));
    assert(replay_layer::replay(cfg, prefix).phase[k4_a0_request()]
        == replay_layer::Phase::Armed);
    assert(replay_layer::started_count(prefix, k4_a0_request()) == 1nat);
    assert(replay_layer::outcome_observation(
        prefix, k4_a0_request(), 1nat,
    ).is_none());
    assert(!replay_layer::has_durable_success(prefix, k4_a0_request()));
    assert(!replay_layer::failure_conclusive(
        cfg, prefix, k4_a0_request(),
    ));
    assert(replay_layer::evidence_complete_decision(
        cfg, prefix, k4_a0_request(),
    ) == replay_layer::EvidenceDecision::Unknown);
    assert(k4_a3_lost_reply_effect_worlds().len() == 2);
    assert(k4_a3_lost_reply_effect_worlds()[0] == 0nat);
    assert(k4_a3_lost_reply_effect_worlds()[1] == 1nat);
    assert(k4_a3_unknown_effect_cardinality_allowed(
        k4_a3_lost_reply_effect_worlds()[0],
    ));
    assert(k4_a3_unknown_effect_cardinality_allowed(
        k4_a3_lost_reply_effect_worlds()[1],
    ));
    assert(k4_a3_lost_reply_effect_worlds()[0]
        != k4_a3_lost_reply_effect_worlds()[1]);
}

pub proof fn k4_a3_fail_records_legal(config: KManifestConfig)
    requires
        k4_a0_manifest_profile(config),
    ensures
        replay_layer::journal_legal(
            k_manifest_config_view(config), k4_a3_fail_records(),
        ),
{
    let cfg = k_manifest_config_view(config);
    let journal4 = k4_a0_records().take(4);
    let journal5 = journal4.push(k4_a3_fail_outcome_record());

    k_manifest_config_is_well_formed(config);
    k4_a0_manifest_records_legal(config);
    replay_layer::journal_legal_take(cfg, k4_a0_records(), 4nat);
    reveal_with_fuel(replay_layer::replay, 8);
    reveal_with_fuel(replay_layer::started_count, 8);
    reveal_with_fuel(replay_layer::outcome_count, 8);
    reveal_with_fuel(replay_layer::outcome_observation, 8);
    reveal_with_fuel(replay_layer::start_lsn, 8);
    reveal_with_fuel(replay_layer::outcome_lsn, 8);
    reveal(replay_layer::all_attempts_failed);
    reveal(replay_layer::failure_conclusive);

    replay_layer::replay_domains(cfg, journal4);
    assert(replay_layer::replay(cfg, journal4).phase[k4_a0_request()]
        == replay_layer::Phase::Armed);
    assert(replay_layer::request_fields_match(
        cfg,
        k4_a0_request(),
        replay_layer::Digest { id: 1nat },
        Option::None,
    ));
    assert(replay_layer::started_count(journal4, k4_a0_request())
        == 1nat);
    assert(replay_layer::outcome_count(
        journal4, k4_a0_request(), 1nat,
    ) == 0nat);
    assert(replay_layer::start_lsn(
        journal4, k4_a0_request(), 1nat,
    ) == Option::Some(4nat));
    assert(replay_layer::success_is_valid(
        cfg, k4_a0_request(), replay_layer::Observation::Failure,
    ));
    assert(replay_layer::structural_enabled(
        cfg, journal4, k4_a3_fail_outcome_record(),
    ));
    replay_layer::journal_legal_push(
        cfg, journal4, k4_a3_fail_outcome_record(),
    );

    replay_layer::replay_domains(cfg, journal5);
    assert(replay_layer::replay(cfg, journal5).phase[k4_a0_request()]
        == replay_layer::Phase::Armed);
    assert(replay_layer::started_count(journal5, k4_a0_request())
        == 1nat);
    assert(replay_layer::outcome_observation(
        journal5, k4_a0_request(), 1nat,
    ) == Option::Some(replay_layer::Observation::Failure));
    assert forall|attempt: replay_layer::AttemptId|
        1 <= attempt && attempt <= 1nat implies
            #[trigger] replay_layer::outcome_observation(
                journal5, k4_a0_request(), attempt,
            ) == Option::Some(replay_layer::Observation::Failure) by {
        assert(attempt == 1nat);
    }
    assert(replay_layer::all_attempts_failed(
        journal5, k4_a0_request(),
    ));
    assert(replay_layer::failure_conclusive(
        cfg, journal5, k4_a0_request(),
    ));
    assert(replay_layer::outcome_lsn(
        journal5, k4_a0_request(), 1nat,
    ) == Option::Some(5nat));
    assert(replay_layer::structural_enabled(
        cfg, journal5, k4_a3_fail_record(),
    ));
    replay_layer::journal_legal_push(
        cfg, journal5, k4_a3_fail_record(),
    );
    assert(k4_a3_fail_records()
        == journal5.push(k4_a3_fail_record()));
}

pub proof fn k4_a3_recovery_records_legal(config: KManifestConfig)
    requires
        k4_a3_uncontrolled_profile(config),
    ensures
        replay_layer::journal_legal(
            k_manifest_config_view(config), k4_a3_recovery_records(),
        ),
{
    let cfg = k_manifest_config_view(config);
    let request = replay_layer::RequestId { id: 1nat };
    let journal0 = Seq::<replay_layer::JournalRecord>::empty();
    let journal1 = journal0.push(k4_a3_recovery_authorize_record());
    let journal2 = journal1.push(k4_a3_recovery_prepare_record());
    let journal3 = journal2.push(k4_a3_recovery_arm_record());
    let journal4 = journal3.push(k4_a3_recovery_start_record());

    k_manifest_config_is_well_formed(config);
    reveal_with_fuel(replay_layer::replay, 8);
    reveal_with_fuel(replay_layer::authorize_lsn, 8);
    reveal_with_fuel(replay_layer::prepare_lsn, 8);
    reveal_with_fuel(replay_layer::arm_lsn, 8);
    reveal_with_fuel(replay_layer::start_lsn, 8);
    reveal_with_fuel(replay_layer::started_count, 8);
    reveal_with_fuel(replay_layer::outcome_observation, 8);
    reveal(replay_layer::all_attempts_failed);
    reveal(replay_layer::failure_conclusive);
    reveal(replay_layer::latest_evidence_lsn);
    assert(replay_layer::journal_legal(cfg, journal0));

    assert(replay_layer::structural_enabled(
        cfg, journal0, k4_a3_recovery_authorize_record(),
    ));
    replay_layer::journal_legal_push(
        cfg, journal0, k4_a3_recovery_authorize_record(),
    );

    assert(replay_layer::structural_enabled(
        cfg, journal1, k4_a3_recovery_prepare_record(),
    ));
    replay_layer::journal_legal_push(
        cfg, journal1, k4_a3_recovery_prepare_record(),
    );

    assert(replay_layer::structural_enabled(
        cfg, journal2, k4_a3_recovery_arm_record(),
    ));
    replay_layer::journal_legal_push(
        cfg, journal2, k4_a3_recovery_arm_record(),
    );

    replay_layer::replay_domains(cfg, journal3);
    assert(replay_layer::replay(cfg, journal3).phase[request]
        == replay_layer::Phase::Armed);
    assert(replay_layer::request_fields_match(
        cfg,
        request,
        replay_layer::Digest { id: 1nat },
        Option::None,
    ));
    assert(replay_layer::started_count(journal3, request) == 0nat);
    assert(!replay_layer::failure_conclusive(cfg, journal3, request));
    assert(!replay_layer::has_durable_success(journal3, request));
    assert(replay_layer::evidence_complete_decision(cfg, journal3, request)
        == replay_layer::EvidenceDecision::Retry);
    assert(replay_layer::arm_lsn(journal3, request)
        == Option::Some(3nat));
    assert(replay_layer::structural_enabled(
        cfg, journal3, k4_a3_recovery_start_record(),
    ));
    replay_layer::journal_legal_push(
        cfg, journal3, k4_a3_recovery_start_record(),
    );

    replay_layer::replay_domains(cfg, journal4);
    reveal(replay_layer::latest_evidence_lsn);
    reveal_with_fuel(replay_layer::outcome_lsn, 8);
    assert(replay_layer::replay(cfg, journal4).phase[request]
        == replay_layer::Phase::Armed);
    assert(replay_layer::started_count(journal4, request) == 1nat);
    assert(replay_layer::outcome_observation(journal4, request, 1nat).is_none());
    assert(!replay_layer::failure_conclusive(cfg, journal4, request));
    assert(!replay_layer::has_durable_success(journal4, request));
    assert(replay_layer::evidence_complete_decision(cfg, journal4, request)
        == replay_layer::EvidenceDecision::Unknown);
    assert(replay_layer::start_lsn(journal4, request, 1nat)
        == Option::Some(4nat));
    assert(replay_layer::latest_attempt(journal4, request)
        == Option::Some(1nat));
    assert(replay_layer::outcome_lsn(journal4, request, 1nat)
        == Option::None);
    assert(replay_layer::latest_evidence_lsn(journal4, request)
        == Option::Some(4nat));
    assert(replay_layer::structural_enabled(
        cfg, journal4, k4_a3_recovery_unknown_record(),
    ));
    replay_layer::journal_legal_push(
        cfg, journal4, k4_a3_recovery_unknown_record(),
    );
    assert(k4_a3_recovery_records()
        == journal4.push(k4_a3_recovery_unknown_record()));
}

pub fn k4_a3_fail_record_exec(index: u64) -> (record: KJournalRecord)
    ensures
        1 <= index <= 6 ==> k_journal_record_view(record)
            == k4_a3_fail_records()[index as int - 1],
{
    let record = match index {
        1 => KJournalRecord::Authorize {
            request: 1, capability: 1, digest: 1,
        },
        2 => KJournalRecord::Prepare {
            request: 1,
            class: KRetryClass::Idempotent,
            digest: 1,
            key_present: false,
            key: 0,
            auth_ref: 1,
        },
        3 => KJournalRecord::Arm {
            request: 1,
            digest: 1,
            key_present: false,
            key: 0,
            prepare_ref: 2,
        },
        4 => KJournalRecord::Start {
            request: 1,
            attempt: 1,
            digest: 1,
            key_present: false,
            key: 0,
            arm_ref: 3,
        },
        5 => KJournalRecord::Outcome {
            request: 1,
            attempt: 1,
            observation: KObservation::Failure,
            digest: 1,
            key_present: false,
            key: 0,
            start_ref: 4,
        },
        _ => KJournalRecord::Fail {
            request: 1,
            attempt: 1,
            digest: 1,
            key_present: false,
            key: 0,
            outcome_ref: 5,
        },
    };
    record
}

pub fn k4_a3_recovery_record_exec(index: u64)
    -> (record: KJournalRecord)
    ensures
        1 <= index <= 5 ==> k_journal_record_view(record)
            == k4_a3_recovery_records()[index as int - 1],
{
    match index {
        1 => KJournalRecord::Authorize {
            request: 1, capability: 1, digest: 1,
        },
        2 => KJournalRecord::Prepare {
            request: 1,
            class: KRetryClass::Uncontrolled,
            digest: 1,
            key_present: false,
            key: 0,
            auth_ref: 1,
        },
        3 => KJournalRecord::Arm {
            request: 1,
            digest: 1,
            key_present: false,
            key: 0,
            prepare_ref: 2,
        },
        4 => KJournalRecord::Start {
            request: 1,
            attempt: 1,
            digest: 1,
            key_present: false,
            key: 0,
            arm_ref: 3,
        },
        _ => KJournalRecord::Unknown {
            request: 1,
            attempt_present: true,
            attempt: 1,
            reason: KUnknownReason::Recovery,
            digest: 1,
            key_present: false,
            key: 0,
            evidence_ref: 4,
        },
    }
}

pub proof fn k4_a3_terminal_phase_reflects(
    config: KManifestConfig,
    state: KKernelState,
    request: u64,
    phase: KPhase,
)
    requires
        k4_a3_inv(config, state),
        phase == KPhase::Failed || phase == KPhase::Unknown,
        replay_layer::replay(
            k_manifest_config_view(config),
            k_journal_seq_view(state.journal@),
        ).phase[k_request_id(request)] == k_phase_view(phase),
    ensures
        exists|index: int| {
            &&& 0 <= index < state.durable.requests@.len()
            &&& state.durable.requests@[index].request == request
            &&& state.durable.requests@[index].phase == phase
        },
{
    let cfg = k_manifest_config_view(config);
    let journal = k_journal_seq_view(state.journal@);
    let durable = replay_layer::replay(cfg, journal);
    assert(k_tracks_request(state.durable, request as nat)) by {
        if !k_tracks_request(state.durable, request as nat) {
            assert(durable.phase[k_request_id(request)]
                == replay_layer::Phase::New);
            match phase {
                KPhase::Failed | KPhase::Unknown => {},
                _ => assert(false),
            }
            assert(false);
        }
    }
    let index = choose|index: int|
        0 <= index < state.durable.requests@.len()
            && #[trigger] state.durable.requests@[index].request as nat
                == request as nat;
    let entry = state.durable.requests@[index];
    assert(entry.request == request);
    assert(k_request_entry_couples(entry, durable));
    assert(k_phase_view(entry.phase) == k_phase_view(phase));
    k_phase_view_reflects(entry.phase, k_phase_view(phase));
    match phase {
        KPhase::Failed => {
            assert(k_phase_view(phase) == replay_layer::Phase::Failed);
            assert(entry.phase == KPhase::Failed);
        },
        KPhase::Unknown => {
            assert(k_phase_view(phase) == replay_layer::Phase::Unknown);
            assert(entry.phase == KPhase::Unknown);
        },
        _ => assert(false),
    }
    assert(exists|candidate: int| {
        &&& 0 <= candidate < state.durable.requests@.len()
        &&& state.durable.requests@[candidate].request == request
        &&& state.durable.requests@[candidate].phase == phase
    }) by {
        assert(0 <= index < state.durable.requests@.len());
    }
}

pub fn k_manifest_fail_enabled(
    config: &KManifestConfig,
    kd: &KDurable,
    request: u64,
    attempt: u64,
    digest: u64,
    key_present: bool,
    key: u64,
    Ghost(durable): Ghost<replay_layer::DurableBroker>,
) -> (decision: bool)
    requires
        k_manifest_wf(*config),
        k_durable_inv(
            *kd, k_manifest_config_view(*config), durable,
        ),
    ensures
        decision == query_layer::abstract_record_enabled(
            k_manifest_config_view(*config),
            durable,
            replay_layer::JournalRecord::FailRec {
                request: k_request_id(request),
                attempt: attempt as nat,
                digest: k_digest_id(digest),
                key: k_key_view(key_present, key),
                outcome_ref: 0,
            },
        ),
{
    let ghost cfg = k_manifest_config_view(*config);
    let ghost spec_request = k_request_id(request);
    let fields_match = k_manifest_fields_match(
        config, request, digest, key_present, key,
    );
    let profile = k_manifest_attempt_profile(config, request);
    let class_is_idempotent = profile.0;
    let max_attempts = profile.2;

    match k_find_request(kd, request) {
        Option::Some(index) => {
            let entry = &kd.requests[index];
            proof {
                assert(k_request_entry_couples(
                    kd.requests@[index as int], durable,
                ));
                assert(entry.outcomes@.len()
                    <= cfg.max_attempts[spec_request]);
                assert(max_attempts as nat
                    == cfg.max_attempts[spec_request]);
                assert(max_attempts == 1 || max_attempts == 3);
                assert(entry.outcomes@.len() <= 3);
            }
            let phase_armed = match entry.phase {
                KPhase::Armed => true,
                _ => false,
            };
            let attempt_latest = k_attempt_is_latest(
                entry, attempt, Ghost(durable),
            );
            let conclusive = k_failure_conclusive(
                entry, class_is_idempotent, Ghost(cfg), Ghost(durable),
            );
            let has_success = k_has_durable_success_exec(entry);
            proof {
                assert(k_phase_view(entry.phase)
                    == durable.phase[spec_request]);
                k_phase_view_reflects(
                    entry.phase, durable.phase[spec_request],
                );
                assert(phase_armed == (
                    durable.phase[spec_request]
                        == replay_layer::Phase::Armed
                ));
                k_has_durable_success_couples(*entry, durable);
                assert(has_success == query_layer::d_has_durable_success(
                    durable, spec_request,
                ));
            }
            phase_armed && fields_match && attempt_latest && conclusive
                && !has_success
        },
        Option::None => {
            proof {
                assert(!k_tracks_request(*kd, request as nat));
                assert(durable.phase[spec_request]
                    == replay_layer::Phase::New);
            }
            false
        },
    }
}

pub fn k_manifest_unknown_enabled(
    config: &KManifestConfig,
    entry: &KRequestEntry,
    attempt_present: bool,
    attempt: u64,
    reason: KUnknownReason,
    Ghost(durable): Ghost<replay_layer::DurableBroker>,
) -> (enabled: bool)
    requires
        k_manifest_wf(*config),
        k_request_entry_couples(*entry, durable),
        entry.outcomes@.len() <= k_manifest_config_view(*config).max_attempts[
            k_request_id(entry.request)
        ],
    ensures
        enabled == query_layer::d_unknown_enabled(
            k_manifest_config_view(*config),
            durable,
            k_request_id(entry.request),
            k_attempt_view(attempt_present, attempt),
            k_unknown_reason_view(reason),
        ),
{
    let ghost cfg = k_manifest_config_view(*config);
    let ghost spec_request = k_request_id(entry.request);
    let profile = k_manifest_attempt_profile(config, entry.request);
    let class_is_idempotent = profile.0;
    let class_is_uncontrolled = profile.1;
    let max_attempts = profile.2;
    proof {
        assert(max_attempts as nat == cfg.max_attempts[spec_request]);
        assert(max_attempts == 1 || max_attempts == 3);
        assert(entry.outcomes@.len() <= 3);
    }
    let conclusive = k_failure_conclusive(
        entry, class_is_idempotent, Ghost(cfg), Ghost(durable),
    );
    let has_success = k_has_durable_success_exec(entry);
    let started = entry.outcomes.len();
    proof {
        k_has_durable_success_couples(*entry, durable);
        assert(has_success == query_layer::d_has_durable_success(
            durable, spec_request,
        ));
    }

    if !attempt_present {
        let enabled = match reason {
            KUnknownReason::Recovery => {
                started == 0 && class_is_uncontrolled && !conclusive && !has_success
            },
            _ => false,
        };
        proof {
            assert(query_layer::d_started(durable, spec_request)
                == entry.outcomes@.len());
            assert(started as nat == entry.outcomes@.len());
            assert(k_attempt_view(false, attempt) == Option::None);
            match reason {
                KUnknownReason::Exhausted => {},
                KUnknownReason::Recovery => {},
                KUnknownReason::NonConclusiveFailure => {},
                KUnknownReason::AmbiguousOutcome => {},
                KUnknownReason::InvalidResultReason => {},
            }
            assert(enabled == query_layer::d_unknown_enabled(
                cfg, durable, spec_request, Option::None,
                k_unknown_reason_view(reason),
            ));
        }
        return enabled;
    }

    let attempt_latest = k_attempt_is_latest(
        entry, attempt, Ghost(durable),
    );
    if !attempt_latest {
        proof {
            assert(k_attempt_view(true, attempt)
                == Option::Some(attempt as nat));
            assert(!(attempt as nat
                == query_layer::d_started(durable, spec_request)
                && query_layer::d_started(durable, spec_request) > 0));
            match reason {
                KUnknownReason::Exhausted
                | KUnknownReason::Recovery
                | KUnknownReason::NonConclusiveFailure
                | KUnknownReason::AmbiguousOutcome
                | KUnknownReason::InvalidResultReason => {},
            }
            assert(!query_layer::d_unknown_enabled(
                cfg,
                durable,
                spec_request,
                Option::Some(attempt as nat),
                k_unknown_reason_view(reason),
            ));
        }
        return false;
    }

    match reason {
        KUnknownReason::Exhausted => {
            let uncertain = k_uncertain(entry, Ghost(durable));
            started as u64 == max_attempts && uncertain
        },
        KUnknownReason::Recovery => class_is_uncontrolled && !conclusive && !has_success,
        KUnknownReason::NonConclusiveFailure => {
            let latest = k_latest_outcome(entry);
            let failed = match latest {
                Option::Some(KObservation::Failure) => true,
                _ => false,
            };
            proof {
                assert(attempt as nat == entry.outcomes@.len());
                assert(entry.outcomes@.len() > 0);
                assert(query_layer::d_outcome(
                    durable, spec_request, attempt as nat,
                ) == k_outcome_view(latest));
            }
            failed && !conclusive
        },
        KUnknownReason::AmbiguousOutcome => {
            let latest = k_latest_outcome(entry);
            let ambiguous = match latest {
                Option::Some(KObservation::Ambiguous) => true,
                _ => false,
            };
            proof {
                assert(attempt as nat == entry.outcomes@.len());
                assert(entry.outcomes@.len() > 0);
                assert(query_layer::d_outcome(
                    durable, spec_request, attempt as nat,
                ) == k_outcome_view(latest));
            }
            class_is_uncontrolled && ambiguous
        },
        KUnknownReason::InvalidResultReason => {
            let latest = k_latest_outcome(entry);
            let invalid = match latest {
                Option::Some(KObservation::InvalidResult { .. }) => true,
                _ => false,
            };
            proof {
                assert(attempt as nat == entry.outcomes@.len());
                assert(entry.outcomes@.len() > 0);
                assert(query_layer::d_outcome(
                    durable, spec_request, attempt as nat,
                ) == k_outcome_view(latest));
                if invalid {
                    match latest {
                        Option::Some(KObservation::InvalidResult { value }) => {
                            let bad = replay_layer::InvalidValue {
                                id: value as nat,
                            };
                            assert(query_layer::d_outcome(
                                durable, spec_request, attempt as nat,
                            ) == Option::Some(
                                replay_layer::Observation::InvalidResult(bad),
                            ));
                        },
                        _ => assert(false),
                    }
                }
            }
            class_is_uncontrolled && invalid
        },
    }
}

pub fn k_manifest_guard_unknown(
    config: &KManifestConfig,
    kd: &KDurable,
    request: u64,
    attempt_present: bool,
    attempt: u64,
    reason: KUnknownReason,
    digest: u64,
    key_present: bool,
    key: u64,
    Ghost(durable): Ghost<replay_layer::DurableBroker>,
) -> (decision: bool)
    requires
        k_manifest_wf(*config),
        k_durable_inv(
            *kd, k_manifest_config_view(*config), durable,
        ),
    ensures
        decision == query_layer::abstract_record_enabled(
            k_manifest_config_view(*config),
            durable,
            replay_layer::JournalRecord::UnknownRec {
                request: k_request_id(request),
                attempt: k_attempt_view(attempt_present, attempt),
                reason: k_unknown_reason_view(reason),
                digest: k_digest_id(digest),
                key: k_key_view(key_present, key),
                evidence_ref: 0,
            },
        ),
{
    let ghost cfg = k_manifest_config_view(*config);
    let ghost spec_request = k_request_id(request);
    let fields_match = k_manifest_fields_match(
        config, request, digest, key_present, key,
    );
    match k_find_request(kd, request) {
        Option::Some(index) => {
            let entry = &kd.requests[index];
            proof {
                assert(k_request_entry_couples(
                    kd.requests@[index as int], durable,
                ));
                assert(entry.outcomes@.len()
                    <= cfg.max_attempts[spec_request]);
            }
            let phase_armed = match entry.phase {
                KPhase::Armed => true,
                _ => false,
            };
            let unknown_enabled = k_manifest_unknown_enabled(
                config,
                entry,
                attempt_present,
                attempt,
                reason,
                Ghost(durable),
            );
            let profile = k_manifest_attempt_profile(config, request);
            let conclusive = k_failure_conclusive(
                entry, profile.0, Ghost(cfg), Ghost(durable),
            );
            let has_success = k_has_durable_success_exec(entry);
            let classifier_unknown = if !attempt_present {
                false
            } else if !unknown_enabled {
                false
            } else {
                true
            };
            proof {
                assert(k_phase_view(entry.phase)
                    == durable.phase[spec_request]);
                k_phase_view_reflects(
                    entry.phase, durable.phase[spec_request],
                );
                assert(phase_armed == (
                    durable.phase[spec_request]
                        == replay_layer::Phase::Armed
                ));
                k_has_durable_success_couples(*entry, durable);
                assert(has_success == query_layer::d_has_durable_success(
                    durable, spec_request,
                ));
                assert(conclusive == query_layer::d_failure_conclusive(
                    cfg, durable, spec_request,
                ));
                if phase_armed && attempt_present && unknown_enabled
                        && !conclusive && !has_success {
                    query_layer::unknown_terminal_implies_unknown_decision(
                        cfg,
                        durable,
                        spec_request,
                        attempt as nat,
                        k_unknown_reason_view(reason),
                    );
                    assert(query_layer::d_evidence_complete_decision(
                        cfg, durable, spec_request,
                    ) == replay_layer::EvidenceDecision::Unknown);
                }
            }
            phase_armed && fields_match && unknown_enabled && classifier_unknown
                && !conclusive && !has_success
        },
        Option::None => {
            proof {
                assert(!k_tracks_request(*kd, request as nat));
                assert(durable.phase[spec_request]
                    == replay_layer::Phase::New);
            }
            false
        },
    }
}

pub fn k_manifest_apply_terminal_record(
    config: &KManifestConfig,
    kd: &mut KDurable,
    request_index: usize,
    phase: KPhase,
    Ghost(record): Ghost<replay_layer::JournalRecord>,
    Ghost(durable): Ghost<replay_layer::DurableBroker>,
)
    requires
        k_manifest_wf(*config),
        k_update_inv(
            *old(kd), k_manifest_config_view(*config), durable,
        ),
        request_index < old(kd).requests@.len(),
        k_phase_record_shape(
            record,
            k_request_id(old(kd).requests@[request_index as int].request),
            k_phase_view(phase),
        ),
        query_layer::abstract_record_enabled(
            k_manifest_config_view(*config), durable, record,
        ),
    ensures
        k_phase_delta(
            *old(kd), *final(kd), request_index as int, phase,
        ),
        k_update_inv(
            *final(kd),
            k_manifest_config_view(*config),
            replay_layer::apply_record(durable, record),
        ),
{
    let ghost before = *kd;
    k_set_request_phase(kd, request_index, phase);
    proof {
        k_phase_record_delta_refines_apply_record(
            before,
            *kd,
            k_manifest_config_view(*config),
            durable,
            request_index as int,
            phase,
            record,
        );
    }
}

pub fn k4_a3_semantic_record_enabled(
    config: &KManifestConfig,
    durable: &KDurable,
    record: &KJournalRecord,
    Ghost(abstract_durable): Ghost<replay_layer::DurableBroker>,
) -> (enabled: bool)
    requires
        k_manifest_wf(*config),
        k_durable_inv(
            *durable, k_manifest_config_view(*config), abstract_durable,
        ),
    ensures
        enabled == (
            k4_a3_supported(*record)
                && query_layer::abstract_record_enabled(
                    k_manifest_config_view(*config),
                    abstract_durable,
                    k_journal_record_view(*record),
                )
        ),
{
    match *record {
        KJournalRecord::Fail {
            request, attempt, digest, key_present, key, ..
        } => k_manifest_fail_enabled(
            config,
            durable,
            request,
            attempt,
            digest,
            key_present,
            key,
            Ghost(abstract_durable),
        ),
        KJournalRecord::Unknown {
            request, attempt_present, attempt, reason,
            digest, key_present, key, ..
        } => k_manifest_guard_unknown(
            config,
            durable,
            request,
            attempt_present,
            attempt,
            reason,
            digest,
            key_present,
            key,
            Ghost(abstract_durable),
        ),
        KJournalRecord::Revoke { .. } => false,
        KJournalRecord::Authorize { .. }
        | KJournalRecord::Prepare { .. }
        | KJournalRecord::Arm { .. }
        | KJournalRecord::Start { .. }
        | KJournalRecord::Outcome { .. }
        | KJournalRecord::Commit { .. } => k4_a2_semantic_record_enabled(
            config, durable, record, Ghost(abstract_durable),
        ),
    }
}

pub fn k4_a3_exact_references_enabled(
    config: &KManifestConfig,
    journal: &Vec<KJournalRecord>,
    record: &KJournalRecord,
) -> (enabled: bool)
    requires
        journal@.len() <= 0xffff_ffff_ffff_ffff,
        k_manifest_wf(*config),
        replay_layer::config_wf(k_manifest_config_view(*config)),
        replay_layer::journal_legal(
            k_manifest_config_view(*config),
            k_journal_seq_view(journal@),
        ),
        k4_a3_supported(*record),
        query_layer::abstract_record_enabled(
            k_manifest_config_view(*config),
            replay_layer::replay(
                k_manifest_config_view(*config),
                k_journal_seq_view(journal@),
            ),
            k_journal_record_view(*record),
        ),
    ensures
        enabled == k_exact_references(
            k_journal_seq_view(journal@),
            k_journal_record_view(*record),
        ),
{
    match *record {
        KJournalRecord::Authorize { .. }
        | KJournalRecord::Prepare { .. }
        | KJournalRecord::Arm { .. }
        | KJournalRecord::Start { .. }
        | KJournalRecord::Outcome { .. }
        | KJournalRecord::Commit { .. } => {
            let enabled = k4_a2_exact_references_enabled(journal, record);
            proof {
                assert(k4_a2_supported(*record));
            }
            enabled
        },
        KJournalRecord::Fail {
            request, attempt, outcome_ref, ..
        } => {
            let found = k_find_latest_reference(
                journal, KReferenceKind::Outcome, request, attempt,
            );
            proof {
                k_latest_reference_view_exact(
                    journal@,
                    KReferenceKind::Outcome,
                    request,
                    attempt,
                );
            }
            found == Option::Some(outcome_ref)
        },
        KJournalRecord::Unknown {
            request,
            attempt_present,
            attempt,
            reason,
            evidence_ref,
            ..
        } => {
            if !attempt_present {
                let found = k_find_latest_reference(
                    journal, KReferenceKind::Arm, request, 0,
                );
                proof {
                    k_latest_reference_view_exact(
                        journal@, KReferenceKind::Arm, request, 0,
                    );
                }
                found == Option::Some(evidence_ref)
            } else {
                let outcome = k_find_latest_reference(
                    journal, KReferenceKind::Outcome, request, attempt,
                );
                let start = k_find_latest_reference(
                    journal, KReferenceKind::Start, request, attempt,
                );
                let latest = match outcome {
                    Option::Some(reference) => Option::Some(reference),
                    Option::None => start,
                };
                let outcome_required = match reason {
                    KUnknownReason::NonConclusiveFailure
                    | KUnknownReason::AmbiguousOutcome
                    | KUnknownReason::InvalidResultReason => true,
                    KUnknownReason::Exhausted
                    | KUnknownReason::Recovery => false,
                };
                proof {
                    let cfg = k_manifest_config_view(*config);
                    let spec_request = k_request_id(request);
                    let spec_attempt = attempt as nat;
                    let spec_journal = k_journal_seq_view(journal@);
                    k_latest_reference_view_exact(
                        journal@,
                        KReferenceKind::Outcome,
                        request,
                        attempt,
                    );
                    k_latest_reference_view_exact(
                        journal@,
                        KReferenceKind::Start,
                        request,
                        attempt,
                    );
                    query_layer::replay_d_started_exact(
                        cfg, spec_journal, spec_request,
                    );
                    assert(spec_attempt == replay_layer::started_count(
                        spec_journal, spec_request,
                    ));
                    assert(replay_layer::latest_attempt(
                        spec_journal, spec_request,
                    ) == Option::Some(spec_attempt));
                    reveal(replay_layer::latest_evidence_lsn);
                }
                latest == Option::Some(evidence_ref)
                    && (!outcome_required
                        || outcome == Option::Some(evidence_ref))
            }
        },
        KJournalRecord::Revoke { .. } => {
            proof { assert(false); }
            false
        },
    }
}

pub fn k4_a3_structural_record_enabled(
    config: &KManifestConfig,
    durable: &KDurable,
    journal: &Vec<KJournalRecord>,
    record: &KJournalRecord,
) -> (enabled: bool)
    requires
        journal@.len() < 0xffff_ffff_ffff_ffff,
        k_manifest_wf(*config),
        replay_layer::config_wf(k_manifest_config_view(*config)),
        replay_layer::journal_legal(
            k_manifest_config_view(*config),
            k_journal_seq_view(journal@),
        ),
        k_update_inv(
            *durable,
            k_manifest_config_view(*config),
            replay_layer::replay(
                k_manifest_config_view(*config),
                k_journal_seq_view(journal@),
            ),
        ),
    ensures
        enabled == (
            k4_a3_supported(*record)
                && replay_layer::structural_enabled(
                    k_manifest_config_view(*config),
                    k_journal_seq_view(journal@),
                    k_journal_record_view(*record),
                )
        ),
{
    let ghost cfg = k_manifest_config_view(*config);
    let ghost records = k_journal_seq_view(journal@);
    let ghost abstract_durable = replay_layer::replay(cfg, records);
    let semantic = k4_a3_semantic_record_enabled(
        config, durable, record, Ghost(abstract_durable),
    );
    if semantic {
        let exact = k4_a3_exact_references_enabled(
            config, journal, record,
        );
        proof {
            k_abstract_exact_is_structural(
                cfg, records, k_journal_record_view(*record),
            );
        }
        exact
    } else {
        proof {
            k_abstract_exact_is_structural(
                cfg, records, k_journal_record_view(*record),
            );
        }
        false
    }
}

pub fn k4_a3_initial(config: &KManifestConfig) -> (state: KKernelState)
    requires
        k_manifest_wf(*config),
    ensures
        k4_a3_inv(*config, state),
        k_append_view(state)
            == append_layer::initial_state::<replay_layer::JournalRecord>(),
{
    k4_a2_initial(config)
}

pub open spec fn k4_a3_call_expected(
    config: KManifestConfig,
    state: KKernelState,
    record: KJournalRecord,
) -> bool {
    &&& state.journal@.len() < 0xffff_ffff_ffff_ffff
    &&& k4_a3_supported(record)
    &&& replay_layer::structural_enabled(
        k_manifest_config_view(config),
        k_journal_seq_view(state.journal@),
        k_journal_record_view(record),
    )
}

pub fn k4_a3_try_call(
    config: &KManifestConfig,
    state: &mut KKernelState,
    record: KJournalRecord,
) -> (accepted: bool)
    requires
        k4_a3_inv(*config, *old(state)),
        old(state).append is Idle,
    ensures
        k4_a3_inv(*config, *final(state)),
        accepted == k4_a3_call_expected(*config, *old(state), record),
        accepted ==> {
            &&& final(state).durable == old(state).durable
            &&& final(state).journal@ == old(state).journal@
            &&& final(state).ack_cuts@ == old(state).ack_cuts@
            &&& final(state).append == KAppendControl::Called { record }
            &&& k_append_view(*final(state))
                == append_layer::apply(
                    k_append_view(*old(state)),
                    append_layer::Event::Call {
                        record: k_journal_record_view(record),
                    },
                )
        },
        !accepted ==> *final(state) == *old(state),
{
    let journal_len = state.journal.len() as u64;
    if journal_len == 0xffff_ffff_ffff_ffffu64 {
        proof { assert(!k4_a3_call_expected(*config, *state, record)); }
        return false;
    }
    let enabled = k4_a3_structural_record_enabled(
        config, &state.durable, &state.journal, &record,
    );
    if !enabled {
        proof { assert(!k4_a3_call_expected(*config, *state, record)); }
        return false;
    }

    let ghost before = *state;
    let ghost before_view = k_append_view(before);
    let ghost cfg = k_manifest_config_view(*config);
    let ghost event = append_layer::Event::Call {
        record: k_journal_record_view(record),
    };
    proof {
        assert(k4_a3_supported(record));
        assert(replay_layer::structural_enabled(
            cfg,
            k_journal_seq_view(before.journal@),
            k_journal_record_view(record),
        ));
        assert(append_layer::enabled(before_view, event));
        assert(append_layer::record_eligible(
            c1_layer::c1_eligibility(cfg), before_view, event,
        ));
        append_layer::step_preserves_invariant(before_view, event);
        append_layer::step_preserves_legal_control(
            c1_layer::c1_eligibility(cfg), before_view, event,
        );
    }
    state.append = KAppendControl::Called { record };
    proof {
        assert(k_append_view(*state)
            == append_layer::apply(before_view, event));
        assert(k3_control_exact(*state));
        assert(k4_a3_call_expected(*config, before, record));
    }
    true
}

pub open spec fn k4_a3_linearize_expected(
    state: KKernelState,
    record: KJournalRecord,
) -> bool {
    &&& k4_a3_supported(record)
    &&& match state.append {
        KAppendControl::Called { record: called } => called == record,
        KAppendControl::Idle | KAppendControl::Linearized { .. } => false,
    }
}

pub fn k4_a3_linearize(
    config: &KManifestConfig,
    state: &mut KKernelState,
    record: KJournalRecord,
) -> (linearized: Option<u64>)
    requires
        k4_a3_inv(*config, *old(state)),
    ensures
        k4_a3_inv(*config, *final(state)),
        linearized.is_some()
            == k4_a3_linearize_expected(*old(state), record),
        match linearized {
            Option::None => *final(state) == *old(state),
            Option::Some(lsn) => {
                &&& final(state).journal@
                    == old(state).journal@.push(record)
                &&& final(state).ack_cuts@ == old(state).ack_cuts@
                &&& final(state).append
                    == KAppendControl::Linearized { record, lsn }
                &&& lsn as nat == old(state).journal@.len() + 1
                &&& k_append_view(*final(state))
                    == append_layer::apply(
                        k_append_view(*old(state)),
                        append_layer::Event::Linearize {
                            record: k_journal_record_view(record),
                        },
                    )
            },
        },
{
    let ghost entry_state = *state;
    let a2_supported = k4_a2_supported_exec(&record);
    if a2_supported {
        let result = k4_a2_linearize(config, state, record);
        proof {
            assert(k4_a2_supported(record));
            assert(k4_a3_supported(record));
            assert(k4_a3_linearize_expected(entry_state, record)
                == k4_a2_linearize_expected(entry_state, record));
        }
        return result;
    }

    let called = match state.append {
        KAppendControl::Called { record: called } => called,
        KAppendControl::Idle | KAppendControl::Linearized { .. } => {
            proof {
                assert(!k4_a3_linearize_expected(*state, record));
            }
            return Option::None;
        },
    };
    if !k_journal_record_equal(called, record) {
        proof {
            assert(called != record);
            assert(!k4_a3_linearize_expected(*state, record));
        }
        return Option::None;
    }
    let supported = k4_a3_supported_exec(&record);
    if !supported {
        proof {
            assert(!k4_a3_supported(record));
            assert(!k4_a3_linearize_expected(*state, record));
        }
        return Option::None;
    }

    let ghost before = *state;
    let ghost before_journal = k_journal_seq_view(before.journal@);
    let ghost cfg = k_manifest_config_view(*config);
    let ghost durable = replay_layer::replay(cfg, before_journal);
    let ghost spec_record = k_journal_record_view(record);
    let ghost before_view = k_append_view(before);
    let ghost event = append_layer::Event::Linearize {
        record: spec_record,
    };
    proof {
        assert(!k4_a2_supported(record));
        assert(called == record);
        assert(before.append == KAppendControl::Called { record });
        assert(before_view.append
            == append_layer::AppendControl::Called {
                record: spec_record,
            });
        assert(replay_layer::structural_enabled(
            cfg, before_journal, spec_record,
        ));
        query_layer::structural_enabled_implies_abstract_record_enabled(
            cfg, before_journal, spec_record,
        );
        assert(append_layer::enabled(before_view, event));
        assert(append_layer::record_eligible(
            c1_layer::c1_eligibility(cfg), before_view, event,
        ));
        append_layer::step_preserves_invariant(before_view, event);
        append_layer::step_preserves_legal_control(
            c1_layer::c1_eligibility(cfg), before_view, event,
        );
        append_layer::acknowledged_prefix_survives_record_push(
            before_view.evidence.records,
            before_view.evidence.ack_cuts,
            spec_record,
        );
        assert(k4_a3_linearize_expected(before, record));
    }

    match record {
        KJournalRecord::Fail { request, .. } => {
            let request_index = k4_a2_ensure_request(
                config, &mut state.durable, request, Ghost(durable),
            );
            proof {
                assert(k_phase_record_shape(
                    spec_record,
                    k_request_id(request),
                    k_phase_view(KPhase::Failed),
                ));
            }
            k_manifest_apply_terminal_record(
                config,
                &mut state.durable,
                request_index,
                KPhase::Failed,
                Ghost(spec_record),
                Ghost(durable),
            );
        },
        KJournalRecord::Unknown { request, .. } => {
            let request_index = k4_a2_ensure_request(
                config, &mut state.durable, request, Ghost(durable),
            );
            proof {
                assert(k_phase_record_shape(
                    spec_record,
                    k_request_id(request),
                    k_phase_view(KPhase::Unknown),
                ));
            }
            k_manifest_apply_terminal_record(
                config,
                &mut state.durable,
                request_index,
                KPhase::Unknown,
                Ghost(spec_record),
                Ghost(durable),
            );
        },
        KJournalRecord::Revoke { .. } => {
            proof { assert(false); }
            return Option::None;
        },
        KJournalRecord::Authorize { .. }
        | KJournalRecord::Prepare { .. }
        | KJournalRecord::Arm { .. }
        | KJournalRecord::Start { .. }
        | KJournalRecord::Outcome { .. }
        | KJournalRecord::Commit { .. } => {
            proof { assert(false); }
            return Option::None;
        },
    }

    proof {
        assert(state.journal@ == before.journal@);
        assert(state.ack_cuts@ == before.ack_cuts@);
        assert(state.append == before.append);
    }
    let old_len = state.journal.len();
    let lsn = old_len as u64 + 1;
    state.journal.push(record);
    state.append = KAppendControl::Linearized { record, lsn };
    proof {
        k_journal_seq_view_push(before.journal@, record);
        k_journal_seq_view_len(before.journal@);
        k_update_inv_lifts_through_replay_push(
            state.durable, cfg, before_journal, spec_record,
        );
        assert(k_journal_seq_view(state.journal@)
            == before_journal.push(spec_record));
        assert(k_append_view(*state)
            == append_layer::apply(before_view, event));
        assert(state.journal@.last() == record);
        assert(lsn as nat == state.journal@.len());
        assert(k3_control_exact(*state));
    }
    Option::Some(lsn)
}

pub fn k4_a3_return(
    config: &KManifestConfig,
    state: &mut KKernelState,
) -> (returned: Option<u64>)
    requires
        k4_a3_inv(*config, *old(state)),
    ensures
        k4_a3_inv(*config, *final(state)),
        returned.is_some() <==> old(state).append is Linearized,
        match returned {
            Option::None => *final(state) == *old(state),
            Option::Some(cut) => {
                &&& final(state).durable == old(state).durable
                &&& final(state).journal@ == old(state).journal@
                &&& final(state).ack_cuts@
                    == old(state).ack_cuts@.push(cut)
                &&& final(state).append == KAppendControl::Idle
                &&& cut as nat == old(state).journal@.len()
                &&& k_append_view(*final(state))
                    == append_layer::apply(
                        k_append_view(*old(state)),
                        append_layer::Event::ReturnOk {
                            cut: cut as nat,
                        },
                    )
            },
        },
{
    k4_a2_return(config, state)
}

pub fn k4_a3_append_one(
    config: &KManifestConfig,
    state: &mut KKernelState,
    record: KJournalRecord,
) -> (cut: u64)
    requires
        k4_a3_inv(*config, *old(state)),
        old(state).append is Idle,
        old(state).journal@.len() < 0xffff_ffff_ffff_ffff,
        k4_a3_supported(record),
        replay_layer::structural_enabled(
            k_manifest_config_view(*config),
            k_journal_seq_view(old(state).journal@),
            k_journal_record_view(record),
        ),
    ensures
        k4_a3_inv(*config, *final(state)),
        final(state).append is Idle,
        final(state).journal@ == old(state).journal@.push(record),
        final(state).ack_cuts@ == old(state).ack_cuts@.push(cut),
        cut as nat == old(state).journal@.len() + 1,
{
    let old_len = state.journal.len();
    let accepted = k4_a3_try_call(config, state, record);
    proof { assert(accepted); }
    let linearized = k4_a3_linearize(config, state, record);
    let lsn = match linearized {
        Option::Some(value) => value,
        Option::None => 0,
    };
    proof { assert(linearized.is_some()); }
    let returned = k4_a3_return(config, state);
    let returned_cut = match returned {
        Option::Some(value) => value,
        Option::None => 0,
    };
    proof {
        assert(returned.is_some());
        assert(lsn as nat == old_len + 1);
        assert(returned_cut == lsn);
    }
    returned_cut
}

pub fn k4_a3_fail_append_witness()
    -> (result: (usize, usize, u64))
    ensures
        result == (6usize, 6usize, 6u64),
        exists|config: KManifestConfig, state: KKernelState| {
            &&& k4_a0_manifest_profile(config)
            &&& k4_a3_inv(config, state)
            &&& state.append is Idle
            &&& k_journal_seq_view(state.journal@)
                == k4_a3_fail_records()
            &&& exists|index: int| {
                &&& 0 <= index < state.durable.requests@.len()
                &&& state.durable.requests@[index].request == 1
                &&& state.durable.requests@[index].phase
                    == KPhase::Failed
            }
        },
{
    let config = k4_a2_layer::k4_a1_layer::k4_a0_layer::k4_r7_layer::k4_r6_layer::k4_r5_layer::k4_r4_layer::k4_r3_layer::k4_r2_layer::k4_r1_layer::k4_r0_layer::k4_layer::k4_idempotent_manifest();
    let mut state = k4_a3_initial(&config);
    proof {
        assert(k4_a0_manifest_profile(config));
        k4_a3_fail_records_legal(config);
    }

    let first = k4_a3_fail_record_exec(1);
    proof {
        replay_layer::journal_legal_take(
            k_manifest_config_view(config), k4_a3_fail_records(), 1nat,
        );
        replay_layer::journal_legal_last(
            k_manifest_config_view(config),
            k4_a3_fail_records().take(1),
        );
    }
    let ghost before_first = state;
    let cut1 = k4_a3_append_one(&config, &mut state, first);
    proof {
        k4_a2_journal_push_view(before_first, state, first);
        assert(k_journal_seq_view(state.journal@)
            == k4_a3_fail_records().take(1));
        assert(cut1 == 1u64);
    }

    let second = k4_a3_fail_record_exec(2);
    proof {
        replay_layer::journal_legal_take(
            k_manifest_config_view(config), k4_a3_fail_records(), 2nat,
        );
        replay_layer::journal_legal_last(
            k_manifest_config_view(config),
            k4_a3_fail_records().take(2),
        );
    }
    let ghost before_second = state;
    let cut2 = k4_a3_append_one(&config, &mut state, second);
    proof {
        k4_a2_journal_push_view(before_second, state, second);
        assert(k_journal_seq_view(state.journal@)
            == k4_a3_fail_records().take(2));
        assert(cut2 == 2u64);
    }

    let third = k4_a3_fail_record_exec(3);
    proof {
        replay_layer::journal_legal_take(
            k_manifest_config_view(config), k4_a3_fail_records(), 3nat,
        );
        replay_layer::journal_legal_last(
            k_manifest_config_view(config),
            k4_a3_fail_records().take(3),
        );
    }
    let ghost before_third = state;
    let cut3 = k4_a3_append_one(&config, &mut state, third);
    proof {
        k4_a2_journal_push_view(before_third, state, third);
        assert(k_journal_seq_view(state.journal@)
            == k4_a3_fail_records().take(3));
        assert(cut3 == 3u64);
    }

    let fourth = k4_a3_fail_record_exec(4);
    proof {
        replay_layer::journal_legal_take(
            k_manifest_config_view(config), k4_a3_fail_records(), 4nat,
        );
        replay_layer::journal_legal_last(
            k_manifest_config_view(config),
            k4_a3_fail_records().take(4),
        );
    }
    let ghost before_fourth = state;
    let cut4 = k4_a3_append_one(&config, &mut state, fourth);
    proof {
        k4_a2_journal_push_view(before_fourth, state, fourth);
        assert(k_journal_seq_view(state.journal@)
            == k4_a3_fail_records().take(4));
        assert(cut4 == 4u64);
    }

    let fifth = k4_a3_fail_record_exec(5);
    proof {
        replay_layer::journal_legal_take(
            k_manifest_config_view(config), k4_a3_fail_records(), 5nat,
        );
        replay_layer::journal_legal_last(
            k_manifest_config_view(config),
            k4_a3_fail_records().take(5),
        );
    }
    let ghost before_fifth = state;
    let cut5 = k4_a3_append_one(&config, &mut state, fifth);
    proof {
        k4_a2_journal_push_view(before_fifth, state, fifth);
        assert(k_journal_seq_view(state.journal@)
            == k4_a3_fail_records().take(5));
        assert(cut5 == 5u64);
    }

    let sixth = k4_a3_fail_record_exec(6);
    proof {
        replay_layer::journal_legal_last(
            k_manifest_config_view(config), k4_a3_fail_records(),
        );
    }
    let ghost before_sixth = state;
    let cut6 = k4_a3_append_one(&config, &mut state, sixth);
    proof {
        k4_a2_journal_push_view(before_sixth, state, sixth);
        assert(k_journal_seq_view(state.journal@)
            == k4_a3_fail_records());
        assert(cut6 == 6u64);
    }

    proof {
        reveal_with_fuel(replay_layer::replay, 8);
        assert(replay_layer::replay(
            k_manifest_config_view(config), k4_a3_fail_records(),
        ).phase[k4_a0_request()] == replay_layer::Phase::Failed);
        k4_a3_terminal_phase_reflects(
            config, state, 1, KPhase::Failed,
        );
        assert(exists|candidate_config: KManifestConfig,
                       candidate_state: KKernelState| {
            &&& k4_a0_manifest_profile(candidate_config)
            &&& k4_a3_inv(candidate_config, candidate_state)
            &&& candidate_state.append is Idle
            &&& k_journal_seq_view(candidate_state.journal@)
                == k4_a3_fail_records()
            &&& exists|index: int| {
                &&& 0 <= index
                    < candidate_state.durable.requests@.len()
                &&& candidate_state.durable.requests@[index].request == 1
                &&& candidate_state.durable.requests@[index].phase
                    == KPhase::Failed
            }
        }) by {
            assert(k4_a0_manifest_profile(config));
        }
    }
    (state.journal.len(), state.ack_cuts.len(), cut6)
}

pub fn k4_a3_recovery_append_witness()
    -> (result: (usize, usize, u64))
    ensures
        result == (5usize, 5usize, 5u64),
        exists|config: KManifestConfig, state: KKernelState| {
            &&& k4_a3_uncontrolled_profile(config)
            &&& k4_a3_inv(config, state)
            &&& state.append is Idle
            &&& k_journal_seq_view(state.journal@)
                == k4_a3_recovery_records()
            &&& exists|index: int| {
                &&& 0 <= index < state.durable.requests@.len()
                &&& state.durable.requests@[index].request == 1
                &&& state.durable.requests@[index].phase
                    == KPhase::Unknown
                &&& state.durable.requests@[index].outcomes@.len() == 1
            }
        },
{
    let config = k4_a3_uncontrolled_manifest();
    let mut state = k4_a3_initial(&config);
    proof {
        assert(k4_a3_uncontrolled_profile(config));
        k4_a3_recovery_records_legal(config);
    }

    let first = k4_a3_recovery_record_exec(1);
    proof {
        replay_layer::journal_legal_take(
            k_manifest_config_view(config),
            k4_a3_recovery_records(),
            1nat,
        );
        replay_layer::journal_legal_last(
            k_manifest_config_view(config),
            k4_a3_recovery_records().take(1),
        );
    }
    let ghost before_first = state;
    let cut1 = k4_a3_append_one(&config, &mut state, first);
    proof {
        k4_a2_journal_push_view(before_first, state, first);
        assert(k_journal_seq_view(state.journal@)
            == k4_a3_recovery_records().take(1));
        assert(cut1 == 1u64);
    }

    let second = k4_a3_recovery_record_exec(2);
    proof {
        replay_layer::journal_legal_take(
            k_manifest_config_view(config),
            k4_a3_recovery_records(),
            2nat,
        );
        replay_layer::journal_legal_last(
            k_manifest_config_view(config),
            k4_a3_recovery_records().take(2),
        );
    }
    let ghost before_second = state;
    let cut2 = k4_a3_append_one(&config, &mut state, second);
    proof {
        k4_a2_journal_push_view(before_second, state, second);
        assert(k_journal_seq_view(state.journal@)
            == k4_a3_recovery_records().take(2));
        assert(cut2 == 2u64);
    }

    let third = k4_a3_recovery_record_exec(3);
    proof {
        replay_layer::journal_legal_take(
            k_manifest_config_view(config),
            k4_a3_recovery_records(),
            3nat,
        );
        replay_layer::journal_legal_last(
            k_manifest_config_view(config),
            k4_a3_recovery_records().take(3),
        );
    }
    let ghost before_third = state;
    let cut3 = k4_a3_append_one(&config, &mut state, third);
    proof {
        k4_a2_journal_push_view(before_third, state, third);
        assert(k_journal_seq_view(state.journal@)
            == k4_a3_recovery_records().take(3));
        assert(cut3 == 3u64);
    }

    let fourth = k4_a3_recovery_record_exec(4);
    proof {
        replay_layer::journal_legal_take(
            k_manifest_config_view(config),
            k4_a3_recovery_records(),
            4nat,
        );
        replay_layer::journal_legal_last(
            k_manifest_config_view(config),
            k4_a3_recovery_records().take(4),
        );
    }
    let ghost before_fourth = state;
    let cut4 = k4_a3_append_one(&config, &mut state, fourth);
    proof {
        k4_a2_journal_push_view(before_fourth, state, fourth);
        assert(k_journal_seq_view(state.journal@)
            == k4_a3_recovery_records().take(4));
        assert(cut4 == 4u64);
    }

    let fifth = k4_a3_recovery_record_exec(5);
    proof {
        replay_layer::journal_legal_last(
            k_manifest_config_view(config),
            k4_a3_recovery_records(),
        );
    }
    let ghost before_fifth = state;
    let cut5 = k4_a3_append_one(&config, &mut state, fifth);
    proof {
        k4_a2_journal_push_view(before_fifth, state, fifth);
        assert(k_journal_seq_view(state.journal@)
            == k4_a3_recovery_records());
        assert(cut5 == 5u64);
    }

    proof {
        reveal_with_fuel(replay_layer::replay, 8);
        assert(replay_layer::replay(
            k_manifest_config_view(config), k4_a3_recovery_records(),
        ).phase[replay_layer::RequestId { id: 1nat }]
            == replay_layer::Phase::Unknown);
        k4_a3_terminal_phase_reflects(
            config, state, 1, KPhase::Unknown,
        );
        let index = choose|index: int|
            0 <= index < state.durable.requests@.len()
                && #[trigger] state.durable.requests@[index].request == 1
                && state.durable.requests@[index].phase == KPhase::Unknown;
        let entry = state.durable.requests@[index];
        assert(k_request_entry_couples(
            entry,
            replay_layer::replay(
                k_manifest_config_view(config),
                k4_a3_recovery_records(),
            ),
        ));
        query_layer::replay_d_started_exact(
            k_manifest_config_view(config),
            k4_a3_recovery_records(),
            replay_layer::RequestId { id: 1nat },
        );
        reveal_with_fuel(replay_layer::started_count, 8);
        assert(entry.outcomes@.len() == 1);
        assert(exists|candidate_config: KManifestConfig,
                       candidate_state: KKernelState| {
            &&& k4_a3_uncontrolled_profile(candidate_config)
            &&& k4_a3_inv(candidate_config, candidate_state)
            &&& candidate_state.append is Idle
            &&& k_journal_seq_view(candidate_state.journal@)
                == k4_a3_recovery_records()
            &&& exists|candidate: int| {
                &&& 0 <= candidate
                    < candidate_state.durable.requests@.len()
                &&& candidate_state.durable.requests@[candidate].request
                    == 1
                &&& candidate_state.durable.requests@[candidate].phase
                    == KPhase::Unknown
                &&& candidate_state.durable.requests@[candidate]
                    .outcomes@.len() == 1
            }
        }) by {
            assert(k4_a3_uncontrolled_profile(config));
        }
    }
    (state.journal.len(), state.ack_cuts.len(), cut5)
}

} // verus!
