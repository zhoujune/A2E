use vstd::prelude::*;

#[path = "k2_durable_record_kernel.rs"]
pub mod k2_record_layer;

pub use k2_record_layer::k2_guard_layer::{KRetryClass, KUnknownReason};
pub use k2_record_layer::k2_guard_layer::k1_layer::KObservation;

verus! {

use k2_record_layer::*;
use k2_record_layer::k2_guard_layer::*;
use k2_record_layer::k2_guard_layer::k1_layer::*;
use k2_record_layer::k2_guard_layer::k1_layer::query_layer;
use query_layer::c1_layer;
use c1_layer::{append_layer, replay_layer};

broadcast use {
    vstd::imap::group_imap_lemmas,
    vstd::iset::group_iset_lemmas,
};

// K3-A0 supplies the first serialized executable append loop over K2-T0.
// Exact records and their one-based references are represented at runtime.
// Crash/recovery, executor slots, invocation, and physical persistence remain
// later milestones.

#[derive(PartialEq, Eq, Clone, Copy)]
pub enum KJournalRecord {
    Authorize {
        request: u64,
        capability: u64,
        digest: u64,
    },
    Revoke {
        capability: u64,
    },
    Prepare {
        request: u64,
        class: KRetryClass,
        digest: u64,
        key_present: bool,
        key: u64,
        auth_ref: u64,
    },
    Arm {
        request: u64,
        digest: u64,
        key_present: bool,
        key: u64,
        prepare_ref: u64,
    },
    Start {
        request: u64,
        attempt: u64,
        digest: u64,
        key_present: bool,
        key: u64,
        arm_ref: u64,
    },
    Outcome {
        request: u64,
        attempt: u64,
        observation: KObservation,
        digest: u64,
        key_present: bool,
        key: u64,
        start_ref: u64,
    },
    Commit {
        request: u64,
        attempt: u64,
        value: u64,
        digest: u64,
        key_present: bool,
        key: u64,
        outcome_ref: u64,
    },
    Fail {
        request: u64,
        attempt: u64,
        digest: u64,
        key_present: bool,
        key: u64,
        outcome_ref: u64,
    },
    Unknown {
        request: u64,
        attempt_present: bool,
        attempt: u64,
        reason: KUnknownReason,
        digest: u64,
        key_present: bool,
        key: u64,
        evidence_ref: u64,
    },
}

pub open spec fn k_journal_record_view(
    record: KJournalRecord,
) -> replay_layer::JournalRecord {
    match record {
        KJournalRecord::Authorize { request, capability, digest } =>
            replay_layer::JournalRecord::Authorize {
                request: k_request_id(request),
                capability: k_capability_id(capability),
                digest: k_digest_id(digest),
            },
        KJournalRecord::Revoke { capability } =>
            replay_layer::JournalRecord::Revoke {
                capability: k_capability_id(capability),
            },
        KJournalRecord::Prepare {
            request, class, digest, key_present, key, auth_ref,
        } => replay_layer::JournalRecord::Prepare {
            request: k_request_id(request),
            class: k_retry_class_view(class),
            digest: k_digest_id(digest),
            key: k_key_view(key_present, key),
            auth_ref: auth_ref as nat,
        },
        KJournalRecord::Arm {
            request, digest, key_present, key, prepare_ref,
        } => replay_layer::JournalRecord::Arm {
            request: k_request_id(request),
            digest: k_digest_id(digest),
            key: k_key_view(key_present, key),
            prepare_ref: prepare_ref as nat,
        },
        KJournalRecord::Start {
            request, attempt, digest, key_present, key, arm_ref,
        } => replay_layer::JournalRecord::Start {
            request: k_request_id(request),
            attempt: attempt as nat,
            digest: k_digest_id(digest),
            key: k_key_view(key_present, key),
            arm_ref: arm_ref as nat,
        },
        KJournalRecord::Outcome {
            request, attempt, observation, digest, key_present, key, start_ref,
        } => replay_layer::JournalRecord::Outcome {
            request: k_request_id(request),
            attempt: attempt as nat,
            observation: k_observation_view(observation),
            digest: k_digest_id(digest),
            key: k_key_view(key_present, key),
            start_ref: start_ref as nat,
        },
        KJournalRecord::Commit {
            request, attempt, value, digest, key_present, key, outcome_ref,
        } => replay_layer::JournalRecord::CommitRec {
            request: k_request_id(request),
            attempt: attempt as nat,
            value: replay_layer::Value { id: value as nat },
            digest: k_digest_id(digest),
            key: k_key_view(key_present, key),
            outcome_ref: outcome_ref as nat,
        },
        KJournalRecord::Fail {
            request, attempt, digest, key_present, key, outcome_ref,
        } => replay_layer::JournalRecord::FailRec {
            request: k_request_id(request),
            attempt: attempt as nat,
            digest: k_digest_id(digest),
            key: k_key_view(key_present, key),
            outcome_ref: outcome_ref as nat,
        },
        KJournalRecord::Unknown {
            request, attempt_present, attempt, reason, digest,
            key_present, key, evidence_ref,
        } => replay_layer::JournalRecord::UnknownRec {
            request: k_request_id(request),
            attempt: k_attempt_view(attempt_present, attempt),
            reason: k_unknown_reason_view(reason),
            digest: k_digest_id(digest),
            key: k_key_view(key_present, key),
            evidence_ref: evidence_ref as nat,
        },
    }
}

pub open spec fn k_journal_seq_view(
    records: Seq<KJournalRecord>,
) -> Seq<replay_layer::JournalRecord>
    decreases records.len(),
{
    if records.len() == 0 {
        Seq::empty()
    } else {
        k_journal_seq_view(records.drop_last()).push(
            k_journal_record_view(records.last()),
        )
    }
}

pub proof fn k_journal_seq_view_push(
    records: Seq<KJournalRecord>,
    record: KJournalRecord,
)
    ensures
        k_journal_seq_view(records.push(record))
            == k_journal_seq_view(records).push(k_journal_record_view(record)),
{
    assert(records.push(record).drop_last() =~= records);
    assert(records.push(record).last() == record);
}

pub proof fn k_journal_seq_view_len(records: Seq<KJournalRecord>)
    ensures
        k_journal_seq_view(records).len() == records.len(),
    decreases records.len(),
{
    if records.len() > 0 {
        k_journal_seq_view_len(records.drop_last());
    }
}

#[derive(PartialEq, Eq, Clone, Copy)]
pub enum KReferenceKind {
    Authorize,
    Prepare,
    Arm,
    Start,
    Outcome,
}

pub open spec fn k_reference_record_matches(
    record: KJournalRecord,
    kind: KReferenceKind,
    request: u64,
    attempt: u64,
) -> bool {
    match kind {
        KReferenceKind::Authorize => match record {
            KJournalRecord::Authorize { request: target, .. } => target == request,
            _ => false,
        },
        KReferenceKind::Prepare => match record {
            KJournalRecord::Prepare { request: target, .. } => target == request,
            _ => false,
        },
        KReferenceKind::Arm => match record {
            KJournalRecord::Arm { request: target, .. } => target == request,
            _ => false,
        },
        KReferenceKind::Start => match record {
            KJournalRecord::Start {
                request: target, attempt: selected, ..
            } => target == request && selected == attempt,
            _ => false,
        },
        KReferenceKind::Outcome => match record {
            KJournalRecord::Outcome {
                request: target, attempt: selected, ..
            } => target == request && selected == attempt,
            _ => false,
        },
    }
}

pub fn k_reference_record_matches_exec(
    record: &KJournalRecord,
    kind: KReferenceKind,
    request: u64,
    attempt: u64,
) -> (matches: bool)
    ensures
        matches == k_reference_record_matches(*record, kind, request, attempt),
{
    match kind {
        KReferenceKind::Authorize => match *record {
            KJournalRecord::Authorize { request: target, .. } => target == request,
            _ => false,
        },
        KReferenceKind::Prepare => match *record {
            KJournalRecord::Prepare { request: target, .. } => target == request,
            _ => false,
        },
        KReferenceKind::Arm => match *record {
            KJournalRecord::Arm { request: target, .. } => target == request,
            _ => false,
        },
        KReferenceKind::Start => match *record {
            KJournalRecord::Start {
                request: target, attempt: selected, ..
            } => target == request && selected == attempt,
            _ => false,
        },
        KReferenceKind::Outcome => match *record {
            KJournalRecord::Outcome {
                request: target, attempt: selected, ..
            } => target == request && selected == attempt,
            _ => false,
        },
    }
}

pub open spec fn k_latest_reference_in(
    records: Seq<KJournalRecord>,
    kind: KReferenceKind,
    request: u64,
    attempt: u64,
) -> Option<nat>
    decreases records.len(),
{
    if records.len() == 0 {
        Option::None
    } else if k_reference_record_matches(
        records.last(), kind, request, attempt,
    ) {
        Option::Some(records.len())
    } else {
        k_latest_reference_in(records.drop_last(), kind, request, attempt)
    }
}

pub open spec fn k_reference_lsn_view(
    journal: Seq<replay_layer::JournalRecord>,
    kind: KReferenceKind,
    request: u64,
    attempt: u64,
) -> Option<nat> {
    match kind {
        KReferenceKind::Authorize =>
            replay_layer::authorize_lsn(journal, k_request_id(request)),
        KReferenceKind::Prepare =>
            replay_layer::prepare_lsn(journal, k_request_id(request)),
        KReferenceKind::Arm =>
            replay_layer::arm_lsn(journal, k_request_id(request)),
        KReferenceKind::Start => replay_layer::start_lsn(
            journal, k_request_id(request), attempt as nat,
        ),
        KReferenceKind::Outcome => replay_layer::outcome_lsn(
            journal, k_request_id(request), attempt as nat,
        ),
    }
}

pub proof fn k_latest_reference_view_exact(
    records: Seq<KJournalRecord>,
    kind: KReferenceKind,
    request: u64,
    attempt: u64,
)
    ensures
        k_latest_reference_in(records, kind, request, attempt)
            == k_reference_lsn_view(
                k_journal_seq_view(records), kind, request, attempt,
            ),
    decreases records.len(),
{
    reveal_with_fuel(k_latest_reference_in, 2);
    reveal_with_fuel(k_journal_seq_view, 2);
    if records.len() > 0 {
        let prefix = records.drop_last();
        let record = records.last();
        k_latest_reference_view_exact(prefix, kind, request, attempt);
        k_journal_seq_view_len(prefix);
        k_journal_seq_view_len(records);
        assert(prefix.push(record) =~= records);
        k_journal_seq_view_push(prefix, record);
        assert(k_journal_seq_view(records)
            == k_journal_seq_view(prefix).push(k_journal_record_view(record)));
        assert(k_journal_seq_view(records).drop_last()
            =~= k_journal_seq_view(prefix));
        assert(k_journal_seq_view(records).last()
            == k_journal_record_view(record));
        match kind {
            KReferenceKind::Authorize => {
                reveal_with_fuel(replay_layer::authorize_lsn, 2);
                match record {
                KJournalRecord::Authorize { request: target, .. } => {
                    assert(k_request_id(target) == k_request_id(request)
                        <==> target == request);
                    if target == request {
                        assert(k_reference_record_matches(
                            record, kind, request, attempt,
                        ));
                        assert(k_latest_reference_in(
                            records, kind, request, attempt,
                        ) == Option::Some(records.len()));
                        assert(replay_layer::authorize_lsn(
                            k_journal_seq_view(records), k_request_id(request),
                        ) == Option::Some(k_journal_seq_view(records).len()));
                    } else {
                        assert(!k_reference_record_matches(
                            record, kind, request, attempt,
                        ));
                        assert(k_latest_reference_in(
                            records, kind, request, attempt,
                        ) == k_latest_reference_in(
                            prefix, kind, request, attempt,
                        ));
                        assert(replay_layer::authorize_lsn(
                            k_journal_seq_view(records), k_request_id(request),
                        ) == replay_layer::authorize_lsn(
                            k_journal_seq_view(prefix), k_request_id(request),
                        ));
                    }
                },
                KJournalRecord::Revoke { .. }
                | KJournalRecord::Prepare { .. }
                | KJournalRecord::Arm { .. }
                | KJournalRecord::Start { .. }
                | KJournalRecord::Outcome { .. }
                | KJournalRecord::Commit { .. }
                | KJournalRecord::Fail { .. }
                | KJournalRecord::Unknown { .. } => {
                    assert(!k_reference_record_matches(
                        record, kind, request, attempt,
                    ));
                    assert(k_latest_reference_in(
                        records, kind, request, attempt,
                    ) == k_latest_reference_in(
                        prefix, kind, request, attempt,
                    ));
                    assert(replay_layer::authorize_lsn(
                        k_journal_seq_view(records), k_request_id(request),
                    ) == replay_layer::authorize_lsn(
                        k_journal_seq_view(prefix), k_request_id(request),
                    ));
                },
                }
                assert(k_latest_reference_in(
                    records, kind, request, attempt,
                ) == replay_layer::authorize_lsn(
                    k_journal_seq_view(records), k_request_id(request),
                ));
            },
            KReferenceKind::Prepare => {
                reveal_with_fuel(replay_layer::prepare_lsn, 2);
                match record {
                KJournalRecord::Prepare { request: target, .. } => {
                    assert(k_request_id(target) == k_request_id(request)
                        <==> target == request);
                    if target == request {
                        assert(k_reference_record_matches(
                            record, kind, request, attempt,
                        ));
                        assert(k_latest_reference_in(
                            records, kind, request, attempt,
                        ) == Option::Some(records.len()));
                        assert(replay_layer::prepare_lsn(
                            k_journal_seq_view(records), k_request_id(request),
                        ) == Option::Some(k_journal_seq_view(records).len()));
                    } else {
                        assert(!k_reference_record_matches(
                            record, kind, request, attempt,
                        ));
                        assert(k_latest_reference_in(
                            records, kind, request, attempt,
                        ) == k_latest_reference_in(
                            prefix, kind, request, attempt,
                        ));
                        assert(replay_layer::prepare_lsn(
                            k_journal_seq_view(records), k_request_id(request),
                        ) == replay_layer::prepare_lsn(
                            k_journal_seq_view(prefix), k_request_id(request),
                        ));
                    }
                },
                KJournalRecord::Authorize { .. }
                | KJournalRecord::Revoke { .. }
                | KJournalRecord::Arm { .. }
                | KJournalRecord::Start { .. }
                | KJournalRecord::Outcome { .. }
                | KJournalRecord::Commit { .. }
                | KJournalRecord::Fail { .. }
                | KJournalRecord::Unknown { .. } => {
                    assert(!k_reference_record_matches(
                        record, kind, request, attempt,
                    ));
                    assert(k_latest_reference_in(
                        records, kind, request, attempt,
                    ) == k_latest_reference_in(
                        prefix, kind, request, attempt,
                    ));
                    assert(replay_layer::prepare_lsn(
                        k_journal_seq_view(records), k_request_id(request),
                    ) == replay_layer::prepare_lsn(
                        k_journal_seq_view(prefix), k_request_id(request),
                    ));
                },
                }
                assert(k_latest_reference_in(
                    records, kind, request, attempt,
                ) == replay_layer::prepare_lsn(
                    k_journal_seq_view(records), k_request_id(request),
                ));
            },
            KReferenceKind::Arm => {
                reveal_with_fuel(replay_layer::arm_lsn, 2);
                match record {
                KJournalRecord::Arm { request: target, .. } => {
                    assert(k_request_id(target) == k_request_id(request)
                        <==> target == request);
                },
                KJournalRecord::Authorize { .. }
                | KJournalRecord::Revoke { .. }
                | KJournalRecord::Prepare { .. }
                | KJournalRecord::Start { .. }
                | KJournalRecord::Outcome { .. }
                | KJournalRecord::Commit { .. }
                | KJournalRecord::Fail { .. }
                | KJournalRecord::Unknown { .. } => {},
                }
                assert(k_latest_reference_in(
                    records, kind, request, attempt,
                ) == replay_layer::arm_lsn(
                    k_journal_seq_view(records), k_request_id(request),
                ));
            },
            KReferenceKind::Start => {
                reveal_with_fuel(replay_layer::start_lsn, 2);
                match record {
                KJournalRecord::Start {
                    request: target, attempt: selected, ..
                } => {
                    assert(k_request_id(target) == k_request_id(request)
                        <==> target == request);
                    assert(selected as nat == attempt as nat
                        <==> selected == attempt);
                },
                KJournalRecord::Authorize { .. }
                | KJournalRecord::Revoke { .. }
                | KJournalRecord::Prepare { .. }
                | KJournalRecord::Arm { .. }
                | KJournalRecord::Outcome { .. }
                | KJournalRecord::Commit { .. }
                | KJournalRecord::Fail { .. }
                | KJournalRecord::Unknown { .. } => {},
                }
                assert(k_latest_reference_in(
                    records, kind, request, attempt,
                ) == replay_layer::start_lsn(
                    k_journal_seq_view(records),
                    k_request_id(request),
                    attempt as nat,
                ));
            },
            KReferenceKind::Outcome => {
                reveal_with_fuel(replay_layer::outcome_lsn, 2);
                match record {
                KJournalRecord::Outcome {
                    request: target, attempt: selected, ..
                } => {
                    assert(k_request_id(target) == k_request_id(request)
                        <==> target == request);
                    assert(selected as nat == attempt as nat
                        <==> selected == attempt);
                },
                KJournalRecord::Authorize { .. }
                | KJournalRecord::Revoke { .. }
                | KJournalRecord::Prepare { .. }
                | KJournalRecord::Arm { .. }
                | KJournalRecord::Start { .. }
                | KJournalRecord::Commit { .. }
                | KJournalRecord::Fail { .. }
                | KJournalRecord::Unknown { .. } => {},
                }
                assert(k_latest_reference_in(
                    records, kind, request, attempt,
                ) == replay_layer::outcome_lsn(
                    k_journal_seq_view(records),
                    k_request_id(request),
                    attempt as nat,
                ));
            },
        }
    } else {
        assert(k_journal_seq_view(records) =~=
            Seq::<replay_layer::JournalRecord>::empty());
        match kind {
            KReferenceKind::Authorize => {
                reveal_with_fuel(replay_layer::authorize_lsn, 2);
            },
            KReferenceKind::Prepare => {
                reveal_with_fuel(replay_layer::prepare_lsn, 2);
            },
            KReferenceKind::Arm => {
                reveal_with_fuel(replay_layer::arm_lsn, 2);
            },
            KReferenceKind::Start => {
                reveal_with_fuel(replay_layer::start_lsn, 2);
            },
            KReferenceKind::Outcome => {
                reveal_with_fuel(replay_layer::outcome_lsn, 2);
            },
        }
    }
}

pub open spec fn k_option_u64_view(value: Option<u64>) -> Option<nat> {
    match value {
        Option::Some(number) => Option::Some(number as nat),
        Option::None => Option::None,
    }
}

pub fn k_find_latest_reference(
    journal: &Vec<KJournalRecord>,
    kind: KReferenceKind,
    request: u64,
    attempt: u64,
) -> (reference: Option<u64>)
    requires
        journal@.len() <= 0xffff_ffff_ffff_ffff,
    ensures
        k_option_u64_view(reference)
            == k_latest_reference_in(journal@, kind, request, attempt),
{
    let mut index = journal.len();
    proof {
        assert(index as nat == journal@.len());
        assert(journal@.take(index as int) =~= journal@);
    }
    while index > 0
        invariant
            index <= journal@.len(),
            k_latest_reference_in(journal@, kind, request, attempt)
                == k_latest_reference_in(
                    journal@.take(index as int), kind, request, attempt,
                ),
        decreases index,
    {
        let next = index - 1;
        proof {
            assert(journal@.take(index as int).len() == index);
            assert(journal@.take(index as int).last()
                == journal@[next as int]);
            assert(journal@.take(index as int).drop_last()
                =~= journal@.take(next as int));
        }
        if k_reference_record_matches_exec(
            &journal[next], kind, request, attempt,
        ) {
            return Option::Some(index as u64);
        }
        index = next;
    }
    Option::None
}

pub open spec fn k_exact_references(
    journal: Seq<replay_layer::JournalRecord>,
    record: replay_layer::JournalRecord,
) -> bool {
    match record {
        replay_layer::JournalRecord::Authorize { .. }
        | replay_layer::JournalRecord::Revoke { .. } => true,
        replay_layer::JournalRecord::Prepare { request, auth_ref, .. } =>
            replay_layer::ref_is(
                auth_ref, replay_layer::authorize_lsn(journal, request),
            ),
        replay_layer::JournalRecord::Arm { request, prepare_ref, .. } =>
            replay_layer::ref_is(
                prepare_ref, replay_layer::prepare_lsn(journal, request),
            ),
        replay_layer::JournalRecord::Start {
            request, attempt: _, arm_ref, ..
        } => replay_layer::ref_is(
            arm_ref, replay_layer::arm_lsn(journal, request),
        ),
        replay_layer::JournalRecord::Outcome {
            request, attempt, start_ref, ..
        } => replay_layer::ref_is(
            start_ref, replay_layer::start_lsn(journal, request, attempt),
        ),
        replay_layer::JournalRecord::CommitRec {
            request, attempt, outcome_ref, ..
        }
        | replay_layer::JournalRecord::FailRec {
            request, attempt, outcome_ref, ..
        } => replay_layer::ref_is(
            outcome_ref, replay_layer::outcome_lsn(journal, request, attempt),
        ),
        replay_layer::JournalRecord::UnknownRec {
            request, attempt, reason, evidence_ref, ..
        } => match attempt {
            Option::None => replay_layer::ref_is(
                evidence_ref, replay_layer::arm_lsn(journal, request),
            ),
            Option::Some(selected) => {
                &&& replay_layer::ref_is(
                    evidence_ref,
                    replay_layer::latest_evidence_lsn(journal, request),
                )
                &&& match reason {
                    replay_layer::UnknownReason::NonConclusiveFailure
                    | replay_layer::UnknownReason::AmbiguousOutcome
                    | replay_layer::UnknownReason::InvalidResultReason =>
                        replay_layer::ref_is(
                            evidence_ref,
                            replay_layer::outcome_lsn(
                                journal, request, selected,
                            ),
                        ),
                    replay_layer::UnknownReason::Exhausted
                    | replay_layer::UnknownReason::Recovery => true,
                }
            },
        },
    }
}

pub proof fn k_outcome_none_iff_count_zero(
    journal: Seq<replay_layer::JournalRecord>,
    request: replay_layer::RequestId,
    attempt: replay_layer::AttemptId,
)
    ensures
        replay_layer::outcome_observation(journal, request, attempt).is_none()
            <==> replay_layer::outcome_count(journal, request, attempt) == 0,
    decreases journal.len(),
{
    if journal.len() > 0 {
        k_outcome_none_iff_count_zero(
            journal.drop_last(), request, attempt,
        );
        match journal.last() {
            replay_layer::JournalRecord::Outcome {
                request: target, attempt: selected, ..
            } => {
                if target == request && selected == attempt {
                }
            },
            replay_layer::JournalRecord::Authorize { .. }
            | replay_layer::JournalRecord::Revoke { .. }
            | replay_layer::JournalRecord::Prepare { .. }
            | replay_layer::JournalRecord::Arm { .. }
            | replay_layer::JournalRecord::Start { .. }
            | replay_layer::JournalRecord::CommitRec { .. }
            | replay_layer::JournalRecord::FailRec { .. }
            | replay_layer::JournalRecord::UnknownRec { .. } => {},
        }
    }
}

pub proof fn k_abstract_exact_is_structural(
    cfg: replay_layer::Config,
    journal: Seq<replay_layer::JournalRecord>,
    record: replay_layer::JournalRecord,
)
    requires
        replay_layer::config_wf(cfg),
        replay_layer::journal_legal(cfg, journal),
    ensures
        replay_layer::structural_enabled(cfg, journal, record)
            <==> query_layer::abstract_record_enabled(
                    cfg, replay_layer::replay(cfg, journal), record,
                ) && k_exact_references(journal, record),
{
    if replay_layer::structural_enabled(cfg, journal, record) {
        query_layer::structural_enabled_implies_abstract_record_enabled(
            cfg, journal, record,
        );
        match record {
            replay_layer::JournalRecord::Authorize { .. }
            | replay_layer::JournalRecord::Revoke { .. }
            | replay_layer::JournalRecord::Prepare { .. }
            | replay_layer::JournalRecord::Arm { .. }
            | replay_layer::JournalRecord::Start { .. }
            | replay_layer::JournalRecord::Outcome { .. }
            | replay_layer::JournalRecord::CommitRec { .. }
            | replay_layer::JournalRecord::FailRec { .. }
            | replay_layer::JournalRecord::UnknownRec { .. } => {},
        }
    }
    if query_layer::abstract_record_enabled(
        cfg, replay_layer::replay(cfg, journal), record,
    ) && k_exact_references(journal, record) {
        match record {
            replay_layer::JournalRecord::Authorize { .. }
            | replay_layer::JournalRecord::Revoke { .. }
            | replay_layer::JournalRecord::Prepare { .. }
            | replay_layer::JournalRecord::Arm { .. } => {},
            replay_layer::JournalRecord::Start { request, .. } => {
                query_layer::replay_d_started_exact(cfg, journal, request);
                query_layer::replay_d_failure_conclusive_exact(
                    cfg, journal, request,
                );
            },
            replay_layer::JournalRecord::Outcome {
                request, attempt, ..
            } => {
                query_layer::replay_d_started_exact(cfg, journal, request);
                query_layer::replay_d_outcome_exact(
                    cfg, journal, request, attempt,
                );
                k_outcome_none_iff_count_zero(journal, request, attempt);
            },
            replay_layer::JournalRecord::CommitRec {
                request, attempt, ..
            } => {
                query_layer::replay_d_started_exact(cfg, journal, request);
                query_layer::replay_d_outcome_exact(
                    cfg, journal, request, attempt,
                );
            },
            replay_layer::JournalRecord::FailRec {
                request, attempt, ..
            } => {
                query_layer::replay_d_started_exact(cfg, journal, request);
                query_layer::replay_d_outcome_exact(
                    cfg, journal, request, attempt,
                );
                query_layer::replay_d_failure_conclusive_exact(
                    cfg, journal, request,
                );
            },
            replay_layer::JournalRecord::UnknownRec {
                request, attempt, ..
            } => {
                query_layer::replay_d_started_exact(cfg, journal, request);
                query_layer::replay_d_failure_conclusive_exact(
                    cfg, journal, request,
                );
                query_layer::replay_d_uncertain_exact(cfg, journal, request);
                match attempt {
                    Option::Some(selected) => {
                        query_layer::replay_d_outcome_exact(
                            cfg, journal, request, selected,
                        );
                    },
                    Option::None => {},
                }
            },
        }
    }
}

pub fn k_semantic_record_enabled(
    durable: &KDurable,
    record: &KJournalRecord,
    Ghost(abstract_durable): Ghost<replay_layer::DurableBroker>,
) -> (enabled: bool)
    requires
        k_durable_inv(*durable, k_demo_config(), abstract_durable),
    ensures
        enabled == query_layer::abstract_record_enabled(
            k_demo_config(), abstract_durable, k_journal_record_view(*record),
        ),
{
    match *record {
        KJournalRecord::Authorize { request, capability, digest } =>
            k_guard_authorize(
                durable, request, capability, digest, Ghost(abstract_durable),
            ),
        KJournalRecord::Revoke { capability } =>
            k_guard_revoke(durable, capability, Ghost(abstract_durable)),
        KJournalRecord::Prepare {
            request, class, digest, key_present, key, ..
        } => k_guard_prepare(
            durable, request, class, digest, key_present, key,
            Ghost(abstract_durable),
        ),
        KJournalRecord::Arm {
            request, digest, key_present, key, ..
        } => k_guard_arm(
            durable, request, digest, key_present, key,
            Ghost(abstract_durable),
        ),
        KJournalRecord::Start {
            request, attempt, digest, key_present, key, ..
        } => {
            if attempt < 0xffff_ffff_ffff_ffff {
                k_guard_start(
                    durable, request, attempt, digest, key_present, key,
                    Ghost(abstract_durable),
                )
            } else {
                proof {
                    let spec_request = k_request_id(request);
                    assert(k_demo_config().max_attempts[spec_request]
                        == if k_lane_of(spec_request) == 3 { 1nat } else { 3nat });
                    assert(attempt as nat
                        > k_demo_config().max_attempts[spec_request]);
                }
                false
            }
        },
        KJournalRecord::Outcome {
            request, attempt, observation, digest, key_present, key, ..
        } => k_guard_outcome(
            durable, request, attempt, observation, digest, key_present, key,
            Ghost(abstract_durable),
        ),
        KJournalRecord::Commit {
            request, attempt, value, digest, key_present, key, ..
        } => k_guard_commit(
            durable, request, attempt, value, digest, key_present, key,
            Ghost(abstract_durable),
        ),
        KJournalRecord::Fail {
            request, attempt, digest, key_present, key, ..
        } => k_guard_fail(
            durable, request, attempt, digest, key_present, key,
            Ghost(abstract_durable),
        ),
        KJournalRecord::Unknown {
            request, attempt_present, attempt, reason,
            digest, key_present, key, ..
        } => k_guard_unknown(
            durable, request, attempt_present, attempt, reason,
            digest, key_present, key, Ghost(abstract_durable),
        ),
    }
}

pub fn k_exact_references_enabled(
    journal: &Vec<KJournalRecord>,
    record: &KJournalRecord,
) -> (enabled: bool)
    requires
        journal@.len() <= 0xffff_ffff_ffff_ffff,
        replay_layer::config_wf(k_demo_config()),
        replay_layer::journal_legal(
            k_demo_config(), k_journal_seq_view(journal@),
        ),
        query_layer::abstract_record_enabled(
            k_demo_config(),
            replay_layer::replay(
                k_demo_config(), k_journal_seq_view(journal@),
            ),
            k_journal_record_view(*record),
        ),
    ensures
        enabled == k_exact_references(
            k_journal_seq_view(journal@), k_journal_record_view(*record),
        ),
{
    match *record {
        KJournalRecord::Authorize { .. }
        | KJournalRecord::Revoke { .. } => true,
        KJournalRecord::Prepare { request, auth_ref, .. } => {
            let found = k_find_latest_reference(
                journal, KReferenceKind::Authorize, request, 0,
            );
            proof {
                k_latest_reference_view_exact(
                    journal@, KReferenceKind::Authorize, request, 0,
                );
            }
            found == Option::Some(auth_ref)
        },
        KJournalRecord::Arm { request, prepare_ref, .. } => {
            let found = k_find_latest_reference(
                journal, KReferenceKind::Prepare, request, 0,
            );
            proof {
                k_latest_reference_view_exact(
                    journal@, KReferenceKind::Prepare, request, 0,
                );
            }
            found == Option::Some(prepare_ref)
        },
        KJournalRecord::Start { request, arm_ref, .. } => {
            let found = k_find_latest_reference(
                journal, KReferenceKind::Arm, request, 0,
            );
            proof {
                k_latest_reference_view_exact(
                    journal@, KReferenceKind::Arm, request, 0,
                );
            }
            found == Option::Some(arm_ref)
        },
        KJournalRecord::Outcome {
            request, attempt, start_ref, ..
        } => {
            let found = k_find_latest_reference(
                journal, KReferenceKind::Start, request, attempt,
            );
            proof {
                k_latest_reference_view_exact(
                    journal@, KReferenceKind::Start, request, attempt,
                );
            }
            found == Option::Some(start_ref)
        },
        KJournalRecord::Commit {
            request, attempt, outcome_ref, ..
        }
        | KJournalRecord::Fail {
            request, attempt, outcome_ref, ..
        } => {
            let found = k_find_latest_reference(
                journal, KReferenceKind::Outcome, request, attempt,
            );
            proof {
                k_latest_reference_view_exact(
                    journal@, KReferenceKind::Outcome, request, attempt,
                );
            }
            found == Option::Some(outcome_ref)
        },
        KJournalRecord::Unknown {
            request, attempt_present, attempt, reason, evidence_ref, ..
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
                    let spec_request = k_request_id(request);
                    let spec_attempt = attempt as nat;
                    let spec_journal = k_journal_seq_view(journal@);
                    k_latest_reference_view_exact(
                        journal@, KReferenceKind::Outcome, request, attempt,
                    );
                    k_latest_reference_view_exact(
                        journal@, KReferenceKind::Start, request, attempt,
                    );
                    query_layer::replay_d_started_exact(
                        k_demo_config(), spec_journal, spec_request,
                    );
                    assert(spec_attempt
                        == replay_layer::started_count(spec_journal, spec_request));
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
    }
}

pub fn k_structural_record_enabled(
    durable: &KDurable,
    journal: &Vec<KJournalRecord>,
    record: &KJournalRecord,
) -> (enabled: bool)
    requires
        journal@.len() < 0xffff_ffff_ffff_ffff,
        replay_layer::config_wf(k_demo_config()),
        replay_layer::journal_legal(
            k_demo_config(), k_journal_seq_view(journal@),
        ),
        k_update_inv(
            *durable,
            k_demo_config(),
            replay_layer::replay(
                k_demo_config(), k_journal_seq_view(journal@),
            ),
        ),
    ensures
        enabled == replay_layer::structural_enabled(
            k_demo_config(),
            k_journal_seq_view(journal@),
            k_journal_record_view(*record),
        ),
{
    let ghost abstract_durable = replay_layer::replay(
        k_demo_config(), k_journal_seq_view(journal@),
    );
    let semantic = k_semantic_record_enabled(
        durable, record, Ghost(abstract_durable),
    );
    if semantic {
        let exact = k_exact_references_enabled(journal, record);
        proof {
            k_abstract_exact_is_structural(
                k_demo_config(),
                k_journal_seq_view(journal@),
                k_journal_record_view(*record),
            );
        }
        exact
    } else {
        proof {
            k_abstract_exact_is_structural(
                k_demo_config(),
                k_journal_seq_view(journal@),
                k_journal_record_view(*record),
            );
        }
        false
    }
}

// K2's public Start and Outcome mutation helpers erase journal references to
// zero.  K3 retains the exact accepted record while reusing K2's generic delta
// refinement lemmas.
pub fn k_apply_exact_start(
    kd: &mut KDurable,
    request_index: usize,
    request: u64,
    attempt: u64,
    digest: u64,
    key_present: bool,
    key: u64,
    arm_ref: u64,
    Ghost(durable): Ghost<replay_layer::DurableBroker>,
)
    requires
        k_update_inv(*old(kd), k_demo_config(), durable),
        request_index < old(kd).requests@.len(),
        old(kd).requests@[request_index as int].request == request,
        query_layer::abstract_record_enabled(
            k_demo_config(),
            durable,
            replay_layer::JournalRecord::Start {
                request: k_request_id(request),
                attempt: attempt as nat,
                digest: k_digest_id(digest),
                key: k_key_view(key_present, key),
                arm_ref: arm_ref as nat,
            },
        ),
    ensures
        k_update_inv(
            *final(kd),
            k_demo_config(),
            replay_layer::apply_record(
                durable,
                replay_layer::JournalRecord::Start {
                    request: k_request_id(request),
                    attempt: attempt as nat,
                    digest: k_digest_id(digest),
                    key: k_key_view(key_present, key),
                    arm_ref: arm_ref as nat,
                },
            ),
        ),
{
    let ghost before = *kd;
    k_push_started(kd, request_index);
    proof {
        let record = replay_layer::JournalRecord::Start {
            request: k_request_id(request),
            attempt: attempt as nat,
            digest: k_digest_id(digest),
            key: k_key_view(key_present, key),
            arm_ref: arm_ref as nat,
        };
        assert(k_start_record_for(record, k_request_id(request)));
        k_start_delta_refines_apply_record(
            before,
            *kd,
            k_demo_config(),
            durable,
            request_index as int,
            record,
        );
    }
}

pub fn k_apply_exact_outcome(
    kd: &mut KDurable,
    request_index: usize,
    request: u64,
    attempt: u64,
    observation: KObservation,
    digest: u64,
    key_present: bool,
    key: u64,
    start_ref: u64,
    Ghost(durable): Ghost<replay_layer::DurableBroker>,
)
    requires
        k_update_inv(*old(kd), k_demo_config(), durable),
        request_index < old(kd).requests@.len(),
        old(kd).requests@[request_index as int].request == request,
        query_layer::abstract_record_enabled(
            k_demo_config(),
            durable,
            replay_layer::JournalRecord::Outcome {
                request: k_request_id(request),
                attempt: attempt as nat,
                observation: k_observation_view(observation),
                digest: k_digest_id(digest),
                key: k_key_view(key_present, key),
                start_ref: start_ref as nat,
            },
        ),
    ensures
        k_update_inv(
            *final(kd),
            k_demo_config(),
            replay_layer::apply_record(
                durable,
                replay_layer::JournalRecord::Outcome {
                    request: k_request_id(request),
                    attempt: attempt as nat,
                    observation: k_observation_view(observation),
                    digest: k_digest_id(digest),
                    key: k_key_view(key_present, key),
                    start_ref: start_ref as nat,
                },
            ),
        ),
{
    proof {
        let entry = old(kd).requests@[request_index as int];
        assert(k_request_entry_couples(entry, durable));
        assert(query_layer::d_started(durable, k_request_id(request))
            == entry.outcomes@.len());
        assert(attempt as nat > 0);
        assert(attempt as nat
            == query_layer::d_started(durable, k_request_id(request)));
        assert(entry.outcomes@.len() > 0);
    }
    let ghost before = *kd;
    k_set_latest_outcome(kd, request_index, observation);
    proof {
        let record = replay_layer::JournalRecord::Outcome {
            request: k_request_id(request),
            attempt: attempt as nat,
            observation: k_observation_view(observation),
            digest: k_digest_id(digest),
            key: k_key_view(key_present, key),
            start_ref: start_ref as nat,
        };
        assert(k_outcome_record_for(
            record, k_request_id(request), observation,
        ));
        k_outcome_delta_refines_apply_record(
            before,
            *kd,
            k_demo_config(),
            durable,
            request_index as int,
            observation,
            record,
        );
    }
}

pub fn k_apply_exact_record(
    kd: &mut KDurable,
    record: KJournalRecord,
    Ghost(durable): Ghost<replay_layer::DurableBroker>,
)
    requires
        k_update_inv(*old(kd), k_demo_config(), durable),
        query_layer::abstract_record_enabled(
            k_demo_config(), durable, k_journal_record_view(record),
        ),
    ensures
        k_update_inv(
            *final(kd),
            k_demo_config(),
            replay_layer::apply_record(
                durable, k_journal_record_view(record),
            ),
        ),
{
    match record {
        KJournalRecord::Authorize { request, capability, digest } => {
            let request_index = k_ensure_request(
                kd, request, Ghost(durable),
            );
            let ghost before_cap = *kd;
            let cap_index = k_ensure_capability(
                kd, capability, Ghost(durable),
            );
            proof {
                if k_tracks_capability(
                    before_cap, capability as nat,
                ) {
                    assert(*kd == before_cap);
                } else {
                    assert(k_default_cap_delta(
                        before_cap, *kd, capability,
                    ));
                    assert(kd.requests@ == before_cap.requests@);
                }
                assert(kd.requests@[request_index as int].request
                    == request);
            }
            k_apply_authorize(
                kd,
                request_index,
                cap_index,
                request,
                capability,
                digest,
                Ghost(durable),
            );
        },
        KJournalRecord::Revoke { capability } => {
            let cap_index = k_ensure_capability(
                kd, capability, Ghost(durable),
            );
            k_apply_revoke(
                kd, cap_index, capability, Ghost(durable),
            );
        },
        KJournalRecord::Prepare { request, .. } => {
            let request_index = k_ensure_request(
                kd, request, Ghost(durable),
            );
            proof {
                assert(k_phase_record_shape(
                    k_journal_record_view(record),
                    k_request_id(request),
                    k_phase_view(KPhase::Prepared),
                ));
            }
            k_apply_phase_record(
                kd,
                request_index,
                KPhase::Prepared,
                Ghost(k_journal_record_view(record)),
                Ghost(durable),
            );
        },
        KJournalRecord::Arm { request, .. } => {
            let request_index = k_ensure_request(
                kd, request, Ghost(durable),
            );
            proof {
                assert(k_phase_record_shape(
                    k_journal_record_view(record),
                    k_request_id(request),
                    k_phase_view(KPhase::Armed),
                ));
            }
            k_apply_phase_record(
                kd,
                request_index,
                KPhase::Armed,
                Ghost(k_journal_record_view(record)),
                Ghost(durable),
            );
        },
        KJournalRecord::Start {
            request, attempt, digest, key_present, key, arm_ref,
        } => {
            let request_index = k_ensure_request(
                kd, request, Ghost(durable),
            );
            k_apply_exact_start(
                kd,
                request_index,
                request,
                attempt,
                digest,
                key_present,
                key,
                arm_ref,
                Ghost(durable),
            );
        },
        KJournalRecord::Outcome {
            request, attempt, observation, digest,
            key_present, key, start_ref,
        } => {
            let request_index = k_ensure_request(
                kd, request, Ghost(durable),
            );
            k_apply_exact_outcome(
                kd,
                request_index,
                request,
                attempt,
                observation,
                digest,
                key_present,
                key,
                start_ref,
                Ghost(durable),
            );
        },
        KJournalRecord::Commit { request, .. } => {
            let request_index = k_ensure_request(
                kd, request, Ghost(durable),
            );
            proof {
                assert(k_phase_record_shape(
                    k_journal_record_view(record),
                    k_request_id(request),
                    k_phase_view(KPhase::Committed),
                ));
            }
            k_apply_phase_record(
                kd,
                request_index,
                KPhase::Committed,
                Ghost(k_journal_record_view(record)),
                Ghost(durable),
            );
        },
        KJournalRecord::Fail { request, .. } => {
            let request_index = k_ensure_request(
                kd, request, Ghost(durable),
            );
            proof {
                assert(k_phase_record_shape(
                    k_journal_record_view(record),
                    k_request_id(request),
                    k_phase_view(KPhase::Failed),
                ));
            }
            k_apply_phase_record(
                kd,
                request_index,
                KPhase::Failed,
                Ghost(k_journal_record_view(record)),
                Ghost(durable),
            );
        },
        KJournalRecord::Unknown { request, .. } => {
            let request_index = k_ensure_request(
                kd, request, Ghost(durable),
            );
            proof {
                assert(k_phase_record_shape(
                    k_journal_record_view(record),
                    k_request_id(request),
                    k_phase_view(KPhase::Unknown),
                ));
            }
            k_apply_phase_record(
                kd,
                request_index,
                KPhase::Unknown,
                Ghost(k_journal_record_view(record)),
                Ghost(durable),
            );
        },
    }
}

#[derive(PartialEq, Eq, Clone, Copy)]
pub enum KAppendControl {
    Idle,
    Called { record: KJournalRecord },
    Linearized { record: KJournalRecord, lsn: u64 },
}

pub struct KKernelState {
    pub durable: KDurable,
    pub journal: Vec<KJournalRecord>,
    pub ack_cuts: Vec<u64>,
    pub append: KAppendControl,
}

pub open spec fn k_ack_seq_view(cuts: Seq<u64>) -> Seq<nat>
    decreases cuts.len(),
{
    if cuts.len() == 0 {
        Seq::empty()
    } else {
        k_ack_seq_view(cuts.drop_last()).push(cuts.last() as nat)
    }
}

pub proof fn k_ack_seq_view_push(cuts: Seq<u64>, cut: u64)
    ensures
        k_ack_seq_view(cuts.push(cut))
            == k_ack_seq_view(cuts).push(cut as nat),
{
    assert(cuts.push(cut).drop_last() =~= cuts);
    assert(cuts.push(cut).last() == cut);
}

pub proof fn k_ack_seq_view_len(cuts: Seq<u64>)
    ensures
        k_ack_seq_view(cuts).len() == cuts.len(),
    decreases cuts.len(),
{
    if cuts.len() > 0 {
        k_ack_seq_view_len(cuts.drop_last());
    }
}

pub open spec fn k_append_control_view(
    control: KAppendControl,
) -> append_layer::AppendControl<replay_layer::JournalRecord> {
    match control {
        KAppendControl::Idle => append_layer::AppendControl::Idle,
        KAppendControl::Called { record } =>
            append_layer::AppendControl::Called {
                record: k_journal_record_view(record),
            },
        KAppendControl::Linearized { record, .. } =>
            append_layer::AppendControl::Linearized {
                record: k_journal_record_view(record),
            },
    }
}

pub open spec fn k_append_view(
    state: KKernelState,
) -> append_layer::State<replay_layer::JournalRecord> {
    let records = k_journal_seq_view(state.journal@);
    let cuts = k_ack_seq_view(state.ack_cuts@);
    append_layer::State {
        append: k_append_control_view(state.append),
        evidence: append_layer::AppendGhost {
            records,
            ack_cuts: cuts,
            acknowledged_prefix:
                append_layer::acknowledged_prefix_for(records, cuts),
        },
    }
}

pub open spec fn k3_control_exact(state: KKernelState) -> bool {
    match state.append {
        KAppendControl::Idle => true,
        KAppendControl::Called { .. } =>
            state.journal@.len() < 0xffff_ffff_ffff_ffff,
        KAppendControl::Linearized { record, lsn } => {
            &&& state.journal@.len() > 0
            &&& state.journal@.last() == record
            &&& lsn as nat == state.journal@.len()
        },
    }
}

pub open spec fn k3_inv(state: KKernelState) -> bool {
    let journal = k_journal_seq_view(state.journal@);
    let view = k_append_view(state);
    &&& state.journal@.len() <= 0xffff_ffff_ffff_ffff
    &&& replay_layer::config_wf(k_demo_config())
    &&& replay_layer::journal_legal(k_demo_config(), journal)
    &&& k_update_inv(
        state.durable,
        k_demo_config(),
        replay_layer::replay(k_demo_config(), journal),
    )
    &&& append_layer::b1_invariant(view)
    &&& append_layer::legal_control_shape(
        c1_layer::c1_eligibility(k_demo_config()), view,
    )
    &&& k3_control_exact(state)
}

pub fn k3_initial() -> (state: KKernelState)
    ensures
        k3_inv(state),
        k_append_view(state)
            == append_layer::initial_state::<replay_layer::JournalRecord>(),
{
    let state = KKernelState {
        durable: KDurable {
            requests: Vec::new(),
            caps: Vec::new(),
        },
        journal: Vec::new(),
        ack_cuts: Vec::new(),
        append: KAppendControl::Idle,
    };
    proof {
        k_demo_config_is_well_formed();
        k_initial_satisfies_update_inv(
            state.durable,
            k_demo_config(),
        );
        append_layer::initial_invariant::<
            replay_layer::JournalRecord
        >();
        assert(k_journal_seq_view(state.journal@) =~= Seq::empty());
        assert(k_ack_seq_view(state.ack_cuts@) =~= Seq::empty());
        assert(k_append_view(state)
            == append_layer::initial_state::<
                replay_layer::JournalRecord
            >());
        assert(append_layer::legal_control_shape(
            c1_layer::c1_eligibility(k_demo_config()),
            k_append_view(state),
        ));
    }
    state
}

pub proof fn k3_b1_projection_step_exact(
    events: Seq<append_layer::Event<replay_layer::JournalRecord>>,
    event: append_layer::Event<replay_layer::JournalRecord>,
)
    ensures
        append_layer::pi_append(events.push(event)) == match event {
            append_layer::Event::Call { record } =>
                append_layer::pi_append(events).push(
                    append_layer::AppendEvent::Call { record },
                ),
            append_layer::Event::Linearize { record } =>
                append_layer::pi_append(events).push(
                    append_layer::AppendEvent::Linearize { record },
                ),
            append_layer::Event::ReturnOk { cut } =>
                append_layer::pi_append(events).push(
                    append_layer::AppendEvent::Return {
                        result: append_layer::AppendResult::Ok,
                        cut,
                    },
                ),
            append_layer::Event::DiskFull { record, cut } =>
                append_layer::pi_append(events)
                    .push(append_layer::AppendEvent::Call { record })
                    .push(append_layer::AppendEvent::Return {
                        result: append_layer::AppendResult::Full,
                        cut,
                    }),
            append_layer::Event::Crash
            | append_layer::Event::Stutter { .. } =>
                append_layer::pi_append(events),
        },
        append_layer::pi_journal(events.push(event)) == match event {
            append_layer::Event::Linearize { record } =>
                append_layer::pi_journal(events).push(record),
            append_layer::Event::Call { .. }
            | append_layer::Event::ReturnOk { .. }
            | append_layer::Event::DiskFull { .. }
            | append_layer::Event::Crash
            | append_layer::Event::Stutter { .. } =>
                append_layer::pi_journal(events),
        },
        append_layer::pi_ack(events.push(event)) == match event {
            append_layer::Event::ReturnOk { cut } =>
                append_layer::pi_ack(events).push(cut),
            append_layer::Event::Call { .. }
            | append_layer::Event::Linearize { .. }
            | append_layer::Event::DiskFull { .. }
            | append_layer::Event::Crash
            | append_layer::Event::Stutter { .. } =>
                append_layer::pi_ack(events),
        },
{
    append_layer::b1_projection_step_exact(events, event);
}

pub proof fn k3_b1_run_push(
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

pub proof fn k3_b1_admissibly_executable_push(
    events: Seq<append_layer::Event<replay_layer::JournalRecord>>,
    event: append_layer::Event<replay_layer::JournalRecord>,
)
    requires
        append_layer::admissibly_executable(
            c1_layer::c1_eligibility(k_demo_config()), events,
        ),
        append_layer::enabled(append_layer::run(events), event),
        append_layer::record_eligible(
            c1_layer::c1_eligibility(k_demo_config()),
            append_layer::run(events),
            event,
        ),
    ensures
        append_layer::admissibly_executable(
            c1_layer::c1_eligibility(k_demo_config()),
            events.push(event),
        ),
{
    assert(events.push(event).len() > 0);
    assert(events.push(event).drop_last() =~= events);
    assert(events.push(event).last() == event);
}

pub fn k_retry_class_equal(
    left: KRetryClass,
    right: KRetryClass,
) -> (equal: bool)
    ensures
        equal == (left == right),
{
    match left {
        KRetryClass::ReadOnly => match right {
            KRetryClass::ReadOnly => true,
            _ => false,
        },
        KRetryClass::Idempotent => match right {
            KRetryClass::Idempotent => true,
            _ => false,
        },
        KRetryClass::Deduplicated => match right {
            KRetryClass::Deduplicated => true,
            _ => false,
        },
        KRetryClass::Uncontrolled => match right {
            KRetryClass::Uncontrolled => true,
            _ => false,
        },
    }
}

pub fn k_observation_equal(
    left: KObservation,
    right: KObservation,
) -> (equal: bool)
    ensures
        equal == (left == right),
{
    match left {
        KObservation::Success { value } => match right {
            KObservation::Success { value: other } => value == other,
            _ => false,
        },
        KObservation::Failure => match right {
            KObservation::Failure => true,
            _ => false,
        },
        KObservation::Ambiguous => match right {
            KObservation::Ambiguous => true,
            _ => false,
        },
        KObservation::InvalidResult { value } => match right {
            KObservation::InvalidResult { value: other } => value == other,
            _ => false,
        },
    }
}

pub fn k_unknown_reason_equal(
    left: KUnknownReason,
    right: KUnknownReason,
) -> (equal: bool)
    ensures
        equal == (left == right),
{
    match left {
        KUnknownReason::Exhausted => match right {
            KUnknownReason::Exhausted => true,
            _ => false,
        },
        KUnknownReason::Recovery => match right {
            KUnknownReason::Recovery => true,
            _ => false,
        },
        KUnknownReason::NonConclusiveFailure => match right {
            KUnknownReason::NonConclusiveFailure => true,
            _ => false,
        },
        KUnknownReason::AmbiguousOutcome => match right {
            KUnknownReason::AmbiguousOutcome => true,
            _ => false,
        },
        KUnknownReason::InvalidResultReason => match right {
            KUnknownReason::InvalidResultReason => true,
            _ => false,
        },
    }
}

pub fn k_journal_record_equal(
    left: KJournalRecord,
    right: KJournalRecord,
) -> (equal: bool)
    ensures
        equal == (left == right),
{
    match left {
        KJournalRecord::Authorize { request, capability, digest } =>
            match right {
                KJournalRecord::Authorize {
                    request: other_request,
                    capability: other_capability,
                    digest: other_digest,
                } => request == other_request
                    && capability == other_capability
                    && digest == other_digest,
                _ => false,
            },
        KJournalRecord::Revoke { capability } => match right {
            KJournalRecord::Revoke { capability: other } =>
                capability == other,
            _ => false,
        },
        KJournalRecord::Prepare {
            request, class, digest, key_present, key, auth_ref,
        } => match right {
            KJournalRecord::Prepare {
                request: other_request,
                class: other_class,
                digest: other_digest,
                key_present: other_key_present,
                key: other_key,
                auth_ref: other_auth_ref,
            } => request == other_request
                && k_retry_class_equal(class, other_class)
                && digest == other_digest
                && key_present == other_key_present
                && key == other_key
                && auth_ref == other_auth_ref,
            _ => false,
        },
        KJournalRecord::Arm {
            request, digest, key_present, key, prepare_ref,
        } => match right {
            KJournalRecord::Arm {
                request: other_request,
                digest: other_digest,
                key_present: other_key_present,
                key: other_key,
                prepare_ref: other_prepare_ref,
            } => request == other_request
                && digest == other_digest
                && key_present == other_key_present
                && key == other_key
                && prepare_ref == other_prepare_ref,
            _ => false,
        },
        KJournalRecord::Start {
            request, attempt, digest, key_present, key, arm_ref,
        } => match right {
            KJournalRecord::Start {
                request: other_request,
                attempt: other_attempt,
                digest: other_digest,
                key_present: other_key_present,
                key: other_key,
                arm_ref: other_arm_ref,
            } => request == other_request
                && attempt == other_attempt
                && digest == other_digest
                && key_present == other_key_present
                && key == other_key
                && arm_ref == other_arm_ref,
            _ => false,
        },
        KJournalRecord::Outcome {
            request, attempt, observation, digest,
            key_present, key, start_ref,
        } => match right {
            KJournalRecord::Outcome {
                request: other_request,
                attempt: other_attempt,
                observation: other_observation,
                digest: other_digest,
                key_present: other_key_present,
                key: other_key,
                start_ref: other_start_ref,
            } => request == other_request
                && attempt == other_attempt
                && k_observation_equal(observation, other_observation)
                && digest == other_digest
                && key_present == other_key_present
                && key == other_key
                && start_ref == other_start_ref,
            _ => false,
        },
        KJournalRecord::Commit {
            request, attempt, value, digest,
            key_present, key, outcome_ref,
        } => match right {
            KJournalRecord::Commit {
                request: other_request,
                attempt: other_attempt,
                value: other_value,
                digest: other_digest,
                key_present: other_key_present,
                key: other_key,
                outcome_ref: other_outcome_ref,
            } => request == other_request
                && attempt == other_attempt
                && value == other_value
                && digest == other_digest
                && key_present == other_key_present
                && key == other_key
                && outcome_ref == other_outcome_ref,
            _ => false,
        },
        KJournalRecord::Fail {
            request, attempt, digest, key_present, key, outcome_ref,
        } => match right {
            KJournalRecord::Fail {
                request: other_request,
                attempt: other_attempt,
                digest: other_digest,
                key_present: other_key_present,
                key: other_key,
                outcome_ref: other_outcome_ref,
            } => request == other_request
                && attempt == other_attempt
                && digest == other_digest
                && key_present == other_key_present
                && key == other_key
                && outcome_ref == other_outcome_ref,
            _ => false,
        },
        KJournalRecord::Unknown {
            request, attempt_present, attempt, reason, digest,
            key_present, key, evidence_ref,
        } => match right {
            KJournalRecord::Unknown {
                request: other_request,
                attempt_present: other_attempt_present,
                attempt: other_attempt,
                reason: other_reason,
                digest: other_digest,
                key_present: other_key_present,
                key: other_key,
                evidence_ref: other_evidence_ref,
            } => request == other_request
                && attempt_present == other_attempt_present
                && attempt == other_attempt
                && k_unknown_reason_equal(reason, other_reason)
                && digest == other_digest
                && key_present == other_key_present
                && key == other_key
                && evidence_ref == other_evidence_ref,
            _ => false,
        },
    }
}

#[derive(PartialEq, Eq, Clone, Copy)]
pub enum KKernelEvent {
    Call { record: KJournalRecord },
    Linearize { record: KJournalRecord },
    ReturnOk { cut: u64 },
}

pub open spec fn k_kernel_event_view(
    event: KKernelEvent,
) -> append_layer::Event<replay_layer::JournalRecord> {
    match event {
        KKernelEvent::Call { record } => append_layer::Event::Call {
            record: k_journal_record_view(record),
        },
        KKernelEvent::Linearize { record } =>
            append_layer::Event::Linearize {
                record: k_journal_record_view(record),
            },
        KKernelEvent::ReturnOk { cut } =>
            append_layer::Event::ReturnOk { cut: cut as nat },
    }
}

pub open spec fn k_kernel_event_seq_view(
    events: Seq<KKernelEvent>,
) -> Seq<append_layer::Event<replay_layer::JournalRecord>>
    decreases events.len(),
{
    if events.len() == 0 {
        Seq::empty()
    } else {
        k_kernel_event_seq_view(events.drop_last()).push(
            k_kernel_event_view(events.last()),
        )
    }
}

pub proof fn k_kernel_event_seq_view_push(
    events: Seq<KKernelEvent>,
    event: KKernelEvent,
)
    ensures
        k_kernel_event_seq_view(events.push(event))
            == k_kernel_event_seq_view(events).push(
                k_kernel_event_view(event),
            ),
{
    assert(events.push(event).drop_last() =~= events);
    assert(events.push(event).last() == event);
}

pub open spec fn k_kernel_append_history(
    events: Seq<KKernelEvent>,
) -> Seq<append_layer::AppendEvent<replay_layer::JournalRecord>>
    decreases events.len(),
{
    if events.len() == 0 {
        Seq::empty()
    } else {
        let prefix = events.drop_last();
        match events.last() {
            KKernelEvent::Call { record } =>
                k_kernel_append_history(prefix).push(
                    append_layer::AppendEvent::Call {
                        record: k_journal_record_view(record),
                    },
                ),
            KKernelEvent::Linearize { record } =>
                k_kernel_append_history(prefix).push(
                    append_layer::AppendEvent::Linearize {
                        record: k_journal_record_view(record),
                    },
                ),
            KKernelEvent::ReturnOk { cut } =>
                k_kernel_append_history(prefix).push(
                    append_layer::AppendEvent::Return {
                        result: append_layer::AppendResult::Ok,
                        cut: cut as nat,
                    },
                ),
        }
    }
}

pub proof fn k_kernel_append_history_push(
    events: Seq<KKernelEvent>,
    event: KKernelEvent,
)
    ensures
        k_kernel_append_history(events.push(event)) == match event {
            KKernelEvent::Call { record } =>
                k_kernel_append_history(events).push(
                    append_layer::AppendEvent::Call {
                        record: k_journal_record_view(record),
                    },
                ),
            KKernelEvent::Linearize { record } =>
                k_kernel_append_history(events).push(
                    append_layer::AppendEvent::Linearize {
                        record: k_journal_record_view(record),
                    },
                ),
            KKernelEvent::ReturnOk { cut } =>
                k_kernel_append_history(events).push(
                    append_layer::AppendEvent::Return {
                        result: append_layer::AppendResult::Ok,
                        cut: cut as nat,
                    },
                ),
        },
{
    assert(events.push(event).drop_last() =~= events);
    assert(events.push(event).last() == event);
}

pub open spec fn k3_successful_step(
    before: KKernelState,
    event: KKernelEvent,
    after: KKernelState,
) -> bool {
    let before_view = k_append_view(before);
    let projected = k_kernel_event_view(event);
    &&& k3_inv(before)
    &&& k3_inv(after)
    &&& append_layer::enabled(before_view, projected)
    &&& append_layer::record_eligible(
        c1_layer::c1_eligibility(k_demo_config()),
        before_view,
        projected,
    )
    &&& k_append_view(after)
        == append_layer::apply(before_view, projected)
}

pub open spec fn k3_successful_trace(
    start: KKernelState,
    events: Seq<KKernelEvent>,
    end: KKernelState,
) -> bool
    decreases events.len(),
{
    if events.len() == 0 {
        end == start
    } else {
        exists|middle: KKernelState|
            k3_successful_trace(start, events.drop_last(), middle)
                && k3_successful_step(middle, events.last(), end)
    }
}

pub fn k3_try_call(
    state: &mut KKernelState,
    record: KJournalRecord,
) -> (accepted: bool)
    requires
        k3_inv(*old(state)),
        old(state).append is Idle,
    ensures
        k3_inv(*final(state)),
        accepted == (
            old(state).journal@.len() < 0xffff_ffff_ffff_ffff
                && replay_layer::structural_enabled(
                    k_demo_config(),
                    k_journal_seq_view(old(state).journal@),
                    k_journal_record_view(record),
                )
        ),
        accepted ==> {
            &&& final(state).durable == old(state).durable
            &&& final(state).journal@ == old(state).journal@
            &&& final(state).ack_cuts@ == old(state).ack_cuts@
            &&& final(state).append
                == KAppendControl::Called { record }
            &&& k_append_view(*final(state))
                == append_layer::apply(
                    k_append_view(*old(state)),
                    append_layer::Event::Call {
                        record: k_journal_record_view(record),
                    },
                )
        },
        accepted ==> k3_successful_step(
            *old(state),
            KKernelEvent::Call { record },
            *final(state),
        ),
        !accepted ==> *final(state) == *old(state),
{
    let journal_len = state.journal.len() as u64;
    if journal_len == 0xffff_ffff_ffff_ffffu64 {
        return false;
    }
    let enabled = k_structural_record_enabled(
        &state.durable, &state.journal, &record,
    );
    if !enabled {
        return false;
    }

    let ghost before = *state;
    let ghost before_view = k_append_view(before);
    let ghost event = append_layer::Event::Call {
        record: k_journal_record_view(record),
    };
    proof {
        assert(append_layer::enabled(before_view, event));
        assert(append_layer::record_eligible(
            c1_layer::c1_eligibility(k_demo_config()),
            before_view,
            event,
        ));
        append_layer::step_preserves_invariant(before_view, event);
        append_layer::step_preserves_legal_control(
            c1_layer::c1_eligibility(k_demo_config()),
            before_view,
            event,
        );
    }
    state.append = KAppendControl::Called { record };
    proof {
        assert(k_append_view(*state)
            == append_layer::apply(before_view, event));
        assert(k3_control_exact(*state));
    }
    true
}

pub fn k3_linearize(
    state: &mut KKernelState,
    record: KJournalRecord,
) -> (linearized: Option<u64>)
    requires
        k3_inv(*old(state)),
    ensures
        k3_inv(*final(state)),
        linearized.is_some() <==> match old(state).append {
            KAppendControl::Called { record: called } => called == record,
            KAppendControl::Idle
            | KAppendControl::Linearized { .. } => false,
        },
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
        linearized.is_some() ==> k3_successful_step(
            *old(state),
            KKernelEvent::Linearize { record },
            *final(state),
        ),
{
    let called = match state.append {
        KAppendControl::Called { record: called } => called,
        KAppendControl::Idle
        | KAppendControl::Linearized { .. } => {
            return Option::None;
        },
    };
    if !k_journal_record_equal(called, record) {
        return Option::None;
    }

    let ghost before = *state;
    let ghost before_journal = k_journal_seq_view(before.journal@);
    let ghost spec_record = k_journal_record_view(record);
    let ghost durable = replay_layer::replay(
        k_demo_config(), before_journal,
    );
    let ghost before_view = k_append_view(before);
    let ghost event = append_layer::Event::Linearize {
        record: spec_record,
    };
    proof {
        assert(called == record);
        assert(before.append == KAppendControl::Called { record });
        assert(before_view.append
            == append_layer::AppendControl::Called {
                record: spec_record,
            });
        assert(append_layer::enabled(before_view, event));
        assert(replay_layer::structural_enabled(
            k_demo_config(), before_journal, spec_record,
        ));
        assert(append_layer::record_eligible(
            c1_layer::c1_eligibility(k_demo_config()),
            before_view,
            event,
        ));
        query_layer::structural_enabled_implies_abstract_record_enabled(
            k_demo_config(), before_journal, spec_record,
        );
        append_layer::step_preserves_invariant(before_view, event);
        append_layer::step_preserves_legal_control(
            c1_layer::c1_eligibility(k_demo_config()),
            before_view,
            event,
        );
        append_layer::acknowledged_prefix_survives_record_push(
            before_view.evidence.records,
            before_view.evidence.ack_cuts,
            spec_record,
        );
    }

    k_apply_exact_record(
        &mut state.durable, record, Ghost(durable),
    );
    let old_len = state.journal.len();
    let old_len_u64 = old_len as u64;
    let lsn = old_len_u64 + 1;
    state.journal.push(record);
    state.append = KAppendControl::Linearized { record, lsn };
    proof {
        k_journal_seq_view_push(before.journal@, record);
        k_journal_seq_view_len(before.journal@);
        k_update_inv_lifts_through_replay_push(
            state.durable,
            k_demo_config(),
            before_journal,
            spec_record,
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

pub fn k3_return(
    state: &mut KKernelState,
) -> (returned: Option<u64>)
    requires
        k3_inv(*old(state)),
    ensures
        k3_inv(*final(state)),
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
        match returned {
            Option::Some(cut) => k3_successful_step(
                *old(state),
                KKernelEvent::ReturnOk { cut },
                *final(state),
            ),
            Option::None => true,
        },
{
    let (stored_record, stored_lsn) = match state.append {
        KAppendControl::Linearized { record, lsn } => (record, lsn),
        KAppendControl::Idle
        | KAppendControl::Called { .. } => {
            return Option::None;
        },
    };

    let cut = state.journal.len() as u64;
    let ghost before = *state;
    let ghost before_view = k_append_view(before);
    let ghost event = append_layer::Event::ReturnOk {
        cut: cut as nat,
    };
    proof {
        assert(before.append == KAppendControl::Linearized {
            record: stored_record,
            lsn: stored_lsn,
        });
        assert(cut == stored_lsn);
        k_journal_seq_view_len(before.journal@);
        assert(before_view.evidence.records.len()
            == cut as nat);
        assert(before_view.append
            == append_layer::AppendControl::Linearized {
                record: k_journal_record_view(stored_record),
            });
        assert(append_layer::enabled(before_view, event));
        assert(append_layer::record_eligible(
            c1_layer::c1_eligibility(k_demo_config()),
            before_view,
            event,
        ));
        append_layer::step_preserves_invariant(before_view, event);
        append_layer::step_preserves_legal_control(
            c1_layer::c1_eligibility(k_demo_config()),
            before_view,
            event,
        );
        append_layer::take_full(before_view.evidence.records);
    }
    state.ack_cuts.push(cut);
    state.append = KAppendControl::Idle;
    proof {
        k_ack_seq_view_push(before.ack_cuts@, cut);
        assert(k_append_view(*state)
            == append_layer::apply(before_view, event));
        assert(k3_control_exact(*state));
    }
    Option::Some(cut)
}

pub proof fn k3_successful_trace_projects(
    start: KKernelState,
    events: Seq<KKernelEvent>,
    end: KKernelState,
)
    requires
        k3_inv(start),
        k_append_view(start)
            == append_layer::initial_state::<
                replay_layer::JournalRecord
            >(),
        k3_successful_trace(start, events, end),
    ensures
        append_layer::admissibly_executable(
            c1_layer::c1_eligibility(k_demo_config()),
            k_kernel_event_seq_view(events),
        ),
        k_append_view(end)
            == append_layer::run(k_kernel_event_seq_view(events)),
        k_journal_seq_view(end.journal@)
            == append_layer::pi_journal(
                k_kernel_event_seq_view(events),
            ),
        k_ack_seq_view(end.ack_cuts@)
            == append_layer::pi_ack(
                k_kernel_event_seq_view(events),
            ),
        k_kernel_append_history(events)
            == append_layer::pi_append(
                k_kernel_event_seq_view(events),
            ),
    decreases events.len(),
{
    if events.len() == 0 {
        assert(events =~= Seq::empty());
        assert(end == start);
        assert(k_kernel_event_seq_view(events) =~= Seq::empty());
        assert(k_kernel_append_history(events) =~= Seq::empty());
    } else {
        let prefix = events.drop_last();
        let event = events.last();
        assert(exists|middle: KKernelState|
            k3_successful_trace(start, prefix, middle)
                && k3_successful_step(middle, event, end));
        let middle = choose|middle: KKernelState|
            k3_successful_trace(start, prefix, middle)
                && k3_successful_step(middle, event, end);
        k3_successful_trace_projects(start, prefix, middle);

        let projected_prefix = k_kernel_event_seq_view(prefix);
        let projected_event = k_kernel_event_view(event);
        k_kernel_event_seq_view_push(prefix, event);
        k_kernel_append_history_push(prefix, event);
        assert(events =~= prefix.push(event));
        assert(k_kernel_event_seq_view(events)
            == projected_prefix.push(projected_event));
        assert(k3_successful_step(middle, event, end));
        assert(k_append_view(middle)
            == append_layer::run(projected_prefix));
        assert(k_append_view(end)
            == append_layer::apply(
                k_append_view(middle), projected_event,
            ));
        k3_b1_run_push(projected_prefix, projected_event);
        assert(k_append_view(end)
            == append_layer::run(k_kernel_event_seq_view(events)));

        assert(append_layer::admissibly_executable(
            c1_layer::c1_eligibility(k_demo_config()),
            projected_prefix,
        ));
        assert(append_layer::enabled(
            append_layer::run(projected_prefix), projected_event,
        ));
        assert(append_layer::record_eligible(
            c1_layer::c1_eligibility(k_demo_config()),
            append_layer::run(projected_prefix),
            projected_event,
        ));
        k3_b1_admissibly_executable_push(
            projected_prefix, projected_event,
        );

        k3_b1_projection_step_exact(projected_prefix, projected_event);
        match event {
            KKernelEvent::Call { .. }
            | KKernelEvent::Linearize { .. }
            | KKernelEvent::ReturnOk { .. } => {},
        }
        assert(k_kernel_append_history(events)
            == append_layer::pi_append(
                k_kernel_event_seq_view(events),
            ));
    }

    let projected = k_kernel_event_seq_view(events);
    append_layer::admissible_trace_checkpoint(
        c1_layer::c1_eligibility(k_demo_config()), projected,
    );
    assert(append_layer::history_agreement(
        append_layer::run(projected), projected,
    ));
    assert(k_append_view(end).evidence.records
        == k_journal_seq_view(end.journal@));
    assert(k_append_view(end).evidence.ack_cuts
        == k_ack_seq_view(end.ack_cuts@));
}

} // verus!
