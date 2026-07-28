use vstd::prelude::*;

#[path = "k2_executable_kernel_refinement.rs"]
pub mod k2_guard_layer;

verus! {

use k2_guard_layer::*;
use k2_guard_layer::k1_layer::*;
use k2_guard_layer::k1_layer::query_layer;
use query_layer::c1_layer::replay_layer;

broadcast use {
    vstd::imap::group_imap_lemmas,
    vstd::iset::group_iset_lemmas,
};

// K2-T0 adds executable durable-summary mutations to K2-G0's complete guard
// surface.  Each small mutation first exposes a precise sequence delta; the
// refinement lemmas then couple that delta to replay_layer::apply_record and
// replay_push.  This is not a complete event loop: exact LSN references,
// append control, executor slots, invocation, and crash recovery remain later
// kernel milestones.

pub open spec fn k_no_future_outcomes(
    durable: replay_layer::DurableBroker,
) -> bool {
    forall|request: replay_layer::RequestId,
           attempt: replay_layer::AttemptId|
        attempt > query_layer::d_started(durable, request) ==>
            #[trigger] query_layer::d_outcome(durable, request, attempt).is_none()
}

pub open spec fn k_update_inv(
    kd: KDurable,
    cfg: replay_layer::Config,
    durable: replay_layer::DurableBroker,
) -> bool {
    k_durable_inv(kd, cfg, durable) && k_no_future_outcomes(durable)
}

// KDurable observes only these replay projections.  Authorization and terminal
// records also update provenance fields that deliberately remain ghost-only.
pub open spec fn k_observed_durable_eq(
    left: replay_layer::DurableBroker,
    right: replay_layer::DurableBroker,
) -> bool {
    &&& left.phase == right.phase
    &&& left.remaining == right.remaining
    &&& left.revoked == right.revoked
    &&& left.witness == right.witness
    &&& left.attempt_log == right.attempt_log
}

pub proof fn k_update_inv_observed_transport(
    kd: KDurable,
    cfg: replay_layer::Config,
    left: replay_layer::DurableBroker,
    right: replay_layer::DurableBroker,
)
    requires
        k_update_inv(kd, cfg, left),
        k_observed_durable_eq(left, right),
    ensures
        k_update_inv(kd, cfg, right),
{
    assert forall|request: replay_layer::RequestId|
        query_layer::d_started(left, request)
            == query_layer::d_started(right, request) by {
    }
    assert forall|request: replay_layer::RequestId,
                  attempt: replay_layer::AttemptId|
        query_layer::d_outcome(left, request, attempt)
            == query_layer::d_outcome(right, request, attempt) by {
    }
    assert(k_durable_inv(kd, cfg, right));
    assert forall|request: replay_layer::RequestId,
                  attempt: replay_layer::AttemptId|
        attempt > query_layer::d_started(right, request) implies
            #[trigger] query_layer::d_outcome(right, request, attempt).is_none() by {
    }
}

pub proof fn k_update_inv_lifts_through_replay_push(
    kd: KDurable,
    cfg: replay_layer::Config,
    journal: Seq<replay_layer::JournalRecord>,
    record: replay_layer::JournalRecord,
)
    requires
        replay_layer::config_wf(cfg),
        replay_layer::journal_legal(cfg, journal),
        replay_layer::structural_enabled(cfg, journal, record),
        k_update_inv(
            kd,
            cfg,
            replay_layer::apply_record(
                replay_layer::replay(cfg, journal), record,
            ),
        ),
    ensures
        replay_layer::journal_legal(cfg, journal.push(record)),
        k_update_inv(
            kd,
            cfg,
            replay_layer::replay(cfg, journal.push(record)),
        ),
{
    replay_layer::journal_legal_push(cfg, journal, record);
    replay_layer::replay_push(cfg, journal, record);
}

pub proof fn k_initial_satisfies_update_inv(
    kd: KDurable,
    cfg: replay_layer::Config,
)
    requires
        kd.requests@.len() == 0,
        kd.caps@.len() == 0,
    ensures
        k_update_inv(kd, cfg, replay_layer::initial_durable(cfg)),
{
    k_initial_satisfies_inv(kd, cfg);
    let durable = replay_layer::initial_durable(cfg);
    assert forall|request: replay_layer::RequestId,
                  attempt: replay_layer::AttemptId|
        attempt > query_layer::d_started(durable, request) implies
            #[trigger] query_layer::d_outcome(durable, request, attempt).is_none() by {
        assert(durable.attempt_log =~= Seq::<replay_layer::AttemptEntry>::empty());
        reveal_with_fuel(query_layer::attempt_log_started, 2);
        reveal_with_fuel(query_layer::attempt_log_outcome, 2);
    }
}

pub open spec fn k_phase_delta(
    before: KDurable,
    after: KDurable,
    index: int,
    phase: KPhase,
) -> bool {
    &&& k_requests_same_except(before, after, index)
    &&& after.requests@[index].request == before.requests@[index].request
    &&& after.requests@[index].phase == phase
    &&& after.requests@[index].witness == before.requests@[index].witness
    &&& after.requests@[index].outcomes@ == before.requests@[index].outcomes@
    &&& after.caps@ == before.caps@
}

pub open spec fn k_requests_same_except(
    before: KDurable,
    after: KDurable,
    index: int,
) -> bool {
    &&& 0 <= index < before.requests@.len()
    &&& after.requests@.len() == before.requests@.len()
    &&& forall|other: int| 0 <= other < before.requests@.len()
        && other != index ==> #[trigger] after.requests@[other]
            == before.requests@[other]
}

pub open spec fn k_caps_same_except(
    before: KDurable,
    after: KDurable,
    index: int,
) -> bool {
    &&& 0 <= index < before.caps@.len()
    &&& after.caps@.len() == before.caps@.len()
    &&& forall|other: int| 0 <= other < before.caps@.len()
        && other != index ==> #[trigger] after.caps@[other]
            == before.caps@[other]
}

pub proof fn k_requests_same_except_preserves_keys(
    before: KDurable,
    after: KDurable,
    index: int,
)
    requires
        k_requests_same_except(before, after, index),
        after.requests@[index].request == before.requests@[index].request,
    ensures
        forall|other: int| 0 <= other < before.requests@.len() ==>
            #[trigger] after.requests@[other].request
                == before.requests@[other].request,
        forall|id: nat| #[trigger] k_tracks_request(after, id)
            <==> k_tracks_request(before, id),
{
    assert forall|other: int| 0 <= other < before.requests@.len() implies
        #[trigger] after.requests@[other].request
            == before.requests@[other].request by {
        if other != index {
            assert(after.requests@[other] == before.requests@[other]);
        }
    }
    assert forall|id: nat| k_tracks_request(after, id)
        implies #[trigger] k_tracks_request(before, id) by {
        if k_tracks_request(after, id) {
            let witness = choose|witness: int|
                0 <= witness < after.requests@.len()
                    && #[trigger] after.requests@[witness].request as nat == id;
            assert(before.requests@[witness].request as nat == id);
        }
    }
    assert forall|id: nat| k_tracks_request(before, id)
        implies #[trigger] k_tracks_request(after, id) by {
        if k_tracks_request(before, id) {
            let witness = choose|witness: int|
                0 <= witness < before.requests@.len()
                    && #[trigger] before.requests@[witness].request as nat == id;
            assert(after.requests@[witness].request as nat == id);
        }
    }
}

pub proof fn k_caps_same_except_preserves_keys(
    before: KDurable,
    after: KDurable,
    index: int,
)
    requires
        k_caps_same_except(before, after, index),
        after.caps@[index].capability == before.caps@[index].capability,
    ensures
        forall|other: int| 0 <= other < before.caps@.len() ==>
            #[trigger] after.caps@[other].capability
                == before.caps@[other].capability,
        forall|id: nat| #[trigger] k_tracks_capability(after, id)
            <==> k_tracks_capability(before, id),
{
    assert forall|other: int| 0 <= other < before.caps@.len() implies
        #[trigger] after.caps@[other].capability
            == before.caps@[other].capability by {
        if other != index {
            assert(after.caps@[other] == before.caps@[other]);
        }
    }
    assert forall|id: nat| k_tracks_capability(after, id)
        implies #[trigger] k_tracks_capability(before, id) by {
        if k_tracks_capability(after, id) {
            let witness = choose|witness: int|
                0 <= witness < after.caps@.len()
                    && #[trigger] after.caps@[witness].capability as nat == id;
            assert(before.caps@[witness].capability as nat == id);
        }
    }
    assert forall|id: nat| k_tracks_capability(before, id)
        implies #[trigger] k_tracks_capability(after, id) by {
        if k_tracks_capability(before, id) {
            let witness = choose|witness: int|
                0 <= witness < before.caps@.len()
                    && #[trigger] before.caps@[witness].capability as nat == id;
            assert(after.caps@[witness].capability as nat == id);
        }
    }
}

pub fn k_set_request_phase(
    kd: &mut KDurable,
    index: usize,
    phase: KPhase,
)
    requires
        index < old(kd).requests@.len(),
    ensures
        k_phase_delta(*old(kd), *final(kd), index as int, phase),
{
    kd.requests[index].phase = phase;
}

pub open spec fn k_durable_with_phase(
    durable: replay_layer::DurableBroker,
    request: replay_layer::RequestId,
    phase: replay_layer::Phase,
) -> replay_layer::DurableBroker {
    replay_layer::DurableBroker {
        phase: durable.phase.insert(request, phase),
        ..durable
    }
}

pub proof fn k_phase_delta_preserves_update_inv(
    before: KDurable,
    after: KDurable,
    cfg: replay_layer::Config,
    durable: replay_layer::DurableBroker,
    index: int,
    phase: KPhase,
)
    requires
        k_update_inv(before, cfg, durable),
        k_phase_delta(before, after, index, phase),
    ensures
        k_update_inv(
            after,
            cfg,
            k_durable_with_phase(
                durable,
                k_request_id(before.requests@[index].request),
                k_phase_view(phase),
            ),
        ),
{
    let target = before.requests@[index];
    let request = k_request_id(target.request);
    let next = k_durable_with_phase(durable, request, k_phase_view(phase));
    k_requests_same_except_preserves_keys(before, after, index);

    assert forall|left: int, right: int|
        0 <= left < after.requests@.len()
            && 0 <= right < after.requests@.len()
            && #[trigger] after.requests@[left].request
                == #[trigger] after.requests@[right].request
        implies left == right by {
        assert(after.requests@[left].request == before.requests@[left].request);
        assert(after.requests@[right].request == before.requests@[right].request);
    }

    assert forall|other: int| 0 <= other < after.requests@.len() implies {
        let entry = #[trigger] after.requests@[other];
        &&& k_request_entry_couples(entry, next)
        &&& entry.outcomes@.len()
            <= cfg.max_attempts[k_request_id(entry.request)]
    } by {
        let entry = after.requests@[other];
        let old_entry = before.requests@[other];
        assert(k_request_entry_couples(old_entry, durable));
        assert(old_entry.outcomes@.len()
            <= cfg.max_attempts[k_request_id(old_entry.request)]);
        if other == index {
            assert(entry.request == target.request);
            assert(entry.phase == phase);
            assert(entry.witness == target.witness);
            assert(entry.outcomes@ == target.outcomes@);
            assert(next.phase[request] == k_phase_view(phase));
            assert(next.witness[request] == durable.witness[request]);
            assert(next.attempt_log == durable.attempt_log);
            assert(query_layer::d_started(next, request)
                == query_layer::d_started(durable, request));
            assert forall|attempt: replay_layer::AttemptId|
                1 <= attempt && attempt <= entry.outcomes@.len() implies
                    #[trigger] query_layer::d_outcome(next, request, attempt)
                        == k_outcome_view(entry.outcomes@[attempt - 1]) by {
                assert(query_layer::d_outcome(next, request, attempt)
                    == query_layer::d_outcome(durable, request, attempt));
                assert(query_layer::d_outcome(durable, request, attempt)
                    == k_outcome_view(target.outcomes@[attempt - 1]));
            }
            assert(k_request_entry_couples(entry, next));
            assert(entry.outcomes@.len()
                <= cfg.max_attempts[k_request_id(entry.request)]);
        } else {
            assert(entry == old_entry);
            if old_entry.request == target.request {
                assert(other == index);
            }
            assert(k_request_id(old_entry.request) != request);
            assert(next.phase[k_request_id(old_entry.request)]
                == durable.phase[k_request_id(old_entry.request)]);
            assert(next.witness == durable.witness);
            assert(next.attempt_log == durable.attempt_log);
            assert(query_layer::d_started(
                next, k_request_id(entry.request),
            ) == query_layer::d_started(
                durable, k_request_id(entry.request),
            ));
            assert forall|attempt: replay_layer::AttemptId|
                1 <= attempt && attempt <= entry.outcomes@.len() implies
                    #[trigger] query_layer::d_outcome(
                        next, k_request_id(entry.request), attempt,
                    ) == k_outcome_view(entry.outcomes@[attempt - 1]) by {
                assert(query_layer::d_outcome(
                    next, k_request_id(entry.request), attempt,
                ) == query_layer::d_outcome(
                    durable, k_request_id(entry.request), attempt,
                ));
            }
            assert(k_request_entry_couples(entry, next));
            assert(entry.outcomes@.len()
                <= cfg.max_attempts[k_request_id(entry.request)]);
        }
    }

    assert forall|id: nat| !k_tracks_request(after, id) implies {
        &&& #[trigger] next.phase[replay_layer::RequestId { id }]
            == replay_layer::Phase::New
        &&& next.witness[replay_layer::RequestId { id }]
            == Option::<replay_layer::CapabilityId>::None
        &&& query_layer::d_started(
            next, replay_layer::RequestId { id },
        ) == 0
    } by {
        let candidate = replay_layer::RequestId { id };
        assert(!k_tracks_request(before, id));
        assert(durable.phase[candidate] == replay_layer::Phase::New);
        assert(durable.witness[candidate]
            == Option::<replay_layer::CapabilityId>::None);
        assert(query_layer::d_started(durable, candidate) == 0);
        assert(k_tracks_request(before, target.request as nat));
        assert(id != target.request as nat);
        assert(candidate != request);
        assert(next.phase[candidate] == durable.phase[candidate]);
        assert(next.witness == durable.witness);
        assert(next.attempt_log == durable.attempt_log);
    }

    assert(after.caps@ == before.caps@);
    assert forall|left: int, right: int|
        0 <= left < after.caps@.len()
            && 0 <= right < after.caps@.len()
            && #[trigger] after.caps@[left].capability
                == #[trigger] after.caps@[right].capability
        implies left == right by {
    }
    assert forall|other: int| 0 <= other < after.caps@.len() implies {
        let entry = #[trigger] after.caps@[other];
        &&& next.remaining[k_capability_id(entry.capability)]
            == entry.remaining as nat
        &&& next.revoked.contains(k_capability_id(entry.capability))
            == entry.revoked
    } by {
    }
    assert forall|id: nat| !k_tracks_capability(after, id) implies {
        &&& #[trigger] next.remaining[replay_layer::CapabilityId { id }]
            == cfg.initial_budget[replay_layer::CapabilityId { id }]
        &&& !next.revoked.contains(replay_layer::CapabilityId { id })
    } by {
    }
    assert(k_durable_inv(after, cfg, next));

    assert forall|candidate: replay_layer::RequestId,
                  attempt: replay_layer::AttemptId|
        attempt > query_layer::d_started(next, candidate) implies
            #[trigger] query_layer::d_outcome(next, candidate, attempt).is_none() by {
        assert(next.attempt_log == durable.attempt_log);
        assert(query_layer::d_started(next, candidate)
            == query_layer::d_started(durable, candidate));
        assert(query_layer::d_outcome(next, candidate, attempt)
            == query_layer::d_outcome(durable, candidate, attempt));
    }
}

pub open spec fn k_phase_record_shape(
    record: replay_layer::JournalRecord,
    request: replay_layer::RequestId,
    phase: replay_layer::Phase,
) -> bool {
    match record {
        replay_layer::JournalRecord::Prepare { request: target, .. } =>
            target == request && phase == replay_layer::Phase::Prepared,
        replay_layer::JournalRecord::Arm { request: target, .. } =>
            target == request && phase == replay_layer::Phase::Armed,
        replay_layer::JournalRecord::CommitRec { request: target, .. } =>
            target == request && phase == replay_layer::Phase::Committed,
        replay_layer::JournalRecord::FailRec { request: target, .. } =>
            target == request && phase == replay_layer::Phase::Failed,
        replay_layer::JournalRecord::UnknownRec { request: target, .. } =>
            target == request && phase == replay_layer::Phase::Unknown,
        _ => false,
    }
}

pub proof fn k_phase_record_delta_refines_apply_record(
    before: KDurable,
    after: KDurable,
    cfg: replay_layer::Config,
    durable: replay_layer::DurableBroker,
    index: int,
    phase: KPhase,
    record: replay_layer::JournalRecord,
)
    requires
        k_update_inv(before, cfg, durable),
        k_phase_delta(before, after, index, phase),
        k_phase_record_shape(
            record,
            k_request_id(before.requests@[index].request),
            k_phase_view(phase),
        ),
    ensures
        k_update_inv(
            after,
            cfg,
            replay_layer::apply_record(durable, record),
        ),
{
    let request = k_request_id(before.requests@[index].request);
    let phase_durable = k_durable_with_phase(
        durable,
        request,
        k_phase_view(phase),
    );
    k_phase_delta_preserves_update_inv(
        before, after, cfg, durable, index, phase,
    );
    assert(k_observed_durable_eq(
        phase_durable,
        replay_layer::apply_record(durable, record),
    )) by {
        match record {
            replay_layer::JournalRecord::Prepare { .. }
            | replay_layer::JournalRecord::Arm { .. }
            | replay_layer::JournalRecord::CommitRec { .. }
            | replay_layer::JournalRecord::FailRec { .. }
            | replay_layer::JournalRecord::UnknownRec { .. } => {},
            _ => assert(false),
        }
    }
    k_update_inv_observed_transport(
        after,
        cfg,
        phase_durable,
        replay_layer::apply_record(durable, record),
    );
}

pub open spec fn k_authorize_delta(
    before: KDurable,
    after: KDurable,
    request_index: int,
    cap_index: int,
    capability: u64,
) -> bool {
    &&& k_requests_same_except(before, after, request_index)
    &&& k_caps_same_except(before, after, cap_index)
    &&& before.caps@[cap_index].remaining > 0
    &&& after.requests@[request_index].request
        == before.requests@[request_index].request
    &&& after.requests@[request_index].phase == KPhase::Authorized
    &&& after.requests@[request_index].witness == Option::Some(capability)
    &&& after.requests@[request_index].outcomes@
        == before.requests@[request_index].outcomes@
    &&& after.caps@[cap_index].capability
        == before.caps@[cap_index].capability
    &&& after.caps@[cap_index].remaining as nat + 1
        == before.caps@[cap_index].remaining as nat
    &&& after.caps@[cap_index].revoked == before.caps@[cap_index].revoked
}

pub fn k_set_authorized(
    kd: &mut KDurable,
    request_index: usize,
    cap_index: usize,
    capability: u64,
)
    requires
        request_index < old(kd).requests@.len(),
        cap_index < old(kd).caps@.len(),
        old(kd).caps@[cap_index as int].remaining > 0,
    ensures
        k_authorize_delta(
            *old(kd),
            *final(kd),
            request_index as int,
            cap_index as int,
            capability,
        ),
{
    kd.requests[request_index].phase = KPhase::Authorized;
    kd.requests[request_index].witness = Option::Some(capability);
    let remaining = kd.caps[cap_index].remaining;
    kd.caps[cap_index].remaining = remaining - 1;
}

pub proof fn k_authorize_delta_refines_apply_record(
    before: KDurable,
    after: KDurable,
    cfg: replay_layer::Config,
    durable: replay_layer::DurableBroker,
    request_index: int,
    cap_index: int,
    request: u64,
    capability: u64,
    digest: u64,
)
    requires
        k_update_inv(before, cfg, durable),
        k_authorize_delta(
            before, after, request_index, cap_index, capability,
        ),
        before.requests@[request_index].request == request,
        before.caps@[cap_index].capability == capability,
    ensures
        k_update_inv(
            after,
            cfg,
            replay_layer::apply_record(
                durable,
                replay_layer::JournalRecord::Authorize {
                    request: k_request_id(request),
                    capability: k_capability_id(capability),
                    digest: k_digest_id(digest),
                },
            ),
        ),
{
    let request_id = k_request_id(request);
    let capability_id = k_capability_id(capability);
    // Keep the ghost-only authorization provenance unchanged while coupling
    // the executable projections, then transport to the real apply_record.
    let observed = replay_layer::DurableBroker {
        phase: durable.phase.insert(
            request_id, replay_layer::Phase::Authorized,
        ),
        remaining: durable.remaining.insert(
            capability_id,
            replay_layer::pred0(durable.remaining[capability_id]),
        ),
        witness: durable.witness.insert(
            request_id, Option::Some(capability_id),
        ),
        ..durable
    };

    k_requests_same_except_preserves_keys(before, after, request_index);
    k_caps_same_except_preserves_keys(before, after, cap_index);

    assert forall|left: int, right: int|
        0 <= left < after.requests@.len()
            && 0 <= right < after.requests@.len()
            && #[trigger] after.requests@[left].request
                == #[trigger] after.requests@[right].request
        implies left == right by {
        assert(after.requests@[left].request
            == before.requests@[left].request);
        assert(after.requests@[right].request
            == before.requests@[right].request);
    }

    assert forall|other: int| 0 <= other < after.requests@.len() implies {
        let entry = #[trigger] after.requests@[other];
        &&& k_request_entry_couples(entry, observed)
        &&& entry.outcomes@.len()
            <= cfg.max_attempts[k_request_id(entry.request)]
    } by {
        let entry = after.requests@[other];
        let old_entry = before.requests@[other];
        assert(k_request_entry_couples(old_entry, durable));
        assert(old_entry.outcomes@.len()
            <= cfg.max_attempts[k_request_id(old_entry.request)]);
        if other == request_index {
            assert(entry.request == request);
            assert(entry.phase == KPhase::Authorized);
            assert(entry.witness == Option::Some(capability));
            assert(entry.outcomes@ == old_entry.outcomes@);
            assert(observed.phase[request_id]
                == replay_layer::Phase::Authorized);
            assert(observed.witness[request_id]
                == Option::Some(capability_id));
            assert(observed.attempt_log == durable.attempt_log);
            assert(query_layer::d_started(observed, request_id)
                == query_layer::d_started(durable, request_id));
            assert forall|attempt: replay_layer::AttemptId|
                1 <= attempt && attempt <= entry.outcomes@.len() implies
                    #[trigger] query_layer::d_outcome(
                        observed, request_id, attempt,
                    ) == k_outcome_view(entry.outcomes@[attempt - 1]) by {
                assert(query_layer::d_outcome(
                    observed, request_id, attempt,
                ) == query_layer::d_outcome(
                    durable, request_id, attempt,
                ));
            }
            assert(k_request_entry_couples(entry, observed));
        } else {
            assert(entry == old_entry);
            if old_entry.request == request {
                assert(old_entry.request
                    == before.requests@[request_index].request);
                assert(other == request_index);
            }
            let other_request = k_request_id(old_entry.request);
            assert(other_request != request_id);
            assert(observed.phase[other_request]
                == durable.phase[other_request]);
            assert(observed.witness[other_request]
                == durable.witness[other_request]);
            assert(observed.attempt_log == durable.attempt_log);
            assert(query_layer::d_started(observed, other_request)
                == query_layer::d_started(durable, other_request));
            assert forall|attempt: replay_layer::AttemptId|
                1 <= attempt && attempt <= entry.outcomes@.len() implies
                    #[trigger] query_layer::d_outcome(
                        observed, other_request, attempt,
                    ) == k_outcome_view(entry.outcomes@[attempt - 1]) by {
                assert(query_layer::d_outcome(
                    observed, other_request, attempt,
                ) == query_layer::d_outcome(
                    durable, other_request, attempt,
                ));
            }
            assert(k_request_entry_couples(entry, observed));
        }
    }

    assert forall|id: nat| !k_tracks_request(after, id) implies {
        &&& #[trigger] observed.phase[replay_layer::RequestId { id }]
            == replay_layer::Phase::New
        &&& observed.witness[replay_layer::RequestId { id }]
            == Option::<replay_layer::CapabilityId>::None
        &&& query_layer::d_started(
            observed, replay_layer::RequestId { id },
        ) == 0
    } by {
        let candidate = replay_layer::RequestId { id };
        assert(!k_tracks_request(before, id));
        assert(k_tracks_request(before, request as nat));
        assert(id != request as nat);
        assert(candidate != request_id);
        assert(observed.phase[candidate] == durable.phase[candidate]);
        assert(observed.witness[candidate] == durable.witness[candidate]);
        assert(observed.attempt_log == durable.attempt_log);
    }

    assert forall|left: int, right: int|
        0 <= left < after.caps@.len()
            && 0 <= right < after.caps@.len()
            && #[trigger] after.caps@[left].capability
                == #[trigger] after.caps@[right].capability
        implies left == right by {
        assert(after.caps@[left].capability
            == before.caps@[left].capability);
        assert(after.caps@[right].capability
            == before.caps@[right].capability);
    }

    assert forall|other: int| 0 <= other < after.caps@.len() implies {
        let entry = #[trigger] after.caps@[other];
        &&& observed.remaining[k_capability_id(entry.capability)]
            == entry.remaining as nat
        &&& observed.revoked.contains(k_capability_id(entry.capability))
            == entry.revoked
    } by {
        let entry = after.caps@[other];
        let old_entry = before.caps@[other];
        assert(durable.remaining[k_capability_id(old_entry.capability)]
            == old_entry.remaining as nat);
        assert(durable.revoked.contains(k_capability_id(old_entry.capability))
            == old_entry.revoked);
        if other == cap_index {
            assert(entry.capability == capability);
            assert(entry.remaining as nat + 1 == old_entry.remaining as nat);
            assert(old_entry.remaining > 0);
            assert(durable.remaining[capability_id] > 0);
            assert(replay_layer::pred0(durable.remaining[capability_id])
                == durable.remaining[capability_id] - 1);
            assert(entry.remaining as nat
                == replay_layer::pred0(durable.remaining[capability_id]));
            assert(entry.revoked == old_entry.revoked);
            assert(observed.remaining[capability_id]
                == replay_layer::pred0(durable.remaining[capability_id]));
            assert(observed.revoked == durable.revoked);
        } else {
            assert(entry == old_entry);
            if old_entry.capability == capability {
                assert(old_entry.capability
                    == before.caps@[cap_index].capability);
                assert(other == cap_index);
            }
            let other_capability = k_capability_id(old_entry.capability);
            assert(other_capability != capability_id);
            assert(observed.remaining[other_capability]
                == durable.remaining[other_capability]);
            assert(observed.revoked == durable.revoked);
        }
    }

    assert forall|id: nat| !k_tracks_capability(after, id) implies {
        &&& #[trigger] observed.remaining[replay_layer::CapabilityId { id }]
            == cfg.initial_budget[replay_layer::CapabilityId { id }]
        &&& !observed.revoked.contains(replay_layer::CapabilityId { id })
    } by {
        let candidate = replay_layer::CapabilityId { id };
        assert(!k_tracks_capability(before, id));
        assert(k_tracks_capability(before, capability as nat));
        assert(id != capability as nat);
        assert(candidate != capability_id);
        assert(observed.remaining[candidate] == durable.remaining[candidate]);
        assert(observed.revoked == durable.revoked);
    }

    assert(k_durable_inv(after, cfg, observed));
    assert forall|candidate: replay_layer::RequestId,
                  attempt: replay_layer::AttemptId|
        attempt > query_layer::d_started(observed, candidate) implies
            #[trigger] query_layer::d_outcome(
                observed, candidate, attempt,
            ).is_none() by {
        assert(observed.attempt_log == durable.attempt_log);
        assert(query_layer::d_started(observed, candidate)
            == query_layer::d_started(durable, candidate));
        assert(query_layer::d_outcome(observed, candidate, attempt)
            == query_layer::d_outcome(durable, candidate, attempt));
    }
    assert(k_update_inv(after, cfg, observed));

    let record = replay_layer::JournalRecord::Authorize {
        request: request_id,
        capability: capability_id,
        digest: k_digest_id(digest),
    };
    let applied = replay_layer::apply_record(durable, record);
    assert(k_observed_durable_eq(observed, applied)) by {
        assert(observed.phase == applied.phase);
        assert(observed.remaining == applied.remaining);
        assert(observed.revoked == applied.revoked);
        assert(observed.witness == applied.witness);
        assert(observed.attempt_log == applied.attempt_log);
    }
    k_update_inv_observed_transport(after, cfg, observed, applied);
}

pub open spec fn k_revoke_delta(
    before: KDurable,
    after: KDurable,
    cap_index: int,
) -> bool {
    &&& k_caps_same_except(before, after, cap_index)
    &&& after.requests@ == before.requests@
    &&& after.caps@[cap_index].capability
        == before.caps@[cap_index].capability
    &&& after.caps@[cap_index].remaining == before.caps@[cap_index].remaining
    &&& after.caps@[cap_index].revoked
}

pub fn k_set_revoked(kd: &mut KDurable, cap_index: usize)
    requires
        cap_index < old(kd).caps@.len(),
    ensures
        k_revoke_delta(*old(kd), *final(kd), cap_index as int),
{
    kd.caps[cap_index].revoked = true;
}

pub proof fn k_revoke_delta_refines_apply_record(
    before: KDurable,
    after: KDurable,
    cfg: replay_layer::Config,
    durable: replay_layer::DurableBroker,
    cap_index: int,
    capability: u64,
)
    requires
        k_update_inv(before, cfg, durable),
        k_revoke_delta(before, after, cap_index),
        before.caps@[cap_index].capability == capability,
    ensures
        k_update_inv(
            after,
            cfg,
            replay_layer::apply_record(
                durable,
                replay_layer::JournalRecord::Revoke {
                    capability: k_capability_id(capability),
                },
            ),
        ),
{
    let capability_id = k_capability_id(capability);
    let record = replay_layer::JournalRecord::Revoke {
        capability: capability_id,
    };
    let next = replay_layer::apply_record(durable, record);

    k_caps_same_except_preserves_keys(before, after, cap_index);

    assert(after.requests@ == before.requests@);
    assert forall|left: int, right: int|
        0 <= left < after.requests@.len()
            && 0 <= right < after.requests@.len()
            && #[trigger] after.requests@[left].request
                == #[trigger] after.requests@[right].request
        implies left == right by {
    }
    assert forall|other: int| 0 <= other < after.requests@.len() implies {
        let entry = #[trigger] after.requests@[other];
        &&& k_request_entry_couples(entry, next)
        &&& entry.outcomes@.len()
            <= cfg.max_attempts[k_request_id(entry.request)]
    } by {
        let entry = after.requests@[other];
        assert(entry == before.requests@[other]);
        assert(next.phase == durable.phase);
        assert(next.witness == durable.witness);
        assert(next.attempt_log == durable.attempt_log);
        assert(query_layer::d_started(
            next, k_request_id(entry.request),
        ) == query_layer::d_started(
            durable, k_request_id(entry.request),
        ));
        assert forall|attempt: replay_layer::AttemptId|
            1 <= attempt && attempt <= entry.outcomes@.len() implies
                #[trigger] query_layer::d_outcome(
                    next, k_request_id(entry.request), attempt,
                ) == k_outcome_view(entry.outcomes@[attempt - 1]) by {
            assert(query_layer::d_outcome(
                next, k_request_id(entry.request), attempt,
            ) == query_layer::d_outcome(
                durable, k_request_id(entry.request), attempt,
            ));
        }
        assert(k_request_entry_couples(entry, next));
    }
    assert forall|id: nat| !k_tracks_request(after, id) implies {
        &&& #[trigger] next.phase[replay_layer::RequestId { id }]
            == replay_layer::Phase::New
        &&& next.witness[replay_layer::RequestId { id }]
            == Option::<replay_layer::CapabilityId>::None
        &&& query_layer::d_started(
            next, replay_layer::RequestId { id },
        ) == 0
    } by {
        assert(!k_tracks_request(before, id));
        assert(next.phase == durable.phase);
        assert(next.witness == durable.witness);
        assert(next.attempt_log == durable.attempt_log);
    }

    assert forall|left: int, right: int|
        0 <= left < after.caps@.len()
            && 0 <= right < after.caps@.len()
            && #[trigger] after.caps@[left].capability
                == #[trigger] after.caps@[right].capability
        implies left == right by {
        assert(after.caps@[left].capability
            == before.caps@[left].capability);
        assert(after.caps@[right].capability
            == before.caps@[right].capability);
    }
    assert forall|other: int| 0 <= other < after.caps@.len() implies {
        let entry = #[trigger] after.caps@[other];
        &&& next.remaining[k_capability_id(entry.capability)]
            == entry.remaining as nat
        &&& next.revoked.contains(k_capability_id(entry.capability))
            == entry.revoked
    } by {
        let entry = after.caps@[other];
        let old_entry = before.caps@[other];
        assert(durable.remaining[k_capability_id(old_entry.capability)]
            == old_entry.remaining as nat);
        assert(durable.revoked.contains(k_capability_id(old_entry.capability))
            == old_entry.revoked);
        assert(next.remaining == durable.remaining);
        if other == cap_index {
            assert(entry.capability == capability);
            assert(entry.remaining == old_entry.remaining);
            assert(entry.revoked);
            assert(next.revoked.contains(capability_id));
        } else {
            assert(entry == old_entry);
            if old_entry.capability == capability {
                assert(old_entry.capability
                    == before.caps@[cap_index].capability);
                assert(other == cap_index);
            }
            let other_capability = k_capability_id(old_entry.capability);
            assert(other_capability != capability_id);
            assert(next.revoked.contains(other_capability)
                == durable.revoked.contains(other_capability));
        }
    }
    assert forall|id: nat| !k_tracks_capability(after, id) implies {
        &&& #[trigger] next.remaining[replay_layer::CapabilityId { id }]
            == cfg.initial_budget[replay_layer::CapabilityId { id }]
        &&& !next.revoked.contains(replay_layer::CapabilityId { id })
    } by {
        let candidate = replay_layer::CapabilityId { id };
        assert(!k_tracks_capability(before, id));
        assert(k_tracks_capability(before, capability as nat));
        assert(id != capability as nat);
        assert(candidate != capability_id);
        assert(next.remaining == durable.remaining);
        assert(next.revoked.contains(candidate)
            == durable.revoked.contains(candidate));
    }

    assert(k_durable_inv(after, cfg, next));
    assert forall|candidate: replay_layer::RequestId,
                  attempt: replay_layer::AttemptId|
        attempt > query_layer::d_started(next, candidate) implies
            #[trigger] query_layer::d_outcome(
                next, candidate, attempt,
            ).is_none() by {
        assert(next.attempt_log == durable.attempt_log);
        assert(query_layer::d_started(next, candidate)
            == query_layer::d_started(durable, candidate));
        assert(query_layer::d_outcome(next, candidate, attempt)
            == query_layer::d_outcome(durable, candidate, attempt));
    }
}

pub open spec fn k_start_delta(
    before: KDurable,
    after: KDurable,
    request_index: int,
) -> bool {
    &&& k_requests_same_except(before, after, request_index)
    &&& after.requests@[request_index].request
        == before.requests@[request_index].request
    &&& after.requests@[request_index].phase
        == before.requests@[request_index].phase
    &&& after.requests@[request_index].witness
        == before.requests@[request_index].witness
    &&& after.requests@[request_index].outcomes@
        == before.requests@[request_index].outcomes@.push(Option::None)
    &&& after.caps@ == before.caps@
}

pub fn k_push_started(kd: &mut KDurable, request_index: usize)
    requires
        request_index < old(kd).requests@.len(),
    ensures
        k_start_delta(*old(kd), *final(kd), request_index as int),
{
    kd.requests[request_index].outcomes.push(Option::None);
}

pub open spec fn k_durable_with_started(
    durable: replay_layer::DurableBroker,
    request: replay_layer::RequestId,
    attempt: replay_layer::AttemptId,
) -> replay_layer::DurableBroker {
    replay_layer::DurableBroker {
        attempt_log: durable.attempt_log.push(replay_layer::AttemptEntry {
            request,
            attempt,
            knowledge: replay_layer::AttemptKnowledge::Started,
        }),
        ..durable
    }
}

pub proof fn k_start_delta_preserves_update_inv(
    before: KDurable,
    after: KDurable,
    cfg: replay_layer::Config,
    durable: replay_layer::DurableBroker,
    request_index: int,
    attempt: replay_layer::AttemptId,
)
    requires
        k_update_inv(before, cfg, durable),
        k_start_delta(before, after, request_index),
        attempt == query_layer::d_started(
            durable,
            k_request_id(before.requests@[request_index].request),
        ) + 1,
        attempt <= cfg.max_attempts[
            k_request_id(before.requests@[request_index].request)
        ],
    ensures
        k_update_inv(
            after,
            cfg,
            k_durable_with_started(
                durable,
                k_request_id(before.requests@[request_index].request),
                attempt,
            ),
        ),
{
    let target = before.requests@[request_index];
    let request = k_request_id(target.request);
    let appended = replay_layer::AttemptEntry {
        request,
        attempt,
        knowledge: replay_layer::AttemptKnowledge::Started,
    };
    let next = k_durable_with_started(durable, request, attempt);
    k_requests_same_except_preserves_keys(before, after, request_index);
    query_layer::attempt_log_started_push(
        durable.attempt_log, request, appended,
    );

    assert forall|left: int, right: int|
        0 <= left < after.requests@.len()
            && 0 <= right < after.requests@.len()
            && #[trigger] after.requests@[left].request
                == #[trigger] after.requests@[right].request
        implies left == right by {
        assert(after.requests@[left].request == before.requests@[left].request);
        assert(after.requests@[right].request == before.requests@[right].request);
    }

    assert forall|other: int| 0 <= other < after.requests@.len() implies {
        let entry = #[trigger] after.requests@[other];
        &&& k_request_entry_couples(entry, next)
        &&& entry.outcomes@.len()
            <= cfg.max_attempts[k_request_id(entry.request)]
    } by {
        let entry = after.requests@[other];
        let old_entry = before.requests@[other];
        let old_request = k_request_id(old_entry.request);
        assert(k_request_entry_couples(old_entry, durable));
        assert(old_entry.outcomes@.len()
            <= cfg.max_attempts[old_request]);
        if other == request_index {
            assert(old_entry == target);
            assert(entry.request == target.request);
            assert(entry.phase == target.phase);
            assert(entry.witness == target.witness);
            assert(entry.outcomes@ == target.outcomes@.push(Option::None));
            assert(query_layer::d_started(durable, request)
                == target.outcomes@.len());
            assert(query_layer::d_started(next, request)
                == query_layer::d_started(durable, request) + 1);
            assert(entry.outcomes@.len() == target.outcomes@.len() + 1);
            assert(attempt == entry.outcomes@.len());
            assert forall|candidate: replay_layer::AttemptId|
                1 <= candidate && candidate <= entry.outcomes@.len() implies
                    #[trigger] query_layer::d_outcome(
                        next, request, candidate,
                    ) == k_outcome_view(entry.outcomes@[candidate - 1]) by {
                query_layer::attempt_log_outcome_push(
                    durable.attempt_log,
                    request,
                    candidate,
                    appended,
                );
                assert(query_layer::d_outcome(next, request, candidate)
                    == query_layer::d_outcome(
                        durable, request, candidate,
                    ));
                if candidate <= target.outcomes@.len() {
                    assert(entry.outcomes@[candidate - 1]
                        == target.outcomes@[candidate - 1]);
                    assert(query_layer::d_outcome(
                        durable, request, candidate,
                    ) == k_outcome_view(target.outcomes@[candidate - 1]));
                } else {
                    assert(candidate == target.outcomes@.len() + 1);
                    assert(candidate > query_layer::d_started(durable, request));
                    assert(query_layer::d_outcome(
                        durable, request, candidate,
                    ).is_none());
                    assert(candidate - 1 == target.outcomes@.len());
                    assert(entry.outcomes@[candidate - 1] == Option::None);
                }
            }
            assert(k_request_entry_couples(entry, next));
            assert(entry.outcomes@.len()
                <= cfg.max_attempts[k_request_id(entry.request)]);
        } else {
            assert(entry == old_entry);
            if old_entry.request == target.request {
                assert(other == request_index);
            }
            assert(old_request != request);
            query_layer::attempt_log_started_push(
                durable.attempt_log, old_request, appended,
            );
            assert(query_layer::d_started(next, old_request)
                == query_layer::d_started(durable, old_request));
            assert forall|candidate: replay_layer::AttemptId|
                1 <= candidate && candidate <= entry.outcomes@.len() implies
                    #[trigger] query_layer::d_outcome(
                        next, old_request, candidate,
                    ) == k_outcome_view(entry.outcomes@[candidate - 1]) by {
                query_layer::attempt_log_outcome_push(
                    durable.attempt_log,
                    old_request,
                    candidate,
                    appended,
                );
                assert(query_layer::d_outcome(
                    next, old_request, candidate,
                ) == query_layer::d_outcome(
                    durable, old_request, candidate,
                ));
            }
            assert(k_request_entry_couples(entry, next));
        }
    }

    assert forall|id: nat| !k_tracks_request(after, id) implies {
        &&& #[trigger] next.phase[replay_layer::RequestId { id }]
            == replay_layer::Phase::New
        &&& next.witness[replay_layer::RequestId { id }]
            == Option::<replay_layer::CapabilityId>::None
        &&& query_layer::d_started(
            next, replay_layer::RequestId { id },
        ) == 0
    } by {
        let candidate = replay_layer::RequestId { id };
        assert(!k_tracks_request(before, id));
        assert(k_tracks_request(before, target.request as nat));
        assert(id != target.request as nat);
        assert(candidate != request);
        query_layer::attempt_log_started_push(
            durable.attempt_log, candidate, appended,
        );
        assert(next.phase[candidate] == durable.phase[candidate]);
        assert(next.witness[candidate] == durable.witness[candidate]);
        assert(query_layer::d_started(next, candidate)
            == query_layer::d_started(durable, candidate));
    }

    assert(after.caps@ == before.caps@);
    assert forall|left: int, right: int|
        0 <= left < after.caps@.len()
            && 0 <= right < after.caps@.len()
            && #[trigger] after.caps@[left].capability
                == #[trigger] after.caps@[right].capability
        implies left == right by {
    }
    assert forall|other: int| 0 <= other < after.caps@.len() implies {
        let entry = #[trigger] after.caps@[other];
        &&& next.remaining[k_capability_id(entry.capability)]
            == entry.remaining as nat
        &&& next.revoked.contains(k_capability_id(entry.capability))
            == entry.revoked
    } by {
    }
    assert forall|id: nat| !k_tracks_capability(after, id) implies {
        &&& #[trigger] next.remaining[replay_layer::CapabilityId { id }]
            == cfg.initial_budget[replay_layer::CapabilityId { id }]
        &&& !next.revoked.contains(replay_layer::CapabilityId { id })
    } by {
    }
    assert(k_durable_inv(after, cfg, next));

    assert forall|candidate: replay_layer::RequestId,
                  future: replay_layer::AttemptId|
        future > query_layer::d_started(next, candidate) implies
            #[trigger] query_layer::d_outcome(
                next, candidate, future,
            ).is_none() by {
        query_layer::attempt_log_started_push(
            durable.attempt_log, candidate, appended,
        );
        query_layer::attempt_log_outcome_push(
            durable.attempt_log, candidate, future, appended,
        );
        assert(query_layer::d_outcome(next, candidate, future)
            == query_layer::d_outcome(durable, candidate, future));
        if candidate == request {
            assert(query_layer::d_started(next, candidate)
                == query_layer::d_started(durable, candidate) + 1);
        } else {
            assert(query_layer::d_started(next, candidate)
                == query_layer::d_started(durable, candidate));
        }
        assert(future > query_layer::d_started(durable, candidate));
    }
}

pub open spec fn k_start_record_for(
    record: replay_layer::JournalRecord,
    request: replay_layer::RequestId,
) -> bool {
    match record {
        replay_layer::JournalRecord::Start { request: target, .. } =>
            target == request,
        _ => false,
    }
}

pub proof fn k_start_delta_refines_apply_record(
    before: KDurable,
    after: KDurable,
    cfg: replay_layer::Config,
    durable: replay_layer::DurableBroker,
    request_index: int,
    record: replay_layer::JournalRecord,
)
    requires
        k_update_inv(before, cfg, durable),
        k_start_delta(before, after, request_index),
        k_start_record_for(
            record,
            k_request_id(before.requests@[request_index].request),
        ),
        query_layer::abstract_record_enabled(cfg, durable, record),
    ensures
        k_update_inv(
            after,
            cfg,
            replay_layer::apply_record(durable, record),
        ),
{
    let request = k_request_id(before.requests@[request_index].request);
    match record {
        replay_layer::JournalRecord::Start {
            request: target,
            attempt,
            ..
        } => {
            assert(target == request);
            assert(attempt == query_layer::d_started(durable, request) + 1);
            assert(attempt <= cfg.max_attempts[request]);
            k_start_delta_preserves_update_inv(
                before,
                after,
                cfg,
                durable,
                request_index,
                attempt,
            );
            assert(k_observed_durable_eq(
                k_durable_with_started(durable, request, attempt),
                replay_layer::apply_record(durable, record),
            ));
            k_update_inv_observed_transport(
                after,
                cfg,
                k_durable_with_started(durable, request, attempt),
                replay_layer::apply_record(durable, record),
            );
        },
        _ => assert(false),
    }
}

pub open spec fn k_outcome_delta(
    before: KDurable,
    after: KDurable,
    request_index: int,
    observation: KObservation,
) -> bool {
    &&& k_requests_same_except(before, after, request_index)
    &&& before.requests@[request_index].outcomes@.len() > 0
    &&& after.requests@[request_index].request
        == before.requests@[request_index].request
    &&& after.requests@[request_index].phase
        == before.requests@[request_index].phase
    &&& after.requests@[request_index].witness
        == before.requests@[request_index].witness
    &&& after.requests@[request_index].outcomes@
        == before.requests@[request_index].outcomes@.update(
            before.requests@[request_index].outcomes@.len() - 1,
            Option::Some(observation),
        )
    &&& after.caps@ == before.caps@
}

pub fn k_set_latest_outcome(
    kd: &mut KDurable,
    request_index: usize,
    observation: KObservation,
)
    requires
        request_index < old(kd).requests@.len(),
        old(kd).requests@[request_index as int].outcomes@.len() > 0,
    ensures
        k_outcome_delta(
            *old(kd),
            *final(kd),
            request_index as int,
            observation,
        ),
{
    let latest = kd.requests[request_index].outcomes.len() - 1;
    kd.requests[request_index].outcomes.set(
        latest,
        Option::Some(observation),
    );
}

pub open spec fn k_durable_with_outcome(
    durable: replay_layer::DurableBroker,
    request: replay_layer::RequestId,
    attempt: replay_layer::AttemptId,
    observation: KObservation,
) -> replay_layer::DurableBroker {
    replay_layer::DurableBroker {
        attempt_log: durable.attempt_log.push(replay_layer::AttemptEntry {
            request,
            attempt,
            knowledge: replay_layer::AttemptKnowledge::Recorded(
                k_observation_view(observation),
            ),
        }),
        ..durable
    }
}

pub proof fn k_outcome_delta_preserves_update_inv(
    before: KDurable,
    after: KDurable,
    cfg: replay_layer::Config,
    durable: replay_layer::DurableBroker,
    request_index: int,
    attempt: replay_layer::AttemptId,
    observation: KObservation,
)
    requires
        k_update_inv(before, cfg, durable),
        k_outcome_delta(
            before, after, request_index, observation,
        ),
        attempt > 0,
        attempt == query_layer::d_started(
            durable,
            k_request_id(before.requests@[request_index].request),
        ),
    ensures
        k_update_inv(
            after,
            cfg,
            k_durable_with_outcome(
                durable,
                k_request_id(before.requests@[request_index].request),
                attempt,
                observation,
            ),
        ),
{
    let target = before.requests@[request_index];
    let request = k_request_id(target.request);
    let appended = replay_layer::AttemptEntry {
        request,
        attempt,
        knowledge: replay_layer::AttemptKnowledge::Recorded(
            k_observation_view(observation),
        ),
    };
    let next = k_durable_with_outcome(
        durable, request, attempt, observation,
    );
    k_requests_same_except_preserves_keys(before, after, request_index);

    assert forall|left: int, right: int|
        0 <= left < after.requests@.len()
            && 0 <= right < after.requests@.len()
            && #[trigger] after.requests@[left].request
                == #[trigger] after.requests@[right].request
        implies left == right by {
        assert(after.requests@[left].request == before.requests@[left].request);
        assert(after.requests@[right].request == before.requests@[right].request);
    }

    assert forall|other: int| 0 <= other < after.requests@.len() implies {
        let entry = #[trigger] after.requests@[other];
        &&& k_request_entry_couples(entry, next)
        &&& entry.outcomes@.len()
            <= cfg.max_attempts[k_request_id(entry.request)]
    } by {
        let entry = after.requests@[other];
        let old_entry = before.requests@[other];
        let old_request = k_request_id(old_entry.request);
        assert(k_request_entry_couples(old_entry, durable));
        assert(old_entry.outcomes@.len()
            <= cfg.max_attempts[old_request]);
        query_layer::attempt_log_started_push(
            durable.attempt_log, old_request, appended,
        );
        assert(query_layer::d_started(next, old_request)
            == query_layer::d_started(durable, old_request));
        if other == request_index {
            assert(old_entry == target);
            assert(entry.request == target.request);
            assert(entry.phase == target.phase);
            assert(entry.witness == target.witness);
            assert(entry.outcomes@ == target.outcomes@.update(
                target.outcomes@.len() - 1,
                Option::Some(observation),
            ));
            assert(target.outcomes@.len()
                == query_layer::d_started(durable, request));
            assert(attempt == target.outcomes@.len());
            assert(entry.outcomes@.len() == target.outcomes@.len());
            assert forall|candidate: replay_layer::AttemptId|
                1 <= candidate && candidate <= entry.outcomes@.len() implies
                    #[trigger] query_layer::d_outcome(
                        next, request, candidate,
                    ) == k_outcome_view(entry.outcomes@[candidate - 1]) by {
                query_layer::attempt_log_outcome_push(
                    durable.attempt_log,
                    request,
                    candidate,
                    appended,
                );
                if candidate == attempt {
                    assert(query_layer::d_outcome(
                        next, request, candidate,
                    ) == Option::Some(k_observation_view(observation)));
                    assert(candidate - 1 == target.outcomes@.len() - 1);
                    assert(entry.outcomes@[candidate - 1]
                        == Option::Some(observation));
                } else {
                    assert(query_layer::d_outcome(
                        next, request, candidate,
                    ) == query_layer::d_outcome(
                        durable, request, candidate,
                    ));
                    assert(entry.outcomes@[candidate - 1]
                        == target.outcomes@[candidate - 1]);
                }
            }
            assert(k_request_entry_couples(entry, next));
        } else {
            assert(entry == old_entry);
            if old_entry.request == target.request {
                assert(other == request_index);
            }
            assert(old_request != request);
            assert forall|candidate: replay_layer::AttemptId|
                1 <= candidate && candidate <= entry.outcomes@.len() implies
                    #[trigger] query_layer::d_outcome(
                        next, old_request, candidate,
                    ) == k_outcome_view(entry.outcomes@[candidate - 1]) by {
                query_layer::attempt_log_outcome_push(
                    durable.attempt_log,
                    old_request,
                    candidate,
                    appended,
                );
                assert(query_layer::d_outcome(
                    next, old_request, candidate,
                ) == query_layer::d_outcome(
                    durable, old_request, candidate,
                ));
            }
            assert(k_request_entry_couples(entry, next));
        }
    }

    assert forall|id: nat| !k_tracks_request(after, id) implies {
        &&& #[trigger] next.phase[replay_layer::RequestId { id }]
            == replay_layer::Phase::New
        &&& next.witness[replay_layer::RequestId { id }]
            == Option::<replay_layer::CapabilityId>::None
        &&& query_layer::d_started(
            next, replay_layer::RequestId { id },
        ) == 0
    } by {
        let candidate = replay_layer::RequestId { id };
        assert(!k_tracks_request(before, id));
        assert(k_tracks_request(before, target.request as nat));
        assert(id != target.request as nat);
        assert(candidate != request);
        query_layer::attempt_log_started_push(
            durable.attempt_log, candidate, appended,
        );
        assert(next.phase[candidate] == durable.phase[candidate]);
        assert(next.witness[candidate] == durable.witness[candidate]);
        assert(query_layer::d_started(next, candidate)
            == query_layer::d_started(durable, candidate));
    }

    assert(after.caps@ == before.caps@);
    assert forall|left: int, right: int|
        0 <= left < after.caps@.len()
            && 0 <= right < after.caps@.len()
            && #[trigger] after.caps@[left].capability
                == #[trigger] after.caps@[right].capability
        implies left == right by {
    }
    assert forall|other: int| 0 <= other < after.caps@.len() implies {
        let entry = #[trigger] after.caps@[other];
        &&& next.remaining[k_capability_id(entry.capability)]
            == entry.remaining as nat
        &&& next.revoked.contains(k_capability_id(entry.capability))
            == entry.revoked
    } by {
    }
    assert forall|id: nat| !k_tracks_capability(after, id) implies {
        &&& #[trigger] next.remaining[replay_layer::CapabilityId { id }]
            == cfg.initial_budget[replay_layer::CapabilityId { id }]
        &&& !next.revoked.contains(replay_layer::CapabilityId { id })
    } by {
    }
    assert(k_durable_inv(after, cfg, next));

    assert forall|candidate: replay_layer::RequestId,
                  future: replay_layer::AttemptId|
        future > query_layer::d_started(next, candidate) implies
            #[trigger] query_layer::d_outcome(
                next, candidate, future,
            ).is_none() by {
        query_layer::attempt_log_started_push(
            durable.attempt_log, candidate, appended,
        );
        query_layer::attempt_log_outcome_push(
            durable.attempt_log, candidate, future, appended,
        );
        assert(query_layer::d_started(next, candidate)
            == query_layer::d_started(durable, candidate));
        if candidate == request && future == attempt {
            assert(false);
        }
        assert(query_layer::d_outcome(next, candidate, future)
            == query_layer::d_outcome(durable, candidate, future));
    }
}

pub open spec fn k_outcome_record_for(
    record: replay_layer::JournalRecord,
    request: replay_layer::RequestId,
    observation: KObservation,
) -> bool {
    match record {
        replay_layer::JournalRecord::Outcome {
            request: target,
            observation: recorded,
            ..
        } => target == request && recorded == k_observation_view(observation),
        _ => false,
    }
}

pub proof fn k_outcome_delta_refines_apply_record(
    before: KDurable,
    after: KDurable,
    cfg: replay_layer::Config,
    durable: replay_layer::DurableBroker,
    request_index: int,
    observation: KObservation,
    record: replay_layer::JournalRecord,
)
    requires
        k_update_inv(before, cfg, durable),
        k_outcome_delta(
            before, after, request_index, observation,
        ),
        k_outcome_record_for(
            record,
            k_request_id(before.requests@[request_index].request),
            observation,
        ),
        query_layer::abstract_record_enabled(cfg, durable, record),
    ensures
        k_update_inv(
            after,
            cfg,
            replay_layer::apply_record(durable, record),
        ),
{
    let request = k_request_id(before.requests@[request_index].request);
    match record {
        replay_layer::JournalRecord::Outcome {
            request: target,
            attempt,
            observation: recorded,
            ..
        } => {
            assert(target == request);
            assert(recorded == k_observation_view(observation));
            assert(attempt > 0);
            assert(attempt == query_layer::d_started(durable, request));
            k_outcome_delta_preserves_update_inv(
                before,
                after,
                cfg,
                durable,
                request_index,
                attempt,
                observation,
            );
            assert(k_observed_durable_eq(
                k_durable_with_outcome(
                    durable, request, attempt, observation,
                ),
                replay_layer::apply_record(durable, record),
            ));
            k_update_inv_observed_transport(
                after,
                cfg,
                k_durable_with_outcome(
                    durable, request, attempt, observation,
                ),
                replay_layer::apply_record(durable, record),
            );
        },
        _ => assert(false),
    }
}

pub open spec fn k_default_request_delta(
    before: KDurable,
    after: KDurable,
    request: u64,
) -> bool {
    &&& after.requests@.len() == before.requests@.len() + 1
    &&& after.requests@.drop_last() == before.requests@
    &&& after.requests@.last().request == request
    &&& after.requests@.last().phase == KPhase::New
    &&& after.requests@.last().witness == Option::None
    &&& after.requests@.last().outcomes@ == Seq::empty()
    &&& after.caps@ == before.caps@
}

pub fn k_push_default_request(
    kd: &mut KDurable,
    request: u64,
) -> (index: usize)
    ensures
        index as int == old(kd).requests@.len(),
        k_default_request_delta(*old(kd), *final(kd), request),
{
    let index = kd.requests.len();
    let ghost before = kd.requests@;
    kd.requests.push(KRequestEntry {
        request,
        phase: KPhase::New,
        witness: Option::None,
        outcomes: Vec::new(),
    });
    proof {
        assert(kd.requests@.drop_last() =~= before);
        assert(kd.requests@.last().outcomes@ =~= Seq::empty());
    }
    index
}

pub open spec fn k_initial_cap_budget(capability: u64) -> u64 {
    if capability == 3 { 1u64 } else { 4u64 }
}

pub open spec fn k_default_cap_delta(
    before: KDurable,
    after: KDurable,
    capability: u64,
) -> bool {
    &&& after.requests@ == before.requests@
    &&& after.caps@.len() == before.caps@.len() + 1
    &&& after.caps@.drop_last() == before.caps@
    &&& after.caps@.last().capability == capability
    &&& after.caps@.last().remaining == k_initial_cap_budget(capability)
    &&& !after.caps@.last().revoked
}

pub fn k_push_default_capability(
    kd: &mut KDurable,
    capability: u64,
) -> (index: usize)
    ensures
        index as int == old(kd).caps@.len(),
        k_default_cap_delta(*old(kd), *final(kd), capability),
{
    let index = kd.caps.len();
    let ghost before = kd.caps@;
    let remaining = if capability == 3 { 1 } else { 4 };
    kd.caps.push(KCapEntry {
        capability,
        remaining,
        revoked: false,
    });
    proof {
        assert(kd.caps@.drop_last() =~= before);
    }
    index
}

pub proof fn k_default_request_delta_preserves_update_inv(
    before: KDurable,
    after: KDurable,
    cfg: replay_layer::Config,
    durable: replay_layer::DurableBroker,
    request: u64,
)
    requires
        k_update_inv(before, cfg, durable),
        k_default_request_delta(before, after, request),
        !k_tracks_request(before, request as nat),
        cfg.max_attempts[k_request_id(request)] > 0,
    ensures
        k_update_inv(after, cfg, durable),
{
    let new_index = before.requests@.len() as int;
    let new_entry = after.requests@[new_index];
    assert(after.requests@.len() > 0);
    assert(new_index == after.requests@.len() - 1);
    assert(after.requests@ =~= before.requests@.push(new_entry));

    assert forall|index: int| 0 <= index < before.requests@.len() implies
        #[trigger] before.requests@[index].request != request by {
        if before.requests@[index].request == request {
            assert(exists|witness: int|
                0 <= witness < before.requests@.len()
                    && #[trigger] before.requests@[witness].request as nat
                        == request as nat) by {
                assert(before.requests@[index].request as nat == request as nat);
            }
            assert(k_tracks_request(before, request as nat));
        }
    }
    assert forall|index: int| 0 <= index < before.requests@.len() implies
        #[trigger] after.requests@[index] == before.requests@[index] by {
    }
    assert(k_tracks_request(after, request as nat)) by {
        assert(new_entry.request == request);
        assert(exists|witness: int|
            0 <= witness < after.requests@.len()
                && #[trigger] after.requests@[witness].request as nat
                    == request as nat) by {
            assert(after.requests@[new_index].request as nat == request as nat);
        }
    }

    assert forall|left: int, right: int|
        0 <= left < after.requests@.len()
            && 0 <= right < after.requests@.len()
            && #[trigger] after.requests@[left].request
                == #[trigger] after.requests@[right].request
        implies left == right by {
        if left < before.requests@.len() && right < before.requests@.len() {
            assert(after.requests@[left] == before.requests@[left]);
            assert(after.requests@[right] == before.requests@[right]);
        } else if left < before.requests@.len() {
            assert(right == new_index);
            assert(after.requests@[right].request == request);
            assert(before.requests@[left].request != request);
        } else if right < before.requests@.len() {
            assert(left == new_index);
            assert(after.requests@[left].request == request);
            assert(before.requests@[right].request != request);
        } else {
            assert(left == new_index);
            assert(right == new_index);
        }
    }

    assert forall|index: int| 0 <= index < after.requests@.len() implies {
        let entry = #[trigger] after.requests@[index];
        &&& k_request_entry_couples(entry, durable)
        &&& entry.outcomes@.len()
            <= cfg.max_attempts[k_request_id(entry.request)]
    } by {
        let entry = after.requests@[index];
        if index < before.requests@.len() {
            assert(entry == before.requests@[index]);
        } else {
            assert(index == new_index);
            assert(entry == new_entry);
            assert(entry.request == request);
            assert(entry.phase == KPhase::New);
            assert(entry.witness == Option::None);
            assert(entry.outcomes@ =~= Seq::empty());
            let spec_request = k_request_id(request);
            assert(durable.phase[spec_request] == replay_layer::Phase::New);
            assert(durable.witness[spec_request]
                == Option::<replay_layer::CapabilityId>::None);
            assert(query_layer::d_started(durable, spec_request) == 0);
            assert forall|attempt: replay_layer::AttemptId|
                1 <= attempt && attempt <= entry.outcomes@.len() implies
                    #[trigger] query_layer::d_outcome(
                        durable, spec_request, attempt,
                    ) == k_outcome_view(entry.outcomes@[attempt - 1]) by {
            }
            assert(k_request_entry_couples(entry, durable));
            assert(entry.outcomes@.len()
                <= cfg.max_attempts[k_request_id(entry.request)]);
        }
    }

    assert forall|id: nat| k_tracks_request(before, id) implies
        #[trigger] k_tracks_request(after, id) by {
        let witness = choose|witness: int|
            0 <= witness < before.requests@.len()
                && #[trigger] before.requests@[witness].request as nat == id;
        assert(after.requests@[witness] == before.requests@[witness]);
    }
    assert forall|id: nat| !k_tracks_request(after, id) implies {
        &&& #[trigger] durable.phase[replay_layer::RequestId { id }]
            == replay_layer::Phase::New
        &&& durable.witness[replay_layer::RequestId { id }]
            == Option::<replay_layer::CapabilityId>::None
        &&& query_layer::d_started(
            durable, replay_layer::RequestId { id },
        ) == 0
    } by {
        assert(!k_tracks_request(before, id));
    }

    assert(after.caps@ == before.caps@);
    assert(k_durable_inv(after, cfg, durable));
    assert(k_no_future_outcomes(durable));
}

pub proof fn k_default_cap_delta_preserves_update_inv(
    before: KDurable,
    after: KDurable,
    cfg: replay_layer::Config,
    durable: replay_layer::DurableBroker,
    capability: u64,
)
    requires
        k_update_inv(before, cfg, durable),
        k_default_cap_delta(before, after, capability),
        !k_tracks_capability(before, capability as nat),
        cfg.initial_budget[k_capability_id(capability)]
            == k_initial_cap_budget(capability) as nat,
    ensures
        k_update_inv(after, cfg, durable),
{
    let new_index = before.caps@.len() as int;
    let new_entry = after.caps@[new_index];
    assert(after.caps@.len() > 0);
    assert(new_index == after.caps@.len() - 1);
    assert(after.caps@ =~= before.caps@.push(new_entry));

    assert forall|index: int| 0 <= index < before.caps@.len() implies
        #[trigger] before.caps@[index].capability != capability by {
        if before.caps@[index].capability == capability {
            assert(exists|witness: int|
                0 <= witness < before.caps@.len()
                    && #[trigger] before.caps@[witness].capability as nat
                        == capability as nat) by {
                assert(before.caps@[index].capability as nat
                    == capability as nat);
            }
            assert(k_tracks_capability(before, capability as nat));
        }
    }
    assert forall|index: int| 0 <= index < before.caps@.len() implies
        #[trigger] after.caps@[index] == before.caps@[index] by {
    }
    assert(k_tracks_capability(after, capability as nat)) by {
        assert(new_entry.capability == capability);
        assert(exists|witness: int|
            0 <= witness < after.caps@.len()
                && #[trigger] after.caps@[witness].capability as nat
                    == capability as nat) by {
            assert(after.caps@[new_index].capability as nat
                == capability as nat);
        }
    }

    assert forall|left: int, right: int|
        0 <= left < after.caps@.len()
            && 0 <= right < after.caps@.len()
            && #[trigger] after.caps@[left].capability
                == #[trigger] after.caps@[right].capability
        implies left == right by {
        if left < before.caps@.len() && right < before.caps@.len() {
            assert(after.caps@[left] == before.caps@[left]);
            assert(after.caps@[right] == before.caps@[right]);
        } else if left < before.caps@.len() {
            assert(right == new_index);
            assert(after.caps@[right].capability == capability);
            assert(before.caps@[left].capability != capability);
        } else if right < before.caps@.len() {
            assert(left == new_index);
            assert(after.caps@[left].capability == capability);
            assert(before.caps@[right].capability != capability);
        } else {
            assert(left == new_index);
            assert(right == new_index);
        }
    }

    assert forall|index: int| 0 <= index < after.caps@.len() implies {
        let entry = #[trigger] after.caps@[index];
        &&& durable.remaining[k_capability_id(entry.capability)]
            == entry.remaining as nat
        &&& durable.revoked.contains(k_capability_id(entry.capability))
            == entry.revoked
    } by {
        let entry = after.caps@[index];
        if index < before.caps@.len() {
            assert(entry == before.caps@[index]);
        } else {
            assert(index == new_index);
            assert(entry == new_entry);
            assert(entry.capability == capability);
            assert(entry.remaining == k_initial_cap_budget(capability));
            assert(!entry.revoked);
            let spec_capability = k_capability_id(capability);
            assert(durable.remaining[spec_capability]
                == cfg.initial_budget[spec_capability]);
            assert(durable.remaining[spec_capability] == entry.remaining as nat);
            assert(!durable.revoked.contains(spec_capability));
        }
    }

    assert forall|id: nat| k_tracks_capability(before, id) implies
        #[trigger] k_tracks_capability(after, id) by {
        let witness = choose|witness: int|
            0 <= witness < before.caps@.len()
                && #[trigger] before.caps@[witness].capability as nat == id;
        assert(after.caps@[witness] == before.caps@[witness]);
    }
    assert forall|id: nat| !k_tracks_capability(after, id) implies {
        &&& #[trigger] durable.remaining[replay_layer::CapabilityId { id }]
            == cfg.initial_budget[replay_layer::CapabilityId { id }]
        &&& !durable.revoked.contains(replay_layer::CapabilityId { id })
    } by {
        assert(!k_tracks_capability(before, id));
    }

    assert(after.requests@ == before.requests@);
    assert(k_durable_inv(after, cfg, durable));
    assert(k_no_future_outcomes(durable));
}

pub fn k_ensure_request(
    kd: &mut KDurable,
    request: u64,
    Ghost(durable): Ghost<replay_layer::DurableBroker>,
) -> (index: usize)
    requires
        k_update_inv(*old(kd), k_demo_config(), durable),
    ensures
        index < final(kd).requests@.len(),
        final(kd).requests@[index as int].request == request,
        k_update_inv(*final(kd), k_demo_config(), durable),
        k_tracks_request(*old(kd), request as nat) ==>
            *final(kd) == *old(kd),
        !k_tracks_request(*old(kd), request as nat) ==>
            k_default_request_delta(*old(kd), *final(kd), request),
{
    match k_find_request(kd, request) {
        Option::Some(index) => {
            proof {
                assert(k_tracks_request(*kd, request as nat)) by {
                    assert(exists|witness: int|
                        0 <= witness < kd.requests@.len()
                            && #[trigger] kd.requests@[witness].request as nat
                                == request as nat) by {
                        assert(kd.requests@[index as int].request as nat
                            == request as nat);
                    }
                }
            }
            index
        },
        Option::None => {
            let ghost before = *kd;
            proof {
                assert(!k_tracks_request(before, request as nat));
            }
            let index = k_push_default_request(kd, request);
            proof {
                k_demo_config_is_well_formed();
                assert(k_demo_config().max_attempts[k_request_id(request)] > 0);
                k_default_request_delta_preserves_update_inv(
                    before,
                    *kd,
                    k_demo_config(),
                    durable,
                    request,
                );
            }
            index
        },
    }
}

pub fn k_ensure_capability(
    kd: &mut KDurable,
    capability: u64,
    Ghost(durable): Ghost<replay_layer::DurableBroker>,
) -> (index: usize)
    requires
        k_update_inv(*old(kd), k_demo_config(), durable),
    ensures
        index < final(kd).caps@.len(),
        final(kd).caps@[index as int].capability == capability,
        k_update_inv(*final(kd), k_demo_config(), durable),
        k_tracks_capability(*old(kd), capability as nat) ==>
            *final(kd) == *old(kd),
        !k_tracks_capability(*old(kd), capability as nat) ==>
            k_default_cap_delta(*old(kd), *final(kd), capability),
{
    match k_find_capability(kd, capability) {
        Option::Some(index) => {
            proof {
                assert(k_tracks_capability(*kd, capability as nat)) by {
                    assert(exists|witness: int|
                        0 <= witness < kd.caps@.len()
                            && #[trigger] kd.caps@[witness].capability as nat
                                == capability as nat) by {
                        assert(kd.caps@[index as int].capability as nat
                            == capability as nat);
                    }
                }
            }
            index
        },
        Option::None => {
            let ghost before = *kd;
            proof {
                assert(!k_tracks_capability(before, capability as nat));
            }
            let index = k_push_default_capability(kd, capability);
            proof {
                if capability == 3 {
                    assert(k_capability_id(capability).id == 3);
                } else {
                    assert(k_capability_id(capability).id != 3);
                }
                assert(k_demo_config().initial_budget[
                    k_capability_id(capability)
                ] == k_initial_cap_budget(capability) as nat);
                k_default_cap_delta_preserves_update_inv(
                    before,
                    *kd,
                    k_demo_config(),
                    durable,
                    capability,
                );
            }
            index
        },
    }
}

// These wrappers are the accepted-record mutation boundary.  Guard evaluation
// and exact Journal references remain separate; each wrapper consumes the
// reference-erased acceptance fact and preserves the executable coupling.
pub fn k_apply_authorize(
    kd: &mut KDurable,
    request_index: usize,
    cap_index: usize,
    request: u64,
    capability: u64,
    digest: u64,
    Ghost(durable): Ghost<replay_layer::DurableBroker>,
)
    requires
        k_update_inv(*old(kd), k_demo_config(), durable),
        request_index < old(kd).requests@.len(),
        cap_index < old(kd).caps@.len(),
        old(kd).requests@[request_index as int].request == request,
        old(kd).caps@[cap_index as int].capability == capability,
        query_layer::abstract_record_enabled(
            k_demo_config(),
            durable,
            replay_layer::JournalRecord::Authorize {
                request: k_request_id(request),
                capability: k_capability_id(capability),
                digest: k_digest_id(digest),
            },
        ),
    ensures
        k_update_inv(
            *final(kd),
            k_demo_config(),
            replay_layer::apply_record(
                durable,
                replay_layer::JournalRecord::Authorize {
                    request: k_request_id(request),
                    capability: k_capability_id(capability),
                    digest: k_digest_id(digest),
                },
            ),
        ),
{
    proof {
        let entry = old(kd).caps@[cap_index as int];
        assert(durable.remaining[k_capability_id(entry.capability)]
            == entry.remaining as nat);
        assert(durable.remaining[k_capability_id(capability)] > 0);
        assert(entry.remaining > 0);
    }
    let ghost before = *kd;
    k_set_authorized(kd, request_index, cap_index, capability);
    proof {
        k_authorize_delta_refines_apply_record(
            before,
            *kd,
            k_demo_config(),
            durable,
            request_index as int,
            cap_index as int,
            request,
            capability,
            digest,
        );
    }
}

pub fn k_apply_revoke(
    kd: &mut KDurable,
    cap_index: usize,
    capability: u64,
    Ghost(durable): Ghost<replay_layer::DurableBroker>,
)
    requires
        k_update_inv(*old(kd), k_demo_config(), durable),
        cap_index < old(kd).caps@.len(),
        old(kd).caps@[cap_index as int].capability == capability,
        query_layer::abstract_record_enabled(
            k_demo_config(),
            durable,
            replay_layer::JournalRecord::Revoke {
                capability: k_capability_id(capability),
            },
        ),
    ensures
        k_update_inv(
            *final(kd),
            k_demo_config(),
            replay_layer::apply_record(
                durable,
                replay_layer::JournalRecord::Revoke {
                    capability: k_capability_id(capability),
                },
            ),
        ),
{
    let ghost before = *kd;
    k_set_revoked(kd, cap_index);
    proof {
        k_revoke_delta_refines_apply_record(
            before,
            *kd,
            k_demo_config(),
            durable,
            cap_index as int,
            capability,
        );
    }
}

pub fn k_apply_phase_record(
    kd: &mut KDurable,
    request_index: usize,
    phase: KPhase,
    Ghost(record): Ghost<replay_layer::JournalRecord>,
    Ghost(durable): Ghost<replay_layer::DurableBroker>,
)
    requires
        k_update_inv(*old(kd), k_demo_config(), durable),
        request_index < old(kd).requests@.len(),
        k_phase_record_shape(
            record,
            k_request_id(old(kd).requests@[request_index as int].request),
            k_phase_view(phase),
        ),
        query_layer::abstract_record_enabled(
            k_demo_config(), durable, record,
        ),
    ensures
        k_update_inv(
            *final(kd),
            k_demo_config(),
            replay_layer::apply_record(durable, record),
        ),
{
    let ghost before = *kd;
    k_set_request_phase(kd, request_index, phase);
    proof {
        k_phase_record_delta_refines_apply_record(
            before,
            *kd,
            k_demo_config(),
            durable,
            request_index as int,
            phase,
            record,
        );
    }
}

pub fn k_apply_start(
    kd: &mut KDurable,
    request_index: usize,
    request: u64,
    attempt: u64,
    digest: u64,
    key_present: bool,
    key: u64,
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
                arm_ref: 0,
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
                    arm_ref: 0,
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
            arm_ref: 0,
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

pub fn k_apply_outcome(
    kd: &mut KDurable,
    request_index: usize,
    request: u64,
    attempt: u64,
    observation: KObservation,
    digest: u64,
    key_present: bool,
    key: u64,
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
                start_ref: 0,
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
                    start_ref: 0,
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
            start_ref: 0,
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

} // verus!
