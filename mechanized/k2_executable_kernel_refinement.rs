use vstd::prelude::*;

#[path = "k1_executable_kernel.rs"]
pub mod k1_layer;

verus! {

use k1_layer::*;
use k1_layer::query_layer as query_layer;
use query_layer::c1_layer;
use c1_layer::replay_layer;

// K2-G0 completes the executable, reference-erased record guards for the
// fixed K1 demo configuration.  It deliberately does not mutate KDurable.
// The zero references below are semantically inert only because the target is
// Q1's `abstract_record_enabled`; exact LSN references, mode/slot control, and
// append linearization remain obligations of later kernel milestones.

#[derive(PartialEq, Eq, Clone, Copy)]
pub enum KRetryClass {
    ReadOnly,
    Idempotent,
    Deduplicated,
    Uncontrolled,
}

pub open spec fn k_retry_class_view(
    class: KRetryClass,
) -> replay_layer::RetryClass {
    match class {
        KRetryClass::ReadOnly => replay_layer::RetryClass::ReadOnly,
        KRetryClass::Idempotent => replay_layer::RetryClass::Idempotent,
        KRetryClass::Deduplicated => replay_layer::RetryClass::Deduplicated,
        KRetryClass::Uncontrolled => replay_layer::RetryClass::Uncontrolled,
    }
}

#[derive(PartialEq, Eq, Clone, Copy)]
pub enum KUnknownReason {
    Exhausted,
    Recovery,
    NonConclusiveFailure,
    AmbiguousOutcome,
    InvalidResultReason,
}

pub open spec fn k_unknown_reason_view(
    reason: KUnknownReason,
) -> replay_layer::UnknownReason {
    match reason {
        KUnknownReason::Exhausted => replay_layer::UnknownReason::Exhausted,
        KUnknownReason::Recovery => replay_layer::UnknownReason::Recovery,
        KUnknownReason::NonConclusiveFailure =>
            replay_layer::UnknownReason::NonConclusiveFailure,
        KUnknownReason::AmbiguousOutcome =>
            replay_layer::UnknownReason::AmbiguousOutcome,
        KUnknownReason::InvalidResultReason =>
            replay_layer::UnknownReason::InvalidResultReason,
    }
}

pub proof fn k_phase_view_reflects(
    phase: KPhase,
    abstract_phase: replay_layer::Phase,
)
    requires
        k_phase_view(phase) == abstract_phase,
    ensures
        (phase == KPhase::New)
            == (abstract_phase == replay_layer::Phase::New),
        (phase == KPhase::Authorized)
            == (abstract_phase == replay_layer::Phase::Authorized),
        (phase == KPhase::Prepared)
            == (abstract_phase == replay_layer::Phase::Prepared),
        (phase == KPhase::Armed)
            == (abstract_phase == replay_layer::Phase::Armed),
        (phase == KPhase::Committed)
            == (abstract_phase == replay_layer::Phase::Committed),
        (phase == KPhase::Failed)
            == (abstract_phase == replay_layer::Phase::Failed),
        (phase == KPhase::Unknown)
            == (abstract_phase == replay_layer::Phase::Unknown),
{
    match phase {
        KPhase::New => {},
        KPhase::Authorized => {},
        KPhase::Prepared => {},
        KPhase::Armed => {},
        KPhase::Committed => {},
        KPhase::Failed => {},
        KPhase::Unknown => {},
    }
}

pub open spec fn k_key_view(
    key_present: bool,
    key: u64,
) -> Option<replay_layer::StableKey> {
    if key_present {
        Option::Some(replay_layer::StableKey { id: key as nat })
    } else {
        Option::None
    }
}

pub open spec fn k_attempt_view(
    attempt_present: bool,
    attempt: u64,
) -> Option<replay_layer::AttemptId> {
    if attempt_present { Option::Some(attempt as nat) } else { Option::None }
}

// The fixed demo request fields are executable: digest equals request, and a
// stable key equal to the request exists exactly in the Deduplicated lane.
pub fn k_fields_match(
    request: u64,
    digest: u64,
    key_present: bool,
    key: u64,
) -> (matches: bool)
    ensures
        matches == replay_layer::request_fields_match(
            k_demo_config(),
            k_request_id(request),
            k_digest_id(digest),
            k_key_view(key_present, key),
        ),
{
    let lane = request % 4;
    let digest_matches = digest == request;
    let key_matches = if lane == 2 {
        key_present && key == request
    } else {
        !key_present
    };
    proof {
        let cfg = k_demo_config();
        let spec_request = k_request_id(request);
        assert(k_lane_of(spec_request) == (request as nat) % 4);
        assert((request % 4) as nat == (request as nat) % 4);
        assert(cfg.request_digest[spec_request]
            == replay_layer::Digest { id: spec_request.id });
        assert(cfg.request_key[spec_request] == if k_lane_of(spec_request) == 2 {
            Option::Some(replay_layer::StableKey { id: spec_request.id })
        } else {
            Option::<replay_layer::StableKey>::None
        });
    }
    digest_matches && key_matches
}

pub fn k_class_matches(request: u64, class: KRetryClass) -> (matches: bool)
    ensures
        matches == (k_retry_class_view(class)
            == k_demo_config().request_class[k_request_id(request)]),
{
    let lane = request % 4;
    let matches = if lane == 0 {
        match class {
            KRetryClass::ReadOnly => true,
            _ => false,
        }
    } else if lane == 1 {
        match class {
            KRetryClass::Idempotent => true,
            _ => false,
        }
    } else if lane == 2 {
        match class {
            KRetryClass::Deduplicated => true,
            _ => false,
        }
    } else {
        match class {
            KRetryClass::Uncontrolled => true,
            _ => false,
        }
    };
    proof {
        let spec_request = k_request_id(request);
        assert(k_lane_of(spec_request) == (request as nat) % 4);
        assert((request % 4) as nat == (request as nat) % 4);
        assert(request % 4 < 4);
        assert(k_demo_config().request_class[spec_request]
            == k_class_of_lane(k_lane_of(spec_request)));
        if lane == 0 {
            assert(matches == (class == KRetryClass::ReadOnly));
            match class {
                KRetryClass::ReadOnly => {},
                KRetryClass::Idempotent => {},
                KRetryClass::Deduplicated => {},
                KRetryClass::Uncontrolled => {},
            }
        } else if lane == 1 {
            assert(matches == (class == KRetryClass::Idempotent));
            match class {
                KRetryClass::ReadOnly => {},
                KRetryClass::Idempotent => {},
                KRetryClass::Deduplicated => {},
                KRetryClass::Uncontrolled => {},
            }
        } else if lane == 2 {
            assert(matches == (class == KRetryClass::Deduplicated));
            match class {
                KRetryClass::ReadOnly => {},
                KRetryClass::Idempotent => {},
                KRetryClass::Deduplicated => {},
                KRetryClass::Uncontrolled => {},
            }
        } else {
            assert(lane == 3);
            assert(matches == (class == KRetryClass::Uncontrolled));
            match class {
                KRetryClass::ReadOnly => {},
                KRetryClass::Idempotent => {},
                KRetryClass::Deduplicated => {},
                KRetryClass::Uncontrolled => {},
            }
        }
    }
    matches
}

pub proof fn k_demo_entry_attempt_bound(
    kd: KDurable,
    durable: replay_layer::DurableBroker,
    index: int,
)
    requires
        k_durable_inv(kd, k_demo_config(), durable),
        0 <= index < kd.requests@.len(),
    ensures
        k_request_entry_couples(kd.requests@[index], durable),
        kd.requests@[index].outcomes@.len() <= 3,
{
    let entry = kd.requests@[index];
    let request = k_request_id(entry.request);
    assert(entry.outcomes@.len()
        <= k_demo_config().max_attempts[request]);
    assert(k_lane_of(request) == (entry.request as nat) % 4);
    assert((entry.request % 4) as nat == (entry.request as nat) % 4);
    assert(k_demo_config().max_attempts[request]
        == if k_lane_of(request) == 3 { 1nat } else { 3nat });
}

pub proof fn k_demo_cap_entry_facts(
    kd: KDurable,
    durable: replay_layer::DurableBroker,
    index: int,
)
    requires
        k_durable_inv(kd, k_demo_config(), durable),
        0 <= index < kd.caps@.len(),
    ensures
        durable.remaining[k_capability_id(kd.caps@[index].capability)]
            == kd.caps@[index].remaining as nat,
        durable.revoked.contains(
            k_capability_id(kd.caps@[index].capability),
        ) == kd.caps@[index].revoked,
{
}

pub proof fn k_demo_untracked_capability_facts(
    kd: KDurable,
    durable: replay_layer::DurableBroker,
    capability: u64,
)
    requires
        k_durable_inv(kd, k_demo_config(), durable),
        !k_tracks_capability(kd, capability as nat),
    ensures
        durable.remaining[k_capability_id(capability)]
            == k_demo_config().initial_budget[k_capability_id(capability)],
        !durable.revoked.contains(k_capability_id(capability)),
{
    let id = capability as nat;
    let spec_capability = replay_layer::CapabilityId { id };
    assert(k_capability_id(capability) == spec_capability);
    assert(!k_tracks_capability(kd, id));
    assert(durable.remaining[spec_capability]
        == k_demo_config().initial_budget[spec_capability]);
    assert(!durable.revoked.contains(spec_capability));
}

// This includes the positive-attempt check used by Outcome and all terminal
// records.  K1's invariant bounds every demo entry by three attempts.
pub fn k_attempt_is_latest(
    entry: &KRequestEntry,
    attempt: u64,
    Ghost(durable): Ghost<replay_layer::DurableBroker>,
) -> (latest: bool)
    requires
        k_request_entry_couples(*entry, durable),
        entry.outcomes@.len() <= 3,
    ensures
        latest == (
            attempt as nat > 0
                && attempt as nat == query_layer::d_started(
                    durable, k_request_id(entry.request),
                )
        ),
{
    let started = entry.outcomes.len();
    let latest = if started == 1 {
        attempt == 1
    } else if started == 2 {
        attempt == 2
    } else if started == 3 {
        attempt == 3
    } else {
        false
    };
    proof {
        assert(query_layer::d_started(
            durable, k_request_id(entry.request),
        ) == entry.outcomes@.len());
    }
    latest
}

pub fn k_latest_outcome(entry: &KRequestEntry) -> (outcome: Option<KObservation>)
    ensures
        outcome == if entry.outcomes@.len() == 0 {
            Option::None
        } else {
            entry.outcomes@[entry.outcomes@.len() - 1]
        },
{
    if entry.outcomes.len() == 0 {
        Option::None
    } else {
        entry.outcomes[entry.outcomes.len() - 1]
    }
}

// Durable uncertainty is exactly the presence of a started attempt whose
// summary is absent or is any observation other than Failure.
pub fn k_uncertain(
    entry: &KRequestEntry,
    Ghost(durable): Ghost<replay_layer::DurableBroker>,
) -> (uncertain: bool)
    requires
        k_request_entry_couples(*entry, durable),
        entry.outcomes@.len() <= 3,
    ensures
        uncertain == query_layer::d_uncertain(
            durable, k_request_id(entry.request),
        ),
{
    let ghost request = k_request_id(entry.request);
    let mut index: usize = 0;
    while index < entry.outcomes.len()
        invariant
            index <= entry.outcomes@.len(),
            request == k_request_id(entry.request),
            k_request_entry_couples(*entry, durable),
            forall|scanned: int| 0 <= scanned < index ==>
                k_outcome_view(#[trigger] entry.outcomes@[scanned])
                    == Option::Some(replay_layer::Observation::Failure),
        decreases entry.outcomes@.len() - index,
    {
        let is_uncertain = match entry.outcomes[index] {
            Option::Some(KObservation::Failure) => false,
            _ => true,
        };
        if is_uncertain {
            proof {
                let attempt = (index + 1) as nat;
                assert(1 <= attempt && attempt <= entry.outcomes@.len());
                assert(attempt - 1 == index as int);
                assert(k_request_entry_couples(*entry, durable));
                assert(query_layer::d_outcome(durable, request, attempt)
                    == k_outcome_view(entry.outcomes@[attempt - 1]));
                assert(entry.outcomes@[attempt - 1]
                    == entry.outcomes@[index as int]);
                match entry.outcomes@[index as int] {
                    Option::None => {},
                    Option::Some(KObservation::Success { .. }) => {},
                    Option::Some(KObservation::Ambiguous) => {},
                    Option::Some(KObservation::InvalidResult { .. }) => {},
                    Option::Some(KObservation::Failure) => assert(false),
                }
                assert(exists|candidate: replay_layer::AttemptId|
                    1 <= candidate
                        && candidate <= query_layer::d_started(durable, request)
                        && match #[trigger] query_layer::d_outcome(
                            durable, request, candidate,
                        ) {
                            Option::None => true,
                            Option::Some(replay_layer::Observation::Failure) => false,
                            Option::Some(_) => true,
                        }) by {
                    assert(query_layer::d_started(durable, request)
                        == entry.outcomes@.len());
                }
                assert(query_layer::d_uncertain(durable, request));
            }
            return true;
        }
        proof {
            assert(k_outcome_view(entry.outcomes@[index as int])
                == Option::Some(replay_layer::Observation::Failure));
        }
        index = index + 1;
    }
    proof {
        assert(k_request_entry_couples(*entry, durable));
        assert forall|attempt: replay_layer::AttemptId|
            1 <= attempt && attempt <= query_layer::d_started(durable, request)
        implies
            #[trigger] query_layer::d_outcome(durable, request, attempt)
                == Option::Some(replay_layer::Observation::Failure) by {
            assert(query_layer::d_started(durable, request)
                == entry.outcomes@.len());
            assert(0 <= attempt - 1 && attempt - 1 < entry.outcomes@.len());
            assert(k_outcome_view(entry.outcomes@[attempt - 1])
                == Option::Some(replay_layer::Observation::Failure));
            assert(query_layer::d_outcome(durable, request, attempt)
                == k_outcome_view(entry.outcomes@[attempt - 1]));
        }
        if query_layer::d_uncertain(durable, request) {
            let attempt = choose|attempt: replay_layer::AttemptId|
                1 <= attempt
                    && attempt <= query_layer::d_started(durable, request)
                    && match #[trigger] query_layer::d_outcome(
                        durable, request, attempt,
                    ) {
                        Option::None => true,
                        Option::Some(replay_layer::Observation::Failure) => false,
                        Option::Some(_) => true,
                    };
            assert(query_layer::d_outcome(durable, request, attempt)
                == Option::Some(replay_layer::Observation::Failure));
            assert(false);
        }
        assert(!query_layer::d_uncertain(durable, request));
    }
    false
}

pub fn k_guard_revoke(
    kd: &KDurable,
    capability: u64,
    Ghost(durable): Ghost<replay_layer::DurableBroker>,
) -> (decision: bool)
    requires
        k_durable_inv(*kd, k_demo_config(), durable),
    ensures
        decision == query_layer::abstract_record_enabled(
            k_demo_config(),
            durable,
            replay_layer::JournalRecord::Revoke {
                capability: k_capability_id(capability),
            },
        ),
{
    match k_find_capability(kd, capability) {
        Option::Some(index) => {
            let revoked = kd.caps[index].revoked;
            proof {
                k_demo_cap_entry_facts(*kd, durable, index as int);
                let entry = kd.caps@[index as int];
                assert(durable.revoked.contains(
                    k_capability_id(entry.capability),
                ) == entry.revoked);
            }
            !revoked
        },
        Option::None => {
            proof {
                assert(!k_tracks_capability(*kd, capability as nat));
                k_demo_untracked_capability_facts(*kd, durable, capability);
                assert(!durable.revoked.contains(k_capability_id(capability)));
            }
            true
        },
    }
}

pub fn k_guard_prepare(
    kd: &KDurable,
    request: u64,
    class: KRetryClass,
    digest: u64,
    key_present: bool,
    key: u64,
    Ghost(durable): Ghost<replay_layer::DurableBroker>,
) -> (decision: bool)
    requires
        k_durable_inv(*kd, k_demo_config(), durable),
    ensures
        decision == query_layer::abstract_record_enabled(
            k_demo_config(),
            durable,
            replay_layer::JournalRecord::Prepare {
                request: k_request_id(request),
                class: k_retry_class_view(class),
                digest: k_digest_id(digest),
                key: k_key_view(key_present, key),
                auth_ref: 0,
            },
        ),
{
    let class_matches = k_class_matches(request, class);
    let fields_match = k_fields_match(request, digest, key_present, key);
    let lane = request % 4;
    match k_find_request(kd, request) {
        Option::Some(index) => {
            let entry = &kd.requests[index];
            let phase_authorized = match entry.phase {
                KPhase::Authorized => true,
                _ => false,
            };
            let witness_matches = match entry.witness {
                Option::Some(capability) => capability == lane,
                Option::None => false,
            };
            proof {
                let cfg = k_demo_config();
                let spec_request = k_request_id(request);
                k_demo_entry_attempt_bound(*kd, durable, index as int);
                assert(k_request_entry_couples(
                    kd.requests@[index as int], durable,
                ));
                assert(k_phase_view(entry.phase) == durable.phase[spec_request]);
                k_phase_view_reflects(entry.phase, durable.phase[spec_request]);
                assert(phase_authorized == (entry.phase == KPhase::Authorized));
                assert(k_lane_of(spec_request) == (request as nat) % 4);
                assert((request % 4) as nat == (request as nat) % 4);
                assert(cfg.request_capability[spec_request]
                    == replay_layer::CapabilityId { id: k_lane_of(spec_request) });
                assert(phase_authorized == (
                    durable.phase[spec_request] == replay_layer::Phase::Authorized
                ));
                assert(witness_matches == (
                    durable.witness[spec_request]
                        == Option::Some(cfg.request_capability[spec_request])
                ));
            }
            phase_authorized && class_matches && fields_match && witness_matches
        },
        Option::None => {
            proof {
                let spec_request = k_request_id(request);
                assert(!k_tracks_request(*kd, request as nat));
                assert(durable.phase[spec_request] == replay_layer::Phase::New);
            }
            false
        },
    }
}

pub fn k_guard_arm(
    kd: &KDurable,
    request: u64,
    digest: u64,
    key_present: bool,
    key: u64,
    Ghost(durable): Ghost<replay_layer::DurableBroker>,
) -> (decision: bool)
    requires
        k_durable_inv(*kd, k_demo_config(), durable),
    ensures
        decision == query_layer::abstract_record_enabled(
            k_demo_config(),
            durable,
            replay_layer::JournalRecord::Arm {
                request: k_request_id(request),
                digest: k_digest_id(digest),
                key: k_key_view(key_present, key),
                prepare_ref: 0,
            },
        ),
{
    let fields_match = k_fields_match(request, digest, key_present, key);
    match k_find_request(kd, request) {
        Option::Some(index) => {
            let phase_prepared = match kd.requests[index].phase {
                KPhase::Prepared => true,
                _ => false,
            };
            proof {
                let spec_request = k_request_id(request);
                k_demo_entry_attempt_bound(*kd, durable, index as int);
                assert(k_request_entry_couples(
                    kd.requests@[index as int], durable,
                ));
                assert(k_phase_view(kd.requests@[index as int].phase)
                    == durable.phase[spec_request]);
                k_phase_view_reflects(
                    kd.requests@[index as int].phase,
                    durable.phase[spec_request],
                );
                assert(phase_prepared == (
                    kd.requests@[index as int].phase == KPhase::Prepared
                ));
                assert(phase_prepared == (
                    durable.phase[spec_request] == replay_layer::Phase::Prepared
                ));
            }
            phase_prepared && fields_match
        },
        Option::None => {
            proof {
                let spec_request = k_request_id(request);
                assert(!k_tracks_request(*kd, request as nat));
                assert(durable.phase[spec_request] == replay_layer::Phase::New);
            }
            false
        },
    }
}

pub fn k_guard_outcome(
    kd: &KDurable,
    request: u64,
    attempt: u64,
    observation: KObservation,
    digest: u64,
    key_present: bool,
    key: u64,
    Ghost(durable): Ghost<replay_layer::DurableBroker>,
) -> (decision: bool)
    requires
        k_durable_inv(*kd, k_demo_config(), durable),
    ensures
        decision == query_layer::abstract_record_enabled(
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
{
    let fields_match = k_fields_match(request, digest, key_present, key);
    match k_find_request(kd, request) {
        Option::Some(index) => {
            proof {
                k_demo_entry_attempt_bound(*kd, durable, index as int);
            }
            let entry = &kd.requests[index];
            let phase_armed = match entry.phase {
                KPhase::Armed => true,
                _ => false,
            };
            let attempt_latest = k_attempt_is_latest(
                entry, attempt, Ghost(durable),
            );
            let latest_outcome = k_latest_outcome(entry);
            let outcome_missing = latest_outcome.is_none();
            proof {
                let cfg = k_demo_config();
                let spec_request = k_request_id(request);
                assert(k_request_entry_couples(*entry, durable));
                assert(k_phase_view(entry.phase) == durable.phase[spec_request]);
                k_phase_view_reflects(entry.phase, durable.phase[spec_request]);
                assert(phase_armed == (entry.phase == KPhase::Armed));
                assert(phase_armed == (
                    durable.phase[spec_request] == replay_layer::Phase::Armed
                ));
                if attempt_latest {
                    assert(attempt as nat == entry.outcomes@.len());
                    assert(entry.outcomes@.len() > 0);
                    assert(query_layer::d_outcome(
                        durable, spec_request, attempt as nat,
                    ) == k_outcome_view(latest_outcome));
                }
                assert((attempt_latest && outcome_missing) == (
                    attempt as nat > 0
                        && attempt as nat
                            == query_layer::d_started(durable, spec_request)
                        && query_layer::d_outcome(
                            durable, spec_request, attempt as nat,
                        ).is_none()
                ));
                assert(cfg.valid_results.contains((
                    spec_request,
                    replay_layer::Value { id: match observation {
                        KObservation::Success { value } => value as nat,
                        _ => 0nat,
                    } },
                )));
                assert(replay_layer::success_is_valid(
                    cfg, spec_request, k_observation_view(observation),
                ));
            }
            phase_armed && fields_match && attempt_latest && outcome_missing
        },
        Option::None => {
            proof {
                let spec_request = k_request_id(request);
                assert(!k_tracks_request(*kd, request as nat));
                assert(durable.phase[spec_request] == replay_layer::Phase::New);
            }
            false
        },
    }
}

pub fn k_guard_commit(
    kd: &KDurable,
    request: u64,
    attempt: u64,
    value: u64,
    digest: u64,
    key_present: bool,
    key: u64,
    Ghost(durable): Ghost<replay_layer::DurableBroker>,
) -> (decision: bool)
    requires
        k_durable_inv(*kd, k_demo_config(), durable),
    ensures
        decision == query_layer::abstract_record_enabled(
            k_demo_config(),
            durable,
            replay_layer::JournalRecord::CommitRec {
                request: k_request_id(request),
                attempt: attempt as nat,
                value: replay_layer::Value { id: value as nat },
                digest: k_digest_id(digest),
                key: k_key_view(key_present, key),
                outcome_ref: 0,
            },
        ),
{
    let fields_match = k_fields_match(request, digest, key_present, key);
    match k_find_request(kd, request) {
        Option::Some(index) => {
            proof {
                k_demo_entry_attempt_bound(*kd, durable, index as int);
            }
            let entry = &kd.requests[index];
            let phase_armed = match entry.phase {
                KPhase::Armed => true,
                _ => false,
            };
            let attempt_latest = k_attempt_is_latest(
                entry, attempt, Ghost(durable),
            );
            let latest_outcome = k_latest_outcome(entry);
            let value_matches = match latest_outcome {
                Option::Some(KObservation::Success { value: observed }) => {
                    observed == value
                },
                _ => false,
            };
            proof {
                let spec_request = k_request_id(request);
                assert(k_request_entry_couples(*entry, durable));
                assert(k_phase_view(entry.phase) == durable.phase[spec_request]);
                k_phase_view_reflects(entry.phase, durable.phase[spec_request]);
                assert(phase_armed == (entry.phase == KPhase::Armed));
                assert(phase_armed == (
                    durable.phase[spec_request] == replay_layer::Phase::Armed
                ));
                if attempt_latest {
                    assert(attempt as nat == entry.outcomes@.len());
                    assert(entry.outcomes@.len() > 0);
                    assert(query_layer::d_outcome(
                        durable, spec_request, attempt as nat,
                    ) == k_outcome_view(latest_outcome));
                }
                assert((attempt_latest && value_matches) == (
                    attempt as nat > 0
                        && attempt as nat
                            == query_layer::d_started(durable, spec_request)
                        && query_layer::d_outcome(
                            durable, spec_request, attempt as nat,
                        ) == Option::Some(replay_layer::Observation::Success(
                            replay_layer::Value { id: value as nat },
                        ))
                ));
            }
            phase_armed && fields_match && attempt_latest && value_matches
        },
        Option::None => {
            proof {
                let spec_request = k_request_id(request);
                assert(!k_tracks_request(*kd, request as nat));
                assert(durable.phase[spec_request] == replay_layer::Phase::New);
            }
            false
        },
    }
}

pub fn k_guard_fail(
    kd: &KDurable,
    request: u64,
    attempt: u64,
    digest: u64,
    key_present: bool,
    key: u64,
    Ghost(durable): Ghost<replay_layer::DurableBroker>,
) -> (decision: bool)
    requires
        k_durable_inv(*kd, k_demo_config(), durable),
    ensures
        decision == query_layer::abstract_record_enabled(
            k_demo_config(),
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
    let fields_match = k_fields_match(request, digest, key_present, key);
    let lane = request % 4;
    let class_is_idempotent = lane == 1;
    match k_find_request(kd, request) {
        Option::Some(index) => {
            proof {
                k_demo_entry_attempt_bound(*kd, durable, index as int);
            }
            let entry = &kd.requests[index];
            proof {
                let spec_request = k_request_id(request);
                assert(k_lane_of(spec_request) == (request as nat) % 4);
                assert((request % 4) as nat == (request as nat) % 4);
                assert(k_demo_config().request_class[spec_request]
                    == k_class_of_lane(k_lane_of(spec_request)));
                assert(class_is_idempotent == (
                    k_demo_config().request_class[spec_request]
                        == replay_layer::RetryClass::Idempotent
                ));
            }
            let phase_armed = match entry.phase {
                KPhase::Armed => true,
                _ => false,
            };
            let attempt_latest = k_attempt_is_latest(
                entry, attempt, Ghost(durable),
            );
            let conclusive = k_failure_conclusive(
                entry,
                class_is_idempotent,
                Ghost(k_demo_config()),
                Ghost(durable),
            );
            proof {
                let spec_request = k_request_id(request);
                assert(k_request_entry_couples(*entry, durable));
                assert(k_phase_view(entry.phase) == durable.phase[spec_request]);
                k_phase_view_reflects(entry.phase, durable.phase[spec_request]);
                assert(phase_armed == (entry.phase == KPhase::Armed));
                assert(phase_armed == (
                    durable.phase[spec_request] == replay_layer::Phase::Armed
                ));
            }
            phase_armed && fields_match && attempt_latest && conclusive
        },
        Option::None => {
            proof {
                let spec_request = k_request_id(request);
                assert(!k_tracks_request(*kd, request as nat));
                assert(durable.phase[spec_request] == replay_layer::Phase::New);
            }
            false
        },
    }
}

pub fn k_unknown_enabled(
    entry: &KRequestEntry,
    attempt_present: bool,
    attempt: u64,
    reason: KUnknownReason,
    Ghost(durable): Ghost<replay_layer::DurableBroker>,
) -> (enabled: bool)
    requires
        k_request_entry_couples(*entry, durable),
        entry.outcomes@.len() <= 3,
    ensures
        enabled == query_layer::d_unknown_enabled(
            k_demo_config(),
            durable,
            k_request_id(entry.request),
            k_attempt_view(attempt_present, attempt),
            k_unknown_reason_view(reason),
        ),
{
    let lane = entry.request % 4;
    let class_is_idempotent = lane == 1;
    let class_is_uncontrolled = lane == 3;
    let max_attempts: usize = if lane == 3 { 1 } else { 3 };
    proof {
        let spec_request = k_request_id(entry.request);
        assert(k_lane_of(spec_request) == (entry.request as nat) % 4);
        assert((entry.request % 4) as nat == (entry.request as nat) % 4);
        assert(k_demo_config().request_class[spec_request]
            == k_class_of_lane(k_lane_of(spec_request)));
        assert(class_is_idempotent == (
            k_demo_config().request_class[spec_request]
                == replay_layer::RetryClass::Idempotent
        ));
        assert(class_is_uncontrolled == (
            k_demo_config().request_class[spec_request]
                == replay_layer::RetryClass::Uncontrolled
        ));
        assert(max_attempts as nat
            == k_demo_config().max_attempts[spec_request]);
    }
    let conclusive = k_failure_conclusive(
        entry,
        class_is_idempotent,
        Ghost(k_demo_config()),
        Ghost(durable),
    );
    let started = entry.outcomes.len();
    if !attempt_present {
        let enabled = match reason {
            KUnknownReason::Recovery => {
                started == 0 && class_is_uncontrolled && !conclusive
            },
            _ => false,
        };
        proof {
            let spec_request = k_request_id(entry.request);
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
                k_demo_config(),
                durable,
                spec_request,
                Option::None,
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
            let spec_request = k_request_id(entry.request);
            assert(k_attempt_view(true, attempt) == Option::Some(attempt as nat));
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
                k_demo_config(),
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
            started == max_attempts && uncertain
        },
        KUnknownReason::Recovery => class_is_uncontrolled && !conclusive,
        KUnknownReason::NonConclusiveFailure => {
            let latest = k_latest_outcome(entry);
            let failed = match latest {
                Option::Some(KObservation::Failure) => true,
                _ => false,
            };
            proof {
                let spec_request = k_request_id(entry.request);
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
                let spec_request = k_request_id(entry.request);
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
                let spec_request = k_request_id(entry.request);
                assert(attempt as nat == entry.outcomes@.len());
                assert(entry.outcomes@.len() > 0);
                assert(query_layer::d_outcome(
                    durable, spec_request, attempt as nat,
                ) == k_outcome_view(latest));
                if invalid {
                    match latest {
                        Option::Some(KObservation::InvalidResult { value }) => {
                            let bad = replay_layer::InvalidValue { id: value as nat };
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

pub fn k_guard_unknown(
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
        k_durable_inv(*kd, k_demo_config(), durable),
    ensures
        decision == query_layer::abstract_record_enabled(
            k_demo_config(),
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
    let fields_match = k_fields_match(request, digest, key_present, key);
    match k_find_request(kd, request) {
        Option::Some(index) => {
            proof {
                k_demo_entry_attempt_bound(*kd, durable, index as int);
            }
            let entry = &kd.requests[index];
            let phase_armed = match entry.phase {
                KPhase::Armed => true,
                _ => false,
            };
            let unknown_enabled = k_unknown_enabled(
                entry,
                attempt_present,
                attempt,
                reason,
                Ghost(durable),
            );
            proof {
                let spec_request = k_request_id(request);
                assert(k_request_entry_couples(*entry, durable));
                assert(k_phase_view(entry.phase) == durable.phase[spec_request]);
                k_phase_view_reflects(entry.phase, durable.phase[spec_request]);
                assert(phase_armed == (entry.phase == KPhase::Armed));
                assert(phase_armed == (
                    durable.phase[spec_request] == replay_layer::Phase::Armed
                ));
            }
            phase_armed && fields_match && unknown_enabled
        },
        Option::None => {
            proof {
                let spec_request = k_request_id(request);
                assert(!k_tracks_request(*kd, request as nat));
                assert(durable.phase[spec_request] == replay_layer::Phase::New);
            }
            false
        },
    }
}

} // verus!
