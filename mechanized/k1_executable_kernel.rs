use vstd::prelude::*;

#[path = "t1_durable_queries.rs"]
pub mod query_layer;

verus! {

use query_layer::c1_layer;
use c1_layer::replay_layer;

broadcast use {
    vstd::imap::group_imap_lemmas,
    vstd::iset::group_iset_lemmas,
};

// K1: Ring-0 of the executable broker kernel.
//
// This file contains executable (exec-mode) decision functions whose results
// are proved equal to the specification-level guards of the verified Broker
// theory.  The refinement anchor is Q1's reference-erased
// `abstract_record_enabled`: the executable guard that the mechanization
// proves is implied by full structural record legality.  A later kernel
// control layer maintains an executable durable state `KDurable` alongside a
// ghost `replay_layer::DurableBroker`; the coupling invariant `k_durable_inv`
// ties the two, and every Ring-0 function's postcondition speaks about the
// ghost state through that invariant.
//
// The demo configuration is a fixed specification constant: request ids are
// partitioned into four class lanes by `id % 4` (0 ReadOnly, 1 Idempotent,
// 2 Deduplicated, 3 Uncontrolled), each lane served by the capability with
// the lane's id.  Uncontrolled requests get a single attempt and unit
// budget; the other lanes get three attempts and budget four.
//
// K1 scope: types and views, the coupling invariant, the initial-state
// theorem, the Authorize guard, and the Start guard including the
// conclusive-failure scan.  K2 adds the remaining guards, accepted-record
// durable-summary mutations, and the replay-push coupling lemmas.

// ---------------------------------------------------------------------------
// Demo configuration (specification constant)
// ---------------------------------------------------------------------------

pub open spec fn k_lane_of(request: replay_layer::RequestId) -> nat {
    request.id % 4
}

pub open spec fn k_class_of_lane(lane: nat) -> replay_layer::RetryClass {
    if lane == 0 {
        replay_layer::RetryClass::ReadOnly
    } else if lane == 1 {
        replay_layer::RetryClass::Idempotent
    } else if lane == 2 {
        replay_layer::RetryClass::Deduplicated
    } else {
        replay_layer::RetryClass::Uncontrolled
    }
}

pub open spec fn k_demo_config() -> replay_layer::Config {
    replay_layer::Config {
        initial_budget: IMap::new(
            |_capability: replay_layer::CapabilityId| true,
            |capability: replay_layer::CapabilityId|
                if capability.id == 3 { 1nat } else { 4nat },
        ),
        request_capability: IMap::new(
            |_request: replay_layer::RequestId| true,
            |request: replay_layer::RequestId|
                replay_layer::CapabilityId { id: k_lane_of(request) },
        ),
        request_class: IMap::new(
            |_request: replay_layer::RequestId| true,
            |request: replay_layer::RequestId|
                k_class_of_lane(k_lane_of(request)),
        ),
        request_digest: IMap::new(
            |_request: replay_layer::RequestId| true,
            |request: replay_layer::RequestId|
                replay_layer::Digest { id: request.id },
        ),
        request_key: IMap::new(
            |_request: replay_layer::RequestId| true,
            |request: replay_layer::RequestId|
                if k_lane_of(request) == 2 {
                    Option::Some(replay_layer::StableKey { id: request.id })
                } else {
                    Option::<replay_layer::StableKey>::None
                },
        ),
        request_namespace: IMap::new(
            |_request: replay_layer::RequestId| true,
            |_request: replay_layer::RequestId|
                replay_layer::AdapterNamespace { id: 0 },
        ),
        max_attempts: IMap::new(
            |_request: replay_layer::RequestId| true,
            |request: replay_layer::RequestId|
                if k_lane_of(request) == 3 { 1nat } else { 3nat },
        ),
        matches: ISet::new(
            |pair: (replay_layer::RequestId, replay_layer::CapabilityId)|
                pair.1.id == k_lane_of(pair.0),
        ),
        valid_results: ISet::new(
            |_pair: (replay_layer::RequestId, replay_layer::Value)| true,
        ),
    }
}

pub proof fn k_demo_class_is_deduplicated(
    request: replay_layer::RequestId,
)
    ensures
        k_demo_config().request_class[request]
                == replay_layer::RetryClass::Deduplicated
            <==> k_lane_of(request) == 2,
{
    assert(k_lane_of(request) < 4);
}

pub proof fn k_demo_config_is_well_formed()
    ensures
        replay_layer::config_wf(k_demo_config()),
{
    let cfg = k_demo_config();
    assert(cfg.initial_budget.dom()
        == ISet::<replay_layer::CapabilityId>::full());
    assert(cfg.request_capability.dom()
        == ISet::<replay_layer::RequestId>::full());
    assert(cfg.request_class.dom()
        == ISet::<replay_layer::RequestId>::full());
    assert(cfg.request_digest.dom()
        == ISet::<replay_layer::RequestId>::full());
    assert(cfg.request_key.dom()
        == ISet::<replay_layer::RequestId>::full());
    assert(cfg.request_namespace.dom()
        == ISet::<replay_layer::RequestId>::full());
    assert(cfg.max_attempts.dom()
        == ISet::<replay_layer::RequestId>::full());
    assert forall|request: replay_layer::RequestId|
        #[trigger] cfg.max_attempts[request] > 0 by {
    }
    assert forall|request: replay_layer::RequestId|
        (#[trigger] cfg.request_class[request]
                == replay_layer::RetryClass::Deduplicated
            <==> k_lane_of(request) == 2) by {
        k_demo_class_is_deduplicated(request);
    }
    assert forall|request: replay_layer::RequestId|
        (#[trigger] cfg.request_class[request]
                == replay_layer::RetryClass::Deduplicated
            <==> cfg.request_key[request].is_some()) by {
        k_demo_class_is_deduplicated(request);
        assert(k_lane_of(request) < 4);
    }
    assert forall|left: replay_layer::RequestId,
                  right: replay_layer::RequestId| #![auto]
        cfg.request_class[left] == replay_layer::RetryClass::Deduplicated
            && cfg.request_class[right]
                == replay_layer::RetryClass::Deduplicated
            && cfg.request_namespace[left] == cfg.request_namespace[right]
            && cfg.request_key[left] == cfg.request_key[right]
            ==> left == right by {
        if cfg.request_class[left]
                == replay_layer::RetryClass::Deduplicated
            && cfg.request_class[right]
                == replay_layer::RetryClass::Deduplicated
            && cfg.request_namespace[left] == cfg.request_namespace[right]
            && cfg.request_key[left] == cfg.request_key[right]
        {
            k_demo_class_is_deduplicated(left);
            k_demo_class_is_deduplicated(right);
            assert(k_lane_of(left) == 2);
            assert(k_lane_of(right) == 2);
            assert(cfg.request_key[left]
                == Option::Some(replay_layer::StableKey { id: left.id }));
            assert(cfg.request_key[right]
                == Option::Some(replay_layer::StableKey { id: right.id }));
        }
    }
}

// ---------------------------------------------------------------------------
// Executable mirrors of the specification types
// ---------------------------------------------------------------------------

pub open spec fn k_request_id(id: u64) -> replay_layer::RequestId {
    replay_layer::RequestId { id: id as nat }
}

pub open spec fn k_capability_id(id: u64) -> replay_layer::CapabilityId {
    replay_layer::CapabilityId { id: id as nat }
}

pub open spec fn k_digest_id(id: u64) -> replay_layer::Digest {
    replay_layer::Digest { id: id as nat }
}

#[derive(PartialEq, Eq, Clone, Copy)]
pub enum KPhase {
    New,
    Authorized,
    Prepared,
    Armed,
    Committed,
    Failed,
    Unknown,
}

pub open spec fn k_phase_view(phase: KPhase) -> replay_layer::Phase {
    match phase {
        KPhase::New => replay_layer::Phase::New,
        KPhase::Authorized => replay_layer::Phase::Authorized,
        KPhase::Prepared => replay_layer::Phase::Prepared,
        KPhase::Armed => replay_layer::Phase::Armed,
        KPhase::Committed => replay_layer::Phase::Committed,
        KPhase::Failed => replay_layer::Phase::Failed,
        KPhase::Unknown => replay_layer::Phase::Unknown,
    }
}

#[derive(PartialEq, Eq, Clone, Copy)]
pub enum KObservation {
    Success { value: u64 },
    Failure,
    Ambiguous,
    InvalidResult { value: u64 },
}

pub open spec fn k_observation_view(
    observation: KObservation,
) -> replay_layer::Observation {
    match observation {
        KObservation::Success { value } => replay_layer::Observation::Success(
            replay_layer::Value { id: value as nat },
        ),
        KObservation::Failure => replay_layer::Observation::Failure,
        KObservation::Ambiguous => replay_layer::Observation::Ambiguous,
        KObservation::InvalidResult { value } =>
            replay_layer::Observation::InvalidResult(
                replay_layer::InvalidValue { id: value as nat },
            ),
    }
}

pub open spec fn k_outcome_view(
    outcome: Option<KObservation>,
) -> Option<replay_layer::Observation> {
    match outcome {
        Option::Some(observation) =>
            Option::Some(k_observation_view(observation)),
        Option::None => Option::None,
    }
}

// Per-request executable durable summary.  `outcomes[a - 1]` is the durable
// outcome of attempt `a`; the number of started attempts is `outcomes.len()`.
pub struct KRequestEntry {
    pub request: u64,
    pub phase: KPhase,
    pub witness: Option<u64>,
    pub outcomes: Vec<Option<KObservation>>,
}

pub struct KCapEntry {
    pub capability: u64,
    pub remaining: u64,
    pub revoked: bool,
}

pub struct KDurable {
    pub requests: Vec<KRequestEntry>,
    pub caps: Vec<KCapEntry>,
}

// ---------------------------------------------------------------------------
// Coupling invariant between KDurable and the ghost DurableBroker
// ---------------------------------------------------------------------------

pub open spec fn k_tracks_request(kd: KDurable, id: nat) -> bool {
    exists|index: int| 0 <= index < kd.requests@.len()
        && #[trigger] kd.requests@[index].request as nat == id
}

pub open spec fn k_tracks_capability(kd: KDurable, id: nat) -> bool {
    exists|index: int| 0 <= index < kd.caps@.len()
        && #[trigger] kd.caps@[index].capability as nat == id
}

pub open spec fn k_request_entry_couples(
    entry: KRequestEntry,
    durable: replay_layer::DurableBroker,
) -> bool {
    let request = k_request_id(entry.request);
    &&& durable.phase[request] == k_phase_view(entry.phase)
    &&& durable.witness[request] == match entry.witness {
        Option::Some(capability) =>
            Option::Some(k_capability_id(capability)),
        Option::None => Option::None,
    }
    &&& query_layer::d_started(durable, request) == entry.outcomes@.len()
    &&& forall|attempt: replay_layer::AttemptId|
        1 <= attempt && attempt <= entry.outcomes@.len() ==>
            #[trigger] query_layer::d_outcome(durable, request, attempt)
                == k_outcome_view(entry.outcomes@[attempt - 1])
}

pub open spec fn k_durable_inv(
    kd: KDurable,
    cfg: replay_layer::Config,
    durable: replay_layer::DurableBroker,
) -> bool {
    // Tracked request entries are unique and coupled.
    &&& forall|left: int, right: int|
        0 <= left < kd.requests@.len() && 0 <= right < kd.requests@.len()
            && #[trigger] kd.requests@[left].request
                == #[trigger] kd.requests@[right].request
            ==> left == right
    &&& forall|index: int| 0 <= index < kd.requests@.len() ==> {
        let entry = #[trigger] kd.requests@[index];
        &&& k_request_entry_couples(entry, durable)
        &&& entry.outcomes@.len()
            <= cfg.max_attempts[k_request_id(entry.request)]
    }
    // Untracked requests carry the initial durable defaults.
    &&& forall|id: nat| !k_tracks_request(kd, id) ==> {
        &&& #[trigger] durable.phase[replay_layer::RequestId { id }]
            == replay_layer::Phase::New
        &&& durable.witness[replay_layer::RequestId { id }]
            == Option::<replay_layer::CapabilityId>::None
        &&& query_layer::d_started(
            durable, replay_layer::RequestId { id },
        ) == 0
    }
    // Tracked capability entries are unique and coupled.
    &&& forall|left: int, right: int|
        0 <= left < kd.caps@.len() && 0 <= right < kd.caps@.len()
            && #[trigger] kd.caps@[left].capability
                == #[trigger] kd.caps@[right].capability
            ==> left == right
    &&& forall|index: int| 0 <= index < kd.caps@.len() ==> {
        let entry = #[trigger] kd.caps@[index];
        &&& durable.remaining[k_capability_id(entry.capability)]
            == entry.remaining as nat
        &&& durable.revoked.contains(k_capability_id(entry.capability))
            == entry.revoked
    }
    // Untracked capabilities carry the configured budget, unrevoked.
    &&& forall|id: nat| !k_tracks_capability(kd, id) ==> {
        &&& #[trigger] durable.remaining[replay_layer::CapabilityId { id }]
            == cfg.initial_budget[replay_layer::CapabilityId { id }]
        &&& !durable.revoked.contains(replay_layer::CapabilityId { id })
    }
}

// ---------------------------------------------------------------------------
// Initial state
// ---------------------------------------------------------------------------

pub fn k_initial() -> (kd: KDurable)
    ensures
        kd.requests@.len() == 0,
        kd.caps@.len() == 0,
{
    KDurable { requests: Vec::new(), caps: Vec::new() }
}

pub proof fn k_initial_satisfies_inv(kd: KDurable, cfg: replay_layer::Config)
    requires
        kd.requests@.len() == 0,
        kd.caps@.len() == 0,
    ensures
        k_durable_inv(kd, cfg, replay_layer::initial_durable(cfg)),
{
    let durable = replay_layer::initial_durable(cfg);
    assert forall|id: nat| !k_tracks_request(kd, id) implies {
        &&& durable.phase[replay_layer::RequestId { id }]
            == replay_layer::Phase::New
        &&& durable.witness[replay_layer::RequestId { id }]
            == Option::<replay_layer::CapabilityId>::None
        &&& query_layer::d_started(
            durable, replay_layer::RequestId { id },
        ) == 0
    } by {
        assert(durable.attempt_log =~= Seq::<replay_layer::AttemptEntry>::empty());
        reveal_with_fuel(query_layer::attempt_log_started, 2);
    }
}

// ---------------------------------------------------------------------------
// Executable lookups
// ---------------------------------------------------------------------------

pub fn k_find_request(kd: &KDurable, request: u64) -> (found: Option<usize>)
    ensures
        match found {
            Option::Some(index) => {
                &&& index < kd.requests@.len()
                &&& kd.requests@[index as int].request == request
            },
            Option::None => forall|index: int|
                0 <= index < kd.requests@.len() ==>
                    #[trigger] kd.requests@[index].request != request,
        },
{
    let mut index: usize = 0;
    while index < kd.requests.len()
        invariant
            index <= kd.requests@.len(),
            forall|scanned: int| 0 <= scanned < index ==>
                #[trigger] kd.requests@[scanned].request != request,
        decreases kd.requests@.len() - index,
    {
        if kd.requests[index].request == request {
            return Option::Some(index);
        }
        index = index + 1;
    }
    Option::None
}

pub fn k_find_capability(kd: &KDurable, capability: u64) -> (found: Option<usize>)
    ensures
        match found {
            Option::Some(index) => {
                &&& index < kd.caps@.len()
                &&& kd.caps@[index as int].capability == capability
            },
            Option::None => forall|index: int|
                0 <= index < kd.caps@.len() ==>
                    #[trigger] kd.caps@[index].capability != capability,
        },
{
    let mut index: usize = 0;
    while index < kd.caps.len()
        invariant
            index <= kd.caps@.len(),
            forall|scanned: int| 0 <= scanned < index ==>
                #[trigger] kd.caps@[scanned].capability != capability,
        decreases kd.caps@.len() - index,
    {
        if kd.caps[index].capability == capability {
            return Option::Some(index);
        }
        index = index + 1;
    }
    Option::None
}

// ---------------------------------------------------------------------------
// The Authorize guard
// ---------------------------------------------------------------------------

// Executable authorize decision, proved equal to Q1's reference-erased
// record guard for the demo configuration.  The ghost `durable` is the replay
// of the current journal; callers supply it and K2 preserves the coupling
// across accepted durable-summary mutations.
pub fn k_guard_authorize(
    kd: &KDurable,
    request: u64,
    capability: u64,
    digest: u64,
    Ghost(durable): Ghost<replay_layer::DurableBroker>,
) -> (decision: bool)
    requires
        k_durable_inv(*kd, k_demo_config(), durable),
    ensures
        decision == query_layer::abstract_record_enabled(
            k_demo_config(),
            durable,
            replay_layer::JournalRecord::Authorize {
                request: k_request_id(request),
                capability: k_capability_id(capability),
                digest: k_digest_id(digest),
            },
        ),
{
    let ghost cfg = k_demo_config();
    let ghost spec_request = k_request_id(request);

    // Phase must be New.
    let phase_new: bool = match k_find_request(kd, request) {
        Option::Some(index) => {
            let entry_phase = kd.requests[index].phase;
            proof {
                assert(k_request_entry_couples(
                    kd.requests@[index as int], durable,
                ));
            }
            match entry_phase {
                KPhase::New => true,
                _ => false,
            }
        },
        Option::None => {
            proof {
                assert(!k_tracks_request(*kd, request as nat));
                assert(durable.phase[spec_request]
                    == replay_layer::Phase::New);
            }
            true
        },
    };
    proof {
        assert(phase_new
            == (durable.phase[spec_request] == replay_layer::Phase::New));
    }

    // Capability identity and scope: in the demo configuration the
    // configured capability of a request is its lane, and `matches`
    // holds exactly for that pair.
    let lane: u64 = request % 4;
    let capability_matches: bool = capability == lane;
    proof {
        assert(cfg.request_capability[spec_request]
            == replay_layer::CapabilityId { id: k_lane_of(spec_request) });
        assert(k_lane_of(spec_request) == (request as nat) % 4);
        assert((request % 4) as nat == (request as nat) % 4);
        assert(capability_matches
            == (k_capability_id(capability)
                == cfg.request_capability[spec_request]));
        assert(cfg.matches.contains((
            spec_request, k_capability_id(capability),
        )) == (k_capability_id(capability).id == k_lane_of(spec_request)));
    }

    // Revocation and budget.
    let mut unrevoked: bool;
    let mut budget_positive: bool;
    match k_find_capability(kd, capability) {
        Option::Some(index) => {
            unrevoked = !kd.caps[index].revoked;
            budget_positive = kd.caps[index].remaining > 0;
            proof {
                let entry = kd.caps@[index as int];
                assert(durable.remaining[k_capability_id(entry.capability)]
                    == entry.remaining as nat);
                assert(durable.revoked.contains(
                    k_capability_id(entry.capability),
                ) == entry.revoked);
            }
        },
        Option::None => {
            proof {
                assert(!k_tracks_capability(*kd, capability as nat));
            }
            unrevoked = true;
            let ghost spec_capability = k_capability_id(capability);
            let budget_by_lane: u64 = if capability == 3 { 1 } else { 4 };
            proof {
                assert(durable.remaining[spec_capability]
                    == cfg.initial_budget[spec_capability]);
                assert(cfg.initial_budget[spec_capability]
                    == if spec_capability.id == 3 { 1nat } else { 4nat });
            }
            budget_positive = budget_by_lane > 0;
        },
    }
    proof {
        assert(unrevoked == !durable.revoked.contains(
            k_capability_id(capability),
        ));
        assert(budget_positive
            == (durable.remaining[k_capability_id(capability)] > 0));
    }

    // Digest binding: the demo digest of a request is its own id.
    let digest_matches: bool = digest == request;
    proof {
        assert(cfg.request_digest[spec_request]
            == replay_layer::Digest { id: spec_request.id });
        assert(digest_matches
            == (k_digest_id(digest) == cfg.request_digest[spec_request]));
    }

    phase_new && capability_matches && unrevoked
        && budget_positive && digest_matches
}

// ---------------------------------------------------------------------------
// The Start guard, including the conclusive-failure scan
// ---------------------------------------------------------------------------

// Every started attempt of the entry has a durable Failure outcome.
pub fn k_all_outcomes_failed(entry: &KRequestEntry) -> (all_failed: bool)
    ensures
        all_failed == forall|attempt: int|
            0 <= attempt < entry.outcomes@.len() ==>
                k_outcome_view(#[trigger] entry.outcomes@[attempt])
                    == Option::Some(replay_layer::Observation::Failure),
{
    let mut index: usize = 0;
    while index < entry.outcomes.len()
        invariant
            index <= entry.outcomes@.len(),
            forall|scanned: int| 0 <= scanned < index ==>
                k_outcome_view(#[trigger] entry.outcomes@[scanned])
                    == Option::Some(replay_layer::Observation::Failure),
        decreases entry.outcomes@.len() - index,
    {
        let failed = match entry.outcomes[index] {
            Option::Some(KObservation::Failure) => true,
            _ => false,
        };
        if !failed {
            proof {
                assert(k_outcome_view(entry.outcomes@[index as int])
                    != Option::Some(replay_layer::Observation::Failure));
            }
            return false;
        }
        index = index + 1;
    }
    true
}

// Evidence queries shared by the executable guards.  A Success remains
// durable even when its terminal record has not yet been appended.
pub open spec fn k_has_durable_success(entry: KRequestEntry) -> bool {
    exists|index: int| 0 <= index < entry.outcomes@.len()
        && match #[trigger] entry.outcomes@[index] {
            Option::Some(KObservation::Success { .. }) => true,
            Option::None
            | Option::Some(KObservation::Failure)
            | Option::Some(KObservation::Ambiguous)
            | Option::Some(KObservation::InvalidResult { .. }) => false,
        }
}

pub fn k_has_durable_success_exec(entry: &KRequestEntry) -> (has_success: bool)
    ensures has_success == k_has_durable_success(*entry),
{
    let mut index: usize = 0;
    while index < entry.outcomes.len()
        invariant
            index <= entry.outcomes@.len(),
            forall|scanned: int| 0 <= scanned < index ==>
                match #[trigger] entry.outcomes@[scanned] {
                    Option::Some(KObservation::Success { .. }) => false,
                    Option::None
                    | Option::Some(KObservation::Failure)
                    | Option::Some(KObservation::Ambiguous)
                    | Option::Some(KObservation::InvalidResult { .. }) => true,
                },
        decreases entry.outcomes@.len() - index,
    {
        if matches!(entry.outcomes[index], Option::Some(KObservation::Success { .. })) {
            proof {
                assert(exists|witness: int| 0 <= witness < entry.outcomes@.len()
                    && match #[trigger] entry.outcomes@[witness] {
                        Option::Some(KObservation::Success { .. }) => true,
                        Option::None
                        | Option::Some(KObservation::Failure)
                        | Option::Some(KObservation::Ambiguous)
                        | Option::Some(KObservation::InvalidResult { .. }) => false,
                    }) by {
                    let witness = index as int;
                }
            }
            return true;
        }
        index = index + 1;
    }
    false
}

pub proof fn k_has_durable_success_couples(
    entry: KRequestEntry,
    durable: replay_layer::DurableBroker,
)
    requires k_request_entry_couples(entry, durable),
    ensures k_has_durable_success(entry)
        == query_layer::d_has_durable_success(
            durable, k_request_id(entry.request),
        ),
{
    let request = k_request_id(entry.request);
    if k_has_durable_success(entry) {
        let index = choose|index: int|
            0 <= index < entry.outcomes@.len()
                && match #[trigger] entry.outcomes@[index] {
                    Option::Some(KObservation::Success { .. }) => true,
                    Option::None
                    | Option::Some(KObservation::Failure)
                    | Option::Some(KObservation::Ambiguous)
                    | Option::Some(KObservation::InvalidResult { .. }) => false,
                };
        let attempt = (index + 1) as nat;
        assert(1 <= attempt && attempt <= query_layer::d_started(durable, request));
        assert(query_layer::d_outcome(durable, request, attempt)
            == k_outcome_view(entry.outcomes@[index]));
        assert(k_outcome_view(entry.outcomes@[index])
            == Option::Some(replay_layer::Observation::Success(
                replay_layer::Value { id: 0nat },
            )) || k_outcome_view(entry.outcomes@[index]).is_some());
        assert(query_layer::d_has_durable_success(durable, request));
    }
    if query_layer::d_has_durable_success(durable, request) {
        let attempt = choose|attempt: replay_layer::AttemptId|
            exists|value: replay_layer::Value| #![auto]
                1 <= attempt && attempt <= query_layer::d_started(durable, request)
                    && #[trigger] query_layer::d_outcome(durable, request, attempt)
                        == Option::Some(replay_layer::Observation::Success(value));
        assert(1 <= attempt && attempt <= entry.outcomes@.len());
        let index = (attempt - 1) as int;
        assert(query_layer::d_outcome(durable, request, attempt)
            == k_outcome_view(entry.outcomes@[index]));
        match entry.outcomes@[index] {
            Option::Some(KObservation::Success { .. }) => {},
            Option::None
            | Option::Some(KObservation::Failure)
            | Option::Some(KObservation::Ambiguous)
            | Option::Some(KObservation::InvalidResult { .. }) => {
                assert(false);
            },
        }
        assert(k_has_durable_success(entry));
    }
}

// Executable mirror of Q1's `d_failure_conclusive` for a tracked entry.
pub fn k_failure_conclusive(
    entry: &KRequestEntry,
    class_is_idempotent: bool,
    Ghost(cfg): Ghost<replay_layer::Config>,
    Ghost(durable): Ghost<replay_layer::DurableBroker>,
) -> (conclusive: bool)
    requires
        k_request_entry_couples(*entry, durable),
        class_is_idempotent == (
            cfg.request_class[k_request_id(entry.request)]
                == replay_layer::RetryClass::Idempotent
        ),
    ensures
        conclusive == query_layer::d_failure_conclusive(
            cfg, durable, k_request_id(entry.request),
        ),
{
    let ghost spec_request = k_request_id(entry.request);
    let started = entry.outcomes.len();
    if started == 0 {
        return false;
    }
    let last_failed = match entry.outcomes[started - 1] {
        Option::Some(KObservation::Failure) => true,
        _ => false,
    };
    proof {
        assert(query_layer::d_started(durable, spec_request)
            == entry.outcomes@.len());
        assert(query_layer::d_outcome(
            durable, spec_request, entry.outcomes@.len() as nat,
        ) == k_outcome_view(entry.outcomes@[entry.outcomes@.len() - 1]));
        assert(last_failed == (
            query_layer::d_outcome(
                durable, spec_request,
                query_layer::d_started(durable, spec_request),
            ) == Option::Some(replay_layer::Observation::Failure)
        ));
    }
    if !last_failed {
        return false;
    }
    if !class_is_idempotent {
        return true;
    }
    let all_failed = k_all_outcomes_failed(entry);
    proof {
        if all_failed {
            assert forall|attempt: replay_layer::AttemptId|
                1 <= attempt
                    && attempt <= query_layer::d_started(
                        durable, spec_request,
                    ) implies
                #[trigger] query_layer::d_outcome(
                    durable, spec_request, attempt,
                ) == Option::Some(replay_layer::Observation::Failure) by {
                assert(query_layer::d_outcome(durable, spec_request, attempt)
                    == k_outcome_view(entry.outcomes@[attempt - 1]));
            }
            assert(query_layer::d_all_failed(durable, spec_request));
        } else {
            let bad = choose|attempt: int|
                0 <= attempt < entry.outcomes@.len()
                    && k_outcome_view(#[trigger] entry.outcomes@[attempt])
                        != Option::Some(replay_layer::Observation::Failure);
            assert(query_layer::d_outcome(
                durable, spec_request, (bad + 1) as nat,
            ) == k_outcome_view(entry.outcomes@[bad]));
            assert(!query_layer::d_all_failed(durable, spec_request));
        }
    }
    all_failed
}

// Executable Start-record guard, proved equal to Q1's reference-erased
// guard for the demo configuration.
pub fn k_guard_start(
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
        attempt < 0xffff_ffff_ffff_ffff,
    ensures
        decision == query_layer::abstract_record_enabled(
            k_demo_config(),
            durable,
            replay_layer::JournalRecord::Start {
                request: k_request_id(request),
                attempt: attempt as nat,
                digest: k_digest_id(digest),
                key: if key_present {
                    Option::Some(replay_layer::StableKey { id: key as nat })
                } else {
                    Option::None
                },
                arm_ref: 0,
            },
        ),
{
    let ghost cfg = k_demo_config();
    let ghost spec_request = k_request_id(request);
    let ghost spec_key: Option<replay_layer::StableKey> = if key_present {
        Option::Some(replay_layer::StableKey { id: key as nat })
    } else {
        Option::None
    };

    let lane: u64 = request % 4;
    proof {
        assert(k_lane_of(spec_request) == (request as nat) % 4);
        assert((request % 4) as nat == (request as nat) % 4);
    }

    // Field binding for the demo configuration.
    let digest_matches: bool = digest == request;
    let key_matches: bool = if lane == 2 {
        key_present && key == request
    } else {
        !key_present
    };
    proof {
        assert(cfg.request_digest[spec_request]
            == replay_layer::Digest { id: spec_request.id });
        assert(cfg.request_key[spec_request] == if k_lane_of(spec_request) == 2 {
            Option::Some(replay_layer::StableKey { id: spec_request.id })
        } else {
            Option::<replay_layer::StableKey>::None
        });
        assert((digest_matches && key_matches)
            == replay_layer::request_fields_match(
                cfg, spec_request, k_digest_id(digest), spec_key,
            ));
    }

    // Class and attempt limits for the demo configuration.
    let class_is_idempotent: bool = lane == 1;
    let class_is_uncontrolled: bool = lane == 3;
    let max_attempts: u64 = if lane == 3 { 1 } else { 3 };
    proof {
        assert(cfg.request_class[spec_request]
            == k_class_of_lane(k_lane_of(spec_request)));
        assert(class_is_idempotent == (
            cfg.request_class[spec_request]
                == replay_layer::RetryClass::Idempotent
        ));
        assert(class_is_uncontrolled == (
            cfg.request_class[spec_request]
                == replay_layer::RetryClass::Uncontrolled
        ));
        assert(max_attempts as nat == cfg.max_attempts[spec_request]);
    }

    match k_find_request(kd, request) {
        Option::Some(index) => {
            let entry = &kd.requests[index];
            proof {
                assert(k_request_entry_couples(
                    kd.requests@[index as int], durable,
                ));
            }
            let phase_armed = match entry.phase {
                KPhase::Armed => true,
                _ => false,
            };
            let started = entry.outcomes.len();
            let attempt_is_next: bool = if started == 0 {
                attempt == 1
            } else if started == 1 {
                attempt == 2
            } else if started == 2 {
                attempt == 3
            } else {
                false
            };
            let within_limit: bool = attempt <= max_attempts;
            proof {
                assert(query_layer::d_started(durable, spec_request)
                    == entry.outcomes@.len());
                assert((attempt_is_next && within_limit) == (
                    attempt as nat
                        == query_layer::d_started(durable, spec_request) + 1
                    && attempt as nat <= cfg.max_attempts[spec_request]
                ));
            }
            let not_conclusive: bool = !k_failure_conclusive(
                entry,
                class_is_idempotent,
                Ghost(cfg),
                Ghost(durable),
            );
            let has_success = k_has_durable_success_exec(entry);
            let latest_failed = if started == 0 {
                false
            } else {
                match entry.outcomes[started - 1] {
                    Option::Some(KObservation::Failure) => true,
                    _ => false,
                }
            };
            let uncontrolled_fresh: bool =
                !class_is_uncontrolled || started == 0;
            proof {
                assert(uncontrolled_fresh == (
                    cfg.request_class[spec_request]
                        == replay_layer::RetryClass::Uncontrolled
                    ==> query_layer::d_started(durable, spec_request) == 0
                ));
                k_has_durable_success_couples(*entry, durable);
                assert(has_success == query_layer::d_has_durable_success(
                    durable, spec_request,
                ));
                assert(latest_failed == (
                    started > 0
                        && query_layer::d_outcome(
                            durable, spec_request,
                            query_layer::d_started(durable, spec_request),
                        ) == Option::Some(replay_layer::Observation::Failure)
                ));
            }
            phase_armed && digest_matches && key_matches && attempt_is_next
                && within_limit && not_conclusive && uncontrolled_fresh
                && !has_success && !latest_failed
        },
        Option::None => {
            // Untracked requests are in phase New, so Start is disabled.
            proof {
                assert(!k_tracks_request(*kd, request as nat));
                assert(durable.phase[spec_request]
                    == replay_layer::Phase::New);
            }
            false
        },
    }
}

} // verus!
