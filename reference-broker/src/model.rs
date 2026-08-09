use std::fmt;

macro_rules! id_type {
    ($name:ident) => {
        #[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
        pub struct $name(pub u64);

        impl fmt::Display for $name {
            fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
                self.0.fmt(formatter)
            }
        }
    };
}

id_type!(RequestId);
id_type!(CapabilityId);
id_type!(Digest);
id_type!(DedupKey);
id_type!(InvocationId);
id_type!(Value);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RetryClass {
    ReadOnly,
    Idempotent,
    Deduplicated,
    Uncontrolled,
}

impl RetryClass {
    #[must_use]
    pub const fn max_attempts(self) -> u64 {
        match self {
            Self::Uncontrolled | Self::ReadOnly => 1,
            Self::Idempotent | Self::Deduplicated => 3,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Observation {
    Success(Value),
    Failure,
    Ambiguous,
    InvalidResult(Value),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum UnknownReason {
    Exhausted,
    Recovery,
    NonConclusiveFailure,
    AmbiguousOutcome,
    InvalidResult,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Phase {
    New,
    Authorized,
    Prepared,
    Armed,
    Committed,
    Failed,
    Unknown,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RequestSpec {
    pub digest: Digest,
    pub class: RetryClass,
    pub key: Option<DedupKey>,
}

impl RequestSpec {
    #[must_use]
    pub const fn uncontrolled(digest: Digest) -> Self {
        Self {
            digest,
            class: RetryClass::Uncontrolled,
            key: None,
        }
    }

    #[must_use]
    pub const fn idempotent(digest: Digest) -> Self {
        Self {
            digest,
            class: RetryClass::Idempotent,
            key: None,
        }
    }

    #[must_use]
    pub const fn deduplicated(digest: Digest, key: DedupKey) -> Self {
        Self {
            digest,
            class: RetryClass::Deduplicated,
            key: Some(key),
        }
    }

    #[must_use]
    pub const fn has_valid_key_shape(self) -> bool {
        matches!(self.class, RetryClass::Deduplicated) == self.key.is_some()
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Invocation {
    pub id: InvocationId,
    pub request: RequestId,
    pub attempt: u64,
    pub digest: Digest,
    pub key: Option<DedupKey>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TerminalResult {
    Committed {
        attempt: u64,
        value: Value,
    },
    Failed {
        attempt: u64,
    },
    Unknown {
        attempt: Option<u64>,
        reason: UnknownReason,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum JournalRecord {
    Authorize {
        request: RequestId,
        capability: CapabilityId,
        digest: Digest,
    },
    Revoke {
        capability: CapabilityId,
    },
    Prepare {
        request: RequestId,
        class: RetryClass,
        digest: Digest,
        key: Option<DedupKey>,
        auth_ref: u64,
    },
    Arm {
        request: RequestId,
        digest: Digest,
        key: Option<DedupKey>,
        prepare_ref: u64,
    },
    Start {
        request: RequestId,
        attempt: u64,
        digest: Digest,
        key: Option<DedupKey>,
        arm_ref: u64,
    },
    Outcome {
        request: RequestId,
        attempt: u64,
        observation: Observation,
        digest: Digest,
        key: Option<DedupKey>,
        start_ref: u64,
    },
    Commit {
        request: RequestId,
        attempt: u64,
        value: Value,
        digest: Digest,
        key: Option<DedupKey>,
        outcome_ref: u64,
    },
    Fail {
        request: RequestId,
        attempt: u64,
        digest: Digest,
        key: Option<DedupKey>,
        outcome_ref: u64,
    },
    Unknown {
        request: RequestId,
        attempt: Option<u64>,
        reason: UnknownReason,
        digest: Digest,
        key: Option<DedupKey>,
        evidence_ref: u64,
    },
}
