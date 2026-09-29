//! Minimal executable broker for the ProveAI protocol.
//!
//! This crate is a standard-Rust reference implementation. It mirrors the
//! verified K1-K3 record vocabulary, but is not itself verified. See the crate
//! README for the exact trusted and unverified boundaries.

pub mod adapter;
pub mod adapters;
pub mod broker;
pub mod evaluation;
pub mod fault;
pub mod model;
pub mod wal;

pub use adapter::{Adapter, Delivery};
pub use broker::{
    AdmissionBinding, AppendGate, Broker, BrokerConfig, BrokerError, CapabilitySpec, GateError,
};
pub use fault::{CrashPlan, CrashSite};
pub use model::{
    CapabilityId, DedupKey, Digest, Invocation, InvocationId, JournalRecord, Observation, Phase,
    RecoveryDecision, RequestId, RequestSpec, RetryClass, TerminalResult, UnknownReason, Value,
};
