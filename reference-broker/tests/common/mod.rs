#![allow(dead_code)]

use std::path::PathBuf;
use std::sync::atomic::{AtomicU64, Ordering};

use proveai_reference_broker::{
    BrokerConfig, CapabilityId, CapabilitySpec, DedupKey, Digest, RequestSpec,
};

static NEXT_DIRECTORY: AtomicU64 = AtomicU64::new(1);

pub struct TestDirectory(PathBuf);

impl TestDirectory {
    pub fn new(label: &str) -> Self {
        let serial = NEXT_DIRECTORY.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!(
            "proveai-reference-broker-{label}-{}-{serial}",
            std::process::id()
        ));
        std::fs::create_dir(&path).expect("create test directory");
        Self(path)
    }

    pub fn wal(&self) -> PathBuf {
        self.0.join("broker.wal")
    }
}

impl Drop for TestDirectory {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

pub fn config(budget: u64) -> BrokerConfig {
    BrokerConfig {
        capabilities: vec![CapabilitySpec {
            id: CapabilityId(7),
            budget,
        }],
    }
}

pub const fn uncontrolled_spec() -> RequestSpec {
    RequestSpec::uncontrolled(Digest(101))
}

pub const fn idempotent_spec() -> RequestSpec {
    RequestSpec::idempotent(Digest(102))
}

pub const fn deduplicated_spec() -> RequestSpec {
    RequestSpec::deduplicated(Digest(103), DedupKey(9001))
}
