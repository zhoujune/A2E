use std::collections::{BTreeMap, VecDeque};

use crate::adapter::{Adapter, Delivery};
use crate::model::{DedupKey, Invocation, Observation, RetryClass, Value};

#[derive(Debug, Default)]
pub struct DeduplicatedAdapter {
    decisions: BTreeMap<DedupKey, Value>,
    invocations: u64,
    mutations: u64,
    deliveries: VecDeque<Observation>,
}

impl DeduplicatedAdapter {
    #[must_use]
    pub fn scripted(deliveries: impl IntoIterator<Item = Observation>) -> Self {
        Self {
            decisions: BTreeMap::new(),
            invocations: 0,
            mutations: 0,
            deliveries: deliveries.into_iter().collect(),
        }
    }

    #[must_use]
    pub const fn mutation_count(&self) -> u64 {
        self.mutations
    }

    #[must_use]
    pub const fn invocation_count(&self) -> u64 {
        self.invocations
    }

    #[must_use]
    pub fn decision(&self, key: DedupKey) -> Option<Value> {
        self.decisions.get(&key).copied()
    }
}

impl Adapter for DeduplicatedAdapter {
    fn retry_class(&self) -> RetryClass {
        RetryClass::Deduplicated
    }

    fn invoke(&mut self, invocation: Invocation) -> Delivery {
        self.invocations = self.invocations.saturating_add(1);
        let key = invocation
            .key
            .expect("broker validates deduplicated invocations have a key");
        let value = if let Some(value) = self.decisions.get(&key) {
            *value
        } else {
            self.mutations = self.mutations.saturating_add(1);
            let value = Value(self.mutations);
            self.decisions.insert(key, value);
            value
        };
        let observation = match self.deliveries.pop_front() {
            Some(Observation::Success(_)) | None => Observation::Success(value),
            Some(other) => other,
        };
        Delivery {
            invocation: invocation.id,
            observation,
        }
    }
}
