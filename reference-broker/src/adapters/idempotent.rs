use std::collections::VecDeque;

use crate::adapter::{Adapter, Delivery};
use crate::model::{Invocation, Observation, RetryClass, Value};

#[derive(Debug, Default)]
pub struct IdempotentAdapter {
    applied: bool,
    invocations: u64,
    mutations: u64,
    deliveries: VecDeque<Observation>,
}

impl IdempotentAdapter {
    #[must_use]
    pub fn scripted(deliveries: impl IntoIterator<Item = Observation>) -> Self {
        Self {
            applied: false,
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
}

impl Adapter for IdempotentAdapter {
    fn retry_class(&self) -> RetryClass {
        RetryClass::Idempotent
    }

    fn invoke(&mut self, invocation: Invocation) -> Delivery {
        self.invocations = self.invocations.saturating_add(1);
        if !self.applied {
            self.applied = true;
            self.mutations = self.mutations.saturating_add(1);
        }
        Delivery {
            invocation: invocation.id,
            observation: self
                .deliveries
                .pop_front()
                .unwrap_or(Observation::Success(Value(1))),
        }
    }
}
