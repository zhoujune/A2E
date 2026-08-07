use std::collections::VecDeque;

use crate::adapter::{Adapter, Delivery};
use crate::model::{Invocation, Observation, RetryClass, Value};

#[derive(Debug, Default)]
pub struct UncontrolledAdapter {
    effects: u64,
    deliveries: VecDeque<Observation>,
}

impl UncontrolledAdapter {
    #[must_use]
    pub fn scripted(deliveries: impl IntoIterator<Item = Observation>) -> Self {
        Self {
            effects: 0,
            deliveries: deliveries.into_iter().collect(),
        }
    }

    #[must_use]
    pub const fn effect_count(&self) -> u64 {
        self.effects
    }
}

impl Adapter for UncontrolledAdapter {
    fn retry_class(&self) -> RetryClass {
        RetryClass::Uncontrolled
    }

    fn invoke(&mut self, invocation: Invocation) -> Delivery {
        self.effects = self.effects.saturating_add(1);
        Delivery {
            invocation: invocation.id,
            observation: self
                .deliveries
                .pop_front()
                .unwrap_or(Observation::Success(Value(self.effects))),
        }
    }
}
