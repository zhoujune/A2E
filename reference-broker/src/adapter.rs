use crate::model::{Invocation, InvocationId, Observation, RetryClass};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Delivery {
    pub invocation: InvocationId,
    pub observation: Observation,
}

pub trait Adapter {
    fn retry_class(&self) -> RetryClass;

    fn invoke(&mut self, invocation: Invocation) -> Delivery;
}
