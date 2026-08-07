mod deduplicated;
mod idempotent;
mod uncontrolled;

pub use deduplicated::DeduplicatedAdapter;
pub use idempotent::IdempotentAdapter;
pub use uncontrolled::UncontrolledAdapter;
