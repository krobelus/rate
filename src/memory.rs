//! Customized data structures.
//!
//! Currently they mostly behave the same as standard vectors and slices, with
//! these exceptions:
//!
//! - Custom type for indexing as first template argument in `Array<I, T>`.
//! - Bounds checking can be disabled to some extent (work in progress).
//! - If we know a good upper bound for a stack we prefer to use
//! `BoundedStack<T>` or `StackMapping<Key, T>` as they never allocate after being constructed.

mod array;
mod boundedstack;
mod slice;
mod stack;
mod stackmapping;

pub use crate::memory::{
    array::Array,
    boundedstack::BoundedStack,
    slice::{Slice, SliceMut},
    stack::Stack,
    stackmapping::StackMapping,
};

/// Trait for types that can be used as index in an array.
pub trait Offset {
    fn as_offset(self) -> usize;
}

impl Offset for usize {
    fn as_offset(self) -> usize {
        self
    }
}
