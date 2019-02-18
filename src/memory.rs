//! Data structures.
//!
//! Currently they mostly behave the same as standard vectors and slices. Some
//! differences include:
//!
//! - The first template argument in `Array<I, T>` and `StackMapping<I, T>`
//!   requires to specify a type that will be used for indexing. This prevents
//!   us from accidentally using an index of the wrong type.
//!
//! - Bounds checking can be disabled.
//!
//! If we know a good upper bound for the size of a stack we prefer to use
//! `BoundedStack<T>` or `StackMapping<Key, T>` as they never allocate after
//! being constructed.

mod array;
mod boundedstack;
mod slice;
#[macro_use]
mod stack;
mod stackmapping;

pub use crate::memory::{
    array::Array,
    boundedstack::BoundedStack,
    slice::{Slice, SliceMut},
    stack::{Stack, StackIterator},
    stackmapping::StackMapping,
};

/// Trait for index-like types
pub trait Offset {
    fn as_offset(&self) -> usize;
}

impl Offset for usize {
    fn as_offset(&self) -> usize {
        *self
    }
}

/// Report memory usage
pub trait HeapSpace {
    fn heap_space(&self) -> usize;
}

impl<T: Copy> HeapSpace for T {
    fn heap_space(&self) -> usize {
        0
    }
}

pub fn format_memory_usage(bytes: usize) -> String {
    format!("{:0.2}", (bytes as f64) / (1 << 20) as f64)
}
