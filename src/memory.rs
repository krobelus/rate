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
//! If we know a good upper bound for the size of a vector we prefer to use
//! `BoundedStack<T>` or `StackMapping<Key, T>` as they never allocate after
//! being constructed.

mod array;
mod boundedstack;
#[macro_use]
mod vector;
mod smallstack;
mod stackmapping;

use std::convert::TryFrom;

pub use crate::memory::{
    array::Array,
    boundedstack::BoundedStack,
    smallstack::SmallStack,
    stackmapping::StackMapping,
    vector::{assert_in_bounds, Vector},
};

/// Trait for types that can be used as an array index.
pub trait Offset {
    fn as_offset(&self) -> usize;
}

impl Offset for usize {
    fn as_offset(&self) -> usize {
        *self
    }
}

impl Offset for u64 {
    fn as_offset(&self) -> usize {
        requires!(usize::try_from(*self).is_ok());
        *self as usize
    }
}

impl Offset for i32 {
    fn as_offset(&self) -> usize {
        requires!(usize::try_from(*self).is_ok());
        *self as usize
    }
}

/// A trait for objects that can report their memory usage on the heap
pub trait HeapSpace {
    /// The number of bytes allocated on the heap that this owns.
    fn heap_space(&self) -> usize;
}

impl<T: Copy> HeapSpace for T {
    fn heap_space(&self) -> usize {
        0
    }
}

/// Convert bytes to  megabytes for readability.
pub fn format_memory_usage(bytes: usize) -> String {
    format!("{:12}", bytes >> 20) // MB
}
