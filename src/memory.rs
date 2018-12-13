//! Customized data structures.
//!
//! Currently they mostly behave the same as standard vectors and slices, with
//! these exceptions:
//!
//! - Custom type for indexing as first template argument in `Array<I, T>`.
//! - Bounds checking can be disabled to some extent (work in progress).
//! - If we know a good upper bound for a stack we prefer to use
//! `BoundedStack<T>` or `StackMapping<Key, T>` as they never allocate after being constructed.

use crate::config::BOUNDS_CHECKING;

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

fn index_vec<T>(vec: &Vec<T>, index: impl Offset) -> &T {
    if BOUNDS_CHECKING {
        &vec[index.as_offset()]
    } else {
        unsafe { vec.get_unchecked(index.as_offset()) }
    }
}

fn index_vec_mut<T>(vec: &mut Vec<T>, index: impl Offset) -> &mut T {
    if BOUNDS_CHECKING {
        &mut vec[index.as_offset()]
    } else {
        unsafe { vec.get_unchecked_mut(index.as_offset()) }
    }
}
