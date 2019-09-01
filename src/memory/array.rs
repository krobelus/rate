//! `Array` is a non-growable
//! [`std::vec::Vec`](https://doc.rust-lang.org/std/vec/struct.Vec.html)` with
//! strongly-typed indexing.

use crate::memory::{assert_in_bounds, HeapSpace, Offset, Vector};
use std::{
    marker::PhantomData,
    ops::{Deref, DerefMut, Index, IndexMut},
};

/// A contiguous non-growable array type with strongly-typed indexing.
///
/// The first template argument specifies the type that can be used for
/// indexing the array. The second template argument specifies the type of
/// the elements in the array.
///
/// An `Array` can be used as a fixed size map or set data structure.
/// The maximum index must be set at construction time, which will allocate
/// an area of memory of that size. As a result, this can be quite memory-consuming
/// for sparse maps or sets, but it is as efficient as it gets for fast lookups.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Array<I: Offset, T> {
    /// The vector of elements
    pub data: Vector<T>,
    /// Zero-sized field to appease the compiler, since `I` is not used in any other field
    pub phantom: PhantomData<I>,
}

impl<I: Offset, T: Clone> Array<I, T> {
    /// Create a new array of size `size` with all elements set to `value`.
    pub fn new(value: T, size: usize) -> Array<I, T> {
        Array {
            data: Vector::from_vec(vec![value; size]),
            phantom: PhantomData,
        }
    }
}
impl<I: Offset, T> Array<I, T> {
    /// Create a new array of size `size` without initializing its elements.
    pub fn with_capacity(size: usize) -> Array<I, T> {
        Array {
            data: Vector::with_capacity(size),
            phantom: PhantomData,
        }
    }
    /// Create a new array by taking ownership of a `Vector`.
    pub fn from(data: Vector<T>) -> Array<I, T> {
        Array {
            data,
            phantom: PhantomData,
        }
    }
    /// Returns the size of the array.
    pub fn size(&self) -> usize {
        self.data.capacity()
    }
}

impl<I: Offset, T> Default for Array<I, T> {
    fn default() -> Array<I, T> {
        Array::with_capacity(0)
    }
}

impl<I: Offset, T> Deref for Array<I, T> {
    type Target = [T];
    fn deref(&self) -> &[T] {
        self.data.deref()
    }
}

impl<I: Offset, T> DerefMut for Array<I, T> {
    fn deref_mut(&mut self) -> &mut [T] {
        self.data.deref_mut()
    }
}

impl<I: Offset, T> AsRef<Array<I, T>> for Array<I, T> {
    fn as_ref(&self) -> &Array<I, T> {
        self
    }
}

impl<I: Offset, T> AsMut<Array<I, T>> for Array<I, T> {
    fn as_mut(&mut self) -> &mut Array<I, T> {
        self
    }
}

impl<I: Offset, T> AsRef<[T]> for Array<I, T> {
    fn as_ref(&self) -> &[T] {
        self
    }
}

impl<I: Offset, T> AsMut<[T]> for Array<I, T> {
    fn as_mut(&mut self) -> &mut [T] {
        self
    }
}

impl<I: Offset, T> Index<I> for Array<I, T> {
    type Output = T;
    fn index(&self, key: I) -> &T {
        assert_in_bounds(0..self.size(), key.as_offset());
        unsafe { self.data.get_unchecked(key.as_offset()) }
    }
}

impl<I: Offset, T> IndexMut<I> for Array<I, T> {
    fn index_mut(&mut self, key: I) -> &mut T {
        assert_in_bounds(0..self.size(), key.as_offset());
        unsafe { self.data.get_unchecked_mut(key.as_offset()) }
    }
}

impl<I: Offset, T: HeapSpace> HeapSpace for Array<I, T> {
    fn heap_space(&self) -> usize {
        self.data.heap_space()
            + self
                .data
                .iter()
                .fold(0, |sum, item| sum + item.heap_space())
    }
}
