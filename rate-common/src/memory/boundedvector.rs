//! `BoundedVector` is a non-growable
//! [`std::vec::Vec`](https://doc.rust-lang.org/std/vec/struct.Vec.html).

use crate::memory::{HeapSpace, Vector};
use rate_macros::HeapSpace;
use std::{
    ops::{Index, IndexMut},
    slice,
};

/// A contiguous but non-growable array type, using [`Vector`](../vector/struct.Vector.html)
///
/// This exposes a subset of the `Vector` API (and thus essentially behaves
/// like a `std::vec::Vec`). Notably, it does not provide functions that grow the
/// capacity of the vector.
///
/// A `BoundedVector` can be used as a stack with a known maximum size.
#[derive(Debug, Clone, HeapSpace, PartialEq, Default)]
pub struct BoundedVector<T>
where
    T: HeapSpace,
{
    /// The wrapped `Vector`
    vector: Vector<T>,
}

impl<T: HeapSpace> BoundedVector<T> {
    /// See [`Vec::with_capacity()`](https://doc.rust-lang.org/std/vec/struct.Vec.html#method.with_capacity).
    pub fn with_capacity(capacity: usize) -> BoundedVector<T> {
        BoundedVector {
            vector: Vector::with_capacity(capacity),
        }
    }
    /// Pushes a value, increasing the vector's length by one.
    ///
    /// Note that unlike `
    /// [`Vec::push()`](https://doc.rust-lang.org/std/vec/struct.Vec.html#method.push)
    /// this does not grow the vector if it is full.
    ///
    /// # Panics
    /// Panics if there is no space for the new element.
    pub fn push(&mut self, value: T) {
        self.vector.push_no_grow(value)
    }
    /// See [`Vec::len()`](https://doc.rust-lang.org/std/vec/struct.Vec.html#method.len).
    pub fn len(&self) -> usize {
        self.vector.len()
    }
    /// See [`Vec::is_empty()`](https://doc.rust-lang.org/std/vec/struct.Vec.html#method.is_empty).
    pub fn is_empty(&self) -> bool {
        self.vector.is_empty()
    }
    /// See [`Vec::capacity()`](https://doc.rust-lang.org/std/vec/struct.Vec.html#method.capacity).
    pub fn capacity(&self) -> usize {
        self.vector.capacity()
    }
    /// See [`Vec::pop()`](https://doc.rust-lang.org/std/vec/struct.Vec.html#method.pop).
    pub fn pop(&mut self) -> Option<T> {
        self.vector.pop()
    }
    /// See [`Vec::first()`](https://doc.rust-lang.org/std/vec/struct.Vec.html#method.first).
    pub fn first(&self) -> &T {
        self.vector.first()
    }
    /// See [`Vec::last()`](https://doc.rust-lang.org/std/vec/struct.Vec.html#method.last).
    pub fn last(&self) -> &T {
        self.vector.last()
    }
    /// See [`Vec::iter()`](https://doc.rust-lang.org/std/vec/struct.Vec.html#method.iter).
    pub fn iter(&self) -> slice::Iter<T> {
        self.vector.iter()
    }
    /// See [`Vec::as_ptr()`](https://doc.rust-lang.org/std/vec/struct.Vec.html#method.as_ptr).
    pub fn as_ptr(&mut self) -> *const T {
        self.vector.as_ptr()
    }
    /// See [`Vec::mut_ptr()`](https://doc.rust-lang.org/std/vec/struct.Vec.html#method.mut_ptr).
    pub fn mut_ptr(&mut self) -> *mut T {
        self.vector.mut_ptr()
    }
    /// See [`Vec::truncate()`](https://doc.rust-lang.org/std/vec/struct.Vec.html#method.truncate).
    pub fn truncate(&mut self, new_length: usize) {
        self.vector.truncate(new_length)
    }
    /// See [`Vec::clear()`](https://doc.rust-lang.org/std/vec/struct.Vec.html#method.clear).
    pub fn clear(&mut self) {
        self.vector.clear()
    }
}

impl<T: HeapSpace + Clone + Default> BoundedVector<T> {
    /// See [`Vec::resize()`](https://doc.rust-lang.org/std/vec/struct.Vec.html#method.resize).
    pub fn resize(&mut self, new_length: usize) {
        self.vector.resize(new_length)
    }
}

impl<T: HeapSpace + Ord> BoundedVector<T> {
    /// See [`Vec::sort_unstable()`](https://doc.rust-lang.org/std/vec/struct.Vec.html#method.sort_unstable).
    pub fn sort_unstable(&mut self) {
        self.vector.sort_unstable()
    }
}

impl<T: HeapSpace> BoundedVector<T> {
    /// See [`Vec::sort_unstable_by_key()`](https://doc.rust-lang.org/std/vec/struct.Vec.html#method.sort_unstable_by_key).
    pub fn sort_unstable_by_key<F, K>(&mut self, f: F)
    where
        F: FnMut(&T) -> K,
        K: Ord,
    {
        self.vector.sort_unstable_by_key(f)
    }
}

impl<T: HeapSpace> Index<usize> for BoundedVector<T> {
    type Output = T;
    fn index(&self, offset: usize) -> &T {
        self.vector.index(offset)
    }
}

impl<T: HeapSpace> IndexMut<usize> for BoundedVector<T> {
    fn index_mut(&mut self, offset: usize) -> &mut T {
        self.vector.index_mut(offset)
    }
}

impl<'a, T: HeapSpace> IntoIterator for &'a BoundedVector<T> {
    type Item = &'a T;
    type IntoIter = slice::Iter<'a, T>;
    fn into_iter(self) -> Self::IntoIter {
        self.vector.iter()
    }
}
