//! Vector that never grows.

use crate::memory::{HeapSpace, Vector};
use rate_macros::HeapSpace;
use std::{
    ops::{Index, IndexMut},
    slice,
};

#[derive(Debug, Clone, HeapSpace, PartialEq, Default)]
pub struct BoundedVector<T>
where
    T: HeapSpace,
{
    vector: Vector<T>,
}

impl<T: HeapSpace> BoundedVector<T> {
    pub fn with_capacity(capacity: usize) -> BoundedVector<T> {
        BoundedVector {
            vector: Vector::with_capacity(capacity),
        }
    }
    pub fn push(&mut self, value: T) {
        self.vector.push_no_grow(value)
    }
    pub fn len(&self) -> usize {
        self.vector.len()
    }
    pub fn is_empty(&self) -> bool {
        self.vector.is_empty()
    }
    pub fn capacity(&self) -> usize {
        self.vector.capacity()
    }
    pub fn pop(&mut self) -> Option<T> {
        self.vector.pop()
    }
    pub fn first(&self) -> &T {
        self.vector.first()
    }
    pub fn last(&self) -> &T {
        self.vector.last()
    }
    pub fn iter(&self) -> slice::Iter<T> {
        self.vector.iter()
    }
    // pub fn as_slice(&self) -> Slice<T> {
    //     self.vector.as_slice()
    // }
    // pub fn mut_slice(&mut self) -> SliceMut<T> {
    //     self.vector.mut_slice()
    // }
    pub fn as_ptr(&mut self) -> *const T {
        self.vector.as_ptr()
    }
    pub fn mut_ptr(&mut self) -> *mut T {
        self.vector.mut_ptr()
    }
    pub fn truncate(&mut self, new_length: usize) {
        self.vector.truncate(new_length)
    }
    pub fn clear(&mut self) {
        self.vector.clear()
    }
}

impl<T: HeapSpace + Clone + Default> BoundedVector<T> {
    pub fn resize(&mut self, new_length: usize) {
        self.vector.resize(new_length)
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

impl<T: HeapSpace> BoundedVector<T> {
    pub fn sort_unstable_by_key<F, K>(&mut self, f: F)
    where
        F: FnMut(&T) -> K,
        K: Ord,
    {
        self.vector.sort_unstable_by_key(f)
    }
}

impl<T: HeapSpace + Ord> BoundedVector<T> {
    pub fn sort_unstable(&mut self) {
        self.vector.sort_unstable()
    }
}
