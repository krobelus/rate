//! Stack that never grows.

use crate::memory::{HeapSpace, Stack};
use rate_macros::HeapSpace;
use std::{
    ops::{Index, IndexMut},
    slice,
};

#[derive(Debug, Clone, HeapSpace, PartialEq, Default)]
pub struct BoundedStack<T>
where
    T: HeapSpace,
{
    stack: Stack<T>,
}

impl<T: HeapSpace> BoundedStack<T> {
    pub fn with_capacity(capacity: usize) -> BoundedStack<T> {
        BoundedStack {
            stack: Stack::with_capacity(capacity),
        }
    }
    pub fn push(&mut self, value: T) {
        self.stack.push_no_grow(value)
    }
    pub fn len(&self) -> usize {
        self.stack.len()
    }
    pub fn is_empty(&self) -> bool {
        self.stack.is_empty()
    }
    pub fn capacity(&self) -> usize {
        self.stack.capacity()
    }
    pub fn pop(&mut self) -> T {
        self.stack.pop()
    }
    pub fn first(&self) -> &T {
        self.stack.first()
    }
    pub fn last(&self) -> &T {
        self.stack.last()
    }
    pub fn iter(&self) -> slice::Iter<T> {
        self.stack.iter()
    }
    // pub fn as_slice(&self) -> Slice<T> {
    //     self.stack.as_slice()
    // }
    // pub fn mut_slice(&mut self) -> SliceMut<T> {
    //     self.stack.mut_slice()
    // }
    pub fn as_ptr(&mut self) -> *const T {
        self.stack.as_ptr()
    }
    pub fn mut_ptr(&mut self) -> *mut T {
        self.stack.mut_ptr()
    }
    pub fn truncate(&mut self, new_length: usize) {
        self.stack.truncate(new_length)
    }
    pub fn clear(&mut self) {
        self.stack.clear()
    }
}

impl<T: HeapSpace + Clone + Default> BoundedStack<T> {
    pub fn resize(&mut self, new_length: usize) {
        self.stack.resize(new_length)
    }
}

impl<T: HeapSpace> Index<usize> for BoundedStack<T> {
    type Output = T;
    fn index(&self, offset: usize) -> &T {
        self.stack.index(offset)
    }
}

impl<T: HeapSpace> IndexMut<usize> for BoundedStack<T> {
    fn index_mut(&mut self, offset: usize) -> &mut T {
        self.stack.index_mut(offset)
    }
}

impl<'a, T: HeapSpace> IntoIterator for &'a BoundedStack<T> {
    type Item = &'a T;
    type IntoIter = slice::Iter<'a, T>;
    fn into_iter(self) -> Self::IntoIter {
        self.stack.iter()
    }
}

impl<T: HeapSpace> BoundedStack<T> {
    pub fn sort_unstable_by_key<F, K>(&mut self, f: F)
    where
        F: FnMut(&T) -> K,
        K: Ord,
    {
        self.stack.sort_unstable_by_key(f)
    }
}

impl<T: HeapSpace + Ord> BoundedStack<T> {
    pub fn sort_unstable(&mut self) {
        self.stack.sort_unstable()
    }
}
