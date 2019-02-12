//! Stack that never grows.
use crate::memory::{Array, HeapSpace};
use std::{
    iter::IntoIterator,
    ops::{Index, IndexMut},
};

#[derive(Debug, Clone)]
pub struct BoundedStack<T: Clone> {
    array: Array<usize, T>,
    len: usize,
}

impl<T: Copy> BoundedStack<T> {
    pub fn with_capacity(capacity: usize) -> BoundedStack<T> {
        BoundedStack {
            array: Array::with_capacity(capacity),
            len: 0,
        }
    }
}

impl<T: Copy> BoundedStack<T> {
    pub fn len(&self) -> usize {
        self.len
    }
    pub fn empty(&self) -> bool {
        self.len() == 0
    }
    pub fn capacity(&self) -> usize {
        self.array.size()
    }
    pub fn push(&mut self, value: T) {
        invariant!(self.len < self.capacity());
        self.array[self.len] = value;
        self.len += 1;
    }
    pub fn pop(&mut self) -> T {
        invariant!(self.len() != 0);
        self.len -= 1;
        self.array[self.len]
    }
    pub fn clear(&mut self) {
        self.len = 0
    }
}

impl<T: Copy> BoundedStack<T> {
    pub fn resize(&mut self, new_len: usize) {
        self.len = new_len
    }
}

impl<T: Copy> Index<usize> for BoundedStack<T> {
    type Output = T;
    fn index(&self, offset: usize) -> &T {
        &self.array[offset]
    }
}

impl<T: Copy> IndexMut<usize> for BoundedStack<T> {
    fn index_mut(&mut self, offset: usize) -> &mut T {
        &mut self.array[offset]
    }
}

impl<'a, T: Copy> IntoIterator for &'a BoundedStack<T> {
    type Item = &'a T;
    type IntoIter = std::slice::Iter<'a, T>;
    fn into_iter(self) -> std::slice::Iter<'a, T> {
        unsafe { std::slice::from_raw_parts(self.array.ptr(), self.len).into_iter() }
    }
}

impl<T: Copy> BoundedStack<T> {
    pub fn sort_unstable_by_key<F, K>(&mut self, f: F)
    where
        F: FnMut(&T) -> K,
        K: Ord,
    {
        unsafe { std::slice::from_raw_parts_mut(self.array.mut_ptr(), self.len) }
            .sort_unstable_by_key(f)
    }
}

impl<T: Copy> HeapSpace for BoundedStack<T> {
    fn heap_space(&self) -> usize {
        (0..self.len()).fold(0, |sum, i| sum + self[i].heap_space())
    }
}
