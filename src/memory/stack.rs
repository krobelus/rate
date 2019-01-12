use crate::{
    config::BOUNDS_CHECKING,
    memory::{Slice, SliceMut},
};
use std::ops::{Index, IndexMut};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Stack<T> {
    pub vec: Vec<T>,
}

impl<T> Stack<T> {
    pub fn new() -> Stack<T> {
        Stack { vec: Vec::new() }
    }
    pub fn with_capacity(capacity: usize) -> Stack<T> {
        Stack {
            vec: Vec::with_capacity(capacity),
        }
    }
    pub fn from_vec(vec: Vec<T>) -> Stack<T> {
        Stack { vec: vec }
    }
    pub fn len(&self) -> usize {
        self.vec.len()
    }
    pub fn empty(&self) -> bool {
        self.len() == 0
    }
    pub fn capacity(&self) -> usize {
        self.vec.capacity()
    }
    pub fn push(&mut self, value: T) {
        self.vec.push(value)
    }
    pub fn pop(&mut self) -> T {
        self.vec.pop().unwrap()
    }
    pub fn clear(&mut self) {
        self.vec.clear()
    }
    pub fn first(&self) -> &T {
        requires!(!self.empty());
        &self[0]
    }
    pub fn last(&self) -> &T {
        requires!(!self.empty());
        &self[self.len() - 1]
    }
    pub fn iter(&self) -> std::slice::Iter<T> {
        self.into_iter()
    }
    pub fn as_slice(&self) -> Slice<T> {
        Slice::new(&self.vec)
    }
    pub fn as_mut_slice(&mut self) -> SliceMut<T> {
        SliceMut::new(&mut self.vec)
    }
    pub fn as_ptr(&mut self) -> *const T {
        self.vec.as_ptr()
    }
    pub fn as_mut_ptr(&mut self) -> *mut T {
        self.vec.as_mut_ptr()
    }
}

impl<T: Clone> Stack<T> {
    pub fn fill(size: usize, default_value: T) -> Stack<T> {
        Stack {
            vec: vec![default_value; size],
        }
    }
    pub fn truncate(&mut self, new_len: usize) {
        self.vec.truncate(new_len)
    }
}

impl<T: Copy> Stack<T> {
    pub fn swap_remove(&mut self, offset: usize) {
        self[offset] = self[self.len() - 1];
        self.vec.pop();
    }
}

impl<T: Ord> Stack<T> {
    pub fn sort_unstable(&mut self) {
        self.vec.sort_unstable()
    }
}

impl<T> Stack<T> {
    pub fn sort_unstable_by_key<F, K>(&mut self, f: F)
    where
        F: FnMut(&T) -> K,
        K: Ord,
    {
        self.vec.sort_unstable_by_key(f)
    }
}

impl<T> Index<usize> for Stack<T> {
    type Output = T;
    fn index(&self, offset: usize) -> &T {
        if BOUNDS_CHECKING {
            &self.vec[offset]
        } else {
            unsafe { self.vec.get_unchecked(offset) }
        }
    }
}

impl<T> IndexMut<usize> for Stack<T> {
    fn index_mut(&mut self, offset: usize) -> &mut T {
        if BOUNDS_CHECKING {
            &mut self.vec[offset]
        } else {
            unsafe { self.vec.get_unchecked_mut(offset) }
        }
    }
}

impl<'a, T> IntoIterator for &'a Stack<T> {
    type Item = &'a T;
    type IntoIter = std::slice::Iter<'a, T>;
    fn into_iter(self) -> std::slice::Iter<'a, T> {
        self.vec.iter()
    }
}
