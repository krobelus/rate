//! Stack that never grows.
use crate::memory::Stack;
use std::{
    iter::IntoIterator,
    ops::{Index, IndexMut},
};

#[derive(Debug)]
pub struct BoundedStack<T> {
    stack: Stack<T>,
}

impl<T> BoundedStack<T> {
    pub fn with_capacity(size: usize) -> BoundedStack<T> {
        BoundedStack {
            stack: Stack::with_capacity(size),
        }
    }
    pub fn len(&self) -> usize {
        self.stack.len()
    }
    pub fn capacity(&self) -> usize {
        self.stack.capacity()
    }
    pub fn push(&mut self, value: T) {
        ensure!(self.len() < self.capacity());
        self.stack.push(value)
    }
    pub fn pop(&mut self) -> T {
        ensure!(self.len() != 0);
        self.stack.pop()
    }
    pub fn clear(&mut self) {
        self.stack.clear()
    }
}

impl<T> Index<usize> for BoundedStack<T> {
    type Output = T;
    fn index(&self, offset: usize) -> &T {
        &self.stack[offset]
    }
}

impl<T> IndexMut<usize> for BoundedStack<T> {
    fn index_mut(&mut self, offset: usize) -> &mut T {
        &mut self.stack[offset]
    }
}

impl<'a, T> IntoIterator for &'a BoundedStack<T> {
    type Item = &'a T;
    type IntoIter = std::slice::Iter<'a, T>;
    fn into_iter(self) -> std::slice::Iter<'a, T> {
        self.stack.into_iter()
    }
}
