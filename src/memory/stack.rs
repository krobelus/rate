use crate::memory::{index_vec, index_vec_mut};
use std::ops::{Index, IndexMut};

#[derive(Debug)]
pub struct Stack<T> {
    vec: Vec<T>,
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
}

impl<T> Index<usize> for Stack<T> {
    type Output = T;
    fn index(&self, offset: usize) -> &T {
        index_vec(&self.vec, offset)
    }
}

impl<T> IndexMut<usize> for Stack<T> {
    fn index_mut(&mut self, offset: usize) -> &mut T {
        index_vec_mut(&mut self.vec, offset)
    }
}

impl<'a, T> IntoIterator for &'a Stack<T> {
    type Item = &'a T;
    type IntoIter = std::slice::Iter<'a, T>;
    fn into_iter(self) -> std::slice::Iter<'a, T> {
        self.vec.iter()
    }
}
