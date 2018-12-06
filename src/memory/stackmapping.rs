use crate::memory::{Array, BoundedStack, Offset};
use std::{
    iter::IntoIterator,
    ops::{Index, IndexMut},
};

#[derive(Debug)]
pub struct StackMapping<Key: Offset + Copy, T: Copy> {
    default_value: T,
    array: Array<Key, T>,
    stack: BoundedStack<Key>,
}

impl<Key: Offset + Copy, T: Copy> StackMapping<Key, T> {
    pub fn new(default_value: T, array_size: usize, stack_capacity: usize) -> StackMapping<Key, T> {
        StackMapping {
            default_value: default_value,
            array: Array::new(default_value, array_size),
            stack: BoundedStack::with_capacity(stack_capacity),
        }
    }
    pub fn len(&self) -> usize {
        self.stack.len()
    }
    pub fn insert(&mut self, key: Key, value: T) {
        self.array[key] = value;
        self.stack.push(key);
    }
    pub fn pop(&mut self) {
        let key = self.stack.pop();
        self.array[key] = self.default_value;
    }
    pub fn clear(&mut self) {
        while self.len() != 0 {
            self.pop()
        }
    }
}

impl<Key: Offset + Copy, T: Copy> Index<Key> for StackMapping<Key, T> {
    type Output = T;
    fn index(&self, key: Key) -> &T {
        &self.array[key]
    }
}

impl<Key: Offset + Copy, T: Copy> IndexMut<Key> for StackMapping<Key, T> {
    fn index_mut(&mut self, key: Key) -> &mut T {
        &mut self.array[key]
    }
}

impl<'a, Key: Offset + Copy, T: Copy> IntoIterator for &'a StackMapping<Key, T> {
    type Item = &'a Key;
    type IntoIter = std::slice::Iter<'a, Key>;
    fn into_iter(self) -> std::slice::Iter<'a, Key> {
        self.stack.into_iter()
    }
}
