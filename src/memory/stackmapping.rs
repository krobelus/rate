//! Stack with fast lookup.

use crate::memory::{Array, BoundedStack, Offset};
use std::{fmt::Debug, iter::IntoIterator, ops::Index};

#[derive(Debug)]
pub struct StackMapping<Key: Offset + Copy + Debug, T: Copy + Debug> {
    default_value: T,
    array: Array<Key, T>,
    stack: BoundedStack<Key>,
}

impl<Key: Offset + Copy + Debug, T: Copy + Debug> StackMapping<Key, T> {
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
    pub fn empty(&self) -> bool {
        self.stack.empty()
    }
    pub fn push(&mut self, key: Key, value: T) {
        self.array[key] = value;
        self.stack.push(key);
    }
    pub fn pop(&mut self) -> Key {
        let key = self.stack.pop();
        self.array[key] = self.default_value;
        key
    }
    pub fn clear(&mut self) {
        while self.len() != 0 {
            self.pop();
        }
    }
    pub fn stack_at(&self, offset: usize) -> Key {
        self.stack[offset]
    }
    pub fn stack_at_mut(&mut self, offset: usize) -> &mut Key {
        &mut self.stack[offset]
    }
    pub fn set_but_do_not_push(&mut self, key: Key, value: T) {
        self.array[key] = value;
    }
    pub fn push_but_do_not_set(&mut self, key: Key) {
        self.stack.push(key);
    }
}

impl<Key: Offset + Copy + Debug, T: Copy + Debug> Index<Key> for StackMapping<Key, T> {
    type Output = T;
    fn index(&self, key: Key) -> &T {
        &self.array[key]
    }
}

impl<'a, Key: Offset + Copy + Debug, T: Copy + Debug> IntoIterator for &'a StackMapping<Key, T> {
    type Item = &'a Key;
    type IntoIter = std::slice::Iter<'a, Key>;
    fn into_iter(self) -> std::slice::Iter<'a, Key> {
        self.stack.into_iter()
    }
}
