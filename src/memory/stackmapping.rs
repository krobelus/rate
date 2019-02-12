//! Stack with fast lookup.

use crate::memory::{Array, BoundedStack, HeapSpace, Offset};
use std::{fmt::Debug, iter::IntoIterator, ops::Index};

#[derive(Debug)]
pub struct StackMapping<Key: Offset + Copy + Debug, T: Copy + Debug> {
    default_value: T,
    array: Array<Key, T>,
    stack: BoundedStack<Key>,
}

impl<Key: Offset + Copy + Debug, T: Copy + Debug> StackMapping<Key, T> {
    pub fn with_array_value_size_stack_size(
        array_value: T,
        array_size: usize,
        stack_size: usize,
    ) -> StackMapping<Key, T> {
        StackMapping {
            default_value: array_value,
            array: Array::new(array_value, array_size),
            stack: BoundedStack::with_capacity(stack_size),
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
    pub fn peek(&self) -> Key {
        self.stack[self.stack.len() - 1]
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
    pub fn iter(&self) -> std::slice::Iter<Key> {
        self.into_iter()
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

impl<Key: Offset + Copy + Debug, T: Copy + Debug> HeapSpace for StackMapping<Key, T> {
    fn heap_space(&self) -> usize {
        self.array.heap_space() + self.stack.heap_space()
    }
}
