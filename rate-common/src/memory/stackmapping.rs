//! `StackMapping` combines a `BoundedVector` and an `Array`, providing fast look-up and iteration.

use crate::memory::{Array, BoundedVector, HeapSpace, Offset};
use rate_macros::HeapSpace;
use std::{fmt::Debug, iter::IntoIterator, ops::Index, slice};

/// A combination of a [`BoundedVector`](../boundedvector/struct.BoundedVector.html)
/// and an [`Array`](../array/struct.Array.html).
///
/// This provides `Vec`-like semantics with elements of type `Key`.
/// Additionally, each key is associated with one value of type `T` (key is
/// mapped to value).
/// The value can be looked up in constant time using the index operator (`[]`).
#[derive(Debug, HeapSpace, Default)]
pub struct StackMapping<Key: Offset + Copy + Debug, T: Copy + Debug> {
    /// The default value to use for unmapped keys.
    default_value: T,
    /// The `Array` that stores the key-value pairs.
    array: Array<Key, T>,
    /// The stack that stores the keys.
    vector: BoundedVector<Key>,
}

impl<Key: Offset + Copy + Debug, T: Copy + Debug> StackMapping<Key, T> {
    /// Construct a new `StackMapping`.
    ///
    /// # Parameters
    /// - `array_value:` see [default_value](#structfield.default_value)
    /// - `array_size:` the size of the array, must be large enough to hold
    ///   the highest expected value of type `Key`
    /// - `stack_size:` the maximum size of the stack, e.g. the maximum
    ///   number of keys that can be added to this stackmapping
    pub fn with_array_value_size_stack_size(
        array_value: T,
        array_size: usize,
        stack_size: usize,
    ) -> StackMapping<Key, T> {
        StackMapping {
            default_value: array_value,
            array: Array::new(array_value, array_size),
            vector: BoundedVector::with_capacity(stack_size),
        }
    }
    /// See [`Vec::len()`](https://doc.rust-lang.org/std/vec/struct.Vec.html#method.len).
    pub fn len(&self) -> usize {
        self.vector.len()
    }
    /// See [`Vec::is_empty()`](https://doc.rust-lang.org/std/vec/struct.Vec.html#method.is_empty).
    pub fn is_empty(&self) -> bool {
        self.vector.is_empty()
    }
    /// This removs the top `Key` and also resets the mapping of this key
    /// to the [default_value](#structfield.default_value).
    pub fn pop(&mut self) -> Option<Key> {
        self.vector.pop().map(|key| {
            self.array[key] = self.default_value;
            key
        })
    }
    /// Returns the last key in the vector.
    /// # Panics
    /// Panics if the vector is empty.
    pub fn peek(&self) -> Key {
        self.vector[self.vector.len() - 1]
    }
    /// This clears the vector and resets all mappings.
    pub fn clear(&mut self) {
        while !self.is_empty() {
            self.pop();
        }
    }
    /// Returns the key in the vector at the given index.
    pub fn stack_at(&self, offset: usize) -> Key {
        self.vector[offset]
    }
    /// Returns the mutable key in the vector at the given index.
    pub fn stack_at_mut(&mut self, offset: usize) -> &mut Key {
        &mut self.vector[offset]
    }
    /// Pushes to the vector and maps `key` to `value`.
    pub fn push(&mut self, key: Key, value: T) {
        self.array[key] = value;
        self.vector.push(key);
    }
    /// Pushes to the vector.
    pub fn push_but_do_not_set(&mut self, key: Key) {
        self.vector.push(key);
    }
    /// Maps `key` to `value`.
    pub fn set_but_do_not_push(&mut self, key: Key, value: T) {
        self.array[key] = value;
    }
    /// Returns an iterator over the keys in the vector.
    pub fn iter(&self) -> slice::Iter<Key> {
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
    type IntoIter = slice::Iter<'a, Key>;
    fn into_iter(self) -> Self::IntoIter {
        self.vector.into_iter()
    }
}

impl<Key: Ord + Offset + Copy + Debug, T: Copy + Debug> StackMapping<Key, T> {
    /// See [`Vec::sort_unstable()`](https://doc.rust-lang.org/std/vec/struct.Vec.html#method.sort_unstable).
    pub fn sort_unstable(&mut self) {
        self.vector.sort_unstable()
    }
}

impl<Key: Offset + Copy + Debug, T: Copy + Debug> StackMapping<Key, T> {
    /// See [`Vec::sort_unstable_by_key()`](https://doc.rust-lang.org/std/vec/struct.Vec.html#method.sort_unstable_by_key).
    pub fn sort_unstable_by_key<F, K>(&mut self, f: F)
    where
        F: FnMut(&Key) -> K,
        K: Ord,
    {
        self.vector.sort_unstable_by_key(f)
    }
}
