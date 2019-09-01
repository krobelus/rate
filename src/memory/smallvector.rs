//! `SmallVector` is a
//! [`std::vec::Vec`](https://doc.rust-lang.org/std/vec/struct.Vec.html) that
//! does not allocate if it contains one ore no element.

use crate::{
    config::unreachable,
    memory::{assert_in_bounds, Vector},
};
use std::{
    iter::FromIterator,
    ops::{Index, IndexMut},
};

/// A [`Vector`](../vector/struct.Vector.html) with small-buffer-optimization
#[derive(Debug, PartialEq, Clone)]
pub enum SmallVector<T> {
    /// Empty variant, no need to allocate anything (same as `Vector`)
    Empty,
    /// A `SmallVector` with a single element that is stored in place
    One(T),
    /// Fallback to a plain `Vector`, for two or more elements
    Many(Vector<T>),
}

impl<T> SmallVector<T> {
    /// See [`Vec::len()`](https://doc.rust-lang.org/std/vec/struct.Vec.html#method.len).
    pub fn len(&self) -> usize {
        match self {
            SmallVector::Empty => 0,
            SmallVector::One(_value) => 1,
            SmallVector::Many(vector) => vector.len(),
        }
    }
}

impl<T: Copy + Default> SmallVector<T> {
    /// Constructs a new empty `SmallVector`.
    pub fn new() -> SmallVector<T> {
        SmallVector::Empty
    }
    /// Constructs a new `SmallVector` containing a single element.
    #[allow(dead_code)]
    pub fn singleton(value: T) -> SmallVector<T> {
        SmallVector::One(value)
    }
    /// Convert a `Vector` to a `SmallVector`.
    pub fn from_vector(vector: Vector<T>) -> SmallVector<T> {
        SmallVector::Many(vector)
    }
    /// See [`Vec::first()`](https://doc.rust-lang.org/std/vec/struct.Vec.html#method.first).
    pub fn first(&self) -> Option<T> {
        match self {
            SmallVector::Empty => None,
            &SmallVector::One(value) => Some(value),
            SmallVector::Many(vector) => vector.get(0).cloned(),
        }
    }
    /// See [`Vec::is_empty()`](https://doc.rust-lang.org/std/vec/struct.Vec.html#method.is_empty).
    pub fn is_empty(&self) -> bool {
        match self {
            SmallVector::Empty => true,
            &SmallVector::One(_value) => false,
            SmallVector::Many(vector) => vector.is_empty(),
        }
    }
    /// See [`Vec::push()`](https://doc.rust-lang.org/std/vec/struct.Vec.html#method.push).
    pub fn push(&mut self, new_value: T) {
        if let SmallVector::Empty = self {
            *self = SmallVector::One(new_value);
            return;
        }
        if let SmallVector::One(value) = *self {
            *self = SmallVector::Many(vector!(value));
        }
        if let SmallVector::Many(vector) = self {
            vector.push(new_value);
            return;
        }
        unreachable();
    }
    /// See [`Vec::swap_remove()`](https://doc.rust-lang.org/std/vec/struct.Vec.html#method.swap_remove).
    ///
    /// *Note*: this currently only supports being called with index=0 because that's all we need for parsing.
    pub fn swap_remove(&mut self, index: usize) -> T {
        requires!(index == 0);
        if let SmallVector::One(value) = *self {
            *self = SmallVector::Empty;
            value
        } else if let SmallVector::Many(vector) = self {
            vector.swap_remove(0)
        } else {
            unreachable!()
        }
    }
}

impl<T: Copy + Default> FromIterator<T> for SmallVector<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> SmallVector<T> {
        SmallVector::from_vector(Vector::from_iter(iter))
    }
}
impl<T> Index<usize> for SmallVector<T> {
    type Output = T;
    fn index(&self, index: usize) -> &Self::Output {
        assert_in_bounds(0..self.len(), index);
        match self {
            SmallVector::Empty => unreachable!(),
            SmallVector::One(value) => value,
            SmallVector::Many(vector) => &vector[index],
        }
    }
}

impl<T> IndexMut<usize> for SmallVector<T> {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        assert_in_bounds(0..self.len(), index);
        match self {
            SmallVector::Empty => unreachable!(),
            SmallVector::One(value) => value,
            SmallVector::Many(vector) => &mut vector[index],
        }
    }
}
