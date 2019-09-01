//! A vector that does not allocate if it contains one ore no element.

use crate::{config::unreachable, memory::Vector};

use std::iter::FromIterator;

#[derive(Debug, PartialEq, Clone)]
pub enum SmallVector<T> {
    Empty,
    One(T),
    Many(Vector<T>),
}

impl<T: Copy + Default> SmallVector<T> {
    pub fn new() -> SmallVector<T> {
        SmallVector::Empty
    }
    #[allow(dead_code)]
    pub fn singleton(value: T) -> SmallVector<T> {
        SmallVector::One(value)
    }
    pub fn from_stack(vector: Vector<T>) -> SmallVector<T> {
        SmallVector::Many(vector)
    }
    pub fn front(&self) -> Option<T> {
        match self {
            SmallVector::Empty => None,
            &SmallVector::One(value) => Some(value),
            SmallVector::Many(vector) => vector.get(0).cloned(),
        }
    }
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
    pub fn swap_remove(&mut self, index: usize) -> Option<T> {
        requires!(index == 0);
        if let SmallVector::One(value) = *self {
            *self = SmallVector::Empty;
            Some(value)
        } else if let SmallVector::Many(vector) = self {
            if vector.is_empty() {
                None
            } else {
                Some(vector.swap_remove(0))
            }
        } else {
            None
        }
    }
    #[allow(dead_code)]
    pub fn to_vec(&self) -> Vec<T> {
        match &self {
            SmallVector::Empty => vec![],
            SmallVector::One(value) => vec![*value],
            SmallVector::Many(vector) => vector.clone().to_vec(),
        }
    }
}

impl<T: Copy + Default> FromIterator<T> for SmallVector<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> SmallVector<T> {
        SmallVector::from_stack(Vector::from_iter(iter))
    }
}
