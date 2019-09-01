//! A vector that does not allocate if it contains one ore no element.

use crate::{config::unreachable, memory::Vector};

use std::iter::FromIterator;

#[derive(Debug, PartialEq, Clone)]
pub enum SmallStack<T> {
    Empty,
    One(T),
    Many(Vector<T>),
}

impl<T: Copy + Default> SmallStack<T> {
    pub fn new() -> SmallStack<T> {
        SmallStack::Empty
    }
    #[allow(dead_code)]
    pub fn singleton(value: T) -> SmallStack<T> {
        SmallStack::One(value)
    }
    pub fn from_stack(vector: Vector<T>) -> SmallStack<T> {
        SmallStack::Many(vector)
    }
    pub fn front(&self) -> Option<T> {
        match self {
            SmallStack::Empty => None,
            &SmallStack::One(value) => Some(value),
            SmallStack::Many(vector) => vector.get(0).cloned(),
        }
    }
    pub fn push(&mut self, new_value: T) {
        if let SmallStack::Empty = self {
            *self = SmallStack::One(new_value);
            return;
        }
        if let SmallStack::One(value) = *self {
            *self = SmallStack::Many(vector!(value));
        }
        if let SmallStack::Many(vector) = self {
            vector.push(new_value);
            return;
        }
        unreachable();
    }
    pub fn swap_remove(&mut self, index: usize) -> Option<T> {
        requires!(index == 0);
        if let SmallStack::One(value) = *self {
            *self = SmallStack::Empty;
            Some(value)
        } else if let SmallStack::Many(vector) = self {
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
            SmallStack::Empty => vec![],
            SmallStack::One(value) => vec![*value],
            SmallStack::Many(vector) => vector.clone().to_vec(),
        }
    }
}

impl<T: Copy + Default> FromIterator<T> for SmallStack<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> SmallStack<T> {
        SmallStack::from_stack(Vector::from_iter(iter))
    }
}
