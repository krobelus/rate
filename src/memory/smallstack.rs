//! A stack that does not allocate if it is contains less than 2 elements.

use crate::{config::unreachable, memory::Stack};

use std::iter::FromIterator;

#[derive(Debug, PartialEq, Clone)]
enum SmallStackState<T> {
    Empty,
    One(T),
    Many(Stack<T>),
}

#[derive(Debug, PartialEq, Clone)]
pub struct SmallStack<T> {
    state: SmallStackState<T>,
}

impl<T: Copy + Default> SmallStack<T> {
    pub fn new() -> SmallStack<T> {
        SmallStack {
            state: SmallStackState::Empty,
        }
    }
    #[allow(dead_code)]
    pub fn singleton(value: T) -> SmallStack<T> {
        SmallStack {
            state: SmallStackState::One(value),
        }
    }
    pub fn from_stack(stack: Stack<T>) -> SmallStack<T> {
        SmallStack {
            state: SmallStackState::Many(stack),
        }
    }
    pub fn push(&mut self, new_value: T) {
        if let SmallStackState::Empty = self.state {
            self.state = SmallStackState::One(new_value);
            return;
        }
        if let SmallStackState::One(value) = self.state {
            self.state = SmallStackState::Many(stack!(value));
        }
        if let SmallStackState::Many(stack) = &mut self.state {
            stack.push(new_value);
            return;
        }
        unreachable();
    }
    pub fn swap_remove(&mut self, index: usize) -> Option<T> {
        requires!(index == 0);
        if let SmallStackState::One(value) = self.state {
            self.state = SmallStackState::Empty;
            Some(value)
        } else if let SmallStackState::Many(stack) = &mut self.state {
            if stack.empty() {
                None
            } else {
                Some(stack.swap_remove(0))
            }
        } else {
            None
        }
    }
    #[allow(dead_code)]
    pub fn to_vec(&self) -> Vec<T> {
        match &self.state {
            SmallStackState::Empty => vec![],
            SmallStackState::One(value) => vec![*value],
            SmallStackState::Many(stack) => stack.clone().to_vec(),
        }
    }
}

impl<T: Copy + Default> FromIterator<T> for SmallStack<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> SmallStack<T> {
        SmallStack::from_stack(Stack::from_iter(iter))
    }
}
