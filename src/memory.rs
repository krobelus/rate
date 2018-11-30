//! Strongly-typed Data structures that optionally do not perform bounds
//! checking by default and avoid allocations.

use crate::config::BOUNDS_CHECKING;
use std::{
    iter::IntoIterator,
    marker::PhantomData,
    ops::{Index, IndexMut},
    slice,
};

/// Trait for types that can be used as index in an array.
pub trait Offset {
    fn as_offset(self) -> usize;
}

impl Offset for usize {
    fn as_offset(self) -> usize {
        self
    }
}

/// Map data structure with contiguous storage.
///
/// The first template argument is the type that is used for indexing.
///
/// The array is allocated at construction time, i.e. the maximum capacity needs to be known
/// already.
#[derive(Debug, PartialEq, Eq)]
pub struct TypedArray<I: Offset, T: Clone> {
    vec: Vec<T>,
    phantom: PhantomData<I>,
}

/// Stack data structure.
///
/// Similar to TypedArray, the maximum size of the stack needs to be passed to Stack::new().
#[derive(Debug, PartialEq, Eq)]
pub struct Stack<T: Clone> {
    vec: TypedArray<usize, T>,
    size: usize,
}

impl<'a, I: Offset, T: Clone> IntoIterator for &'a TypedArray<I, T> {
    type Item = &'a T;
    type IntoIter = slice::Iter<'a, T>;

    fn into_iter(self) -> slice::Iter<'a, T> {
        self.vec.iter()
    }
}

impl<I: Offset, T: Clone> Index<I> for TypedArray<I, T> {
    type Output = T;
    fn index(&self, index: I) -> &T {
        get(&self.vec, index.as_offset())
    }
}

impl<I: Offset, T: Clone> IndexMut<I> for TypedArray<I, T> {
    fn index_mut(&mut self, index: I) -> &mut T {
        get_mut(&mut self.vec, index.as_offset())
    }
}

impl<T: Clone> Stack<T> {
    pub fn new(value: T, size: usize) -> Stack<T> {
        Stack {
            vec: TypedArray::new(value, size),
            size: 0,
        }
    }
    pub fn len(&self) -> usize {
        self.size
    }
    pub fn push(&mut self, value: T) {
        ensure!(self.size < self.vec.capacity());
        self.vec[self.size] = value;
        self.size += 1
    }
    pub fn pop(&mut self) -> &T {
        ensure!(self.size != 0);
        self.size -= 1;
        &self.vec[self.size]
    }
    pub fn clear(&mut self) {
        self.size = 0;
    }
}

impl<'a, T: Clone> IntoIterator for &'a Stack<T> {
    type Item = &'a T;
    type IntoIter = slice::Iter<'a, T>;
    fn into_iter(self) -> slice::Iter<'a, T> {
        self.vec.vec[0..self.size].into_iter()
    }
}

impl<I: Offset, T: Clone> TypedArray<I, T> {
    pub fn new(value: T, size: usize) -> TypedArray<I, T> {
        TypedArray {
            vec: vec![value; size],
            phantom: PhantomData,
        }
    }
    pub fn from(vector: Vec<T>) -> TypedArray<I, T> {
        TypedArray {
            vec: vector,
            phantom: PhantomData,
        }
    }
    pub fn capacity(&self) -> usize {
        self.vec.len()
    }
}

fn get<T>(vec: &Vec<T>, offset: usize) -> &T {
    if BOUNDS_CHECKING {
        &vec[offset]
    } else {
        unsafe { vec.get_unchecked(offset) }
    }
}

fn get_mut<T>(vec: &mut Vec<T>, offset: usize) -> &mut T {
    if BOUNDS_CHECKING {
        &mut vec[offset]
    } else {
        unsafe { vec.get_unchecked_mut(offset) }
    }
}
