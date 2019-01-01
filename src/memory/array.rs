use crate::memory::{Offset, Slice, SliceMut, Stack};
use std::{
    marker::PhantomData,
    ops::{Index, IndexMut},
};

/// Map data structure with contiguous storage.
///
/// The first template argument is the type that is used for indexing.
///
/// The array is allocated at construction time, i.e. the maximum capacity needs to be known
/// already.
#[derive(Debug)]
pub struct Array<I: Offset, T: Clone> {
    // TODO replace by ptr
    vec: Stack<T>,
    phantom: PhantomData<I>,
}

impl<I: Offset, T: Clone> Array<I, T> {
    pub fn new(value: T, size: usize) -> Array<I, T> {
        Array {
            vec: Stack::from_vec(vec![value; size]),
            phantom: PhantomData,
        }
    }
    pub fn from(vector: Stack<T>) -> Array<I, T> {
        Array {
            vec: vector,
            phantom: PhantomData,
        }
    }
    pub fn len(&self) -> usize {
        self.vec.len()
    }
    // TODO avoid bounds checking
    pub fn as_slice(&self) -> Slice<T> {
        self.vec.as_slice()
    }
    pub fn as_mut_slice(&mut self) -> SliceMut<T> {
        self.vec.as_mut_slice()
    }
}

impl<I: Offset, T: Clone> Index<I> for Array<I, T> {
    type Output = T;
    fn index(&self, key: I) -> &T {
        &self.vec[key.as_offset()]
    }
}

impl<I: Offset, T: Clone> IndexMut<I> for Array<I, T> {
    fn index_mut(&mut self, key: I) -> &mut T {
        &mut self.vec[key.as_offset()]
    }
}
