use crate::memory::{index_vec, index_vec_mut, Offset, Slice, SliceMut};
use std::{
    iter::IntoIterator,
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
    pub vec: Vec<T>,
    phantom: PhantomData<I>,
}

impl<I: Offset, T: Clone> Array<I, T> {
    pub fn new(value: T, size: usize) -> Array<I, T> {
        Array {
            vec: vec![value; size],
            phantom: PhantomData,
        }
    }
    pub fn from(vector: Vec<T>) -> Array<I, T> {
        Array {
            vec: vector,
            phantom: PhantomData,
        }
    }
    pub fn capacity(&self) -> usize {
        self.vec.len()
    }
    // TODO avoid bounds checking
    pub fn as_slice(&self) -> Slice<T> {
        Slice::new(&self.vec[..])
    }
    pub fn as_mut_slice(&mut self) -> SliceMut<T> {
        SliceMut::new(&mut self.vec[..])
    }
}

impl<I: Offset, T: Clone> Index<I> for Array<I, T> {
    type Output = T;
    fn index(&self, key: I) -> &T {
        index_vec(&self.vec, key)
    }
}

impl<I: Offset, T: Clone> IndexMut<I> for Array<I, T> {
    fn index_mut(&mut self, key: I) -> &mut T {
        index_vec_mut(&mut self.vec, key)
    }
}

impl<'a, I: Offset, T: Clone> IntoIterator for &'a Array<I, T> {
    type Item = &'a T;
    type IntoIter = std::slice::Iter<'a, T>;

    fn into_iter(self) -> std::slice::Iter<'a, T> {
        self.vec.iter()
    }
}
