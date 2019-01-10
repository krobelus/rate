use crate::{config::BOUNDS_CHECKING, memory::Stack};

use std::{
    ops::{Index, IndexMut},
    slice,
};

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct Slice<'a, T> {
    slice: &'a [T],
}

#[derive(Debug)]
pub struct SliceMut<'a, T> {
    slice: &'a mut [T],
}

impl<'a, T> Slice<'a, T> {
    pub fn new(slice: &'a [T]) -> Slice<'a, T> {
        Slice { slice: slice }
    }
    pub fn len(&self) -> usize {
        self.slice.len()
    }
    pub fn empty(&self) -> bool {
        self.len() == 0
    }
    // TODO rename to slice
    pub fn range(&self, start: usize, end: usize) -> Slice<'a, T> {
        let slice = unsafe { slice::from_raw_parts(self.slice.as_ptr().add(start), end - start) };
        Slice::new(slice)
    }
    // TODO avoid bounds checking
    pub fn iter(&self) -> std::slice::Iter<T> {
        self.slice.iter()
    }
    pub fn slice(&self) -> &'a [T] {
        self.slice
    }
}

impl<'a, T: Clone> Slice<'a, T> {
    pub fn to_vec(&self) -> Vec<T> {
        self.slice.to_vec()
    }
    pub fn to_stack(&self) -> Stack<T> {
        Stack::from_vec(self.to_vec())
    }
}

#[allow(dead_code)]
impl<'a, T> SliceMut<'a, T> {
    pub fn new(slice: &'a mut [T]) -> SliceMut<'a, T> {
        SliceMut { slice: slice }
    }
    pub fn len(&self) -> usize {
        self.slice.len()
    }
    pub fn as_const(&self) -> Slice<T> {
        Slice::new(self.slice)
    }
    pub fn range(&mut self, start: usize, end: usize) -> SliceMut<'a, T> {
        let slice = unsafe {
            std::slice::from_raw_parts_mut(self.slice.as_mut_ptr().add(start), end - start)
        };
        SliceMut::new(slice)
    }
    // TODO avoid bounds checking
    pub fn iter(&self) -> std::slice::Iter<T> {
        self.slice.iter()
    }
}

impl<'a, T: Copy> SliceMut<'a, T> {
    pub fn swap(&mut self, a: usize, b: usize) {
        let tmp = self[a];
        self[a] = self[b];
        self[b] = tmp;
    }
}

impl<'a, T> Index<usize> for Slice<'a, T> {
    type Output = T;
    fn index(&self, offset: usize) -> &T {
        if BOUNDS_CHECKING {
            &self.slice[offset]
        } else {
            unsafe { self.slice.get_unchecked(offset) }
        }
    }
}

impl<'a, T> Index<usize> for SliceMut<'a, T> {
    type Output = T;
    fn index(&self, offset: usize) -> &T {
        if BOUNDS_CHECKING {
            &self.slice[offset]
        } else {
            unsafe { &self.slice.get_unchecked(offset) }
        }
    }
}
impl<'a, T> IndexMut<usize> for SliceMut<'a, T> {
    fn index_mut(&mut self, offset: usize) -> &mut T {
        if BOUNDS_CHECKING {
            &mut self.slice[offset]
        } else {
            unsafe { self.slice.get_unchecked_mut(offset) }
        }
    }
}

// TODO avoid bounds checking
impl<'a, T> IntoIterator for Slice<'a, T> {
    type Item = &'a T;
    type IntoIter = std::slice::Iter<'a, T>;
    fn into_iter(self) -> Self::IntoIter {
        self.slice.into_iter()
    }
}

// TODO avoid bounds checking
impl<'a, T> IntoIterator for SliceMut<'a, T> {
    type Item = &'a mut T;
    type IntoIter = std::slice::IterMut<'a, T>;
    fn into_iter(self) -> Self::IntoIter {
        self.slice.into_iter()
    }
}

impl<'a, T: Ord> SliceMut<'a, T> {
    pub fn sort_unstable(&mut self) {
        self.slice.sort_unstable()
    }
}

impl<'a, T> SliceMut<'a, T> {
    pub fn sort_unstable_by_key<K, F>(&mut self, f: F)
    where
        F: FnMut(&T) -> K,
        K: Ord,
    {
        self.slice.sort_unstable_by_key(f)
    }
}
