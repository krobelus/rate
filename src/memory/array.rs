//! A dynamic array.

use crate::memory::{assert_in_bounds, HeapSpace, Offset, Stack};
use std::{
    marker::PhantomData,
    mem::size_of,
    ops::{Deref, DerefMut, Index, IndexMut},
};

/// Map data structure with contiguous storage.
///
/// The first template argument is the type that is used for indexing.
///
/// The array is allocated at construction time, i.e. the maximum capacity needs to be known
/// already.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Array<I: Offset, T> {
    pub data: Vec<T>,
    pub phantom: PhantomData<I>,
}

impl<I: Offset, T> Default for Array<I, T> {
    fn default() -> Array<I, T> {
        Array::with_capacity(0)
    }
}

impl<I: Offset, T: Clone> Array<I, T> {
    pub fn new(value: T, size: usize) -> Array<I, T> {
        Array {
            data: vec![value; size],
            phantom: PhantomData,
        }
    }
}
impl<I: Offset, T> Array<I, T> {
    pub fn with_capacity(size: usize) -> Array<I, T> {
        Array {
            data: Vec::with_capacity(size),
            phantom: PhantomData,
        }
    }
    pub fn from(stack: Stack<T>) -> Array<I, T> {
        Array {
            data: stack.into_vec(),
            phantom: PhantomData,
        }
    }
    // pub fn from_vec(data: Vec<T>) -> Array<I, T> {
    //     Array {
    //         data,
    //         phantom: PhantomData,
    //     }
    // }
    // pub fn ptr(&self) -> *const T {
    //     self.data.ptr()
    // }
    // pub fn mut_ptr(&self) -> *mut T {
    //     self.data.ptr()
    // }
    // pub fn size(&self) -> usize {
    //     self.data.cap()
    // }
    pub fn size(&self) -> usize {
        self.data.capacity()
    }
    // pub fn mut_slice(&mut self) -> &mut [T] {
    //     unsafe { slice::from_raw_parts_mut(self.mut_ptr(), self.size()) }
    // }
}

impl<I: Offset, T> Deref for Array<I, T> {
    type Target = [T];
    fn deref(&self) -> &[T] {
        self.data.deref()
    }
}

impl<I: Offset, T> DerefMut for Array<I, T> {
    fn deref_mut(&mut self) -> &mut [T] {
        self.data.deref_mut()
    }
}

impl<I: Offset, T> AsRef<Array<I, T>> for Array<I, T> {
    fn as_ref(&self) -> &Array<I, T> {
        self
    }
}

impl<I: Offset, T> AsMut<Array<I, T>> for Array<I, T> {
    fn as_mut(&mut self) -> &mut Array<I, T> {
        self
    }
}

impl<I: Offset, T> AsRef<[T]> for Array<I, T> {
    fn as_ref(&self) -> &[T] {
        self
    }
}

impl<I: Offset, T> AsMut<[T]> for Array<I, T> {
    fn as_mut(&mut self) -> &mut [T] {
        self
    }
}

impl<I: Offset, T> Index<I> for Array<I, T> {
    type Output = T;
    fn index(&self, key: I) -> &T {
        assert_in_bounds(0..self.size(), key.as_offset());
        unsafe { self.data.get_unchecked(key.as_offset()) }
    }
}

impl<I: Offset, T> IndexMut<I> for Array<I, T> {
    fn index_mut(&mut self, key: I) -> &mut T {
        assert_in_bounds(0..self.size(), key.as_offset());
        unsafe { self.data.get_unchecked_mut(key.as_offset()) }
    }
}

impl<I: Offset, T: HeapSpace> HeapSpace for Array<I, T> {
    fn heap_space(&self) -> usize {
        self.size() * size_of::<T>()
            + self
                .data
                .iter()
                .fold(0, |sum, item| sum + item.heap_space())
    }
}
