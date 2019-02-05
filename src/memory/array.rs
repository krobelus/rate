//! A dynamic array.

use crate::memory::{Offset, Stack};
use alloc::raw_vec::RawVec;
use std::{
    fmt,
    fmt::Debug,
    marker::PhantomData,
    mem::forget,
    ops::{Index, IndexMut},
    ptr,
    ptr::write,
    slice,
};

/// Map data structure with contiguous storage.
///
/// The first template argument is the type that is used for indexing.
///
/// The array is allocated at construction time, i.e. the maximum capacity needs to be known
/// already.

pub struct Array<I: Offset, T: Clone> {
    vec: RawVec<T>,
    phantom: PhantomData<I>,
}

impl<I: Offset, T: Clone> Array<I, T> {
    pub fn new(value: T, size: usize) -> Array<I, T> {
        // optimize zero?
        let vec = RawVec::with_capacity(size);
        for i in 0..size {
            unsafe {
                write((vec.ptr() as *mut T).offset(i as isize), value.clone());
            }
        }
        Array {
            vec: vec,
            phantom: PhantomData,
        }
    }
    pub fn with_capacity(size: usize) -> Array<I, T> {
        Array {
            vec: RawVec::with_capacity(size),
            phantom: PhantomData,
        }
    }
    pub fn from(mut stack: Stack<T>) -> Array<I, T> {
        let ptr = stack.as_mut_ptr();
        let cap = stack.capacity();
        forget(stack);
        Array {
            vec: unsafe { RawVec::from_raw_parts(ptr, cap) },
            phantom: PhantomData,
        }
    }
    pub fn ptr(&self) -> *const T {
        self.vec.ptr()
    }
    pub fn mut_ptr(&self) -> *mut T {
        self.vec.ptr()
    }
    pub fn size(&self) -> usize {
        self.vec.cap()
    }
    pub fn mut_slice(&self) -> &mut [T] {
        unsafe { slice::from_raw_parts_mut(self.mut_ptr(), self.size()) }
    }
}

impl<I: Offset, T: Clone> Index<I> for Array<I, T> {
    type Output = T;
    fn index(&self, key: I) -> &T {
        unsafe { &*self.ptr().offset(key.as_offset() as isize) }
    }
}

impl<I: Offset, T: Clone> IndexMut<I> for Array<I, T> {
    fn index_mut(&mut self, key: I) -> &mut T {
        unsafe { &mut *self.vec.ptr().offset(key.as_offset() as isize) }
    }
}

impl<I: Offset, T: Clone> Clone for Array<I, T> {
    fn clone(&self) -> Self {
        let copy = Array::with_capacity(self.size());
        for i in 0..self.size() {
            unsafe {
                let value = (*self.ptr().offset(i as isize)).clone();
                write((copy.ptr() as *mut T).offset(i as isize), value);
            }
        }
        copy
    }
}

impl<I: Offset, T: Clone + Debug> Debug for Array<I, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "[")?;
        for i in 0..self.size() {
            let value = unsafe { (*self.ptr().offset(i as isize)).clone() };
            write!(f, "{:?}, ", value)?;
        }
        write!(f, "]")
    }
}

impl<I: Offset, T: Clone + PartialEq> PartialEq for Array<I, T> {
    fn eq(&self, other: &Self) -> bool {
        self.size() == other.size()
            && (0..self.size()).all(|i| unsafe {
                (*self.ptr().offset(i as isize)) == (*other.ptr().offset(i as isize))
            })
    }
}

/// If T does not implement Copy, then each member must have been initialized.
impl<I: Offset, T: Clone> Drop for Array<I, T> {
    fn drop(&mut self) {
        unsafe { ptr::drop_in_place(self.mut_slice()) }
    }
}
