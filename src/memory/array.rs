//! A dynamic array.

use crate::{memory::{HeapSpace, Offset, Stack}, config::ENABLE_BOUNDS_CHECKING};
use alloc::raw_vec::RawVec;
use std::{
    fmt,
    fmt::Debug,
    marker::PhantomData,
    mem::{forget, size_of},
    ops::{Deref, DerefMut, Index, IndexMut},
    ptr::write,
    slice,
};

/// Map data structure with contiguous storage.
///
/// The first template argument is the type that is used for indexing.
///
/// The array is allocated at construction time, i.e. the maximum capacity needs to be known
/// already.
pub struct Array<I: Offset, T> {
    pub data: RawVec<T>,
    pub phantom: PhantomData<I>,
}

impl<I: Offset, T> Default for Array<I, T> {
    fn default() -> Array<I, T> {
        Array::with_capacity(0)
    }
}

impl<I: Offset, T: Clone> Array<I, T> {
    pub fn new(value: T, size: usize) -> Array<I, T> {
        // optimize zero?
        let data = RawVec::with_capacity(size);
        for i in 0..size {
            unsafe {
                write((data.ptr() as *mut T).offset(i as isize), value.clone());
            }
        }
        Array {
            data: data,
            phantom: PhantomData,
        }
    }
    pub fn grow(&mut self, new_size: usize, value: T) {
        requires!(new_size > self.size());
        let old_size = self.size();
        let needed = new_size - old_size;
        self.data.reserve(old_size, needed);
        for offset in old_size..new_size {
            unsafe {
                write(self.mut_ptr().add(offset), value.clone());
            }
        }
    }
}
impl<I: Offset, T> Array<I, T> {
    pub fn with_capacity(size: usize) -> Array<I, T> {
        Array {
            data: RawVec::with_capacity(size),
            phantom: PhantomData,
        }
    }
    pub fn from(mut stack: Stack<T>) -> Array<I, T> {
        let ptr = stack.as_mut_ptr();
        let cap = stack.len();
        forget(stack);
        Array {
            data: unsafe { RawVec::from_raw_parts(ptr, cap) },
            phantom: PhantomData,
        }
    }
    pub fn from_vec(mut vec: Vec<T>) -> Array<I, T> {
        let ptr = vec.as_mut_ptr();
        let cap = vec.capacity();
        forget(vec);
        Array {
            data: unsafe { RawVec::from_raw_parts(ptr, cap) },
            phantom: PhantomData,
        }
    }
    pub fn ptr(&self) -> *const T {
        self.data.ptr()
    }
    pub fn mut_ptr(&self) -> *mut T {
        self.data.ptr()
    }
    pub fn size(&self) -> usize {
        self.data.cap()
    }
    pub fn mut_slice(&self) -> &mut [T] {
        unsafe { slice::from_raw_parts_mut(self.mut_ptr(), self.size()) }
    }
}

impl<I: Offset, T> Deref for Array<I, T> {
    type Target = [T];
    fn deref(&self) -> &[T] {
        unsafe {
            let p = self.ptr();
            invariant!(!p.is_null());
            slice::from_raw_parts(p, self.size())
        }
    }
}

impl<I: Offset, T> DerefMut for Array<I, T> {
    fn deref_mut(&mut self) -> &mut [T] {
        unsafe {
            let ptr = self.mut_ptr();
            invariant!(!ptr.is_null());
            slice::from_raw_parts_mut(ptr, self.size())
        }
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
        if ENABLE_BOUNDS_CHECKING {
            assert!((0..self.size()).contains(&key.as_offset()));
        }
        unsafe { &*self.ptr().add(key.as_offset()) }
    }
}

impl<I: Offset, T> IndexMut<I> for Array<I, T> {
    fn index_mut(&mut self, key: I) -> &mut T {
        if ENABLE_BOUNDS_CHECKING {
            assert!((0..self.size()).contains(&key.as_offset()));
        }
        unsafe { &mut *self.data.ptr().add(key.as_offset()) }
    }
}

impl<I: Offset, T: Clone> Clone for Array<I, T> {
    fn clone(&self) -> Self {
        let copy = Array::with_capacity(self.size());
        for i in 0..self.size() {
            unsafe {
                let value = (*self.ptr().add(i)).clone();
                write((copy.ptr() as *mut T).offset(i as isize), value);
            }
        }
        copy
    }
}

impl<I: Offset, T> Debug for Array<I, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "[array of size {}]", self.size())
    }
}

impl<I: Offset, T: PartialEq> PartialEq for Array<I, T> {
    fn eq(&self, other: &Self) -> bool {
        self.size() == other.size()
            && (0..self.size()).all(|i| unsafe {
                (*self.ptr().offset(i as isize)) == (*other.ptr().offset(i as isize))
            })
    }
}

/// If T does not implement Copy, then each member must have been initialized.
impl<I: Offset, T> Drop for Array<I, T> {
    fn drop(&mut self) {
        unsafe { std::ptr::drop_in_place(self.mut_slice()) }
    }
}

impl<I: Offset, T: HeapSpace> HeapSpace for Array<I, T> {
    fn heap_space(&self) -> usize {
        self.size() * size_of::<T>()
            + (0..self.size()).fold(0, |sum, i| {
                sum + unsafe { &(*self.ptr().offset(i as isize)) }.heap_space()
            })
    }
}
