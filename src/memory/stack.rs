//! A stack, much like std::vec::Vec.
//!
//! We use a different growth factor (1.5 instead of 2)

use crate::{
    config::ENABLE_BOUNDS_CHECKING,
    memory::{Array, HeapSpace, Slice, SliceMut},
};
use alloc::raw_vec::RawVec;
use std::{
    cmp::max,
    iter::FromIterator,
    marker::PhantomData,
    mem::{self, size_of},
    ops::{Deref, DerefMut, Index, IndexMut},
};

#[derive(Debug, Clone)]
pub struct Stack<T> {
    array: Array<usize, T>,
    len: usize,
}

impl<T> Default for Stack<T> {
    fn default() -> Stack<T> {
        Stack::new()
    }
}

impl<T> Stack<T> {
    /// ATM it's not possible to make the `new` const.
    pub const fn const_new() -> Stack<T> {
        Stack {
            array: Array {
                data: RawVec::new(),
                phantom: PhantomData,
            },
            len: 0,
        }
    }
    pub fn new() -> Stack<T> {
        Stack {
            array: Array::with_capacity(0),
            len: 0,
        }
    }
    pub fn with_capacity(capacity: usize) -> Stack<T> {
        Stack {
            array: Array::with_capacity(capacity),
            len: 0,
        }
    }
    pub fn from_vec(vec: Vec<T>) -> Stack<T> {
        let len = vec.len();
        Stack {
            array: Array::from_vec(vec),
            len: len,
        }
    }
    pub fn len(&self) -> usize {
        self.len
    }
    pub fn empty(&self) -> bool {
        self.len() == 0
    }
    pub fn capacity(&self) -> usize {
        self.array.size()
    }
    pub fn pop(&mut self) -> T {
        // We should change this to return an `Option<T>`
        requires!(!self.empty());
        self.len -= 1;
        unsafe { std::ptr::read(self.get_unchecked(self.len())) }
    }
    pub fn first(&self) -> &T {
        requires!(!self.empty());
        &self[0]
    }
    pub fn last(&self) -> &T {
        requires!(!self.empty());
        &self[self.len() - 1]
    }
    pub fn iter(&self) -> StackIterator<T> {
        self.array.iter().take(self.len())
    }
    pub fn as_slice(&self) -> Slice<T> {
        Slice::from_ref(self).range(0, self.len())
    }
    pub fn mut_slice(&mut self) -> SliceMut<T> {
        SliceMut::new(&mut self.array).range(0, self.len)
    }
    pub fn as_ptr(&mut self) -> *const T {
        self.array.as_ptr()
    }
    pub fn mut_ptr(&mut self) -> *mut T {
        self.array.mut_ptr()
    }
    pub fn truncate(&mut self, new_length: usize) {
        while self.len() > new_length {
            self.pop();
        }
    }
    pub fn set_len(&mut self, new_length: usize) {
        self.len = new_length
    }
    pub fn clear(&mut self) {
        self.truncate(0)
    }
    pub fn push_no_grow(&mut self, value: T) {
        requires!(self.len() < self.capacity());
        unsafe {
            let end = self.mut_ptr().add(self.len);
            std::ptr::write(end, value);
            self.len += 1;
        }
    }
}

impl<T> Deref for Stack<T> {
    type Target = [T];
    fn deref(&self) -> &[T] {
        &self.array
    }
}

impl<T> DerefMut for Stack<T> {
    fn deref_mut(&mut self) -> &mut [T] {
        &mut self.array
    }
}

impl<T> AsRef<Stack<T>> for Stack<T> {
    fn as_ref(&self) -> &Stack<T> {
        self
    }
}

impl<T> AsMut<Stack<T>> for Stack<T> {
    fn as_mut(&mut self) -> &mut Stack<T> {
        self
    }
}

impl<T> AsRef<[T]> for Stack<T> {
    fn as_ref(&self) -> &[T] {
        self
    }
}

impl<T> AsMut<[T]> for Stack<T> {
    fn as_mut(&mut self) -> &mut [T] {
        self
    }
}

impl<T: Clone + Default> Stack<T> {
    pub fn grow(&mut self, new_capacity: usize) {
        self.array.grow(new_capacity, T::default());
    }
    pub fn push(&mut self, value: T) {
        if self.len() == self.capacity() {
            let new_capacity = next_capacity(self);
            self.grow(new_capacity);
        }
        self.push_no_grow(value)
    }
    pub fn fill(size: usize, default_value: T) -> Stack<T> {
        let mut result = Stack::new();
        for _ in 0..size {
            result.push(default_value.clone());
        }
        result
    }
}

// Related: https://github.com/rust-lang/rust/issues/29931
fn next_capacity<T>(stack: &Stack<T>) -> usize {
    if stack.empty() {
        max(64 / size_of::<T>(), 1)
    } else {
        (stack.capacity() * 3 + 1) / 2
    }
}

#[allow(unused_macros)]
macro_rules! stack {
    ($($x:expr),*) => (
        {
            #[allow(unused_mut)]
            let mut result = Stack::new();
            $(
                result.push($x);
            )*
            result
        }
    );
    ($($x:expr,)*) => (stack![$($x),*])
}

impl<T: Copy> Stack<T> {
    pub fn swap_remove(&mut self, offset: usize) -> T {
        let value = self[offset];
        self[offset] = self[self.len() - 1];
        self.pop();
        value
    }
}

impl<T: Ord> Stack<T> {
    pub fn sort_unstable(&mut self) {
        self.mut_slice().sort_unstable()
    }
}

impl<T> Stack<T> {
    pub fn sort_unstable_by_key<F, K>(&mut self, f: F)
    where
        F: FnMut(&T) -> K,
        K: Ord,
    {
        self.mut_slice().sort_unstable_by_key(f)
    }
}

impl<T> Index<usize> for Stack<T> {
    type Output = T;
    fn index(&self, offset: usize) -> &T {
        if ENABLE_BOUNDS_CHECKING {
            assert!((0..self.len()).contains(&offset));
            &self.array[offset]
        } else {
            unsafe { self.array.get_unchecked(offset) }
        }
    }
}

impl<T> IndexMut<usize> for Stack<T> {
    fn index_mut(&mut self, offset: usize) -> &mut T {
        if ENABLE_BOUNDS_CHECKING {
            assert!((0..self.len()).contains(&offset));
            &mut self.array[offset]
        } else {
            unsafe { self.array.get_unchecked_mut(offset) }
        }
    }
}

impl<T: PartialEq> PartialEq for Stack<T> {
    fn eq(&self, other: &Self) -> bool {
        self.len() == other.len() && (0..self.len()).all(|i| self[i] == other[i])
    }
}

pub type StackIterator<'a, T> = std::iter::Take<std::slice::Iter<'a, T>>;

impl<'a, T> IntoIterator for &'a Stack<T> {
    type Item = &'a T;
    type IntoIter = StackIterator<'a, T>;
    fn into_iter(self) -> StackIterator<'a, T> {
        self.iter()
    }
}

impl<T> FromIterator<T> for Stack<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Stack<T> {
        Stack::from_vec(Vec::from_iter(iter))
    }
}

impl<T: HeapSpace> HeapSpace for Stack<T> {
    fn heap_space(&self) -> usize {
        self.capacity() * size_of::<T>()
            + (0..self.len()).fold(0, |sum, i| sum + self[i].heap_space())
    }
}

pub struct ConsumingStackIterator<T> {
    buf: *mut T,
    cap: usize,
    ptr: *const T,
    end: *const T,
}

/// Very similar to Vec::into_iter()
impl<T> IntoIterator for Stack<T> {
    type Item = T;
    type IntoIter = ConsumingStackIterator<T>;
    fn into_iter(mut self) -> ConsumingStackIterator<T> {
        unsafe {
            let begin = self.mut_ptr();
            requires!(!begin.is_null());
            requires!(size_of::<T>() != 0);
            let end = begin.add(self.len()) as *const T;
            let cap = self.capacity();
            mem::forget(self);
            ConsumingStackIterator {
                buf: begin,
                cap,
                ptr: begin,
                end,
            }
        }
    }
}

impl<T> Iterator for ConsumingStackIterator<T> {
    type Item = T;
    fn next(&mut self) -> Option<T> {
        if self.ptr as *const _ == self.end {
            None
        } else {
            let old = self.ptr;
            unsafe {
                self.ptr = self.ptr.add(1);
                Some(std::ptr::read(old))
            }
        }
    }
}

impl<T> Drop for ConsumingStackIterator<T> {
    fn drop(&mut self) {
        // destroy the remaining elements
        for _x in self.by_ref() {}

        // RawVec handles deallocation
        let _ = unsafe { RawVec::from_raw_parts(self.buf, self.cap) };
    }
}
