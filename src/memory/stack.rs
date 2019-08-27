//! A stack, much like std::vec::Vec.
//!
//! We use a different growth factor (1.5 instead of 2)

use crate::memory::HeapSpace;
use crate::{config::ENABLE_BOUNDS_CHECKING, features::RangeContainsExt};
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use std::{
    iter::FromIterator,
    mem::size_of,
    ops::{Deref, DerefMut, Index, IndexMut, Range},
    ptr, slice,
};

#[derive(Debug, Clone, Default, Eq)]
pub struct Stack<T>(Vec<T>);

impl<T> Stack<T> {
    /// ATM it's not possible to make the `new` const.
    pub fn new() -> Stack<T> {
        Stack(Vec::new())
    }
    pub fn with_capacity(capacity: usize) -> Stack<T> {
        Stack(Vec::with_capacity(capacity))
    }
    pub fn from_vec(vec: Vec<T>) -> Stack<T> {
        Stack(vec)
    }
    pub fn into_vec(self) -> Vec<T> {
        self.0
    }
    pub fn len(&self) -> usize {
        self.0.len()
    }
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
    pub fn capacity(&self) -> usize {
        self.0.capacity()
    }
    pub fn pop(&mut self) -> T {
        self.0.pop().unwrap()
    }
    pub fn first(&self) -> &T {
        requires!(!self.is_empty());
        &self[0]
    }
    pub fn last(&self) -> &T {
        requires!(!self.is_empty());
        &self[self.len() - 1]
    }
    pub fn iter(&self) -> slice::Iter<T> {
        self.0.iter()
    }
    pub fn as_ptr(&self) -> *const T {
        self.0.as_ptr()
    }
    pub fn mut_ptr(&mut self) -> *mut T {
        self.0.as_mut_ptr()
    }
    pub fn truncate(&mut self, new_length: usize) {
        self.0.truncate(new_length)
    }
    pub fn clear(&mut self) {
        self.0.clear()
    }
    pub fn push_no_grow(&mut self, value: T) {
        requires!(self.len() < self.capacity());
        unsafe {
            ptr::write(self.mut_ptr().add(self.len()), value);
            self.0.set_len(self.len() + 1)
        }
    }
    pub fn shrink_to_fit(&mut self) {
        self.0.shrink_to_fit()
    }
}

impl<T: Clone + Default> Stack<T> {
    pub fn resize(&mut self, new_length: usize) {
        self.0.resize(new_length, T::default())
    }
}

impl<T> Deref for Stack<T> {
    type Target = [T];
    fn deref(&self) -> &[T] {
        &self.0
    }
}

impl<T> DerefMut for Stack<T> {
    fn deref_mut(&mut self) -> &mut [T] {
        &mut self.0
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
    pub fn push(&mut self, value: T) {
        if self.len() == self.capacity() {
            let new_capacity = next_capacity(self);
            self.0.reserve_exact(new_capacity - self.capacity())
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
    if stack.is_empty() {
        4
    } else {
        (stack.capacity().checked_mul(3).unwrap()) / 2
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
    ($($x:expr,)*) => (stack!($($x),*))
}

impl<T: Copy> Stack<T> {
    pub fn swap_remove(&mut self, index: usize) -> T {
        // copied from Vec::swap_remove to use our own bounds checking
        unsafe {
            // We replace self[index] with the last element. Note that if the
            // bounds check on hole succeeds there must be a last element (which
            // can be self[index] itself).
            let hole: *mut T = &mut self[index];
            let last = ptr::read(self.get_unchecked(self.len() - 1));
            self.0.set_len(self.len() - 1);
            ptr::replace(hole, last)
        }
    }
}

impl<T: Ord> Stack<T> {
    pub fn sort_unstable(&mut self) {
        self.0.sort_unstable()
    }
}

impl<T> Stack<T> {
    pub fn sort_unstable_by_key<F, K>(&mut self, f: F)
    where
        F: FnMut(&T) -> K,
        K: Ord,
    {
        self.0.sort_unstable_by_key(f)
    }
}

pub fn assert_in_bounds(bounds: Range<usize>, offset: usize) {
    if ENABLE_BOUNDS_CHECKING {
        assert!(
            bounds.contains_item(&offset),
            format!(
                "array index out of bounds: {} (range is {:?})",
                offset, bounds
            )
        );
    }
}

impl<T> Index<usize> for Stack<T> {
    type Output = T;
    fn index(&self, index: usize) -> &Self::Output {
        assert_in_bounds(0..self.len(), index);
        unsafe { self.0.get_unchecked(index) }
    }
}

impl<T> Index<Range<usize>> for Stack<T> {
    type Output = [T];
    #[allow(clippy::range_plus_one)]
    fn index(&self, index: Range<usize>) -> &Self::Output {
        assert_in_bounds(0..self.len() + 1, index.start);
        assert_in_bounds(0..self.len() + 1, index.end);
        unsafe { slice::from_raw_parts(self.as_ptr().add(index.start), index.end - index.start) }
    }
}

impl<T> IndexMut<usize> for Stack<T> {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        assert_in_bounds(0..self.len(), index);
        unsafe { self.0.get_unchecked_mut(index) }
    }
}

impl<T> IndexMut<Range<usize>> for Stack<T> {
    #[allow(clippy::range_plus_one)]
    fn index_mut(&mut self, index: Range<usize>) -> &mut Self::Output {
        assert_in_bounds(0..self.len() + 1, index.start);
        assert_in_bounds(0..self.len() + 1, index.end);
        unsafe {
            slice::from_raw_parts_mut(self.mut_ptr().add(index.start), index.end - index.start)
        }
    }
}

impl<T: PartialEq> PartialEq for Stack<T> {
    fn eq(&self, other: &Self) -> bool {
        self.len() == other.len() && (0..self.len()).all(|i| self[i] == other[i])
    }
}

impl<'a, T> IntoIterator for &'a Stack<T> {
    type Item = &'a T;
    type IntoIter = slice::Iter<'a, T>;
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<T> FromIterator<T> for Stack<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Stack<T> {
        Stack(Vec::from_iter(iter))
    }
}

impl<T: HeapSpace> HeapSpace for Stack<T> {
    fn heap_space(&self) -> usize {
        self.capacity() * size_of::<T>()
            + (0..self.len()).fold(0, |sum, i| sum + self[i].heap_space())
    }
}

impl<T> IntoIterator for Stack<T> {
    type Item = T;
    type IntoIter = <Vec<T> as IntoIterator>::IntoIter;
    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<T: Clone + Serialize> Serialize for Stack<T> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        self.clone().into_vec().serialize(serializer)
    }
}

impl<'de, T: Clone + Deserialize<'de>> Deserialize<'de> for Stack<T> {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        Vec::deserialize(deserializer).map(Stack::from_vec)
    }
}
