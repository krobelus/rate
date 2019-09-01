//! A thin wrapper around std::vec::Vec
//!
//! See https://doc.rust-lang.org/std/vec/struct.Vec.html
//!
//! We use a different growth factor (1.5 instead of 2).

use crate::memory::HeapSpace;
use crate::{config::ENABLE_BOUNDS_CHECKING, features::RangeContainsExt};
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use static_assertions::const_assert;
use std::{
    iter::FromIterator,
    mem::size_of,
    ops::{Deref, DerefMut, Index, IndexMut, Range},
    ptr, slice,
};

#[derive(Debug, Clone, Default, Eq)]
pub struct Vector<T>(Vec<T>);

impl<T> Vector<T> {
    /// Currently it's not possible to make the `new` const.
    pub fn new() -> Vector<T> {
        Vector(Vec::new())
    }
    pub fn with_capacity(capacity: usize) -> Vector<T> {
        Vector(Vec::with_capacity(capacity))
    }
    pub fn from_vec(vec: Vec<T>) -> Vector<T> {
        Vector(vec)
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

impl<T: Clone + Default> Vector<T> {
    pub fn resize(&mut self, new_length: usize) {
        self.0.resize(new_length, T::default())
    }
}

impl<T> Deref for Vector<T> {
    type Target = [T];
    fn deref(&self) -> &[T] {
        &self.0
    }
}

impl<T> DerefMut for Vector<T> {
    fn deref_mut(&mut self) -> &mut [T] {
        &mut self.0
    }
}

impl<T> AsRef<Vector<T>> for Vector<T> {
    fn as_ref(&self) -> &Vector<T> {
        self
    }
}

impl<T> AsMut<Vector<T>> for Vector<T> {
    fn as_mut(&mut self) -> &mut Vector<T> {
        self
    }
}

impl<T> AsRef<[T]> for Vector<T> {
    fn as_ref(&self) -> &[T] {
        self
    }
}

impl<T> AsMut<[T]> for Vector<T> {
    fn as_mut(&mut self) -> &mut [T] {
        self
    }
}

impl<T: Clone + Default> Vector<T> {
    pub fn push(&mut self, value: T) {
        if self.len() == self.capacity() {
            let new_capacity = next_capacity(self);
            self.0.reserve_exact(new_capacity - self.capacity())
        }
        self.push_no_grow(value)
    }
    pub fn fill(size: usize, default_value: T) -> Vector<T> {
        let mut result = Vector::new();
        for _ in 0..size {
            result.push(default_value.clone());
        }
        result
    }
}

// Related: https://github.com/rust-lang/rust/issues/29931
fn next_capacity<T>(vector: &Vector<T>) -> usize {
    if vector.is_empty() {
        4
    } else {
        // Assuming we are running on a 64 bit system, this will not overflow
        // for our expected input sizes.
        const_assert!(size_of::<usize>() >= 8);
        vector.capacity() * 3 / 2
    }
}

#[allow(unused_macros)]
macro_rules! vector {
    ($($x:expr),*) => (
        {
            #[allow(unused_mut)]
            let mut result = Vector::new();
            $(
                result.push($x);
            )*
            result
        }
    );
    ($($x:expr,)*) => (vector!($($x),*))
}

impl<T: Copy> Vector<T> {
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

impl<T: Ord> Vector<T> {
    pub fn sort_unstable(&mut self) {
        self.0.sort_unstable()
    }
}

impl<T> Vector<T> {
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

impl<T> Index<usize> for Vector<T> {
    type Output = T;
    fn index(&self, index: usize) -> &Self::Output {
        assert_in_bounds(0..self.len(), index);
        unsafe { self.0.get_unchecked(index) }
    }
}

impl<T> Index<Range<usize>> for Vector<T> {
    type Output = [T];
    #[allow(clippy::range_plus_one)]
    fn index(&self, index: Range<usize>) -> &Self::Output {
        assert_in_bounds(0..self.len() + 1, index.start);
        assert_in_bounds(0..self.len() + 1, index.end);
        unsafe { slice::from_raw_parts(self.as_ptr().add(index.start), index.end - index.start) }
    }
}

impl<T> IndexMut<usize> for Vector<T> {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        assert_in_bounds(0..self.len(), index);
        unsafe { self.0.get_unchecked_mut(index) }
    }
}

impl<T> IndexMut<Range<usize>> for Vector<T> {
    #[allow(clippy::range_plus_one)]
    fn index_mut(&mut self, index: Range<usize>) -> &mut Self::Output {
        assert_in_bounds(0..self.len() + 1, index.start);
        assert_in_bounds(0..self.len() + 1, index.end);
        unsafe {
            slice::from_raw_parts_mut(self.mut_ptr().add(index.start), index.end - index.start)
        }
    }
}

impl<T: PartialEq> PartialEq for Vector<T> {
    fn eq(&self, other: &Self) -> bool {
        self.len() == other.len() && (0..self.len()).all(|i| self[i] == other[i])
    }
}

impl<'a, T> IntoIterator for &'a Vector<T> {
    type Item = &'a T;
    type IntoIter = slice::Iter<'a, T>;
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<T> FromIterator<T> for Vector<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Vector<T> {
        Vector(Vec::from_iter(iter))
    }
}

impl<T: HeapSpace> HeapSpace for Vector<T> {
    fn heap_space(&self) -> usize {
        self.capacity() * size_of::<T>()
            + (0..self.len()).fold(0, |sum, i| sum + self[i].heap_space())
    }
}

impl<T> IntoIterator for Vector<T> {
    type Item = T;
    type IntoIter = <Vec<T> as IntoIterator>::IntoIter;
    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<T: Clone + Serialize> Serialize for Vector<T> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        self.clone().into_vec().serialize(serializer)
    }
}

impl<'de, T: Clone + Deserialize<'de>> Deserialize<'de> for Vector<T> {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        Vec::deserialize(deserializer).map(Vector::from_vec)
    }
}
