//! Implementation of nightly-only language features

use std::ops::{Bound, RangeBounds};

/// Replacement for `#![feature(range_contains)]`
pub(crate) trait RangeContainsExt<T> {
    fn contains_item<U>(&self, item: &U) -> bool
    where
        T: PartialOrd<U>,
        U: ?Sized + PartialOrd<T>;
}

impl<T, R> RangeContainsExt<T> for R
where
    R: RangeBounds<T>,
{
    fn contains_item<U>(&self, item: &U) -> bool
    where
        T: PartialOrd<U>,
        U: ?Sized + PartialOrd<T>,
    {
        (match self.start_bound() {
            Bound::Included(ref start) => *start <= item,
            Bound::Excluded(ref start) => *start < item,
            Bound::Unbounded => true,
        }) && (match self.end_bound() {
            Bound::Included(ref end) => item <= *end,
            Bound::Excluded(ref end) => item < *end,
            Bound::Unbounded => true,
        })
    }
}
