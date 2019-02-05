//! Data structures for the checker.

use derive_more::Add;

use crate::memory::Offset;
use std::{
    fmt,
    ops::{Add, AddAssign, Sub, SubAssign},
};

/// The index of a clause or lemma, immutable during the lifetime of the program.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Add, Hash)]
pub struct Clause(pub usize);

impl Clause {
    pub fn range(start: impl Offset, end: impl Offset) -> impl Iterator<Item = Clause> {
        (start.as_offset()..end.as_offset()).map(Clause)
    }

    pub const NEVER_READ: Clause = Clause(usize::max_value());
    pub const DOES_NOT_EXIST: Clause = Clause(usize::max_value());
    pub const UNINITIALIZED: Clause = Clause(usize::max_value());
}

impl Offset for Clause {
    fn as_offset(self) -> usize {
        self.0
    }
}

impl Add<usize> for Clause {
    type Output = Clause;
    fn add(self, value: usize) -> Clause {
        Clause(self.0 + value)
    }
}

impl AddAssign<usize> for Clause {
    fn add_assign(&mut self, value: usize) {
        self.0 += value;
    }
}

impl Sub<usize> for Clause {
    type Output = Clause;
    fn sub(self, value: usize) -> Clause {
        Clause(self.0 - value)
    }
}

impl SubAssign<usize> for Clause {
    fn sub_assign(&mut self, value: usize) {
        self.0 -= value;
    }
}

impl fmt::Display for Clause {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum ProofStep {
    Lemma(Clause),
    Deletion(Clause),
}
