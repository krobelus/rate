//! Data structures for the checker.

use crate::{
    literal::Literal,
    memory::{Offset, TypedArray},
};
use std::{
    fmt, ops,
    ops::{Add, AddAssign, Sub, SubAssign},
    slice,
};

/// The index of a clause or lemma, immutable during the lifetime of the program.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Add)]
pub struct Clause(pub usize);

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

pub fn clause_as_slice<'a>(
    db: &'a TypedArray<usize, Literal>,
    clause_offset: &TypedArray<Clause, usize>,
    c: Clause,
) -> &'a [Literal] {
    &db.as_slice()[clause_offset[c]..clause_offset[c + 1]]
}

/// A lemma in a DRAT proof.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Lemma {
    Addition(Clause),
    Deletion(Clause),
}

#[derive(PartialEq, Eq, Clone, Copy)]
pub struct ClauseView<'a> {
    pub id: Clause,
    pub literals: &'a [Literal],
}

impl<'a> ClauseView<'a> {
    pub fn new(id: Clause, literals: &'a [Literal]) -> ClauseView {
        ClauseView {
            id: id,
            literals: literals,
        }
    }
}

impl<'a> ClauseView<'a> {
    pub fn len(&self) -> usize {
        self.literals.len()
    }
    pub fn iter(self) -> slice::Iter<'a, Literal> {
        self.literals.into_iter()
    }
}

impl<'a> IntoIterator for ClauseView<'a> {
    type Item = &'a Literal;
    type IntoIter = slice::Iter<'a, Literal>;
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a> fmt::Display for ClauseView<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for literal in self.literals {
            write!(f, "{} ", literal)?;
        }
        write!(f, "0")
    }
}

impl<'a> ops::Index<usize> for ClauseView<'a> {
    type Output = Literal;
    fn index(&self, offset: usize) -> &Literal {
        &self.literals[offset]
    }
}
