//! Data structures for the checker.

use derive_more::Add;

use crate::{
    literal::Literal,
    memory::{Offset, Stack},
};
use std::{
    fmt, ops,
    ops::{Add, AddAssign, Sub, SubAssign},
};

/// The index of a clause or lemma, immutable during the lifetime of the program.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Add)]
pub struct Clause(pub usize);

pub const CLAUSE_SENTINEL: Clause = Clause(usize::max_value());

impl Clause {
    pub fn range(start: impl Offset, end: impl Offset) -> impl Iterator<Item = Clause> {
        (start.as_offset()..end.as_offset()).map(Clause)
    }
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

#[derive(Debug)]
pub struct ClauseCopy {
    pub id: Clause,
    pub literals: Stack<Literal>,
}

impl<'a> ClauseCopy {
    pub fn new(id: Clause, literals: &[Literal]) -> ClauseCopy {
        ClauseCopy {
            id: id,
            literals: Stack::from_vec(literals.to_vec()),
        }
    }
    pub fn iter(&'a self) -> std::slice::Iter<'a, Literal> {
        self.into_iter()
    }
}

impl<'a> IntoIterator for &'a ClauseCopy {
    type Item = &'a Literal;
    type IntoIter = std::slice::Iter<'a, Literal>;
    fn into_iter(self) -> Self::IntoIter {
        self.literals.into_iter()
    }
}

impl fmt::Display for ClauseCopy {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for literal in &self.literals {
            write!(f, "{} ", literal)?;
        }
        write!(f, "0")
    }
}

impl ops::Index<usize> for ClauseCopy {
    type Output = Literal;
    fn index(&self, offset: usize) -> &Literal {
        &self.literals[offset]
    }
}
