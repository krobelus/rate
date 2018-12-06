//! Data structures for the checker.

use crate::{
    literal::Literal,
    memory::{Array, Offset, Slice, SliceMut},
};
use std::{
    fmt, ops,
    ops::{Add, AddAssign, Sub, SubAssign},
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
    db: &'a Array<usize, Literal>,
    clause_offset: &Array<Clause, usize>,
    c: Clause,
) -> Slice<'a, Literal> {
    db.as_slice().range(clause_offset[c], clause_offset[c + 1])
}

pub fn clause_as_mut_slice<'a>(
    db: &'a mut Array<usize, Literal>,
    clause_offset: &Array<Clause, usize>,
    c: Clause,
) -> SliceMut<'a, Literal> {
    db.as_mut_slice()
        .range(clause_offset[c], clause_offset[c + 1])
}

pub fn clause_as_copy(
    db: &Array<usize, Literal>,
    clause_offset: &Array<Clause, usize>,
    c: Clause,
) -> Vec<Literal> {
    clause_as_slice(db, clause_offset, c).to_vec()
}

/// A lemma in a DRAT proof.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Lemma {
    Addition(Clause),
    Deletion(Clause),
}

#[derive(PartialEq, Eq, Clone)]
pub struct ClauseCopy {
    pub id: Clause,
    pub literals: Vec<Literal>,
}

impl ClauseCopy {
    pub fn new(id: Clause, literals: &[Literal]) -> ClauseCopy {
        ClauseCopy {
            id: id,
            literals: literals.to_vec(),
        }
    }
    pub fn slice(&self) -> Slice<Literal> {
        Slice::new(&self.literals[..])
    }
}

impl ClauseCopy {
    pub fn len(&self) -> usize {
        self.literals.len()
    }
    pub fn iter(self) -> std::vec::IntoIter<Literal> {
        self.literals.into_iter()
    }
}

impl IntoIterator for ClauseCopy {
    type Item = Literal;
    type IntoIter = std::vec::IntoIter<Literal>;
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
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
