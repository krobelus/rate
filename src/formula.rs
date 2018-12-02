//! Data structures for the checker.

use crate::{
    literal::Literal,
    memory::{Offset, TypedArray},
};
use std::{
    fmt,
    fmt::Display,
    iter,
    ops::{AddAssign, Sub, SubAssign},
};

/// The index of a clause or lemma, immutable during the lifetime of the program.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Add)]
pub struct Clause(pub usize);

impl Offset for Clause {
    fn as_offset(self) -> usize {
        self.0
    }
}

impl AddAssign<usize> for Clause {
    fn add_assign(&mut self, increment: usize) {
        self.0 += increment;
    }
}

impl Sub<usize> for Clause {
    type Output = Clause;
    fn sub(self, decrement: usize) -> Clause {
        Clause(self.0 - decrement)
    }
}

impl SubAssign<usize> for Clause {
    fn sub_assign(&mut self, decrement: usize) {
        self.0 -= decrement;
    }
}

impl Display for Clause {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// A formula.
#[derive(Debug, PartialEq, Eq)]
pub struct Formula {
    pub maxvar: u32,
    pub db: TypedArray<usize, Literal>,
    pub clause_to_offset: TypedArray<Clause, usize>,
    pub clause_active: TypedArray<Clause, bool>,
    pub proof_start: Clause,
}

/// A lemma in a DRAT proof.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Lemma {
    Addition(Clause),
    Deletion(Clause),
}

/// A proof.
pub type Proof = TypedArray<usize, Lemma>;

pub fn member(formula: &Formula, literal: Literal, c: Clause) -> bool {
    formula.clause(c).find(|l| *l == literal).is_some()
}

impl Formula {
    pub fn clauses(&self) -> FormulaIterator {
        FormulaIterator::all(self)
    }
    pub fn clause(&self, clause: Clause) -> ClauseIterator {
        ClauseIterator::new(self, clause)
    }
    pub fn num_clauses(&self) -> usize {
        self.clause_to_offset.capacity()
    }
}

pub struct FormulaIterator<'a> {
    formula: &'a Formula,
    clause: Clause,
}

impl<'a> FormulaIterator<'a> {
    fn all(formula: &'a Formula) -> FormulaIterator {
        FormulaIterator {
            formula: formula,
            clause: Clause(usize::max_value()),
        }
    }
}

impl<'a> iter::Iterator for FormulaIterator<'a> {
    type Item = Clause;
    fn next(&mut self) -> Option<Clause> {
        let formula = self.formula;
        let end = formula.proof_start;

        self.clause = Clause(self.clause.0.wrapping_add(1));

        // skip deleted clauses
        while self.clause < end && !formula.clause_active[self.clause] {
            self.clause += 1;
        }

        if self.clause == end {
            None
        } else {
            Some(self.clause)
        }
    }
}

pub struct ClauseIterator<'a> {
    formula: &'a Formula,
    index: usize,
}

impl<'a> ClauseIterator<'a> {
    pub fn empty(&self) -> bool {
        let db = &self.formula.db;
        ensure!(self.index == 0 || db[self.index - 1] == Literal::new(0));
        db[self.index] == Literal::new(0)
    }
    fn new(formula: &'a Formula, clause: Clause) -> ClauseIterator {
        ensure!(
            formula.clause_active[clause],
            "Must not iterate over deleted clause."
        );
        ClauseIterator {
            formula: formula,
            index: formula.clause_to_offset[clause],
        }
    }
}

impl<'a> Iterator for ClauseIterator<'a> {
    type Item = Literal;
    fn next(&mut self) -> Option<Literal> {
        let value = self.formula.db[self.index];
        self.index += 1;
        if value.zero() {
            None
        } else {
            Some(value)
        }
    }
}

impl<'a> Display for ClauseIterator<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut i = self.index;
        loop {
            let literal = self.formula.db[i];
            if literal == Literal::new(0) {
                break;
            }
            write!(f, "{} ", literal)?;
            i += 1;
            ensure!(i < self.formula.db.capacity())
        }
        write!(f, "0")
    }
}

impl Display for Formula {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "p cnf {} {}\n", self.maxvar, self.proof_start)?;
        for c in self.clauses() {
            for l in self.clause(c) {
                write!(f, "{} ", l)?;
            }
            write!(f, "0\n")?;
        }
        write!(f, "")
    }
}
