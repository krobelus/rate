//! Abstraction for a partial assignment

use crate::{
    literal::{Literal, Variable},
    memory::{Array, BoundedStack},
};
use std::{fmt, fmt::Display, ops::Index};

#[derive(Debug, Clone)]
pub struct Assignment {
    mapping: Array<Literal, bool>,
    trace: BoundedStack<Literal>,
    position_in_trace: Array<Literal, usize>,
}

impl Assignment {
    pub fn new(maxvar: Variable) -> Assignment {
        let mut assignment = Assignment {
            mapping: Array::new(false, maxvar.array_size_for_literals()),
            // 2 extra for Literal::TOP and one conflicting assignment
            trace: BoundedStack::with_capacity(maxvar.array_size_for_variables() + 2),
            position_in_trace: Array::new(usize::max_value(), maxvar.array_size_for_literals()),
        };
        // NOTE copied from self.push
        // equivalent to assignment.push(Literal::TOP); but does not check invariants
        assignment.mapping[Literal::TOP] = true;
        assignment.position_in_trace[Literal::TOP] = assignment.len();
        assignment.trace.push(Literal::TOP);
        assignment
    }
    pub fn len(&self) -> usize {
        self.trace.len()
    }
    pub fn position_in_trace(&self, lit: Literal) -> usize {
        self.position_in_trace[lit]
    }
    pub fn trace_at(&self, offset: usize) -> Literal {
        self.trace[offset]
    }
    pub fn push(&mut self, lit: Literal) {
        requires!(!lit.is_constant());
        requires!(!self[lit]);
        self.mapping[lit] = true;
        self.position_in_trace[lit] = self.len();
        self.trace.push(lit);
    }
    pub fn pop(&mut self) -> Literal {
        let lit = self.trace.pop();
        if !lit.is_constant() {
            self.mapping[lit] = false;
        }
        lit
    }
    pub fn peek(&mut self) -> Literal {
        self.trace[self.len() - 1]
    }
    pub fn move_to(&mut self, src: usize, dst: usize) {
        let literal = self.trace[src];
        self.trace[dst] = literal;
        self.position_in_trace[literal] = dst;
    }
    pub fn resize_trace(&mut self, level: usize) {
        self.trace.resize(level);
    }
    pub fn unassign(&mut self, lit: Literal) {
        requires!(self[lit], "Literal {} is not assigned.", lit);
        self.mapping[lit] = false;
    }
    pub fn set_literal_at_level(&mut self, literal: Literal, offset: usize) {
        self.mapping[literal] = true;
        self.trace[offset] = literal;
        self.position_in_trace[literal] = offset;
    }
}

impl<'a> IntoIterator for &'a Assignment {
    type Item = &'a Literal;
    type IntoIter = std::slice::Iter<'a, Literal>;
    fn into_iter(self) -> Self::IntoIter {
        self.trace.into_iter()
    }
}

impl Display for Assignment {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Assignment: {} {{ ", self.len())?;
        for literal in self {
            write!(f, "{} ", literal)?;
        }
        write!(f, "}}")
    }
}

impl Index<Literal> for Assignment {
    type Output = bool;
    fn index(&self, literal: Literal) -> &bool {
        requires!(self.mapping[Literal::TOP] && !self.mapping[Literal::BOTTOM]);
        &self.mapping[literal]
    }
}
