//! Abstraction for a partial assignment

use crate::{
    formula::{Clause, Formula},
    literal::Literal,
    memory::{Stack, TypedArray},
};
use ansi_term::Colour;
use std::{
    fmt,
    fmt::Display,
    ops::{Index, IndexMut},
    slice,
};

#[derive(Debug, PartialEq, Eq)]
pub struct Assignment {
    map: TypedArray<Literal, bool>,
    // We use Literal::new(0) to replace literals in the assignment stack that
    // have been unassigned as a result of deleting a unit clause.
    stack: Stack<Literal>,
    position_in_stack: TypedArray<Literal, usize>,
}

impl Assignment {
    pub fn new(num_variables: usize) -> Assignment {
        let array_size_literals = 2 * (num_variables + 1);
        Assignment {
            map: TypedArray::new(false, array_size_literals),
            stack: Stack::new(Literal::new(0), num_variables),
            position_in_stack: TypedArray::new(0, array_size_literals),
        }
    }
    pub fn len(&self) -> usize {
        self.stack.len()
    }
    pub fn level_prior_to_assigning(&self, l: Literal) -> usize {
        self.position_in_stack[l]
    }
}

impl<'a> IntoIterator for &'a Assignment {
    type Item = &'a Literal;
    type IntoIter = slice::Iter<'a, Literal>;
    fn into_iter(self) -> slice::Iter<'a, Literal> {
        self.stack.into_iter()
    }
}

impl Display for Assignment {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Assignment: {{ ")?;
        for literal in &self.stack {
            write!(f, "{} ", literal)?;
        }
        write!(f, "}}")
    }
}

impl Index<Literal> for Assignment {
    type Output = bool;
    fn index(&self, literal: Literal) -> &bool {
        ensure!(
            literal != Literal::new(0),
            "Illegal read of assignment to literal 0."
        );
        &self.map[literal]
    }
}
impl IndexMut<Literal> for Assignment {
    fn index_mut(&mut self, literal: Literal) -> &mut bool {
        &mut self.map[literal]
    }
}

pub fn assign(assignment: &mut Assignment, l: Literal) {
    ensure!(!assignment[-l] && !assignment[l]);
    assignment.position_in_stack[l] = assignment.stack.len();
    assignment.stack.push(l);
    assignment[l] = true;
}

pub fn unassign(assignment: &mut Assignment, l: Literal) {
    assignment[l] = false;
    // It is not necessary to reset assignment.position_in_stack here, as it
    // will be written before the next use.
}

pub fn reset_assignment(assignment: &mut Assignment, level: usize) {
    while assignment.stack.len() > level {
        let literal = *assignment.stack.pop();
        // literal can be 0 here but we don't need to introduce a branch since the assignment for
        // Literal::new(0) will never be read.
        unassign(assignment, literal);
    }
    ensure!(assignment.stack.len() <= level);
}

fn format_clause_under_assignment(formula: &Formula, assignment: &Assignment, c: Clause) -> String {
    let mut result = String::new();
    for l in formula.clause(c) {
        let style = if assignment[l] {
            Colour::Green.normal()
        } else if assignment[-l] {
            Colour::Red.normal()
        } else {
            Colour::Yellow.normal()
        };
        result += &format!("{}", style.paint(&format!("{} ", l)));
    }
    result += "\n";
    result
}

#[allow(dead_code)]
pub fn format_formula_under_assignment(formula: &Formula, assignment: &Assignment) -> String {
    let mut result = String::new();
    for c in formula.clauses() {
        result += &format_clause_under_assignment(&formula, &assignment, c);
    }
    result
}
