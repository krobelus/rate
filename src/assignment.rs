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
    stack: Stack<Literal>,
}

impl Assignment {
    pub fn new(num_variables: usize) -> Assignment {
        Assignment {
            map: TypedArray::new(false, 2 * (num_variables + 1)),
            stack: Stack::new(Literal::new(0), num_variables),
        }
    }
    pub fn len(&self) -> usize {
        self.stack.len()
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
        &self.map[literal]
    }
}
impl IndexMut<Literal> for Assignment {
    fn index_mut(&mut self, literal: Literal) -> &mut bool {
        &mut self.map[literal]
    }
}

pub fn assign(assignment: &mut Assignment, l: Literal) {
    assignment.stack.push(l);
    debug_assert!(!assignment[-l]);
    assignment[l] = true;
}

pub fn reset_assignment(assignment: &mut Assignment, level: usize) {
    let stack = &mut assignment.stack;
    while stack.len() > level {
        let literal = *stack.pop();
        assignment.map[literal] = false;
    }
    assignment.stack.clear();
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
