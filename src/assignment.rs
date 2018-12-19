//! Abstraction for a partial assignment

use crate::{
    literal::{literal_array_len, Literal, Variable},
    memory::{Array, Offset, StackMapping},
};
use ansi_term::Colour;
use std::{fmt, fmt::Display, ops::Index};

#[derive(Debug)]
pub struct Assignment {
    first_unprocessed: usize,
    mapping: StackMapping<Literal, bool>,
    position_in_stack: Array<Literal, usize>,
}

impl Assignment {
    pub fn new(maxvar: Variable) -> Assignment {
        let array_size = literal_array_len(maxvar);
        let stack_capacity = maxvar.as_offset();
        let mut assignment = Assignment {
            first_unprocessed: 0,
            mapping: StackMapping::new(false, array_size, stack_capacity),
            position_in_stack: Array::new(0, literal_array_len(maxvar)),
        };
        assignment.mapping.set_but_do_not_push(Literal::TOP, true);
        assignment
            .mapping
            .set_but_do_not_push(Literal::BOTTOM, false);
        assignment
    }
    pub fn level(&self) -> usize {
        self.first_unprocessed
    }
    pub fn level_prior_to_assigning(&self, l: Literal) -> usize {
        self.position_in_stack[l]
    }
    pub fn literal_at_level(&self, offset: usize) -> Literal {
        self.mapping.stack_at(offset)
    }
    pub fn literal_at_level_mut(&mut self, offset: usize) -> &mut Literal {
        self.mapping.stack_at_mut(offset)
    }
    pub fn assign(&mut self, l: Literal) {
        ensure!(!self.any_scheduled());
        self.schedule(l);
        self.advance();
    }
    pub fn unassign(&mut self, l: Literal) {
        ensure!(!self[l], format!("Literal {} is not assigned.", l));
        // TODO remove reason flag
        self.mapping.set_but_do_not_push(l, false);
    }
    pub fn advance(&mut self) {
        ensure!(self.any_scheduled());
        let l = self.mapping.stack_at(self.first_unprocessed);
        self.first_unprocessed += 1;
        self.mapping.set_but_do_not_push(l, true);
    }
    pub fn schedule(&mut self, l: Literal) {
        ensure!(!l.is_constant());
        ensure!(!self[-l] && !self[l]);
        self.position_in_stack[l] = self.first_unprocessed;
        self.mapping.push_but_do_not_set(l);
    }
    fn any_scheduled(&self) -> bool {
        self.level() == self.mapping.len()
    }
    pub fn reset(&mut self, level: usize) {
        ensure!(!self.any_scheduled());
        while self.mapping.len() > level {
            self.mapping.pop();
            // It is not necessary to reset position_in_stack here, as it
            // will be written before the next use.
        }
        self.first_unprocessed = level;
        ensure!(self.mapping.len() <= level);
    }
    pub fn was_assigned_before(&self, l: Literal, level: usize) -> bool {
        self[l] && self.position_in_stack[l] < level
    }
}

impl<'a> IntoIterator for &'a Assignment {
    type Item = &'a Literal;
    type IntoIter = std::slice::Iter<'a, Literal>;
    fn into_iter(self) -> std::slice::Iter<'a, Literal> {
        self.mapping.into_iter()
    }
}

impl Display for Assignment {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Assignment: {{ ")?;
        for literal in self {
            write!(f, "{} ", literal)?;
        }
        write!(f, "}}")
    }
}

impl Index<Literal> for Assignment {
    type Output = bool;
    fn index(&self, literal: Literal) -> &bool {
        ensure!(self.mapping[Literal::TOP] && !self.mapping[Literal::BOTTOM]);
        &self.mapping[literal]
    }
}

#[allow(dead_code)]
fn format_clause_under_assignment(clause: &[Literal], assignment: &Assignment) -> String {
    let mut result = String::new();
    for &literal in clause {
        let style = if assignment[literal] {
            Colour::Green.normal()
        } else if assignment[-literal] {
            Colour::Red.normal()
        } else {
            Colour::Yellow.normal()
        };
        result += &format!("{}", style.paint(&format!("{} ", literal)));
    }
    result += "\n";
    result
}
