//! A partial assignment.
//!
//! This has proven to be a useful abstraction. Unfortunately we need to expose
//! most of its internals since we modify the assignment stack when applying a
//! revision.

use crate::{
    clause::Reason,
    literal::{Literal, Variable},
    memory::{Array, BoundedStack, HeapSpace, Slice, StackIterator},
};
use std::{fmt, fmt::Display, ops::Index};

/// An assignment comprising a mapping plus a trail (stack of literals).
///
/// Note that [`Literal::TOP`] is always assigned.
///
/// It is valid to assign both a literal and its negation - this is how we detect
/// a conflict.
#[derive(Debug, Clone)]
pub struct Assignment {
    /// Maps assigned literal to true.
    mapping: Array<Literal, bool>,
    /// Assigned literals, in chronologic order.
    trail: BoundedStack<(Literal, Reason)>,
    /// Maps literal to their offset in `trail`, or `usize::max_value()`
    position_in_trail: Array<Literal, usize>,
}

impl PartialEq for Assignment {
    fn eq(&self, other: &Assignment) -> bool {
        self.mapping == other.mapping
            && self.trail == other.trail
            && (0..self.trail.len()).all(|pos| {
                let lit = self.trail_at(pos).0;
                self.position_in_trail[lit] == other.position_in_trail[lit]
            })
    }
}

impl Assignment {
    /// Create an empty assignment.
    pub fn new(maxvar: Variable) -> Assignment {
        let mut assignment = Assignment {
            mapping: Array::new(false, maxvar.array_size_for_literals()),
            /// + 2 for Literal::TOP and one conflicting assignment
            trail: BoundedStack::with_capacity(maxvar.array_size_for_variables() + 2),
            position_in_trail: Array::new(usize::max_value(), maxvar.array_size_for_literals()),
        };
        // Equivalent to assignment.push(Literal::TOP); but does not check invariants
        assignment.mapping[Literal::TOP] = true;
        assignment.position_in_trail[Literal::TOP] = assignment.len();
        assignment.trail.push((Literal::TOP, Reason::assumed()));
        assignment
    }
    /// Return the number of assigned literals.
    pub fn len(&self) -> usize {
        self.trail.len()
    }
    /// Return the position in the trail where this literal was assigned.
    pub fn position_in_trail(&self, literal: Literal) -> usize {
        requires!(self[literal]);
        self.position_in_trail[literal]
    }
    /// Access the trail by offset.
    pub fn trail_at(&self, offset: usize) -> (Literal, Reason) {
        self.trail[offset]
    }
    /// Add a new literal to the trail, assigning it to true.
    pub fn push(&mut self, lit: Literal, reason: Reason) {
        requires!(!lit.is_constant());
        requires!(!self[lit]);
        self.mapping[lit] = true;
        self.position_in_trail[lit] = self.len();
        self.trail.push((lit, reason));
    }
    /// View the literal that was assigned last.
    pub fn peek(&mut self) -> (Literal, Reason) {
        self.trail[self.len() - 1]
    }
    /// Unassign the literal that was assigned last.
    pub fn pop(&mut self) -> (Literal, Reason) {
        let (literal, reason) = self.trail.pop();
        if !literal.is_constant() {
            self.mapping[literal] = false;
        }
        (literal, reason)
    }
    /// Move the literal at trail position `src` to `dst`.
    pub fn move_to(&mut self, src: usize, dst: usize) {
        let (literal, reason) = self.trail[src];
        self.trail[dst] = (literal, reason);
        self.position_in_trail[literal] = dst;
    }
    /// Increase the size of the trail.
    /// Note: this does not change the assigned values, only the trail.
    pub fn grow_trail(&mut self, level: usize) {
        self.trail.set_len(level)
    }
    /// Descrease the size of the trail.
    /// Note: this does not change the assigned values, only the trail.
    pub fn shrink_trail(&mut self, level: usize) {
        self.trail.truncate(level)
    }
    /// Remove the assignment for a literal, without modifying the trail.
    pub fn unassign(&mut self, literal: Literal) {
        requires!(self[literal], "Literal {} is not assigned.", literal);
        self.mapping[literal] = false;
    }
    /// Insert a literal into the trail and assign it.
    pub fn set_trail_at(&mut self, offset: usize, literal: Literal, reason: Reason) {
        self.mapping[literal] = true;
        self.trail[offset] = (literal, reason);
        self.position_in_trail[literal] = offset;
    }
}

/// Iterate over the literals in the trail, from oldest to newest.
impl<'a> IntoIterator for &'a Assignment {
    type Item = &'a (Literal, Reason);
    type IntoIter = StackIterator<'a, (Literal, Reason)>;
    fn into_iter(self) -> Self::IntoIter {
        self.trail.into_iter()
    }
}

impl Display for Assignment {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Assignment: {}", self.len())?;
        for (literal, reason) in self {
            write!(f, " {} ({}),", literal, reason)?;
        }
        Ok(())
    }
}

impl Index<Literal> for Assignment {
    type Output = bool;
    /// This assumes that we don't ever pass a constant literal, however this
    /// can be changed if necessary.
    fn index(&self, literal: Literal) -> &bool {
        requires!(self.mapping[Literal::TOP] && !self.mapping[Literal::BOTTOM]);
        &self.mapping[literal]
    }
}

impl HeapSpace for Assignment {
    fn heap_space(&self) -> usize {
        self.mapping.heap_space() + self.trail.heap_space() + self.position_in_trail.heap_space()
    }
}

/// UP-models in rupee
pub fn stable_under_unit_propagation(assignment: &Assignment, clause: Slice<Literal>) -> bool {
    let clause_is_satisfied = clause.iter().any(|&literal| assignment[literal]);
    let unknown_count = clause
        .iter()
        .filter(|&&literal| !assignment[literal] && !assignment[-literal])
        .count();
    clause_is_satisfied || unknown_count >= 2
}
