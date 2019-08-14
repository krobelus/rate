///! Container for clauses
use crate::{
    clause::{Clause, ClauseStorage},
    literal::Literal,
    memory::{Offset, Stack},
};

use rate_macros::HeapSpace;
use std::{
    convert::TryFrom,
    ops::{Index, IndexMut, Range},
};

pub const PADDING_START: usize = 2;
pub const FIELDS_OFFSET: usize = 1;
pub const PADDING_END: usize = 1;

/// Clause are stored in field `data`:
/// The first two elements encode the clause ID.
/// The third element contains a `struct ClauseFields`.
/// After that, the literals are stored (zero-terminated)
#[derive(Debug, PartialEq, HeapSpace)]
pub struct ClauseDatabase {
    data: Stack<Literal>,
    offset: Stack<usize>,
    have_sentinel: bool,
}

impl ClauseDatabase {
    pub fn new() -> ClauseDatabase {
        ClauseDatabase {
            data: Stack::new(),
            offset: Stack::new(),
            have_sentinel: false,
        }
    }
    #[cfg(test)]
    pub fn from(data: Stack<Literal>, offset: Stack<usize>) -> ClauseDatabase {
        let mut db = ClauseDatabase {
            data,
            offset,
            have_sentinel: false,
        };
        db.push_sentinel(db.data.len());
        db
    }
    pub fn initialize(&mut self) {
        requires!(!self.have_sentinel);
        self.push_sentinel(0);
    }
    pub const PADDING: usize = 1;
    pub fn number_of_clauses(&self) -> ClauseStorage {
        requires!(self.have_sentinel);
        requires!(u64::try_from(self.offset.len() - ClauseDatabase::PADDING).is_ok());
        (self.offset.len() - ClauseDatabase::PADDING) as ClauseStorage
    }
    pub fn last_clause(&self) -> Clause {
        requires!(self.have_sentinel);
        Clause::new(self.number_of_clauses() - 1)
    }
    fn last_clause_no_sentinel(&self) -> Clause {
        requires!(!self.have_sentinel);
        let index = self.offset.len() - 1;
        Clause::from_usize(index)
    }
    pub fn is_empty(&self) -> bool {
        self.offset.is_empty()
    }
    fn push_sentinel(&mut self, offset: usize) {
        requires!(!self.have_sentinel);
        self.offset.push(offset);
        self.have_sentinel = true;
    }
    fn pop_sentinel(&mut self) {
        requires!(self.have_sentinel);
        self.offset.pop();
        self.have_sentinel = false;
    }
    pub fn push_literal(&mut self, literal: Literal) {
        if literal.is_zero() {
            self.close_clause()
        } else {
            self.data.push(literal)
        }
    }
    pub fn open_clause(&mut self) -> Clause {
        requires!(self.have_sentinel);
        let id = self.number_of_clauses();
        self.pop_sentinel();
        let clause = Clause::new(id);
        self.offset.push(self.data.len()); // clause
        self.data.push(Literal::from_raw(id));
        self.data.push(Literal::from_raw(0)); // fields
        clause
    }
    fn close_clause(&mut self) {
        requires!(!self.have_sentinel);
        let clause = self.last_clause_no_sentinel();
        let start = self.offset[clause.as_offset()] + PADDING_START;
        let end = self.data.len();
        let _sort_literally = |&literal: &Literal| literal.decode();
        let _sort_magnitude = |&literal: &Literal| literal.encoding;
        &mut self.data[start..end].sort_unstable_by_key(_sort_literally);
        let mut duplicate = false;
        let mut length = 0;
        for i in start..end {
            if i + 1 < end && self[i] == self[i + 1] {
                duplicate = true;
            } else {
                self[start + length] = self[i];
                length += 1;
            }
        }
        self.data.truncate(start + length);
        if length == 1 {
            self.data.push(Literal::BOTTOM);
        }
        self.data.push(Literal::new(0));
        self.push_sentinel(self.data.len());
        if duplicate {
            warn!(
                "Removed duplicate literals in {}",
                self.clause_to_string(clause)
            );
        }
    }
    pub fn pop_clause(&mut self) {
        requires!(self.have_sentinel);
        let last_clause = self.last_clause();
        let last_clause_offset = self.offset[last_clause.as_offset()];
        self.data.truncate(last_clause_offset);
        self.pop_sentinel();
        self.offset.pop(); // clause
        self.push_sentinel(last_clause_offset);
    }
    pub fn clause_to_string(&self, clause: Clause) -> String {
        format!(
            "[{}]{} 0",
            clause,
            self.clause(clause)
                .iter()
                .filter(|&literal| *literal != Literal::BOTTOM)
                .map(|&literal| format!(" {}", literal))
                .collect::<Vec<_>>()
                .join("")
        )
    }
    pub fn clause(&self, clause: Clause) -> &[Literal] {
        &self.data[self.clause_range(clause)]
    }
    pub fn clause_range(&self, clause: Clause) -> Range<usize> {
        requires!(self.have_sentinel);
        self.offset[clause.as_offset()] + PADDING_START
            ..self.offset[clause.as_offset() + 1] - PADDING_END
    }
    pub fn watches(&self, head: usize) -> [Literal; 2] {
        [self[head], self[head + 1]]
    }
    pub fn clause2offset(&self, clause: Clause) -> usize {
        self.clause_range(clause).start
    }
    pub fn offset2clause(&self, head: usize) -> Clause {
        Clause::new(self[head - PADDING_START].encoding)
    }
    pub fn swap(&mut self, a: usize, b: usize) {
        self.data.swap(a, b);
    }
    pub fn make_clause_empty(&mut self, target: Clause) {
        self.offset[target.as_offset() + 1] =
            self.offset[target.as_offset()] + PADDING_START + PADDING_END;
    }
    pub fn fields(&self, clause: Clause) -> &u32 {
        &self.data[self.offset[clause.as_offset()] + FIELDS_OFFSET].encoding
    }
    pub fn fields_mut(&mut self, clause: Clause) -> &mut u32 {
        &mut self.data[self.offset[clause.as_offset()] + FIELDS_OFFSET].encoding
    }
    pub fn fields_from_offset(&self, offset: usize) -> &u32 {
        &self.data[offset - 1].encoding
    }
    pub fn fields_mut_from_offset(&mut self, offset: usize) -> &mut u32 {
        &mut self.data[offset - 1].encoding
    }
    pub fn clear(&mut self) {
        self.data.clear();
        self.offset.clear();
        self.have_sentinel = false;
    }
}

impl Index<usize> for ClauseDatabase {
    type Output = Literal;
    fn index(&self, offset: usize) -> &Literal {
        &self.data[offset]
    }
}

impl IndexMut<usize> for ClauseDatabase {
    fn index_mut(&mut self, offset: usize) -> &mut Literal {
        &mut self.data[offset]
    }
}

#[derive(Debug, PartialEq, HeapSpace)]
pub struct WitnessDatabase {
    data: Stack<Literal>,
    offset: Stack<usize>,
}

impl WitnessDatabase {
    pub fn new() -> WitnessDatabase {
        WitnessDatabase {
            data: Stack::new(),
            offset: Stack::new(),
        }
    }
    #[cfg(test)]
    pub fn from(data: Stack<Literal>, offset: Stack<usize>) -> WitnessDatabase {
        WitnessDatabase { data, offset }
    }
    pub fn empty(&self) -> bool {
        self.offset.is_empty()
    }
    pub fn initialize(&mut self) {
        self.offset.push(0)
    }
    pub fn open_witness(&mut self) -> Clause {
        self.offset.pop();
        let witness = Clause::from_usize(self.offset.len());
        self.offset.push(self.data.len());
        witness
    }
    fn close_witness(&mut self) {
        self.offset.push(self.data.len())
    }
    pub fn push_literal(&mut self, literal: Literal) {
        if literal.is_zero() {
            self.close_witness();
        } else {
            self.data.push(literal);
        }
    }
    pub fn witness_to_string(&self, clause: Clause) -> String {
        format!(
            "Witness for [{}]:{} 0",
            clause,
            self.witness(clause)
                .iter()
                .map(|&literal| format!(" {}", literal))
                .collect::<Vec<_>>()
                .join("")
        )
    }
    pub fn witness(&self, clause: Clause) -> &[Literal] {
        &self.data[self.witness_range(clause)]
    }
    pub fn witness_range(&self, clause: Clause) -> Range<usize> {
        self.offset[clause.as_offset()]..self.offset[clause.as_offset() + 1]
    }
    pub fn clear(&mut self) {
        self.data.clear();
        self.offset.clear();
    }
}

impl Index<usize> for WitnessDatabase {
    type Output = Literal;
    fn index(&self, offset: usize) -> &Literal {
        &self.data[offset]
    }
}

impl IndexMut<usize> for WitnessDatabase {
    fn index_mut(&mut self, offset: usize) -> &mut Literal {
        &mut self.data[offset]
    }
}
