///! Container for clauses
use crate::{
    checker::ClauseFields,
    clause::Clause,
    literal::Literal,
    memory::{Offset, Slice, Stack},
};

use rate_macros::HeapSpace;
use std::ops::{Index, IndexMut, Range};

pub const PADDING_START: usize = 3;
pub const FIELDS_OFFSET: usize = 2;
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
    pub const fn new() -> ClauseDatabase {
        ClauseDatabase {
            data: Stack::const_new(),
            offset: Stack::const_new(),
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
    pub fn number_of_clauses(&self) -> u64 {
        requires!(self.have_sentinel);
        (self.offset.len() - ClauseDatabase::PADDING) as u64
    }
    pub fn last_clause(&self) -> Clause {
        requires!(self.have_sentinel);
        Clause::new(self.number_of_clauses() - 1)
    }
    fn last_clause_no_sentinel(&self) -> Clause {
        requires!(!self.have_sentinel);
        let index = self.offset.len() - 1;
        Clause::new(index as u64)
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
        let lower = (id & 0x0000_0000_ffff_ffff) as u32;
        let upper = ((id & 0xffff_ffff_0000_0000) >> 32) as u32;
        self.data.push(Literal::from_raw(lower));
        self.data.push(Literal::from_raw(upper));
        self.data.push(Literal::from_raw(0));
        clause
    }
    fn close_clause(&mut self) {
        requires!(!self.have_sentinel);
        let clause = self.last_clause_no_sentinel();
        let start = self.offset[clause.as_offset()] + PADDING_START;
        let end = self.data.len();
        let _sort_literally = |&literal: &Literal| literal.decode();
        let _sort_magnitude = |&literal: &Literal| literal.encoding;
        self.data
            .mut_slice()
            .range(start, end)
            .sort_unstable_by_key(_sort_literally);
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
    pub fn clause(&self, clause: Clause) -> Slice<Literal> {
        let range = self.clause_range(clause);
        self.data.as_slice().range(range.start, range.end)
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
        let lower = self[head - PADDING_START];
        let upper = self[head - PADDING_START + 1];
        Clause::new(u64::from(lower.encoding) | u64::from(upper.encoding) << 32)
    }
    pub fn swap(&mut self, a: usize, b: usize) {
        self.data.mut_slice().swap(a, b);
    }
    pub fn make_clause_empty(&mut self, target: Clause) {
        self.offset[target.as_offset() + 1] =
            self.offset[target.as_offset()] + PADDING_START + PADDING_END;
    }
    pub fn fields(&self, clause: Clause) -> &ClauseFields {
        unsafe {
            &*(&self.data[self.offset[clause.as_offset()] + FIELDS_OFFSET].encoding as *const u32
                as *const ClauseFields)
        }
    }
    pub fn fields_mut(&mut self, clause: Clause) -> &mut ClauseFields {
        unsafe {
            &mut *(&mut (self.data[self.offset[clause.as_offset()] + FIELDS_OFFSET].encoding)
                as *mut u32 as *mut ClauseFields)
        }
    }
    pub fn fields_from_offset(&self, offset: usize) -> &ClauseFields {
        unsafe { &*(&(self.data[offset - 1].encoding) as *const u32 as *const ClauseFields) }
    }
    pub fn fields_mut_from_offset(&mut self, offset: usize) -> &mut ClauseFields {
        unsafe { &mut *(&mut (self.data[offset - 1].encoding) as *mut u32 as *mut ClauseFields) }
    }
    #[cfg(test)]
    pub fn clear(&mut self) {
        self.data.clear();
        self.offset.clear();
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
    pub const fn new() -> WitnessDatabase {
        WitnessDatabase {
            data: Stack::const_new(),
            offset: Stack::const_new(),
        }
    }
    #[cfg(test)]
    pub fn from(data: Stack<Literal>, offset: Stack<usize>) -> WitnessDatabase {
        WitnessDatabase { data, offset }
    }
    pub fn empty(&self) -> bool {
        self.offset.empty()
    }
    pub fn initialize(&mut self) {
        self.offset.push(0)
    }
    pub fn open_witness(&mut self) -> Clause {
        self.offset.pop();
        let witness = Clause::new(self.offset.len() as u64);
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
    pub fn witness(&self, clause: Clause) -> Slice<Literal> {
        let range = self.witness_range(clause);
        self.data.as_slice().range(range.start, range.end)
    }
    pub fn witness_range(&self, clause: Clause) -> Range<usize> {
        self.offset[clause.as_offset()]..self.offset[clause.as_offset() + 1]
    }
    #[cfg(test)]
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
