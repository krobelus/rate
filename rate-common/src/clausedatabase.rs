//! Container for clauses

use crate::{
    clause::{puts_clause_with_id, Clause, ClauseIdentifierType},
    literal::Literal,
    memory::{HeapSpace, Offset, Vector},
};

use rate_macros::HeapSpace;
use std::{
    convert::TryFrom,
    mem::size_of,
    ops::{Index, IndexMut, Range},
};

pub trait ClauseStorage {
    /// Initialze a new clause.
    ///
    /// This must be called before adding literals with
    /// [`push_literal()`](#tymethod.push_literal).
    fn open_clause(&mut self) -> Clause;
    /// Add a literal to the current clause.
    ///
    /// If passed literal 0, the clause will be finished and
    /// [`open_clause()`](#tymethod.open_clause) must be called before adding
    /// literals to the next clause.
    fn push_literal(&mut self, literal: Literal, verbose: bool);
}

/// Size of metadata that precede the literals of a clause
pub const PADDING_START: usize = 2;
/// Location of the fields within the metadata.
pub const FIELDS_OFFSET: usize = 1;
/// Size of the clause suffix (terminating 0)
pub const PADDING_END: usize = 1;

/// Stores clauses in a flat buffer
#[derive(Debug, PartialEq, HeapSpace)]
pub struct ClauseDatabase {
    /// Stores clauses with some metadata.
    /// The first element encodes the clause ID.
    /// The second element contains a `struct ClauseFields`.
    /// After that, the literals are stored (zero-terminated)
    data: Vector<Literal>,
    /// Maps clause ID to offset in above data.
    offset: Vector<usize>,
    /// Used to assert that `offset` contains an extra value that points
    /// one beyond the last element of `data`.
    have_sentinel: bool,
}

impl ClauseStorage for ClauseDatabase {
    fn open_clause(&mut self) -> Clause {
        requires!(self.have_sentinel);
        let id = self.number_of_clauses();
        self.pop_sentinel();
        let clause = Clause::new(id);
        self.offset.push(self.data.len()); // clause
        self.data.push(Literal::from_raw(id));
        self.data.push(Literal::from_raw(0)); // fields
        clause
    }
    fn push_literal(&mut self, literal: Literal, verbose: bool) {
        if literal.is_zero() {
            self.close_clause(verbose)
        } else {
            self.data.push(literal)
        }
    }
}

impl Default for ClauseDatabase {
    /// Create an empty clause database.
    fn default() -> ClauseDatabase {
        let mut db = ClauseDatabase {
            data: Vector::new(),
            offset: Vector::new(),
            have_sentinel: false,
        };
        db.push_sentinel(db.data.len());
        db
    }
}

impl ClauseDatabase {
    /// Create a database from raw elements; used only for tests.
    #[cfg(test)]
    pub fn from(data: Vector<Literal>, offset: Vector<usize>) -> ClauseDatabase {
        let mut db = ClauseDatabase {
            data,
            offset,
            have_sentinel: false,
        };
        db.push_sentinel(db.data.len());
        db
    }
    /// Returns the total number that are stored.
    pub fn number_of_clauses(&self) -> ClauseIdentifierType {
        requires!(self.have_sentinel);
        let sentinel_size = 1;
        let number = self.offset.len() - sentinel_size;
        requires!(ClauseIdentifierType::try_from(number).is_ok());
        number as ClauseIdentifierType
    }
    /// Returns the clause that was added last.
    pub fn last_clause(&self) -> Clause {
        requires!(self.have_sentinel);
        requires!(self.number_of_clauses() > 0);
        Clause::new(self.number_of_clauses() - 1)
    }
    /// Returns the clause that was added last, assuming there is no sentinel
    fn last_clause_no_sentinel(&self) -> Clause {
        requires!(!self.have_sentinel);
        let index = self.offset.len() - 1;
        Clause::from_usize(index)
    }
    /// Add the sentinel, stating that `offset` is the end of the last clause.
    fn push_sentinel(&mut self, offset: usize) {
        requires!(!self.have_sentinel);
        self.offset.push(offset);
        self.have_sentinel = true;
    }
    /// Remove the sentinel to allow adding a new clause.
    fn pop_sentinel(&mut self) {
        requires!(self.have_sentinel);
        self.offset.pop();
        self.have_sentinel = false;
    }
    /// Finish the current clause.
    fn close_clause(&mut self, verbose: bool) {
        requires!(!self.have_sentinel);
        let clause = self.last_clause_no_sentinel();
        let start = self.offset[clause.as_offset()] + PADDING_START;
        let end = self.data.len();
        sort_clause(&mut self.data[start..end]);
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
        if verbose && duplicate {
            as_warning!({
                puts!("c removed duplicate literals in ");
                puts_clause_with_id(clause, self.clause(clause));
                puts!("\n");
            });
        }
    }
    /// Delete the last clause.
    pub fn pop_clause(&mut self) {
        requires!(self.have_sentinel);
        let last_clause = self.last_clause();
        let last_clause_offset = self.offset[last_clause.as_offset()];
        self.data.truncate(last_clause_offset);
        self.pop_sentinel();
        self.offset.pop(); // clause
        self.push_sentinel(last_clause_offset);
    }
    /// Give the DIMACS representation of a clause.
    ///
    /// Only used for debugging, prefer `clause::write_clause()`.
    pub fn clause_to_string(&self, clause: Clause) -> String {
        format!(
            "[{}]{} 0",
            clause,
            self.clause(clause)
                .iter()
                .filter(|&literal| *literal != Literal::BOTTOM)
                .map(|&literal| format!(" {}", literal))
                .collect::<Vector<_>>()
                .join("")
        )
    }
    /// The literals in the the clause.
    pub fn clause(&self, clause: Clause) -> &[Literal] {
        &self.data[self.clause_range(clause)]
    }
    /// The internal offsets of the literals in the the clause.
    pub fn clause_range(&self, clause: Clause) -> Range<usize> {
        requires!(self.have_sentinel);
        self.offset[clause.as_offset()] + PADDING_START
            ..self.offset[clause.as_offset() + 1] - PADDING_END
    }
    /// The first two literals in the clause.
    pub fn watches(&self, head: usize) -> [Literal; 2] {
        [self[head], self[head + 1]]
    }
    /// Convert a clause identifier to the offset of the clause.
    pub fn clause2offset(&self, clause: Clause) -> usize {
        self.clause_range(clause).start
    }
    /// Convert a clause offset to the identifier of the clause.
    pub fn offset2clause(&self, head: usize) -> Clause {
        Clause::new(self[head - PADDING_START].encoding)
    }
    /// Swap the literal at the given offsets in the clause database.
    pub fn swap(&mut self, a: usize, b: usize) {
        self.data.swap(a, b);
    }
    /// Access the metadata for this clause.
    pub fn fields(&self, clause: Clause) -> &u32 {
        &self.data[self.offset[clause.as_offset()] + FIELDS_OFFSET].encoding
    }
    /// Access the mutable metadata for this clause.
    pub fn fields_mut(&mut self, clause: Clause) -> &mut u32 {
        &mut self.data[self.offset[clause.as_offset()] + FIELDS_OFFSET].encoding
    }
    /// Access the metadata for the clause with this offset.
    /// This is possibly more efficient than [`fields()`](#method.fields).
    pub fn fields_from_offset(&self, offset: usize) -> &u32 {
        &self.data[offset - 1].encoding
    }
    /// Access the mutable metadata for the clause with this offset.
    /// This is possibly more efficient than [`fields()`](#method.fields_mut).
    pub fn fields_mut_from_offset(&mut self, offset: usize) -> &mut u32 {
        &mut self.data[offset - 1].encoding
    }
    /// See [`Vec::shrink_to_fit()`](https://doc.rust-lang.org/std/vec/struct.Vec.html#method.shrink_to_fit).
    pub fn shrink_to_fit(&mut self) {
        // TODO: Should be (nightly) shrink_to(len() + 1), see rate::close_proof.
        self.data.push(Literal::new(0));
        self.data.shrink_to_fit();
        self.data.pop();
        self.offset.push(0);
        self.offset.shrink_to_fit();
        self.offset.pop();
    }
    /// Expected memory usage.
    #[allow(dead_code)]
    fn metrics(&self) {
        let _db_size = self.data.capacity() * size_of::<Literal>();
        let _drat_trim_clause_db_size = size_of::<Literal>()
            * (
                self.data.capacity() // our
                // we add padding to unit clauses
                - (0..self.number_of_clauses()).map(Clause::new).filter(|&c| is_size_1_clause(self.clause(c))).count()
                + self.number_of_clauses() as usize // pivots
                - (2 + 1) // extra empty clause (id + fields + zero literal)
                + 1
                // sentinel
            );
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

/// Stores witnesses in a flat buffer
///
/// Each witness is a set of literals that are associated with a clause.
#[derive(Debug, PartialEq, HeapSpace)]
pub struct WitnessDatabase {
    data: Vector<Literal>,
    offset: Vector<usize>,
}

impl ClauseStorage for WitnessDatabase {
    fn open_clause(&mut self) -> Clause {
        self.offset.pop();
        let witness = Clause::from_usize(self.offset.len());
        self.offset.push(self.data.len());
        witness
    }
    fn push_literal(&mut self, literal: Literal, _verbose: bool) {
        if literal.is_zero() {
            self.close_witness();
        } else {
            self.data.push(literal);
        }
    }
}

impl Default for WitnessDatabase {
    /// Create an empty witness database.
    fn default() -> WitnessDatabase {
        let mut db = WitnessDatabase {
            data: Vector::new(),
            offset: Vector::new(),
        };
        db.offset.push(0);
        db
    }
}

impl WitnessDatabase {
    /// Create a database from raw elements; used only for tests.
    #[cfg(test)]
    pub fn from(data: Vector<Literal>, offset: Vector<usize>) -> WitnessDatabase {
        WitnessDatabase { data, offset }
    }
    /// Finish the current witness.
    /// Similar to [`close_clause()`](struct.ClauseDatabase.html#method.close_clause).
    fn close_witness(&mut self) {
        self.offset.push(self.data.len())
    }
    /// Give the DIMACS representation of a witness.
    ///
    /// Similar to [`clause_to_string()`](struct.ClauseDatabase.html#method.clause_to_string).
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
    /// The literals in the the witness.
    pub fn witness(&self, clause: Clause) -> &[Literal] {
        &self.data[self.witness_range(clause)]
    }
    /// The internal offsets of the literals in the the witness.
    pub fn witness_range(&self, clause: Clause) -> Range<usize> {
        self.offset[clause.as_offset()]..self.offset[clause.as_offset() + 1]
    }
    /// See [`Vec::shrink_to_fit()`](https://doc.rust-lang.org/std/vec/struct.Vec.html#method.shrink_to_fit).
    pub fn shrink_to_fit(&mut self) {
        // TODO: Should be (nightly) shrink_to(len() + 1), see rate::close_proof.
        self.data.push(Literal::new(0));
        self.data.shrink_to_fit();
        self.data.pop();
        self.offset.push(0);
        self.offset.shrink_to_fit();
        self.offset.pop();
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

/// Return true if this clause is of size one (special type of unit clause).
fn is_size_1_clause(clause: &[Literal]) -> bool {
    clause.len() == 2 && (clause[0] == Literal::BOTTOM || clause[1] == Literal::BOTTOM)
}

/// Sort a clause by its internal encoding
fn sort_clause(clause: &mut [Literal]) {
    let _sort_literally = |&literal: &Literal| literal.decode();
    let _sort_magnitude = |&literal: &Literal| literal.encoding;
    clause.sort_unstable_by_key(_sort_literally);
}
