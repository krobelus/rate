//! Clause hash tables

use crate::{
    clause::{Clause},
    clausedatabase::{clause_db},
    memory::{HeapSpace, Offset, SmallVector, Vector},
    literal::{Literal},
};
use std::{
    collections::HashMap,
    hash::{Hash, Hasher},
    slice,
};

/// A hash table that maps clauses (sets of literals) to clause identifiers.
pub trait HashTable {
    /// Add a new clause to the hashtable.
    fn add_clause(&mut self, clause: Clause);
    /// Find a clause that is equivalent to given clause.
    ///
    /// If delete is true, delete the found clause.
    fn find_equal_clause(&mut self, needle: Clause, delete: bool) -> Option<Clause>;
    /// Return true if this exact clause is active.
    fn clause_is_active(&self, needle: Clause) -> bool;
    /// Delete this exact clause, return true if that succeeded.
    fn delete_clause(&mut self, needle: Clause) -> bool;
}

/// A hash table with a fixed size
///
/// This should work exactly like the one used in `drat-trim`.
/// Given that we expect the number of clauses in the hash table
/// not to exceed a couple million this should be faster and leaner than
/// [DynamicHashTable](struct.DynamicHashTable.html).
pub struct FixedSizeHashTable(Vector<Vector<Clause>>);

/// Return the hash bucket to which this clause belongs.
fn bucket_index(clause: &[Literal]) -> usize {
    clause_hash(clause) % FixedSizeHashTable::SIZE
}

impl FixedSizeHashTable {
    /// The number of buckets in our hash table (`drat-trim` uses a million)
    const SIZE: usize = 2 * 1024 * 1024;
    /// The initial size of each bucket.
    ///
    /// We could increase this to at least use `malloc_usable_size` (system-dependent).
    const BUCKET_INITIAL_SIZE: u16 = 4;
    /// Allocate the hash table.
    #[allow(clippy::new_without_default)]
    pub fn new() -> FixedSizeHashTable {
        FixedSizeHashTable(Vector::from_vec(vec![
            Vector::with_capacity(
                FixedSizeHashTable::BUCKET_INITIAL_SIZE.into()
            );
            FixedSizeHashTable::SIZE
        ]))
    }
}

/// An iterator over the elements of the hash table
pub struct FixedSizeHashTableIterator<'a> {
    /// The iterator over the buckets
    buckets: slice::Iter<'a, Vector<Clause>>,
    /// The iterator over a single bucket
    bucket: slice::Iter<'a, Clause>,
}

impl<'a> Iterator for FixedSizeHashTableIterator<'a> {
    type Item = &'a Clause;
    fn next(&mut self) -> Option<Self::Item> {
        self.bucket.next().or_else(|| {
            self.buckets.next().and_then(|next_bucket| {
                self.bucket = next_bucket.iter();
                self.bucket.next()
            })
        })
    }
}

impl<'a> IntoIterator for &'a FixedSizeHashTable {
    type Item = &'a Clause;
    type IntoIter = FixedSizeHashTableIterator<'a>;
    fn into_iter(self) -> Self::IntoIter {
        FixedSizeHashTableIterator {
            buckets: self.0.iter(),
            bucket: self.0[0].iter(),
        }
    }
}

impl HashTable for FixedSizeHashTable {
    fn add_clause(&mut self, clause: Clause) {
        self.0[bucket_index(clause_db().clause(clause))].push(clause);
    }
    fn find_equal_clause(&mut self, needle: Clause, delete: bool) -> Option<Clause> {
        let bucket = &mut self.0[bucket_index(clause_db().clause(needle))];
        for offset in 0..bucket.len() {
            let clause = bucket[offset];
            if clause_db().clause(needle) == clause_db().clause(clause) {
                if delete {
                    bucket.swap_remove(offset);
                }
                return Some(clause);
            }
        }
        None
    }
    fn clause_is_active(&self, needle: Clause) -> bool {
        self.0[bucket_index(clause_db().clause(needle))]
            .iter()
            .any(|&clause| needle == clause)
    }
    fn delete_clause(&mut self, needle: Clause) -> bool {
        self.0[bucket_index(clause_db().clause(needle))]
            .iter()
            .position(|&clause| needle == clause)
            .map(|offset| self.0[bucket_index(clause_db().clause(needle))].swap_remove(offset))
            .is_some()
    }
}

impl HeapSpace for FixedSizeHashTable {
    fn heap_space(&self) -> usize {
        self.0.heap_space()
    }
}

/// A hashtable that simply uses the standard `HashMap`
///
/// This maps clauses (by equality) to a a list of clause identifiers.
/// We chose `SmallVector<Clause>` for the latter because most clauses are
/// not duplicated. This way we can avoid one allocation for unique clauses.
pub struct DynamicHashTable(HashMap<ClauseHashEq, SmallVector<Clause>>);

impl DynamicHashTable {
    /// Create a new empty hash table.
    pub fn new() -> DynamicHashTable {
        DynamicHashTable(HashMap::new())
    }
}
impl HashTable for DynamicHashTable {
    fn add_clause(&mut self, clause: Clause) {
        let key = ClauseHashEq(clause);
        self.0
            .entry(key)
            .or_insert_with(SmallVector::default)
            .push(clause)
    }
    fn find_equal_clause(&mut self, needle: Clause, delete: bool) -> Option<Clause> {
        self.0
            .get_mut(&ClauseHashEq(needle))
            .and_then(|equal_clauses| {
                let first = equal_clauses.first();
                invariant!(first != Some(needle));
                if delete {
                    equal_clauses.swap_remove(0);
                }
                first
            })
    }
    // these are not optimized but only used in sick-check
    fn clause_is_active(&self, needle: Clause) -> bool {
        self.0
            .get(&ClauseHashEq(needle))
            .map_or(false, |vector| !vector.is_empty())
    }
    fn delete_clause(&mut self, needle: Clause) -> bool {
        self.0
            .get_mut(&ClauseHashEq(needle))
            .map_or(false, |equal_clauses| {
                let mut i = 0;
                while equal_clauses[i] != needle {
                    i += 1;
                    invariant!(i < equal_clauses.len());
                }
                invariant!(i == 0);
                equal_clauses.swap_remove(i);
                true
            })
    }
}

/// Wrapper struct around clause implementing hash and equality by looking
/// at the literals in the clause database.
#[derive(Debug, Eq, Clone, Copy)]
pub struct ClauseHashEq(pub Clause);

impl Hash for ClauseHashEq {
    fn hash<H: Hasher>(&self, hasher: &mut H) {
        clause_hash(clause_db().clause(self.0)).hash(hasher);
    }
}

impl PartialEq for ClauseHashEq {
    fn eq(&self, other: &ClauseHashEq) -> bool {
        clause_db().clause(self.0) == clause_db().clause(other.0)
    }
}

/// Compute the hash of a clause. This is the same hash function `drat-trim` uses.
fn clause_hash(clause: &[Literal]) -> usize {
    let mut sum: usize = 0;
    let mut prod: usize = 1;
    let mut xor: usize = 0;
    for &literal in clause {
        prod = prod.wrapping_mul(literal.as_offset());
        sum = sum.wrapping_add(literal.as_offset());
        xor ^= literal.as_offset();
    }
    ((1023 * sum + prod) ^ (31 * xor))
}
