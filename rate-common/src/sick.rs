//! SICK incorrectness certificates

use crate::{
    literal::Literal,
    memory::{HeapSpace, Vector},
};
use serde_derive::{Deserialize, Serialize};

/// A SICK certificate.
#[derive(Serialize, Deserialize, Debug, Default)]
pub struct Sick {
    /// The string identifying the proof format
    pub proof_format: String,
    //// The line in the proof that failed
    pub proof_step: Option<usize>,
    /// The trail of the formula before any inference checks
    pub natural_model: Vector<Literal>,
    /// The list of witnesses (none for RUP, one for each pivot for RAT)
    pub witness: Option<Vector<Witness>>,
}

/// The refutation of an inference given a witness
#[derive(Clone, Serialize, Deserialize, Debug, Default)]
pub struct Witness {
    /// The candidate clause that failed to produce a conflict
    pub failing_clause: Vector<Literal>,
    /// The trail after the inference check failed
    pub failing_model: Vector<Literal>,
    /// If RAT, the pivot literal.
    pub pivot: Option<Literal>,
}

// Can't derive HeapSpace for Option<T> yet.
impl HeapSpace for Sick {
    fn heap_space(&self) -> usize {
        self.natural_model.heap_space() + self.witness.as_ref().map_or(0, HeapSpace::heap_space)
    }
}

impl HeapSpace for Witness {
    fn heap_space(&self) -> usize {
        self.failing_clause.heap_space() + self.failing_model.heap_space()
    }
}
