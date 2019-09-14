use crate::{
    clause::{Clause, ProofStep},
    literal::{Literal, Variable},
    memory::Vector,
};

#[derive(Debug)]
pub struct Proof {
    pub maxvar: Variable,
    pub cnf_clauses: u64,
    pub proof_introductions: u64,
    pub proof_deletions: u64,
    pub proof_srs: u64,
    pub proof_start: Clause,
    pub pivots: Vector<Literal>,
    pub proof: Vector<ProofStep>,
}
impl Proof {
    pub fn new() -> Proof {
        Proof {
            maxvar: Variable::new(0),
            cnf_clauses: 0u64,
            proof_introductions: 0u64,
            proof_deletions: 0u64,
            proof_srs: 0u64,
            proof_start: Clause::new(0),
            pivots: Vector::<Literal>::new(),
            proof: Vector::<ProofStep>::new(),
        }
    }
}
