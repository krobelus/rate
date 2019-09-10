use crate::{
    clause::{Clause , ProofStep} ,
    literal::{Literal , Variable} ,
    memory::{Stack} ,
} ;

#[derive(Debug)]
pub struct Proof {
    pub maxvar : Variable ,
    pub cnf_clauses : u64 ,
    pub proof_introductions : u64 ,
    pub proof_deletions : u64 ,
    pub proof_srs : u64 ,
    pub proof_start : Clause ,
    pub pivots : Stack<Literal> ,
    pub proof : Stack<ProofStep> ,
}
impl Proof {
    pub fn new() -> Proof {
        Proof {
            maxvar : Variable::new(0) ,
            cnf_clauses : 0u64 ,
            proof_introductions : 0u64 ,
            proof_deletions : 0u64 ,
            proof_srs : 0u64 ,
            proof_start : Clause::new(0) ,
            pivots : Stack::<Literal>::new() ,
            proof : Stack::<ProofStep>::new() ,
        }
    }
}