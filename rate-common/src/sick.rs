//! SICK incorrectness certificates

use crate::{
    as_error,
    assignment::{stable_under_unit_propagation, Assignment},
    clause::{Reason, RedundancyProperty},
    clausedatabase::ClauseStorage,
    literal::Literal,
    memory::{Array, HeapSpace, Vector},
    parser::{run_parser, HashTable, Parser},
    puts, requires,
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

/// Check a SICK certificate and prints an appropriate error message.
/// Returns true if accepted.
pub fn check_incorrectness_certificate(
    formula_filename: &str,
    proof_filename: &str,
    sick: Sick,
    verbose: bool,
) -> bool {
    match check_incorrectness_certificate_aux(formula_filename, proof_filename, sick, verbose) {
        Ok(()) => true,
        Err(string) => {
            as_error!({
                puts!("{}\n", &string);
                puts!("Proof claimed incorrect but validation failed, please report a bug!\n");
            });
            false
        }
    }
}

/// Parses both formula and proof and checks the SICK certificate.
/// Returns an error of what went wrong.
fn check_incorrectness_certificate_aux(
    formula_filename: &str,
    proof_filename: &str,
    sick: Sick,
    verbose: bool,
) -> Result<(), String> {
    let redundancy_property = match sick.proof_format.as_ref() {
        "DRAT-arbitrary-pivot" => RedundancyProperty::RAT,
        "DRAT-pivot-is-first-literal" => RedundancyProperty::RAT,
        "PR" => RedundancyProperty::PR,
        format => return Err(format!("Unsupported proof format: {}", format)),
    };
    let mut clause_ids = HashTable::new();
    let mut parser = Parser {
        max_proof_steps: sick.proof_step,
        verbose,
        ..Parser::default()
    };
    run_parser(
        &mut parser,
        formula_filename,
        proof_filename,
        &mut clause_ids,
    );

    let mut assignment = Assignment::new(parser.maxvar);
    for &literal in &sick.natural_model {
        if assignment[-literal] {
            return Err(format!(
                "Natural model is inconsistent in variable {}",
                literal.variable()
            ));
        }
        assignment.push(literal, Reason::assumed());
    }
    let proof_step = match sick.proof_step {
        Some(proof_step) => proof_step,
        None => {
            return Ok(());
        }
    };
    if proof_step > parser.proof.len() {
        return Err(format!(
            "Specified proof step exceeds proof size: {}",
            proof_step
        ));
    }
    let lemma = parser.proof[proof_step - 1].clause();
    requires!(lemma.index < parser.clause_db.number_of_clauses());
    if parser.clause_db.clause(lemma).is_empty() {
        return Ok(());
    }
    let natural_model_length = assignment.len();

    for &literal in parser.clause_db.clause(lemma) {
        if !assignment[-literal] {
            return Err(format!(
                "Natural model does not falsify lemma literal {}",
                literal
            ));
        }
    }
    // Delete the lemma, so it is not considered to be part of the formula.
    clause_ids.delete_clause(&parser.clause_db, lemma);
    for &clause in &clause_ids {
        if clause < lemma
            && !stable_under_unit_propagation(&assignment, parser.clause_db.clause(clause))
        {
            return Err(format!(
                "Natural model is not the shared UP-model for clause {}",
                parser.clause_db.clause_to_string(clause)
            ));
        }
    }
    let witnesses = sick.witness.unwrap_or_else(Vector::new);
    const PIVOT: &str = "RAT requires to specify a pivot for each witness";
    if redundancy_property == RedundancyProperty::RAT {
        let mut specified_pivots: Vec<Literal> = witnesses
            .iter()
            .map(|witness| witness.pivot.expect(PIVOT))
            .collect();
        let mut expected_pivots: Vec<Literal> = parser
            .clause_db
            .clause(lemma)
            .iter()
            .filter(|&&l| l != Literal::BOTTOM)
            .cloned()
            .collect();
        if !specified_pivots.is_empty() {
            match sick.proof_format.as_ref() {
                "DRAT-arbitrary-pivot" => {
                    specified_pivots.sort();
                    expected_pivots.sort();
                    if specified_pivots != expected_pivots {
                        return Err(format!("Using proof_format = \"{}\": you need exactly one counterexample for each pivot in the lemma\nlemma: {}\npivots: {}",
                        sick.proof_format,
                        expected_pivots.iter().map(|l| format!("{}", l)).collect::<Vec<_>>().join(" "),
                        specified_pivots.iter().map(|l| format!("{}", l)).collect::<Vec<_>>().join(" "),
                        ));
                    }
                }
                "DRAT-pivot-is-first-literal" => {
                    if specified_pivots.len() > 1 {
                        return Err(format!("Using proof_format = \"{}\", the first literal must be specified as pivot and nothing else",
                        sick.proof_format));
                    }
                }
                _ => unreachable!(),
            };
        }
    }
    for witness in witnesses {
        parser.clause_db.open_clause();
        for &literal in &witness.failing_clause {
            parser.clause_db.push_literal(literal, verbose);
        }
        parser.clause_db.push_literal(Literal::new(0), verbose);
        let failing_clause_tmp = parser.clause_db.last_clause();
        let failing_clause = match clause_ids.find_equal_clause(
            &parser.clause_db,
            failing_clause_tmp,
            /*delete=*/ false,
        ) {
            Some(clause) => clause,
            None => {
                return Err(format!(
                    "Failing clause is not present in the formula: {}",
                    parser.clause_db.clause_to_string(failing_clause_tmp)
                ))
            }
        };
        parser.clause_db.pop_clause();
        let lemma_slice = parser.clause_db.clause(lemma);
        for &literal in &witness.failing_model {
            if assignment[-literal] {
                return Err(format!(
                    "Failing model is inconsistent in variable {}",
                    literal.variable()
                ));
            }
            assignment.push(literal, Reason::assumed());
        }
        let resolvent: Vec<Literal> = match redundancy_property {
            RedundancyProperty::RAT => {
                let pivot = witness.pivot.expect(PIVOT);
                lemma_slice
                    .iter()
                    .chain(witness.failing_clause.iter())
                    .filter(|&&lit| lit.variable() != pivot.variable())
                    .cloned()
                    .collect()
            }
            RedundancyProperty::PR => {
                let mut literal_is_in_witness =
                    Array::new(false, parser.maxvar.array_size_for_literals());
                for &literal in parser.witness_db.witness(lemma) {
                    literal_is_in_witness[literal] = true;
                }
                if witness
                    .failing_clause
                    .iter()
                    .any(|&lit| literal_is_in_witness[lit])
                {
                    return Err(format!(
                        "Reduct of failing clause {} is satisified under witness {}",
                        parser.clause_db.clause_to_string(failing_clause),
                        parser.witness_db.witness_to_string(failing_clause)
                    ));
                }
                lemma_slice
                    .iter()
                    .chain(
                        witness
                            .failing_clause
                            .iter()
                            .filter(|&&lit| !literal_is_in_witness[-lit]),
                    )
                    .cloned()
                    .collect()
            }
        };
        // TODO also for PR
        if redundancy_property == RedundancyProperty::RAT {
            for &literal in &resolvent {
                if !assignment[-literal] {
                    return Err(format!(
                        "Failing model does not falsify resolvent literal {}",
                        literal
                    ));
                }
            }
        }
        for &clause in &clause_ids {
            if clause < lemma
                && !stable_under_unit_propagation(&assignment, parser.clause_db.clause(clause))
            {
                return Err(format!(
                    "Failing model is not the shared UP-model for clause {}",
                    parser.clause_db.clause_to_string(clause)
                ));
            }
        }
        while assignment.len() > natural_model_length {
            assignment.pop();
        }
    }
    Ok(())
}
