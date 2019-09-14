//! Verify a SICK certificate

#![allow(dead_code)]
#![allow(unused_macros)]
#![allow(clippy::collapsible_if)]

#[macro_use]
mod output;
#[macro_use]
mod memory;
mod assignment;
mod clause;
mod clausedatabase;
mod config;
mod features;
mod hashtable;
mod input;
mod literal;
mod parser;
mod proof;
mod sick;

#[macro_use(Serialize, Deserialize)]
extern crate serde_derive;

use clap::Arg;
use std::io::Read;
use toml;

use crate::{
    assignment::{stable_under_unit_propagation, Assignment},
    clause::Reason,
    clausedatabase::{clause_db, witness_db},
    config::ProofFormat,
    hashtable::HashTable,
    literal::Literal,
    memory::{Array, Vector},
    output::{solution, RuntimeError},
    parser::{open_file, proof_format_by_extension, BinaryMode, Parser, ParsingInfo, SyntaxFormat},
    sick::Sick,
};

#[allow(clippy::cognitive_complexity)]
fn main() -> Result<(), RuntimeError> {
    crate::config::signals();
    let app = clap::App::new("sick-check")
        .version(env!("CARGO_PKG_VERSION"))
        .about("Verify SICK certificates stating why a DRAT proof is incorrect")
        .arg(
            Arg::with_name("INPUT")
                .required(true)
                .help("input file in DIMACS format"),
        )
        .arg(
            Arg::with_name("PROOF")
                .required(true)
                .help("proof file in DRAT format"),
        )
        .arg(
            Arg::with_name("CERTIFICATE")
                .required(true)
                .help("falsifying certificate file in SICK format"),
        );
    let matches = app.get_matches();
    let formula_filename = matches.value_of("INPUT").unwrap();
    let proof_filename = matches.value_of("PROOF").unwrap();
    let sick_filename = matches.value_of("CERTIFICATE").unwrap();
    let proof_file_proof_format = proof_format_by_extension(proof_filename);

    let mut toml_str = String::new();
    let mut sick_file = open_file(sick_filename);
    sick_file
        .read_to_string(&mut toml_str)
        .unwrap_or_else(|err| die!("Failed to read SICK file: {}", err));
    let sick: Sick =
        toml::from_str(&toml_str).unwrap_or_else(|err| die!("Failed to parse SICK file: {}", err));
    let proof_format = match sick.proof_format.as_ref() {
        "DRAT-arbitrary-pivot" => ProofFormat::DratAnyPivot,
        "DRAT-pivot-is-first-literal" => ProofFormat::DratFirstPivot,
        "PR" => ProofFormat::DprFirstPivot,
        format => die!("Unsupported proof format: {}", format),
    };
    requires!(
        proof_format.dpr() == proof_file_proof_format.dpr()
            && proof_format.drat() == proof_file_proof_format.drat()
    );
    let mut parse_info = ParsingInfo::new();
    {
        let parser = Parser::new(
            parse_info,
            formula_filename,
            SyntaxFormat::Dimacs,
            BinaryMode::Text,
        )?;
        parse_info = parser.parse()?;
    }
    {
        let mut parser = Parser::new(
            parse_info,
            proof_filename,
            SyntaxFormat::from(proof_format),
            BinaryMode::DratTrimDetection,
        )?;
        parser.max_proof_steps = Some(sick.proof_step);
        parse_info = parser.parse()?;
    }

    if sick.proof_step > parse_info.proof.proof.len() {
        die!(
            "Specified proof step exceeds proof size: {}",
            sick.proof_step
        );
    }
    let lemma = parse_info.proof.proof[sick.proof_step - 1].clause();
    requires!(lemma.index < clause_db().number_of_clauses());
    let mut assignment = Assignment::new(parse_info.proof.maxvar);
    for &literal in &sick.natural_model {
        if assignment[-literal] {
            die!(
                "Natural model is inconsistent in variable {}",
                literal.variable()
            );
        }
        assignment.push(literal, Reason::assumed());
    }
    if clause_db().clause(lemma).is_empty() {
        comment!("Tried to introduce empty clause but natural model is consistent");
        solution("ACCEPTED");
        return Ok(());
    }
    let natural_model_length = assignment.len();

    for &literal in clause_db().clause(lemma) {
        if !assignment[-literal] {
            die!("Natural model does not falsify lemma literal {}", literal);
        }
    }
    // Delete the lemma, so it is not considered to be part of the formula.
    parse_info.table.delete_clause(lemma);
    for &clause in &parse_info.table {
        if clause < lemma && !stable_under_unit_propagation(&assignment, clause_db().clause(clause))
        {
            die!(
                "Natural model is not the shared UP-model for clause {}",
                clause_db().clause_to_string(clause)
            );
        }
    }
    let witnesses = sick.witness.unwrap_or_else(Vector::new);
    const PIVOT: &str = "RAT requires to specify a pivot for each witness";
    if proof_format.drat() {
        let mut specified_pivots: Vec<Literal> = witnesses
            .iter()
            .map(|witness| witness.pivot.expect(PIVOT))
            .collect();
        let mut expected_pivots: Vec<Literal> = clause_db()
            .clause(lemma)
            .iter()
            .filter(|&&l| l != Literal::BOTTOM)
            .cloned()
            .collect();
        if !specified_pivots.is_empty() {
            match proof_format {
                ProofFormat::DratAnyPivot => {
                    specified_pivots.sort();
                    expected_pivots.sort();
                    if specified_pivots != expected_pivots {
                        die!("Using proof_format = \"{}\": you need exactly one counterexample for each pivot in the lemma\nlemma: {}\npivots: {}",
                        sick.proof_format,
                        expected_pivots.iter().map(|l| format!("{}", l)).collect::<Vec<_>>().join(" "),
                        specified_pivots.iter().map(|l| format!("{}", l)).collect::<Vec<_>>().join(" "),
                        )
                    }
                }
                ProofFormat::DratFirstPivot => {
                    if specified_pivots.len() > 1 {
                        die!("Using proof_format = \"{}\", the first literal must be specified as pivot and nothing else",
                        sick.proof_format);
                    }
                }
                _ => unreachable!(),
            }
        }
    }
    for witness in witnesses {
        clause_db().open_clause();
        for &literal in &witness.failing_clause {
            clause_db().push_literal(literal);
        }
        clause_db().push_literal(Literal::new(0));
        let failing_clause_tmp = clause_db().last_clause();
        let failing_clause = parse_info
            .table
            .find_equal_clause(failing_clause_tmp, /*delete=*/ false)
            .unwrap_or_else(|| {
                die!(
                    "Failing clause is not present in the formula: {}",
                    clause_db().clause_to_string(failing_clause_tmp)
                );
            });
        clause_db().pop_clause();
        let lemma_slice = clause_db().clause(lemma);
        for &literal in &witness.failing_model {
            if assignment[-literal] {
                die!(
                    "Failing model is inconsistent in variable {}",
                    literal.variable()
                );
            }
            assignment.push(literal, Reason::assumed());
        }
        let resolvent: Vec<Literal> = if proof_format.drat() {
            let pivot = witness.pivot.expect(PIVOT);
            lemma_slice
                .iter()
                .chain(witness.failing_clause.iter())
                .filter(|&&lit| lit.variable() != pivot.variable())
                .cloned()
                .collect()
        } else {
            requires!(proof_format.dpr());
            let mut literal_is_in_witness =
                Array::new(false, parse_info.proof.maxvar.array_size_for_literals());
            for &literal in witness_db().witness(lemma) {
                literal_is_in_witness[literal] = true;
            }
            if witness
                .failing_clause
                .iter()
                .any(|&lit| literal_is_in_witness[lit])
            {
                die!(
                    "Reduct of failing clause {} is satisified under witness {}",
                    clause_db().clause_to_string(failing_clause),
                    witness_db().witness_to_string(failing_clause)
                )
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
        };
        for &literal in &resolvent {
            if !assignment[-literal] {
                die!(
                    "Failing model does not falsify resolvent literal {}",
                    literal
                );
            }
        }
        for &clause in &parse_info.table {
            if clause < lemma
                && !stable_under_unit_propagation(&assignment, clause_db().clause(clause))
            {
                die!(
                    "Failing model is not the shared UP-model for clause {}",
                    clause_db().clause_to_string(clause)
                );
            }
        }
        while assignment.len() > natural_model_length {
            assignment.pop();
        }
    }
    solution("ACCEPTED");
    Ok(())
}
