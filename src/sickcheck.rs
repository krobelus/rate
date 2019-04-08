#![allow(dead_code)]
#![allow(unused_macros)]
#![feature(
    try_trait,
    alloc,
    ptr_wrapping_offset_from,
    raw_vec_internals,
    range_contains,
    const_vec_new,
    vec_resize_default,
    result_map_or_else,
    stmt_expr_attributes
)]

#[macro_use]
mod output;
#[macro_use]
mod memory;
mod assignment;
mod clause;
mod clausedatabase;
mod config;
mod literal;
mod parser;

extern crate alloc;
#[macro_use(Serialize, Deserialize)]
extern crate serde_derive;

use clap::Arg;
use std::{fs::File, io::Read, process::exit};
use toml;

use crate::{
    assignment::{stable_under_unit_propagation, Assignment},
    clause::{Clause, Reason},
    config::RedundancyProperty,
    literal::Literal,
    memory::{Array, Offset},
    output::solution,
    parser::{run_parser, ClauseHashEq, HashTable, Parser},
};

#[derive(Serialize, Deserialize, Debug)]
struct Sick {
    proof_format: String,
    proof_step: usize,
    natural_model: Vec<Literal>,
    witness: Option<Vec<Witness>>,
}

#[derive(Serialize, Deserialize, Debug)]
struct Witness {
    failing_clause: Vec<Literal>,
    failing_model: Vec<Literal>,
    pivot: Option<Literal>,
}

#[allow(clippy::cyclomatic_complexity)]
fn main() {
    let app = clap::App::new("sickcheck")
        .version(env!("CARGO_PKG_VERSION"))
        .about(env!("CARGO_PKG_DESCRIPTION"))
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
    let proof_file_redundancy_property = if proof_filename.ends_with(".drat") {
        RedundancyProperty::RAT
    } else if proof_filename.ends_with(".pr") || proof_filename.ends_with(".dpr") {
        RedundancyProperty::PR
    } else {
        comment!("unknown file extension, defaulting to RAT checking");
        RedundancyProperty::RAT
    };

    let mut toml_str = String::new();
    let mut sick_file = File::open(sick_filename)
        .unwrap_or_else(|err| die!("Failed to open SICK certificate: {}", err));
    sick_file
        .read_to_string(&mut toml_str)
        .unwrap_or_else(|err| die!("Failed to read SICK file: {}", err));
    let sick: Sick =
        toml::from_str(&toml_str).unwrap_or_else(|err| die!("Failed to parse SICK file: {}", err));
    let mut need_pivot = false;
    let redundancy_property = match sick.proof_format.as_ref() {
        "DRAT-arbitrary-pivot" => {
            need_pivot = true;
            RedundancyProperty::RAT
        }
        "DRAT-pivot-is-first-literal" => RedundancyProperty::RAT,
        "PR" => RedundancyProperty::PR,
        format => die!("Unsupported proof format: {}", format),
    };
    requires!(redundancy_property == proof_file_redundancy_property);
    let mut clause_ids = HashTable::new();
    let mut parser = Parser::new(proof_file_redundancy_property);
    parser.max_proof_steps = Some(sick.proof_step);
    run_parser(
        &mut parser,
        formula_filename,
        proof_filename,
        &mut clause_ids,
    );

    if sick.proof_step - 1 >= parser.proof.len() {
        die!(
            "Specified proof step exceeds proof size: {}",
            sick.proof_step
        );
    }
    let lemma = parser.proof[sick.proof_step - 1].clause();
    requires!(lemma.index < parser.clause_db.number_of_clauses());
    let mut assignment = Assignment::new(parser.maxvar);
    for &literal in &sick.natural_model {
        if assignment[-literal] {
            die!(
                "Natural model is inconsistent in variable {}",
                literal.variable()
            );
        }
        assignment.push(literal, Reason::assumed());
    }
    if parser.clause_db.clause(lemma).empty() {
        comment!("Tried to introduce empty clause but natural model is consistent");
        solution("ACCEPTED");
        exit(0);
    }
    let natural_model_length = assignment.len();

    for &literal in parser.clause_db.clause(lemma) {
        if !assignment[-literal] {
            die!("Natural model does not falsify lemma literal {}", literal);
        }
    }
    // Delete the lemma, so it is not considered to be part of the formula.
    clause_ids
        .get_mut(&ClauseHashEq(lemma))
        .map(|clause_stack| clause_stack.swap_remove(0));
    fn clause_is_active(clause_ids: &HashTable, needle: Clause) -> bool {
        clause_ids
            .get(&ClauseHashEq(needle))
            .map_or(false, |stack| !stack.to_vec().is_empty())
    }
    for clause in Clause::range(0, lemma) {
        if clause_is_active(&clause_ids, clause) {
            if !stable_under_unit_propagation(&assignment, parser.clause_db.clause(clause)) {
                die!(
                    "Natural model is not a UP-model for clause {}",
                    parser.clause_db.clause_to_string(clause)
                );
            }
        }
    }
    for witness in &sick.witness.unwrap_or_else(|| vec![]) {
        parser.clause_db.open_clause();
        for &literal in &witness.failing_clause {
            parser.clause_db.push_literal(literal);
        }
        parser.clause_db.push_literal(Literal::new(0));
        let failing_clause_tmp = parser.clause_db.last_clause();
        let failing_clause = clause_ids
            .get(&ClauseHashEq(failing_clause_tmp))
            .and_then(|stack| stack.to_vec().get(0).cloned())
            .unwrap_or_else(|| {
                die!(
                    "Failing clause is not present in the formula: {}",
                    parser.clause_db.clause_to_string(failing_clause_tmp),
                )
            });
        parser.clause_db.pop_clause();
        let lemma_slice = parser.clause_db.clause(lemma);
        for &literal in &witness.failing_model {
            if assignment[-literal] {
                die!(
                    "Failing model is inconsistent in variable {}",
                    literal.variable()
                );
            }
            assignment.push(literal, Reason::assumed());
        }
        let resolvent: Vec<Literal> = match redundancy_property {
            RedundancyProperty::RAT => {
                let pivot = if need_pivot {
                    witness.pivot.expect("Format requires to specify pivot")
                } else {
                    parser.clause_pivot[lemma.as_offset()]
                };
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
                    die!(
                        "Reduct of failing clause {} is satisified under witness {}",
                        parser.clause_db.clause_to_string(failing_clause),
                        parser.witness_db.witness_to_string(failing_clause)
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
            }
        };
        for &literal in &resolvent {
            if !assignment[-literal] {
                die!(
                    "Failing model does not falsify resolvent literal {}",
                    literal
                );
            }
        }
        for clause in Clause::range(0, lemma) {
            if clause_is_active(&clause_ids, clause) {
                if !stable_under_unit_propagation(&assignment, parser.clause_db.clause(clause)) {
                    die!(
                        "Failing model is not a UP-model for clause {}",
                        parser.clause_db.clause_to_string(clause)
                    );
                }
            }
        }
        while assignment.len() > natural_model_length {
            assignment.pop();
        }
    }
    solution("ACCEPTED");
}
