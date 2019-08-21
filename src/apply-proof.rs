#![allow(dead_code)]
#![allow(unused_macros)]
#![allow(clippy::collapsible_if)]

#[macro_use]
mod output;
#[macro_use]
mod memory;
mod clause;
mod clausedatabase;
mod config;
mod features;
mod literal;
mod parser;

#[macro_use(Serialize, Deserialize)]
extern crate serde_derive;

use clap::Arg;
use std::{
    fs::File,
    io::{self, BufWriter, Write},
};

use crate::{
    clause::{write_clause, Clause},
    parser::{
        clause_db, is_binary_drat, parse_proof_step, read_file, run_parser_on_formula,
        FixedSizeHashTable, HashTable, Input, Parser, ProofParserState, Result, SimpleInput,
    },
};

fn main() -> Result<()> {
    crate::config::signals();
    let matches = clap::App::new("apply-proof")
        .version(env!("CARGO_PKG_VERSION"))
        .about(
            "Apply a clausal proof up to a given line number and
output the accumulated formula to <OUTPUT>.cnf and the
remaining proof to <OUTPUT>.drat",
        )
        .arg(
            Arg::with_name("INPUT")
                .required(true)
                .help("input file in DIMACS format"),
        )
        .arg(Arg::with_name("PROOF").required(true).help("proof file"))
        .arg(
            Arg::with_name("LINE NUMBER")
                .required(true)
                .help("number of proof steps to apply"),
        )
        .arg(
            Arg::with_name("OUTPUT")
                .required(true)
                .help("name for output formula and proof"),
        )
        .get_matches();
    let formula_filename = matches.value_of("INPUT").unwrap();
    let proof_filename = matches.value_of("PROOF").unwrap();
    let line_number = matches
        .value_of("LINE NUMBER")
        .unwrap()
        .parse()
        .unwrap_or_else(|err| die!("Line number must be an integer: {}", err));
    let output_name = matches.value_of("OUTPUT").unwrap();
    let mut parser = Parser::new();
    parser.verbose = false;
    let mut clause_ids = FixedSizeHashTable::new();
    run_parser_on_formula(
        &mut parser,
        Some(formula_filename),
        proof_filename,
        &mut clause_ids,
    );
    let mut state = ProofParserState::Start;
    let binary = is_binary_drat(read_file(proof_filename).take(10));
    let mut proof_input = SimpleInput::new(read_file(&proof_filename), binary);
    fn open(name: &str) -> impl Write {
        BufWriter::new(
            File::create(name)
                .unwrap_or_else(|err| die!("Failed to open output file {}: {}", name, err)),
        )
    }
    let mut formula_output = open(&format!("{}.cnf", output_name));
    let mut proof_output = open(&format!("{}.drat", output_name));
    for _ in 0..line_number {
        let _result = parse_proof_step(
            &mut parser,
            &mut clause_ids,
            &mut proof_input,
            binary,
            &mut state,
        )
        .expect("Failed to parse proof step");
        assert!(_result == Some(()));
    }
    let mut write_formula = || {
        let number_of_active_clauses = (0..clause_db().number_of_clauses())
        .map(Clause::new)
        .filter(|&clause| clause_ids.clause_is_active(clause))
        .count();
        write!(&mut formula_output, "p cnf {} {}\n", parser.maxvar, number_of_active_clauses)?;
        for clause in (0..clause_db().number_of_clauses()).map(Clause::new) {
            if !clause_ids.clause_is_active(clause) {
                continue;
            }
            write_clause(&mut formula_output, clause_db().clause(clause).iter())?;
            write!(&mut formula_output, "\n")?;
        }
        let result : io::Result<()> = Ok(());
        result
    };
    write_formula().expect("Failed to write formula");
    while let Some(byte) = proof_input.next() {
        proof_output.write(&[byte]).expect("Failed to write proof");
    }
    Ok(())
}
