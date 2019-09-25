//! Apply a clausal proof up to a given line number and output the accumulated
//! formula and the remaining proof.

use ansi_term;
use clap::Arg;
use std::io::{Result, Write};

use rate_common::{
    clause::{write_clause, Clause},
    clausedatabase::{clause_db},
    die,
    hashtable::{FixedSizeHashTable, HashTable},
    input::Input,
    output::install_signal_handler,
    parser::{
        open_file_for_writing, parse_instruction,
        parse_formula, BinaryMode, Parser, ProofSyntax,
    },
    write_to_stdout,
};

/// Run `apply-proof`.
fn main() -> Result<()> {
    install_signal_handler();
    let matches = clap::App::new("apply-proof")
        .version(env!("CARGO_PKG_VERSION"))
        .about(
            "
Apply a clausal proof up to a given line number and output the accumulated
formula to <FORMULA_OUTPUT> and the remaining proof to <PROOF_OUTPUT>."
                .trim(),
        )
        .arg(
            Arg::with_name("INPUT")
                .required(true)
                .help("input formula file in DIMACS format"),
        )
        .arg(
            Arg::with_name("PROOF")
                .required(true)
                .help("input proof file in DRAT/DPR format"),
        )
        .arg(
            Arg::with_name("LINE NUMBER")
                .required(true)
                .help("number of proof steps to apply"),
        )
        .arg(
            Arg::with_name("FORMULA_OUTPUT")
                .required(true)
                .help("file for the output formula"),
        )
        .arg(
            Arg::with_name("PROOF_OUTPUT")
                .required(true)
                .help("file for the output proof"),
        )
        .get_matches();
    let formula_filename = matches.value_of("INPUT").unwrap();
    let proof_filename = matches.value_of("PROOF").unwrap();
    let line_number = matches
        .value_of("LINE NUMBER")
        .unwrap()
        .parse()
        .unwrap_or_else(|err| die!("Line number must be an integer: {}", err));
    let mut parser = Parser::new(ProofSyntax::Dpr); // todo: change this into option
    parser.verbose = false;
    let binary = BinaryMode::DratTrim.detect(proof_filename);
    let mut clause_ids = FixedSizeHashTable::new();
    let formula_input = Input::from_file(formula_filename, false);
    let mut proof_input = Input::from_file(&proof_filename, binary);
    let mut formula_output = open_file_for_writing(matches.value_of("FORMULA_OUTPUT").unwrap());
    let mut proof_output = open_file_for_writing(matches.value_of("PROOF_OUTPUT").unwrap());
    parse_formula(
        &mut parser,
        &mut clause_ids,
        formula_input,
    )?;
    for _ in 0..line_number {
        let _result = parse_instruction(
            &mut parser,
            &mut clause_ids,
            &mut proof_input,
            binary,
        )
        .expect("Failed to parse proof step");
        // assert!(_result == Some(()));
    }
    let mut write_formula = || {
        let number_of_active_clauses = (0..clause_db().number_of_clauses())
            .map(Clause::new)
            .filter(|&clause| clause_ids.clause_is_active(clause))
            .count();
        writeln!(
            &mut formula_output,
            "p cnf {} {}",
            parser.maxvar, number_of_active_clauses
        )?;
        for clause in (0..clause_db().number_of_clauses()).map(Clause::new) {
            if !clause_ids.clause_is_active(clause) {
                continue;
            }
            write_clause(&mut formula_output, clause_db().clause(clause).iter())?;
            writeln!(&mut formula_output)?;
        }
        let result: Result<()> = Ok(());
        result
    };
    write_formula().expect("Failed to write formula");
    for byte in proof_input {
        proof_output
            .write_all(&[byte])
            .expect("Failed to write proof");
    }
    Ok(())
}
