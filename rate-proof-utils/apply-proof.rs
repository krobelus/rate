//! Apply a clausal proof up to a given line number and output the accumulated
//! formula and the remaining proof.

use clap::Arg;
use std::io::{self, Result, Write};

use rate_common::{
    clause::{write_clause, Clause},
    die, output,
    parser::{
        is_binary_drat, open_file_for_writing, parse_proof_step, read_compressed_file,
        run_parser_on_formula, HashTable, Parser, ProofParserState,
    },
};

/// Run `apply-proof`.
fn main() {
    output::panic_on_error(run())
}

/// Run `apply-proof`, possible returning an `io::Error`.
fn run() -> Result<()> {
    output::install_signal_handler();
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
    let mut parser = Parser {
        verbose: false,
        ..Parser::default()
    };
    let binary = is_binary_drat(proof_filename);
    let mut clause_ids = HashTable::new();
    run_parser_on_formula(
        &mut parser,
        formula_filename,
        proof_filename,
        &mut clause_ids,
    );
    let mut state = ProofParserState::Start;
    let mut proof_input = read_compressed_file(&proof_filename, binary);
    let stdout = io::stdout();
    let mut formula_output =
        open_file_for_writing(matches.value_of("FORMULA_OUTPUT").unwrap(), &stdout);
    let mut proof_output =
        open_file_for_writing(matches.value_of("PROOF_OUTPUT").unwrap(), &stdout);
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
        let number_of_active_clauses = (0..parser.clause_db.number_of_clauses())
            .map(Clause::new)
            .filter(|&clause| clause_ids.clause_is_active(&parser.clause_db, clause))
            .count();
        writeln!(
            &mut formula_output,
            "p cnf {} {}",
            parser.maxvar, number_of_active_clauses
        )?;
        for clause in (0..parser.clause_db.number_of_clauses()).map(Clause::new) {
            if !clause_ids.clause_is_active(&parser.clause_db, clause) {
                continue;
            }
            write_clause(&mut formula_output, parser.clause_db.clause(clause).iter())?;
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
