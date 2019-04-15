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
    stmt_expr_attributes,
    existential_type,
    try_from
)]
#![allow(clippy::collapsible_if)]

#[macro_use]
mod output;
#[macro_use]
mod memory;
mod clause;
mod clausedatabase;
mod config;
mod literal;
mod parser;

extern crate alloc;
#[macro_use(Serialize, Deserialize)]
extern crate serde_derive;

use std::{
    convert::TryInto,
    fs::File,
    io::{self, Write},
};

use crate::{
    clause::{write_clause, Clause, ProofStep},
    memory::{Offset, Stack},
    parser::{
        clause_is_active, finish_proof, is_binary_drat, parse_proof_step, read_file, run_parser,
        run_parser_on_formula, HashTable, Input, Parser, ProofParserState, Result,
    },
};
use clap::Arg;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum LineNumber {
    Invalid,
    Active(usize),
    Deleted,
}

impl Default for LineNumber {
    fn default() -> Self {
        LineNumber::Invalid
    }
}

struct Splitter<'a> {
    clause_line: Stack<LineNumber>,
    line: usize, // the next line number to append
    parser: Parser,
    clause_ids: HashTable,
    proof_input: Input,
    binary: bool,
    proof_file: &'a str,
    chunk: usize,
    total_chunks: usize,
}

fn main() {
    let matches = clap::App::new("split-proof")
        .version(env!("CARGO_PKG_VERSION"))
        .about(env!("CARGO_PKG_DESCRIPTION"))
        .arg(
            Arg::with_name("INPUT")
                .required(true)
                .help("proof_input file in DIMACS format"),
        )
        .arg(
            Arg::with_name("PROOF")
                .required(true)
                .help("proof file in DRAT format"),
        )
        .arg(
            Arg::with_name("PARTITIONS")
                .required(true)
                .help("number of partitions"),
        )
        .get_matches();

    let formula_file = matches.value_of("INPUT").unwrap();
    let proof_file = matches.value_of("PROOF").unwrap();
    let total_chunks: usize = matches
        .value_of("PARTITIONS")
        .unwrap()
        .parse()
        .unwrap_or_else(|err| die!("Number of partitions must be an integer: {}", err));
    if total_chunks == 0 {
        die!("Number of paritions must be at least one")
    }
    let number_of_proof_steps = count_proof_steps(proof_file);
    let steps_per_partition = number_of_proof_steps / total_chunks;
    let binary = is_binary_drat(read_file(proof_file).take(10));
    let mut slicer = Splitter {
        clause_line: Stack::new(),
        line: 2, // CNF header + 1-based
        parser: Parser::new(),
        clause_ids: HashTable::new(),
        proof_input: Input::new(read_file(&proof_file), binary),
        binary,
        proof_file,
        chunk: 0,
        total_chunks,
    };
    run_parser_on_formula(
        &mut slicer.parser,
        Some(formula_file),
        proof_file,
        &mut slicer.clause_ids,
    );
    if slicer.parser.clause_db.number_of_clauses() == 0 {
        die!("empty formula is not handled");
    }
    // TODO this assumes there are no comments!
    for _clause in 0..slicer.parser.clause_db.number_of_clauses() {
        requires!(_clause == slicer.clause_line.len().try_into().unwrap());
        slicer.clause_line.push(LineNumber::Active(slicer.line));
        slicer.line += 1;
    }
    for _ in 0..total_chunks - 1 {
        write_proof_slice(&mut slicer, Some(steps_per_partition));
    }
    write_proof_slice(&mut slicer, None)
}

fn write_proof_slice(slicer: &mut Splitter, steps: Option<usize>) {
    slicer.chunk += 1;
    assert!(slicer.total_chunks < usize::pow(10, 4));
    let name = format!("{}-{:04}.diff", slicer.proof_file, slicer.chunk,);
    println!("writing patch to {}", name);
    let mut dst = File::create(name.clone())
        .unwrap_or_else(|err| die!("Failed to open output file {}: {}", name, err));
    write_proof_slice_aux(&mut dst, slicer, steps)
        .unwrap_or_else(|err| die!("error parsing proof at line {}", err.line));
    let mut bias = 0;
    for i in 0..slicer.clause_line.len() {
        let clause = Clause::from_usize(i);
        match slicer.clause_line[i] {
            LineNumber::Active(line) => {
                let line_after_patch = if clause_is_active(&slicer.clause_ids, clause) {
                    LineNumber::Active(line - bias)
                } else {
                    bias += 1;
                    LineNumber::Deleted
                };
                slicer.clause_line[clause.as_offset()] = line_after_patch;
            }
            LineNumber::Deleted => (),
            LineNumber::Invalid => unreachable!(),
        }
    }
    slicer.line -= bias;
}

fn write_proof_slice_aux(
    dst: &mut File,
    slicer: &mut Splitter,
    steps: Option<usize>,
) -> Result<()> {
    let mut state = ProofParserState::Start;
    if let Some(exact_steps) = steps {
        for _ in 0..exact_steps {
            let _result = do_parse_proof_step(dst, slicer, &mut state)?;
            invariant!(_result == Some(()));
        }
    } else {
        while let Some(()) = do_parse_proof_step(dst, slicer, &mut state)? {}
        finish_proof(&mut slicer.parser, &mut slicer.clause_ids, &mut state);
    }
    Ok(())
}

fn do_parse_proof_step(
    dst: &mut File,
    slicer: &mut Splitter,
    state: &mut ProofParserState,
) -> Result<Option<()>> {
    parse_proof_step(
        &mut slicer.parser,
        &mut slicer.clause_ids,
        &mut slicer.proof_input,
        slicer.binary,
        state,
    )
    .map(|result| {
        let proof_step = *slicer.parser.proof.last();
        write_edit_script(dst, slicer, proof_step)
            .unwrap_or_else(|err| die!("Write failed: {}", err));
        result
    })
}

fn line_number(slicer: &Splitter, clause: Clause) -> Option<usize> {
    match slicer.clause_line[clause.as_offset()] {
        LineNumber::Active(line) => Some(line),
        LineNumber::Deleted => None,
        LineNumber::Invalid => unreachable!(),
    }
}

fn write_edit_script(
    dst: &mut File,
    slicer: &mut Splitter,
    proof_step: ProofStep,
) -> io::Result<()> {
    let clause = proof_step.clause();
    if proof_step.is_deletion() {
        write!(dst, "{}d", line_number(slicer, clause).unwrap())?;
    } else {
        let line = slicer.line;
        slicer.clause_line.push(LineNumber::Active(line));
        write!(dst, "$a")?;
        write_clause(dst, slicer.parser.clause_db.clause(clause).iter())?;
        slicer.line += 1;
    }
    writeln!(dst, "")?;
    Ok(())
}

fn count_proof_steps(proof_file: &str) -> usize {
    let mut parser = Parser::new();
    parser.verbose = false;
    let mut clause_ids = HashTable::new();
    run_parser(&mut parser, None, proof_file, &mut clause_ids);
    parser.proof.len()
}
