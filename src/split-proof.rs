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
    convert::{TryFrom, TryInto},
    fs::File,
    io::{self, Write},
};

use crate::{
    clause::{write_clause, Clause},
    memory::{Offset, Stack},
    parser::{
        clause_is_active_same_id, finish_proof, is_binary_drat, read_file, run_parser,
        run_parser_on_formula, HashTable, Input, ParseError, Parser, ProofParserState, Result,
        SimpleInput,
    },
};
use clap::Arg;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum LineNumber {
    Invalid,
    Active(u64),
    Deleted,
}

impl Default for LineNumber {
    fn default() -> Self {
        LineNumber::Invalid
    }
}

struct Splitter<'a> {
    clause_line: Stack<LineNumber>, // TODO: use im::Vector?
    lines: u64,       // the next line number to append
    proof_end: usize, // steps from the proof that we have already processed
    parser: Parser,
    clause_ids: HashTable,
    proof_input: TappedInput,
    binary: bool,
    proof_file: &'a str,
    chunk: u64,
    total_chunks: u32,
    log_total_chunks: u32,
}

// lines include the CNF header + 1-based
fn lines2clauses(lines: u64) -> u64 {
    lines - 2
}
fn clauses2lines(clauses: u64) -> u64 {
    clauses + 2
}

fn main() {
    let matches = clap::App::new("split-proof")
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
            Arg::with_name("CHUNKS")
                .required(true)
                .help("number of chunks"),
        )
        .get_matches();

    let formula_file = matches.value_of("INPUT").unwrap();
    let proof_file = matches.value_of("PROOF").unwrap();
    let total_chunks: u32 = matches
        .value_of("CHUNKS")
        .unwrap()
        .parse()
        .unwrap_or_else(|err| die!("Number of chunks must be an integer: {}", err));
    if total_chunks == 0 {
        die!("Number of paritions must be at least one")
    }
    let number_of_proof_steps = count_proof_steps(proof_file);
    let steps_per_chunk = number_of_proof_steps / u64::from(total_chunks);
    let binary = is_binary_drat(read_file(proof_file).take(10));
    let mut splitter = Splitter {
        clause_line: Stack::new(),
        lines: clauses2lines(0),
        proof_end: 0,
        parser: Parser::new(),
        clause_ids: HashTable::new(),
        proof_input: TappedInput {
            source: SimpleInput::new(read_file(&proof_file), binary),
            tap: None,
        },
        binary,
        proof_file,
        chunk: 0,
        total_chunks,
        log_total_chunks: f64::log10(total_chunks.into()).ceil() as u32,
    };
    splitter.parser.verbose = false;
    run_parser_on_formula(
        &mut splitter.parser,
        Some(formula_file),
        proof_file,
        &mut splitter.clause_ids,
    );
    for _clause in 0..splitter.parser.clause_db.number_of_clauses() {
        requires!(_clause == splitter.clause_line.len().try_into().unwrap());
        splitter
            .clause_line
            .push(LineNumber::Active(splitter.lines));
        splitter.lines += 1;
    }
    for _ in 0..total_chunks - 1 {
        write_chunk(&mut splitter, Some(steps_per_chunk));
    }
    write_chunk(&mut splitter, None)
}

fn write_chunk(splitter: &mut Splitter, steps: Option<u64>) {
    let name = format!(
        "{proof_file}.{chunk:0width$}.sed",
        proof_file = splitter.proof_file,
        chunk = splitter.chunk,
        width = usize::try_from(splitter.log_total_chunks).unwrap(),
    );
    let chunk_drat = format!(
        "{proof_file}.{chunk:0width$}.drat",
        proof_file = splitter.proof_file,
        chunk = splitter.chunk,
        width = usize::try_from(splitter.log_total_chunks).unwrap(),
    );
    splitter.proof_input.tap = Some(
        File::create(chunk_drat)
            .unwrap_or_else(|err| die!("Failed to open output file {}: {}", name, err)),
    );
    let mut chunk_sed = File::create(name.clone())
        .unwrap_or_else(|err| die!("Failed to open output file {}: {}", name, err));

    parse_chunk(splitter, steps)
        .unwrap_or_else(|err| die!("error parsing proof at line {}", err.line));

    fn line_number(splitter: &Splitter, clause: Clause) -> Option<u64> {
        if clause == Clause::DOES_NOT_EXIST {
            return None;
        }
        match splitter.clause_line[clause.as_offset()] {
            LineNumber::Active(line) => Some(line),
            LineNumber::Deleted => None,
            LineNumber::Invalid => unreachable!(),
        }
    }

    let previous_lines = splitter.lines;
    for step in splitter
        .parser
        .proof
        .as_slice()
        .range(splitter.proof_end, splitter.parser.proof.len())
    {
        if !step.is_deletion() {
            splitter
                .clause_line
                .push(LineNumber::Active(splitter.lines));
            splitter.lines += 1;
        }
    }
    // write added clauses
    for step in splitter
        .parser
        .proof
        .as_slice()
        .range(splitter.proof_end, splitter.parser.proof.len())
    {
        let clause = step.clause();
        if !step.is_deletion() {
            if clause_is_active_same_id(&splitter.clause_ids, clause) {
                write!(chunk_sed, "$a")
                    .and(write_clause(
                        &mut chunk_sed,
                        splitter.parser.clause_db.clause(clause).iter(),
                    ))
                    .and(writeln!(chunk_sed))
                    .unwrap_or_else(write_error)
            }
        }
    }
    // write deletions for clauses that predate our chunk
    for step in splitter
        .parser
        .proof
        .as_slice()
        .range(splitter.proof_end, splitter.parser.proof.len())
    {
            let clause = step.clause();
            if step.is_deletion() {
                if let Some(line) = line_number(splitter, clause) {
                    if line < previous_lines {
                        writeln!(chunk_sed, "{}d", line).unwrap_or_else(write_error);
                    }
                }
            }
    }
    // set inactive all clauses deleted in the current chunk
    // and adjust the line numbers of all subsequent clauses
    splitter.proof_end = splitter.parser.proof.len();
    let mut newly_deleted = 0;
    for i in 0..splitter.clause_line.len() {
        let clause = Clause::from_usize(i);
        match splitter.clause_line[i] {
            LineNumber::Active(line) => {
                let line_after_patch = if clause_is_active_same_id(&splitter.clause_ids, clause) {
                    LineNumber::Active(line - newly_deleted)
                } else {
                    newly_deleted += 1;
                    LineNumber::Deleted
                };
                splitter.clause_line[clause.as_offset()] = line_after_patch;
            }
            LineNumber::Deleted => (),
            LineNumber::Invalid => unreachable!(),
        }
    }
    splitter.lines -= newly_deleted;
    write!(
        chunk_sed,
        "1cp cnf {} {}",
        splitter.parser.maxvar,
        lines2clauses(splitter.lines)
    )
    .unwrap_or_else(write_error);
    splitter.chunk += 1;
}

fn parse_chunk(splitter: &mut Splitter, steps: Option<u64>) -> Result<()> {
    let mut state = ProofParserState::Start;
    if let Some(exact_steps) = steps {
        for _ in 0..exact_steps {
            let _result = parse_proof_step(splitter, &mut state)?;
            invariant!(_result == Some(()));
        }
    } else {
        while let Some(()) = parse_proof_step(splitter, &mut state)? {}
        finish_proof(&mut splitter.parser, &mut splitter.clause_ids, &mut state);
    }
    Ok(())
}

fn parse_proof_step(splitter: &mut Splitter, state: &mut ProofParserState) -> Result<Option<()>> {
    parser::parse_proof_step(
        &mut splitter.parser,
        &mut splitter.clause_ids,
        &mut splitter.proof_input,
        splitter.binary,
        state,
    )
}

fn count_proof_steps(proof_file: &str) -> u64 {
    let mut parser = Parser::new();
    parser.verbose = false;
    let mut clause_ids = HashTable::new();
    run_parser(&mut parser, None, proof_file, &mut clause_ids);
    parser.proof.len().try_into().unwrap()
}

fn write_error(error: io::Error) {
    die!("Write failed: {}", error)
}

pub struct TappedInput {
    source: SimpleInput,
    tap: Option<File>,
}

impl Input for TappedInput {
    fn next(&mut self) -> Option<u8> {
        self.source.next().map(|c| {
            self.tap.as_ref().unwrap().write(&[c]).unwrap();
            c
        })
    }
    fn peek(&mut self) -> Option<u8> {
        self.source.peek()
    }
    fn error(&self, why: &'static str) -> ParseError {
        self.source.error(why)
    }
}
