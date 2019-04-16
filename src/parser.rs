//! DIMACS and DRAT parser

use crate::{
    clause::{Clause, ProofStep},
    clausedatabase::{ClauseDatabase, WitnessDatabase},
    config::{unreachable, RedundancyProperty},
    literal::{Literal, Variable},
    memory::{HeapSpace, Offset, Slice, SmallStack, Stack},
    output::Timer,
};
#[cfg(feature = "flame_it")]
use flamer::flame;
use memmap::{Mmap, MmapOptions};
use std::collections::HashMap;
use std::{
    cmp,
    convert::TryInto,
    fmt,
    fmt::{Display, Formatter},
    fs::File,
    hash::{Hash, Hasher},
    io::{self, Read},
    iter::Peekable,
    panic,
};

// This needs to be static so that ClauseHashEq can access it.
pub static mut CLAUSE_DATABASE: ClauseDatabase = ClauseDatabase::new();
pub static mut WITNESS_DATABASE: WitnessDatabase = WitnessDatabase::new();

#[derive(Debug, PartialEq)]
pub struct Parser {
    pub redundancy_property: RedundancyProperty,
    pub maxvar: Variable,
    pub clause_db: &'static mut ClauseDatabase,
    pub witness_db: &'static mut WitnessDatabase,
    pub clause_pivot: Stack<Literal>,
    #[cfg(feature = "clause_lifetime_heuristic")]
    pub clause_deleted_at: Stack<usize>,
    pub proof_start: Clause,
    pub proof: Stack<ProofStep>,
    pub max_proof_steps: Option<usize>,
    pub verbose: bool,
}

impl Parser {
    pub fn new() -> Parser {
        unsafe {
            CLAUSE_DATABASE.clear();
            WITNESS_DATABASE.clear();
        }
        unsafe {
            assert!(
                CLAUSE_DATABASE.is_empty(),
                "Only one parser can be active at any time."
            );
            CLAUSE_DATABASE.initialize();
        }
        Parser {
            redundancy_property: RedundancyProperty::RAT,
            maxvar: Variable::new(0),
            clause_db: unsafe { &mut CLAUSE_DATABASE },
            witness_db: unsafe { &mut WITNESS_DATABASE },
            clause_pivot: Stack::new(),
            #[cfg(feature = "clause_lifetime_heuristic")]
            clause_deleted_at: Stack::new(),
            proof_start: Clause::new(0),
            proof: Stack::new(),
            max_proof_steps: None,
            verbose: true,
        }
    }
    pub fn is_pr(&self) -> bool {
        self.redundancy_property == RedundancyProperty::PR
    }
}

pub type HashTable = HashMap<ClauseHashEq, SmallStack<Clause>>;

pub fn parse_files(formula_file: &str, proof_file: &str) -> Parser {
    let mut parser = Parser::new();
    let mut clause_ids = HashTable::new();
    run_parser(&mut parser, Some(formula_file), proof_file, &mut clause_ids);
    parser
}

pub fn run_parser_on_formula(
    mut parser: &mut Parser,
    formula: Option<&str>,
    proof_file: &str,
    mut clause_ids: &mut HashTable,
) {
    parser.redundancy_property = proof_format_by_extension(&proof_file);
    if parser.verbose {
        comment!("mode: {}", parser.redundancy_property);
    }
    if parser.redundancy_property != RedundancyProperty::RAT {
        parser.witness_db.initialize();
    }
    if let Some(formula_file) = formula {
        let mut _timer = Timer::name("parsing formula");
        if !parser.verbose {
            _timer.disabled = true;
        }
        let formula_input = read_file(formula_file);
        parse_formula(
            &mut parser,
            &mut clause_ids,
            SimpleInput::new(Box::new(formula_input), false),
        )
        .unwrap_or_else(|err| die!("error parsing formula at line {}", err.line));
    }
}

pub fn run_parser(
    mut parser: &mut Parser,
    formula: Option<&str>,
    proof_file: &str,
    mut clause_ids: &mut HashTable,
) {
    run_parser_on_formula(parser, formula, proof_file, clause_ids);
    let mut _timer = Timer::name("parsing proof");
    if !parser.verbose {
        _timer.disabled = true;
    }
    let binary = is_binary_drat(read_file(proof_file).take(10));
    let proof_input = Box::new(read_file(&proof_file));
    if binary {
        if parser.verbose {
            comment!("binary proof mode");
        }
    }
    parse_proof(
        &mut parser,
        &mut clause_ids,
        SimpleInput::new(proof_input, binary),
        binary,
    )
    .unwrap_or_else(|err| die!("error parsing proof at line {}", err.line));
}

fn open_file(filename: &str) -> File {
    File::open(&filename).unwrap_or_else(|err| die!("error opening file: {}", err))
}

const ZSTD: &str = ".zst";
const GZIP: &str = ".gz";
const BZIP2: &str = ".bz2";
const LZ4: &str = ".lz4";
const XZ: &str = ".xz";

fn compression_format_by_extension(filename: &str) -> (&str, &str) {
    let mut basename = filename;
    let mut compression_format = "";
    for extension in &[ZSTD, GZIP, BZIP2, LZ4, XZ] {
        if filename.ends_with(extension) {
            compression_format = extension;
            basename = &filename[0..filename.len() - extension.len()];
            break;
        }
    }
    (basename, compression_format)
}

pub fn proof_format_by_extension(proof_filename: &str) -> RedundancyProperty {
    let (basename, _compression_format) = compression_format_by_extension(proof_filename);
    if basename.ends_with(".drat") {
        RedundancyProperty::RAT
    } else if basename.ends_with(".pr") || basename.ends_with(".dpr") {
        RedundancyProperty::PR
    } else {
        RedundancyProperty::RAT
    }
}

pub fn read_file(filename: &str) -> Box<dyn Iterator<Item = u8>> {
    let file = open_file(filename);
    let (_basename, compression_format) = compression_format_by_extension(filename);
    if compression_format == "" {
        return Box::new(
            mmap_file(file)
                .map_or(vec![], |mmap| mmap.to_owned())
                .into_iter(),
        );
    }
    match compression_format {
        ZSTD => {
            let de = zstd::stream::read::Decoder::new(file)
                .unwrap_or_else(|err| die!("failed to decompress ZST archive: {}", err));
            Box::new(de.bytes().map(panic_on_error))
        }
        GZIP => {
            let de = flate2::read::GzDecoder::new(file);
            Box::new(de.bytes().map(panic_on_error))
        }
        BZIP2 => {
            let de = bzip2::read::BzDecoder::new(file);
            Box::new(de.bytes().map(panic_on_error))
        }
        XZ => {
            let de = xz2::read::XzDecoder::new(file);
            Box::new(de.bytes().map(panic_on_error))
        }
        LZ4 => {
            let de = lz4::Decoder::new(file)
                .unwrap_or_else(|err| die!("Failed to decode LZ4 archive: {}", err));
            Box::new(de.bytes().map(panic_on_error))
        }
        _ => unreachable(),
    }
}

fn panic_on_error(result: io::Result<u8>) -> u8 {
    result.unwrap_or_else(|error| die!("read error: {}", error))
}

fn mmap_file(file: File) -> Option<Mmap> {
    let size = file.metadata().unwrap().len();
    if size == 0 {
        None
    } else {
        Some(unsafe { MmapOptions::new().map(&file) }.expect("mmap failed"))
    }
}

fn add_literal(
    parser: &mut Parser,
    clause_ids: &mut HashTable,
    state: ProofParserState,
    literal: Literal,
) {
    parser.maxvar = cmp::max(parser.maxvar, literal.variable());
    match state {
        ProofParserState::Clause => {
            parser.clause_db.push_literal(literal);
            if parser.is_pr() && literal.is_zero() {
                parser.witness_db.push_literal(literal);
            }
        }
        ProofParserState::Witness => {
            invariant!(parser.is_pr());
            parser.witness_db.push_literal(literal);
            if literal.is_zero() {
                parser.clause_db.push_literal(literal);
            }
        }
        ProofParserState::Deletion => {
            parser.clause_db.push_literal(literal);
            if literal.is_zero() {
                add_deletion(parser, clause_ids)
            }
        }
        ProofParserState::Start => unreachable(),
    }
    match state {
        ProofParserState::Clause | ProofParserState::Witness => {
            if literal.is_zero() {
                let clause = parser.clause_db.last_clause();
                let key = ClauseHashEq(clause);
                clause_ids
                    .entry(key)
                    .or_insert_with(SmallStack::new)
                    .push(clause);
            }
        }
        _ => (),
    }
}

fn add_deletion(parser: &mut Parser, clause_ids: &mut HashTable) {
    let clause = parser.clause_db.last_clause();
    match find_clause(clause_ids, clause) {
        None => {
            if parser.verbose {
                warn!(
                    "Deleted clause is not present in the formula: {}",
                    parser.clause_db.clause_to_string(clause)
                );
            }
            // Need this for sickcheck
            parser
                .proof
                .push(ProofStep::deletion(Clause::DOES_NOT_EXIST))
        }
        Some(clause) => {
            #[cfg(feature = "clause_lifetime_heuristic")]
            {
                invariant!(parser.clause_deleted_at[clause.as_offset()] == usize::max_value());
                parser.clause_deleted_at[clause.as_offset()] = parser.proof.len();
            }
            parser.proof.push(ProofStep::deletion(clause))
        }
    }
    parser.clause_db.pop_clause();
}

#[derive(Debug, Eq, Clone, Copy)]
pub struct ClauseHashEq(pub Clause);

impl Hash for ClauseHashEq {
    fn hash<H: Hasher>(&self, hasher: &mut H) {
        unsafe {
            compute_hash(CLAUSE_DATABASE.clause(self.0)).hash(hasher);
        }
    }
}

impl PartialEq for ClauseHashEq {
    fn eq(&self, other: &ClauseHashEq) -> bool {
        unsafe {
            let clause = CLAUSE_DATABASE.clause(self.0);
            let other_clause = CLAUSE_DATABASE.clause(other.0);
            clause == other_clause
        }
    }
}

fn find_clause(clause_ids: &mut HashTable, needle: Clause) -> Option<Clause> {
    clause_ids
        .get_mut(&ClauseHashEq(needle))
        // TODO why not just pop
        .and_then(|clause_stack| clause_stack.swap_remove(0))
}

#[allow(dead_code)]
pub fn clause_is_active(clause_ids: &HashTable, needle: Clause) -> bool {
    clause_ids
        .get(&ClauseHashEq(needle))
        .map_or(false, |stack| !stack.to_vec().is_empty())
}

#[allow(dead_code)]
pub fn clause_is_active_same_id(clause_ids: &HashTable, needle: Clause) -> bool {
    clause_ids
        .get(&ClauseHashEq(needle))
        .map_or(false, |stack| {
            stack.to_vec().iter().any(|&clause| clause == needle)
        })
}

fn compute_hash(clause: Slice<Literal>) -> usize {
    let mut sum: usize = 0;
    let mut prod: usize = 1;
    let mut xor: usize = 0;
    for &literal in clause {
        prod = prod.wrapping_mul(literal.as_offset());
        sum = sum.wrapping_add(literal.as_offset());
        xor ^= literal.as_offset();
    }
    ((1023 * sum + prod) ^ (31 * xor))
}

fn is_digit(value: u8) -> bool {
    value >= b'0' && value <= b'9'
}

fn is_digit_or_dash(value: u8) -> bool {
    is_digit(value) || value == b'-'
}

pub type Result<T> = std::result::Result<T, ParseError>;

#[derive(Debug, PartialEq, Eq)]
pub struct ParseError {
    pub line: usize,
    pub why: &'static str,
}

const OVERFLOW: &str = "overflow while parsing number";
const NUMBER: &str = "expected number";
const EOF: &str = "premature end of file";
const P_CNF: &str = "expected \"p cnf\"";
const DRAT: &str = "expected DRAT instruction";

fn parse_literal(input: &mut impl Input) -> Result<Literal> {
    match input.peek() {
        None => Err(input.error(EOF)),
        Some(c) if is_digit_or_dash(c) => {
            let sign = if c == b'-' {
                input.next();
                -1
            } else {
                1
            };
            Ok(Literal::new(sign * parse_i32(input)?))
        }
        _ => Err(input.error(NUMBER)),
    }
}

fn parse_u64(input: &mut impl Input) -> Result<u64> {
    while input.peek() == Some(b' ') {
        input.next();
    }
    let mut value: u64 = 0;
    while let Some(c) = input.next() {
        if is_space(c) {
            break;
        }
        if !is_digit(c) {
            return Err(input.error(NUMBER));
        }
        value = value
            .checked_mul(10)
            .expect(OVERFLOW)
            .checked_add(u64::from(c - b'0'))
            .expect(OVERFLOW);
    }
    Ok(value)
}

fn parse_i32(input: &mut impl Input) -> Result<i32> {
    let value = parse_u64(input)?;
    if value > i32::max_value().try_into().unwrap() {
        Err(input.error(OVERFLOW))
    } else {
        Ok(value as i32)
    }
}

fn parse_literal_binary(input: &mut impl Input) -> Result<Literal> {
    let mut i = 0;
    let mut result = 0;
    while let Some(value) = input.next() {
        result |= u32::from(value & 0x7f) << (7 * i);
        i += 1;
        if (value & 0x80) == 0 {
            break;
        }
    }
    Ok(Literal::from_raw(result))
}

fn parse_comment(input: &mut impl Input) -> Option<()> {
    match input.peek() {
        Some(b'c') => {
            input.next();
            while let Some(c) = input.next() {
                if c == b'\n' {
                    return Some(());
                }
            }
            None
        }
        None => Some(()),
        _ => None,
    }
}

fn parse_formula_header(input: &mut impl Input) -> Result<(u64, u64)> {
    while let Some(()) = parse_comment(input) {}
    for &expected in b"p cnf" {
        if input.peek().map_or(true, |c| c != expected) {
            return Err(input.error(P_CNF));
        }
        input.next();
    }
    let maxvar = parse_u64(input)?;
    let num_clauses = parse_u64(input)?;
    Ok((maxvar, num_clauses))
}

fn is_space(c: u8) -> bool {
    [b' ', b'\n', b'\r'].iter().any(|&s| s == c)
}

fn open_clause(parser: &mut Parser, state: ProofParserState) -> Clause {
    let clause = parser.clause_db.open_clause();
    if parser.is_pr() && state != ProofParserState::Deletion {
        let witness = parser.witness_db.open_witness();
        invariant!(clause == witness);
    }
    clause
}

fn parse_formula(
    parser: &mut Parser,
    clause_ids: &mut HashTable,
    mut input: impl Input,
) -> Result<()> {
    parse_formula_header(&mut input)?;
    let mut clause_head = true;
    while let Some(c) = input.peek() {
        if is_space(c) {
            input.next();
            continue;
        }
        if c == b'c' {
            parse_comment(&mut input);
            continue;
        }
        let literal = parse_literal(&mut input)?;
        if clause_head {
            open_clause(parser, ProofParserState::Clause);
            parser.clause_pivot.push(Literal::NEVER_READ);
            #[cfg(feature = "clause_lifetime_heuristic")]
            parser.clause_deleted_at.push(usize::max_value());
        }
        add_literal(parser, clause_ids, ProofParserState::Clause, literal);
        clause_head = literal.is_zero();
    }
    Ok(())
}

// See drat-trim
pub fn is_binary_drat(buffer: impl Iterator<Item = u8>) -> bool {
    for c in buffer {
        if (c != 100) && (c != 10) && (c != 13) && (c != 32) && (c != 45) && ((c < 48) || (c > 57))
        {
            return true;
        }
    }
    false
    /*
    requires!(buffer.len() <= 12);
    match buffer.len() {
        0 => return true,
        1 => return true,
        12 => (),
        _ => return false,
    };
    let c0 = buffer[0];
    let c1 = buffer[1];
    let comment = c0 == 99 && c1 == 32;
    [c0, c1]
        .into_iter()
        .any(|&c| (c != 13 && c != 32 && c != 45 && (c < 48 || c > 57) && c != 99 && c != 100))
        || (2..12).any(|i| {
            let c = buffer[i];
            c != 100
                && c != 10
                && c != 13
                && c != 32
                && c != 45
                && (c < 48 || c > 57)
                && comment
                && (c < 65 && c > 122)
        })
        */
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum ProofParserState {
    Start,
    Clause,
    Witness,
    Deletion,
}

pub fn parse_proof_step(
    parser: &mut Parser,
    clause_ids: &mut HashTable,
    input: &mut impl Input,
    binary: bool,
    state: &mut ProofParserState,
) -> Result<Option<()>> {
    let literal_parser = if binary {
        parse_literal_binary
    } else {
        parse_literal
    };
    let mut lemma_head = true;
    let mut first_literal = None;
    while let Some(c) = input.peek() {
        if !binary && is_space(c) {
            input.next();
            continue;
        }
        if *state == ProofParserState::Start {
            *state = match c {
                b'd' => {
                    input.next();
                    open_clause(parser, ProofParserState::Deletion);
                    ProofParserState::Deletion
                }
                b'c' => {
                    parse_comment(input);
                    ProofParserState::Start
                }
                c if (!binary && is_digit_or_dash(c)) || (binary && c == b'a') => {
                    if binary {
                        input.next();
                    }
                    lemma_head = true;
                    let clause = open_clause(parser, ProofParserState::Clause);
                    parser.proof.push(ProofStep::lemma(clause));
                    ProofParserState::Clause
                }
                _ => return Err(input.error(DRAT)),
            };
            continue;
        }
        let literal = literal_parser(input)?;
        if parser.is_pr() && *state == ProofParserState::Clause && first_literal == Some(literal) {
            *state = ProofParserState::Witness;
        }
        if *state == ProofParserState::Clause && lemma_head {
            parser.clause_pivot.push(literal);
            #[cfg(feature = "clause_lifetime_heuristic")]
            parser.clause_deleted_at.push(usize::max_value());
            first_literal = Some(literal);
            lemma_head = false;
        }
        invariant!(*state != ProofParserState::Start);
        add_literal(parser, clause_ids, *state, literal);
        if literal.is_zero() {
            *state = ProofParserState::Start;
            return Ok(Some(()));
        }
    }
    Ok(None)
}

pub fn finish_proof(parser: &mut Parser, clause_ids: &mut HashTable, state: &mut ProofParserState) {
    // patch missing zero terminators
    match *state {
        ProofParserState::Clause | ProofParserState::Deletion | ProofParserState::Witness => {
            add_literal(parser, clause_ids, *state, Literal::new(0));
        }
        ProofParserState::Start => (),
    };
    // ensure that every proof ends with an empty clause
    let clause = open_clause(parser, ProofParserState::Clause);
    parser.proof.push(ProofStep::lemma(clause));
    add_literal(
        parser,
        clause_ids,
        ProofParserState::Clause,
        Literal::new(0),
    );
}
fn parse_proof(
    parser: &mut Parser,
    clause_ids: &mut HashTable,
    mut input: impl Input,
    binary: bool,
) -> Result<()> {
    parser.proof_start = Clause::new(parser.clause_db.number_of_clauses());
    let mut state = ProofParserState::Start;
    if parser.max_proof_steps != Some(0) {
        while let Some(()) = parse_proof_step(parser, clause_ids, &mut input, binary, &mut state)? {
            if parser
                .max_proof_steps
                .map_or(false, |max_steps| parser.proof.len() == max_steps)
            {
                break;
            }
        }
    }
    finish_proof(parser, clause_ids, &mut state);
    Ok(())
}

impl Display for ParseError {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "Parse error at line {}:  {}", self.line, self.why)
    }
}

#[allow(dead_code)]
fn print_db() {
    let clause_db = unsafe { &CLAUSE_DATABASE };
    let witness_db = unsafe { &WITNESS_DATABASE };
    let is_pr = !witness_db.empty();
    for clause in Clause::range(0, clause_db.last_clause() + 1) {
        println!(
            "{}{} {:?}",
            clause_db.clause_to_string(clause),
            if is_pr {
                format!(", {}", witness_db.witness_to_string(clause))
            } else {
                "".into()
            },
            clause_db.fields(clause)
        );
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[allow(unused_macros)]
    macro_rules! literals {
        ($($x:expr),*) => (Stack::from_vec(vec!($(Literal::new($x)),*)));
    }

    fn sample_formula(clause_ids: &mut HashTable) -> Parser {
        let mut parser = Parser::new();
        parser.redundancy_property = RedundancyProperty::RAT;
        let example = r#"c comment
p cnf 2 2
1 2 0
c comment
-1 -2 0"#;
        assert!(parse_formula(
            &mut parser,
            clause_ids,
            SimpleInput::new(Box::new(example.as_bytes().iter().cloned()), false),
        )
        .is_ok());
        parser
    }
    #[test]
    fn valid_formula_and_proof() {
        run_test(|| {
            let mut clause_ids = HashTable::new();
            let mut parser = sample_formula(&mut clause_ids);
            let result = parse_proof(
                &mut parser,
                &mut clause_ids,
                SimpleInput::new(Box::new(b"1 2 3 0\nd 1 2 0".into_iter().cloned()), false),
                false,
            );
            assert!(result.is_ok());
            let expected_clause_ids = [
                (
                    ClauseHashEq(Clause::new(1)),
                    SmallStack::singleton(Clause::new(1)),
                ),
                (
                    ClauseHashEq(Clause::new(2)),
                    SmallStack::singleton(Clause::new(2)),
                ),
                (ClauseHashEq(Clause::new(0)), SmallStack::new()),
                (
                    ClauseHashEq(Clause::new(3)),
                    SmallStack::singleton(Clause::new(3)),
                ),
            ]
            .iter()
            .cloned()
            .collect();
            fn lit(x: i32) -> Literal {
                Literal::new(x)
            }
            fn raw(x: u32) -> Literal {
                Literal::from_raw(x)
            }
            print_db();
            assert_eq!(
                unsafe { &CLAUSE_DATABASE },
                &ClauseDatabase::from(
                    #[rustfmt::skip]
                     stack!(
                       raw(0), raw(0), raw(0), lit(1), lit(2), lit(0),
                       raw(1), raw(0), raw(0), lit(-2), lit(-1), lit(0),
                       raw(2), raw(0), raw(0), lit(1), lit(2), lit(3), lit(0),
                       raw(3), raw(0), raw(0), lit(0),
                     ),
                    stack!(0, 6, 12, 19)
                )
            );
            assert_eq!(
                unsafe { &WITNESS_DATABASE },
                &WitnessDatabase::from(stack!(), stack!())
            );
            assert_eq!(clause_ids, expected_clause_ids);
            assert_eq!(
                parser,
                Parser {
                    redundancy_property: RedundancyProperty::RAT,
                    maxvar: Variable::new(3),
                    clause_db: unsafe { &mut CLAUSE_DATABASE },
                    witness_db: unsafe { &mut WITNESS_DATABASE },
                    clause_pivot: stack!(Literal::NEVER_READ, Literal::NEVER_READ, Literal::new(1)),
                    #[cfg(feature = "clause_lifetime_heuristic")]
                    clause_deleted_at: stack!(1, usize::max_value(), usize::max_value(),),
                    proof_start: Clause::new(2),
                    proof: stack!(
                        ProofStep::lemma(Clause::new(2)),
                        ProofStep::deletion(Clause::new(0)),
                        ProofStep::lemma(Clause::new(3)),
                    ),
                    max_proof_steps: None,
                    verbose: true,
                }
            );
        })
    }

    fn run_test<F>(case: F)
    where
        F: FnOnce() -> () + panic::UnwindSafe,
    {
        let result = panic::catch_unwind(case);
        reset_globals();
        assert!(result.is_ok())
    }
    // TODO obolete
    fn reset_globals() {
        unsafe {
            CLAUSE_DATABASE.clear();
            WITNESS_DATABASE.clear();
        }
    }
}

impl HeapSpace for Parser {
    fn heap_space(&self) -> usize {
        self.clause_db.heap_space() + self.clause_pivot.heap_space() + self.proof.heap_space()
    }
}

pub type InputSource = Peekable<Box<dyn Iterator<Item = u8>>>;

pub trait Input {
    fn next(&mut self) -> Option<u8>;
    fn peek(&mut self) -> Option<u8>;
    fn error(&self, why: &'static str) -> ParseError;
}

pub struct SimpleInput {
    source: InputSource,
    binary: bool,
    line: usize,
}

impl SimpleInput {
    pub fn new(source: Box<dyn Iterator<Item = u8>>, binary: bool) -> Self {
        SimpleInput {
            source: source.peekable(),
            binary,
            line: 0,
        }
    }
}

impl Input for SimpleInput {
    fn next(&mut self) -> Option<u8> {
        self.source.next().map(|c| {
            if self.binary && c == b'\n' {
                self.line += 1;
            }
            c
        })
    }
    fn peek(&mut self) -> Option<u8> {
        self.source.peek().cloned()
    }
    fn error(&self, why: &'static str) -> ParseError {
        ParseError {
            why,
            line: self.line,
        }
    }
}
