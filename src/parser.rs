//! DIMACS and DRAT parser

use crate::{
    clause::{Clause, ProofStep},
    clausedatabase::ClauseDatabase,
    config::unreachable,
    literal::{Literal, Variable},
    memory::{ConsumingStackIterator, HeapSpace, Offset, Slice, Stack},
};
#[cfg(feature = "flame_it")]
use flamer::flame;
use std::collections::HashMap;
use std::{
    cmp, fmt,
    fmt::{Display, Formatter},
    fs::File,
    hash::{Hash, Hasher},
    io::{self, BufReader, Bytes, Read},
    iter::{Chain, Map, Peekable},
    panic, str,
};

/// format: clause are stored sequentially, using:
/// - clause id (usize), stored as 2x32bit LE
/// - sequence of Literal
/// - zero terminator Literal::new(0)

pub const PADDING_START: usize = 2;
pub const PADDING_END: usize = 1;

pub static mut CLAUSE_DATABASE: Stack<Literal> = Stack::const_new();
pub static mut CLAUSE_OFFSET: Stack<usize> = Stack::const_new();

#[derive(Debug, PartialEq)]
pub struct Parser {
    pub maxvar: Variable,
    pub num_clauses: usize,
    pub db: ClauseDatabase<'static>,
    pub current_clause_offset: usize,
    pub clause_pivot: Stack<Literal>,
    pub clause_deleted_at: Stack<usize>,
    pub proof_start: Clause,
    pub proof: Stack<ProofStep>,
}

impl Parser {
    pub fn new() -> Parser {
        unsafe { CLAUSE_OFFSET.push(0) }; // sentinel
        Parser {
            maxvar: Variable::new(0),
            num_clauses: usize::max_value(),
            db: unsafe { ClauseDatabase::new(&mut CLAUSE_DATABASE, &mut CLAUSE_OFFSET) },
            current_clause_offset: 0,
            clause_pivot: Stack::new(),
            clause_deleted_at: Stack::new(),
            proof_start: Clause::new(0),
            proof: Stack::new(),
        }
    }
}

type HashTable = HashMap<ClauseHashEq, Stack<Clause>>;

#[cfg_attr(feature = "flame_it", flame)]
pub fn parse_files(formula_file: &str, proof_file: &str) -> Parser {
    let mut clause_ids = HashTable::new();
    let mut parser = Parser::new();
    {
        parse_formula(&mut parser, &mut clause_ids, open_file(&formula_file))
            .unwrap_or_else(|err| die!("error parsing formula at line {}", err.line));
    }
    {
        parse_proof(&mut parser, &mut clause_ids, open_file(&proof_file))
            .unwrap_or_else(|err| die!("error parsing proof at line {}", err.line));
    }
    parser
}

fn open_file(filename: &str) -> BufReaderInput {
    BufReaderInput::new(BufReader::new(
        File::open(&filename).unwrap_or_else(|err| die!("error opening file: {}", err)),
    ))
}

fn start_clause(parser: &mut Parser) -> Clause {
    parser.db.offset.pop(); // pop sentinel
    let clause = parser.db.offset.len() as u64;
    parser.db.offset.push(parser.db.data.len());
    let lower = (clause & 0x00000000ffffffff) as u32;
    let upper = ((clause & 0xffffffff00000000) >> 32) as u32;
    parser.db.data.push(Literal::from_raw(lower));
    parser.db.data.push(Literal::from_raw(upper));
    parser.clause_deleted_at.push(usize::max_value());
    Clause::new(clause)
}

fn close_clause(parser: &mut Parser) -> Clause {
    let clause = Clause::new(parser.db.offset.len() as u64) - 1;
    let start = parser.current_clause_offset + PADDING_START;
    let end = parser.db.data.len();
    let _sort_literally = |&literal: &Literal| literal.decode();
    let _sort_magnitude = |&literal: &Literal| literal.encoding;
    parser
        .db
        .data
        .mut_slice()
        .range(start, end)
        .sort_unstable_by_key(_sort_literally);
    let mut duplicate = false;
    let mut length = 0;
    for i in start..end {
        if i + 1 < end && parser.db[i] == parser.db[i + 1] {
            duplicate = true;
        } else {
            parser.db[start + length] = parser.db[i];
            length += 1;
        }
    }
    parser.db.data.truncate(start + length);
    if length == 1 {
        parser.db.data.push(Literal::BOTTOM);
    }
    parser.db.data.push(Literal::new(0));
    parser.current_clause_offset = parser.db.data.len();
    parser.db.offset.push(parser.current_clause_offset); // sentinel
    if duplicate {
        warn!(
            "Removed duplicate literals in {}",
            parser.db.clause_to_string(clause)
        );
    }
    clause
}

fn pop_clause(parser: &mut Parser, prev_clause_offset: usize) {
    parser.db.data.truncate(prev_clause_offset);
    parser.current_clause_offset = prev_clause_offset;

    parser.db.offset.pop(); // sentinel
    parser.db.offset.pop();
    parser.db.offset.push(prev_clause_offset);

    parser.clause_deleted_at.pop();
}

fn add_literal<'r>(parser: &'r mut Parser, clause_ids: &mut HashTable, literal: Literal) {
    if literal.is_zero() {
        let clause = close_clause(parser);
        let key = ClauseHashEq(clause);
        clause_ids.entry(key).or_insert(Stack::new()).push(clause);
    } else {
        parser.maxvar = cmp::max(parser.maxvar, literal.variable());
        parser.db.data.push(literal);
    }
}

fn add_deletion(parser: &mut Parser, clause_ids: &mut HashTable, literal: Literal) -> Literal {
    if literal.is_zero() {
        let prev = parser.current_clause_offset;
        let clause = close_clause(parser);
        match find_clause(clause_ids, clause) {
            None => {
                warn!(
                    "Deleted clause is not present in the formula: {}",
                    parser.db.clause_to_string(clause)
                );
                // need this for sickcheck
                parser
                    .proof
                    .push(ProofStep::deletion(Clause::DOES_NOT_EXIST))
            }
            Some(clause) => {
                parser.clause_deleted_at[clause.as_offset()] = parser.proof.len();
                parser.proof.push(ProofStep::deletion(clause))
            }
        }
        pop_clause(parser, prev);
    } else {
        parser.db.data.push(literal);
    }
    literal
}

#[derive(Debug, Eq, Clone, Copy)]
struct ClauseHashEq(Clause);

impl Hash for ClauseHashEq {
    fn hash<H: Hasher>(&self, hasher: &mut H) {
        unsafe {
            let start = CLAUSE_OFFSET[self.0.as_offset()] + PADDING_START;
            let end = CLAUSE_OFFSET[self.0.as_offset() + 1] - PADDING_END;
            compute_hash(CLAUSE_DATABASE.as_slice().range(start, end)).hash(hasher)
        }
    }
}

impl PartialEq for ClauseHashEq {
    fn eq(&self, other: &ClauseHashEq) -> bool {
        unsafe {
            invariant!(self.0.as_offset() + 1 < CLAUSE_OFFSET.len());
            let start = CLAUSE_OFFSET[self.0.as_offset()] + PADDING_START;
            let end = CLAUSE_OFFSET[self.0.as_offset() + 1] - PADDING_END;
            let other_start = CLAUSE_OFFSET[other.0.as_offset()] + PADDING_START;
            for i in 0..end - start {
                if other_start + i == CLAUSE_DATABASE.len() {
                    return false;
                }
                if CLAUSE_DATABASE[start + i] != CLAUSE_DATABASE[other_start + i] {
                    return false;
                }
            }
        }
        true
    }
}

fn find_clause(clause_ids: &mut HashTable, needle: Clause) -> Option<Clause> {
    clause_ids.get_mut(&ClauseHashEq(needle)).map(|clauses| {
        let clause = *clauses.first();
        clauses.swap_remove(0);
        clause
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
    (1023 * sum + prod ^ (31 * xor))
}

fn is_digit(value: u8) -> bool {
    value >= b'0' && value <= b'9'
}

fn is_digit_or_dash(value: u8) -> bool {
    is_digit(value) || value == b'-'
}

type Result<T> = std::result::Result<T, ParseError>;

#[derive(Debug, PartialEq, Eq)]
struct ParseError {
    line: usize,
    why: &'static str,
}

impl Default for ParseError {
    fn default() -> ParseError {
        assert!(false);
        ParseError {
            line: 0,
            why: "TODO",
        }
    }
}

const OVERFLOW: &'static str = "overflow while parsing number";
const NUMBER: &'static str = "expected number";
const EOF: &'static str = "premature end of file";
const P_CNF: &'static str = "expected \"p cnf\"";
const DRAT: &'static str = "expected DRAT instruction";

fn parse_literal(input: &mut impl Input) -> Result<Literal> {
    match input.peek() {
        None => input.error(EOF),
        Some(c) if is_digit_or_dash(c) => {
            let sign = if c == b'-' {
                input.advance();
                -1
            } else {
                1
            };
            Ok(Literal::new(sign * parse_i32(input)?))
        }
        _ => input.error(NUMBER),
    }
}

fn parse_u64(input: &mut impl Input) -> Result<u64> {
    while input.peek() == Some(b' ') {
        input.advance();
    }
    let mut value: u64 = 0;
    while let Some(c) = input.advance() {
        if c == b' ' || c == b'\n' {
            break;
        }
        if !is_digit(c) {
            return input.error(NUMBER);
        }
        value = value
            .checked_mul(10)
            .expect(OVERFLOW)
            .checked_add((c - b'0') as u64)
            .expect(OVERFLOW);
    }
    Ok(value)
}

fn parse_i32(input: &mut impl Input) -> Result<i32> {
    let value = parse_u64(input)?;
    if value > i32::max_value() as u64 {
        input.error(OVERFLOW)
    } else {
        Ok(value as i32)
    }
}

fn parse_literal_binary(input: &mut impl Input) -> Result<Literal> {
    let mut i = 0;
    let mut result = 0;
    while let Some(value) = input.advance() {
        result |= ((value & 0x7f) as u32) << (7 * i);
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
            input.advance();
            while let Some(c) = input.advance() {
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
            return input.error(P_CNF);
        }
        input.advance();
    }
    let maxvar = parse_u64(input)?;
    let num_clauses = parse_u64(input)?;
    Ok((maxvar, num_clauses))
}

fn is_space(c: u8) -> bool {
    [b' ', b'\n', b'\r'].iter().any(|&s| s == c)
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
            input.advance();
            continue;
        }
        if c == b'c' {
            parse_comment(&mut input);
            continue;
        }
        let literal = parse_literal(&mut input)?;
        if clause_head {
            start_clause(&mut *parser);
            parser.clause_pivot.push(Literal::NEVER_READ);
        }
        add_literal(parser, clause_ids, literal);
        clause_head = literal.is_zero();
    }
    Ok(())
}

// See drat-trim
fn is_binary_drat(buffer: Slice<u8>) -> bool {
    for &c in buffer {
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

fn is_binary_drat_stream(mut input: impl Input) -> (impl Input, bool) {
    let mut buffer = Stack::new();
    for _ in 0..10 {
        match input.advance() {
            Some(c) => buffer.push(c),
            None => break,
        }
    }
    let is_binary = is_binary_drat(buffer.as_slice());
    let saved_line = input.line();
    let equivalent_input = ChainInput {
        source: buffer.into_iter().chain(input.into_iter()).peekable(),
        line: saved_line,
    };
    (equivalent_input, is_binary)
}

fn parse_proof<'a>(
    parser: &'a mut Parser,
    clause_ids: &mut HashTable,
    input: impl Input,
) -> Result<()> {
    parser.proof_start = Clause::new(parser.db.offset.len() as u64 - 1);

    let (mut input, is_binary) = is_binary_drat_stream(input);

    if is_binary {
        comment!("Turning on binary mode.");
    }
    let result = do_parse_proof(parser, clause_ids, &mut input, is_binary);
    // Add empty clauses to the end of the proof.
    parser.num_clauses = parser.db.offset.len();
    let empty_clause = Clause::new(parser.db.offset.len() as u64) - 1;
    parser.db.data.push(Literal::NEVER_READ);
    parser.db.data.push(Literal::NEVER_READ);
    parser.db.data.push(Literal::new(0));
    parser.db.offset.push(parser.db.data.len());
    parser.proof.push(ProofStep::lemma(empty_clause));
    result
}

fn do_parse_proof(
    parser: &mut Parser,
    clause_ids: &mut HashTable,
    input: &mut impl Input,
    binary: bool,
) -> Result<()> {
    #[derive(Debug, PartialEq, Eq)]
    enum State {
        Start,
        Lemma,
        Deletion,
    }

    let literal_parser = if binary {
        parse_literal_binary
    } else {
        parse_literal
    };
;
    let mut state = State::Start;
    let mut lemma_head = true;
    while let Some(c) = input.peek() {
        if !binary && is_space(c) {
            input.advance();
            continue;
        }
        state = match state {
            State::Start => match c {
                b'd' => {
                    input.advance();
                    start_clause(parser);
                    State::Deletion
                }
                b'c' => {
                    parse_comment(input);
                    State::Start
                }
                c if (!binary && is_digit_or_dash(c)) || (binary && c == b'a') => {
                    if binary {
                        input.advance();
                    }
                    lemma_head = true;
                    let clause = start_clause(parser);
                    parser.proof.push(ProofStep::lemma(clause));
                    State::Lemma
                }
                _ => return input.error(DRAT),
            },
            State::Lemma | State::Deletion => {
                let literal = literal_parser(input)?;
                match state {
                    State::Lemma => {
                        if lemma_head {
                            parser.clause_pivot.push(literal);
                        }
                        lemma_head = false;
                        add_literal(parser, clause_ids, literal);
                    }
                    State::Deletion => {
                        add_deletion(parser, clause_ids, literal);
                    }
                    _ => unreachable(),
                }
                if literal.is_zero() {
                    State::Start
                } else {
                    state
                }
            }
        }
    }
    match state {
        State::Lemma => {
            add_literal(parser, clause_ids, Literal::new(0));
        }
        State::Deletion => {
            add_deletion(parser, clause_ids, Literal::new(0));
        }
        _ => (),
    };
    let clause = start_clause(parser);
    parser.proof.push(ProofStep::lemma(clause));
    add_literal(parser, clause_ids, Literal::new(0));
    Ok(())
}

impl Display for ParseError {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "Parse error at line {}:  {}", self.line, self.why)
    }
}

#[allow(dead_code)]
fn print_db() {
    println!(
        "CLAUSE_DATABASE: [{}]",
        (unsafe { &CLAUSE_DATABASE })
            .iter()
            .map(|&l| format!("{}", l))
            .collect::<Vec<_>>()
            .join(", "),
    );
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
        let example = r#"c comment
p cnf 2 2
1 2 0
c comment
-1 -2 0"#;
        assert!(parse_formula(
            &mut parser,
            clause_ids,
            BufferInput::from(example.as_bytes().to_vec())
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
                BufferInput::from(b"1 2 3 0\nd 1 2 0".to_vec()),
            );
            assert!(result.is_ok());
            let expected_clause_ids = [
                (ClauseHashEq(Clause::new(1)), stack!(Clause::new(1))),
                (ClauseHashEq(Clause::new(2)), stack!(Clause::new(2))),
                (ClauseHashEq(Clause::new(0)), stack!()),
                (ClauseHashEq(Clause::new(3)), stack!(Clause::new(3))),
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
                #[rustfmt::skip]
             &stack!(
                 raw(0), raw(0), lit(1), lit(2), lit(0),
                 raw(1), raw(0), lit(-2), lit(-1), lit(0),
                 raw(2), raw(0), lit(1), lit(2), lit(3), lit(0),
                 raw(3), raw(0), lit(0),
                 Literal::NEVER_READ, Literal::NEVER_READ, lit(0) // TODO cut this one?
             )
            );
            assert_eq!(unsafe { &CLAUSE_OFFSET }, &stack!(0, 5, 10, 16, 19, 22));
            assert_eq!(clause_ids, expected_clause_ids);
            assert_eq!(
                parser,
                Parser {
                    maxvar: Variable::new(3),
                    num_clauses: 5,
                    db: unsafe { ClauseDatabase::new(&mut CLAUSE_DATABASE, &mut CLAUSE_OFFSET) },
                    current_clause_offset: 19,
                    clause_pivot: stack!(Literal::NEVER_READ, Literal::NEVER_READ, Literal::new(1)),
                    clause_deleted_at: stack!(
                        1,
                        usize::max_value(),
                        usize::max_value(),
                        usize::max_value()
                    ),
                    proof_start: Clause::new(2),
                    proof: stack![
                        ProofStep::lemma(Clause::new(2)),
                        ProofStep::deletion(Clause::new(0)),
                        ProofStep::lemma(Clause::new(3)),
                        ProofStep::lemma(Clause::new(4)),
                    ],
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
    fn reset_globals() {
        unsafe {
            CLAUSE_OFFSET.clear();
            CLAUSE_DATABASE.clear();
        }
    }
}

impl HeapSpace for Parser {
    fn heap_space(&self) -> usize {
        self.db.heap_space()
            + self.clause_pivot.heap_space()
            + self.clause_deleted_at.heap_space()
            + self.proof.heap_space()
    }
}

trait Input {
    type Iter: Iterator<Item = u8>;
    fn line(&self) -> usize;
    fn line_mut(&mut self) -> &mut usize;
    fn iter_mut(&mut self) -> &mut Peekable<Self::Iter>;

    fn advance(&mut self) -> Option<u8>
    where
        Self: Sized,
    {
        self.iter_mut().next().map(|c| {
            if c == b'\n' {
                *self.line_mut() += 1;
            }
            c
        })
    }

    fn peek(&mut self) -> Option<u8>
    where
        Self: Sized,
    {
        match self.iter_mut().peek() {
            Some(c) => Some(*c),
            None => None,
        }
    }

    fn error<U>(&self, why: &'static str) -> Result<U>
    where
        Self: Sized,
    {
        Err(ParseError {
            why: why,
            line: self.line(),
        })
    }

    fn into_iter(self) -> Peekable<InputIntoIter<Self>>
    where
        Self: Sized,
    {
        InputIntoIter(self).peekable()
    }
}

struct InputIntoIter<T: Input>(T);

impl<T: Input> Iterator for InputIntoIter<T> {
    type Item = u8;
    fn next(&mut self) -> Option<u8> {
        self.0.iter_mut().next()
    }
}

type BufReaderInputIter = Map<Bytes<BufReader<File>>, fn(io::Result<u8>) -> u8>;
struct BufReaderInput {
    source: Peekable<BufReaderInputIter>,
    line: usize,
}

impl BufReaderInput {
    fn new(source: BufReader<File>) -> BufReaderInput {
        BufReaderInput {
            source: source
                .bytes()
                .map(panic_on_error as fn(io::Result<u8>) -> u8)
                .peekable(),
            line: 0,
        }
    }
}

fn panic_on_error(result: io::Result<u8>) -> u8 {
    result.unwrap_or_else(|error| die!("read error: {}", error))
}

impl Input for BufReaderInput {
    type Iter = BufReaderInputIter;
    fn line(&self) -> usize {
        self.line
    }
    fn line_mut(&mut self) -> &mut usize {
        &mut self.line
    }
    fn iter_mut(&mut self) -> &mut Peekable<Self::Iter> {
        &mut self.source
    }
}

type BufferInputIter = std::vec::IntoIter<u8>;

struct BufferInput {
    source: Peekable<BufferInputIter>,
    line: usize,
}

impl From<Vec<u8>> for BufferInput {
    fn from(vec: Vec<u8>) -> BufferInput {
        BufferInput {
            source: vec.into_iter().peekable(),
            line: 0,
        }
    }
}

impl Input for BufferInput {
    type Iter = BufferInputIter;
    fn line(&self) -> usize {
        self.line
    }
    fn line_mut(&mut self) -> &mut usize {
        &mut self.line
    }
    fn iter_mut(&mut self) -> &mut Peekable<Self::Iter> {
        &mut self.source
    }
}

type ChainInputIter<T> = Chain<ConsumingStackIterator<u8>, Peekable<T>>;

struct ChainInput<T: Iterator<Item = u8>> {
    source: Peekable<ChainInputIter<T>>,
    line: usize,
}

impl<'a, T: Iterator<Item = u8>> Input for ChainInput<T> {
    type Iter = ChainInputIter<T>;
    fn line(&self) -> usize {
        self.line
    }
    fn line_mut(&mut self) -> &mut usize {
        &mut self.line
    }
    fn iter_mut(&mut self) -> &mut Peekable<Self::Iter> {
        &mut self.source
    }
}
