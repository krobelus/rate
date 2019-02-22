//! DIMACS and DRAT parser

use crate::{
    clause::{Clause, ProofStep},
    clausedatabase::{ClauseDatabase, WitnessDatabase},
    config::{unreachable, RedundancyProperty},
    literal::{Literal, Variable},
    memory::{ConsumingStackIterator, HeapSpace, Offset, Slice, Stack},
    output::Timer,
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
    iter::{Chain, FromIterator, Map, Peekable},
    panic, str,
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
}

impl Parser {
    pub fn new(redundancy_property: RedundancyProperty) -> Parser {
        unsafe {
            CLAUSE_DATABASE.initialize();
            if redundancy_property == RedundancyProperty::PR {
                WITNESS_DATABASE.initialize();
            }
        }
        Parser {
            redundancy_property: redundancy_property,
            maxvar: Variable::new(0),
            clause_db: unsafe { &mut CLAUSE_DATABASE },
            witness_db: unsafe { &mut WITNESS_DATABASE },
            clause_pivot: Stack::new(),
            #[cfg(feature = "clause_lifetime_heuristic")]
            clause_deleted_at: Stack::new(),
            proof_start: Clause::new(0),
            proof: Stack::new(),
        }
    }
    pub fn is_pr(&self) -> bool {
        self.redundancy_property == RedundancyProperty::PR
    }
}

type HashTable = HashMap<ClauseHashEq, SmallStack<Clause>>;

#[cfg_attr(feature = "flame_it", flame)]
pub fn parse_files(
    formula_file: &str,
    proof_file: &str,
    redundancy_property: RedundancyProperty,
) -> Parser {
    let mut clause_ids = HashTable::new();
    let mut parser = Parser::new(redundancy_property);
    {
        let _timer = Timer::name("parsing formula");
        parse_formula(&mut parser, &mut clause_ids, open_file(&formula_file))
            .unwrap_or_else(|err| die!("error parsing formula at line {}", err.line));
    }
    {
        let _timer = Timer::name("parsing proof");
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

fn add_literal(
    parser: &mut Parser,
    clause_ids: &mut HashTable,
    state: ParserState,
    literal: Literal,
) {
    parser.maxvar = cmp::max(parser.maxvar, literal.variable());
    match state {
        ParserState::Clause => {
            parser.clause_db.push_literal(literal);
            if parser.is_pr() && literal.is_zero() {
                parser.witness_db.push_literal(literal);
            }
        }
        ParserState::Witness => {
            invariant!(parser.is_pr());
            parser.witness_db.push_literal(literal);
            if literal.is_zero() {
                parser.clause_db.push_literal(literal);
            }
        }
        ParserState::Deletion => {
            parser.clause_db.push_literal(literal);
            if literal.is_zero() {
                add_deletion(parser, clause_ids)
            }
        }
        ParserState::Start => unreachable(),
    }
    match state {
        ParserState::Clause | ParserState::Witness => {
            if literal.is_zero() {
                let clause = parser.clause_db.last_clause();
                let key = ClauseHashEq(clause);
                clause_ids
                    .entry(key)
                    .or_insert(SmallStack::empty())
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
            warn!(
                "Deleted clause is not present in the formula: {}",
                parser.clause_db.clause_to_string(clause)
            );
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
struct ClauseHashEq(Clause);

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
        .map(|clause_db| clause_db.swap_remove(0))
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

fn open_clause(parser: &mut Parser, state: ParserState) -> Clause {
    let clause = parser.clause_db.open_clause();
    if parser.is_pr() && state != ParserState::Deletion {
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
            input.advance();
            continue;
        }
        if c == b'c' {
            parse_comment(&mut input);
            continue;
        }
        let literal = parse_literal(&mut input)?;
        if clause_head {
            open_clause(parser, ParserState::Clause);
            parser.clause_pivot.push(Literal::NEVER_READ);
            #[cfg(feature = "clause_lifetime_heuristic")]
            parser.clause_deleted_at.push(usize::max_value());
        }
        add_literal(parser, clause_ids, ParserState::Clause, literal);
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

fn parse_proof(parser: &mut Parser, clause_ids: &mut HashTable, input: impl Input) -> Result<()> {
    parser.proof_start = Clause::new(parser.clause_db.number_of_clauses());
    let (mut input, is_binary) = is_binary_drat_stream(input);
    if is_binary {
        comment!("binary proof mode");
    }
    do_parse_proof(parser, clause_ids, &mut input, is_binary)
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
enum ParserState {
    Start,
    Clause,
    Witness,
    Deletion,
}

fn do_parse_proof(
    parser: &mut Parser,
    clause_ids: &mut HashTable,
    input: &mut impl Input,
    binary: bool,
) -> Result<()> {
    let literal_parser = if binary {
        parse_literal_binary
    } else {
        parse_literal
    };
    let mut state = ParserState::Start;
    let mut lemma_head = true;
    let mut first_literal = None;
    while let Some(c) = input.peek() {
        if !binary && is_space(c) {
            input.advance();
            continue;
        }
        if state == ParserState::Start {
            state = match c {
                b'd' => {
                    input.advance();
                    open_clause(parser, ParserState::Deletion);
                    ParserState::Deletion
                }
                b'c' => {
                    parse_comment(input);
                    ParserState::Start
                }
                c if (!binary && is_digit_or_dash(c)) || (binary && c == b'a') => {
                    if binary {
                        input.advance();
                    }
                    lemma_head = true;
                    let clause = open_clause(parser, ParserState::Clause);
                    parser.proof.push(ProofStep::lemma(clause));
                    ParserState::Clause
                }
                _ => return input.error(DRAT),
            };
            continue;
        }
        let literal = literal_parser(input)?;
        if parser.is_pr() && state == ParserState::Clause && first_literal == Some(literal) {
            first_literal = None;
            state = ParserState::Witness;
        }
        if state == ParserState::Clause && lemma_head {
            parser.clause_pivot.push(literal);
            #[cfg(feature = "clause_lifetime_heuristic")]
            parser.clause_deleted_at.push(usize::max_value());
            first_literal = Some(literal);
            lemma_head = false;
        }
        invariant!(state != ParserState::Start);
        add_literal(parser, clause_ids, state, literal);
        if literal.is_zero() {
            state = ParserState::Start;
        }
    }
    // patch missing zero terminators
    match state {
        ParserState::Clause | ParserState::Deletion | ParserState::Witness => {
            add_literal(parser, clause_ids, state, Literal::new(0));
        }
        ParserState::Start => (),
    };
    // ensure that every proof ends with an empty clause
    let clause = open_clause(parser, ParserState::Clause);
    parser.proof.push(ProofStep::lemma(clause));
    add_literal(parser, clause_ids, ParserState::Clause, Literal::new(0));
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
        let mut parser = Parser::new(RedundancyProperty::RAT);
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
                (
                    ClauseHashEq(Clause::new(1)),
                    SmallStack::one(Clause::new(1)),
                ),
                (
                    ClauseHashEq(Clause::new(2)),
                    SmallStack::one(Clause::new(2)),
                ),
                (ClauseHashEq(Clause::new(0)), SmallStack::empty()),
                (
                    ClauseHashEq(Clause::new(3)),
                    SmallStack::one(Clause::new(3)),
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

#[derive(Debug, PartialEq, Clone)]
enum SmallStackState<T> {
    Empty,
    One(T),
    Many(Stack<T>),
}

#[derive(Debug, PartialEq, Clone)]
struct SmallStack<T> {
    state: SmallStackState<T>,
}

impl<T: Copy + Default> SmallStack<T> {
    fn empty() -> SmallStack<T> {
        SmallStack {
            state: SmallStackState::Empty,
        }
    }
    #[allow(dead_code)]
    fn one(value: T) -> SmallStack<T> {
        SmallStack {
            state: SmallStackState::One(value),
        }
    }
    fn many(stack: Stack<T>) -> SmallStack<T> {
        SmallStack {
            state: SmallStackState::Many(stack),
        }
    }
    fn push(&mut self, new_value: T) {
        if let SmallStackState::Empty = self.state {
            self.state = SmallStackState::One(new_value);
            return;
        }
        if let SmallStackState::One(value) = self.state {
            self.state = SmallStackState::Many(stack!(value));
        }
        if let SmallStackState::Many(stack) = &mut self.state {
            stack.push(new_value);
            return;
        }
        unreachable();
    }
    fn swap_remove(&mut self, index: usize) -> T {
        requires!(index == 0);
        if let SmallStackState::One(value) = self.state {
            self.state = SmallStackState::Empty;
            value
        } else if let SmallStackState::Many(stack) = &mut self.state {
            stack.swap_remove(0)
        } else {
            unreachable()
        }
    }
}

impl<T: Copy + Default> FromIterator<T> for SmallStack<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> SmallStack<T> {
        SmallStack::many(Stack::from_iter(iter))
    }
}
