//! DIMACS and DRAT parser

use crate::{
    clause::{Clause, ProofStep},
    clausedatabase::ClauseDatabase,
    literal::{Literal, Variable},
    memory::{format_memory_usage, HeapSpace, Offset, Slice, Stack},
    output::number,
};
#[cfg(feature = "flame_it")]
use flamer::flame;
use memmap::MmapOptions;
use std::collections::HashMap;
use std::{
    cmp, fmt,
    fmt::{Display, Formatter},
    fs::File,
    hash::{Hash, Hasher},
    io, panic, str,
};

/// format: clause are stored sequentially, using:
/// - clause id (usize), stored as 2x32bit LE
/// - sequence of Literal
/// - zero terminator Literal::new(0)

pub const PADDING_START: usize = 2;
pub const PADDING_END: usize = 1;

pub static mut CLAUSE_DATABASE: Stack<Literal> = Stack { vec: Vec::new() };
pub static mut CLAUSE_OFFSET: Stack<usize> = Stack { vec: Vec::new() };

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

#[derive(Debug, PartialEq, Eq)]
struct ParseError {
    line: usize,
    col: usize,
    why: String,
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
    parse_formula(
        &mut parser,
        &mut clause_ids,
        read_or_die(formula_file).as_slice(),
    )
    .map(|err| die!("error parsing formula at line {} col {}", err.line, err.col));
    parse_proof(
        &mut parser,
        &mut clause_ids,
        read_or_die(proof_file).as_slice(),
    )
    .map(|err| die!("error parsing proof at line {} col {}", err.line, err.col));
    parser
}

fn read_or_die(filename: &str) -> Stack<u8> {
    read_file(filename).unwrap_or_else(|err| die!("{}", err))
}

fn read_file(filename: &str) -> Result<Stack<u8>, io::Error> {
    let file = File::open(&filename)?;
    let size = file.metadata()?.len();
    Ok(if size == 0 {
        Stack::new()
    } else {
        Stack::from_vec(unsafe { MmapOptions::new().map(&file) }.unwrap().to_owned())
    })
}

fn convert_ascii<T: str::FromStr>(ascii: Slice<u8>) -> T
where
    <T as str::FromStr>::Err: fmt::Debug,
{
    unsafe { str::from_utf8_unchecked(ascii.slice()) }
        .parse::<T>()
        .unwrap()
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
        .as_mut_slice()
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

fn add_literal_ascii<'r>(
    parser: &'r mut Parser,
    clause_ids: &mut HashTable,
    input: Slice<u8>,
) -> Literal {
    let literal = Literal::new(convert_ascii::<i32>(input));
    add_literal(parser, clause_ids, literal);
    literal
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

fn add_deletion_ascii(
    parser: &mut Parser,
    clause_ids: &mut HashTable,
    input: Slice<u8>,
) -> Literal {
    add_deletion(
        parser,
        clause_ids,
        Literal::new(convert_ascii::<i32>(input)),
    )
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

fn isdigit(value: u8) -> bool {
    value >= b'0' && value <= b'9'
}

fn parse_number(input: Slice<u8>) -> Option<(Slice<u8>, u32)> {
    let mut offset = 0;
    while offset < input.len() {
        if input[offset] != b' ' {
            break;
        }
        offset += 1;
    }
    let start = offset;
    while offset < input.len() {
        let value = input[offset];
        if value == b' ' || value == b'\n' {
            break;
        }
        if !isdigit(value) {
            return None;
        }
        offset += 1;
    }
    if offset == input.len() {
        return None;
    }
    Some((
        input.range(offset, input.len()),
        convert_ascii(input.range(start, offset)),
    ))
}

fn parse_comment(input: Slice<u8>) -> Option<(Slice<u8>, ())> {
    if input.empty() {
        return None;
    }
    if input[0] != b'c' {
        return None;
    }
    for offset in 0..input.len() {
        if input[offset] == b'\n' {
            return Some((input.range(offset + 1, input.len()), ()));
        }
    }
    return None;
}

fn parse_formula_header<'a>(
    mut input: Slice<'a, u8>,
    line: &mut usize,
) -> Option<(Slice<'a, u8>, (u32, u32))> {
    while let Some((rest, _comment)) = parse_comment(input) {
        input = rest;
        *line += 1;
    }
    let prefix = Slice::new(b"p cnf");
    if input.range(0, prefix.len()) != prefix {
        return None;
    }
    let (input, maxvar) = parse_number(input.range(prefix.len(), input.len()))?;
    let (input, num_clauses) = parse_number(input)?;
    Some((input, (maxvar, num_clauses)))
}

fn isspace(c: u8) -> bool {
    [b' ', b'\n', b'\r'].iter().any(|&s| s == c)
}

fn parse_formula(
    parser: &mut Parser,
    clause_ids: &mut HashTable,
    input: Slice<u8>,
) -> Option<ParseError> {
    #[derive(Debug)]
    enum ClauseState {
        InLiteral,
        NotInLiteral,
        Comment,
    }
    let mut line = 0;
    let mut col = 0;

    let input = match parse_formula_header(input, &mut line) {
        None => {
            return Some(ParseError {
                line: line,
                col: col,
                why: "Failed to parse DIMACS header".to_string(),
            });
        }
        Some((rest, (_maxvar, _num_clauses))) => rest,
    };

    let mut head = true;
    let mut state = ClauseState::NotInLiteral;
    let mut start = 0;
    for i in 0..input.len() {
        let c = input[i];
        line += if c == b'\n' { 1 } else { 0 };
        col = if c == b'\n' { 0 } else { col + 1 };
        let error = || Some(ParseError::new(line, col, ""));
        match state {
            ClauseState::NotInLiteral => match c {
                b'-' | b'0'..=b'9' => {
                    state = ClauseState::InLiteral;
                    start = i;
                }
                b'c' if col == 1 => {
                    state = ClauseState::Comment;
                }
                _ if isspace(c) => (),
                _ => return error(),
            },
            ClauseState::InLiteral => match c {
                b'-' | b'0'..=b'9' => (),
                _ if isspace(c) => {
                    if head {
                        start_clause(&mut *parser);
                        parser.clause_pivot.push(Literal::NEVER_READ);
                    }
                    let literal =
                        add_literal_ascii(&mut *parser, clause_ids, input.range(start, i));
                    head = literal.is_zero();
                    state = ClauseState::NotInLiteral;
                }
                _ => return error(),
            },
            ClauseState::Comment => {
                if c == b'\n' {
                    state = ClauseState::NotInLiteral;
                }
            }
        }
    }
    // handle missing newline at EOF
    match state {
        ClauseState::InLiteral => {
            add_literal_ascii(parser, clause_ids, input.range(start, input.len()));
        }
        _ => (),
    }
    None
}

fn lemma_binary(input: Slice<u8>) -> (Slice<u8>, char) {
    invariant!(input.len() > 0);
    (input.range(1, input.len()), input[0] as char)
}

fn number_binary(input: Slice<u8>) -> (Slice<u8>, Literal) {
    let mut i = 0;
    let mut result = 0;
    while i < input.len() {
        let value = input[i];
        result |= ((value & 0x7f) as u32) << (7 * i);
        i += 1;
        if (value & 0x80) == 0 {
            break;
        }
    }
    (input.range(i, input.len()), Literal::from_raw(result))
}

fn parse_proof_binary<'a, 'r>(
    mut parser: &'r mut Parser,
    clause_ids: &mut HashTable,
    mut input: Slice<u8>,
) {
    enum LemmaPositionBinary {
        Start,
        Lemma,
        Deletion,
    }

    let mut state = LemmaPositionBinary::Start;
    let mut head = true;
    while input.len() > 0 {
        input = match state {
            LemmaPositionBinary::Start => {
                let (input, addition_or_deletion) = lemma_binary(input);
                if addition_or_deletion == 'd' {
                    state = LemmaPositionBinary::Deletion;
                    start_clause(parser);
                } else {
                    invariant!(addition_or_deletion == 'a');
                    state = LemmaPositionBinary::Lemma;
                    let clause = start_clause(&mut parser);
                    head = true;
                    parser.proof.push(ProofStep::lemma(clause));
                }
                input
            }
            LemmaPositionBinary::Lemma => match number_binary(input) {
                (input, literal) => {
                    if head {
                        parser.clause_pivot.push(literal);
                        head = false;
                    }
                    add_literal(parser, clause_ids, literal);
                    if literal.is_zero() {
                        state = LemmaPositionBinary::Start;
                    }
                    input
                }
            },
            LemmaPositionBinary::Deletion => match number_binary(input) {
                (input, literal) => {
                    add_deletion(parser, clause_ids, literal);
                    if literal.is_zero() {
                        state = LemmaPositionBinary::Start;
                    }
                    input
                }
            },
        }
    }
}

fn parse_proof<'a>(
    parser: &'a mut Parser,
    clause_ids: &mut HashTable,
    input: Slice<u8>,
) -> Option<ParseError> {
    parser.proof_start = Clause::new(parser.db.offset.len() as u64 - 1);

    let mut binary = false;

    // copied from drat-trim
    for i in 0..cmp::min(10, input.len()) {
        let c = input[i];
        if (c != 100) && (c != 10) && (c != 13) && (c != 32) && (c != 45) && ((c < 48) || (c > 57))
        {
            binary = true;
        }
    }
    let result = if binary {
        comment!("Turning on binary mode.");
        parse_proof_binary(parser, clause_ids, input);
        None
    } else {
        parse_proof_text(parser, clause_ids, input)
    };
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

fn parse_proof_text<'a, 'r>(
    parser: &'r mut Parser,
    clause_ids: &mut HashTable,
    input: Slice<u8>,
) -> Option<ParseError> {
    #[derive(Debug, PartialEq, Eq)]
    enum LemmaPositionText {
        Start,
        LemmaLiteral,
        PostLemmaLiteral,
        Deletion,
        DeletionLiteral,
    }

    let mut state = LemmaPositionText::Start;
    let mut head = true;
    let mut start = 0;
    let mut line = 0;
    let mut col = 0;
    for i in 0..input.len() {
        let c = input[i];
        line += if c == b'\n' { 1 } else { 0 };
        col = if c == b'\n' { 0 } else { col + 1 };
        let error = || Some(ParseError::new(line, col, ""));
        match state {
            LemmaPositionText::Start => match c {
                b'\n' => head = true,
                b' ' | b'\r' => (),
                b'd' => {
                    start_clause(parser);
                    state = LemmaPositionText::Deletion
                }
                b'-' | b'0'..=b'9' => {
                    if head {
                        let clause = start_clause(parser);
                        parser.proof.push(ProofStep::lemma(clause));
                    }
                    state = LemmaPositionText::LemmaLiteral;
                    start = i;
                }
                _ => return error(),
            },
            LemmaPositionText::LemmaLiteral => match c {
                _ if isspace(c) => {
                    let literal =
                        add_literal_ascii(&mut *parser, clause_ids, input.range(start, i));
                    if head {
                        parser.clause_pivot.push(literal);
                    }
                    head = literal.is_zero();
                    state = if head {
                        LemmaPositionText::Start
                    } else {
                        LemmaPositionText::PostLemmaLiteral
                    }
                }
                b'0'..=b'9' => (),
                _ => return error(),
            },
            LemmaPositionText::PostLemmaLiteral => match c {
                b'\n' => state = LemmaPositionText::Start,
                b' ' | b'\r' => (),
                b'-' | b'0'..=b'9' => {
                    state = LemmaPositionText::LemmaLiteral;
                    start = i;
                }
                _ => return error(),
            },
            LemmaPositionText::Deletion => match c {
                b' ' => (),
                b'-' | b'0'..=b'9' => {
                    state = LemmaPositionText::DeletionLiteral;
                    start = i;
                }
                _ => return error(),
            },
            LemmaPositionText::DeletionLiteral => match c {
                _ if isspace(c) => {
                    let literal = add_deletion_ascii(parser, clause_ids, input.range(start, i));
                    state = if literal.is_zero() {
                        LemmaPositionText::Start
                    } else {
                        LemmaPositionText::Deletion
                    };
                }
                b'-' | b'0'..=b'9' => (),
                _ => return error(),
            },
        };
    }
    let state = match state {
        LemmaPositionText::LemmaLiteral => {
            let literal = add_literal_ascii(parser, clause_ids, input.range(start, input.len()));
            if literal.is_zero() {
                LemmaPositionText::Start
            } else {
                LemmaPositionText::PostLemmaLiteral
            }
        }
        LemmaPositionText::DeletionLiteral => {
            let literal = add_deletion_ascii(parser, clause_ids, input.range(start, input.len()));
            if literal.is_zero() {
                LemmaPositionText::Start
            } else {
                LemmaPositionText::PostLemmaLiteral
            }
        }
        _ => state,
    };
    let state = match state {
        LemmaPositionText::PostLemmaLiteral => {
            // Some solvers don't terminate the last clause in the proof with a
            // zero, so we add it here.
            add_literal(parser, clause_ids, Literal::new(0));
            LemmaPositionText::Start
        }
        _ => state,
    };
    invariant!(state == LemmaPositionText::Start);
    None
}

impl ParseError {
    fn new(line: usize, col: usize, why: &str) -> ParseError {
        ParseError {
            line: line,
            col: col,
            why: why.to_string(),
        }
    }
}

impl Display for ParseError {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(
            f,
            "Parse error at line {} column {}: {}",
            self.line, self.col, self.why
        )
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

    macro_rules! stack {
        ($($x:expr),*) => (Stack::from_vec(vec!($($x),*)));
    }

    fn sample_formula(clause_ids: &mut HashTable) -> Parser {
        let mut parser = Parser::new();
        parse_formula(
            &mut parser,
            clause_ids,
            Slice::new(
                r#"c comment
p cnf 2 2
1 2 0
-1 -2 0"#
                    .as_bytes(),
            ),
        )
        .map(|err| assert!(false, "{}", err));
        parser
    }

    #[test]
    fn valid_formula_and_proof() {
        run_test(|| {
            let mut clause_ids = HashTable::new();
            let mut parser = sample_formula(&mut clause_ids);
            parse_proof(
                &mut parser,
                &mut clause_ids,
                Slice::new(b"1 2 3 0\nd 1 2 0"),
            );
            let expected_clause_ids = [
                (ClauseHashEq(Clause::new(1)), stack!(Clause::new(1))),
                (ClauseHashEq(Clause::new(2)), stack!(Clause::new(2))),
                (ClauseHashEq(Clause::new(0)), stack!()),
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
            assert_eq!(
                unsafe { &CLAUSE_DATABASE },
                #[rustfmt::skip]
                &stack!(
                    raw(0), raw(0), lit(1), lit(2), lit(0),
                    raw(1), raw(0), lit(-2), lit(-1), lit(0),
                    raw(2), raw(0), lit(1), lit(2), lit(3), lit(0),
                    Literal::NEVER_READ, Literal::NEVER_READ, lit(0)
                )
            );
            assert_eq!(unsafe { &CLAUSE_OFFSET }, &stack!(0, 5, 10, 16, 19));
            assert_eq!(clause_ids, expected_clause_ids);
            assert_eq!(
                parser,
                Parser {
                    maxvar: Variable::new(3),
                    num_clauses: 4,
                    db: unsafe { ClauseDatabase::new(&mut CLAUSE_DATABASE, &mut CLAUSE_OFFSET) },
                    current_clause_offset: 16,
                    clause_pivot: stack!(Literal::NEVER_READ, Literal::NEVER_READ, Literal::new(1)),
                    clause_deleted_at: stack!(1, usize::max_value(), usize::max_value()),
                    proof_start: Clause::new(2),
                    proof: stack![
                        ProofStep::lemma(Clause::new(2)),
                        ProofStep::deletion(Clause::new(0)),
                        ProofStep::lemma(Clause::new(3))
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

/// Note: this does not account for the memory usage of the hash table `clause_ids`.
impl Parser {
    pub fn print_memory_usage(&self) {
        comment!("parser memory usage (in MB)");
        number("memory-parser", format_memory_usage(self.heap_space()));
    }
}
