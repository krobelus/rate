//! DIMACS and DRAT parser

use crate::{
    clause::{Clause, ClauseCopy, ProofStep},
    literal::{Literal, Variable},
    memory::{Offset, Slice, Stack},
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
    io, ops, panic, str,
};

pub static mut CLAUSE_OFFSET: Stack<usize> = Stack { vec: Vec::new() };
pub static mut DB: Stack<Literal> = Stack { vec: Vec::new() };

#[derive(Debug, PartialEq)]
pub struct Parser {
    pub maxvar: Variable,
    pub num_clauses: usize,
    pub db: &'static mut Stack<Literal>,
    pub current_clause_offset: usize,
    pub clause_offset: &'static mut Stack<usize>,
    clause_ids: HashMap<ClauseHashEq, Stack<Clause>>,
    pub clause_pivot: Option<Stack<Literal>>,
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
    pub fn new(pivot_is_first_literal: bool) -> Parser {
        unsafe { CLAUSE_OFFSET.push(0) }; // sentinel
        Parser {
            maxvar: Variable::new(0),
            num_clauses: usize::max_value(),
            db: unsafe { &mut DB },
            current_clause_offset: 0,
            clause_offset: unsafe { &mut CLAUSE_OFFSET },
            clause_pivot: if pivot_is_first_literal {
                Some(Stack::new())
            } else {
                None
            },
            clause_deleted_at: Stack::new(),
            proof_start: Clause(0),
            proof: Stack::new(),
            clause_ids: HashMap::new(),
        }
    }
    // TODO consolidate
    fn clause(&self, clause: Clause) -> Slice<Literal> {
        let range = self.clause_range(clause);
        self.db.as_slice().range(range.start, range.end)
    }
    fn clause_copy(&self, clause: Clause) -> ClauseCopy {
        ClauseCopy::new(clause, self.clause(clause))
    }
    fn clause_range(&self, clause: Clause) -> ops::Range<usize> {
        self.clause_offset[clause.as_offset()]..self.clause_offset[clause.as_offset() + 1]
    }
}

#[cfg_attr(feature = "flame_it", flame)]
pub fn parse_files<'a>(
    formula_file: &str,
    proof_file: &str,
    pivot_is_first_literal: bool,
) -> Parser {
    let mut parser = Parser::new(pivot_is_first_literal);
    parse_formula(&mut parser, read_or_die(formula_file).as_slice())
        .map(|err| die!("error parsing formula at line {} col {}", err.line, err.col));
    parse_proof(&mut parser, read_or_die(proof_file).as_slice())
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
    parser.clause_offset.pop(); // pop sentinel
    let clause = parser.clause_offset.len();
    parser.clause_offset.push(parser.db.len());
    parser.clause_deleted_at.push(usize::max_value());
    Clause(clause)
}

fn close_clause(parser: &mut Parser) -> Clause {
    let clause = Clause(parser.clause_offset.len()) - 1;
    let start = parser.current_clause_offset;
    let end = parser.db.len();
    let len = end - start;
    parser.current_clause_offset = if len == 1 {
        parser.db.push(Literal::BOTTOM);
        end + 1
    } else {
        end
    };
    let _sort_literally = |&literal: &Literal| literal.decode();
    let _sort_magnitude = |&literal: &Literal| literal.encoding;
    parser
        .db
        .as_mut_slice()
        .range(start, end)
        .sort_unstable_by_key(_sort_literally);
    parser.clause_offset.push(parser.db.len()); // sentinel
    clause
}

fn pop_clause(parser: &mut Parser, previous_offset: usize) {
    parser.current_clause_offset = previous_offset;
    parser.db.truncate(previous_offset);
    parser.clause_offset.pop();
}

fn add_literal<'a, 'r>(parser: &'r mut Parser, literal: Literal) {
    if literal.is_zero() {
        let clause = close_clause(parser);
        // TODO we could handle duplicate literals here
        let key = ClauseHashEq(clause);
        parser
            .clause_ids
            .entry(key)
            .or_insert(Stack::new())
            .push(clause);
    } else {
        parser.maxvar = cmp::max(parser.maxvar, literal.var());
        parser.db.push(literal);
    }
}

fn add_literal_ascii<'a, 'r>(parser: &'r mut Parser, input: Slice<u8>) -> Literal {
    let literal = Literal::new(convert_ascii::<i32>(input));
    add_literal(parser, literal);
    literal
}

fn add_deletion(parser: &mut Parser, literal: Literal) -> Literal {
    if literal.is_zero() {
        let prev = parser.current_clause_offset;
        let clause = close_clause(parser);
        match find_clause(clause, parser) {
            None => {
                warn!(
                    "Deleted clause is not present in the formula: {}",
                    parser.clause_copy(clause)
                );
                // need this for sickcheck
                parser
                    .proof
                    .push(ProofStep::Deletion(Clause::DOES_NOT_EXIST))
            }
            Some(clause) => {
                parser.clause_deleted_at[clause.as_offset()] = parser.proof.len();
                parser.proof.push(ProofStep::Deletion(clause))
            }
        }
        pop_clause(parser, prev);
    } else {
        parser.db.push(literal);
    }
    literal
}

fn add_deletion_ascii(parser: &mut Parser, input: Slice<u8>) -> Literal {
    add_deletion(parser, Literal::new(convert_ascii::<i32>(input)))
}

#[derive(Debug, Eq, Clone, Copy)]
struct ClauseHashEq(Clause);

impl Hash for ClauseHashEq {
    fn hash<H: Hasher>(&self, hasher: &mut H) {
        unsafe {
            let start = CLAUSE_OFFSET[self.0.as_offset()];
            let end = CLAUSE_OFFSET[self.0.as_offset() + 1];
            compute_hash(DB.as_slice().range(start, end)).hash(hasher)
        }
    }
}

impl PartialEq for ClauseHashEq {
    fn eq(&self, other: &ClauseHashEq) -> bool {
        unsafe {
            invariant!(self.0.as_offset() + 1 < CLAUSE_OFFSET.len());
            let start = CLAUSE_OFFSET[self.0.as_offset()];
            let end = CLAUSE_OFFSET[self.0.as_offset() + 1];
            let other_start = CLAUSE_OFFSET[other.0.as_offset()];
            for i in 0..end - start {
                if other_start + i == DB.len() {
                    return false;
                }
                if DB[start + i] != DB[other_start + i] {
                    return false;
                }
            }
        }
        true
    }
}

fn find_clause<'a>(needle: Clause, parser: &mut Parser) -> Option<Clause> {
    parser
        .clause_ids
        .get_mut(&ClauseHashEq(needle))
        .map(|clauses| {
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

fn parse_formula<'a>(parser: &'a mut Parser, input: Slice<u8>) -> Option<ParseError> {
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
                        parser
                            .clause_pivot
                            .as_mut()
                            .map(|pivots| pivots.push(Literal::NEVER_READ));
                    }
                    let literal = add_literal_ascii(&mut *parser, input.range(start, i));
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
            add_literal_ascii(parser, input.range(start, input.len()));
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

fn parse_proof_binary<'a, 'r>(mut parser: &'r mut Parser, mut input: Slice<u8>) {
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
                    parser.proof.push(ProofStep::Lemma(clause));
                }
                input
            }
            LemmaPositionBinary::Lemma => match number_binary(input) {
                (input, literal) => {
                    if head {
                        parser
                            .clause_pivot
                            .as_mut()
                            .map(|pivots| pivots.push(literal));
                        head = false;
                    }
                    add_literal(parser, literal);
                    if literal.is_zero() {
                        state = LemmaPositionBinary::Start;
                    }
                    input
                }
            },
            LemmaPositionBinary::Deletion => match number_binary(input) {
                (input, literal) => {
                    add_deletion(parser, literal);
                    if literal.is_zero() {
                        state = LemmaPositionBinary::Start;
                    }
                    input
                }
            },
        }
    }
}

fn parse_proof<'a>(parser: &'a mut Parser, input: Slice<u8>) -> Option<ParseError> {
    parser.proof_start = Clause(parser.clause_offset.len() - 1);

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
        echo!("c Turning on binary mode.");
        parse_proof_binary(parser, input);
        None
    } else {
        parse_proof_text(parser, input)
    };
    // Add empty clauses to the end of the proof.
    parser.num_clauses = parser.clause_offset.len();
    let empty_clause = close_clause(parser);
    parser.proof.push(ProofStep::Lemma(empty_clause));
    result
}

fn parse_proof_text<'a, 'r>(parser: &'r mut Parser, input: Slice<u8>) -> Option<ParseError> {
    #[derive(Debug)]
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
                b'd' => state = LemmaPositionText::Deletion,
                b'-' | b'0'..=b'9' => {
                    if head {
                        let clause = start_clause(parser);
                        parser.proof.push(ProofStep::Lemma(clause));
                    }
                    state = LemmaPositionText::LemmaLiteral;
                    start = i;
                }
                _ => return error(),
            },
            LemmaPositionText::LemmaLiteral => match c {
                _ if isspace(c) => {
                    let literal = add_literal_ascii(&mut *parser, input.range(start, i));
                    if head {
                        parser
                            .clause_pivot
                            .as_mut()
                            .map(|pivots| pivots.push(literal));
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
                    let literal = add_deletion_ascii(parser, input.range(start, i));
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
    match state {
        LemmaPositionText::LemmaLiteral => {
            add_literal_ascii(parser, input.range(start, input.len()));
        }
        LemmaPositionText::DeletionLiteral => {
            add_deletion_ascii(parser, input.range(start, input.len()));
        }
        _ => (),
    }
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

    fn sample_formula() -> Parser {
        let mut parser = Parser::new(false);
        parse_formula(
            &mut parser,
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
            let mut parser = sample_formula();
            parse_proof(&mut parser, Slice::new(b"1 2 3 0\nd 1 2 0"));
            let clause_ids = [
                (ClauseHashEq(Clause(0)), stack!()),
                (ClauseHashEq(Clause(1)), stack!(Clause(1))),
                (ClauseHashEq(Clause(2)), stack!(Clause(2))),
            ]
            .iter()
            .cloned()
            .collect();
            assert_eq!(unsafe { &DB }, &literals!(1, 2, -2, -1, 1, 2, 3));
            assert_eq!(unsafe { &CLAUSE_OFFSET }, &stack!(0, 2, 4, 7, 7));
            assert_eq!(
                parser,
                Parser {
                    maxvar: Variable::new(3),
                    num_clauses: 4,
                    db: unsafe { &mut DB },
                    current_clause_offset: 7,
                    clause_offset: unsafe { &mut CLAUSE_OFFSET },
                    clause_ids: clause_ids,
                    clause_pivot: None,
                    clause_deleted_at: stack!(1, usize::max_value(), usize::max_value()),
                    proof_start: Clause(2),
                    proof: stack![
                        ProofStep::Lemma(Clause(2)),
                        ProofStep::Deletion(Clause(0)),
                        ProofStep::Lemma(Clause(3))
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
            DB.clear();
        }
    }
}
