//! DIMACS and DRAT parser

use crate::{
    clause::{Clause, ClauseCopy, ProofStep},
    config::HASHTABLE_SIZE,
    literal::{Literal, Variable},
    memory::{Array, Offset, Slice, Stack},
};
#[cfg(feature = "flame_it")]
use flamer::flame;
use memmap::MmapOptions;
use std::{
    cmp, fmt,
    fmt::{Display, Formatter},
    fs::File,
    io, str,
};

#[derive(Debug, PartialEq)]
pub struct Parser {
    pub maxvar: Variable,
    pub num_clauses: usize,
    pub db: Stack<Literal>,
    pub clause_pivot: Option<Stack<Literal>>,
    pub clause_offset: Stack<usize>,
    clause_scheduled_for_deletion: Stack<bool>,
    pub proof_start: Clause,
    pub proof: Stack<ProofStep>,
    hashtable: Array<usize, Stack<Clause>>,
}

#[derive(Debug, PartialEq, Eq)]
struct ParseError {
    line: usize,
    col: usize,
    why: String,
}

impl Parser {
    pub fn new(pivot_is_first_literal: bool) -> Parser {
        Parser {
            maxvar: Variable::new(0),
            num_clauses: usize::max_value(),
            db: Stack::new(),
            clause_pivot: if pivot_is_first_literal {
                Some(Stack::new())
            } else {
                None
            },
            clause_offset: Stack::new(),
            clause_scheduled_for_deletion: Stack::new(),
            proof_start: Clause(0),
            proof: Stack::new(),
            // clause_to_id: MultiMap::new(),
            hashtable: Array::new(Stack::new(), HASHTABLE_SIZE),
        }
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

fn descending(literal: &Literal) -> i32 {
    -(literal.encoding as i32)
}

fn add_deletion(parser: &mut Parser, literal: Literal, buffer: &mut Stack<Literal>) -> Literal {
    if literal.is_zero() {
        if buffer.len() == 1 {
            buffer.push(Literal::BOTTOM);
        }
        buffer.sort_unstable_by_key(descending);
        match find_clause(buffer.as_slice(), parser) {
            None => {
                warn!(
                    "Deleted clause is not present in the formula: {}",
                    ClauseCopy::new(Clause(0), buffer.as_slice())
                );
                // need this for sickcheck
                parser
                    .proof
                    .push(ProofStep::Deletion(Clause::DOES_NOT_EXIST))
            }
            Some(clause) => {
                parser.clause_scheduled_for_deletion[clause.as_offset()] = true;
                parser.proof.push(ProofStep::Deletion(clause))
            }
        }
        buffer.clear();
    } else {
        buffer.push(literal);
    }
    literal
}

fn add_deletion_ascii(
    parser: &mut Parser,
    input: Slice<u8>,
    buffer: &mut Stack<Literal>,
) -> Literal {
    add_deletion(parser, Literal::new(convert_ascii::<i32>(input)), buffer)
}

fn start_clause(parser: &mut Parser) -> Clause {
    let clause = parser.clause_offset.len();
    parser.clause_offset.push(parser.db.len());
    parser.clause_scheduled_for_deletion.push(false);
    Clause(clause)
}

fn add_literal<'a, 'r>(parser: &'r mut Parser, literal: Literal) {
    if literal.is_zero() {
        let begin = if parser.clause_offset.empty() {
            0
        } else {
            *parser.clause_offset.last()
        };
        let mut end = parser.db.len();
        if end - begin == 1 {
            add_literal(parser, Literal::BOTTOM);
            end += 1;
        }
        let clause = Clause(parser.clause_offset.len() - 1);
        let mut slice = parser.db.as_mut_slice().range(begin, end);
        slice.sort_unstable_by_key(descending);
        let hash = compute_hash(slice.as_const());
        parser.hashtable[hash].push(clause)
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

fn find_clause<'a>(needle: Slice<Literal>, parser: &mut Parser) -> Option<Clause> {
    let hash = compute_hash(needle);
    for i in 0..parser.hashtable[hash].len() {
        let clause = parser.hashtable[hash][i];
        let begin = parser.clause_offset[clause.as_offset()];
        let end = if clause.as_offset() + 1 == parser.clause_offset.len() {
            parser.db.len()
        } else {
            parser.clause_offset[clause.as_offset() + 1]
        };
        let literals = parser.db.as_slice().range(begin, end);
        invariant!(!parser.clause_scheduled_for_deletion[clause.as_offset()]);
        if literals != needle {
            continue;
        }
        parser.hashtable[hash].swap_remove(i);
        return Some(clause);
    }
    None
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
    (1023 * sum + prod ^ (31 * xor)) % HASHTABLE_SIZE
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
    }
    let mut line = 0;
    let mut col = 0;

    let input = match parse_formula_header(input, &mut line) {
        None => {
            return Some(ParseError {
                line: line,
                col: col,
                why: "Failed to parse DIMACS header".to_string(),
            })
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
    let mut buffer = Stack::new();
    let mut head = true;
    while input.len() > 0 {
        input = match state {
            LemmaPositionBinary::Start => {
                let (input, addition_or_deletion) = lemma_binary(input);
                if addition_or_deletion == 'd' {
                    state = LemmaPositionBinary::Deletion;
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
                    add_deletion(parser, literal, &mut buffer);
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
    parser.proof_start = Clause(parser.clause_offset.len());

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
    // Add empty clauses to the end of the proof and make sure that the
    // computation of the length of clause `c` can be safely computed as
    // `clause_offset[c + 1] - clause_offset[c]`.
    parser.num_clauses = parser.clause_offset.len() + 1;
    parser
        .proof
        .push(ProofStep::Lemma(Clause(parser.num_clauses - 1)));
    let end_of_empty_clause = parser.db.len();
    parser.clause_offset.push(end_of_empty_clause);
    parser.clause_offset.push(end_of_empty_clause);
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
    let mut buffer = Stack::new();
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
                    let literal = add_deletion_ascii(parser, input.range(start, i), &mut buffer);
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
            add_deletion_ascii(parser, input.range(start, input.len()), &mut buffer);
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

    #[allow(unused_macros)]
    macro_rules! stack {
        ($($x:expr),*) => (Stack::from_vec(vec!($($x),*)));
    }

    #[allow(unused_macros)]
    macro_rules! hashtable(
        { $($literals:expr => $clause:expr),+ } => {
            {
                let mut table = Array::new(Stack::new(), HASHTABLE_SIZE);
                $(
                    table[compute_hash($literals.as_slice())].push($clause);
                )+
                table
            }
        }
    );

    fn sample_formula() -> Parser {
        let mut parser = Parser::new(false);
        assert!(parse_formula(
            &mut parser,
            Slice::new(
                r#"c comment
p cnf 2 2
1 2 0
-1 -2 0"#
                    .as_bytes()
            ),
        )
        .is_none());
        parser
    }

    #[test]
    fn invalid_formulas() {
        invariant!(parse_formula(&mut Parser::new(false), Slice::new(b"p c")).is_some());
        invariant!(parse_formula(&mut Parser::new(false), Slice::new(b"p cnf 1 1\na")).is_some());
    }

    #[test]
    fn valid_formula_and_proof() {
        let mut parser = sample_formula();
        parse_proof(&mut parser, Slice::new(b"1 2 3 0\nd 1 2 0"));
        assert_eq!(
            parser,
            Parser {
                maxvar: Variable::new(3),
                num_clauses: 4,
                db: literals!(2, 1, -2, -1, 3, 2, 1),
                clause_pivot: None,
                clause_offset: stack!(0, 2, 4, 7, 7),
                clause_scheduled_for_deletion: stack!(true, false, false),
                proof_start: Clause(2),
                proof: stack![
                    ProofStep::Lemma(Clause(2)),
                    ProofStep::Deletion(Clause(0)),
                    ProofStep::Lemma(Clause(3))
                ],
                hashtable: hashtable! {
                    literals!(-1, -2) => Clause(1),
                    literals!(1, 2, 3) => Clause(2)
                }
            }
        );
    }
}
