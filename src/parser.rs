//! DIMACS and DRAT parser

use crate::{
    clause::{Clause, ClauseView, Lemma},
    literal::{Literal, Variable},
    memory::Offset,
};
use memmap::MmapOptions;
use std::{
    cmp, fmt,
    fmt::{Display, Formatter},
    fs::File,
    io, str,
};

#[derive(Debug, PartialEq, Eq)]
pub struct Parser {
    pub maxvar: Variable,
    pub db: Vec<Literal>,
    pub clause_offset: Vec<usize>,
    clause_scheduled_for_deletion: Vec<bool>,
    pub proof_start: Clause,
    pub proof: Vec<Lemma>,
}

#[derive(Debug, PartialEq, Eq)]
struct ParseError {
    line: usize,
    col: usize,
    why: String,
}

pub fn parse_files<'a>(formula_file: &'a str, proof_file: &str) -> Parser {
    let parser = try_parse(formula_file, parse_formula);
    try_parse(proof_file, |input| parse_proof(input, parser))
}

fn try_parse<'a, T>(filename: &'a str, parser: impl FnOnce(&[u8]) -> Result<T, ParseError>) -> T {
    let data = read_file(filename).unwrap_or_else(|err| die!("{}", err));
    parser(&data).unwrap_or_else(|err| die!("parse error at line {} col {}", err.line, err.col))
}

fn read_file(filename: &str) -> Result<Vec<u8>, io::Error> {
    let file = File::open(&filename)?;
    let size = file.metadata()?.len();
    Ok(if size == 0 {
        vec![]
    } else {
        unsafe { MmapOptions::new().map(&file) }.unwrap().to_owned()
    })
}

fn convert_ascii<T: str::FromStr>(ascii: &[u8]) -> T
where
    <T as str::FromStr>::Err: fmt::Debug,
{
    unsafe { str::from_utf8_unchecked(ascii) }
        .parse::<T>()
        .unwrap()
}

fn add_deletion(parser: &mut Parser, literal: Literal, buffer: &mut Vec<Literal>) -> Literal {
    if literal.zero() {
        match find_clause(&buffer[..], &parser) {
            None => warn!(
                "Deleted clause is not present in the formula: {}",
                ClauseView::new(Clause(0), &buffer)
            ),
            Some(clause) => {
                parser.clause_scheduled_for_deletion[clause.as_offset()] = true;
                parser.proof.push(Lemma::Deletion(clause))
            }
        }
        buffer.clear();
    } else {
        buffer.push(literal);
    }
    literal
}

fn add_deletion_ascii(parser: &mut Parser, input: &[u8], buffer: &mut Vec<Literal>) -> Literal {
    add_deletion(parser, Literal::new(convert_ascii::<i32>(input)), buffer)
}

fn start_clause(parser: &mut Parser) -> Clause {
    let clause = parser.clause_offset.len();
    parser.clause_offset.push(parser.db.len());
    parser.clause_scheduled_for_deletion.push(false);
    Clause(clause)
}

fn add_literal(parser: &mut Parser, literal: Literal) {
    if literal != Literal::new(0) {
        parser.maxvar = cmp::max(parser.maxvar, literal.var());
        parser.db.push(literal);
    }
}

fn add_literal_ascii(parser: &mut Parser, input: &[u8]) -> Literal {
    let literal = Literal::new(convert_ascii::<i32>(input));
    add_literal(parser, literal);
    literal
}

named!(formula_header<&[u8], Parser>,
       do_parse!(
           many0!(comment) >>
           tag!("p cnf ") >>
               maxvar: unsigned >> tag!(" ")>>
               _num_clauses: unsigned >>
               (Parser { maxvar: Variable::new(maxvar),
                          db: Vec::new(),
                          clause_offset: Vec::new(),
                          clause_scheduled_for_deletion: Vec::new(),
                          proof_start: Clause(0),
                          proof: Vec::new(),
               })
       ));

named!(comment<&[u8], ()>,
    do_parse!(
        tag!(b"c") >>
        take_while!(|c| c != b'\n') >>
        tag!(b"\n") >>
            (())
    )
);

named!(unsigned<&[u8], u32>,
       do_parse!(
           ascii: take_while!(|b| nom::is_digit(b as u8))
               >> (convert_ascii::<u32>(ascii))
       )
);

// TODO this assumes that there are no duplicates
fn clauses_equal(needle: &[Literal], clause: ClauseView) -> bool {
    clause
        .iter()
        .all(|literal| needle.iter().any(|l| l == literal))
        && needle.len() == clause.len()
}

fn find_clause(needle: &[Literal], parser: &Parser) -> Option<Clause> {
    let offset = &parser.clause_offset;
    (0..offset.len())
        .map(Clause)
        .filter(|c| !parser.clause_scheduled_for_deletion[c.as_offset()])
        .filter(|&c| {
            clauses_equal(
                needle,
                ClauseView::new(
                    c,
                    &parser.db[offset[c.0]..if c.0 == offset.len() - 1 {
                        parser.db.len()
                    } else {
                        offset[c.0 + 1]
                    }],
                ),
            )
        })
        .next()
}

enum ClauseState {
    InLiteral,
    NotInLiteral,
}

fn parse_formula(input: &[u8]) -> Result<Parser, ParseError> {
    let mut line = 0;
    let mut col = 0;

    let (rest, mut parser) = formula_header(input).map_err(|_| ParseError {
        line: line,
        col: col,
        why: "Failed to parse DIMACS header".to_string(),
    })?;
    let mut head = true;
    let mut state = ClauseState::NotInLiteral;
    let mut start = 0;
    for i in 0..rest.len() {
        let c = rest[i];
        line += if c == b'\n' { 1 } else { 0 };
        col = if c == b'\n' { 0 } else { col + 1 };
        let error = || Err(ParseError::new(line, col, ""));
        match state {
            ClauseState::NotInLiteral => match c {
                b' ' | b'\n' => (),
                b'-' | b'0'..=b'9' => {
                    state = ClauseState::InLiteral;
                    start = i;
                }
                _ => return error(),
            },
            ClauseState::InLiteral => match c {
                b'-' | b'0'..=b'9' => (),
                b' ' | b'\n' => {
                    if head {
                        start_clause(&mut parser);
                    }
                    let literal = add_literal_ascii(&mut parser, &rest[start..i]);
                    head = literal == Literal::new(0);
                    state = ClauseState::NotInLiteral;
                }
                _ => return error(),
            },
        }
    }
    // handle missing newline at EOF
    match state {
        ClauseState::InLiteral => {
            add_literal_ascii(&mut parser, &rest[start..]);
        }
        _ => (),
    }
    Ok(parser)
}

fn lemma_binary(input: &[u8]) -> (&[u8], char) {
    ensure!(input.len() > 0);
    (&input[1..], input[0] as char)
}

fn number_binary(input: &[u8]) -> (&[u8], Literal) {
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
    (&input[i..], Literal::from_raw(result))
}

enum LemmaPositionBinary {
    Start,
    Addition,
    Deletion,
}

fn parse_proof_binary(mut input: &[u8], mut parser: Parser) -> Parser {
    let mut state = LemmaPositionBinary::Start;
    let mut buffer = Vec::new();
    while input.len() > 0 {
        input = match state {
            LemmaPositionBinary::Start => {
                let (input, addition_or_deletion) = lemma_binary(input);
                if addition_or_deletion == 'd' {
                    state = LemmaPositionBinary::Deletion;
                } else {
                    ensure!(addition_or_deletion == 'a');
                    state = LemmaPositionBinary::Addition;
                    let clause = start_clause(&mut parser);
                    parser.proof.push(Lemma::Addition(clause));
                }
                input
            }
            LemmaPositionBinary::Addition => match number_binary(input) {
                (input, literal) => {
                    add_literal(&mut parser, literal);
                    if literal == Literal::new(0) {
                        state = LemmaPositionBinary::Start;
                    }
                    input
                }
            },
            LemmaPositionBinary::Deletion => match number_binary(input) {
                (input, literal) => {
                    add_deletion(&mut parser, literal, &mut buffer);
                    if literal == Literal::new(0) {
                        state = LemmaPositionBinary::Start;
                    }
                    input
                }
            },
        }
    }
    parser
}

#[derive(Debug)]
enum LemmaPositionText {
    Start,
    LemmaLiteral,
    PostLemmaLiteral,
    Deletion,
    DeletionLiteral,
}

fn parse_proof(input: &[u8], mut parser: Parser) -> Result<Parser, ParseError> {
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
        eprintln!("Turning on binary mode.");
        Ok(parse_proof_binary(input, parser))
    } else {
        parse_proof_text(input, parser)
    };
    result.map(|mut parser| {
        parser.clause_offset.push(parser.db.len());
        parser
    })
}

fn parse_proof_text(input: &[u8], mut parser: Parser) -> Result<Parser, ParseError> {
    let mut state = LemmaPositionText::Start;
    let mut head = true;
    let mut start = 0;
    let mut line = 0;
    let mut col = 0;
    let mut buffer = Vec::new();
    for i in 0..input.len() {
        let c = input[i];
        line += if c == b'\n' { 1 } else { 0 };
        col = if c == b'\n' { 0 } else { col + 1 };
        let error = || Err(ParseError::new(line, col, ""));
        match state {
            LemmaPositionText::Start => match c {
                b'\n' => head = true,
                b' ' => (),
                b'd' => state = LemmaPositionText::Deletion,
                b'-' | b'0'..=b'9' => {
                    if head {
                        let clause = start_clause(&mut parser);
                        parser.proof.push(Lemma::Addition(clause));
                    }
                    state = LemmaPositionText::LemmaLiteral;
                    start = i;
                }
                _ => return error(),
            },
            LemmaPositionText::LemmaLiteral => match c {
                b' ' | b'\n' => {
                    let literal = add_literal_ascii(&mut parser, &input[start..i]);
                    head = literal == Literal::new(0);
                    state = if literal == Literal::new(0) {
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
                b' ' => (),
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
                b' ' | b'\n' => {
                    let literal = add_deletion_ascii(&mut parser, &input[start..i], &mut buffer);
                    state = if literal.zero() {
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
            add_literal_ascii(&mut parser, &input[start..]);
        }
        LemmaPositionText::DeletionLiteral => {
            add_deletion_ascii(&mut parser, &input[start..], &mut buffer);
        }
        _ => (),
    }
    Ok(parser)
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
    macro_rules! vec_of_literals {
        ($($x:expr),*) => (vec!($(Literal::new($x)),*));
    }

    fn sample_formula() -> Parser {
        parse_formula(
            r#"c comment
p cnf 2 2
1 2 0
-1 -2 0"#
                .as_bytes(),
        )
        .unwrap()
    }

    #[test]
    fn valid_formula() {
        assert_eq!(
            sample_formula(),
            Parser {
                maxvar: Variable::new(2),
                db: vec_of_literals!(1, 2, -1, -2),
                clause_offset: vec!(0, 2),
                clause_scheduled_for_deletion: vec!(false, false),
                proof_start: Clause(0),
                proof: Vec::new(),
            }
        );
    }

    #[test]
    fn invalid_formulas() {
        ensure!(parse_formula(b"p c").is_err());
        ensure!(parse_formula(b"p cnf 1 1\na").is_err());
    }

    #[test]
    fn valid_proof() {
        assert_eq!(
            parse_proof(b"1 2 3 0\nd 1 2 0", sample_formula()),
            Ok(Parser {
                maxvar: Variable::new(3),
                db: vec_of_literals!(1, 2, -1, -2, 1, 2, 3),
                clause_offset: vec!(0, 2, 4, 7),
                clause_scheduled_for_deletion: vec!(true, false, false),
                proof_start: Clause(2),
                proof: vec![Lemma::Addition(Clause(2)), Lemma::Deletion(Clause(0))]
            })
        );
    }
}
