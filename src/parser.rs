//! DIMACS and DRAT parser

use crate::{
    formula::{Clause, Formula, Lemma, Proof},
    literal::Literal,
    memory::{Offset, TypedArray},
};
use memmap::MmapOptions;
use std::{
    cmp, fmt,
    fmt::{Display, Formatter},
    fs::File,
    io, str,
};

#[derive(Debug, PartialEq, Eq)]
struct Parser {
    pub maxvar: u32,
    pub db: Vec<Literal>,
    pub clause_to_offset: Vec<usize>,
    pub proof_start: Clause,
    pub proof: Vec<Lemma>,
}

#[derive(Debug, PartialEq, Eq)]
struct ParseError {
    line: usize,
    col: usize,
    why: String,
}

pub fn parse_files<'a>(formula_file: &'a str, proof_file: &str) -> (Formula, Proof) {
    let parser = try_parse(formula_file, parse_formula);
    extract_formula_proof(try_parse(proof_file, |input| parse_proof(input, parser)))
}

fn extract_formula_proof(parser: Parser) -> (Formula, Proof) {
    let num_clauses = parser.clause_to_offset.len();
    (
        Formula {
            maxvar: parser.maxvar,
            db: TypedArray::<usize, Literal>::from(parser.db),
            clause_to_offset: TypedArray::from(parser.clause_to_offset),
            clause_active: TypedArray::new(true, num_clauses),
            proof_start: parser.proof_start,
        },
        TypedArray::from(parser.proof),
    )
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

fn show_slice_as_clause(clause: &[Literal]) -> String {
    let mut result = String::new();
    for literal in clause {
        result += &format!("{} ", literal);
    }
    result + "0"
}

fn add_deletion(parser: &mut Parser, literal: Literal, buffer: &mut Vec<Literal>) -> Literal {
    if literal.zero() {
        match find_clause(&buffer[..], &parser) {
            None => warn!(
                "Deleted clause is not present in the formula: {}",
                show_slice_as_clause(&buffer[..])
            ),
            Some(clause) => parser.proof.push(Lemma::Deletion(clause)),
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
    let clause = parser.clause_to_offset.len();
    parser.clause_to_offset.push(parser.db.len());
    Clause(clause)
}

fn add_literal(parser: &mut Parser, literal: Literal) {
    parser.db.push(literal);
}

fn my_add_literal(parser: &mut Parser, literal: Literal) {
    parser.maxvar = cmp::max(parser.maxvar, literal.var().0);
    add_literal(parser, literal);
}

fn add_literal_ascii(parser: &mut Parser, input: &[u8]) -> Literal {
    let literal = Literal::new(convert_ascii::<i32>(input));
    my_add_literal(parser, literal);
    literal
}

named!(formula_header<&[u8], Parser>,
       do_parse!(
           many0!(comment) >>
           tag!("p cnf ") >>
               maxvar: unsigned >> tag!(" ")>>
               _num_clauses: unsigned >>
               (Parser { maxvar: maxvar,
                          db: Vec::new(),
                          clause_to_offset: Vec::new(),
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
fn clauses_equal(parser: &Parser, needle: &[Literal], clause: Clause) -> bool {
    let mut offset = parser.clause_to_offset[clause.as_offset()];
    loop {
        let literal = parser.db[offset];
        if literal == Literal::new(0) {
            break;
        }
        if !(needle.iter().any(|l| *l == literal)) {
            return false;
        }
        offset += 1
    }
    needle.len() == (offset - parser.clause_to_offset[clause.as_offset()])
}

fn find_clause(needle: &[Literal], parser: &Parser) -> Option<Clause> {
    (0..parser.clause_to_offset.len())
        .map(Clause)
        .filter(|c| clauses_equal(parser, needle, *c))
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
                    my_add_literal(&mut parser, literal);
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
    parser.proof_start = Clause(parser.clause_to_offset.len());

    let mut binary = false;

    // copied from drat-trim
    for i in 0..cmp::min(10, input.len()) {
        let c = input[i];
        if (c != 100) && (c != 10) && (c != 13) && (c != 32) && (c != 45) && ((c < 48) || (c > 57))
        {
            binary = true;
        }
    }
    if binary {
        eprintln!("Turning on binary mode.");
        Ok(parse_proof_binary(input, parser))
    } else {
        parse_proof_text(input, parser)
    }
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
                maxvar: 2,
                db: vec_of_literals!(1, 2, 0, -1, -2, 0),
                clause_to_offset: vec!(0, 3),
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
                maxvar: 3,
                db: vec_of_literals!(1, 2, 0, -1, -2, 0, 1, 2, 3, 0),
                clause_to_offset: vec!(0, 3, 6),
                proof_start: Clause(2),
                proof: vec![Lemma::Addition(Clause(2)), Lemma::Deletion(Clause(0))]
            })
        );
    }
}
