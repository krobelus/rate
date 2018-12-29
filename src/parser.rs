//! DIMACS and DRAT parser

use nom::{call, do_parse, error_position, many0, named, tag, take_while};

use crate::{
    clause::{Clause, ClauseCopy, ProofStep},
    literal::{Literal, Variable},
    memory::Offset,
};
#[cfg(feature = "flame_it")]
use flamer::flame;
use memmap::MmapOptions;
use multimap::MultiMap;
use std::{
    cmp, fmt,
    fmt::{Display, Formatter},
    fs::File,
    io, str,
};

/// Sorted copy of a clause. We perform the copy to make it possible to reuse an existing
/// implementation of a hash map. Generally collections should own the data the contain, otherwise
/// it gets tricky. If this causes as problem, we might implement the hashing ourselves.
#[derive(Debug, PartialEq, Eq, Hash)]
struct HashableClause {
    clause: Vec<Literal>,
}

impl<'a> HashableClause {
    fn new(literals: &[Literal]) -> HashableClause {
        let mut clause = literals.to_vec();
        clause.sort();
        HashableClause { clause: clause }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct Parser {
    pub maxvar: Variable,
    pub num_clauses: usize,
    pub db: Vec<Literal>,
    pub clause_offset: Vec<usize>,
    clause_scheduled_for_deletion: Vec<bool>,
    pub proof_start: Clause,
    pub proof: Vec<ProofStep>,
    clause_to_id: MultiMap<HashableClause, Clause>,
}

#[derive(Debug, PartialEq, Eq)]
struct ParseError {
    line: usize,
    col: usize,
    why: String,
}

impl Parser {
    pub fn new() -> Parser {
        Parser {
            maxvar: Variable::new(0),
            num_clauses: usize::max_value(),
            db: Vec::new(),
            clause_offset: Vec::new(),
            clause_scheduled_for_deletion: Vec::new(),
            proof_start: Clause(0),
            proof: Vec::new(),
            clause_to_id: MultiMap::new(),
        }
    }
}

#[cfg_attr(feature = "flame_it", flame)]
pub fn parse_files<'a>(formula_file: &str, proof_file: &str) -> Parser {
    let mut parser = Parser::new();
    parse_formula(&mut parser, &read_or_die(formula_file))
        .map(|err| die!("error parsing formula at line {} col {}", err.line, err.col));
    parse_proof(&mut parser, &read_or_die(proof_file))
        .map(|err| die!("error parsing proof at line {} col {}", err.line, err.col));
    parser
}

fn read_or_die(filename: &str) -> Vec<u8> {
    read_file(filename).unwrap_or_else(|err| die!("{}", err))
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
    if literal.is_zero() {
        if buffer.len() == 1 {
            buffer.push(Literal::BOTTOM);
        }
        match find_clause(&buffer[..], &parser) {
            None => warn!(
                "Deleted clause is not present in the formula: {}",
                ClauseCopy::new(Clause(0), &buffer)
            ),
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

fn add_deletion_ascii(parser: &mut Parser, input: &[u8], buffer: &mut Vec<Literal>) -> Literal {
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
        let begin = *parser.clause_offset.last().unwrap_or(&0);
        let mut end = parser.db.len();
        if end - begin == 1 {
            add_literal(parser, Literal::BOTTOM);
            end += 1;
        }
        let clause = HashableClause::new(&parser.db.as_slice()[begin..end]);
        parser
            .clause_to_id
            .insert(clause, Clause(parser.clause_offset.len() - 1));
    } else {
        parser.maxvar = cmp::max(parser.maxvar, literal.var());
        parser.db.push(literal);
    }
}

fn add_literal_ascii<'a, 'r>(parser: &'r mut Parser, input: &[u8]) -> Literal {
    let literal = Literal::new(convert_ascii::<i32>(input));
    add_literal(parser, literal);
    literal
}

named!(
    formula_header<&[u8], ()>,
    do_parse!(
        many0!(comment)
            >> tag!("p cnf ")
            >> _maxvar: unsigned
            >> tag!(" ")
            >> _num_clauses: unsigned
            >> ()));

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

fn find_clause<'a>(needle: &[Literal], parser: &Parser) -> Option<Clause> {
    let clause = HashableClause::new(needle);
    parser.clause_to_id.get_vec(&clause).and_then(|clauses| {
        clauses
            .iter()
            .map(|c| *c)
            .find(|c| !parser.clause_scheduled_for_deletion[c.as_offset()])
    })
}

fn parse_formula<'a>(parser: &'a mut Parser, input: &[u8]) -> Option<ParseError> {
    enum ClauseState {
        InLiteral,
        NotInLiteral,
    }
    let mut line = 0;
    let mut col = 0;

    let result = formula_header(input);
    if result.is_err() {
        return Some(ParseError {
            line: line,
            col: col,
            why: "Failed to parse DIMACS header".to_string(),
        });
    }
    let input = result.ok().unwrap().0;

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
                        start_clause(&mut *parser);
                    }
                    let literal = add_literal_ascii(&mut *parser, &input[start..i]);
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
            add_literal_ascii(parser, &input[start..]);
        }
        _ => (),
    }
    None
}

fn lemma_binary(input: &[u8]) -> (&[u8], char) {
    invariant!(input.len() > 0);
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

fn parse_proof_binary<'a, 'r>(mut parser: &'r mut Parser, mut input: &[u8]) {
    enum LemmaPositionBinary {
        Start,
        Lemma,
        Deletion,
    }

    let mut state = LemmaPositionBinary::Start;
    let mut buffer = Vec::new();
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
                    parser.proof.push(ProofStep::Lemma(clause));
                }
                input
            }
            LemmaPositionBinary::Lemma => match number_binary(input) {
                (input, literal) => {
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

fn parse_proof<'a>(parser: &'a mut Parser, input: &[u8]) -> Option<ParseError> {
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

fn parse_proof_text<'a, 'r>(parser: &'r mut Parser, input: &[u8]) -> Option<ParseError> {
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
    let mut buffer = Vec::new();
    for i in 0..input.len() {
        let c = input[i];
        line += if c == b'\n' { 1 } else { 0 };
        col = if c == b'\n' { 0 } else { col + 1 };
        let error = || Some(ParseError::new(line, col, ""));
        match state {
            LemmaPositionText::Start => match c {
                b'\n' => head = true,
                b' ' => (),
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
                b' ' | b'\n' => {
                    let literal = add_literal_ascii(&mut *parser, &input[start..i]);
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
                    let literal = add_deletion_ascii(parser, &input[start..i], &mut buffer);
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
            add_literal_ascii(parser, &input[start..]);
        }
        LemmaPositionText::DeletionLiteral => {
            add_deletion_ascii(parser, &input[start..], &mut buffer);
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
    macro_rules! vec_of_literals {
        ($($x:expr),*) => (vec!($(Literal::new($x)),*));
    }

    #[allow(unused_macros)]
    macro_rules! multimap(
    { $($key:expr => $value:expr),+ } => {
        {
            let mut m = MultiMap::new();
            $(
                m.insert($key, $value);
            )+
            m
        }
     };
);

    fn sample_formula() -> Parser {
        let mut parser = Parser::new();
        assert!(parse_formula(
            &mut parser,
            r#"c comment
p cnf 2 2
1 2 0
-1 -2 0"#
                .as_bytes(),
        )
        .is_none());
        parser
    }

    #[test]
    fn invalid_formulas() {
        invariant!(parse_formula(&mut Parser::new(), b"p c").is_some());
        invariant!(parse_formula(&mut Parser::new(), b"p cnf 1 1\na").is_some());
    }

    #[test]
    fn valid_formula_and_proof() {
        let mut parser = sample_formula();
        parse_proof(&mut parser, b"1 2 3 0\nd 1 2 0");
        assert_eq!(
            parser.clause_to_id,
            multimap! {
                HashableClause::new(&vec_of_literals!(1, 2)) => Clause(0),
                HashableClause::new(&vec_of_literals!(-1, -2)) => Clause(1),
                HashableClause::new(&vec_of_literals!(1, 2, 3)) => Clause(2)
            }
        );
        assert_eq!(
            parser,
            Parser {
                maxvar: Variable::new(3),
                num_clauses: 4,
                db: vec_of_literals!(1, 2, -1, -2, 1, 2, 3),
                clause_offset: vec!(0, 2, 4, 7, 7),
                clause_scheduled_for_deletion: vec!(true, false, false),
                proof_start: Clause(2),
                proof: vec![
                    ProofStep::Lemma(Clause(2)),
                    ProofStep::Deletion(Clause(0)),
                    ProofStep::Lemma(Clause(3))
                ],
                clause_to_id: multimap! {
                    HashableClause::new(&vec_of_literals!(1, 2)) => Clause(0),
                    HashableClause::new(&vec_of_literals!(-1, -2)) => Clause(1),
                    HashableClause::new(&vec_of_literals!(1, 2, 3)) => Clause(2)
                }
            }
        );
    }
}
