//! DIMACS and DRAT/DPR parser

use crate::{
    clause::{Clause, ProofStep},
    clausedatabase::{ClauseDatabase, WitnessDatabase},
    hashtable::{FixedSizeHashTable, HashTable},
    input::{Input},
    literal::{Literal, Variable},
    memory::{format_memory_usage, HeapSpace, Vector},
    output::{print_key_value, unreachable, Timer},
};
use std::{
    cmp,
    convert::TryInto,
    fmt,
    fs::File,
    io::{BufWriter, Result},
    panic,
    ptr::NonNull,
};

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum ProofSyntax {
    Dimacs,
    Rup,
    Drat,
    Dpr,
    // Dsr,
}

#[allow(dead_code)]
impl ProofSyntax {
    pub fn parse(s: &str) -> Option<ProofSyntax> {
        match s {
            "rup" => Some(ProofSyntax::Rup),
            "drat" => Some(ProofSyntax::Drat),
            "dpr" => Some(ProofSyntax::Dpr),
            // "dsr" => Some(ProofSyntax::Dsr),
            _ => None,
        }
    }
    pub fn has_header(self) -> bool {
        self == ProofSyntax::Dimacs
    }
    pub fn has_deletion(self) -> bool {
        match self {
            ProofSyntax::Dimacs | ProofSyntax::Rup => false,
            _ => true,
        }
    }
    pub fn has_repetition_witness(self) -> bool {
        self == ProofSyntax::Dpr
    }
    // pub fn has_pair_witness(self) -> bool {
    //     self == ProofSyntax::Dsr
    // }
}

impl fmt::Display for ProofSyntax {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}",
            match self {
                ProofSyntax::Dimacs => "DIMACS",
                ProofSyntax::Rup => "RUP",
                ProofSyntax::Drat => "DRAT",
                ProofSyntax::Dpr => "DPR",
                // ProofSyntax::Dsr,
            }
        )
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum BinaryMode {
    Text,
    Binary,
    DratTrim,
    Prefix,
}
impl BinaryMode {
    pub fn parse(s: &str) -> Option<BinaryMode> {
        match s {
            "binary" => Some(BinaryMode::Binary),
            "text" => Some(BinaryMode::Text),
            "drat-trim" => Some(BinaryMode::DratTrim),
            "prefix" => Some(BinaryMode::Prefix),
            _ => None,
        }
    }
    pub fn detect(&self, filename: &str) -> bool {
        match self {
            BinaryMode::Binary => true,
            BinaryMode::Text => false,
            BinaryMode::DratTrim => {
                let vec = Input::peek_file(filename, 10);
                for &c in vec.iter() {
                    if Self::drat_trim_heuristic(c) {
                        return true;
                    }
                }
                false
            }
            BinaryMode::Prefix => {
                let vec = Input::peek_file(filename, 1);
                vec.get(0) == Some(&0x80)
            }
        }
    }
    fn drat_trim_heuristic(c: u8) -> bool {
        (c != 100) && (c != 10) && (c != 13) && (c != 32) && (c != 45) && ((c < 48) || (c > 57))
    }
}


/// The static singleton instance of the clause database.
///
/// It needs to be static so that hash and equality functions can access it.
pub static mut CLAUSE_DATABASE: NonNull<ClauseDatabase> = NonNull::dangling();

/// Static singleton instance of the witness database.
///
/// This should be made non-static.
pub static mut WITNESS_DATABASE: NonNull<WitnessDatabase> = NonNull::dangling();

/// Wrapper to access the clause database safely in a single-threaded context.
pub fn clause_db() -> &'static mut ClauseDatabase {
    unsafe { CLAUSE_DATABASE.as_mut() }
}
/// Wrapper to access the witness database safely in a single-threaded context.
pub fn witness_db() -> &'static mut WitnessDatabase {
    unsafe { WITNESS_DATABASE.as_mut() }
}

/// Release the memory by both clause and witness database.
pub fn free_clause_database() {
    unsafe {
        Box::from_raw(CLAUSE_DATABASE.as_ptr());
        Box::from_raw(WITNESS_DATABASE.as_ptr());
    }
}

/// CNF and DRAT/DPR parser.
#[derive(Debug, PartialEq)]
pub struct Parser {
    /// The redundancy property identifying the proof format.
    pub proof_format: ProofSyntax,
    /// The highest variable parsed so far
    pub maxvar: Variable,
    /// For RAT, the pivot (first literal) for each clause
    ///
    /// It is necessary to store this because the clauses will be sorted
    /// (and watches will be shuffled).
    pub clause_pivot: Vector<Literal>,
    /// The first clause that is part of the proof (and not the input formula)
    pub proof_start: Clause,
    /// The proof steps
    pub proof: Vector<ProofStep>,
    /// How many proof steps we want to parse
    pub max_proof_steps: Option<usize>,
    /// Whether to insert an extra empty clause at the end
    pub no_terminating_empty_clause: bool,
    /// Print diagnostics and timing information
    pub verbose: bool,
}

impl Parser {
    /// Create a new parser.
    ///
    /// *Note*: this allocates the static clause and witness databases, so this should only be called once.
    pub fn new(proof_format: ProofSyntax) -> Parser {
        unsafe {
            CLAUSE_DATABASE =
                NonNull::new_unchecked(Box::into_raw(Box::new(ClauseDatabase::new())));
            WITNESS_DATABASE =
                NonNull::new_unchecked(Box::into_raw(Box::new(WitnessDatabase::new())));
        }
        Parser {
            proof_format,
            maxvar: Variable::new(0),
            clause_pivot: Vector::new(),
            proof_start: Clause::new(0),
            proof: Vector::new(),
            max_proof_steps: None,
            no_terminating_empty_clause: false,
            verbose: true,
        }
    }
    /// Returns true if we are parsing a (D)PR proof.
    pub fn is_pr(&self) -> bool {
        self.proof_format == ProofSyntax::Dpr
    }
}

/// Parse a formula and a proof file.
pub fn parse_files(
    formula_file: &str,
    proof_file: &str,
    proof_format: ProofSyntax,
    binary_mode: BinaryMode,
    no_terminating_empty_clause: bool,
    memory_usage_breakdown: bool,
) -> Parser {
    let mut parser = Parser::new(proof_format);
    parser.no_terminating_empty_clause = no_terminating_empty_clause;
    let mut clause_ids = FixedSizeHashTable::new();
    run_parser(&mut parser, formula_file, proof_file, binary_mode, &mut clause_ids);
    if memory_usage_breakdown {
        print_memory_usage(&parser, &clause_ids);
    }
    parser
}

/// Print the memory usage of a parser (useful after parsing).
fn print_memory_usage(parser: &Parser, clause_ids: &impl HashTable) {
    let usages = vec![
        ("db", clause_db().heap_space()),
        ("hash-table", clause_ids.heap_space()),
        ("proof", parser.proof.heap_space()),
        ("rest", parser.clause_pivot.heap_space()),
    ];
    let total = usages.iter().map(|pair| pair.1).sum();
    print_key_value("parser memory (MB)", format_memory_usage(total));
    for (name, usage) in usages {
        print_key_value(&format!("memory-{}", name), format_memory_usage(usage));
    }
}

/// Parse a formula and a proof file using a given hash table.
pub fn run_parser(
    mut parser: &mut Parser,
    formula: &str,
    proof_file: &str,
    binary_mode: BinaryMode,
    clause_ids: &mut impl HashTable,
) {
    if parser.verbose {
        comment!("proof format: {}", parser.proof_format);
    }

    {
        let mut _timer = Timer::name("parsing formula");
        if !parser.verbose {
            _timer.disabled = true;
        }
        let input = Input::from_file(formula, false);
        parse_formula(
            &mut parser,
            clause_ids,
            input,
        )
        .unwrap_or_else(|err| die!("failed to parse formula: {}", err));
    }

    {
        let mut _timer = Timer::name("parsing proof");
        let binary = binary_mode.detect(proof_file);
        if !parser.verbose {
            _timer.disabled = true;
        }
        if binary && parser.verbose {
            comment!("binary proof mode");
        }
        let input = Input::from_file(proof_file, binary);
        parse_proof(
            &mut parser,
            clause_ids,
            input,
            binary,
        )
        .unwrap_or_else(|err| die!("failed to parse proof: {}", err));
    }

    clause_db().shrink_to_fit();
    witness_db().shrink_to_fit();
    parser.clause_pivot.shrink_to_fit();
    parser.proof.shrink_to_fit();
}

/// Open a file for reading.
/// # Panics
/// Panics on error.
pub fn open_file(filename: &str) -> File {
    File::open(filename).unwrap_or_else(|err| die!("cannot open file: {}", err))
}

/// Open a file for writing.
/// # Panics
/// Panics on error.
pub fn open_file_for_writing(filename: &str) -> BufWriter<File> {
    BufWriter::new(
        File::create(filename).unwrap_or_else(|err| die!("cannot open file for writing: {}", err)),
    )
}

/// Unwraps a result, panicking on error.
pub fn panic_on_error<T>(result: Result<T>) -> T {
    result.unwrap_or_else(|error| die!("{}", error))
}



/// Add a deletion to the proof.
///
/// Looks up the last parsed clause in the hash table and adds the deletion upon success.
fn add_deletion(parser: &mut Parser, clause_ids: &mut impl HashTable) {
    let clause = clause_db().last_clause();
    match clause_ids.find_equal_clause(clause, /*delete=*/ true) {
        None => {
            if parser.verbose {
                warn!(
                    "Deleted clause is not present in the formula: {}",
                    clause_db().clause_to_string(clause)
                );
            }
            // Need this for sickcheck
            parser
                .proof
                .push(ProofStep::deletion(Clause::DOES_NOT_EXIST))
        }
        Some(clause) => parser.proof.push(ProofStep::deletion(clause)),
    }
    clause_db().pop_clause();
}

pub fn parse_literal_text(input: &mut Input) -> Result<Literal> {
    match input.peek() {
        // None => return Err(input.error(EOF)),
        None => Ok(Literal::new(0)) ,        // todo: make this optional
        Some(_) => {
            let literal = Literal::new(input.parse_dec32()?);
            input.skip_some_whitespace()?;
            Ok(literal)
        }
    }
}

/// Parse a literal from a compressed proof.
pub fn parse_literal_binary(input: &mut Input) -> Result<Literal> {
    if input.peek() == None {           // todo: make this optional
        Ok(Literal::new(0))
    } else {
        let vbe = input.parse_vbe32()?;
        if vbe == 1 {
            Err(input.error(Input::OVERFLOW))
        } else {
            Ok(Literal::from_raw(vbe))
        }
    }
}

/// Parse a DIMACS header.
fn parse_formula_header(input: &mut Input) -> Result<(i32, u64)> {
    while Some(b'c') == input.peek() {
        input.skip_up_to(b'\n');
    }
    for &expected in b"p cnf" {
        if input.peek().map_or(true, |c| c != expected) {
            return Err(input.error(Input::P_CNF));
        }
        input.next();
    }
    input.skip_some_whitespace()?;
    let maxvar = input.parse_dec32()?;
    input.skip_some_whitespace()?;
    let num_clauses: u64 = input.parse_dec64()?
        .try_into().map_err(|_| input.error(Input::P_CNF))?;
    input.skip_some_whitespace()?;
    Ok((maxvar, num_clauses))
}

enum ParsedClause {
    Clause(Literal),
    Repetition(Literal),
}

// todo: eventually, parse_clause and parse_dpr_witness should be unified.
// That will require unifying the underlying types of ClauseDatabase and WitnessDatabase...

fn parse_clause(
    parser: &mut Parser,
    input: &mut Input,
    repetition: bool,
    binary: bool,
) -> Result<ParsedClause> {
    let mut first : bool = true ;
    let mut initial : Literal = Literal::NEVER_READ ;   // todo: This should be changed to the -0 literal.
                                                        // When doing that, make sure to take into account the case for the empty clause!
    loop {
        let literal = if binary {
            parse_literal_binary(input)?
        } else {
            parse_literal_text(input)?
        };
        parser.maxvar = cmp::max(parser.maxvar, literal.variable());
        if literal.is_zero() {
            return Ok(ParsedClause::Clause(initial)) ;
        } else if repetition && literal == initial {
            return Ok(ParsedClause::Repetition(literal)) ;
        } else if first {
            first = false ;
            initial = literal ;
        }
        clause_db().push_literal(literal);
    }
}

fn parse_dpr_witness(
    parser: &mut Parser,
    input: &mut Input,
    binary: bool,
) -> Result<()> {
    loop {
        let literal = if binary {
            parse_literal_binary(input)?
        } else {
            parse_literal_text(input)?
        };
        parser.maxvar = cmp::max(parser.maxvar, literal.variable());
        if literal.is_zero() {
            return Ok(()) ;
        }
        clause_db().push_literal(literal);
    }
}

/// Parse a DIMACS formula.
pub fn parse_formula(
    parser: &mut Parser,
    clause_ids: &mut impl HashTable,
    mut input: Input,
) -> Result<()> {
    parse_formula_header(&mut input)?;
    while let Some(c) = input.peek() {
        if c == b'c' {
            input.skip_up_to(b'\n');
            continue;
        }
        let clause = clause_db().open_clause();
        match parse_clause(parser, &mut input, false, false)? {
            ParsedClause::Clause(_) => {
                clause_db().push_literal(Literal::new(0));
                if parser.is_pr() {
                    let witness = witness_db().open_witness();
                    invariant!(clause == witness);
                    witness_db().push_literal(Literal::new(0));
                }
                parser.clause_pivot.push(Literal::NEVER_READ);
                clause_ids.add_clause(clause_db().last_clause());
            } ,
            _ => unreachable() ,
        }
    }
    Ok(())
}

/// Parse a proof given the hashtable.
fn parse_proof(
    parser: &mut Parser,
    clause_ids: &mut impl HashTable,
    mut input: Input,
    binary: bool,
) -> Result<()> {
    parser.proof_start = Clause::new(clause_db().number_of_clauses());
    let mut instructions : usize = parser.max_proof_steps.unwrap_or(std::usize::MAX);       // usize::MAX will hopefully be enough here until we're all retired
    if !binary {
        input.skip_any_whitespace();
    }
    while instructions != 0usize && input.peek() != None {
        parse_instruction(parser, clause_ids, &mut input, binary)?;
        instructions -= 1;
    }
    if !parser.no_terminating_empty_clause {        // todo: check if this is really necessary
        let clause = clause_db().open_clause();
        clause_db().push_literal(Literal::new(0));
        if parser.is_pr() {
            witness_db().open_witness();
            witness_db().push_literal(Literal::new(0));
        }
        parser.proof.push(ProofStep::lemma(clause));
        clause_ids.add_clause(clause_db().last_clause());
    }
    Ok(())
}

enum ParsedInstructionKind {
    Introduction,
    Deletion,
}

impl ParsedInstructionKind {
    fn lookahead(input: &mut Input, binary: bool) -> Result<ParsedInstructionKind> {
        if binary {
            match input.peek() {
                Some(0x61) => {
                    input.next();
                    Ok(ParsedInstructionKind::Introduction)
                }
                Some(0x64) => {
                    input.next();
                    Ok(ParsedInstructionKind::Deletion)
                }
                _ => Err(input.error(Input::DRAT)),
            }
        } else {
            match input.peek() {
                Some(b'd') => {
                    input.next();
                    input.skip_some_whitespace()?;
                    Ok(ParsedInstructionKind::Deletion)
                }
                Some(c) if Input::is_digit_or_dash(c) => Ok(ParsedInstructionKind::Introduction),
                _ => Err(input.error(Input::DRAT)),
            }
        }
    }
}

/// Parse a single proof step
pub fn parse_instruction(
    parser: &mut Parser,
    clause_ids: &mut impl HashTable,
    input: &mut Input,
    binary: bool,
) -> Result<()> {
    match ParsedInstructionKind::lookahead(input, binary)? {
        ParsedInstructionKind::Introduction => {
            let clause = clause_db().open_clause();
            if parser.is_pr() {
                let witness = witness_db().open_witness();
                invariant!(clause == witness);
            }
            match parse_clause(parser, input, parser.is_pr(), binary)? {
                ParsedClause::Clause(first) => {
                    parser.clause_pivot.push(first);
                }
                ParsedClause::Repetition(first) => {
                    parser.clause_pivot.push(first);
                    witness_db().push_literal(first);
                    parse_dpr_witness(parser, input, binary)?;
                }
            }
            clause_db().push_literal(Literal::new(0));
            clause_ids.add_clause(clause_db().last_clause());
            parser.proof.push(ProofStep::lemma(clause));
            if parser.is_pr() {
                witness_db().push_literal(Literal::new(0));
            }
        }
        ParsedInstructionKind::Deletion => {
            clause_db().open_clause();
            match parse_clause(parser, input, false, binary)? {
                ParsedClause::Clause(_) => {
                    clause_db().push_literal(Literal::new(0));
                    add_deletion(parser, clause_ids);
                }
                ParsedClause::Repetition(_) => unreachable() ,
            }
        }
    }
    Ok(())
}

/// Print the clause and witness databases, for debugging.
#[allow(dead_code)]
pub fn print_db(have_witnesses: bool) {
    let clause_db = &clause_db();
    let witness_db = &witness_db();
    for clause in Clause::range(0, clause_db.last_clause() + 1) {
        write_to_stdout!(
            "{}{} fields: {:?}\n",
            clause_db.clause_to_string(clause),
            if have_witnesses {
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
        ($($x:expr),*) => (Vector::from_vec(vec!($(Literal::new($x)),*)));
    }

    fn sample_formula(clause_ids: &mut impl HashTable) -> Parser {
        let mut parser = Parser::new(ProofSyntax::Drat);
        parser.proof_format = ProofSyntax::Drat;
        let example = r#"c comment
p cnf 2 2
1 2 0
c comment
-1 -2 0"#;
        assert!(parse_formula(
            &mut parser,
            clause_ids,
            Input::new(Box::new(example.as_bytes().iter().cloned()), false),
        )
        .is_ok());
        parser
    }
    #[test]
    fn valid_formula_and_proof() {
        let mut clause_ids = FixedSizeHashTable::new();
        let mut parser = sample_formula(&mut clause_ids);
        let result = parse_proof(
            &mut parser,
            &mut clause_ids,
            Input::new(Box::new(b"1 2 3 0\nd 1 2 0".into_iter().cloned()), false),
            false,
        );
        assert!(result.is_ok());
        fn lit(x: i32) -> Literal {
            Literal::new(x)
        }
        fn raw(x: u32) -> Literal {
            Literal::from_raw(x)
        }
        assert_eq!(
            clause_db(),
            &ClauseDatabase::from(
                vector!(
                    raw(0),
                    raw(0),
                    lit(1),
                    lit(2),
                    lit(0),
                    raw(1),
                    raw(0),
                    lit(-2),
                    lit(-1),
                    lit(0),
                    raw(2),
                    raw(0),
                    lit(1),
                    lit(2),
                    lit(3),
                    lit(0),
                    raw(3),
                    raw(0),
                    lit(0),
                ),
                vector!(0, 5, 10, 16)
            )
        );
        assert_eq!(witness_db(), &WitnessDatabase::from(vector!(), vector!(0)));
        assert_eq!(
            parser,
            Parser {
                proof_format: ProofSyntax::Drat,
                maxvar: Variable::new(3),
                clause_pivot: vector!(Literal::NEVER_READ, Literal::NEVER_READ, Literal::new(1)),
                proof_start: Clause::new(2),
                proof: vector!(
                    ProofStep::lemma(Clause::new(2)),
                    ProofStep::deletion(Clause::new(0)),
                    ProofStep::lemma(Clause::new(3)),
                ),
                max_proof_steps: None,
                no_terminating_empty_clause: false,
                verbose: true,
            }
        );
    }
}

impl HeapSpace for Parser {
    fn heap_space(&self) -> usize {
        clause_db().heap_space()
            + witness_db().heap_space()
            + self.clause_pivot.heap_space()
            + self.proof.heap_space()
    }
}

