//! DIMACS and DRAT parser

use crate::{
    clause::{Clause, ProofStep},
    clausedatabase::{ClauseDatabase, WitnessDatabase},
    config::{unreachable, RedundancyProperty},
    literal::{Literal, Variable},
    memory::{format_memory_usage, HeapSpace, Offset, SmallStack, Stack},
    output::{self, Timer},
};
use std::{
    cmp,
    collections::HashMap,
    convert::TryInto,
    fmt::{self, Display, Formatter},
    fs::File,
    hash::{Hash, Hasher},
    io::{self, Read},
    iter::Peekable,
    panic,
    ptr::NonNull,
    slice,
};

// This needs to be static so that hash and equality functions can access it.
pub static mut CLAUSE_DATABASE: NonNull<ClauseDatabase> = NonNull::dangling();
pub static mut WITNESS_DATABASE: NonNull<WitnessDatabase> = NonNull::dangling();

pub fn clause_db() -> &'static mut ClauseDatabase {
    unsafe { CLAUSE_DATABASE.as_mut() }
}
pub fn witness_db() -> &'static mut WitnessDatabase {
    unsafe { WITNESS_DATABASE.as_mut() }
}

pub fn free_clause_database() {
    unsafe {
        Box::from_raw(CLAUSE_DATABASE.as_ptr());
        Box::from_raw(WITNESS_DATABASE.as_ptr());
    }
}

#[derive(Debug, PartialEq)]
pub struct Parser {
    pub redundancy_property: RedundancyProperty,
    pub maxvar: Variable,
    pub clause_pivot: Stack<Literal>,
    pub proof_start: Clause,
    pub proof: Stack<ProofStep>,
    pub max_proof_steps: Option<usize>,
    pub no_terminating_empty_clause: bool,
    pub verbose: bool,
}

impl Parser {
    pub fn new() -> Parser {
        unsafe {
            CLAUSE_DATABASE =
                NonNull::new_unchecked(Box::into_raw(Box::new(ClauseDatabase::new())));
            WITNESS_DATABASE =
                NonNull::new_unchecked(Box::into_raw(Box::new(WitnessDatabase::new())));
        }
        assert!(
            clause_db().is_empty(),
            "Only one parser can be active at any time."
        );
        clause_db().clear();
        witness_db().clear();
        clause_db().initialize();
        Parser {
            redundancy_property: RedundancyProperty::RAT,
            maxvar: Variable::new(0),
            clause_pivot: Stack::new(),
            proof_start: Clause::new(0),
            proof: Stack::new(),
            max_proof_steps: None,
            no_terminating_empty_clause: false,
            verbose: true,
        }
    }
    pub fn is_pr(&self) -> bool {
        self.redundancy_property == RedundancyProperty::PR
    }
}

pub trait HashTable {
    fn add_clause(&mut self, clause: Clause);
    fn find_equal_clause(&mut self, needle: Clause, delete: bool) -> Option<Clause>;
    #[allow(dead_code)]
    fn clause_is_active(&self, needle: Clause) -> bool;
    #[allow(dead_code)]
    fn delete_clause(&mut self, needle: Clause) -> bool;
}

pub struct FixedSizeHashTable(Stack<Stack<Clause>>);

fn bucket_index(clause: &[Literal]) -> usize {
    clause_hash(clause) % FixedSizeHashTable::SIZE
}

impl FixedSizeHashTable {
    const SIZE: usize = 2 * 1024 * 1024;
    const BUCKET_INITIAL_SIZE: u16 = 4;
    #[allow(clippy::new_without_default)]
    pub fn new() -> FixedSizeHashTable {
        FixedSizeHashTable(Stack::from_vec(vec![
            Stack::with_capacity(
                FixedSizeHashTable::BUCKET_INITIAL_SIZE.into()
            );
            FixedSizeHashTable::SIZE
        ]))
    }
}

pub struct FixedSizeHashTableIterator<'a> {
    buckets: slice::Iter<'a, Stack<Clause>>,
    bucket: slice::Iter<'a, Clause>,
}

impl<'a> Iterator for FixedSizeHashTableIterator<'a> {
    type Item = &'a Clause;
    fn next(&mut self) -> Option<Self::Item> {
        self.bucket.next().or_else(|| {
            self.buckets.next().and_then(|next_bucket| {
                self.bucket = next_bucket.iter();
                self.bucket.next()
            })
        })
    }
}

impl<'a> IntoIterator for &'a FixedSizeHashTable {
    type Item = &'a Clause;
    type IntoIter = FixedSizeHashTableIterator<'a>;
    fn into_iter(self) -> Self::IntoIter {
        FixedSizeHashTableIterator {
            buckets: self.0.iter(),
            bucket: self.0[0].iter(),
        }
    }
}

impl HashTable for FixedSizeHashTable {
    fn add_clause(&mut self, clause: Clause) {
        self.0[bucket_index(clause_db().clause(clause))].push(clause);
    }
    fn find_equal_clause(&mut self, needle: Clause, delete: bool) -> Option<Clause> {
        let bucket = &mut self.0[bucket_index(clause_db().clause(needle))];
        for offset in 0..bucket.len() {
            let clause = bucket[offset];
            if clause_db().clause(needle) == clause_db().clause(clause) {
                if delete {
                    bucket.swap_remove(offset);
                }
                return Some(clause);
            }
        }
        None
    }
    fn clause_is_active(&self, needle: Clause) -> bool {
        self.0[bucket_index(clause_db().clause(needle))]
            .iter()
            .any(|&clause| needle == clause)
    }
    fn delete_clause(&mut self, needle: Clause) -> bool {
        self.0[bucket_index(clause_db().clause(needle))]
            .iter()
            .position(|&clause| needle == clause)
            .map(|offset| self.0[bucket_index(clause_db().clause(needle))].swap_remove(offset))
            .is_some()
    }
}

impl HeapSpace for FixedSizeHashTable {
    fn heap_space(&self) -> usize {
        self.0.heap_space()
    }
}

pub struct DynamicHashTable(HashMap<ClauseHashEq, SmallStack<Clause>>);

impl DynamicHashTable {
    pub fn new() -> DynamicHashTable {
        DynamicHashTable(HashMap::new())
    }
}
impl HashTable for DynamicHashTable {
    fn add_clause(&mut self, clause: Clause) {
        let key = ClauseHashEq(clause);
        self.0
            .entry(key)
            .or_insert_with(SmallStack::new)
            .push(clause)
    }
    fn find_equal_clause(&mut self, needle: Clause, delete: bool) -> Option<Clause> {
        self.0
            .get_mut(&ClauseHashEq(needle))
            .and_then(|equal_clauses| {
                let first = equal_clauses.front();
                invariant!(first != Some(needle));
                if delete {
                    equal_clauses.swap_remove(0);
                }
                first
            })
    }
    // these are not optimized but only used in sick-check
    fn clause_is_active(&self, needle: Clause) -> bool {
        self.0
            .get(&ClauseHashEq(needle))
            .map_or(false, |stack| !stack.to_vec().is_empty())
    }
    fn delete_clause(&mut self, needle: Clause) -> bool {
        self.0
            .get_mut(&ClauseHashEq(needle))
            .map_or(false, |equal_clauses| {
                let mut i = 0;
                let mut clauses = equal_clauses.to_vec();
                while clauses[i] != needle {
                    i += 1;
                    invariant!(i < clauses.len());
                }
                clauses.swap_remove(i);
                *equal_clauses = clauses.into_iter().collect();
                true
            })
    }
}

#[derive(Debug, Eq, Clone, Copy)]
pub struct ClauseHashEq(pub Clause);

impl Hash for ClauseHashEq {
    fn hash<H: Hasher>(&self, hasher: &mut H) {
        clause_hash(clause_db().clause(self.0)).hash(hasher);
    }
}

impl PartialEq for ClauseHashEq {
    fn eq(&self, other: &ClauseHashEq) -> bool {
        clause_db().clause(self.0) == clause_db().clause(other.0)
    }
}

pub fn parse_files(
    formula_file: &str,
    proof_file: &str,
    no_terminating_empty_clause: bool,
    memory_usage_breakdown: bool,
) -> Parser {
    let mut parser = Parser::new();
    parser.no_terminating_empty_clause = no_terminating_empty_clause;
    let mut clause_ids = FixedSizeHashTable::new();
    // let mut clause_ids = DynamicHashTable::new();
    run_parser(&mut parser, Some(formula_file), proof_file, &mut clause_ids);
    if memory_usage_breakdown {
        print_memory_usage(&parser, &clause_ids);
    }
    parser
}

fn print_memory_usage(parser: &Parser, clause_ids: &impl HashTable) {
    let usages = vec![
        ("db", clause_db().heap_space()),
        ("hash-table", clause_ids.heap_space()),
        ("proof", parser.proof.heap_space()),
        ("rest", parser.clause_pivot.heap_space()),
    ];
    let total = usages.iter().map(|pair| pair.1).sum();
    output::value("parser memory (MB)", format_memory_usage(total));
    for (name, usage) in usages {
        output::value(&format!("memory-{}", name), format_memory_usage(usage));
    }
}

pub fn run_parser_on_formula(
    mut parser: &mut Parser,
    formula: Option<&str>,
    proof_file: &str,
    clause_ids: &mut impl HashTable,
) {
    parser.redundancy_property = proof_format_by_extension(&proof_file);
    if parser.verbose {
        comment!("mode: {}", parser.redundancy_property);
    }
    if parser.redundancy_property != RedundancyProperty::RAT {
        witness_db().initialize();
    }
    if let Some(formula_file) = formula {
        let mut _timer = Timer::name("parsing formula");
        if !parser.verbose {
            _timer.disabled = true;
        }
        let formula_input = read_file(formula_file);
        parse_formula(
            &mut parser,
            clause_ids,
            SimpleInput::new(Box::new(formula_input), false),
        )
        .unwrap_or_else(|err| die!("error parsing formula at line {}: {}", err.line, err.why));
    }
}

pub fn run_parser(
    mut parser: &mut Parser,
    formula: Option<&str>,
    proof_file: &str,
    clause_ids: &mut impl HashTable,
) {
    run_parser_on_formula(parser, formula, proof_file, clause_ids);
    let mut _timer = Timer::name("parsing proof");
    if !parser.verbose {
        _timer.disabled = true;
    }
    let binary = is_binary_drat(read_file(proof_file).take(10));
    let proof_input = Box::new(read_file(&proof_file));
    if binary && parser.verbose {
        comment!("binary proof mode");
    }
    parse_proof(
        &mut parser,
        clause_ids,
        SimpleInput::new(proof_input, binary),
        binary,
    )
    .unwrap_or_else(|err| die!("error parsing proof at line {}: {}", err.line, err.why));
    clause_db().shrink_to_fit();
    witness_db().shrink_to_fit();
    parser.clause_pivot.shrink_to_fit();
    parser.proof.shrink_to_fit();
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

impl RedundancyProperty {
    #[allow(dead_code)]
    pub fn file_extension(&self) -> &str {
        match self {
            RedundancyProperty::RAT => "drat",
            RedundancyProperty::PR => "dpr",
        }
    }
}

pub fn read_file(filename: &str) -> Box<dyn Iterator<Item = u8>> {
    let file = open_file(filename);
    let (_basename, compression_format) = compression_format_by_extension(filename);
    if compression_format == "" {
        return Box::new(std::io::BufReader::new(file).bytes().map(panic_on_error));
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

pub fn panic_on_error(result: io::Result<u8>) -> u8 {
    result.unwrap_or_else(|error| die!("read error: {}", error))
}

fn add_literal(
    parser: &mut Parser,
    clause_ids: &mut impl HashTable,
    state: ProofParserState,
    literal: Literal,
) {
    parser.maxvar = cmp::max(parser.maxvar, literal.variable());
    match state {
        ProofParserState::Clause => {
            clause_db().push_literal(literal);
            if parser.is_pr() && literal.is_zero() {
                witness_db().push_literal(literal);
            }
        }
        ProofParserState::Witness => {
            invariant!(parser.is_pr());
            witness_db().push_literal(literal);
            if literal.is_zero() {
                clause_db().push_literal(literal);
            }
        }
        ProofParserState::Deletion => {
            clause_db().push_literal(literal);
            if literal.is_zero() {
                add_deletion(parser, clause_ids);
            }
        }
        ProofParserState::Start => unreachable(),
    }
    match state {
        ProofParserState::Clause | ProofParserState::Witness => {
            if literal.is_zero() {
                clause_ids.add_clause(clause_db().last_clause());
            }
        }
        _ => (),
    }
}

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

fn clause_hash(clause: &[Literal]) -> usize {
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
        requires!((u64::from(value & 0x7f) << (7 * i)) <= u32::max_value().into());
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
    let clause = clause_db().open_clause();
    if parser.is_pr() && state != ProofParserState::Deletion {
        let witness = witness_db().open_witness();
        invariant!(clause == witness);
    }
    clause
}

fn parse_formula(
    parser: &mut Parser,
    clause_ids: &mut impl HashTable,
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
    clause_ids: &mut impl HashTable,
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

pub fn finish_proof(
    parser: &mut Parser,
    clause_ids: &mut impl HashTable,
    state: &mut ProofParserState,
) {
    // patch missing zero terminators
    match *state {
        ProofParserState::Clause | ProofParserState::Deletion | ProofParserState::Witness => {
            add_literal(parser, clause_ids, *state, Literal::new(0));
        }
        ProofParserState::Start => (),
    };
    if !parser.no_terminating_empty_clause {
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
}

fn parse_proof(
    parser: &mut Parser,
    clause_ids: &mut impl HashTable,
    mut input: impl Input,
    binary: bool,
) -> Result<()> {
    parser.proof_start = Clause::new(clause_db().number_of_clauses());
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
    assert_clause_ids_are_within_limits();
    Ok(())
}

fn assert_clause_ids_are_within_limits() {
    let num_clauses = clause_db().number_of_clauses();
    if num_clauses > Clause::MAX_ID + 1 {
        die!(
            "Number of clauses (in formula and proof) {} exceeds maximum number of clauses {}",
            num_clauses,
            Clause::MAX_ID + 1
        );
    }
}

impl Display for ParseError {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "Parse error at line {}:  {}", self.line, self.why)
    }
}

#[allow(dead_code)]
pub fn print_db() {
    let clause_db = &clause_db();
    let witness_db = &witness_db();
    let is_pr = !witness_db.empty();
    for clause in Clause::range(0, clause_db.last_clause() + 1) {
        write_to_stdout!(
            "{}{} fields: {:?}\n",
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

    fn sample_formula(clause_ids: &mut impl HashTable) -> Parser {
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
        let mut clause_ids = FixedSizeHashTable::new();
        let mut parser = sample_formula(&mut clause_ids);
        let result = parse_proof(
            &mut parser,
            &mut clause_ids,
            SimpleInput::new(Box::new(b"1 2 3 0\nd 1 2 0".into_iter().cloned()), false),
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
                stack!(
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
                stack!(0, 5, 10, 16)
            )
        );
        assert_eq!(witness_db(), &WitnessDatabase::from(stack!(), stack!()));
        assert_eq!(
            parser,
            Parser {
                redundancy_property: RedundancyProperty::RAT,
                maxvar: Variable::new(3),
                clause_pivot: stack!(Literal::NEVER_READ, Literal::NEVER_READ, Literal::new(1)),
                proof_start: Clause::new(2),
                proof: stack!(
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
            if !self.binary && c == b'\n' {
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
