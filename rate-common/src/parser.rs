//! DIMACS and DRAT/DPR parser

use crate::{
    clause::{puts_clause, Clause, ProofStep, RedundancyProperty},
    clausedatabase::{ClauseDatabase, ClauseStorage, WitnessDatabase},
    literal::{Literal, Variable},
    memory::{format_memory_usage, HeapSpace, Offset, Vector},
    output::{print_key_value, unreachable, Timer},
};
use std::{
    cmp,
    convert::TryInto,
    fs::File,
    io::{
        self, BufReader, BufWriter, Error, ErrorKind, Read, Result, Seek, SeekFrom, StdinLock,
        Write,
    },
    iter::Peekable,
    panic, slice,
};

/// CNF and DRAT/DPR parser.
#[derive(Debug, PartialEq)]
pub struct Parser {
    /// The redundancy property identifying the proof format.
    pub redundancy_property: RedundancyProperty,
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
    /// Print diagnostics and timing information
    pub verbose: bool,
    /// Clause store
    pub clause_db: ClauseDatabase,
    /// Witness store
    pub witness_db: WitnessDatabase,
}

impl Default for Parser {
    /// Create a new parser.
    ///
    /// *Note*: this allocates the static clause and witness databases, so this should only be called once.
    fn default() -> Parser {
        Parser {
            redundancy_property: RedundancyProperty::RAT,
            maxvar: Variable::new(0),
            clause_pivot: Vector::new(),
            proof_start: Clause::new(0),
            proof: Vector::new(),
            max_proof_steps: None,
            verbose: true,
            clause_db: ClauseDatabase::default(),
            witness_db: WitnessDatabase::default(),
        }
    }
}

impl Parser {
    /// Returns true if we are parsing a (D)PR proof.
    pub fn is_pr(&self) -> bool {
        self.redundancy_property == RedundancyProperty::PR
    }
}

/// A fixed-size hash table that maps clauses (sets of literals) to clause identifiers.
///
/// This should work exactly like the one used in `drat-trim`.
/// Given that we expect the number of clauses in the hash table
/// not to exceed a couple million this should be faster and leaner than
/// [DynamicHashTable](struct.DynamicHashTable.html).
pub struct HashTable(Vector<Vector<Clause>>);

/// Return the hash bucket to which this clause belongs.
fn bucket_index(clause: &[Literal]) -> usize {
    clause_hash(clause) % HashTable::SIZE
}

impl HashTable {
    /// The number of buckets in our hash table (`drat-trim` uses a million)
    const SIZE: usize = 2 * 1024 * 1024;
    /// The initial size of each bucket.
    ///
    /// We could increase this to at least use `malloc_usable_size` (system-dependent).
    const BUCKET_INITIAL_SIZE: u16 = 4;
    /// Allocate the hash table.
    #[allow(clippy::new_without_default)]
    pub fn new() -> HashTable {
        HashTable(Vector::from_vec(vec![
            Vector::with_capacity(
                HashTable::BUCKET_INITIAL_SIZE.into()
            );
            HashTable::SIZE
        ]))
    }
    /// Add a new clause to the hashtable.
    pub fn add_clause(&mut self, clause_db: &ClauseDatabase, clause: Clause) {
        self.0[bucket_index(clause_db.clause(clause))].push(clause);
    }
    /// Find a clause that is equivalent to given clause.
    ///
    /// If delete is true, delete the found clause.
    pub fn find_equal_clause(
        &mut self,
        clause_db: &ClauseDatabase,
        needle: Clause,
        delete: bool,
    ) -> Option<Clause> {
        let bucket = &mut self.0[bucket_index(clause_db.clause(needle))];
        for offset in 0..bucket.len() {
            let clause = bucket[offset];
            if clause_db.clause(needle) == clause_db.clause(clause) {
                if delete {
                    bucket.swap_remove(offset);
                }
                return Some(clause);
            }
        }
        None
    }
    /// Return true if this exact clause is active.
    pub fn clause_is_active(&self, clause_db: &ClauseDatabase, needle: Clause) -> bool {
        self.0[bucket_index(clause_db.clause(needle))]
            .iter()
            .any(|&clause| needle == clause)
    }
    /// Delete this exact clause, return true if that succeeded.
    pub fn delete_clause(&mut self, clause_db: &ClauseDatabase, needle: Clause) -> bool {
        self.0[bucket_index(clause_db.clause(needle))]
            .iter()
            .position(|&clause| needle == clause)
            .map(|offset| self.0[bucket_index(clause_db.clause(needle))].swap_remove(offset))
            .is_some()
    }
}

/// An iterator over the elements of the hash table
pub struct HashTableIterator<'a> {
    /// The iterator over the buckets
    buckets: slice::Iter<'a, Vector<Clause>>,
    /// The iterator over a single bucket
    bucket: slice::Iter<'a, Clause>,
}

impl<'a> Iterator for HashTableIterator<'a> {
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

impl<'a> IntoIterator for &'a HashTable {
    type Item = &'a Clause;
    type IntoIter = HashTableIterator<'a>;
    fn into_iter(self) -> Self::IntoIter {
        HashTableIterator {
            buckets: self.0.iter(),
            bucket: self.0[0].iter(),
        }
    }
}

impl HeapSpace for HashTable {
    fn heap_space(&self) -> usize {
        self.0.heap_space()
    }
}

/// Parse a formula and a proof file.
pub fn parse_files(formula_file: &str, proof_file: &str, memory_usage_breakdown: bool) -> Parser {
    let mut parser = Parser::default();
    let mut clause_ids = HashTable::new();
    run_parser(&mut parser, formula_file, proof_file, &mut clause_ids);
    if memory_usage_breakdown {
        print_memory_usage(&parser, &clause_ids);
    }
    parser
}

/// Print the memory usage of a parser (useful after parsing).
fn print_memory_usage(parser: &Parser, clause_ids: &HashTable) {
    let usages = vec![
        ("db", parser.clause_db.heap_space()),
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

/// Parse a formula.
///
/// This requires the proof file as well to determine the proof format,
/// which is necessary for initialization of the witness database.
pub fn run_parser_on_formula(
    mut parser: &mut Parser,
    formula_file: &str,
    proof_file: &str,
    clause_ids: &mut HashTable,
) {
    parser.redundancy_property = proof_format_by_extension(&proof_file);
    if parser.verbose {
        comment!("mode: {}", parser.redundancy_property);
    }
    let mut _timer = Timer::name("formula-parsing time");
    if !parser.verbose {
        _timer.disabled = true;
    }
    parse_formula(
        &mut parser,
        clause_ids,
        read_compressed_file(formula_file, false),
    )
    .unwrap_or_else(|err| die!("failed to parse formula: {}", err));
}

/// Parse a formula and a proof file using a given hash table.
pub fn run_parser(
    mut parser: &mut Parser,
    formula: &str,
    proof_file: &str,
    clause_ids: &mut HashTable,
) {
    let binary = is_binary_drat(proof_file);
    run_parser_on_formula(parser, formula, proof_file, clause_ids);
    let mut _timer = Timer::name("proof-parsing time");
    if !parser.verbose {
        _timer.disabled = true;
    }
    if binary && parser.verbose {
        comment!("binary proof mode");
    }
    parse_proof(
        &mut parser,
        clause_ids,
        read_compressed_file(proof_file, binary),
        binary,
    )
    .unwrap_or_else(|err| die!("failed to parse proof: {}", err));
    // TODO these two should be (nightly) shrink_to(len() + 1), see rate::close_proof.
    parser.clause_db.shrink_to_fit();
    parser.witness_db.shrink_to_fit();
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
/// Returns a locked stdout if the filename is "-".
/// # Panics
/// Panics on error.
pub fn open_file_for_writing<'a>(filename: &str, stdout: &'a io::Stdout) -> Box<dyn Write + 'a> {
    if filename == "-" {
        Box::new(BufWriter::new(stdout.lock()))
    } else {
        Box::new(BufWriter::new(File::create(filename).unwrap_or_else(
            |err| die!("cannot open file for writing: {}", err),
        )))
    }
}

/// File extension of Zstandard archives.
const ZSTD: &str = ".zst";
/// File extension of Gzip archives.
const GZIP: &str = ".gz";
/// File extension of Bzip2 archives.
const BZIP2: &str = ".bz2";
/// File extension of XZ archives.
const XZ: &str = ".xz";
/// File extension of LZ4 archives.
const LZ4: &str = ".lz4";

/// Strip the compression format off a filename.
///
/// If the filename ends with a known archive extension,
/// return the filname without extension and the extension.
/// Otherwise return the unmodified filename and the empty string.
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

/// Determine the proof format based on the proof filename.
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
    /// Give the canonical file extension for proofs based on this redundancy property.
    pub fn file_extension(&self) -> &str {
        match self {
            RedundancyProperty::RAT => "drat",
            RedundancyProperty::PR => "dpr",
        }
    }
}

/// Return an [Input](struct.Input.html) to read from a possibly compressed file.
///
/// If the file is compressed it is transparently uncompressed.
/// If the filename is "-", returns an [Input](struct.Input.html) reading data from stdin.
/// Argument `binary` is passed on to [Input](struct.Input.html).
pub fn read_compressed_file_or_stdin<'a>(
    filename: &'a str,
    binary: bool,
    stdin: StdinLock<'a>,
) -> Input<'a> {
    match filename {
        "-" => Input::new(Box::new(stdin.bytes().map(panic_on_error)), binary),
        filename => read_compressed_file(filename, binary),
    }
}

/// Return an [Input](struct.Input.html) to read from a possibly compressed file.
///
/// If the file is compressed it is transparently uncompressed.
/// Argument `binary` is passed on to [Input](struct.Input.html).
pub fn read_compressed_file(filename: &str, binary: bool) -> Input {
    let file = open_file(filename);
    Input::new(read_from_compressed_file(file, filename), binary)
}

/// Return an Iterator to read from a possibly compressed file.
///
/// If the file is compressed it is transparently uncompressed.
fn read_from_compressed_file(file: File, filename: &str) -> Box<dyn Iterator<Item = u8>> {
    let (_basename, compression_format) = compression_format_by_extension(filename);
    if compression_format == "" {
        return Box::new(BufReader::new(file).bytes().map(panic_on_error));
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
                .unwrap_or_else(|err| die!("failed to decode LZ4 archive: {}", err));
            Box::new(de.bytes().map(panic_on_error))
        }
        _ => unreachable(),
    }
}

/// Unwraps a result, panicking on error.
pub fn panic_on_error<T>(result: Result<T>) -> T {
    result.unwrap_or_else(|error| die!("{}", error))
}

/// Add a literal to the clause or witness database.
///
/// If the literal is zero, the current clause or witness will be terminated.
fn add_literal(
    parser: &mut Parser,
    clause_ids: &mut HashTable,
    state: ProofParserState,
    literal: Literal,
) {
    parser.maxvar = cmp::max(parser.maxvar, literal.variable());
    match state {
        ProofParserState::Clause => {
            parser.clause_db.push_literal(literal, parser.verbose);
            if parser.is_pr() && literal.is_zero() {
                parser.witness_db.push_literal(literal, parser.verbose);
            }
        }
        ProofParserState::Witness => {
            invariant!(parser.is_pr());
            parser.witness_db.push_literal(literal, parser.verbose);
            if literal.is_zero() {
                parser.clause_db.push_literal(literal, parser.verbose);
            }
        }
        ProofParserState::Deletion => {
            parser.clause_db.push_literal(literal, parser.verbose);
            if literal.is_zero() {
                add_deletion(parser, clause_ids);
            }
        }
        ProofParserState::Start => unreachable(),
    }
    match state {
        ProofParserState::Clause | ProofParserState::Witness => {
            if literal.is_zero() {
                clause_ids.add_clause(&parser.clause_db, parser.clause_db.last_clause());
            }
        }
        _ => (),
    }
}

/// Add a deletion to the proof.
///
/// Looks up the last parsed clause in the hash table and adds the deletion upon success.
fn add_deletion(parser: &mut Parser, clause_ids: &mut HashTable) {
    let clause = parser.clause_db.last_clause();
    match clause_ids.find_equal_clause(&parser.clause_db, clause, /*delete=*/ true) {
        None => {
            if parser.verbose {
                as_warning!({
                    puts!("c deleted clause is not present in the formula: ");
                    puts_clause(parser.clause_db.clause(clause));
                    puts!("\n");
                });
            }
            // Need this for sickcheck
            parser
                .proof
                .push(ProofStep::deletion(Clause::DOES_NOT_EXIST))
        }
        Some(clause) => parser.proof.push(ProofStep::deletion(clause)),
    }
    parser.clause_db.pop_clause();
}

/// Compute the hash of a clause. This is the same hash function `drat-trim` uses.
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

/// Check if a character is a decimal digit.
fn is_digit(value: u8) -> bool {
    value >= b'0' && value <= b'9'
}

/// Check if a character is a decimal digit or a dash.
fn is_digit_or_dash(value: u8) -> bool {
    is_digit(value) || value == b'-'
}

// Error messages.
/// A numeric overflow. This should only happen for user input.
const OVERFLOW: &str = "overflow while parsing number";
/// Parser error ("unexpected EOF")
const EOF: &str = "premature end of file";
/// Parser error (`expected ...`)
const NUMBER: &str = "expected number";
/// Parser error (`expected ...`)
const SPACE: &str = "expected space";
/// Parser error (`expected ...`)
const NUMBER_OR_SPACE: &str = "expected number or space";
/// Parser error (`expected ...`)
const NUMBER_OR_MINUS: &str = "expected number or \"-\"";
/// Parser error (`expected ...`)
const P_CNF: &str = "expected \"p cnf\"";
/// Parser error (`expected ...`)
const DRAT: &str = "expected DRAT instruction";
/// Parser error (`expected ...`)
const NEWLINE: &str = "expected newline";

/// Parse a decimal number.
///
/// Consumes one or more decimal digits, returning the value of the
/// resulting number on success. Fails if there is no digit or if the digits do
/// not end in a whitespace or newline.
fn parse_u64(input: &mut Input) -> Result<u64> {
    match input.peek() {
        None => return Err(input.error(NUMBER)),
        Some(c) => {
            if !is_digit(c) {
                return Err(input.error(NUMBER));
            }
        }
    }
    let mut value: u64 = 0;
    while let Some(c) = input.peek() {
        if is_space(c) {
            break;
        }
        if !is_digit(c) {
            return Err(input.error(NUMBER_OR_SPACE));
        }
        input.next();
        value = value
            .checked_mul(10)
            .and_then(|val| val.checked_add(u64::from(c - b'0')))
            .ok_or_else(|| input.error(OVERFLOW))?;
    }
    Ok(value)
}

/// Just like `parse_u64` but convert the result to an i32.
fn parse_i32(input: &mut Input) -> Result<i32> {
    let value = parse_u64(input)?;
    if value > i32::max_value().try_into().unwrap() {
        Err(input.error(OVERFLOW))
    } else {
        Ok(value as i32)
    }
}

/// Parse a [Literal](../literal/struct.Literal.html).
///
/// Consumes zero or more whitespace characters followd
/// by an optional "-", a number of at least one decimal digit,
/// trailed by whitespace. If the number is zero, consumes all whitespace
/// until the next newline.
pub fn parse_literal(input: &mut Input) -> Result<Literal> {
    parse_any_space(input);
    match input.peek() {
        None => Err(input.error(EOF)),
        Some(c) if is_digit_or_dash(c) => {
            let sign = if c == b'-' {
                input.next();
                -1
            } else {
                1
            };
            let number = parse_i32(input)?;
            if number == 0 {
                parse_any_whitespace(input);
            }
            Ok(Literal::new(sign * number))
        }
        _ => Err(input.error(NUMBER_OR_MINUS)),
    }
}

/// Parse a literal from a compressed proof.
pub fn parse_literal_binary(input: &mut Input) -> Result<Literal> {
    let mut i = 0;
    let mut result = 0;
    while let Some(value) = input.next() {
        if (u64::from(value & 0x7f) << (7 * i)) > u32::max_value().into() {
            return Err(input.error(OVERFLOW));
        }
        result |= u32::from(value & 0x7f) << (7 * i);
        i += 1;
        if (value & 0x80) == 0 {
            break;
        }
    }
    Ok(Literal::from_raw(result))
}

/// Parse a DIMACS comment starting with "c ".
///
/// Consumes a leading "c" and any characters until (including) the next newline.
fn parse_comment(input: &mut Input) -> Result<()> {
    match input.peek() {
        Some(b'c') => {
            input.next();
            while let Some(c) = input.next() {
                if c == b'\n' {
                    return Ok(());
                }
            }
            Err(input.error(NEWLINE))
        }
        _ => Err(input.error("")),
    }
}

/// Parse one or more spaces.
fn parse_some_spaces(input: &mut Input) -> Result<()> {
    if input.peek() != Some(b' ') {
        return Err(input.error(SPACE));
    }
    while let Some(b' ') = input.peek() {
        input.next();
    }
    Ok(())
}

/// Parse zero or more spaces.
fn parse_any_space(input: &mut Input) {
    while let Some(c) = input.peek() {
        if c != b' ' {
            break;
        }
        input.next();
    }
}

/// Parse zero or more spaces or linebreaks.
fn parse_any_whitespace(input: &mut Input) {
    while let Some(c) = input.peek() {
        if !is_space(c) {
            break;
        }
        input.next();
    }
}

/// Parse a DIMACS header.
fn parse_formula_header(input: &mut Input) -> Result<(i32, u64)> {
    while Some(b'c') == input.peek() {
        parse_comment(input)?
    }
    for &expected in b"p cnf" {
        if input.peek().map_or(true, |c| c != expected) {
            return Err(input.error(P_CNF));
        }
        input.next();
    }
    parse_some_spaces(input)?;
    let maxvar = parse_i32(input)?;
    parse_some_spaces(input)?;
    let num_clauses = parse_u64(input)?;
    parse_any_whitespace(input);
    Ok((maxvar, num_clauses))
}

/// Returns true if the character is one of the whitespace characters we allow.
fn is_space(c: u8) -> bool {
    [b' ', b'\n', b'\r'].iter().any(|&s| s == c)
}

/// Commence the addition of a new clause to the database.
///
/// Must be called before pushing th first literal with
/// [add_literal()](fn.add_literal.html).
fn open_clause(parser: &mut Parser, state: ProofParserState) -> Clause {
    let clause = parser.clause_db.open_clause();
    if parser.is_pr() && state != ProofParserState::Deletion {
        let witness = parser.witness_db.open_clause();
        invariant!(clause == witness);
    }
    clause
}

/// Parse a DIMACS clause.
fn parse_clause(parser: &mut Parser, clause_ids: &mut HashTable, input: &mut Input) -> Result<()> {
    open_clause(parser, ProofParserState::Clause);
    parser.clause_pivot.push(Literal::NEVER_READ);
    loop {
        let literal = parse_literal(input)?;
        add_literal(parser, clause_ids, ProofParserState::Clause, literal);
        if literal.is_zero() {
            return Ok(());
        }
    }
}

/// Parse a DIMACS formula.
fn parse_formula(parser: &mut Parser, clause_ids: &mut HashTable, mut input: Input) -> Result<()> {
    parse_formula_header(&mut input)?;
    while let Some(c) = input.peek() {
        if c == b'c' {
            parse_comment(&mut input)?;
            continue;
        }
        parse_clause(parser, clause_ids, &mut input)?;
    }
    Ok(())
}

/// Return true if the file is in binary (compressed) DRAT.
///
/// Read the first ten characters of the given file to determine
/// that, just like `drat-trim`. This works fine on real proofs.
pub fn is_binary_drat(filename: &str) -> bool {
    let mut file = open_file(filename);
    file.seek(SeekFrom::Start(0)).unwrap_or_else(|_err| {
        die!("proof file is not seekable - cannot currently determine if it has binary DRAT")
    });
    is_binary_drat_impl(read_from_compressed_file(file, filename))
}
/// Implementation of `is_binary_drat`.
fn is_binary_drat_impl(buffer: impl Iterator<Item = u8>) -> bool {
    for c in buffer.take(10) {
        if (c != 100) && (c != 10) && (c != 13) && (c != 32) && (c != 45) && ((c < 48) || (c > 57))
        {
            return true;
        }
    }
    false
}

/// The state of our proof parser
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum ProofParserState {
    /// Before the start of an instruction
    Start,
    /// Inside a clause/lemma
    Clause,
    /// Inside a witness
    Witness,
    /// Inside a deletion
    Deletion,
}

/// Parse a single proof step
pub fn parse_proof_step(
    parser: &mut Parser,
    clause_ids: &mut HashTable,
    input: &mut Input,
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

/// Fix-up incomplete proofs.
///
/// This adds a zero if the last line was missing one.
/// Additionally it adds an empty clause as final lemma.
pub fn finish_proof(parser: &mut Parser, clause_ids: &mut HashTable, state: &mut ProofParserState) {
    // patch missing zero terminators
    match *state {
        ProofParserState::Clause | ProofParserState::Deletion | ProofParserState::Witness => {
            add_literal(parser, clause_ids, *state, Literal::new(0));
        }
        ProofParserState::Start => (),
    };
}

/// Parse a proof given the hashtable.
fn parse_proof(
    parser: &mut Parser,
    clause_ids: &mut HashTable,
    mut input: Input,
    binary: bool,
) -> Result<()> {
    parser.proof_start = Clause::new(parser.clause_db.number_of_clauses());
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
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[allow(unused_macros)]
    macro_rules! literals {
        ($($x:expr),*) => (Vector::from_vec(vec!($(Literal::new($x)),*)));
    }

    fn sample_formula(clause_ids: &mut HashTable) -> Parser {
        let mut parser = Parser::default();
        parser.redundancy_property = RedundancyProperty::RAT;
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
        let mut clause_ids = HashTable::new();
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
            parser,
            Parser {
                redundancy_property: RedundancyProperty::RAT,
                maxvar: Variable::new(3),
                clause_pivot: vector!(Literal::NEVER_READ, Literal::NEVER_READ, Literal::new(1)),
                proof_start: Clause::new(2),
                proof: vector!(
                    ProofStep::lemma(Clause::new(2)),
                    ProofStep::deletion(Clause::new(0)),
                ),
                max_proof_steps: None,
                verbose: true,
                clause_db: ClauseDatabase::from(
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
                    ),
                    vector!(0, 5, 10),
                ),
                witness_db: WitnessDatabase::from(vector!(), vector!(0)),
            }
        );
    }
}

impl HeapSpace for Parser {
    fn heap_space(&self) -> usize {
        self.clause_db.heap_space()
            + self.witness_db.heap_space()
            + self.clause_pivot.heap_space()
            + self.proof.heap_space()
    }
}

/// A peekable iterator for bytes that records line and column information.
pub struct Input<'a> {
    /// The source of the input data
    source: Peekable<Box<dyn Iterator<Item = u8> + 'a>>,
    /// Whether we are parsing binary or textual data
    binary: bool,
    /// The current line number (if not binary)
    line: usize,
    /// The current column
    column: usize,
}

impl<'a> Input<'a> {
    /// Create a new `Input` from some source
    pub fn new(source: Box<dyn Iterator<Item = u8> + 'a>, binary: bool) -> Self {
        Input {
            source: source.peekable(),
            binary,
            line: 1,
            column: 1,
        }
    }
    /// Look at the next byte without consuming it
    pub fn peek(&mut self) -> Option<u8> {
        self.source.peek().cloned()
    }
    /// Create an io::Error with the given message and position information.
    pub fn error(&self, why: &'static str) -> Error {
        Error::new(
            ErrorKind::InvalidData,
            if self.binary {
                format!("{} at position {}", why, self.column)
            } else {
                format!("{} at line {} column {}", why, self.line, self.column)
            },
        )
    }
}

impl Iterator for Input<'_> {
    type Item = u8;
    fn next(&mut self) -> Option<u8> {
        self.source.next().map(|c| {
            if !self.binary && c == b'\n' {
                self.line += 1;
                self.column = 0;
            }
            self.column += 1;
            c
        })
    }
}
