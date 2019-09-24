//! DIMACS and DRAT/DPR parser

use crate::{
    clause::{Clause, ProofStep, RedundancyProperty},
    clausedatabase::{ClauseDatabase, WitnessDatabase},
    input::{Input},
    literal::{Literal, Variable},
    memory::{format_memory_usage, HeapSpace, Offset, SmallVector, Vector},
    output::{print_key_value, unreachable, Timer},
};
use std::{
    cmp,
    collections::HashMap,
    convert::TryInto,
    fs::File,
    hash::{Hash, Hasher},
    io::{Seek, SeekFrom, BufReader, BufWriter, Read, Result, StdinLock},
    panic,
    ptr::NonNull,
    slice,
};

#[derive(Copy, Clone, PartialEq, Eq)]
pub enum ProofSyntax {
    Dimacs,
    Rup,
    Drat,
    Dpr,
    Dsr,
}

#[allow(dead_code)]
impl ProofSyntax {
    fn has_header(self) -> bool {
        self == ProofSyntax::Dimacs
    }
    fn has_deletion(self) -> bool {
        match self {
            ProofSyntax::Dimacs | ProofSyntax::Rup => false,
            _ => true,
        }
    }
    fn has_repetition_witness(self) -> bool {
        self == ProofSyntax::Dpr
    }
    fn has_post_witness(self) -> bool {
        self == ProofSyntax::Dsr
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
    /// Whether to insert an extra empty clause at the end
    pub no_terminating_empty_clause: bool,
    /// Print diagnostics and timing information
    pub verbose: bool,
}

impl Parser {
    /// Create a new parser.
    ///
    /// *Note*: this allocates the static clause and witness databases, so this should only be called once.
    pub fn new() -> Parser {
        unsafe {
            CLAUSE_DATABASE =
                NonNull::new_unchecked(Box::into_raw(Box::new(ClauseDatabase::new())));
            WITNESS_DATABASE =
                NonNull::new_unchecked(Box::into_raw(Box::new(WitnessDatabase::new())));
        }
        Parser {
            redundancy_property: RedundancyProperty::RAT,
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
        self.redundancy_property == RedundancyProperty::PR
    }
}

/// A hash table that maps clauses (sets of literals) to clause identifiers.
pub trait HashTable {
    /// Add a new clause to the hashtable.
    fn add_clause(&mut self, clause: Clause);
    /// Find a clause that is equivalent to given clause.
    ///
    /// If delete is true, delete the found clause.
    fn find_equal_clause(&mut self, needle: Clause, delete: bool) -> Option<Clause>;
    /// Return true if this exact clause is active.
    fn clause_is_active(&self, needle: Clause) -> bool;
    /// Delete this exact clause, return true if that succeeded.
    fn delete_clause(&mut self, needle: Clause) -> bool;
}

/// A hash table with a fixed size
///
/// This should work exactly like the one used in `drat-trim`.
/// Given that we expect the number of clauses in the hash table
/// not to exceed a couple million this should be faster and leaner than
/// [DynamicHashTable](struct.DynamicHashTable.html).
pub struct FixedSizeHashTable(Vector<Vector<Clause>>);

/// Return the hash bucket to which this clause belongs.
fn bucket_index(clause: &[Literal]) -> usize {
    clause_hash(clause) % FixedSizeHashTable::SIZE
}

impl FixedSizeHashTable {
    /// The number of buckets in our hash table (`drat-trim` uses a million)
    const SIZE: usize = 2 * 1024 * 1024;
    /// The initial size of each bucket.
    ///
    /// We could increase this to at least use `malloc_usable_size` (system-dependent).
    const BUCKET_INITIAL_SIZE: u16 = 4;
    /// Allocate the hash table.
    #[allow(clippy::new_without_default)]
    pub fn new() -> FixedSizeHashTable {
        FixedSizeHashTable(Vector::from_vec(vec![
            Vector::with_capacity(
                FixedSizeHashTable::BUCKET_INITIAL_SIZE.into()
            );
            FixedSizeHashTable::SIZE
        ]))
    }
}

/// An iterator over the elements of the hash table
pub struct FixedSizeHashTableIterator<'a> {
    /// The iterator over the buckets
    buckets: slice::Iter<'a, Vector<Clause>>,
    /// The iterator over a single bucket
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

/// A hashtable that simply uses the standard `HashMap`
///
/// This maps clauses (by equality) to a a list of clause identifiers.
/// We chose `SmallVector<Clause>` for the latter because most clauses are
/// not duplicated. This way we can avoid one allocation for unique clauses.
pub struct DynamicHashTable(HashMap<ClauseHashEq, SmallVector<Clause>>);

impl DynamicHashTable {
    /// Create a new empty hash table.
    pub fn new() -> DynamicHashTable {
        DynamicHashTable(HashMap::new())
    }
}
impl HashTable for DynamicHashTable {
    fn add_clause(&mut self, clause: Clause) {
        let key = ClauseHashEq(clause);
        self.0
            .entry(key)
            .or_insert_with(SmallVector::default)
            .push(clause)
    }
    fn find_equal_clause(&mut self, needle: Clause, delete: bool) -> Option<Clause> {
        self.0
            .get_mut(&ClauseHashEq(needle))
            .and_then(|equal_clauses| {
                let first = equal_clauses.first();
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
            .map_or(false, |vector| !vector.is_empty())
    }
    fn delete_clause(&mut self, needle: Clause) -> bool {
        self.0
            .get_mut(&ClauseHashEq(needle))
            .map_or(false, |equal_clauses| {
                let mut i = 0;
                while equal_clauses[i] != needle {
                    i += 1;
                    invariant!(i < equal_clauses.len());
                }
                invariant!(i == 0);
                equal_clauses.swap_remove(i);
                true
            })
    }
}

/// Wrapper struct around clause implementing hash and equality by looking
/// at the literals in the clause database.
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

/// Parse a formula and a proof file.
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
    run_parser(&mut parser, formula_file, proof_file, &mut clause_ids);
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

/// Parse a formula.
///
/// This requires the proof file as well to determine the proof format,
/// which is necessary for initialization of the witness database.
pub fn run_parser_on_formula(
    mut parser: &mut Parser,
    formula_file: &str,
    proof_file: &str,
    clause_ids: &mut impl HashTable,
) {
    parser.redundancy_property = proof_format_by_extension(&proof_file);
    if parser.verbose {
        comment!("mode: {}", parser.redundancy_property);
    }
    let mut _timer = Timer::name("parsing formula");
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
    clause_ids: &mut impl HashTable,
) {
    let binary = is_binary_drat(proof_file);
    run_parser_on_formula(parser, formula, proof_file, clause_ids);
    let mut _timer = Timer::name("parsing proof");
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
    let mut i = 0;
    let mut result = 0;
    while let Some(value) = input.next() {
        if (u64::from(value & 0x7f) << (7 * i)) > u32::max_value().into() {
            return Err(input.error(Input::OVERFLOW));
        }
        result |= u32::from(value & 0x7f) << (7 * i);
        i += 1;
        if (value & 0x80) == 0 {
            break;
        }
    }
    Ok(if i == 0 { Literal::new(0) } else { Literal::from_raw(result) })       // todo: make this optional
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
            Err(input.error(Input::NEWLINE))
        }
        _ => Err(input.error("")),
    }
}

/// Parse a DIMACS header.
fn parse_formula_header(input: &mut Input) -> Result<(i32, u64)> {
    while Some(b'c') == input.peek() {
        parse_comment(input)?
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
fn parse_formula(
    parser: &mut Parser,
    clause_ids: &mut impl HashTable,
    mut input: Input,
) -> Result<()> {
    parse_formula_header(&mut input)?;
    while let Some(c) = input.peek() {
        if c == b'c' {
            parse_comment(&mut input)?;
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

/// Returns true if the file is in binary (compressed) DRAT.
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
    for c in buffer {
        if (c != 100) && (c != 10) && (c != 13) && (c != 32) && (c != 45) && ((c < 48) || (c > 57))
        {
            return true;
        }
    }
    false
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
                redundancy_property: RedundancyProperty::RAT,
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

