//! DIMACS and DRAT parser

use crate::{
    clause::{Clause, ProofStep},
    clausedatabase::{ClauseDatabase, WitnessDatabase, clause_db , witness_db},
    config::{unreachable , ProofFormat},
    hashtable::{FixedSizeHashTable, HashTable} ,
    input::{SimpleInput} ,
    literal::{Literal, Variable},
    memory::{format_memory_usage, HeapSpace, Offset, SmallStack, Stack},
    output::{self, Timer, RuntimeError , RuntimeResult},
    proof::{Proof} ,
};
use std::{
    alloc::{alloc, dealloc, realloc, Layout},
    cmp,
    collections::{HashMap},
    convert::TryInto,
    fmt::{self, Display, Formatter},
    fs::File,
    hash::{Hash, Hasher},
    io::{self, Read},
    iter::Peekable,
    mem::{align_of, drop, size_of},
    panic, ptr::{self, NonNull},
};

#[derive(Debug, PartialEq , Eq)]
pub enum SyntaxFormat {
    Dimacs ,
    DratFirstPivot ,
    DratAnyPivot ,
    DprFirstPivot ,
    DprAnyPivot ,
    Dsr ,
}
impl SyntaxFormat {
    pub fn from(p : ProofFormat) -> SyntaxFormat {
        match p {
            ProofFormat::DratFirstPivot => SyntaxFormat::DratFirstPivot ,
            ProofFormat::DratAnyPivot => SyntaxFormat::DratAnyPivot ,
            ProofFormat::DprFirstPivot => SyntaxFormat::DprFirstPivot ,
            ProofFormat::DprAnyPivot => SyntaxFormat::DprAnyPivot ,
            ProofFormat::Dsr => SyntaxFormat::Dsr ,
        }
    }
    pub fn rat_first_pivot(&self) -> bool {
        match self {
            SyntaxFormat::DratFirstPivot | SyntaxFormat::DprFirstPivot => true ,
            _ => false
        }
    }
    pub fn rat_any_pivot(&self) -> bool {
        match self {
            SyntaxFormat::DratAnyPivot | SyntaxFormat::DprAnyPivot => true ,
            _ => false ,
        }
    }
    pub fn drat(&self) -> bool {
        match self {
            SyntaxFormat::DratFirstPivot | SyntaxFormat::DratAnyPivot => true ,
            _ => false ,
        }
    }
    pub fn dpr(&self) -> bool {
        match self {
            SyntaxFormat::DprFirstPivot | SyntaxFormat::DprAnyPivot => true ,
            _ => false ,
        }
    }
    pub fn dsr(&self) -> bool {
        match self {
            SyntaxFormat::Dsr => true ,
            _ => false ,
        }
    }
}

#[derive(Debug, Copy, Clone)]
pub enum BinaryMode {
    Binary ,
    Text ,
    DratTrimDetection ,
    PrefixDetection ,
}
impl BinaryMode {
    pub fn detect(&self , filename : &str) -> RuntimeResult<bool> {
        match self {
            BinaryMode::Binary => Ok(true) ,
            BinaryMode::Text => Ok(false) ,
            BinaryMode::DratTrimDetection => self.drat_trim_detection(filename) ,
            BinaryMode::PrefixDetection => self.prefix_detection(filename) ,
        }
    }
    fn drat_trim_detection(&self , filename : &str) -> RuntimeResult<bool> {
        let mut input = SimpleInput::from_file(filename, false)? ;
        for i in 0..10 {
            match input.next().map_err(|e| RuntimeError::FileBinaryDetection(filename.to_string()))? {
                None => return Ok(false) ,
                Some(c) => if (c != 100) && (c != 10) && (c != 13) && (c != 32) && (c != 45) && ((c < 48) || (c > 57)) {
                    return Ok(true) ;
                }
            }
        }
        Ok(false)
    }
    fn prefix_detection(&self , filename : &str) -> RuntimeResult<bool> {
        let mut input = SimpleInput::from_file(filename, false)? ;
        let b = input.peek().map_err(|e| RuntimeError::FileBinaryDetection(filename.to_string()))? ;
        Ok(b == Some(0x7F))
    }
}

pub struct ParsingInfo {
    proof : Proof ,
    table : FixedSizeHashTable ,
}
impl ParsingInfo {
    pub fn new() -> ParsingInfo {
        ParsingInfo {
            proof : Proof::new() ,
            table : FixedSizeHashTable::new() ,
        }
    }
    pub fn extract(self) -> Proof {
        self.proof
    }
}

pub enum ParsingError {
    OutOfBounds(usize) ,
    InvalidSyntax(usize) ,
    MissingHeader(usize) ,
    UnmatchedClauses(usize) ,
}

pub struct Parser {
    info : ParsingInfo ,
    input : SimpleInput ,
    syntax : SyntaxFormat ,
    binary : bool ,
}
impl Parser {
    pub fn new(info : ParsingInfo , filename : &str , syntax : SyntaxFormat , binary : BinaryMode) -> RuntimeResult<Parser> {
        // todo : terminating clause
        // todo : memory usage breakdown
        // todo : verbosity
        // todo : how to initialize witness_db ?
        let mode = binary.detect(filename)? ;
        let input = SimpleInput::from_file(filename, mode)? ;
        Ok(Parser {
            info : info ,
            input : input ,
            syntax : syntax ,
            binary : mode ,
        })
    }
    pub fn parse(mut self) -> RuntimeResult<ParsingInfo> {
        let mut _timer = self.timer() ;
        if self.syntax != SyntaxFormat::Dimacs {
            self.info.proof.proof_start = Clause::new(clause_db().number_of_clauses()) ;
        }
        if self.binary {
            self.parse_binary()? ;
        } else {
            self.parse_text()? ;
        }
        Ok(self.info)
    }
    fn parse_binary(&mut self) -> RuntimeResult<()> {
        let mut clauses : u64 = 0u64 ;
        if self.input.peek()? == Some(0x7F) {        //Skipping prefix if necessary
            self.input.next() ;
        }
        while let Some(c) = self.input.next()? {
            if c == 0x61u8 {                        // RUP/RAT/PR clause introduction
                self.parse_introduction(false)? ;
                clauses = clauses + 1 ;
            } else if c == 0x64u8 && self.syntax != SyntaxFormat::Dimacs {                 // clause deletion
                self.parse_deletion()? ;
                self.info.proof.proof_deletions = self.info.proof.proof_deletions + 1 ;
            } else if c == 0x72u8 && self.syntax == SyntaxFormat::Dsr {    // SR clause introduction
                self.parse_introduction(true)? ;
                self.info.proof.proof_srs = self.info.proof.proof_srs + 1 ;
            } else {
                return Err(self.input.throw_invalid_syntax()) ;
            }
        }
        if self.syntax == SyntaxFormat::Dimacs {
            self.info.proof.cnf_clauses = clauses ;
        } else {
            self.info.proof.proof_introductions = clauses ;
        }
        Ok(())
    }
    pub fn parse_text(&mut self) -> RuntimeResult<()> {
        let mut clauses : u64 = 0u64 ;
        let mut header : Option<usize> = None ;
        if(self.syntax == SyntaxFormat::Dimacs) {
            self.skip_comments()? ;
            let (vars , clauses , line) = self.parse_header() ? ;
            self.info.proof.maxvar = Variable::new(vars) ;
            self.info.proof.cnf_clauses = clauses ;
            header = line ;
        }
        while let Some(c) = self.input.peek()? {     //todo: check spaces and peeking
            if SimpleInput::is_digit_or_dash(c) {
                self.parse_introduction(false)? ;
                clauses = clauses + 1 ;
            } else if c == b'd' && self.syntax != SyntaxFormat::Dimacs {
                self.check_spacing()? ;
                self.parse_deletion()? ;
                self.info.proof.proof_deletions = self.info.proof.proof_deletions + 1 ;
            } else if c == b'r' && self.syntax == SyntaxFormat::Dsr {
                self.check_spacing()? ;
                self.parse_introduction(true)? ;
                self.info.proof.proof_srs = self.info.proof.proof_srs + 1 ;
            } else {
                return Err(self.input.throw_invalid_syntax()) ;
            }
            self.check_spacing()? ;
        }
        if self.syntax == SyntaxFormat::Dimacs {
            if clauses != self.info.proof.cnf_clauses {
                return Err(RuntimeError::ParsingUnmatchedClauses(self.input.filename() , header)) ;
            }            
        } else {
            self.info.proof.proof_introductions = clauses ;
        }
        Ok(())
    }
    pub fn parse_introduction(&mut self , sr : bool) -> RuntimeResult<()> {
        // todo : uniform treatment of drat / dpr / dsr
        // todo : are we taking care of tautological clauses?
        // todo : are we checking for repeated literals?
        // todo : patch missing zero terminators, why do we do this?
        // todo : terminating empty clause, why?
        let clause = self.parse_clause(true)? ;
        self.info.table.add_clause(clause_db().last_clause()) ;
        if self.syntax == SyntaxFormat::Dsr && sr {
            self.parse_dsr_witness()? ;
        }
        if self.syntax != SyntaxFormat::Dimacs {
            self.info.proof.proof.push(ProofStep::lemma(clause)) ;
        }
        Ok(())
    }
    pub fn parse_deletion(&mut self) -> RuntimeResult<()> {
        let clause = self.parse_clause(false)? ;
        let found_clause = match self.info.table.find_equal_clause(clause , true) {
            None => {
                // todo : warning
                Clause::DOES_NOT_EXIST
            } ,
            Some(clause) => clause ,
        } ;
        self.info.proof.proof.push(ProofStep::deletion(found_clause)) ;
        clause_db().pop_clause() ;
        Ok(())
    }
    fn parse_header(&mut self) -> RuntimeResult<(u32 , u64 , Option<usize>)> {
        for &expected in b"p cnf" {
            if self.input.peek()?.map_or(true , |c| c != expected) {
                return Err(RuntimeError::ParsingMissingHeader(self.input.filename() , self.input.line())) ;
            }
            self.input.next()? ;
        }
        let line = self.input.line() ;
        self.check_spacing()? ;
        let maxvar = self.input.parse_u32()? ;
        self.check_spacing()? ;
        let nclauses = self.input.parse_u64()? ;
        self.check_spacing()? ;
        Ok((maxvar , nclauses , line))
    }
    pub fn parse_clause(&mut self , intro : bool) -> RuntimeResult<Clause> {
        let clause = clause_db().open_clause() ;
        if self.syntax.dpr() {
            let witness = witness_db().open_witness() ;
            invariant!(clause == witness) ;
        }
        let check_repetition : bool = intro && self.syntax.dpr() ;
        let mut first : Literal = Literal::new(0) ;
        let mut head : bool = true ;
        loop {
            let literal = self.parse_literal()? ;
            if literal.is_zero() {
                if intro {
                    clause_db().push_literal(literal) ;
                    if self.syntax == SyntaxFormat::Dimacs {
                        self.info.proof.pivots.push(Literal::NEVER_READ) ;
                    } else {
                        if self.syntax.rat_first_pivot() {
                            self.info.proof.pivots.push(first) ;
                        }
                        if self.syntax.dpr() {
                            witness_db().push_literal(Literal::new(0)) ;
                        }
                    }
                }
                return Ok(clause) ;
            }
            if head && intro {
                head = false ;
                first = literal ;
            }
            if check_repetition {
                if literal == first {
                    clause_db().push_literal(Literal::new(0)) ;
                    self.parse_dpr_witness(literal) ;
                    return Ok(clause) ;
                }
            }
            self.info.proof.maxvar = cmp::max(self.info.proof.maxvar , literal.variable()) ;
            clause_db().push_literal(literal) ;
        }
    }
    pub fn parse_dpr_witness(&mut self , literal : Literal) -> RuntimeResult<()> {
        witness_db().push_literal(literal) ;
        loop {
            let literal = self.parse_literal()? ;
            witness_db().push_literal(literal) ;
            if literal.is_zero() {
                break ;
            }
            self.info.proof.maxvar = cmp::max(self.info.proof.maxvar , literal.variable()) ;
        }
        Ok(())
    }
    pub fn parse_dsr_witness(&mut self) -> RuntimeResult<()> {
        loop {
            let variable : Literal = self.parse_literal()? ;
            if !variable.is_positive() {
                if variable.is_zero() {
                    witness_db().push_literal(Literal::new(0)) ;
                    return Ok(())
                } else {
                    return Err(self.input.throw_invalid_syntax()) ;
                }
            }
            self.info.proof.maxvar = cmp::max(self.info.proof.maxvar , variable.variable()) ;
            witness_db().push_literal(variable) ;
            let atom : Literal = self.parse_atom()? ;
            witness_db().push_literal(atom) ;
            self.info.proof.maxvar = cmp::max(self.info.proof.maxvar , atom.variable()) ;
        }
    }
    fn parse_literal(&mut self) -> RuntimeResult<Literal> {
        let literal = if self.binary {
                self.input.parse_literal()?
            } else {
                self.input.parse_literal_binary()?
            } ;
        self.check_spacing()? ;
        Ok(literal)
    }
    fn parse_atom(&mut self) -> RuntimeResult<Literal> {
        let literal = if self.binary {
                self.input.parse_atom()?
            } else {
                self.input.parse_atom_binary()?
            } ;
        self.check_spacing()? ;
        Ok(literal)
    }
    fn timer(&self) -> Timer {
        let name : &str = if self.syntax == SyntaxFormat::Dimacs {
                "parsing formula"
            } else {
                "parsing proof"   
            } ;
        Timer::name(name)
    }
    fn skip_comments(&mut self) -> RuntimeResult<()> {
        while let Some(c) = self.input.peek()? {
            if c == b'c' {
                self.skip_line() ;
            } else {
                break ;
            }
        }
        Ok(())
    }
    fn skip_line(&mut self) -> RuntimeResult<()> {
        while let Some(c) = self.input.peek()? {
            if c == b'\n' {
                break ;
            } else {
                self.input.next()? ;
            }
        }
        Ok(())
    }
    fn check_spacing(&mut self) -> RuntimeResult<()> {
        if !self.input.skip_spaces()? {
            return Err(self.input.throw_invalid_syntax()) ;
        }
        Ok(())
    }
}

// #[derive(Debug, PartialEq)]
// pub struct Parser {
//     pub redundancy_property: RedundancyProperty,
//     pub maxvar: Variable,
//     pub clause_pivot: Stack<Literal>,
//     pub proof_start: Clause,
//     pub proof: Stack<ProofStep>,
//     pub max_proof_steps: Option<usize>,
//     pub no_terminating_empty_clause: bool,
//     pub verbose: bool,
// }

// impl Parser {
//     pub fn new() -> Parser {
//         unsafe {
//             CLAUSE_DATABASE = NonNull::new_unchecked(Box::into_raw(Box::new(ClauseDatabase::new())));
//             WITNESS_DATABASE = NonNull::new_unchecked(Box::into_raw(Box::new(WitnessDatabase::new())));
//         }
//         assert!(
//             clause_db().is_empty(),
//             "Only one parser can be active at any time."
//         );
//         clause_db().clear();
//         witness_db().clear();
//         clause_db().initialize();
//         Parser {
//             redundancy_property: RedundancyProperty::RAT,
//             maxvar: Variable::new(0),
//             clause_pivot: Stack::new(),
//             proof_start: Clause::new(0),
//             proof: Stack::new(),
//             max_proof_steps: None,
//             no_terminating_empty_clause: false,
//             verbose: true,
//         }
//     }
//     pub fn is_pr(&self) -> bool {
//         self.redundancy_property == RedundancyProperty::PR
//     }
// }

// pub fn parse_files(
//     formula_file: &str,
//     proof_file: &str,
//     no_terminating_empty_clause: bool,
//     memory_usage_breakdown: bool,
// ) -> Parser {
//     let mut parser = Parser::new();
//     parser.no_terminating_empty_clause = no_terminating_empty_clause;
//     let mut clause_ids = FixedSizeHashTable::new();
//     // let mut clause_ids = DynamicHashTable::new();
//     run_parser(&mut parser, Some(formula_file), proof_file, &mut clause_ids);
//     if memory_usage_breakdown {
//         print_memory_usage(&parser, &clause_ids);
//     }
//     parser
// }

// fn print_memory_usage(parser: &Parser, clause_ids: &impl HashTable) {
//     let usages = vec![
//         ("db", clause_db().heap_space()),
//         ("hash-table", clause_ids.heap_space()),
//         ("proof", parser.proof.heap_space()),
//         ("rest", parser.clause_pivot.heap_space()),
//     ];
//     let total = usages.iter().map(|pair| pair.1).sum();
//     output::value("parser memory (MB)", format_memory_usage(total));
//     for (name, usage) in usages {
//         output::value(&format!("memory-{}", name), format_memory_usage(usage));
//     }
// }

// pub fn run_parser_on_formula(
//     mut parser: &mut Parser,
//     formula: Option<&str>,
//     proof_file: &str,
//     clause_ids: &mut impl HashTable,
// ) {
//     parser.redundancy_property = proof_format_by_extension(&proof_file);
//     if parser.verbose {
//         comment!("mode: {}", parser.redundancy_property);
//     }
//     if parser.redundancy_property != RedundancyProperty::RAT {
//         witness_db().initialize();
//     }
//     if let Some(formula_file) = formula {
//         let mut _timer = Timer::name("parsing formula");
//         if !parser.verbose {
//             _timer.disabled = true;
//         }
//         let formula_input = read_file(formula_file);
//         parse_formula(
//             &mut parser,
//             clause_ids,
//             SimpleInput::new(Box::new(formula_input), false),
//         )
//         .unwrap_or_else(|err| die!("error parsing formula at line {}", err.line));
//     }
// }

// pub fn run_parser(
//     mut parser: &mut Parser,
//     formula: Option<&str>,
//     proof_file: &str,
//     clause_ids: &mut impl HashTable,
// ) {
//     run_parser_on_formula(parser, formula, proof_file, clause_ids);
//     let mut _timer = Timer::name("parsing proof");
//     if !parser.verbose {
//         _timer.disabled = true;
//     }
//     let binary = is_binary_drat(read_file(proof_file).take(10));
//     let proof_input = Box::new(read_file(&proof_file));
//     if binary {
//         if parser.verbose {
//             comment!("binary proof mode");
//         }
//     }
//     parse_proof(
//         &mut parser,
//         clause_ids,
//         SimpleInput::new(proof_input, binary),
//         binary,
//     )
//     .unwrap_or_else(|err| die!("error parsing proof at line {}", err.line));
//     clause_db().shrink_to_fit();
//     witness_db().shrink_to_fit();
//     parser.clause_pivot.shrink_to_fit();
//     parser.proof.shrink_to_fit();
// }

// fn open_file(filename: &str) -> File {
//     File::open(&filename).unwrap_or_else(|err| die!("error opening file: {}", err))
// }

// const ZSTD: &str = ".zst";
// const GZIP: &str = ".gz";
// const BZIP2: &str = ".bz2";
// const LZ4: &str = ".lz4";
// const XZ: &str = ".xz";

// fn compression_format_by_extension(filename: &str) -> (&str, &str) {
//     let mut basename = filename;
//     let mut compression_format = "";
//     for extension in &[ZSTD, GZIP, BZIP2, LZ4, XZ] {
//         if filename.ends_with(extension) {
//             compression_format = extension;
//             basename = &filename[0..filename.len() - extension.len()];
//             break;
//         }
//     }
//     (basename, compression_format)
// }

// pub fn proof_format_by_extension(proof_filename: &str) -> RedundancyProperty {
//     let (basename, _compression_format) = compression_format_by_extension(proof_filename);
//     if basename.ends_with(".drat") {
//         RedundancyProperty::RAT
//     } else if basename.ends_with(".pr") || basename.ends_with(".dpr") {
//         RedundancyProperty::PR
//     } else {
//         RedundancyProperty::RAT
//     }
// }

// impl RedundancyProperty {
//     #[allow(dead_code)]
//     pub fn file_extension(&self) -> &str {
//         match self {
//             RedundancyProperty::RAT => "drat",
//             RedundancyProperty::PR => "dpr",
//         }
//     }
// }
// 
// pub fn read_file(filename: &str) -> Box<dyn Iterator<Item = u8>> {
//     let file = open_file(filename);
//     let (_basename, compression_format) = compression_format_by_extension(filename);
//     if compression_format == "" {
//         return Box::new(std::io::BufReader::new(file).bytes().map(panic_on_error));
//     }
//     match compression_format {
//         ZSTD => {
//             let de = zstd::stream::read::Decoder::new(file)
//                 .unwrap_or_else(|err| die!("failed to decompress ZST archive: {}", err));
//             Box::new(de.bytes().map(panic_on_error))
//         }
//         GZIP => {
//             let de = flate2::read::GzDecoder::new(file);
//             Box::new(de.bytes().map(panic_on_error))
//         }
//         BZIP2 => {
//             let de = bzip2::read::BzDecoder::new(file);
//             Box::new(de.bytes().map(panic_on_error))
//         }
//         XZ => {
//             let de = xz2::read::XzDecoder::new(file);
//             Box::new(de.bytes().map(panic_on_error))
//         }
//         LZ4 => {
//             let de = lz4::Decoder::new(file)
//                 .unwrap_or_else(|err| die!("Failed to decode LZ4 archive: {}", err));
//             Box::new(de.bytes().map(panic_on_error))
//         }
//         _ => unreachable(),
//     }
// }
// 
// fn panic_on_error(result: io::Result<u8>) -> u8 {
//     result.unwrap_or_else(|error| die!("read error: {}", error))
// }

// fn add_literal(
//     parser: &mut Parser,
//     clause_ids: &mut impl HashTable,
//     state: ProofParserState,
//     literal: Literal,
// ) {
//     parser.maxvar = cmp::max(parser.maxvar, literal.variable());
//     match state {
//         ProofParserState::Clause => {
//             clause_db().push_literal(literal);
//             if parser.is_pr() && literal.is_zero() {
//                 witness_db().push_literal(literal);
//             }
//         }
//         ProofParserState::Witness => {
//             invariant!(parser.is_pr());
//             witness_db().push_literal(literal);
//             if literal.is_zero() {
//                 clause_db().push_literal(literal);
//             }
//         }
//         ProofParserState::Deletion => {
//             clause_db().push_literal(literal);
//             if literal.is_zero() {
//                 add_deletion(parser, clause_ids);
//             }
//         }
//         ProofParserState::Start => unreachable(),
//     }
//     match state {
//         ProofParserState::Clause | ProofParserState::Witness => {
//             if literal.is_zero() {
//                 clause_ids.add_clause(clause_db().last_clause());
//             }
//         }
//         _ => (),
//     }
// }

// fn add_deletion(parser: &mut Parser, clause_ids: &mut impl HashTable) {
//     let clause = clause_db().last_clause();
//     match clause_ids.find_equal_clause(clause, /*delete=*/ true) {
//         None => {
//             if parser.verbose {
//                 warn!(
//                     "Deleted clause is not present in the formula: {}",
//                     clause_db().clause_to_string(clause)
//                 );
//             }
//             // Need this for sickcheck
//             parser
//                 .proof
//                 .push(ProofStep::deletion(Clause::DOES_NOT_EXIST))
//         }
//         Some(clause) => parser.proof.push(ProofStep::deletion(clause)),
//     }
//     clause_db().pop_clause();
// }

// fn clause_hash(clause: &[Literal]) -> usize {
//     let mut sum: usize = 0;
//     let mut prod: usize = 1;
//     let mut xor: usize = 0;
//     for &literal in clause {
//         prod = prod.wrapping_mul(literal.as_offset());
//         sum = sum.wrapping_add(literal.as_offset());
//         xor ^= literal.as_offset();
//     }
//     ((1023 * sum + prod) ^ (31 * xor))
// }

// pub type Result<T> = std::result::Result<T, ParseError>;

// #[derive(Debug, PartialEq, Eq)]
// pub struct ParseError {
//     pub line: usize,
//     pub why: &'static str,
// }

// const OVERFLOW: &str = "overflow while parsing number";
// const NUMBER: &str = "expected number";
// const EOF: &str = "premature end of file";
// const P_CNF: &str = "expected \"p cnf\"";
// const DRAT: &str = "expected DRAT instruction";

// fn parse_literal(input: &mut impl Input) -> Result<Literal> {
//     match input.peek() {
//         None => Err(input.error(EOF)),
//         Some(c) if is_digit_or_dash(c) => {
//             let sign = if c == b'-' {
//                 input.next();
//                 -1
//             } else {
//                 1
//             };
//             Ok(Literal::new(sign * parse_i32(input)?))
//         }
//         _ => Err(input.error(NUMBER)),
//     }
// }

// fn parse_comment(input: &mut impl Input) -> Option<()> {
//     match input.peek() {
//         Some(b'c') => {
//             input.next();
//             while let Some(c) = input.next() {
//                 if c == b'\n' {
//                     return Some(());
//                 }
//             }
//             None
//         }
//         _ => None,
//     }
// }

// fn parse_formula_header(input: &mut impl Input) -> Result<(u64, u64)> {
//     while let Some(()) = parse_comment(input) {}
//     for &expected in b"p cnf" {
//         if input.peek().map_or(true, |c| c != expected) {
//             return Err(input.error(P_CNF));
//         }
//         input.next();
//     }
//     let maxvar = input.parse_u64()?;
//     let num_clauses = input.parse_u64()?;
//     Ok((maxvar, num_clauses))
// }

// fn open_clause(parser: &mut Parser, state: ProofParserState) -> Clause {
//     let clause = clause_db().open_clause();
//     if parser.is_pr() && state != ProofParserState::Deletion {
//         let witness = witness_db().open_witness();
//         invariant!(clause == witness);
//     }
//     clause
// }

// fn parse_formula(
//     parser: &mut Parser,
//     clause_ids: &mut impl HashTable,
//     mut input: impl Input,
// ) -> Result<()> {
//     parse_formula_header(&mut input)?;
//     let mut clause_head = true;
//     while let Some(c) = input.peek() {
//         if is_space(c) {
//             input.next();
//             continue;
//         }
//         if c == b'c' {
//             parse_comment(&mut input);
//             continue;
//         }
//         let literal = parse_literal(&mut input)?;
//         if clause_head {
//             open_clause(parser, ProofParserState::Clause);
//             parser.clause_pivot.push(Literal::NEVER_READ);
//         }
//         add_literal(parser, clause_ids, ProofParserState::Clause, literal);
//         clause_head = literal.is_zero();
//     }
//     Ok(())
// }

// // See drat-trim
// pub fn is_binary_drat(buffer: impl Iterator<Item = u8>) -> bool {
//     for c in buffer {
//         if (c != 100) && (c != 10) && (c != 13) && (c != 32) && (c != 45) && ((c < 48) || (c > 57))
//         {
//             return true;
//         }
//     }
//     false
// }

// #[derive(Debug, PartialEq, Eq, Clone, Copy)]
// pub enum ProofParserState {
//     Start,
//     Clause,
//     Witness,
//     Deletion,
// }

// pub fn parse_proof_step(
//     parser: &mut Parser,
//     clause_ids: &mut impl HashTable,
//     input: &mut impl Input,
//     binary: bool,
//     state: &mut ProofParserState,
// ) -> Result<Option<()>> {
//     let literal_parser = if binary {
//         parse_literal_binary
//     } else {
//         parse_literal
//     };
//     let mut lemma_head = true;
//     let mut first_literal = None;
//     while let Some(c) = input.peek() {
//         if !binary && is_space(c) {
//             input.next();
//             continue;
//         }
//         if *state == ProofParserState::Start {
//             *state = match c {
//                 b'd' => {
//                     input.next();
//                     open_clause(parser, ProofParserState::Deletion);
//                     ProofParserState::Deletion
//                 }
//                 b'c' => {
//                     parse_comment(input);
//                     ProofParserState::Start
//                 }
//                 c if (!binary && is_digit_or_dash(c)) || (binary && c == b'a') => {
//                     if binary {
//                         input.next();
//                     }
//                     lemma_head = true;
//                     let clause = open_clause(parser, ProofParserState::Clause);
//                     parser.proof.push(ProofStep::lemma(clause));
//                     ProofParserState::Clause
//                 }
//                 _ => return Err(input.error(DRAT)),
//             };
//             continue;
//         }
//         let literal = literal_parser(input)?;
//         if parser.is_pr() && *state == ProofParserState::Clause && first_literal == Some(literal) {
//             *state = ProofParserState::Witness;
//         }
//         if *state == ProofParserState::Clause && lemma_head {
//             parser.clause_pivot.push(literal);
//             first_literal = Some(literal);
//             lemma_head = false;
//         }
//         invariant!(*state != ProofParserState::Start);
//         add_literal(parser, clause_ids, *state, literal);
//         if literal.is_zero() {
//             *state = ProofParserState::Start;
//             return Ok(Some(()));
//         }
//     }
//     Ok(None)
// }

// pub fn finish_proof(
//     parser: &mut Parser,
//     clause_ids: &mut impl HashTable,
//     state: &mut ProofParserState,
// ) {
//     // patch missing zero terminators
//     match *state {
//         ProofParserState::Clause | ProofParserState::Deletion | ProofParserState::Witness => {
//             add_literal(parser, clause_ids, *state, Literal::new(0));
//         }
//         ProofParserState::Start => (),
//     };
//     if !parser.no_terminating_empty_clause {
//         // ensure that every proof ends with an empty clause
//         let clause = open_clause(parser, ProofParserState::Clause);
//         parser.proof.push(ProofStep::lemma(clause));
//         add_literal(
//             parser,
//             clause_ids,
//             ProofParserState::Clause,
//             Literal::new(0),
//         );
//     }
// }

// fn parse_proof(
//     parser: &mut Parser,
//     clause_ids: &mut impl HashTable,
//     mut input: impl Input,
//     binary: bool,
// ) -> Result<()> {
//     parser.proof_start = Clause::new(clause_db().number_of_clauses());
//     let mut state = ProofParserState::Start;
//     if parser.max_proof_steps != Some(0) {
//         while let Some(()) = parse_proof_step(parser, clause_ids, &mut input, binary, &mut state)? {
//             if parser
//                 .max_proof_steps
//                 .map_or(false, |max_steps| parser.proof.len() == max_steps)
//             {
//                 break;
//             }
//         }
//     }
//     finish_proof(parser, clause_ids, &mut state);
//     Ok(())
// }
// 
// impl Display for ParseError {
//     fn fmt(&self, f: &mut Formatter) -> fmt::Result {
//         write!(f, "Parse error at line {}:  {}", self.line, self.why)
//     }
// }
// 
// #[allow(dead_code)]
// pub fn print_db() {
//     let clause_db = &clause_db();
//     let witness_db = &witness_db();
//     let is_pr = !witness_db.empty();
//     for clause in Clause::range(0, clause_db.last_clause() + 1) {
//         write_to_stdout!(
//             "{}{} fields: {:?}\n",
//             clause_db.clause_to_string(clause),
//             if is_pr {
//                 format!(", {}", witness_db.witness_to_string(clause))
//             } else {
//                 "".into()
//             },
//             clause_db.fields(clause)
//         );
//     }
// }

// #[cfg(test)]
// mod tests {
//     use super::*;

//     #[allow(unused_macros)]
//     macro_rules! literals {
//         ($($x:expr),*) => (Stack::from_vec(vec!($(Literal::new($x)),*)));
//     }

//     fn sample_formula(clause_ids: &mut impl HashTable) -> Parser {
//         let mut parser = Parser::new();
//         parser.redundancy_property = RedundancyProperty::RAT;
//         let example = r#"c comment
// p cnf 2 2
// 1 2 0
// c comment
// -1 -2 0"#;
//         assert!(parse_formula(
//             &mut parser,
//             clause_ids,
//             SimpleInput::new(Box::new(example.as_bytes().iter().cloned()), false),
//         )
//         .is_ok());
//         parser
//     }
//     #[test]
//     fn valid_formula_and_proof() {
//         let mut clause_ids = FixedSizeHashTable::new();
//         let mut parser = sample_formula(&mut clause_ids);
//         let result = parse_proof(
//             &mut parser,
//             &mut clause_ids,
//             SimpleInput::new(Box::new(b"1 2 3 0\nd 1 2 0".into_iter().cloned()), false),
//             false,
//         );
//         assert!(result.is_ok());
//         fn lit(x: i32) -> Literal {
//             Literal::new(x)
//         }
//         fn raw(x: u32) -> Literal {
//             Literal::from_raw(x)
//         }
//         assert_eq!(
//             clause_db(),
//             &ClauseDatabase::from(
//                 stack!(
//                     raw(0),
//                     raw(0),
//                     lit(1),
//                     lit(2),
//                     lit(0),
//                     raw(1),
//                     raw(0),
//                     lit(-2),
//                     lit(-1),
//                     lit(0),
//                     raw(2),
//                     raw(0),
//                     lit(1),
//                     lit(2),
//                     lit(3),
//                     lit(0),
//                     raw(3),
//                     raw(0),
//                     lit(0),
//                 ),
//                 stack!(0, 5, 10, 16)
//             )
//         );
//         assert_eq!(witness_db(), &WitnessDatabase::from(stack!(), stack!()));
//         assert_eq!(
//             parser,
//             Parser {
//                 redundancy_property: RedundancyProperty::RAT,
//                 maxvar: Variable::new(3),
//                 clause_pivot: stack!(Literal::NEVER_READ, Literal::NEVER_READ, Literal::new(1)),
//                 proof_start: Clause::new(2),
//                 proof: stack!(
//                     ProofStep::lemma(Clause::new(2)),
//                     ProofStep::deletion(Clause::new(0)),
//                     ProofStep::lemma(Clause::new(3)),
//                 ),
//                 max_proof_steps: None,
//                 no_terminating_empty_clause: false,
//                 verbose: true,
//             }
//         );
//     }
// }

// impl HeapSpace for Parser {
//     fn heap_space(&self) -> usize {
//         clause_db().heap_space()
//             + witness_db().heap_space()
//             + self.clause_pivot.heap_space()
//             + self.proof.heap_space()
//     }
// }
