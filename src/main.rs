//! Rate is a proof checker for DRAT proofs which are commonly used to certify
//! unsatisfiability of SAT formulas.

#![allow(warnings)]
#![allow(clippy::collapsible_if)]
#![allow(clippy::nonminimal_bool)]

#[macro_use]
mod output;
#[macro_use]
mod memory;
mod assignment;
mod checker;
mod clause;
mod clausedatabase;
mod config;
mod features;
mod hashtable;
mod input;
mod literal;
mod parser;
mod proof;
mod sick;

#[macro_use(defer)]
extern crate scopeguard;
#[macro_use(Serialize, Deserialize)]
extern crate serde_derive;

use clap::Arg;

use crate::{
    checker::{Checker, Verdict},
    clausedatabase::free_clause_database,
    config::{Config, ProofFormat},
    output::{solution, value, RuntimeResult, Timer},
    parser::{BinaryMode, Parser, ParsingInfo, SyntaxFormat},
    proof::Proof,
};

/// Run `rate`.
fn main() {
    match run() {
        Ok(ec) => std::process::exit(ec),
        Err(e) => e.die(),
    }
}

fn run() -> RuntimeResult<i32> {
    crate::config::signals();
    let mut app = clap::App::new("rate")
        .version(concat!(
            env!("CARGO_PKG_VERSION"),
            " (git commit ",
            env!("GIT_COMMIT"),
            ")"
        ))
        .about(env!("CARGO_PKG_DESCRIPTION"))
        .arg(
            Arg::with_name("INPUT")
                .required(true)
                .help("input file in DIMACS format"),
        )
        .arg(
            Arg::with_name("PROOF")
                .required(true)
                .help("proof file in DRAT format"),
        )
        .arg(
            Arg::with_name("RAT_FIRST_PIVOT")
                .short("1")
                .long("rat-first-pivot")
                .help("Assume that the RAT pivot is the first literal in a clause"),
        )
        .arg(
            Arg::with_name("RAT_ANY_PIVOT")
                .long("rat-any-pivot")
                .help("Check for RAT clauses using every literal in a clause as a pivot (default)"),
        )
        .arg(
            Arg::with_name("SKIP_UNIT_DELETIONS")
                .short("d")
                .long("skip-unit-deletions")
                .help("Ignore deletion of unit clauses: operational check"),
        )
        .arg(
            Arg::with_name("RESPECT_UNIT_DELETIONS")
                .long("respect-unit-deletions")
                .help("Respect deletion of unit clauses: specified check (default)"),
        )
        .arg(
            Arg::with_name("DRAT_SYSTEM")
                .long("drat")
                .help("Check proof with respect to the DRAT proof system (default)"),
        )
        .arg(
            Arg::with_name("DPR_SYSTEM")
                .short("p")
                .long("dpr")
                .help("Check proof with respect to the DPR proof system"),
        )
        .arg(
            Arg::with_name("DSR_SYSTEM")
                .short("s")
                .long("dsr")
                .help("Check proof with respect to the DSR proof system"),
        )
        .arg(
            Arg::with_name("TEXT_FORMAT")
                .short("t")
                .long("text")
                .help("Assume the proof is provided in text format"),
        )
        .arg(
            Arg::with_name("BINARY_FORMAT")
                .short("b")
                .long("binary")
                .help("Assume the proof is provided in binary format"),
        )
        .arg(
            Arg::with_name("DRAT_TRIM_FORMAT")
                .long("heuristic-binary-detect")
                .help("Detect text/binary with the drat-trim heuristic (default)"),
        )
        .arg(
            Arg::with_name("PREFIX_FORMAT")
                .short("x")
                .long("prefix-binary-detect")
                .help("Detect text/binary by checking if the first byte is 0x65"),
        )
        .arg(
            Arg::with_name("UNMARKED_RAT_CANDIDATES")
                .short("r")
                .long("noncore-rat-candidates")
                .help("Do not ignore RAT candidates that are not part of the core."),
        )
        .arg(
            Arg::with_name("NO_TERMINATING_EMPTY_CLAUSE")
                .long("--no-terminating-empty-clause")
                .help("Do not assume an implied empty clause at the end of the proof"),
        )
        .arg(
            Arg::with_name("FORWARD")
                .short("f")
                .long("forward")
                .help("Use naive forward checking."),
        )
        .arg(Arg::with_name("DRAT_TRIM").long("drat-trim").help(
            "Try to be compatible with drat-trim.\n
         This implies --rat_any_pivot --skip-unit-deletions --dpr --noncore-rat-candidates",
        ))
        .arg(Arg::with_name("RUPEE").long("--rupee").help(
            "Try to be compatible with rupee.\n
         This implies --rat_first_pivot --respect-unit-deletions --drat",
        ))
        .arg(
            Arg::with_name("LEMMAS_FILE")
                .takes_value(true)
                .short("l")
                .long("lemmas")
                .help("Write the core lemmas to this file."),
        )
        .arg(
            Arg::with_name("LRAT_FILE")
                .takes_value(true)
                .short("L")
                .long("lrat")
                .help("Write the core lemmas as LRAT certificate to this file."),
        )
        .arg(
            Arg::with_name("GRAT_FILE")
                .takes_value(true)
                .short("G")
                .long("grat")
                .help("Write the GRAT certificate to this file."),
        )
        .arg(
            Arg::with_name("SICK_FILE")
                .takes_value(true)
                .short("i")
                .long("recheck")
                .help("Write the recheck incorrectness witness."),
        )
        .arg(
            Arg::with_name("MEMORY_USAGE_BREAKDOWN")
                .short("m")
                .long("--memory-breakdown")
                .help("Output detailled memory usage."),
        );
    if config::ENABLE_LOGGING {
        app = app.arg(
            Arg::with_name("v")
                .short("v")
                .multiple(true)
                .help("Set the verbosity level (use up to four times)"),
        );
    }

    let config = Config::new(app.get_matches());
    comment!("rate version: {}", env!("GIT_COMMIT"));
    let timer = Timer::name("total time");

    let proof = parse_files(&config)?;

    // let parser = parse_files(
    //     &config.formula_filename,
    //     &config.proof_filename,
    //     config.no_terminating_empty_clause,
    //     config.memory_usage_breakdown,
    // );
    // if parser.is_pr() {
    //     if config.lrat_filename.is_some() || config.grat_filename.is_some() {
    //         die!("LRAT and GRAT generation is not possible for PR")
    //     }
    // }
    let mut checker = Checker::new(proof, config);
    let result = checker.run();
    value("premise clauses", checker.premise_length);
    value("proof steps", checker.proof.len());
    value("skipped tautologies", checker.satisfied_count);
    value("RUP introductions", checker.rup_introductions);
    value("RAT introductions", checker.rat_introductions);
    value("deletions", checker.deletions);
    value("skipped deletions", checker.skipped_deletions);
    value("reason deletions", checker.reason_deletions);
    value(
        "reason deletions shrinking trail",
        checker.reason_deletions_shrinking_trail,
    );
    drop(timer);
    checker.print_memory_usage();
    if result == Verdict::NoConflict {
        warn!("all lemmas verified, but no conflict");
    }
    solution(if result == Verdict::Verified {
        "VERIFIED"
    } else {
        "NOT VERIFIED"
    });
    free_clause_database();
    if result == Verdict::Verified {
        Ok(0)
    } else {
        Ok(1)
    }
}

fn parse_files(config: &Config) -> RuntimeResult<Proof> {
    let mut parse_info = ParsingInfo::new();
    {
        let mut parser = Parser::new(
            parse_info,
            &config.formula_filename,
            SyntaxFormat::Dimacs,
            BinaryMode::Text,
        )?;
        parse_info = parser.parse()?;
    }
    {
        let mut parser = Parser::new(
            parse_info,
            &config.proof_filename,
            SyntaxFormat::from(config.proof_format),
            config.binary_mode,
        )?;
        parse_info = parser.parse()?;
    }
    Ok(parse_info.extract())
}
