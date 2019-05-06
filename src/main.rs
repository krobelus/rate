//! Rate is a proof checker for DRAT proofs which are commonly used to certify
//! unsatisfiability of SAT formulas.

#![feature(
    try_trait,
    alloc,
    ptr_wrapping_offset_from,
    raw_vec_internals,
    range_contains,
    const_vec_new,
    vec_resize_default,
    result_map_or_else,
    stmt_expr_attributes,
    existential_type,
    try_from
)]
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
mod literal;
mod parser;
mod sick;

#[macro_use(defer)]
extern crate scopeguard;
extern crate alloc;
#[macro_use(Serialize, Deserialize)]
extern crate serde_derive;

use clap::Arg;
use std::process;

use crate::{
    checker::{check, Checker, Verdict},
    config::Config,
    output::{solution, value, Timer},
    parser::parse_files,
};

fn main() {
    crate::config::signals();
    let mut app = clap::App::new("rate")
    .version(concat!(env!("CARGO_PKG_VERSION"), " (git commit ", env!("GIT_COMMIT"), ")"))
    .about(env!("CARGO_PKG_DESCRIPTION"))
    .arg(Arg::with_name("INPUT").required(true).help("input file in DIMACS format"))
    .arg(Arg::with_name("PROOF").required(true).help("proof file in DRAT format"))

    .arg(Arg::with_name("SKIP_UNIT_DELETIONS").short("d").long("skip-unit-deletions")
         .help("Ignore deletion of unit clauses."))
    .arg(Arg::with_name("UNMARKED_RAT_CANDIDATES").short("r").long("noncore-rat-candidates")
         .help("Do not ignore RAT candidates that are not part of the core."))
    .arg(Arg::with_name("ASSUME_PIVOT_IS_FIRST").short("p").long("assume-pivot-is-first")
         .help("When checking for RAT, only try the first literal as pivot."))
    .arg(Arg::with_name("NO_TERMINATING_EMPTY_CLAUSE").long("--no-terminating-empty-clause")
        .help("Do not assume an implied empty clause at the end of the proof"))
    .arg(Arg::with_name("FORWARD").short("f").long("forward")
         .help("Use naive forward checking."))

    .arg(Arg::with_name("DRAT_TRIM").long("drat-trim")
         .help("Try to be compatible with drat-trim.\nThis implies --skip-unit-deletions and --noncore-rat-candidates"))
    .arg(Arg::with_name("RUPEE").long("--rupee")
         .help("Try to be compatible with rupee.\nThis implies --assume-pivot-is-first"))
    .arg(Arg::with_name("MEMORY_USAGE_BREAKDOWN").short("m").long("--memory-breakdown")
         .help("Output detailled memory usage."))
    .arg(Arg::with_name("LEMMAS_FILE").takes_value(true).short("l").long("lemmas")
         .help("Write the core lemmas to this file."))
    .arg(Arg::with_name("LRAT_FILE").takes_value(true).short("L").long("lrat")
         .help("Write the core lemmas as LRAT certificate to this file."))
    .arg(Arg::with_name("GRAT_FILE").takes_value(true).short("G").long("grat")
         .help("Write the GRAT certificate to this file."))
    .arg(Arg::with_name("SICK_FILE").takes_value(true).short("i").long("recheck")
         .help("Write the recheck incorrectness witness."))
    ;

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
    let parser = parse_files(
        &config.formula_filename,
        &config.proof_filename,
        config.no_terminating_empty_clause,
    );
    if parser.is_pr() {
        if config.lrat_filename.is_some() || config.grat_filename.is_some() {
            die!("LRAT and GRAT generation is not possible for PR")
        }
    }
    let mut checker = Checker::new(parser, config);
    let result = check(&mut checker);
    value("premise clauses", checker.premise_length);
    value("proof steps", checker.proof.size());
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
    process::exit(if result == Verdict::Verified { 0 } else { 1 });
}
