//! Rate is a proof checker for DRAT proofs which are commonly used to certify
//! unsatisfiability of SAT formulas.

#![feature(
    try_trait,
    alloc,
    ptr_wrapping_offset_from,
    raw_vec_internals,
    const_vec_new,
    stmt_expr_attributes
)]

#[macro_use(defer)]
extern crate scopeguard;
extern crate alloc;

#[macro_use]
mod output;
mod assignment;
mod checker;
mod clause;
mod clausedatabase;
mod config;
mod literal;
mod memory;
mod parser;

use clap::Arg;
#[cfg(feature = "flame_it")]
use flamer::flame;
use std::{process, time::SystemTime};

use crate::{
    checker::{check, Checker},
    config::Config,
    output::{number, solution},
    parser::parse_files,
};

#[cfg_attr(feature = "flame_it", flame)]
fn main() {
    let mut app = clap::App::new("rate")
    .version(env!("CARGO_PKG_VERSION"))
    .about(env!("CARGO_PKG_DESCRIPTION"))
    .arg(Arg::with_name("INPUT").required(true).help("input file in DIMACS format"))
    .arg(Arg::with_name("PROOF").required(true).help("proof file in DRAT format"))

    .arg(Arg::with_name("SKIP_UNIT_DELETIONS").short("d").long("skip-unit-deletions")
         .help("Ignore deletion of unit clauses."))
    .arg(Arg::with_name("UNMARKED_RAT_CANDIDATES").short("r").long("noncore-rat-candidates")
         .help("Do not ignore RAT candidates that are not part of the core."))
    .arg(Arg::with_name("ASSUME_PIVOT_IS_FIRST").long("assume-pivot-is-first")
         .help("When checking for RAT, only try the first literal as pivot."))
    .arg(Arg::with_name("NO_CORE_FIRST").short("u").long("no-core-first")
         .help("Disable core first unit propagation."))
    .arg(Arg::with_name("CHECK_SATISFIED_LEMMAS").short("s").long("check-satisfied-lemmas")
         .help("Do not skip lemmas that are satisfied by the partial UP-model."))

    .arg(Arg::with_name("DRAT_TRIM").long("drat-trim")
         .help("Try to be compatible with drat-trim.\nThis implies --skip-unit-deletions and --noncore-rat-candidates"))
    .arg(Arg::with_name("RUPEE").long("--rupee")
         .help("Try to be compatible with rupee.\nThis implies --assume-pivot-is-first"))
    .arg(Arg::with_name("LRATCHECK_COMPAT").long("--lratcheck-compat")
         .help("Try output LRAT suitable for lratcheck (as opposed to the verified lrat-check)"))
    .arg(Arg::with_name("LEMMAS_FILE").takes_value(true).short("l").long("lemmas")
         .help("Write the core lemmas to this file."))
    .arg(Arg::with_name("LRAT_FILE").takes_value(true).short("L").long("lrat")
         .help("Write the core lemmas as LRAT certificate to this file."))
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
    let start = SystemTime::now();
    let parser = parse_files(&config.formula_filename, &config.proof_filename);
    parser.print_memory_usage();
    let mut checker = Checker::new(parser, config);
    checker.print_memory_usage();
    let ok = check(&mut checker);
    comment!(
        "elapsed time: {} seconds",
        start.elapsed().expect("failed to get time").as_secs()
    );
    number("premise-clauses", checker.premise_length);
    number("proof-steps", checker.proof.size());
    number("skipped-tautologies", checker.satisfied_count);
    number("rup-introductions", checker.rup_introductions);
    number("rat-introductions", checker.rat_introductions);
    number("deletions", checker.deletions);
    number("skipped-deletion", checker.skipped_deletions);
    number("reason-deletions", checker.reason_deletions);
    number("assignment-count", checker.assign_count);
    solution(if ok { "VERIFIED" } else { "NOT VERIFIED" });
    #[cfg(feature = "flame_it")]
    flame::dump_html(&mut std::fs::File::create("flame-graph.html").unwrap()).unwrap();
    process::exit(if ok { 0 } else { 1 });
}
