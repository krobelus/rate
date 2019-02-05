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
mod config;
mod assignment;
mod checker;
mod clause;
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
    parser::parse_files,
};

fn run_checker(config: Config) -> (bool, Checker) {
    let parser = parse_files(&config.formula_filename, &config.proof_filename);

    let mut checker = Checker::new(parser, config);
    let ok = check(&mut checker);
    (ok, checker)
}

#[cfg_attr(feature = "flame_it", flame)]
fn main() {
    let mut app = clap::App::new("rate")
    .version(env!("CARGO_PKG_VERSION"))
    .about(env!("CARGO_PKG_DESCRIPTION"))
    .arg(Arg::with_name("INPUT").required(true).help("input file in DIMACS format"))
    .arg(Arg::with_name("PROOF").required(true).help("proof file in DRAT format"))

    .arg(Arg::with_name("SKIP_DELETIONS").short("d").long("skip-deletions")
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
         .help("Try to be compatible with drat-trim.\nThis implies --skip-deletions and --noncore-rat-candidates"))
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
    if !config::DISABLE_CHECKS_AND_LOGGING {
        app = app.arg(
            Arg::with_name("v")
                .short("v")
                .multiple(true)
                .help("Set the verbosity level (use up to four times)"),
        );
    }

    let config = Config::new(app.get_matches());
    let start = SystemTime::now();
    let (ok, checker) = run_checker(config);
    echo!(
        "c Elapsed time: {} seconds",
        start.elapsed().expect("failed to get time").as_secs()
    );
    echo!("c premise-clauses: {}", checker.premise_length);
    echo!("c proof-steps: {}", checker.proof.size());
    echo!("c skipped-tautologies: {}", checker.satisfied_count);
    echo!("c rup-introductions: {}", checker.rup_introductions);
    echo!("c rat-introductions: {}", checker.rat_introductions);
    echo!("c clause-deletions: {}", checker.clause_deletions);
    // echo!("c skipped-deletions {}", checker.skipped_deletions);
    echo!("c reason-deletions: {}", checker.reason_deletions);
    echo!("c assignment-count: {}", checker.assign_count);
    echo!("s {}", if ok { "ACCEPTED" } else { "REJECTED" });
    #[cfg(feature = "flame_it")]
    flame::dump_html(&mut std::fs::File::create("flame-graph.html").unwrap()).unwrap();
    process::exit(if ok { 0 } else { 1 });
}
