#[macro_use(defer)]
extern crate scopeguard;

#[macro_use]
mod config;
mod assignment;
mod checker;
mod clause;
mod literal;
mod memory;
mod parser;

use clap::clap_app;
use std::process;

use crate::{
    checker::{check, Checker},
    config::Config,
    parser::parse_files,
};

fn main() {
    let matches = clap_app!(rate =>
    (version: env!("CARGO_PKG_VERSION"))
    (about: env!("CARGO_PKG_DESCRIPTION"))
    (@arg INPUT: +required "input file in DIMACS format")
    (@arg PROOF: +required "proof file in DRAT format")
    (@arg LRAT_FILE: +takes_value -L "Given a correct proof, write the LRAT certificate to this file.")
    (@arg SKIP_DELETIONS: -d long("skip-deletions") "Ignore deletion of unit clauses.")
    (@arg UNMARKED_RAT_CANDIDATES: -r long("unmarked-rat-candidates")  "Do not ignore RAT candidates that are not marked.")
    (@arg DRAT_TRIM: long("drat-trim")  "Try to be compatible with drat-trim.\nThis implies --skip-deletions and --unmarked-rat-candidates.")
    (@arg TRACE: -t --trace "Output a trace of the execution")
    )
    .get_matches();

    let parser = parse_files(
        matches.value_of("INPUT").unwrap(),
        matches.value_of("PROOF").unwrap(),
    );

    let mut checker = Checker::new(parser, Config::new(matches));
    let ok = check(&mut checker);
    echo!("c propcount {}", checker.propcount);
    echo!("s {}", if ok { "ACCEPTED" } else { "REJECTED" });
    process::exit(if ok { 0 } else { 1 });
}
