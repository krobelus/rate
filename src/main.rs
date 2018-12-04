#[macro_use]
extern crate nom;
#[macro_use]
extern crate derive_more;
#[macro_use]
extern crate clap;

#[macro_use]
mod config;
mod assignment;
mod checker;
mod clause;
mod literal;
mod memory;
mod parser;

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
    (@arg SKIP_DELETIONS: -d long("skip-deletions") "Ignore deletion of unit clauses, as does drat-trim")
    (@arg TRACE: -t --trace "Outputs a trace of the execution")
    )
    .get_matches();

    let parser = parse_files(
        matches.value_of("INPUT").unwrap(),
        matches.value_of("PROOF").unwrap(),
    );

    let mut checker = Checker::new(parser, Config::new(matches));
    let ok = check(&mut checker);
    echo!("s {}", if ok { "ACCEPTED" } else { "REJECTED" });
    process::exit(if ok { 0 } else { 1 });
}
