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

use clap::Arg;
use std::process;

use crate::{
    checker::{check, Checker},
    config::Config,
    parser::parse_files,
};

fn main() {
    let matches = clap::App::new("rate")
    .version(env!("CARGO_PKG_VERSION"))
    .about(env!("CARGO_PKG_DESCRIPTION"))
    .arg(Arg::with_name("INPUT").required(true).help("input file in DIMACS format"))
    .arg(Arg::with_name("PROOF").required(true).help("proof file in DRAT format"))
    .arg(Arg::with_name("LRAT_FILE").takes_value(true).short("L").long("lrat").help("Given a correct proof, write the LRAT certificate to this file."))
    .arg(Arg::with_name("SKIP_DELETIONS").short("d").long("skip-deletions").help("Ignore deletion of unit clauses."))
    .arg(Arg::with_name("UNMARKED_RAT_CANDIDATES").short("r").long("unmarked-rat-candidates").help("Do not ignore RAT candidates that are not marked."))
    .arg(Arg::with_name("DRAT_TRIM").long("drat-trim").help("Try to be compatible with drat-trim.\nThis implies --skip-deletions and --unmarked-rat-candidates."))
    .arg(Arg::with_name("v").short("v").multiple(true).help("Set the verbosity level (use up to three times)"))
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
