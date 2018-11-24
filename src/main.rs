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
mod formula;
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
    (author: env!("CARGO_PKG_AUTHORS"))
    (about: env!("CARGO_PKG_DESCRIPTION"))
    (@arg INPUT: +required "input file in DIMACS format")
    (@arg PROOF: +required "proof file in DRAT format")
    (@arg TRACE: -t --trace "Outputs a trace of the execution")
    )
    .get_matches();

    let (mut formula, proof) = parse_files(
        matches.value_of("INPUT").unwrap(),
        matches.value_of("PROOF").unwrap(),
    );

    let mut checker = Checker::new(&formula, Config::new(matches));
    trace!(checker, "proof_start: {}\n", formula.proof_start);
    let ok = check(&mut formula, &proof, &mut checker);
    trace!(checker, "proof_start: {}\n", formula.proof_start);
    trace!(checker, "propcount: {}\n", checker.propcount);
    trace!(checker, "ratcalls: {}\n", checker.ratcalls);
    trace!(checker, "rupcalls: {}\n", checker.rupcalls);
    echo!("s {}", if ok { "ACCEPTED" } else { "REJECTED" });
    process::exit(if ok { 0 } else { 1 });
}
