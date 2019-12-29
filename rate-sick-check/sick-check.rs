//! Verify SICK certificates of proof incorrectness produced by rate

use clap::Arg;
use std::io::Read;
use toml;

use rate_common::{
    die,
    output::{install_signal_handler, print_solution},
    parser::open_file,
    sick::{check_incorrectness_certificate, Sick},
};

fn main() -> Result<(), ()> {
    install_signal_handler();
    let app = clap::App::new("sick-check")
        .version(env!("CARGO_PKG_VERSION"))
        .about("Verify SICK certificates stating why a DRAT proof is incorrect")
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
            Arg::with_name("CERTIFICATE")
                .required(true)
                .help("falsifying certificate file in SICK format"),
        );
    let matches = app.get_matches();
    let formula_filename = matches.value_of("INPUT").unwrap();
    let proof_filename = matches.value_of("PROOF").unwrap();
    let sick_filename = matches.value_of("CERTIFICATE").unwrap();

    let mut toml_str = String::new();
    let mut sick_file = open_file(sick_filename);
    sick_file
        .read_to_string(&mut toml_str)
        .unwrap_or_else(|err| die!("Failed to read SICK file: {}", err));
    let sick: Sick =
        toml::from_str(&toml_str).unwrap_or_else(|err| die!("Failed to parse SICK file: {}", err));
    check_incorrectness_certificate(
        formula_filename,
        proof_filename,
        sick,
        /*verbose=*/ true,
    )
    .map(|()| print_solution("VERIFIED"))
}
