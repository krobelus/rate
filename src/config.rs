//! Compile time and run time configuration

use clap::ArgMatches;
use libc::{self, signal};
use std::fmt;

/// Parsed arguments.
#[derive(Debug)]
pub struct Config {
    pub skip_unit_deletions: bool,
    pub unmarked_rat_candidates: bool,
    pub pivot_is_first_literal: bool,
    pub no_terminating_empty_clause: bool,
    pub memory_usage_breakdown: bool,
    pub forward: bool,
    pub verbosity: u64,
    pub formula_filename: String,
    pub proof_filename: String,
    pub lemmas_filename: Option<String>,
    pub lrat_filename: Option<String>,
    pub grat_filename: Option<String>,
    pub sick_filename: Option<String>,
}

/// Whether to do bounds checking when accessing array elements.
pub const ENABLE_BOUNDS_CHECKING: bool = cfg!(debug_assertions);
/// Add command line flag `-v`.
pub const ENABLE_LOGGING: bool = true;
/// Runtime invariant checks.
pub const ENABLE_ASSERTIONS: bool = cfg!(debug_assertions);
/// Check assignment sanity.
pub const ASSIGNMENT_INVARIANTS: bool = false;
/// Check correctness of watches.
pub const WATCH_INVARIANTS: bool = false;

pub fn unreachable() -> ! {
    invariant!(false, "unreachable");
    unsafe { std::hint::unreachable_unchecked() }
}

fn incompatible_options(what: &str) {
    die!("incompatible options: {}", what);
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum RedundancyProperty {
    RAT,
    PR,
}

impl fmt::Display for RedundancyProperty {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{}",
            match self {
                RedundancyProperty::RAT => "RAT",
                RedundancyProperty::PR => "PR",
            }
        )
    }
}

pub fn signals() {
    assert!(unsafe { signal(libc::SIGPIPE, libc::SIG_DFL) } != libc::SIG_ERR);
}

impl Config {
    pub fn new(matches: ArgMatches) -> Config {
        let drat_trim = matches.is_present("DRAT_TRIM");
        let rupee = matches.is_present("RUPEE");
        let skip_unit_deletions = matches.is_present("SKIP_UNIT_DELETIONS");
        let unmarked_rat_candidates = matches.is_present("UNMARKED_RAT_CANDIDATES");
        let pivot_is_first_literal = matches.is_present("ASSUME_PIVOT_IS_FIRST");
        let forward = matches.is_present("FORWARD");
        let lrat = matches.is_present("LRAT_FILE");
        let grat = matches.is_present("GRAT_FILE");
        let sick_filename = matches.value_of("SICK_FILE").map(String::from);

        if forward {
            if grat {
                incompatible_options("--forward --grat");
            }
            if lrat {
                incompatible_options("--forward --lrat");
            }
            if sick_filename.is_some() {
                incompatible_options("--forward --recheck");
            }
        }
        if skip_unit_deletions && sick_filename.is_some() {
            warn!(
                "--recheck can produce an incorrect SICK witness when used along --skip-unit-deletions."
            );
        }
        if !skip_unit_deletions && grat {
            warn!("GRAT does not support unit deletions, I might generated invalid certificates.");
        }
        if rupee && skip_unit_deletions {
            incompatible_options("--rupee --skip-unit-deletions");
        }
        if rupee && unmarked_rat_candidates {
            incompatible_options("--rupee --unmarked_rat_candidates");
        }
        if drat_trim && pivot_is_first_literal {
            incompatible_options("--drat-trim --assume-pivot-is-first");
        }
        let proof_filename = matches.value_of("PROOF").unwrap().to_string();
        Config {
            skip_unit_deletions: drat_trim || skip_unit_deletions,
            unmarked_rat_candidates: rupee || unmarked_rat_candidates,
            pivot_is_first_literal: rupee || pivot_is_first_literal,
            no_terminating_empty_clause: matches.is_present("NO_TERMINATING_EMPTY_CLAUSE"),
            memory_usage_breakdown: matches.is_present("MEMORY_USAGE_BREAKDOWN"),
            forward,
            verbosity: match matches.occurrences_of("v") {
                i if i > 4 => {
                    warn!("verbosity can be at most 4");
                    4
                }
                i => i,
            },
            formula_filename: matches.value_of("INPUT").unwrap().to_string(),
            proof_filename,
            lemmas_filename: matches.value_of("LEMMAS_FILE").map(String::from),
            lrat_filename: matches.value_of("LRAT_FILE").map(String::from),
            grat_filename: matches.value_of("GRAT_FILE").map(String::from),
            sick_filename,
        }
    }
}
