//! Compile time and run time configuration

use clap::ArgMatches;
use std::fmt;

/// Parsed arguments.
#[derive(Debug)]
pub struct Config {
    pub redundancy_property: RedundancyProperty,
    pub skip_unit_deletions: bool,
    pub unmarked_rat_candidates: bool,
    pub pivot_is_first_literal: bool,
    pub memory_usage_breakdown: bool,
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
pub const ENABLE_LOGGING: bool = cfg!(debug_assertions);
/// Runtime invariant checks.
pub const ENABLE_ASSERTIONS: bool = cfg!(debug_assertions);
/// Check assignment sanity.
pub const ASSIGNMENT_INVARIANTS: bool = cfg!(debug_assertions);
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

impl Config {
    pub fn new(matches: ArgMatches) -> Config {
        let drat_trim = matches.is_present("DRAT_TRIM");
        let rupee = matches.is_present("RUPEE");
        let skip_unit_deletions = matches.is_present("SKIP_UNIT_DELETIONS");
        let unmarked_rat_candidates = matches.is_present("UNMARKED_RAT_CANDIDATES");
        let pivot_is_first_literal = matches.is_present("ASSUME_PIVOT_IS_FIRST");
        let lrat = matches.is_present("LRAT_FILE");
        let grat = matches.is_present("GRAT_FILE");
        let sick_filename = matches.value_of("SICK_FILE").map(String::from);

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
        if drat_trim && unmarked_rat_candidates {
            incompatible_options("--drat-trim --unmarked_rat_candidates");
        }
        if drat_trim && pivot_is_first_literal {
            incompatible_options("--drat-trim --assume-pivot-is-first");
        }
        let proof_filename = matches.value_of("PROOF").unwrap().to_string();
        let redundancy_property = if proof_filename.ends_with(".drat") {
            RedundancyProperty::RAT
        } else if proof_filename.ends_with(".pr") || proof_filename.ends_with(".dpr") {
            if lrat || grat {
                die!("LRAT and GRAT generation is not possible for PR")
            }
            RedundancyProperty::PR
        } else {
            comment!("unknown file extension, defaulting to RAT checking");
            RedundancyProperty::RAT
        };
        Config {
            redundancy_property,
            skip_unit_deletions: drat_trim || skip_unit_deletions,
            unmarked_rat_candidates: !drat_trim && unmarked_rat_candidates,
            pivot_is_first_literal: rupee || pivot_is_first_literal,
            memory_usage_breakdown: matches.is_present("MEMORY_USAGE_BREAKDOWN"),
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
