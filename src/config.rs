//! Compile time and run time configuration

use crate::parser::BinaryMode;
use clap::ArgMatches;
use libc::{self, signal};

#[derive(Debug, Copy, Clone)]
pub enum ProofFormat {
    DratFirstPivot,
    DratAnyPivot,
    DprFirstPivot,
    DprAnyPivot,
    Dsr,
}
impl ProofFormat {
    pub fn sick_id(&self) -> &str {
        match self {
            ProofFormat::DratFirstPivot => "DRAT-pivot-is-first-literal",
            ProofFormat::DratAnyPivot => "DRAT-arbitrary-pivot",
            ProofFormat::DprFirstPivot => "DPR-pivot-is-first-literal",
            ProofFormat::DprAnyPivot => "DPR-arbitrary-pivot",
            ProofFormat::Dsr => "DSR",
        }
    }
    pub fn rat_first_pivot(&self) -> bool {
        match self {
            ProofFormat::DratFirstPivot | ProofFormat::DprFirstPivot => true,
            _ => false,
        }
    }
    pub fn rat_any_pivot(&self) -> bool {
        match self {
            ProofFormat::DratAnyPivot | ProofFormat::DprAnyPivot => true,
            _ => false,
        }
    }
    pub fn drat(&self) -> bool {
        match self {
            ProofFormat::DratFirstPivot | ProofFormat::DratAnyPivot => true,
            _ => false,
        }
    }
    pub fn dpr(&self) -> bool {
        match self {
            ProofFormat::DprFirstPivot | ProofFormat::DprAnyPivot => true,
            _ => false,
        }
    }
    pub fn dsr(&self) -> bool {
        match self {
            ProofFormat::Dsr => true,
            _ => false,
        }
    }
}

/// Parsed arguments. See `rate --help` or `main.rs`.
#[derive(Debug)]
pub struct Config {
    pub skip_unit_deletions: bool,
    pub unmarked_rat_candidates: bool,
    pub no_terminating_empty_clause: bool,
    pub proof_format: ProofFormat,
    pub memory_usage_breakdown: bool,
    pub binary_mode: BinaryMode,
    pub forward: bool,
    pub verbosity: u64,
    pub formula_filename: String,
    pub proof_filename: String,
    pub lemmas_filename: Option<String>,
    pub lrat_filename: Option<String>,
    pub grat_filename: Option<String>,
    pub sick_filename: Option<String>,
}

/// Add command line flag `-v`.
pub const ENABLE_LOGGING: bool = true;
/// Whether to do bounds checking when accessing array elements.
pub const ENABLE_BOUNDS_CHECKING: bool = cfg!(debug_assertions);
/// Check the `requires!()` assertions at runtime (cheap).
pub const CHECK_PRECONDITIONS: bool = true;
/// Check the `invariant!()` assertions at runtime (cheap).
pub const CHECK_INVARIANTS: bool = true;
/// Sanity-check assignment/trail (expensive).
pub const CHECK_TRAIL_INVARIANTS: bool = cfg!(debug_assertions);
/// Check correctness of watches (very expensive).
pub const CHECK_WATCH_INVARIANTS: bool = false;

/// Our version of `std::unreachable()`, unsafe if invariants are disabled.
pub fn unreachable() -> ! {
    invariant!(false, "unreachable");
    unsafe { std::hint::unreachable_unchecked() }
}

/// Report an error due to invalid parameters.
fn incompatible_options(what: &str) {
    die!("incompatible options: {}", what);
}

// #[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
// pub enum RedundancyProperty {
//     RAT,
//     PR,
// }
//
// impl fmt::Display for RedundancyProperty {
//     fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
//         write!(
//             f,
//             "{}",
//             match self {
//                 RedundancyProperty::RAT => "RAT",
//                 RedundancyProperty::PR => "PR",
//             }
//         )
//     }
// }

/// We handle SIGPIPE ourselves to avoid printing errors.
pub fn signals() {
    assert!(unsafe { signal(libc::SIGPIPE, libc::SIG_DFL) } != libc::SIG_ERR);
}

impl Config {
    /// Create a config from commandline arguments.
    pub fn new(matches: ArgMatches) -> Config {
        let mut rat_first_pivot = matches.is_present("RAT_FIRST_PIVOT");
        let mut rat_any_pivot = matches.is_present("RAT_ANY_PIVOT");
        let mut ignore_unit_deletions = matches.is_present("SKIP_UNIT_DELETIONS");
        let mut respect_unit_deletions = matches.is_present("RESPECT_UNIT_DELETIONS");
        let mut drat_system = matches.is_present("DRAT_SYSTEM");
        let mut dpr_system = matches.is_present("DPR_SYSTEM");
        let dsr_system = matches.is_present("DSR_SYSTEM");
        let text_format = matches.is_present("TEXT_FORMAT");
        let binary_format = matches.is_present("BINARY_FORMAT");
        let mut drat_trim_format = matches.is_present("DRAT_TRIM_FORMAT");
        let prefix_format = matches.is_present("PREFIX_FORMAT");
        let mut unmarked_rat_candidates = matches.is_present("UNMARKED_RAT_CANDIDATES");
        let no_terminating_empty_clause = matches.is_present("NO_TERMINATING_EMPTY_CLAUSE");
        let forward = matches.is_present("FORWARD");
        let drat_trim = matches.is_present("DRAT_TRIM");
        let rupee = matches.is_present("RUPEE");
        let memory_usage_breakdown = matches.is_present("MEMORY_USAGE_BREAKDOWN");
        let lemmas = matches.is_present("LEMMAS_FILE");
        let lrat = matches.is_present("LRAT_FILE");
        let grat = matches.is_present("GRAT_FILE");
        let sick = matches.is_present("SICK_FILE");

        if Self::check_incompatible(&[drat_trim, rupee]) {
            incompatible_options("--drat-trim , --rupee");
        }
        if Self::check_incompatible(&[rat_any_pivot, dsr_system]) {
            incompatible_options("--rat-any-pivot , --dsr");
        }
        if Self::check_incompatible(&[rat_first_pivot, dsr_system]) {
            incompatible_options("--rat-first-pivot , --dsr");
        }
        if !text_format && !binary_format && !drat_trim_format && !prefix_format && !drat_trim {
            comment!("Flag --heuristic-binary-detect set by default");
            drat_trim_format = true;
        }
        if !drat_trim && !rupee {
            if !rat_any_pivot && !rat_first_pivot && !dsr_system {
                comment!("Flag --rat-any-pivot set by default");
                rat_any_pivot = true;
            }
            if !ignore_unit_deletions && !respect_unit_deletions {
                comment!("Flag --respect-unit-deletions set by default");
                respect_unit_deletions = true;
            }
            if !drat_system && !dpr_system && !dsr_system {
                comment!("Flag --drat set by default");
                drat_system = true;
            }
            if !text_format && !binary_format && !drat_trim_format && !prefix_format {
                comment!("Flag --heuristic-binary-detect set by default");
                drat_trim_format = true;
            }
        } else if drat_trim {
            if rat_first_pivot {
                warn!(
                    "Flag --rat-first-pivot overrides the --rat-any-pivot implied by --drat-trim"
                );
            } else {
                rat_any_pivot = true;
            }
            if respect_unit_deletions {
                warn!("Flag --respect-unit-deletions overrides the --ignore-unit-deletions implied by --drat-trim");
            } else {
                ignore_unit_deletions = true;
            }
            if drat_system {
                warn!("Flag --drat overrides the --dpr implied by --drat-trim");
            } else if dsr_system {
                warn!("Flag --dsr overrides the --dpr implied by --drat-trim");
            } else {
                dpr_system = true;
            }
            if text_format {
                warn!("Flag --text overrides the --heuristic-binary-detect implied by --drat-trim");
            } else if binary_format {
                warn!(
                    "Flag --binary overrides the --heuristic-binary-detect implied by --drat-trim"
                );
            } else if prefix_format {
                warn!("Flag --prefix-binary-detect overrides the --heuristic-binary-detect implied by --drat-trim");
            } else {
                drat_trim_format = true;
            }
            unmarked_rat_candidates = true;
        } else if rupee {
            if rat_any_pivot {
                warn!("Flag --rat-any-pivot overrides the --rat-first-pivot implied by --rupee");
            } else {
                rat_first_pivot = true;
            }
            if ignore_unit_deletions {
                warn!("Flag --ignore-unit-deletions overrides the --respect-unit-deletions implied by --rupee");
            } else {
                respect_unit_deletions = true;
            }
            if dpr_system {
                warn!("Flag --dpr overrides the --drat implied by --rupee");
            } else if dsr_system {
                warn!("Flag --dsr overrides the --drat implied by --rupee");
            } else {
                drat_system = true;
            }
        }
        if Self::check_incompatible(&[rat_first_pivot, rat_any_pivot]) {
            incompatible_options("--rat_first_pivot --rat_any_pivot");
        }
        if Self::check_incompatible(&[ignore_unit_deletions, respect_unit_deletions]) {
            incompatible_options("--ignore_unit_deletions , --respect_unit_deletions");
        }
        if Self::check_incompatible(&[drat_system, dpr_system, dsr_system]) {
            incompatible_options("--drat , --dpr , --dsr");
        }
        if Self::check_incompatible(&[text_format, binary_format, drat_trim_format, prefix_format])
        {
            incompatible_options(
                "--text , --binary , --heuristic-binary-detect , --prefix-binary-detect",
            );
        }
        if Self::check_incompatible(&[forward, lemmas]) {
            incompatible_options("--forward , --lemmas");
        }
        if Self::check_incompatible(&[forward, lrat]) {
            incompatible_options("--forward , --lrat");
        }
        if Self::check_incompatible(&[forward, grat]) {
            incompatible_options("--forward , --grat");
        }
        if Self::check_incompatible(&[forward, sick]) {
            incompatible_options("--forward , --recheck")
        }
        if Self::check_incompatible(&[grat, respect_unit_deletions]) {
            incompatible_options("--grat , --respect-unit-deletions");
        }

        let formula_filename = matches.value_of("INPUT").unwrap().to_string();
        let proof_filename = matches.value_of("PROOF").unwrap().to_string();
        let lemmas_filename = matches.value_of("LEMMAS_FILE").map(String::from);
        let lrat_filename = matches.value_of("LRAT_FILE").map(String::from);
        let grat_filename = matches.value_of("GRAT_FILE").map(String::from);
        let sick_filename = matches.value_of("SICK_FILE").map(String::from);

        let proof_format = if drat_system {
            if rat_first_pivot {
                ProofFormat::DratFirstPivot
            } else if rat_any_pivot {
                ProofFormat::DratAnyPivot
            } else {
                unreachable()
            }
        } else if dpr_system {
            if rat_first_pivot {
                ProofFormat::DprFirstPivot
            } else if rat_any_pivot {
                ProofFormat::DprAnyPivot
            } else {
                unreachable()
            }
        } else if dsr_system {
            ProofFormat::Dsr
        } else {
            unreachable()
        };
        let binary_mode = if text_format {
            BinaryMode::Text
        } else if binary_format {
            BinaryMode::Binary
        } else if drat_trim_format {
            BinaryMode::DratTrimDetection
        } else if prefix_format {
            BinaryMode::PrefixDetection
        } else {
            unreachable()
        };
        let verbosity = match matches.occurrences_of("v") {
            i if i > 4 => {
                warn!("verbosity can be at most 4");
                4
            }
            i => i,
        };
        Config {
            skip_unit_deletions: ignore_unit_deletions,
            unmarked_rat_candidates: unmarked_rat_candidates,
            no_terminating_empty_clause: no_terminating_empty_clause,
            proof_format: proof_format,
            binary_mode: binary_mode,
            memory_usage_breakdown: memory_usage_breakdown,
            forward: forward,
            verbosity: verbosity,
            formula_filename: formula_filename,
            proof_filename: proof_filename,
            lemmas_filename: lemmas_filename,
            lrat_filename: lrat_filename,
            grat_filename: grat_filename,
            sick_filename: sick_filename,
        }
    }

    fn check_incompatible(b: &[bool]) -> bool {
        let mut acc: bool = false;
        for &bb in b {
            if bb {
                if acc {
                    return true;
                } else {
                    acc = true;
                }
            }
        }
        false
    }
}
