//! Compile-time and runtime configuration, plus macros

use atty::{self, Stream};
use clap::ArgMatches;

#[derive(Debug)]
pub struct Config {
    pub skip_deletions: bool,
    pub unmarked_rat_candidates: bool,
    pub pivot_is_first_literal: bool,
    pub no_core_first: bool,
    pub check_satisfied_lemmas: bool,
    pub lratcheck_compat: bool,
    pub verbosity: u64,
    pub formula_filename: String,
    pub proof_filename: String,
    pub lemmas_filename: Option<String>,
    pub lrat_filename: Option<String>,
    pub sick_filename: Option<String>,
}

pub const DISABLE_CHECKS_AND_LOGGING: bool = cfg!(feature = "fast");

macro_rules! enabled {
    ($ok:expr) => {
        $ok && !DISABLE_CHECKS_AND_LOGGING
    };
}

pub const BOUNDS_CHECKING: bool = enabled!(true);
pub const ASSERTIONS: bool = enabled!(true);
pub const LOGGING: bool = enabled!(true);
pub const COSTLY_INVARIANT_CHECKING: bool = enabled!(cfg!(debug));

// print to stdout
macro_rules! echo {
    ($($arg:tt)*) => ({
        println!($($arg)*);
    })
}

// print based on verbosity level
macro_rules! _log {
    ($verbosity:expr, $level:expr, $($arg:tt)*) => {
        if crate::config::LOGGING && $level <= $verbosity
        {
            print!($($arg)*);
            print!("\n");
        }
    };
}

macro_rules! log {
    ($checker:expr, $level:expr, $($arg:tt)*) => {
        _log!($checker.config.verbosity, $level, $($arg)*)
    };
}

// Trace upon scope exit without borrowing
macro_rules! defer_log {
    ($checker:expr, $level:expr, $($arg:tt)*) => {
        let verbosity = $checker.config.verbosity;
        defer!(
            _log!(verbosity, $level, $($arg)*)
            );
    }
}

pub fn is_a_tty() -> bool {
    atty::is(Stream::Stdout)
}

// Print in red.
macro_rules! warn {
    ($($arg:tt)*) => ({
        let style = if crate::config::is_a_tty() {
            ansi_term::Colour::Yellow.normal()
        } else {
            ansi_term::Style::default()
        };
        print!("{}", style.paint("Warning: "));
        println!("{}", style.paint(&format!($($arg)*)));
    })
}

macro_rules! die {
    ($($arg:tt)*) => ({
        let style = if crate::config::is_a_tty() {
            ansi_term::Colour::Red.normal()
        } else {
            ansi_term::Style::default()
        };
        print!("{}", style.paint("Error: "));
        println!("{}", style.paint(&format!($($arg)*)));
        std::process::exit(2);
    })
}

macro_rules! invariant {
    ($($arg:tt)*) => ({
        if crate::config::ASSERTIONS {
            assert!($($arg)*);
        }
    })
}

macro_rules! requires {
    ($($arg:tt)*) => ({
        if crate::config::ASSERTIONS {
            assert!($($arg)*);
        }
    })
}

pub fn unreachable() -> ! {
    invariant!(false, "unreachable");
    unsafe { std::hint::unreachable_unchecked() }
}

fn incompatible_options(what: &str) {
    die!("incompatible options: {}", what);
}

impl Config {
    pub fn new(matches: ArgMatches) -> Config {
        let drat_trim = matches.is_present("DRAT_TRIM");
        let rupee = matches.is_present("RUPEE");
        let skip_deletions = matches.is_present("SKIP_DELETIONS");
        let unmarked_rat_candidates = matches.is_present("UNMARKED_RAT_CANDIDATES");
        let pivot_is_first_literal = matches.is_present("ASSUME_PIVOT_IS_FIRST");
        let check_satisfied_lemmas = matches.is_present("CHECK_SATISFIED_LEMMAS");
        let lratcheck_compat = matches.is_present("LRATCHECK_COMPAT");
        let sick_filename = matches.value_of("SICK_FILE").map(String::from);

        if lratcheck_compat {
            warn!("option --lratcheck-compat is most likely broken.");
        }
        if skip_deletions && sick_filename.is_some() {
            warn!("--recheck can produce an incorrect SICK witness when used along --skip-deletions.");
        }
        if rupee && skip_deletions {
            incompatible_options("--rupee --skip-deletions");
        }
        if drat_trim && unmarked_rat_candidates {
            incompatible_options("--drat-trim --unmarked_rat_candidates");
        }
        if drat_trim && pivot_is_first_literal {
            incompatible_options("--drat-trim --assume-pivot-is-first");
        }
        if drat_trim && lratcheck_compat {
            incompatible_options("--drat-trim --lratcheck_compat");
        }
        Config {
            skip_deletions: drat_trim || skip_deletions,
            unmarked_rat_candidates: !drat_trim && unmarked_rat_candidates,
            pivot_is_first_literal: rupee || pivot_is_first_literal,
            no_core_first: matches.is_present("NO_CORE_FIRST"),
            check_satisfied_lemmas: rupee || check_satisfied_lemmas,
            lratcheck_compat: lratcheck_compat,
            verbosity: match matches.occurrences_of("v") {
                i if i > 4 => {
                    warn!("verbosity can be at most 3");
                    4
                }
                i => i,
            },
            formula_filename: matches.value_of("INPUT").unwrap().to_string(),
            proof_filename: matches.value_of("PROOF").unwrap().to_string(),
            lemmas_filename: matches.value_of("LEMMAS_FILE").map(String::from),
            lrat_filename: matches.value_of("LRAT_FILE").map(String::from),
            sick_filename: sick_filename,
        }
    }
}
