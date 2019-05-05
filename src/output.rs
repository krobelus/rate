//! Output routines.

use atty::{self, Stream};
use std::{fmt::Display, time::SystemTime};

/// Check whether we are writing to a terminal.
pub fn is_a_tty() -> bool {
    atty::is(Stream::Stdout)
}

macro_rules! write_to_stdout {
    ($($arg:tt)*) => ({
        use std::io::Write;
        match write!(std::io::stdout(), $($arg)*) {
            Ok(()) => (),
            Err(ref err) if err.kind() == std::io::ErrorKind::BrokenPipe =>  std::process::exit(141),
            Err(ref err) =>  panic!("{}", err),
        };
    })
}

macro_rules! _log {
    ($verbosity:expr, $level:expr, $($arg:tt)*) => {
        if crate::config::ENABLE_LOGGING && $level <= $verbosity
        {
            write_to_stdout!($($arg)*);
            write_to_stdout!("\n");
        }
    };
}

// Print based on verbosity level
macro_rules! log {
    ($checker:expr, $level:expr, $($arg:tt)*) => {
        _log!($checker.config.verbosity, $level, $($arg)*)
    };
}

// Print upon scope exit.
// We need this macro to avoid borrowing $checker.
macro_rules! defer_log {
    ($checker:expr, $level:expr, $($arg:tt)*) => {
        let verbosity = $checker.config.verbosity;
        defer!(
            _log!(verbosity, $level, $($arg)*)
            );
    }
}

// Print in red.
macro_rules! warn {
    ($($arg:tt)*) => ({
        let style = if crate::output::is_a_tty() {
            ansi_term::Colour::Yellow.normal()
        } else {
            ansi_term::Style::default()
        };
        write_to_stdout!("{}", style.paint("Warning: "));
        write_to_stdout!("{}\n", style.paint(&format!($($arg)*)));
    })
}

// Report a fatal error and exit.
macro_rules! die {
    ($($arg:tt)*) => ({
        let style = if crate::output::is_a_tty() {
            ansi_term::Colour::Red.normal()
        } else {
            ansi_term::Style::default()
        };
        write_to_stdout!("{}", style.paint("Error: "));
        write_to_stdout!("{}\n", style.paint(&format!($($arg)*)));
        std::process::exit(2);
    })
}

// Native assertions cannot be disabled, that's why why prefer to use this
// macro.
#[macro_export]
macro_rules! invariant {
    ($($arg:tt)*) => ({
        if crate::config::ENABLE_ASSERTIONS {
            assert!($($arg)*);
        }
    })
}

// Preconditions should use this instead of an invariant.
macro_rules! requires {
    ($($arg:tt)*) => ({
        if crate::config::ENABLE_ASSERTIONS {
            assert!($($arg)*);
        }
    })
}

// Print to stdout.
macro_rules! comment {
    ($($arg:tt)*) => ({
        write_to_stdout!("c ");
        write_to_stdout!($($arg)*);
        write_to_stdout!("\n");
    })
}

pub fn solution(verdict: &str) {
    write_to_stdout!("s {}\n", verdict);
}

pub fn value(key: &str, value: impl Display) {
    requires!(key.len() < 35);
    comment!("{:<35} {:>15}", format!("{}:", key), value);
}

pub struct Timer {
    name: &'static str,
    start: SystemTime,
    pub disabled: bool,
}

impl Timer {
    pub fn name(name: &'static str) -> Timer {
        Timer {
            name,
            start: SystemTime::now(),
            disabled: false,
        }
    }
}

impl Drop for Timer {
    fn drop(&mut self) {
        if self.disabled {
            return;
        }
        let elapsed_time = self.start.elapsed().expect("failed to get time");
        value(
            &format!("{} (s)", self.name),
            format!(
                "{}.{:03}",
                elapsed_time.as_secs(),
                elapsed_time.subsec_millis()
            ),
        );
    }
}
