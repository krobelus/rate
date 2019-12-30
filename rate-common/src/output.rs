//! Unified routines to print data
//!
//! We choose to print everything to stdout. This makes sense for a
//! tool like a proof checker whose output consists of error messages
//! and diagnostics, not data. It is less suited for pure data
//! processing programs like `drat2bdrat`, however those fail only
//! on fatal errors where we cannot guarantee that they did not
//! print garbage (e.g., incomplete clauses), so the user needs
//! to handle the exit code anyway.

use atty::{self, Stream};
use libc::{self, signal};
use std::{fmt::Display, time::SystemTime};

/// The basename of the current executable.
pub fn current_executable() -> String {
    std::env::current_exe()
        .ok()
        .and_then(|abspath| {
            abspath
                .file_name()
                .map(|f| f.to_str().unwrap_or("").to_string())
        })
        .unwrap_or("".to_string())
}

/// Unwraps a result, panicking on error.
pub fn panic_on_error<T>(result: std::io::Result<T>) -> T {
    result.unwrap_or_else(|error| die!("{}: {}", current_executable(), error))
}

/// Write a solution line (`"s ..."`) to stdout.
pub fn print_solution(verdict: &str) {
    puts!("s {}\n", verdict);
}

/// Write a key-value pair to stdout.
pub fn print_key_value(key: &str, value: impl Display) {
    requires!(key.len() < 35);
    comment!("{:<35} {:>15}", format!("{}:", key), value);
}

/// We handle SIGPIPE ourselves to avoid printing errors.
pub fn install_signal_handler() {
    // You can't disable assert! in Rust so this is fine.
    assert!(unsafe { signal(libc::SIGPIPE, libc::SIG_DFL) } != libc::SIG_ERR);
}

/// Our version of `std::unreachable()`, unsafe if invariants are disabled.
pub fn unreachable() -> ! {
    invariant!(false, "unreachable");
    unsafe { std::hint::unreachable_unchecked() }
}

/// Check whether we are writing to a terminal.
pub fn is_a_tty() -> bool {
    atty::is(Stream::Stdout)
}

/// A RAII object that prints a timing message when it is destroyed.
pub struct Timer {
    /// The name of the thing that is being timed
    name: &'static str,
    /// The start time, set at construction time
    start: SystemTime,
    /// Whether this timer should be silenced
    pub disabled: bool,
}

impl Timer {
    /// Create a timer with a given name.
    pub fn name(name: &'static str) -> Timer {
        Timer {
            name,
            start: SystemTime::now(),
            disabled: false,
        }
    }
}

impl Drop for Timer {
    /// Write the elapsed time as comment.
    fn drop(&mut self) {
        if self.disabled {
            return;
        }
        let elapsed_time = self.start.elapsed().expect("failed to get time");
        print_key_value(
            &format!("{} (s)", self.name),
            format!(
                "{}.{:03}",
                elapsed_time.as_secs(),
                elapsed_time.subsec_millis()
            ),
        );
    }
}
