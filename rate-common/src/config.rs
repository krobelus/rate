//! Compile-time constants

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
