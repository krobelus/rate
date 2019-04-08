//! Data structures for the checker.

use crate::memory::Offset;
use derive_more::Add;
use static_assertions::{assert_eq_size, const_assert};
use std::{
    fmt,
    mem::size_of,
    ops::{Add, AddAssign, Sub, SubAssign},
};

/// The index of a clause or lemma, immutable during the lifetime of the program.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Add, Hash, Default)]
pub struct Clause {
    pub index: u64,
}

impl Clause {
    pub fn new(index: u64) -> Clause {
        requires!(index <= Clause::MAX_INDEX);
        Clause { index }
    }
    pub fn range(start: impl Offset, end: impl Offset) -> impl Iterator<Item = Clause> {
        assert_eq_size!(usize, u64);
        (start.as_offset()..end.as_offset()).map(|offset| Clause::new(offset as u64))
    }
    const MAX_INDEX: u64 = Tagged64::MAX_PAYLOAD - 1;
    pub const NEVER_READ: Clause = Clause {
        index: Clause::MAX_INDEX + 1,
    };
    pub const DOES_NOT_EXIST: Clause = Clause {
        index: Clause::MAX_INDEX + 1,
    };
    pub const UNINITIALIZED: Clause = Clause {
        index: Clause::MAX_INDEX + 1,
    };
}

impl Offset for Clause {
    fn as_offset(&self) -> usize {
        self.index as usize
    }
}

impl Add<u64> for Clause {
    type Output = Clause;
    fn add(self, value: u64) -> Clause {
        Clause::new(self.index + value)
    }
}

impl AddAssign<u64> for Clause {
    fn add_assign(&mut self, value: u64) {
        self.index += value;
    }
}

impl Sub<u64> for Clause {
    type Output = Clause;
    fn sub(self, value: u64) -> Clause {
        Clause::new(self.index - value)
    }
}

impl SubAssign<u64> for Clause {
    fn sub_assign(&mut self, value: u64) {
        self.index -= value;
    }
}

impl fmt::Display for Clause {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.index)
    }
}

/// ```
/// enum ProofStep {
///     Lemma(Clause),
///     Deletion(Clause),
/// }
/// ```
#[derive(Debug, PartialEq, Eq, Clone, Copy, Default)]
pub struct ProofStep(Tagged64);

impl ProofStep {
    pub fn lemma(clause: Clause) -> ProofStep {
        ProofStep(Tagged64::new(clause.index))
    }
    pub fn deletion(clause: Clause) -> ProofStep {
        ProofStep(Tagged64::new(clause.index).with_bit1())
    }
    pub fn is_deletion(self) -> bool {
        self.0.bit1()
    }
    pub fn clause(self) -> Clause {
        Clause {
            index: self.0.payload(),
        }
    }
}

/// ```
/// enum Reason {
///     Assumed,
///     Forced(usize),
/// }
/// ```

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Reason(Tagged64);

impl Reason {
    pub fn invalid() -> Reason {
        Reason(Tagged64::new(0))
    }
    pub fn assumed() -> Reason {
        Reason(Tagged64::new(0).with_bit1())
    }
    pub fn forced(offset: usize) -> Reason {
        Reason(Tagged64::new(offset as u64).with_bit1().with_bit2())
    }
    pub fn is_assumed(self) -> bool {
        invariant!(self != Reason::invalid());
        !self.0.bit2()
    }
    pub fn offset(self) -> usize {
        invariant!(self != Reason::invalid());
        invariant!(self != Reason::assumed());
        self.0.payload() as usize
    }
}

impl fmt::Display for Reason {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{}",
            if self.is_assumed() {
                "Assumption".into()
            } else {
                format!("Forced by clause {}", self.offset())
            }
        )
    }
}

/// NOTE: This should be 64 bits but we want to be comparable to drat-trim so 32 it is.
/// ```
/// enum LRATDependency {
///     Unit(Clause),
///     ForcedUnit(Clause),
///     ResolutionCandidate(Clause),
/// }
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Default)]
pub struct LRATDependency(Tagged32);

impl LRATDependency {
    pub fn unit(clause: Clause) -> LRATDependency {
        LRATDependency(Tagged32::new(clause.index as u32))
    }
    pub fn is_unit(self) -> bool {
        !self.0.bit1() && !self.0.bit2()
    }
    pub fn forced_unit(clause: Clause) -> LRATDependency {
        LRATDependency(Tagged32::new(clause.index as u32).with_bit1())
    }
    pub fn is_forced_unit(self) -> bool {
        self.0.bit1() && !self.0.bit2()
    }
    pub fn resolution_candidate(clause: Clause) -> LRATDependency {
        LRATDependency(Tagged32::new(clause.index as u32).with_bit1().with_bit2())
    }
    pub fn is_resolution_candidate(self) -> bool {
        self.0.bit1() && self.0.bit2()
    }
    pub fn clause(self) -> Clause {
        Clause {
            index: u64::from(self.0.payload()),
        }
    }
}

/// ```
/// enum LRATLiteral {
///     ResolutionCandidate(Clause),
///     Hint(Clause),
///     Zero,
/// }
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Default)]
pub struct LRATLiteral(Tagged32);

impl LRATLiteral {
    pub fn resolution_candidate(clause: Clause) -> LRATLiteral {
        LRATLiteral(Tagged32::new(clause.index as u32))
    }
    pub fn is_resolution_candidate(self) -> bool {
        !self.0.bit1() && !self.0.bit2()
    }
    pub fn hint(clause: Clause) -> LRATLiteral {
        LRATLiteral(Tagged32::new(clause.index as u32).with_bit1())
    }
    pub fn is_hint(self) -> bool {
        self.0.bit1() && !self.0.bit2()
    }
    pub fn zero() -> LRATLiteral {
        LRATLiteral(Tagged32::new(0).with_bit1().with_bit2())
    }
    pub fn is_zero(self) -> bool {
        self.0.bit1() && self.0.bit2()
    }
    pub fn clause(self) -> Clause {
        requires!(!self.is_zero());
        Clause {
            index: u64::from(self.0.payload()),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct GRATLiteral(pub i32);

impl GRATLiteral {
    pub const ZERO: Self = Self(0);
    pub const UNIT_PROP: Self = Self(1);
    pub const DELETION: Self = Self(2);
    pub const RUP_LEMMA: Self = Self(3);
    pub const RAT_LEMMA: Self = Self(4);
    pub const CONFLICT: Self = Self(5);
    pub const RAT_COUNTS: Self = Self(6);
    pub fn from_clause(clause: Clause) -> GRATLiteral {
        requires!(clause.index + 1 < u64::from(u32::max_value()));
        Self((clause.index + 1) as i32)
    }
    pub fn to_clause(self) -> Clause {
        requires!(self.0 != 0);
        Clause::new((self.0 - 1) as u64)
    }
}

impl fmt::Display for GRATLiteral {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Default)]
pub struct Tagged64(u64);

impl Tagged64 {
    const MASK: u64 = Tagged64::MASK1 | Tagged64::MASK2;
    const MASK1: u64 = 0x80000000_00000000;
    const MASK2: u64 = 0x40000000_00000000;
    const MAX_PAYLOAD: u64 = u64::max_value() & !Tagged64::MASK;

    pub fn new(payload: u64) -> Tagged64 {
        requires!(payload <= Tagged64::MAX_PAYLOAD);
        Tagged64(payload)
    }
    pub fn with_bit1(self) -> Tagged64 {
        Tagged64(self.0 | Tagged64::MASK1)
    }
    pub fn with_bit2(self) -> Tagged64 {
        Tagged64(self.0 | Tagged64::MASK2)
    }
    pub fn payload(self) -> u64 {
        self.0 & !Tagged64::MASK
    }
    pub fn bit1(self) -> bool {
        self.0 & Tagged64::MASK1 != 0
    }
    pub fn bit2(self) -> bool {
        self.0 & Tagged64::MASK2 != 0
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Default)]
pub struct Tagged32(u32);

impl Tagged32 {
    const MASK: u32 = Tagged32::MASK1 | Tagged32::MASK2;
    const MASK1: u32 = 0x80_00_00_00;
    const MASK2: u32 = 0x40_00_00_00;
    const MAX_PAYLOAD: u32 = u32::max_value() & !Tagged32::MASK;

    pub fn new(payload: u32) -> Tagged32 {
        requires!(payload <= Tagged32::MAX_PAYLOAD);
        Tagged32(payload)
    }
    pub fn with_bit1(self) -> Tagged32 {
        Tagged32(self.0 | Tagged32::MASK1)
    }
    pub fn with_bit2(self) -> Tagged32 {
        Tagged32(self.0 | Tagged32::MASK2)
    }
    pub fn payload(self) -> u32 {
        self.0 & !Tagged32::MASK
    }
    pub fn bit1(self) -> bool {
        self.0 & Tagged32::MASK1 != 0
    }
    pub fn bit2(self) -> bool {
        self.0 & Tagged32::MASK2 != 0
    }
}

#[allow(dead_code)]
fn assert_primitive_sizes() {
    const_assert!(size_of::<crate::literal::Literal>() == 4);
    const_assert!(size_of::<Clause>() == 8);
    const_assert!(size_of::<Reason>() == 8);
    const_assert!(size_of::<LRATDependency>() == 4);
    const_assert!(size_of::<LRATLiteral>() == 4);
    const_assert!(size_of::<ProofStep>() == 8);
}
