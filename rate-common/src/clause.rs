//! Data structures for the checker

use crate::memory::Offset;
use derive_more::Add;
use serde_derive::{Deserialize, Serialize};
use static_assertions::const_assert;
use std::{
    convert::{TryFrom, TryInto},
    fmt,
    io::{self, Write},
    mem::{align_of, size_of},
    ops::{Add, AddAssign, Sub, SubAssign},
};

use crate::literal::Literal;

/// An index uniquely identifying a clause or lemma during the lifetime of the program
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Add, Hash, Default)]
pub struct Clause {
    pub index: ClauseIdentifierType,
}

/// The type that backs [Clause](struct.Clause.html).
pub type ClauseIdentifierType = u32;

impl Clause {
    /// Create the clause index with the given ID.
    /// # Panics
    /// Panics if the index exceeds the internal limit.
    pub fn new(index: ClauseIdentifierType) -> Clause {
        requires!(index <= Clause::MAX_ID);
        Clause { index }
    }
    /// Create the clause index with the given usize ID.
    /// # Panics
    /// Panics if the index exceeds the internal limit.
    pub fn from_usize(index: usize) -> Clause {
        requires!(index < ClauseIdentifierType::max_value().try_into().unwrap());
        Clause::new(index as ClauseIdentifierType)
    }
    /// Create an iterator from clause indices `start` up to (excluding) `end`.
    pub fn range(start: impl Offset, end: impl Offset) -> impl Iterator<Item = Clause> {
        const_assert!(size_of::<usize>() >= size_of::<ClauseIdentifierType>());
        (start.as_offset()..end.as_offset()).map(Clause::from_usize)
    }
    /// The maximum value a regular `Clause` can assume.
    pub const MAX_ID: ClauseIdentifierType = Tagged32::MAX_PAYLOAD - 1;
    /// We need one special value for deleted clauses that do not actually exist.
    /// We cannot simply drop those deletions from the proof because `sick-check`
    /// relies on the line in the proof.
    pub const DOES_NOT_EXIST: Clause = Clause {
        index: Clause::MAX_ID + 1,
    };
    /// A special value for clause IDs. Used in places where we are sure
    /// that the value is written before being used as an actual clause ID.
    pub const UNINITIALIZED: Clause = Clause {
        index: Clause::MAX_ID + 2,
    };
}

impl Offset for Clause {
    fn as_offset(&self) -> usize {
        self.index as usize
    }
}

impl Add<ClauseIdentifierType> for Clause {
    type Output = Clause;
    fn add(self, value: ClauseIdentifierType) -> Clause {
        Clause::new(self.index + value)
    }
}

impl AddAssign<ClauseIdentifierType> for Clause {
    fn add_assign(&mut self, value: ClauseIdentifierType) {
        self.index += value;
    }
}

impl Sub<ClauseIdentifierType> for Clause {
    type Output = Clause;
    fn sub(self, value: ClauseIdentifierType) -> Clause {
        Clause::new(self.index - value)
    }
}

impl SubAssign<ClauseIdentifierType> for Clause {
    fn sub_assign(&mut self, value: ClauseIdentifierType) {
        self.index -= value;
    }
}

impl fmt::Display for Clause {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.index)
    }
}

/// A clause introduction or deletion
///
/// This is essentially this enum, but we pack everything into 32 bits.
/// ```
/// # use rate_common::clause::Clause;
/// enum ProofStep {
///     Lemma(Clause),
///     Deletion(Clause),
/// }
/// ```
#[derive(Debug, PartialEq, Eq, Clone, Copy, Default)]
pub struct ProofStep(Tagged32);

impl ProofStep {
    /// Create a proof step that introduces the given clause.
    pub fn lemma(clause: Clause) -> ProofStep {
        ProofStep(Tagged32::new(clause.index))
    }
    /// Create a proof step that deletes the given clause.
    pub fn deletion(clause: Clause) -> ProofStep {
        ProofStep(Tagged32::new(clause.index).with_bit1())
    }
    /// Return true if this proof step is a clause deletion.
    pub fn is_deletion(self) -> bool {
        self.0.bit1()
    }
    /// Return the clause that this proof step introduces or deletes.
    pub fn clause(self) -> Clause {
        Clause {
            index: self.0.payload(),
        }
    }
}

/// The reason for assigning a literal
///
/// A literal can be assumed, or forced by some clause. The clause
/// is stored as offset to reduce the number of indirections in
/// [propagate](../checker/fn.propagate.html).
///
/// This is essentially this enum, but we pack everything into `size_of::<usize>()` bits.
/// ```
/// enum Reason {
///     Assumed,
///     Forced(usize),
/// }
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct Reason(TaggedUSize);

impl Reason {
    /// Create an invalid reason, i.e. for unassigned literals.
    pub fn invalid() -> Reason {
        Reason(TaggedUSize::new(0))
    }
    /// Create a reason for assumed literals.
    pub fn assumed() -> Reason {
        Reason(TaggedUSize::new(0).with_bit1())
    }
    /// Create a reason for a clause that has been forced by the clause with
    /// the given offset.
    pub fn forced(offset: usize) -> Reason {
        Reason(
            TaggedUSize::new(offset.try_into().unwrap())
                .with_bit1()
                .with_bit2(),
        )
    }
    /// Return true when this is an assumption.
    pub fn is_assumed(self) -> bool {
        invariant!(self != Reason::invalid());
        !self.0.bit2()
    }
    /// Return the offset of the clause. Only valid if this is not an
    /// assumption or invalid.
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

/// An intermediate representation of an LRAT hint
///
/// This is essentially this enum, but we pack everything into 32 bits.
/// ```
/// # use rate_common::clause::Clause;
/// enum LRATDependency {
///     Unit(Clause),
///     ForcedUnit(Clause),
///     ResolutionCandidate(Clause),
/// }
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Default)]
pub struct LRATDependency(Tagged32);

impl LRATDependency {
    /// Create a hint stating that the given clause became unit during the
    /// redundancy check.
    pub fn unit_in_inference(clause: Clause) -> LRATDependency {
        LRATDependency(Tagged32::new(clause.index as u32))
    }
    /// Return true if this was a unit in the inference check.
    pub fn is_unit_in_inference(self) -> bool {
        !self.0.bit1() && !self.0.bit2()
    }
    /// Create a hint stating that the given clause was unit even before
    /// the redundancy check.
    pub fn forced_unit(clause: Clause) -> LRATDependency {
        LRATDependency(Tagged32::new(clause.index as u32).with_bit1())
    }
    /// Return true if this is a hint for a forced unit clause.
    pub fn is_forced_unit(self) -> bool {
        self.0.bit1() && !self.0.bit2()
    }
    /// Create a hint referring to the given clause as resolution candidate.
    pub fn resolution_candidate(clause: Clause) -> LRATDependency {
        LRATDependency(Tagged32::new(clause.index as u32).with_bit1().with_bit2())
    }
    /// Return true if this is a hint for a resolution candidate.
    pub fn is_resolution_candidate(self) -> bool {
        self.0.bit1() && self.0.bit2()
    }
    /// Return the clause referenced by this hint.
    pub fn clause(self) -> Clause {
        Clause {
            index: self.0.payload(),
        }
    }
}

/// A literal in the LRAT proof output
///
/// This is essentially this enum, but we pack everything into 32 bits.
/// ```
/// # use rate_common::clause::Clause;
/// enum LRATLiteral {
///     ResolutionCandidate(Clause),
///     Hint(Clause),
///     Zero,
/// }
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Default)]
pub struct LRATLiteral(Tagged32);

impl LRATLiteral {
    /// Create a hint for a resolution candidate.
    pub fn resolution_candidate(clause: Clause) -> LRATLiteral {
        LRATLiteral(Tagged32::new(clause.index as u32))
    }
    /// Return true if this is refers to a resolution candidate.
    pub fn is_resolution_candidate(self) -> bool {
        !self.0.bit1() && !self.0.bit2()
    }
    /// Create a hint for a unit clause.
    pub fn hint(clause: Clause) -> LRATLiteral {
        LRATLiteral(Tagged32::new(clause.index as u32).with_bit1())
    }
    /// Return true if this is a unit clause hint.
    pub fn is_hint(self) -> bool {
        self.0.bit1() && !self.0.bit2()
    }
    /// Create a zero terminator literal.
    pub fn zero() -> LRATLiteral {
        LRATLiteral(Tagged32::new(0).with_bit1().with_bit2())
    }
    /// Return true if this is a zero terminator.
    pub fn is_zero(self) -> bool {
        self.0.bit1() && self.0.bit2()
    }
    /// Assuming this is not a zero terminator, return the referenced clause.
    pub fn clause(self) -> Clause {
        requires!(!self.is_zero());
        Clause {
            index: self.0.payload(),
        }
    }
}

/// A literal for the GRAT proof output
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
    /// Create a GRAT literal that references the given internal clause.
    pub fn from_clause(clause: Clause) -> GRATLiteral {
        requires!(clause.index + 1 < ClauseIdentifierType::max_value());
        Self((clause.index + 1) as i32)
    }
    /// Compute the internal clause from a given GRAT literal.
    pub fn to_clause(self) -> Clause {
        requires!(self.0 != 0);
        Clause::new(ClauseIdentifierType::try_from(self.0).unwrap() - 1)
    }
}

impl fmt::Display for GRATLiteral {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// Value with 30 bit payload with 2 flag bits
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Default)]
pub struct Tagged32(u32);

impl Tagged32 {
    /// Mask for the both flag bits.
    const MASK: u32 = Tagged32::MASK1 | Tagged32::MASK2;
    /// Mask for the first flag bit.
    const MASK1: u32 = 0x80_00_00_00;
    /// Mask for the second flag bit.
    const MASK2: u32 = 0x40_00_00_00;
    /// The maximum value for the payload.
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

/// Value with `size_of::<usize>() - 2` bits of payload and 2 flag bits
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Default)]
pub struct TaggedUSize(usize);

impl TaggedUSize {
    const MASK: usize = TaggedUSize::MASK1 | TaggedUSize::MASK2;
    pub const MASK1: usize = 1 << (size_of::<usize>() * 8 - 1);
    pub const MASK2: usize = 1 << (size_of::<usize>() * 8 - 2);
    const MAX_PAYLOAD: usize = usize::max_value() & !TaggedUSize::MASK;

    pub fn new(payload: usize) -> TaggedUSize {
        requires!(payload <= TaggedUSize::MAX_PAYLOAD);
        TaggedUSize(payload)
    }
    pub fn with_bit1(self) -> TaggedUSize {
        TaggedUSize(self.0 | TaggedUSize::MASK1)
    }
    pub fn with_bit2(self) -> TaggedUSize {
        TaggedUSize(self.0 | TaggedUSize::MASK2)
    }
    pub fn payload(self) -> usize {
        self.0 & !TaggedUSize::MASK
    }
    pub fn bit1(self) -> bool {
        self.0 & TaggedUSize::MASK1 != 0
    }
    pub fn bit2(self) -> bool {
        self.0 & TaggedUSize::MASK2 != 0
    }
}

/// The redundancy property to use for inference checks.
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

/// State the sizes of data types.
#[allow(dead_code)]
fn assert_primitive_sizes() {
    const_assert!(size_of::<crate::literal::Literal>() == 4);
    const_assert!(size_of::<Clause>() == 4);
    const_assert!(size_of::<LRATDependency>() == 4);
    const_assert!(size_of::<LRATLiteral>() == 4);
    const_assert!(size_of::<ProofStep>() == 4);
    const_assert!(size_of::<Reason>() == size_of::<usize>());
    const_assert!(align_of::<Reason>() == align_of::<usize>());
}

/// Write some literals in DIMACS format.
///
/// Includes a terminating 0, but no newline.
pub fn write_clause<'a, T>(file: &mut impl Write, clause: T) -> io::Result<()>
where
    T: Iterator<Item = &'a Literal>,
{
    for &literal in clause {
        if literal != Literal::BOTTOM {
            write!(file, "{} ", literal)?;
        }
    }
    write!(file, "0")
}

/// Write the some literals in DIMACS format to stdout.
pub fn puts_clause<'a, T>(clause: T)
where
    T: IntoIterator<Item = &'a Literal>,
{
    for &literal in clause.into_iter() {
        if literal != Literal::BOTTOM {
            puts!("{} ", literal);
        }
    }
    puts!("0")
}

/// Write the clause ID and literals to stdout, like [<ID] <literals> 0.
pub fn puts_clause_with_id<'a, T>(clause: Clause, literals: T)
where
    T: IntoIterator<Item = &'a Literal>,
{
    puts!("[{}] ", clause);
    puts_clause(literals);
}

/// Write the clause ID, literals and a witness to stdout, like
/// [<ID] <literals> <witness> 0.
pub fn puts_clause_with_id_and_witness(clause: Clause, literals: &[Literal], witness: &[Literal]) {
    // The order of literals in the clause may have changed,
    // but not in the witness. Make sure to print the first
    // literal in the witness first to maintain the PR format.
    let witness_head = witness.first().cloned();
    puts!("[{}] ", clause);
    for &literal in literals {
        if literal != Literal::BOTTOM && Some(literal) != witness_head {
            puts!("{} ", literal);
        }
    }
    puts_clause(witness);
}
