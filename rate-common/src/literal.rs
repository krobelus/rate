//! Variable and literal representations

use crate::memory::Offset;
use serde::{
    de::{self, Visitor},
    Deserialize, Deserializer, Serialize, Serializer,
};
use std::{convert::TryFrom, fmt, fmt::Display, ops};

/// A variable, encoded as 32 bit unsigned integer.
#[derive(Debug, PartialEq, Eq, Clone, Copy, PartialOrd, Ord)]
pub struct Variable(pub u32);

/// A literal, encoded as 32 bit unsigned integer.
#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash, PartialOrd, Ord, Default)]
pub struct Literal {
    /// We use a sign-magnitude encoding (also used by AIGER and others). This
    /// allows us to directly use this as offset.
    ///
    /// - The least significant bit is the sign (negative if it is 1).
    /// - The remaining bits encode the variable.
    pub encoding: u32,
}

impl Variable {
    pub fn new(value: u32) -> Variable {
        Variable(value)
    }
    /// Convert a variable to a positive literal.
    pub fn literal(self) -> Literal {
        requires!(i32::try_from(self.0).is_ok());
        Literal::new(self.0 as i32)
    }
    /// The size of an array that can contain variables up to and including
    /// `self`.
    pub fn array_size_for_variables(self) -> usize {
        self.as_offset() + 1
    }
    /// The size of an array that can contain literals up to and including
    /// `-self.literal()`.
    pub fn array_size_for_literals(self) -> usize {
        2 * (self.as_offset() + 1)
    }
}

/// Enable as array index.
impl Offset for Variable {
    /// We simply use the variable index, so offset 0 will be generally unused.
    fn as_offset(&self) -> usize {
        requires!(usize::try_from(self.0).is_ok());
        self.0 as usize
    }
}

impl Display for Variable {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.literal())
    }
}

impl Literal {
    /// Create a literal from the signed representation used in DIMACS.
    pub fn new(value: i32) -> Literal {
        requires!(value != i32::min_value());
        requires!((value.abs() as u32) < u32::pow(2, 31));
        Literal {
            encoding: (value.abs() as u32) * 2 + ((value < 0) as u32),
        }
    }
    /// Create a literal without conversion.
    pub const fn from_raw(encoding: u32) -> Literal {
        Literal { encoding }
    }

    /// Encoded as 0.
    pub const TOP: Literal = Literal { encoding: 0 };
    /// Encoded as 1.
    pub const BOTTOM: Literal = Literal { encoding: 1 };

    /// Sentinel value of  `u32::max_value()` to detect errors.
    pub const NEVER_READ: Literal = Literal {
        encoding: u32::max_value(),
    };

    /// DIMACS representation.
    /// # Examples
    /// ```
    /// use rate_common::literal::Literal;
    /// assert_eq!(Literal::new(-1).decode(), -1);
    /// ```
    pub fn decode(self) -> i32 {
        let magnitude = self.variable().0 as i32;
        if self.encoding & 1 != 0 {
            -magnitude
        } else {
            magnitude
        }
    }
    /// # Examples
    /// ```
    /// use rate_common::literal::{Literal, Variable};
    /// assert_eq!(Literal::new(-3).variable(), Variable(3));
    /// ```
    pub const fn variable(self) -> Variable {
        Variable(self.encoding / 2)
    }
    /// True if it is [`Literal::TOP`] or [`Literal::BOTTOM`].
    ///
    /// # Examples
    /// ```
    /// use rate_common::literal::Literal;
    /// assert!(Literal::TOP.is_constant());
    /// assert!(!Literal::new(-3).is_constant());
    /// ```
    pub fn is_constant(self) -> bool {
        self.encoding <= 1
    }
    /// Produce all literals from 1 and -1 up to the given variable.
    ///
    /// # Examples
    ///
    /// ```
    /// use rate_common::literal::{Literal, Variable};
    /// assert_eq!(Literal::all(Variable(2)).collect::<Vec<_>>(),
    ///           vec!(Literal::new(1), Literal::new(-1), Literal::new(2), Literal::new(-2)));
    /// ```
    pub fn all(maxvar: Variable) -> impl Iterator<Item = Literal> {
        let first = Variable(1).literal().encoding;
        let last = maxvar.literal().encoding;
        (first..last + 2).map(Literal::from_raw)
    }
    /// # Examples
    ///
    /// ```
    /// use rate_common::literal::Literal;
    /// assert!(Literal::new(0).is_zero());
    /// assert!(!Literal::new(1).is_zero());
    /// ```
    pub const fn is_zero(self) -> bool {
        self.encoding == 0
    }
}

/// Enable as array index.
impl Offset for Literal {
    fn as_offset(&self) -> usize {
        self.encoding as usize
    }
}

// Note: it might be more idiomatic to use [`std::ops::Not`] (`!`).
/// Negate a literal with operator `-`.
///
///
/// # Examples
///
/// ```
/// use rate_common::literal::Literal;
/// assert!(-Literal::TOP == Literal::BOTTOM);
/// ```
impl ops::Neg for Literal {
    type Output = Literal;
    fn neg(self) -> Literal {
        Literal {
            encoding: self.encoding ^ 1,
        }
    }
}

/// # Examples
///
/// ```
/// use rate_common::literal::Literal;
/// assert_eq!(format!("{}", Literal::TOP), "+0");
/// assert_eq!(format!("{}", Literal::BOTTOM), "-0");
/// assert_eq!(format!("{}", Literal::new(11)), "11");
/// ```
impl Display for Literal {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{}{}",
            if self == &Literal::TOP {
                "+"
            } else if self == &Literal::BOTTOM {
                "-"
            } else {
                ""
            },
            self.decode()
        )
    }
}

impl Serialize for Literal {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        requires!(
            !self.is_constant(),
            "serialization of boolean constants is not supported"
        );
        serializer.serialize_i32(self.decode())
    }
}

impl<'de> Deserialize<'de> for Literal {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let result = Literal::new(deserializer.deserialize_i32(I32Visitor)?);
        requires!(
            !result.is_constant(),
            "deserialization of boolean constants is not supported"
        );
        Ok(result)
    }
}

/// A deserializer for integers.
///
/// Used in the TOML parser in `sick-check`.
struct I32Visitor;

impl<'de> Visitor<'de> for I32Visitor {
    type Value = i32;

    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        formatter.write_str("an integer between -2^31 and 2^31")
    }

    fn visit_i8<E>(self, value: i8) -> Result<Self::Value, E>
    where
        E: de::Error,
    {
        Ok(i32::from(value))
    }

    fn visit_i32<E>(self, value: i32) -> Result<Self::Value, E>
    where
        E: de::Error,
    {
        Ok(value)
    }

    fn visit_i64<E>(self, value: i64) -> Result<Self::Value, E>
    where
        E: de::Error,
    {
        use std::i32;
        if value >= i64::from(i32::MIN) && value <= i64::from(i32::MAX) {
            Ok(value as i32)
        } else {
            Err(E::custom(format!("i32 out of range: {}", value)))
        }
    }
}
