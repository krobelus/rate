//! Variable and literal representations

use crate::memory::Offset;
use std::{fmt, fmt::Display, ops};

#[derive(Debug, PartialEq, Eq, Clone, Copy, PartialOrd, Ord)]
pub struct Variable(pub u32);

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash, PartialOrd, Ord)]
pub struct Literal {
    encoding: u32,
}

impl Variable {
    pub fn new(value: u32) -> Variable {
        Variable(value)
    }
    pub fn literal(self) -> Literal {
        Literal::new(self.0 as i32)
    }
}

impl Offset for Variable {
    fn as_offset(self) -> usize {
        self.0 as usize
    }
}

pub fn literal_array_len(maxvar: Variable) -> usize {
    2 * (maxvar.as_offset() + 1)
}

impl Literal {
    /// Construct a new literal from the usual signed representation.
    pub fn new(value: i32) -> Literal {
        Literal {
            encoding: (value.abs() as u32) * 2 + ((value < 0) as u32),
        }
    }
    pub const fn from_raw(encoding: u32) -> Literal {
        Literal { encoding: encoding }
    }

    pub const TOP: Literal = Literal { encoding: 0 };
    pub const BOTTOM: Literal = Literal { encoding: 1 };

    pub fn decode(self) -> i32 {
        let magnitude = self.var().0 as i32;
        if self.encoding & 1 != 0 {
            -magnitude
        } else {
            magnitude
        }
    }
    pub const fn var(self) -> Variable {
        Variable(self.encoding / 2)
    }
    pub fn is_constant(self) -> bool {
        self.encoding <= 1
    }
    pub fn all(maxvar: Variable) -> impl Iterator<Item = Literal> {
        let end = maxvar.literal().encoding;
        (1..end + 2).map(Literal::from_raw)
    }
    pub const fn is_zero(self) -> bool {
        self.encoding == 0
    }
}

impl Offset for Literal {
    fn as_offset(self) -> usize {
        self.encoding as usize
    }
}

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

impl ops::Neg for Literal {
    type Output = Literal;
    fn neg(self) -> Literal {
        Literal {
            encoding: self.encoding ^ 1,
        }
    }
}
