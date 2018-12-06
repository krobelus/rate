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
    pub fn from_raw(encoding: u32) -> Literal {
        Literal { encoding: encoding }
    }

    pub fn decode(self) -> i32 {
        let magnitude = self.var().0 as i32;
        if self.encoding & 1 != 0 {
            -magnitude
        } else {
            magnitude
        }
    }
    pub fn var(self) -> Variable {
        Variable(self.encoding / 2)
    }
    pub fn zero(self) -> bool {
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
        write!(f, "{}", self.decode())
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
