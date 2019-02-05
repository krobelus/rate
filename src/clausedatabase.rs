use crate::{
    clause::{Clause, ClauseCopy},
    literal::Literal,
    memory::{Offset, Slice, Stack},
    parser::{PADDING_END, PADDING_START},
};

use std::ops::{Index, IndexMut, Range};

#[derive(Debug)]
pub struct ClauseDatabase<'a> {
    data: &'a mut Stack<Literal>,
    offset: &'a mut Stack<usize>,
}

impl<'a> ClauseDatabase<'a> {
    pub fn new(data: &'a mut Stack<Literal>, offset: &'a mut Stack<usize>) -> ClauseDatabase<'a> {
        ClauseDatabase {
            data: data,
            offset: offset,
        }
    }
    pub fn clause(&self, clause: Clause) -> Slice<Literal> {
        let range = self.clause_range(clause);
        self.data.as_slice().range(range.start, range.end)
    }
    pub fn clause_copy(&self, clause: Clause) -> ClauseCopy {
        ClauseCopy::new(clause, self.clause(clause))
    }
    pub fn clause_range(&self, clause: Clause) -> Range<usize> {
        self.offset[clause.as_offset()] + PADDING_START
            ..self.offset[clause.as_offset() + 1] - PADDING_END
    }
    pub fn watches(&self, head: usize) -> [Literal; 2] {
        [self[head], self[head + 1]]
    }
    pub fn h2c(&self, head: usize) -> Clause {
        let lower = self[head - PADDING_START];
        let upper = self[head - PADDING_END + 1];
        Clause((lower.encoding as usize) | (upper.encoding as usize) >> 32)
    }
    pub fn c2h(&self, clause: Clause) -> usize {
        self.clause_range(clause).start
    }
    pub fn swap(&mut self, a: usize, b: usize) {
        self.data.as_mut_slice().swap(a, b);
    }
    pub fn make_clause_empty(&mut self, target: Clause) {
        self.offset[target.as_offset() + 1] =
            self.offset[target.as_offset()] + PADDING_START + PADDING_END;
    }
}

impl<'a> Index<usize> for ClauseDatabase<'a> {
    type Output = Literal;
    fn index(&self, offset: usize) -> &Literal {
        &self.data[offset]
    }
}

impl<'a> IndexMut<usize> for ClauseDatabase<'a> {
    fn index_mut(&mut self, offset: usize) -> &mut Literal {
        &mut self.data[offset]
    }
}