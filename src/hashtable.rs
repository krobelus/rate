use crate::{
    clause::Clause,
    clausedatabase::clause_db,
    literal::Literal,
    memory::{HeapSpace, Offset, Vector},
};

pub trait HashTable {
    fn add_clause(&mut self, clause: Clause);
    fn find_equal_clause(&mut self, needle: Clause, delete: bool) -> Option<Clause>;
    #[allow(dead_code)]
    fn clause_is_active(&self, needle: Clause) -> bool;
    #[allow(dead_code)]
    fn delete_clause(&mut self, needle: Clause) -> bool;
}

// #[derive(HeapSpace)]
pub struct FixedSizeHashTable {
    buckets: Vector<*mut Clause>,
    length: Vector<usize>,
    capacity: Vector<usize>,
}

fn bucket_layout(count: usize) -> Layout {
    let ptr_align = align_of::<Clause>();
    let size_in_bytes = usize::from(count) * size_of::<Clause>();
    Layout::from_size_align(size_in_bytes, ptr_align).unwrap()
}

fn bucket_index(clause: &[Literal]) -> usize {
    let mut sum: usize = 0;
    let mut prod: usize = 1;
    let mut xor: usize = 0;
    for &literal in clause {
        prod = prod.wrapping_mul(literal.as_offset());
        sum = sum.wrapping_add(literal.as_offset());
        xor ^= literal.as_offset();
    }
    ((1023 * sum + prod) ^ (31 * xor)) % FixedSizeHashTable::SIZE
}

impl FixedSizeHashTable {
    const SIZE: usize = 1_000_000;
    const INIT: u16 = 4;
    pub fn new() -> FixedSizeHashTable {
        let mut buckets = Vector::from_vec(vec![ptr::null_mut(); FixedSizeHashTable::SIZE]);
        for i in 0..buckets.len() {
            buckets[i] =
                unsafe { alloc(bucket_layout(FixedSizeHashTable::INIT.into())) } as *mut Clause;
        }
        FixedSizeHashTable {
            buckets,
            length: Vector::from_vec(vec![0; FixedSizeHashTable::SIZE]),
            capacity: Vector::from_vec(vec![
                FixedSizeHashTable::INIT.into();
                FixedSizeHashTable::SIZE
            ]),
        }
    }
}

impl HashTable for FixedSizeHashTable {
    fn add_clause(&mut self, clause: Clause) {
        let i = bucket_index(clause_db().clause(clause));
        if self.length[i] == self.capacity[i] {
            let new_capacity = (self.capacity[i] * 3) / 2;
            self.buckets[i] = unsafe {
                realloc(
                    self.buckets[i] as *mut u8,
                    bucket_layout(self.capacity[i]),
                    new_capacity * size_of::<Clause>(),
                )
            } as *mut Clause;
            self.capacity[i] = new_capacity;
        }
        unsafe { ptr::write(self.buckets[i].add(self.length[i]), clause) };
        self.length[i] += 1;
    }
    fn find_equal_clause(&mut self, needle: Clause, delete: bool) -> Option<Clause> {
        let i = bucket_index(clause_db().clause(needle));
        for offset in 0..self.length[i] {
            let clause = unsafe { *self.buckets[i].add(offset) };
            if clause_db().clause(needle) == clause_db().clause(clause) {
                if delete {
                    self.length[i] -= 1;
                    unsafe {
                        ptr::write(
                            self.buckets[i].add(offset),
                            *self.buckets[i].add(self.length[i]),
                        );
                    }
                }
                return Some(clause);
            }
        }
        None
    }
    fn clause_is_active(&self, needle: Clause) -> bool {
        let i = bucket_index(clause_db().clause(needle));
        for offset in 0..self.length[i] {
            if unsafe { *self.buckets[i].add(offset) } == needle {
                return true;
            }
        }
        false
    }
    fn delete_clause(&mut self, needle: Clause) -> bool {
        let i = bucket_index(clause_db().clause(needle));
        for offset in 0..self.length[i] {
            if unsafe { *self.buckets[i].add(offset) } == needle {
                self.length[i] -= 1;
                unsafe {
                    ptr::write(
                        self.buckets[i].add(offset),
                        *self.buckets[i].add(self.length[i]),
                    );
                }
                return true;
            }
        }
        false
    }
}

impl HeapSpace for FixedSizeHashTable {
    fn heap_space(&self) -> usize {
        let mut bucket_sizes_total: usize = 0;;
        for i in 0..self.buckets.len() {
            bucket_sizes_total += self.capacity[i];
        }
        bucket_sizes_total * size_of::<Clause>()
            + self.length.heap_space()
            + self.capacity.heap_space()
    }
}

impl Drop for FixedSizeHashTable {
    fn drop(&mut self) {
        for i in 0..self.buckets.len() {
            unsafe {
                dealloc(self.buckets[i] as *mut u8, bucket_layout(self.capacity[i]));
            }
        }
        drop(&mut self.buckets);
        drop(&mut self.length);
        drop(&mut self.capacity);
    }
}

// pub struct DynamicHashTable(HashMap<ClauseHashEq, SmallVector<Clause>>);

// impl DynamicHashTable {
//     pub fn new() -> DynamicHashTable {
//         DynamicHashTable(HashMap::new())
//     }
// }
// impl HashTable for DynamicHashTable {
//     fn add_clause(&mut self, clause: Clause) {
//         let key = ClauseHashEq(clause);
//         self.0
//             .entry(key)
//             .or_insert_with(SmallVector::new)
//             .push(clause)
//     }
//     fn find_equal_clause(&mut self, needle: Clause, delete: bool) -> Option<Clause> {
//         self.0
//             .get_mut(&ClauseHashEq(needle))
//             .and_then(|equal_clauses| {
//                 let first = equal_clauses.front();
//                 invariant!(first != Some(needle));
//                 if delete {
//                     equal_clauses.swap_remove(0);
//                 }
//                 first
//             })
//     }
//     // these are not optimized but only used in sick-check
//     fn clause_is_active(&self, needle: Clause) -> bool {
//         self.0
//             .get(&ClauseHashEq(needle))
//             .map_or(false, |stack| !stack.to_vec().is_empty())
//     }
//     fn delete_clause(&mut self, needle: Clause) -> bool {
//         self.0
//             .get_mut(&ClauseHashEq(needle))
//             .map_or(false, |equal_clauses| {
//                 let mut i = 0;
//                 let mut clauses = equal_clauses.to_vec();
//                 while clauses[i] != needle {
//                     i += 1;
//                     invariant!(i < clauses.len());
//                 }
//                 clauses.swap_remove(i);
//                 *equal_clauses = clauses.into_iter().collect();
//                 true
//             })
//     }
// }

// #[derive(Debug, Eq, Clone, Copy)]
// pub struct ClauseHashEq(pub Clause);

// impl Hash for ClauseHashEq {
//     fn hash<H: Hasher>(&self, hasher: &mut H) {
//         let it = clause_db().clause(self.0) ;
//         let mut sum : usize = 0 ;
//         let mut prod : usize = 1 ;
//         let mut xor : usize = 0 ;
//         for &literal in clause {
//             sum = sum.wrapping_add(literal.as_offset()) ;
//             prod = prod.wrapping_mul(literal.as_offset()) ;
//             xor ^= literal.as_offset();
//         }
//         let n = ((1023 * sum + prod) ^ (31 * xor)) ;
//         n.hash(hasher)
//     }
// }

// impl PartialEq for ClauseHashEq {
//     fn eq(&self, other: &ClauseHashEq) -> bool {
//         clause_db().clause(self.0) == clause_db().clause(other.0)
//     }
// }
