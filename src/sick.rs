use crate::{
    literal::Literal,
    memory::{HeapSpace, Stack},
};

#[derive(Serialize, Deserialize, Debug, Default)]
pub struct Sick {
    pub proof_format: String,
    pub proof_step: usize,
    pub natural_model: Stack<Literal>,
    pub witness: Option<Stack<Witness>>,
}

#[derive(Clone, Serialize, Deserialize, Debug, Default)]
pub struct Witness {
    pub failing_clause: Stack<Literal>,
    pub failing_model: Stack<Literal>,
    pub pivot: Option<Literal>,
}

// Can't derive HeapSpace for Option<T> yet.
impl HeapSpace for Sick {
    fn heap_space(&self) -> usize {
        self.natural_model.heap_space() + self.witness.as_ref().map_or(0, HeapSpace::heap_space)
    }
}

impl HeapSpace for Witness {
    fn heap_space(&self) -> usize {
        self.failing_clause.heap_space() + self.failing_model.heap_space()
    }
}

// #[derive(Debug)]
// struct Rejection {
//     lemma: Stack<Literal>,
//     failed_proof_step: usize,
//     pivot: Option<Literal>,
//     resolved_with: Option<Clause>,
//     stable_assignment: Option<Assignment>,
//     natural_model_length: Option<usize>,
// }

// // Can't derive HeapSpace for Option<T> yet.
// impl HeapSpace for Rejection {
//     fn heap_space(&self) -> usize {
//         self.lemma.heap_space()
//             + match &self.stable_assignment {
//                 None => 0,
//                 Some(assignment) => assignment.heap_space(),
//             }
//     }
// }

// impl Rejection {
//     fn new() -> Rejection {
//         Rejection {
//             lemma: Stack::new(),
//             failed_proof_step: usize::max_value(),
//             pivot: None,
//             resolved_with: None,
//             stable_assignment: None,
//             natural_model_length: None,
//         }
//     }
// }
