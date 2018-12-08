//! Proof checking

use crate::{
    assignment::Assignment,
    clause::{Clause, ClauseCopy, ProofStep},
    config::Config,
    literal::{literal_array_len, Literal, Variable},
    memory::{Array, Slice, SliceMut},
    parser::Parser,
};
use std::{hint::unreachable_unchecked, ops};

pub struct Checker {
    assignment: Assignment,
    clause_active: Array<Clause, bool>,
    clause_marked: Array<Clause, bool>,
    clause_offset: Array<Clause, usize>,
    clause_unit: Array<Clause, Literal>, // The last unit that was propagated because of this clause, or Literal::new(0).
    config: Config,
    db: Array<usize, Literal>,
    direction: Direction,
    lemma_to_level: Array<Clause, usize>,
    literal_reason: Array<Literal, Clause>,
    maxvar: Variable,
    proof: Array<usize, ProofStep>,
    proof_start: Clause,
    pub propcount: usize,
    watchlist: Array<Literal, Watchlist>,
}

type Watchlist = Vec<Option<Clause>>;

impl Checker {
    pub fn new(parser: Parser, config: Config) -> Checker {
        let num_clauses = parser.clause_offset.len();
        let maxvar = parser.maxvar;
        Checker {
            assignment: Assignment::new(maxvar),
            clause_active: Array::new(true, num_clauses),
            clause_marked: Array::new(false, num_clauses),
            clause_offset: Array::from(parser.clause_offset),
            clause_unit: Array::new(Literal::TOP, num_clauses),
            config: config,
            db: Array::from(parser.db),
            direction: Direction::Forward,
            lemma_to_level: Array::new(0, num_clauses),
            literal_reason: Array::new(Clause::INVALID, literal_array_len(maxvar)),
            maxvar: maxvar,
            proof: Array::from(parser.proof),
            proof_start: parser.proof_start,
            propcount: 0,
            watchlist: Array::new(Vec::new(), literal_array_len(maxvar)),
        }
    }
    fn clause(&self, c: Clause) -> Slice<Literal> {
        let range = self.clause_range(c);
        self.db.as_slice().range(range.start, range.end)
    }
    fn clause_as_mut_slice(&mut self, c: Clause) -> SliceMut<Literal> {
        let range = self.clause_range(c);
        self.db.as_mut_slice().range(range.start, range.end)
    }
    fn clause_copy(&self, c: Clause) -> ClauseCopy {
        ClauseCopy::new(c, &self.clause(c).to_vec())
    }
    fn watches(&self, c: Clause) -> (Literal, Literal) {
        (self.clause(c)[0], self.clause(c)[1])
    }
    fn is_syntactical_unit(&self, c: Clause) -> bool {
        self.watches(c).1 == Literal::BOTTOM
    }
    fn clause_range(&self, c: Clause) -> ops::Range<usize> {
        self.clause_offset[c]..self.clause_offset[c + 1]
    }
}

#[derive(Debug, PartialEq, Eq)]
enum ClauseStatus {
    Satisfied,
    Falsified,
    Unknown,
    Unit(Literal),
}

fn initialize_watches(checker: &mut Checker) -> bool {
    for c in Clause::range(0, checker.proof_start) {
        if checker.clause(c).len() == 0 {
            return true;
        }
        initialize_watchlist_clause(checker, c);
    }
    false
}

fn initialize_watchlist_clause(checker: &mut Checker, c: Clause) {
    trace!(
        checker,
        "initializing watches for {}\n",
        checker.clause_copy(c)
    );
    let size = checker.clause(c).len();
    ensure!(size >= 2);
    let (i0, l0) = next_unassigned_or_none(&checker, c, size).unwrap_or((0, checker.clause(c)[0]));
    checker.clause_as_mut_slice(c).swap(0, i0);
    checker.watchlist[l0].push(Some(c));
    if !checker.is_syntactical_unit(c) {
        let (i1, l1) = next_unassigned_or_none(&checker, c, 0).unwrap_or((1, checker.clause(c)[1]));
        checker.clause_as_mut_slice(c).swap(1, i1);
        checker.watchlist[l1].push(Some(c));
    }
    trace_watches(checker);
}

fn remove_watchlist_clause(checker: &mut Checker, c: Clause) {
    trace!(checker, "removing watches for {}\n", checker.clause_copy(c));
    let (l0, l1) = checker.watches(c);
    let index = checker.watchlist[l0]
        .iter()
        .position(|watched| watched == &Some(c))
        .unwrap();
    checker.watchlist[l0][index] = None;
    if l1 != Literal::BOTTOM {
        let index = checker.watchlist[l1]
            .iter()
            .position(|watched| watched == &Some(c))
            .unwrap();
        checker.watchlist[l1][index] = None;
    }
    trace_watches(checker);
}

fn update_watchlist_clause(checker: &mut Checker, l: Literal, c: Clause) {
    trace!(
        checker,
        "updating watches of literal {} clause {}\n",
        l,
        checker.clause_copy(c)
    );
    let (l0, l1) = checker.watches(c);
    ensure!(
        !l1.is_constant(),
        "Watches of true unit clauses must not be updated."
    );
    // we could always put falsified watch at position 0 here
    let falsified_watch = if l == l0 {
        0
    } else {
        ensure!(l == l1);
        1
    };
    let keep = 1 - falsified_watch;
    let (new_index, new_literal) = next_unassigned(&checker, c, keep);
    ensure!(!new_literal.is_constant());
    checker.watchlist[new_literal].push(Some(c));
    checker
        .clause_as_mut_slice(c)
        .swap(falsified_watch, new_index);
    trace_watches(checker);
}

fn next_unassigned_or_none(
    checker: &Checker,
    c: Clause,
    forbidden: usize,
) -> Option<(usize, Literal)> {
    for (i, &literal) in checker.clause(c).iter().enumerate() {
        if i != forbidden && !checker.assignment[-literal] {
            return Some((i, literal));
        }
    }
    None
}

fn next_unassigned(checker: &Checker, c: Clause, forbidden: usize) -> (usize, Literal) {
    for (i, &literal) in checker.clause(c).iter().enumerate() {
        ensure!(!checker.assignment[literal]);
        if i != forbidden && !checker.assignment[-literal] {
            return (i, literal);
        }
    }
    unsafe { unreachable_unchecked() }
}

fn trace_watches(checker: &Checker) {
    if cfg!(debug_assertions) {
        Literal::all(checker.maxvar).for_each(|l| {
            trace!(
                checker,
                "w[{}]: {}\n",
                l,
                checker.watchlist[l]
                    .iter()
                    .map(|watch| watch.map_or("x".to_string(), |c| format!("{}", c)))
                    .collect::<Vec<String>>()
                    .join(", ")
            )
        });
    }
}

fn clause_status(literals: Slice<Literal>, assignment: &Assignment) -> ClauseStatus {
    clause_status_impl(literals, assignment, None)
}

fn clause_status_before(
    literals: Slice<Literal>,
    assignment: &Assignment,
    before_level: usize,
) -> ClauseStatus {
    clause_status_impl(literals, assignment, Some(before_level))
}

fn clause_status_impl(
    literals: Slice<Literal>,
    assignment: &Assignment,
    before_level: Option<usize>,
) -> ClauseStatus {
    let mut unknown_count = 0;
    let mut unit = Literal::new(0);
    let is_assigned = |literal| {
        before_level
            .map(|level| assignment.was_assigned_before(literal, level))
            .unwrap_or(assignment[literal])
    };
    for l in literals {
        if is_assigned(*l) {
            return ClauseStatus::Satisfied;
        }
        if !is_assigned(-*l) {
            unit = *l;
            unknown_count += 1;
        }
    }
    match unknown_count {
        0 => ClauseStatus::Falsified,
        1 => ClauseStatus::Unit(unit),
        _ => ClauseStatus::Unknown,
    }
}

fn propagate_literal(checker: &mut Checker, l: Literal, reason: Option<Clause>) -> bool {
    checker.propcount += 1;
    trace!(checker, "propagate_literal {}, {}\n", l, checker.assignment);
    if checker.assignment[l] {
        return false;
    }
    if checker.assignment[-l] {
        return reason.map_or(true, |conflict_clause| {
            reached_conflict_in(checker, conflict_clause)
        });
    }
    reason.map(|unit_clause| {
        ensure!(checker.clause_active[unit_clause]);
        checker.clause_unit[unit_clause] = l;
        checker.literal_reason[l] = unit_clause;
    });
    checker.assignment.assign(l);
    let mut conflict = false;
    for i in 0..checker.watchlist[-l].len() {
        if !checker.watchlist[-l][i].is_some() {
            continue;
        }
        let c = checker.watchlist[-l][i].unwrap();
        if !checker.clause_active[c] {
            continue;
        }
        conflict = match clause_status(checker.clause(c), &checker.assignment) {
            ClauseStatus::Falsified => reached_conflict_in(checker, c),
            ClauseStatus::Unit(literal) => propagate_literal(checker, literal, reason.and(Some(c))),
            ClauseStatus::Unknown => {
                update_watchlist_clause(checker, -l, c);
                checker.watchlist[-l][i] = None;
                false
            }
            ClauseStatus::Satisfied => false,
        };
        if conflict {
            break;
        }
    }
    let mut i = 0;
    // Compact the watch list.
    loop {
        if i >= checker.watchlist[-l].len() {
            break;
        }
        if checker.watchlist[-l][i].is_none() {
            checker.watchlist[-l].swap_remove(i);
        } else {
            i += 1;
        }
    }
    conflict
}

fn reached_conflict_in(checker: &mut Checker, c: Clause) -> bool {
    checker.literal_reason[Literal::new(0)] = c;
    true
}

fn formula_contains_empty_clause(checker: &mut Checker) -> bool {
    initialize_watches(checker)
}

fn propagate(checker: &mut Checker, record_reasons: bool) -> bool {
    for l in Literal::all(checker.maxvar) {
        let mut i = 0;
        loop {
            if i >= checker.watchlist[l].len() {
                break;
            }
            if let Some(c) = checker.watchlist[l][i] {
                if checker.clause(c)[0] == l && checker.clause_active[c] {
                    match clause_status(checker.clause(c), &checker.assignment) {
                        ClauseStatus::Falsified => return reached_conflict_in(checker, c),
                        ClauseStatus::Unit(literal) => {
                            let reason = if record_reasons { Some(c) } else { None };
                            if propagate_literal(checker, literal, reason) {
                                return true;
                            }
                        }
                        ClauseStatus::Satisfied | ClauseStatus::Unknown => (),
                    }
                }
            }
            i += 1;
        }
    }
    false
}

macro_rules! preserve_assignment {
    ($assignment:expr, $computation:expr) => {{
        let level = $assignment.len();
        let result = $computation;
        $assignment.reset(level);
        result
    }};
}

fn member(needle: Literal, literals: Slice<Literal>) -> bool {
    literals.iter().position(|&lit| needle == lit).is_some()
}

fn rat(checker: &mut Checker, literals: ClauseCopy) -> bool {
    let pivot = literals[0];
    preserve_assignment!(checker.assignment, {
        trace!(checker, "RUP check on {}\n", literals);
        rup(checker, literals.iter())
            || Clause::range(0, checker.proof_start) //
                .all(|d| {
                    preserve_assignment!(
                        checker.assignment,
                        !checker.clause_active[d]
                            || (!checker.config.unmarked_rat_candidates
                                && !checker.clause_marked[d])
                            || !member(-pivot, checker.clause(d))
                            || {
                                trace!(checker, "RAT check on {}\n", literals);
                                rup(
                                    checker,
                                    checker
                                        .clause_copy(d)
                                        .iter()
                                        .filter(|literal| **literal != -pivot),
                                )
                            }
                    )
                })
    })
}

fn rup<'a>(checker: &mut Checker, mut literals: impl Iterator<Item = &'a Literal>) -> bool {
    literals.any(|literal| propagate_literal(checker, -*literal, None))
}

fn mark_reasons_for_conflict(checker: &mut Checker) -> bool {
    let literal_reason = &checker.literal_reason;
    let conflict_reason = literal_reason[Literal::new(0)];
    let mut stack = vec![conflict_reason];
    while stack.len() != 0 {
        let c = stack.pop().unwrap();
        for i in checker.clause_range(c) {
            let l = checker.db[i];
            let reason = literal_reason[-l];
            if reason != Clause::INVALID && !checker.clause_marked[reason] {
                checker.clause_marked[reason] = true;
                stack.push(reason);
            }
        }
    }
    true
}

enum Direction {
    Forward,
    Backward,
}

fn apply_step(checker: &mut Checker, step: ProofStep) {
    match checker.direction {
        Direction::Forward => match step {
            ProofStep::Lemma(_) => {
                initialize_watchlist_clause(checker, checker.proof_start);
                checker.proof_start += 1;
            }
            ProofStep::Deletion(c) => {
                checker.clause_active[c] = false;
                remove_watchlist_clause(checker, c);
            }
        },
        Direction::Backward => match step {
            ProofStep::Lemma(_) => {
                checker.proof_start -= 1;
                remove_watchlist_clause(checker, checker.proof_start);
            }
            ProofStep::Deletion(c) => {
                checker.clause_active[c] = true;
                initialize_watchlist_clause(checker, c);
            }
        },
    }
}

fn forward_lemma(checker: &mut Checker) -> bool {
    checker.lemma_to_level[checker.proof_start] = checker.assignment.len();
    let status = clause_status(checker.clause(checker.proof_start), &checker.assignment);
    let conflict_detected = if let ClauseStatus::Unit(literal) = status {
        propagate_literal(checker, literal, Some(checker.proof_start))
    } else {
        false
    };
    apply_step(checker, ProofStep::Lemma(checker.proof_start));
    conflict_detected
}

fn forward_deletion(checker: &mut Checker, c: Clause) -> bool {
    ensure!(
        checker.clause_active[c],
        "Clause {} deleted multiple times.",
        c
    );
    let recorded_unit = checker.clause_unit[c];
    let level = checker.assignment.level_prior_to_assigning(recorded_unit);
    let handle_unit_deletion = !checker.config.skip_deletions
        && recorded_unit != Literal::TOP
        && clause_status_before(checker.clause(c), &checker.assignment, level)
            == ClauseStatus::Unit(recorded_unit);
    apply_step(checker, ProofStep::Deletion(c));
    if handle_unit_deletion {
        checker.assignment.reset(level);
        let conflict = propagate(checker, true);
        ensure!(!conflict);
    }
    false
}

fn forward(checker: &mut Checker) -> Option<usize> {
    trace!(checker, "[forward]\n");
    defer_trace!(checker, "[forward] done\n");
    for i in 0..checker.proof.len() {
        let conflict_detected = match checker.proof[i] {
            ProofStep::Deletion(c) => {
                trace!(checker, "[forward] del {}\n", checker.clause_copy(c));
                forward_deletion(checker, c)
            }
            ProofStep::Lemma(c) => {
                ensure!(c == checker.proof_start);
                trace!(checker, "[forward] add {}\n", checker.clause_copy(c));
                let conflict_claimed = checker.clause(c).len() == 0;
                if conflict_claimed {
                    warn!("conflict claimed but not detected");
                    return None;
                }
                forward_lemma(checker)
            }
        };
        trace!(checker, "[forward] {}\n", checker.assignment);
        if conflict_detected {
            return Some(i);
        }
    }
    None
}

fn backward(checker: &mut Checker, conflict_at_step: usize) -> bool {
    trace!(checker, "[backward]\n");
    defer_trace!(checker, "[backward] done\n");
    checker.direction = Direction::Backward;
    for i in (0..conflict_at_step + 1).rev() {
        let accepted = match checker.proof[i] {
            ProofStep::Deletion(c) => {
                trace!(checker, "[backward] del {}\n", checker.clause_copy(c));
                ensure!(
                    !checker.clause_active[c],
                    "Clause must not be deleted twice."
                );
                apply_step(checker, ProofStep::Deletion(c));
                true
            }
            ProofStep::Lemma(c) => {
                trace!(checker, "[backward] add {}\n", checker.clause_copy(c));
                ensure!(c + 1 == checker.proof_start);
                apply_step(checker, ProofStep::Lemma(c));
                !checker.clause_marked[c] || {
                    let level = checker.lemma_to_level[c];
                    checker.assignment.reset(level);
                    rat(checker, checker.clause_copy(c))
                }
            }
        };
        if !accepted {
            return false;
        }
    }
    true
}

pub fn check(checker: &mut Checker) -> bool {
    formula_contains_empty_clause(checker) || propagate(checker, true) || {
        if let Some(conflict_at_step) = forward(checker) {
            mark_reasons_for_conflict(checker);
            backward(checker, conflict_at_step)
        } else {
            false
        }
    }
}
