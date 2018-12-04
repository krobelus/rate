//! Proof checking

use crate::{
    assignment::{assign, reset_assignment, was_assigned_before, Assignment},
    clause::{clause_as_slice, Clause, ClauseView, Lemma},
    config::Config,
    literal::Literal,
    memory::{Offset, TypedArray},
    parser::Parser,
};

pub struct Checker {
    state: State,
    constants: Constants,
}

struct Constants {
    config: Config,
    clause_offset: TypedArray<Clause, usize>,
    proof: TypedArray<usize, Lemma>,
}

struct State {
    assignment: Assignment,
    // The last unit that was propagated because of this clause, or Literal::new(0).
    clause_to_unit: TypedArray<Clause, Literal>,
    lemma_to_level: TypedArray<Clause, usize>,
    proof_start: Clause,
    clause_active: TypedArray<Clause, bool>,
    db: TypedArray<usize, Literal>,
}

impl Checker {
    pub fn new(parser: Parser, config: Config) -> Checker {
        let num_clauses = parser.clause_offset.len();
        let maxvar = parser.maxvar;
        Checker {
            constants: Constants {
                config: config,
                clause_offset: TypedArray::from(parser.clause_offset),
                proof: TypedArray::from(parser.proof),
            },
            state: State {
                clause_active: TypedArray::new(true, num_clauses),
                proof_start: parser.proof_start,

                db: TypedArray::<usize, Literal>::from(parser.db),

                assignment: Assignment::new(maxvar),
                clause_to_unit: TypedArray::new(Literal::new(0), num_clauses),
                lemma_to_level: TypedArray::new(0, num_clauses),
            },
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
enum ClauseStatus {
    Satisfied,
    Falsified,
    Unknown,
    Unit(Literal),
}

macro_rules! clause_view {
    ($state:expr, $constants:expr, $clause:expr) => {
        ClauseView::new(
            $clause,
            clause_as_slice(&$state.db, &$constants.clause_offset, $clause),
        )
    };
}

macro_rules! clauses {
    ($state:expr, $constants:expr) => {
        clauses(
            $state.proof_start,
            &$state.clause_active,
            &$state.db,
            &$constants.clause_offset,
        )
    };
}

fn clauses<'a>(
    proof_start: Clause,
    clause_active: &'a TypedArray<Clause, bool>,
    db: &'a TypedArray<usize, Literal>,
    clause_offset: &'a TypedArray<Clause, usize>,
) -> impl Iterator<Item = ClauseView<'a>> + 'a {
    (0..proof_start.as_offset())
        .map(Clause)
        .filter(move |&c| clause_active[c])
        .map(move |c| ClauseView::new(c, clause_as_slice(db, clause_offset, c)))
}

fn clause_status(clause: &[Literal], assignment: &Assignment) -> ClauseStatus {
    clause_status_impl(clause, assignment, None)
}

fn clause_status_before(
    clause: &[Literal],
    assignment: &Assignment,
    before_level: usize,
) -> ClauseStatus {
    clause_status_impl(clause, assignment, Some(before_level))
}

fn clause_status_impl(
    clause: &[Literal],
    assignment: &Assignment,
    before_level: Option<usize>,
) -> ClauseStatus {
    let mut unknown_count = 0;
    let mut unit = Literal::new(0);
    let is_assigned = |l| {
        before_level
            .map(|level| was_assigned_before(assignment, l, level))
            .unwrap_or(assignment[l])
    };
    for l in clause {
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

macro_rules! propagate_literal {
    ($literal:expr, $reason:expr, $state:expr, $constants:expr) => {
        propagate_literal(
            $literal,
            $reason,
            &mut $state.clause_to_unit,
            &mut $state.assignment,
            &$constants,
            $state.proof_start,
            &$state.clause_active,
            &$state.db,
        )
    };
}

fn propagate_literal(
    l: Literal,
    reason: Option<Clause>,
    clause_to_unit: &mut TypedArray<Clause, Literal>,
    assignment: &mut Assignment,
    constants: &Constants,
    proof_start: Clause,
    clause_active: &TypedArray<Clause, bool>,
    db: &TypedArray<usize, Literal>,
) -> bool {
    {
        trace!(constants, "prop {}\n", l);
        trace!(constants, "assignment[{}] :", assignment.len());
        for lit in assignment as &Assignment {
            trace!(constants, " {}", lit);
        }
        trace!(constants, "\n");
    }
    if assignment[-l] {
        return true;
    }
    if assignment[l] {
        return false;
    }
    reason.map(|unit_clause| {
        ensure!(clause_active[unit_clause]);
        clause_to_unit[unit_clause] = l;
    });
    assign(assignment, l);
    for clause in clauses(proof_start, &clause_active, &db, &constants.clause_offset) {
        match clause_status(clause.literals, &assignment) {
            ClauseStatus::Falsified => return true,
            ClauseStatus::Unit(literal) => {
                if propagate_literal(
                    literal,
                    reason.and(Some(clause.id)),
                    clause_to_unit,
                    assignment,
                    constants,
                    proof_start,
                    clause_active,
                    db,
                ) {
                    return true;
                }
            }
            ClauseStatus::Satisfied | ClauseStatus::Unknown => (),
        }
    }
    false
}

fn propagate(state: &mut State, constants: &Constants, record_reasons: bool) -> bool {
    for clause in clauses!(state, constants) {
        match clause_status(clause.literals, &state.assignment) {
            ClauseStatus::Falsified => return true,
            ClauseStatus::Unit(literal) => {
                let reason = if record_reasons {
                    Some(clause.id)
                } else {
                    None
                };
                if propagate_literal(
                    literal,
                    reason,
                    &mut state.clause_to_unit,
                    &mut state.assignment,
                    constants,
                    state.proof_start,
                    &state.clause_active,
                    &state.db,
                ) {
                    return true;
                }
            }
            ClauseStatus::Satisfied | ClauseStatus::Unknown => (),
        }
    }
    false
}

macro_rules! preserve_assignment {
    ($assignment:expr, $computation:expr) => {{
        let level = $assignment.len();
        let result = $computation;
        reset_assignment($assignment, level);
        result
    }};
}

fn member(needle: Literal, clause: &[Literal]) -> bool {
    clause.iter().position(|&lit| needle == lit).is_some()
}

fn rat(
    clause: ClauseView,
    clause_to_unit: &mut TypedArray<Clause, Literal>,
    mut assignment: &mut Assignment,
    constants: &Constants,
    proof_start: Clause,
    clause_active: &TypedArray<Clause, bool>,
    db: &TypedArray<usize, Literal>,
) -> bool {
    trace!(constants, "rat({}) - {}\n", clause.id, clause);
    let pivot = clause[0];
    preserve_assignment!(
        &mut assignment,
        rup(
            clause.iter(),
            clause_to_unit,
            assignment,
            &constants,
            proof_start,
            &clause_active,
            db
        ) || clauses(proof_start, &clause_active, &db, &constants.clause_offset)
            .filter(|d| member(-pivot, d.literals))
            .all(|d| preserve_assignment!(
                &mut assignment,
                rup(
                    d.iter().filter(|&literal| *literal != -pivot),
                    clause_to_unit,
                    assignment,
                    constants,
                    proof_start,
                    clause_active,
                    db
                )
            ))
    )
}

fn rup<'a>(
    mut clause: impl Iterator<Item = &'a Literal>,
    clause_to_unit: &mut TypedArray<Clause, Literal>,
    assignment: &mut Assignment,
    constants: &Constants,
    proof_start: Clause,
    clause_active: &TypedArray<Clause, bool>,
    db: &TypedArray<usize, Literal>,
) -> bool {
    clause.any(|&literal| {
        propagate_literal(
            -literal,
            None,
            clause_to_unit,
            assignment,
            constants,
            proof_start,
            clause_active,
            db,
        )
    })
}

fn forward_addition(state: &mut State, constants: &Constants, clause: Clause) -> bool {
    ensure!(clause == state.proof_start);
    state.lemma_to_level[clause] = state.assignment.len();
    let status = clause_status(
        clause_view!(state, constants, clause).literals,
        &state.assignment,
    );
    if let ClauseStatus::Unit(literal) = status {
        if propagate_literal!(literal, Some(clause), state, constants) {
            return true;
        }
    }
    state.proof_start += 1;
    false
}

fn backward_addition(state: &mut State, constants: &Constants, c: Clause) -> bool {
    let clause = clause_view!(state, constants, c);
    ensure!(clause.len() != 0);
    ensure!(clause.id == state.proof_start);
    let level = state.lemma_to_level[clause.id];
    reset_assignment(&mut state.assignment, level);
    if state.clause_to_unit[clause.id].zero() {
        // No need to check clauses that were not used to derive a conflict.
        return true;
    }
    trace!(constants, "rup({}) - {}\n", clause.id, clause);
    rat(
        clause,
        &mut state.clause_to_unit,
        &mut state.assignment,
        &constants,
        state.proof_start,
        &state.clause_active,
        &state.db,
    )
}

fn forward_deletion(state: &mut State, constants: &Constants, c: Clause) -> bool {
    ensure!(
        state.clause_active[c],
        "Clause {} deleted multiple times.",
        c
    );
    let recorded_unit = state.clause_to_unit[c];
    let level = state.assignment.level_prior_to_assigning(recorded_unit);
    let handle_deletion = !constants.config.skip_deletions
        && !recorded_unit.zero()
        && clause_status_before(
            clause_as_slice(&state.db, &constants.clause_offset, c),
            &state.assignment,
            level,
        ) == ClauseStatus::Unit(recorded_unit);
    state.clause_active[c] = false;
    if handle_deletion {
        reset_assignment(&mut state.assignment, level);
        propagate(state, constants, true);
    }
    false
}

fn backward_deletion(state: &mut State, c: Clause) -> bool {
    ensure!(!state.clause_active[c], "Clause must not be deleted twice.");
    state.clause_active[c] = true;
    true
}

fn forward(state: &mut State, constants: &Constants) -> Option<usize> {
    for (i, lemma) in constants.proof.into_iter().enumerate() {
        let conflict_detected = match lemma {
            &Lemma::Deletion(clause) => forward_deletion(state, constants, clause),
            &Lemma::Addition(clause) => {
                let conflict_claimed = clause_view!(state, constants, clause).len() == 0;
                if conflict_claimed {
                    warn!("conflict claimed but not detected");
                    return None;
                }
                forward_addition(state, constants, clause)
            }
        };
        if conflict_detected {
            return Some(i);
        }
    }
    None
}

fn backward(state: &mut State, constants: &Constants, conflict_at: usize) -> bool {
    let proof = constants.proof.as_slice();
    for lemma in proof[0..=conflict_at].iter().rev() {
        let accepted = match lemma {
            &Lemma::Deletion(clause) => backward_deletion(state, clause),
            &Lemma::Addition(clause) => {
                let ok = backward_addition(state, constants, clause);
                state.proof_start -= 1;
                ok
            }
        };
        if !accepted {
            return false;
        }
    }
    true
}

pub fn check(checker: &mut Checker) -> bool {
    let constants = &checker.constants;
    let state = &mut checker.state;
    propagate(state, constants, true)
        || forward(state, constants)
            .map_or(false, |conflict_at| backward(state, constants, conflict_at))
}
