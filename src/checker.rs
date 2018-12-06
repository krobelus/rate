//! Proof checking

use crate::{
    assignment::Assignment,
    clause::{clause_as_copy, clause_as_mut_slice, clause_as_slice, Clause, ClauseCopy, Lemma},
    config::Config,
    literal::{literal_array_len, Literal, Variable},
    memory::{Array, Offset, Slice, SliceMut},
    parser::Parser,
};

pub struct Checker {
    state: State,
    constants: Constants,
}

struct Constants {
    config: Config,
    maxvar: Variable,
    clause_offset: Array<Clause, usize>,
    proof: Array<usize, Lemma>,
}

type Watchlist = Vec<Option<Clause>>;

struct State {
    assignment: Assignment,
    // The last unit that was propagated because of this clause, or Literal::new(0).
    clause_to_unit: Array<Clause, Literal>,
    lemma_to_level: Array<Clause, usize>,
    proof_start: Clause,
    clause_active: Array<Clause, bool>,
    db: Array<usize, Literal>,
    watchlist: Array<Literal, Watchlist>,
}

impl Checker {
    pub fn new(parser: Parser, config: Config) -> Checker {
        let num_clauses = parser.clause_offset.len();
        let maxvar = parser.maxvar;
        let mut checker = Checker {
            constants: Constants {
                config: config,
                maxvar: maxvar,
                clause_offset: Array::from(parser.clause_offset),
                proof: Array::from(parser.proof),
            },
            state: State {
                clause_active: Array::new(true, num_clauses),
                proof_start: parser.proof_start,

                db: Array::from(parser.db),
                watchlist: Array::new(Vec::new(), literal_array_len(maxvar)),

                assignment: Assignment::new(maxvar),
                clause_to_unit: Array::new(Literal::new(0), num_clauses),
                lemma_to_level: Array::new(0, num_clauses),
            },
        };
        let state = &mut checker.state;
        initialize_watches(
            &mut state.watchlist,
            &mut state.db,
            state.proof_start,
            &checker.constants.clause_offset,
        );
        checker
    }
}

#[derive(Debug, PartialEq, Eq)]
enum ClauseStatus {
    Satisfied,
    Falsified,
    Unknown,
    Unit(Literal),
}

fn initialize_watches(
    watchlist: &mut Array<Literal, Watchlist>,
    db: &mut Array<usize, Literal>,
    proof_start: Clause,
    clause_offset: &Array<Clause, usize>,
) {
    let initial_clauses = (0..proof_start.as_offset()).map(Clause);
    for c in initial_clauses {
        let mut literals = clause_as_mut_slice(db, &clause_offset, c);
        initialize_watchlist_clause(c, &mut literals, watchlist, None);
    }
}

fn next_unassigned(clause: Slice<Literal>, assignment: &Assignment, forbidden: usize) -> usize {
    for (i, &literal) in clause.iter().enumerate() {
        ensure!(!assignment[literal]);
        if i != forbidden && !assignment[-literal] {
            return i;
        }
    }
    panic!("not enough literals to watch");
}
fn initialize_watchlist_clause(
    c: Clause,
    literals: &mut SliceMut<Literal>,
    watchlist: &mut Array<Literal, Watchlist>,
    assignment: Option<&Assignment>,
) {
    if literals.len() >= 1 {
        let i0 = assignment.map_or(0, |assignment| {
            next_unassigned(literals.as_const(), &assignment, literals.len())
        });
        literals.swap(0, i0);
        watchlist[literals[0]].push(Some(c));
        if literals.len() >= 2 {
            let i1 = assignment.map_or(1, |assignment| {
                next_unassigned(literals.as_const(), &assignment, i0)
            });
            literals.swap(1, i1);
            watchlist[literals[1]].push(Some(c));
        }
    }
}

fn update_watchlist_clause(
    c: Clause,
    watchlist: &mut Array<Literal, Watchlist>,
    assignment: &Assignment,
    db: &mut Array<usize, Literal>,
    clause_offset: &Array<Clause, usize>,
) {
    let mut literals = clause_as_mut_slice(db, clause_offset, c);
    let falsified = if assignment[-literals[0]] {
        0
    } else {
        ensure!(assignment[-literals[1]]);
        1
    };
    let keep = 1 - falsified;
    let new = next_unassigned(literals.as_const(), &assignment, keep);
    watchlist[literals[new]].push(Some(c));
    let stale = &mut watchlist[literals[falsified]];
    let index = stale.iter().position(|&clause| clause == Some(c)).unwrap();
    stale[index] = None;
    // stale.swap_remove(stale.iter().position(|&clause| clause == c).unwrap());
    literals.swap(falsified, new);
    // remove clause from watchlist of falsified
}

fn trace_watches(constants: &Constants, watchlist: &Array<Literal, Watchlist>, maxvar: Variable) {
    (1..=maxvar.0 as i32)
        .flat_map(|l| vec![l, -l])
        .for_each(|l| trace!(constants, "w[{}]: {:?}\n", l, watchlist[Literal::new(l)]));
}

macro_rules! clause_copy {
    ($state:expr, $constants:expr, $clause:expr) => {
        ClauseCopy::new(
            $clause,
            &clause_as_copy(&$state.db, &$constants.clause_offset, $clause),
        )
    };
}

fn clauses<'a>(
    proof_start: Clause,
    clause_active: &'a Array<Clause, bool>,
) -> impl Iterator<Item = Clause> + 'a {
    (0..proof_start.as_offset())
        .map(Clause)
        .filter(move |&c| clause_active[c])
}

fn clause_status(clause: Slice<Literal>, assignment: &Assignment) -> ClauseStatus {
    clause_status_impl(clause, assignment, None)
}

fn clause_status_before(
    clause: Slice<Literal>,
    assignment: &Assignment,
    before_level: usize,
) -> ClauseStatus {
    clause_status_impl(clause, assignment, Some(before_level))
}

fn clause_status_impl(
    clause: Slice<Literal>,
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
            &mut $state.db,
            &mut $state.watchlist,
        )
    };
}

fn propagate_literal(
    l: Literal,
    reason: Option<Clause>,
    clause_to_unit: &mut Array<Clause, Literal>,
    assignment: &mut Assignment,
    constants: &Constants,
    proof_start: Clause,
    clause_active: &Array<Clause, bool>,
    db: &mut Array<usize, Literal>,
    watchlist: &mut Array<Literal, Watchlist>,
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
    assignment.assign(l);
    for i in 0..watchlist[-l].len() {
        if watchlist[-l][i].is_none() {
            continue;
        }
        let c = watchlist[-l][i].unwrap();
        if !clause_active[c] {
            continue;
        }
        let literals = clause_as_slice(db, &constants.clause_offset, c);
        match clause_status(literals, &assignment) {
            ClauseStatus::Falsified => return true,
            ClauseStatus::Unit(literal) => {
                if propagate_literal(
                    literal,
                    reason.and(Some(c)),
                    clause_to_unit,
                    assignment,
                    constants,
                    proof_start,
                    clause_active,
                    db,
                    watchlist,
                ) {
                    return true;
                }
            }
            ClauseStatus::Unknown => {
                update_watchlist_clause(c, watchlist, assignment, db, &constants.clause_offset);
            }
            ClauseStatus::Satisfied => (),
        }
    }
    false
}

fn propagate(state: &mut State, constants: &Constants, record_reasons: bool) -> bool {
    for c in clauses(state.proof_start, &state.clause_active) {
        let literals = clause_as_slice(&mut state.db, &constants.clause_offset, c);
        match clause_status(literals, &state.assignment) {
            ClauseStatus::Falsified => return true,
            ClauseStatus::Unit(literal) => {
                let reason = if record_reasons { Some(c) } else { None };
                if propagate_literal!(literal, reason, state, constants) {
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
        $assignment.reset(level);
        result
    }};
}

fn member(needle: Literal, clause: Slice<Literal>) -> bool {
    clause.iter().position(|&lit| needle == lit).is_some()
}

fn rat(
    clause: ClauseCopy,
    clause_to_unit: &mut Array<Clause, Literal>,
    mut assignment: &mut Assignment,
    constants: &Constants,
    proof_start: Clause,
    clause_active: &Array<Clause, bool>,
    db: &mut Array<usize, Literal>,
    watchlist: &mut Array<Literal, Watchlist>,
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
            db,
            watchlist,
        ) || clauses(proof_start, clause_active).all(|d| preserve_assignment!(
            &mut assignment,
            !member(-pivot, clause_as_slice(db, &constants.clause_offset, d))
                || rup(
                    clause_as_copy(db, &constants.clause_offset, d)
                        .iter()
                        .map(|literal| *literal)
                        .filter(|literal| *literal != -pivot),
                    clause_to_unit,
                    assignment,
                    &constants,
                    proof_start,
                    &clause_active,
                    db,
                    watchlist
                )
        ))
    )
}

fn rup<'a>(
    mut clause: impl Iterator<Item = Literal>,
    clause_to_unit: &mut Array<Clause, Literal>,
    assignment: &mut Assignment,
    constants: &Constants,
    proof_start: Clause,
    clause_active: &Array<Clause, bool>,
    db: &mut Array<usize, Literal>,
    watchlist: &mut Array<Literal, Watchlist>,
) -> bool {
    clause.any(|literal| {
        propagate_literal(
            -literal,
            None,
            clause_to_unit,
            assignment,
            constants,
            proof_start,
            clause_active,
            db,
            watchlist,
        )
    })
}

fn forward_addition(state: &mut State, constants: &Constants, c: Clause) -> bool {
    let clause = clause_copy!(state, constants, c);
    ensure!(c == state.proof_start);
    state.lemma_to_level[c] = state.assignment.len();
    let status = clause_status(clause.slice(), &state.assignment);
    state.proof_start += 1;
    if let ClauseStatus::Unit(literal) = status {
        if propagate_literal!(literal, Some(c), state, constants) {
            return true;
        }
    } else if status == ClauseStatus::Unknown {
        let mut literals = clause_as_mut_slice(&mut state.db, &constants.clause_offset, c);
        initialize_watchlist_clause(
            c,
            &mut literals,
            &mut state.watchlist,
            Some(&state.assignment),
        );
    }
    false
}

fn backward_addition(state: &mut State, constants: &Constants, c: Clause) -> bool {
    let clause = clause_copy!(state, constants, c);
    state.proof_start -= 1;
    ensure!(clause.len() != 0);
    ensure!(clause.id == state.proof_start);
    let level = state.lemma_to_level[clause.id];
    state.assignment.reset(level);
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
        &mut state.db,
        &mut state.watchlist,
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
        state.assignment.reset(level);
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
    trace!(constants, "[forward]\n");
    defer!(trace!(constants, "[forward] done\n"));
    for (i, lemma) in constants.proof.into_iter().enumerate() {
        let conflict_detected = match lemma {
            &Lemma::Deletion(clause) => {
                trace!(
                    constants,
                    "[forward] del {}\n",
                    clause_copy!(state, constants, clause)
                );
                forward_deletion(state, constants, clause)
            }
            &Lemma::Addition(clause) => {
                trace!(
                    constants,
                    "[forward] add {}\n",
                    clause_copy!(state, constants, clause)
                );
                let conflict_claimed = clause_copy!(state, constants, clause).len() == 0;
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
    trace!(constants, "[backward]\n");
    defer!(trace!(constants, "[backward] done\n"));
    let proof = constants.proof.as_slice();
    for lemma in proof.range(0, conflict_at + 1).iter().rev() {
        // for lemma in proof[0..=conflict_at].iter().rev()
        let accepted = match lemma {
            &Lemma::Deletion(clause) => {
                trace!(
                    constants,
                    "[backward] del {}\n",
                    clause_copy!(state, constants, clause)
                );
                backward_deletion(state, clause)
            }
            &Lemma::Addition(clause) => {
                trace!(
                    constants,
                    "[backward] add {}\n",
                    clause_copy!(state, constants, clause)
                );
                backward_addition(state, constants, clause)
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
    trace_watches(&constants, &state.watchlist, constants.maxvar);
    propagate(state, constants, true)
        || forward(state, constants)
            .map_or(false, |conflict_at| backward(state, constants, conflict_at))
}
