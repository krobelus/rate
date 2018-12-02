//! Proof checking

use crate::{
    assignment::{assign, reset_assignment, was_assigned_before, Assignment},
    config::Config,
    formula::{member, Clause, Formula, Lemma, Proof},
    literal::Literal,
    memory::TypedArray,
};

#[derive(Debug, PartialEq, Eq)]
pub struct Checker {
    pub assignment: Assignment,
    // The last unit that was propagated because of this clause, or Literal::new(0).
    pub clause_to_unit: TypedArray<Clause, Literal>,
    pub lemma_to_level: TypedArray<Clause, usize>,
    pub propcount: usize,
    pub ratcalls: usize,
    pub rupcalls: usize,
    pub config: Config,
}

impl Checker {
    pub fn new(formula: &Formula, config: Config) -> Checker {
        Checker {
            assignment: Assignment::new(formula.maxvar as usize),
            clause_to_unit: TypedArray::new(Literal::new(0), formula.num_clauses()),
            lemma_to_level: TypedArray::new(0, formula.num_clauses()),
            propcount: 0,
            ratcalls: 0,
            rupcalls: 0,
            config: config,
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

fn clause_status(formula: &Formula, assignment: &Assignment, c: Clause) -> ClauseStatus {
    clause_status_impl(formula, assignment, c, None)
}

fn clause_status_before(
    formula: &Formula,
    assignment: &Assignment,
    c: Clause,
    before_level: usize,
) -> ClauseStatus {
    clause_status_impl(formula, assignment, c, Some(before_level))
}

fn clause_status_impl(
    formula: &Formula,
    assignment: &Assignment,
    c: Clause,
    before_level: Option<usize>,
) -> ClauseStatus {
    let mut unknown_count = 0;
    let mut unit = Literal::new(0);
    let is_assigned = |l| {
        before_level
            .map(|level| was_assigned_before(assignment, l, level))
            .unwrap_or(assignment[l])
    };
    for l in formula.clause(c) {
        if is_assigned(l) {
            return ClauseStatus::Satisfied;
        }
        if !is_assigned(-l) {
            unit = l;
            unknown_count += 1;
        }
    }
    match unknown_count {
        0 => ClauseStatus::Falsified,
        1 => ClauseStatus::Unit(unit),
        _ => ClauseStatus::Unknown,
    }
}

fn propagate_temporarily(formula: &Formula, checker: &mut Checker, l: Literal) -> bool {
    propagate(formula, checker, l, None)
}

fn propagate(formula: &Formula, checker: &mut Checker, l: Literal, reason: Option<Clause>) -> bool {
    {
        trace!(checker, "prop {}\n", l);
        trace!(checker, "assignment[{}] :", checker.assignment.len());
        for lit in &checker.assignment {
            trace!(checker, " {}", lit);
        }
        trace!(checker, "\n");
    }
    checker.propcount += 1;
    if checker.assignment[-l] {
        return true;
    }
    if checker.assignment[l] {
        return false;
    }
    reason.map(|clause| {
        ensure!(formula.clause_active[clause]);
        checker.clause_to_unit[clause] = l;
    });
    assign(&mut checker.assignment, l);
    for c in formula.clauses() {
        match clause_status(&formula, &checker.assignment, c) {
            ClauseStatus::Falsified => {
                return true;
            }
            ClauseStatus::Unit(literal) => {
                let reason_clause = reason.map(|_| c);
                if propagate(formula, checker, literal, reason_clause) {
                    return true;
                }
            }
            ClauseStatus::Satisfied | ClauseStatus::Unknown => (),
        }
    }
    false
}

fn propagate_existing_units(formula: &Formula, checker: &mut Checker) -> bool {
    trace!(checker, "propagate existing\n");
    for c in formula.clauses() {
        match clause_status(&formula, &checker.assignment, c) {
            ClauseStatus::Falsified => return true,
            ClauseStatus::Unit(literal) => {
                if propagate(formula, checker, literal, Some(c)) {
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

fn is_rat_on(
    formula: &Formula,
    checker: &mut Checker,
    pivot: Literal,
    c: Clause,
    d: Clause,
) -> bool {
    trace!(checker, "is_rat_on({}, {}) - {}\n", c, d, formula.clause(d));
    preserve_assignment!(
        &mut checker.assignment,
        formula
            .clause(c)
            .any(|literal| propagate_temporarily(formula, checker, -literal))
            || formula
                .clause(d)
                .filter(|literal| *literal != -pivot)
                .any(|literal| propagate_temporarily(formula, checker, -literal))
    )
}

pub fn rat(formula: &Formula, checker: &mut Checker, c: Clause) -> bool {
    trace!(checker, "rat({}) - {}\n", c, formula.clause(c));
    checker.ratcalls += 1;
    let pivot = formula.clause(c).next().unwrap();
    let ok = formula
        .clauses()
        .filter(|d| member(&formula, -pivot, *d))
        .all(|d| is_rat_on(formula, checker, pivot, c, d));
    if !ok {
        trace!(checker, "RAT check failed for clause {}", formula.clause(c));
    }
    ok
}

pub fn rup(formula: &Formula, checker: &mut Checker, c: Clause) -> bool {
    trace!(checker, "rup({}) - {}\n", c, formula.clause(c));
    checker.rupcalls += 1;
    trace!(checker, "propagating reverse clause\n");
    preserve_assignment!(
        &mut checker.assignment,
        formula
            .clause(c)
            .any(|literal| propagate_temporarily(formula, checker, -literal))
    )
}

fn forward_addition(formula: &mut Formula, checker: &mut Checker, lemma: Clause) -> bool {
    ensure!(lemma == formula.proof_start);
    checker.lemma_to_level[lemma] = checker.assignment.len();
    if let ClauseStatus::Unit(literal) = clause_status(formula, &checker.assignment, lemma) {
        if propagate(formula, checker, literal, Some(lemma)) {
            return true;
        }
    }
    formula.proof_start += 1;
    false
}

fn backward_addition(formula: &mut Formula, checker: &mut Checker, lemma: Clause) -> bool {
    ensure!(!formula.clause(lemma).empty());
    ensure!(lemma == formula.proof_start);
    let level = checker.lemma_to_level[lemma];
    reset_assignment(&mut checker.assignment, level);
    if checker.clause_to_unit[lemma] == Literal::new(0) {
        // No need to check clauses that were not used to derive a conflict.
        return true;
    }
    rup(&formula, checker, lemma) || rat(&formula, checker, lemma)
}

fn forward_deletion(formula: &mut Formula, checker: &mut Checker, c: Clause) -> bool {
    ensure!(formula.clause_active[c], "Clause deleted multiple times.");
    let recorded_unit = checker.clause_to_unit[c];
    let level = checker.assignment.level_prior_to_assigning(recorded_unit);
    let handle_deletion = !checker.config.skip_deletions && recorded_unit != Literal::new(0);
    if handle_deletion {
        reset_assignment(&mut checker.assignment, level);
        ensure!(
            match clause_status_before(formula, &checker.assignment, c, level) {
                ClauseStatus::Unit(literal) => literal == recorded_unit,
                _ => false,
            },
            "Deleted clause was unit previously, which it should still be with respect to the \
             assignment immediately before it propagated."
        );
    }
    formula.clause_active[c] = false;
    if handle_deletion {
        propagate_existing_units(formula, checker);
    }
    false
}

fn backward_deletion(formula: &mut Formula, c: Clause) -> bool {
    ensure!(!formula.clause_active[c]);
    formula.clause_active[c] = true;
    true
}

fn forward(formula: &mut Formula, proof: &Proof, checker: &mut Checker) -> Option<usize> {
    for (i, lemma) in proof.into_iter().enumerate() {
        let conflict_detected = match lemma {
            Lemma::Deletion(clause) => forward_deletion(formula, checker, *clause),
            Lemma::Addition(clause) => {
                let conflict_claimed = formula.clause(*clause).empty();
                if conflict_claimed {
                    warn!("conflict claimed but not detected");
                    return None;
                }
                forward_addition(formula, checker, *clause)
            }
        };
        if conflict_detected {
            return Some(i);
        }
    }
    None
}

fn backward(
    formula: &mut Formula,
    proof: &Proof,
    checker: &mut Checker,
    conflict_at: usize,
) -> bool {
    for i in (0..=conflict_at).rev() {
        let lemma = proof[i];

        let accepted = match lemma {
            Lemma::Deletion(clause) => backward_deletion(formula, clause),
            Lemma::Addition(clause) => {
                let ok = backward_addition(formula, checker, clause);
                formula.proof_start -= 1;
                ok
            }
        };
        if !accepted {
            return false;
        }
    }
    true
}

pub fn check(formula: &mut Formula, proof: &Proof, checker: &mut Checker) -> bool {
    if propagate_existing_units(formula, checker) {
        return true;
    }
    forward(formula, proof, checker)
        .map(|conflict_at| backward(formula, proof, checker, conflict_at))
        .unwrap_or(false)
}
