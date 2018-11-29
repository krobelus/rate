//! Proof checking

use crate::{
    assignment::{assign, reset_assignment, Assignment},
    config::Config,
    formula::{member, Clause, Formula, Lemma, Proof},
    literal::Literal,
};

#[derive(Debug, PartialEq, Eq)]
pub struct Checker {
    pub assignment: Assignment,
    pub propcount: usize,
    pub ratcalls: usize,
    pub rupcalls: usize,
    pub config: Config,
}

impl Checker {
    pub fn new(formula: &Formula, config: Config) -> Checker {
        Checker {
            assignment: Assignment::new(formula.maxvar as usize),
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
    let mut unknown_count = 0;
    let mut unit = Literal::new(0);
    for l in formula.clause(c) {
        if assignment[l] {
            return ClauseStatus::Satisfied;
        }
        if !assignment[-l] {
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

fn propagate(formula: &Formula, checker: &mut Checker, l: Literal) -> bool {
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
    assign(&mut checker.assignment, l);
    for c in formula.clauses() {
        match clause_status(&formula, &checker.assignment, c) {
            ClauseStatus::Falsified => {
                return true;
            }
            ClauseStatus::Unit(literal) => {
                if propagate(formula, checker, literal) {
                    return true;
                }
            }
            ClauseStatus::Satisfied | ClauseStatus::Unknown => (),
        }
    }
    false
}

pub fn propagate_existing_units(formula: &Formula, checker: &mut Checker) -> bool {
    trace!(checker, "propagate existing\n");
    for c in formula.clauses() {
        match clause_status(&formula, &checker.assignment, c) {
            ClauseStatus::Falsified => return true,
            ClauseStatus::Unit(literal) => {
                if propagate(formula, checker, literal) {
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
            .any(|literal| propagate(formula, checker, -literal))
            || formula
                .clause(d)
                .filter(|literal| *literal != -pivot)
                .any(|literal| propagate(formula, checker, -literal))
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
            .any(|literal| propagate(formula, checker, -literal))
    )
}

enum LemmaEvaluation {
    Accepted,
    Rejected,
    ProofComplete,
}

fn perform_deletion(formula: &mut Formula, c: Clause) -> LemmaEvaluation {
    formula.clause_active[c] = false;
    // TODO handle deletion of unit clauses here
    LemmaEvaluation::Accepted
}

fn check_insertion(formula: &mut Formula, checker: &mut Checker, lemma: Clause) -> LemmaEvaluation {
    debug_assert!(lemma == formula.proof_start);
    // we should already have reached a conflict here
    if formula.clause(lemma).empty() {
        return LemmaEvaluation::Rejected;
    }
    if !rup(&formula, checker, lemma) && !rat(&formula, checker, lemma) {
        return LemmaEvaluation::Rejected;
    }
    formula.proof_start += 1;
    if let ClauseStatus::Unit(literal) = clause_status(formula, &checker.assignment, lemma) {
        if propagate(formula, checker, literal) {
            return LemmaEvaluation::ProofComplete;
        }
    }
    trace!(checker, "proofstart: {}\n", formula.proof_start);
    LemmaEvaluation::Accepted
}

fn check_lemma(formula: &mut Formula, checker: &mut Checker, lemma: Lemma) -> LemmaEvaluation {
    match lemma {
        Lemma::Deletion(clause) => perform_deletion(formula, clause),
        Lemma::Addition(clause) => check_insertion(formula, checker, clause),
    }
}

pub fn check(mut formula: &mut Formula, proof: &Proof, checker: &mut Checker) -> bool {
    if propagate_existing_units(formula, checker) {
        return true;
    }
    for lemma in proof {
        match check_lemma(&mut formula, checker, *lemma) {
            LemmaEvaluation::Accepted => (),
            LemmaEvaluation::Rejected => return false,
            LemmaEvaluation::ProofComplete => return true,
        }
    }
    false
}
