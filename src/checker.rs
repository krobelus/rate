//! Proof checking

use crate::{
    assignment::Assignment,
    clause::{Clause, ClauseCopy, ProofStep},
    config::Config,
    literal::{literal_array_len, Literal, Variable},
    memory::{Array, Slice, SliceMut, Stack, StackMapping},
    parser::Parser,
};
use std::{hint::unreachable_unchecked, io, io::Write, ops};

pub struct Checker {
    assignment: Assignment,
    clause_active: Array<Clause, bool>,
    clause_core: Array<Clause, bool>,
    clause_id_in_lrat: Array<Clause, Clause>,
    clause_marked: Array<Clause, bool>,
    clause_offset: Array<Clause, usize>,
    clause_pivot: Array<Clause, Literal>,
    clause_unit: Array<Clause, Literal>, // The last unit that was propagated because of this clause, or Literal::TOP.
    config: Config,
    db: Array<usize, Literal>,
    direction: Direction,
    have_empty_clause: bool,
    implication_graph: StackMapping<Clause, bool>,
    lemma_lratlemma: Array<Clause, Stack<LRATLiteral>>,
    lemma_to_level: Array<Clause, usize>,
    literal_cause: Array<Literal, Clause>,
    lrat_id: Clause,
    maxvar: Variable,
    proof: Array<usize, ProofStep>,
    proof_start: Clause,
    proof_steps_until_conflict: usize,
    pub propcount: usize,
    resolution_candidate: Clause,
    watchlist: Array<Literal, Watchlist>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
enum LRATLiteral {
    ResolutionCandidate(Clause),
    Unit(Clause),
}

type Watchlist = Vec<Option<Clause>>;

impl Checker {
    pub fn new(parser: Parser, config: Config) -> Checker {
        let num_clauses = parser.num_clauses;
        let maxvar = parser.maxvar;
        let mut checker = Checker {
            assignment: Assignment::new(maxvar),
            clause_active: Array::new(true, num_clauses),
            clause_core: Array::new(false, num_clauses),
            clause_id_in_lrat: Array::new(Clause::INVALID, num_clauses + 1), // allow for missing empty clause
            clause_marked: Array::new(false, num_clauses),
            clause_offset: Array::from(parser.clause_offset),
            clause_pivot: Array::new(Literal::new(i32::max_value()), num_clauses), // record pivots because we swap watches
            clause_unit: Array::new(Literal::TOP, num_clauses),
            config: config,
            db: Array::from(parser.db),
            direction: Direction::Forward,
            have_empty_clause: false,
            implication_graph: StackMapping::new(false, num_clauses, num_clauses),
            lemma_lratlemma: Array::new(Stack::new(), num_clauses),
            lemma_to_level: Array::new(0, num_clauses),
            literal_cause: Array::new(Clause::INVALID, literal_array_len(maxvar)),
            lrat_id: Clause(0),
            maxvar: maxvar,
            proof: Array::from(parser.proof),
            proof_start: parser.proof_start,
            proof_steps_until_conflict: 0,
            propcount: 0,
            resolution_candidate: Clause::INVALID,
            watchlist: Array::new(Vec::new(), literal_array_len(maxvar)),
        };
        for c in Clause::range(parser.proof_start, Clause(num_clauses)) {
            if !checker.clause(c).empty() {
                checker.clause_pivot[c] = checker.clause(c)[0];
            }
        }
        for i in Clause::range(0, checker.proof_start) {
            checker.lrat_id += 1;
            checker.clause_id_in_lrat[i] = checker.lrat_id;
        }
        checker.have_empty_clause = watches_initialize(&mut checker);
        checker
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

fn watches_initialize(checker: &mut Checker) -> bool {
    for c in Clause::range(0, checker.proof_start) {
        if checker.clause(c).empty() {
            return true;
        }
        watches_add(checker, c);
    }
    false
}

fn watches_add(checker: &mut Checker, c: Clause) {
    traceln!(
        checker,
        "initializing watches for {}",
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
}

fn watches_remove(checker: &mut Checker, c: Clause) {
    traceln!(checker, "removing watches for {}", checker.clause_copy(c));
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
}

fn watches_update(checker: &mut Checker, l: Literal, c: Clause) {
    traceln!(
        checker,
        "updating watches of literal {} clause {}",
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

#[allow(dead_code)]
fn trace_watches(checker: &Checker) {
    if cfg!(debug_assertions) {
        Literal::all(checker.maxvar).for_each(|l| {
            traceln!(
                checker,
                "w[{}]: {}",
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
    let mut unit = Literal::TOP;
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

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
enum PropagationReason {
    UnitInFormula,
    RUPCheck,
}

fn propagate_literal(
    checker: &mut Checker,
    reason: PropagationReason,
    l: Literal,
    cause: Clause,
) -> bool {
    checker.propcount += 1;
    ensure!(cause == Clause::INVALID || checker.clause_active[cause]);
    if checker.assignment[l] {
        return false;
    }
    if reason == PropagationReason::UnitInFormula {
        checker.clause_unit[cause] = l;
    }
    checker.literal_cause[l] = cause;
    if checker.assignment[-l] {
        analyze_conflict(checker, reason, l, cause);
        return true;
    }
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
            ClauseStatus::Falsified => propagate_literal(checker, reason, Literal::BOTTOM, c),
            ClauseStatus::Unit(literal) => propagate_literal(checker, reason, literal, c),
            ClauseStatus::Unknown => {
                watches_update(checker, -l, c);
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
    while i < checker.watchlist[-l].len() {
        if checker.watchlist[-l][i].is_none() {
            checker.watchlist[-l].swap_remove(i);
        } else {
            i += 1;
        }
    }
    conflict
}

fn propagate_all(checker: &mut Checker) -> bool {
    let reason = PropagationReason::UnitInFormula;
    for l in Literal::all(checker.maxvar) {
        for i in 0..checker.watchlist[l].len() {
            if let Some(c) = checker.watchlist[l][i] {
                if checker.clause(c)[0] == l && checker.clause_active[c] {
                    match clause_status(checker.clause(c), &checker.assignment) {
                        ClauseStatus::Falsified => {
                            return propagate_literal(checker, reason, Literal::BOTTOM, c)
                        }
                        ClauseStatus::Unit(literal) => {
                            if propagate_literal(checker, reason, literal, c) {
                                return true;
                            }
                        }
                        ClauseStatus::Satisfied | ClauseStatus::Unknown => (),
                    }
                }
            }
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

fn rat(checker: &mut Checker, c: Clause) -> bool {
    let pivot = checker.clause_pivot[c];
    preserve_assignment!(checker.assignment, {
        traceln!(checker, "RUP check on {}", checker.clause_copy(c));
        rup(checker, c, |_| true) || {
            let ok = Clause::range(0, checker.proof_start) //
                .all(|d| {
                    preserve_assignment!(
                        checker.assignment,
                        !checker.clause_active[d]
                            || !member(-pivot, checker.clause(d))
                            // TODO why is this broken
                            // || (!checker.config.unmarked_rat_candidates && !checker.clause_core[d])
                            || {
                                traceln!(
                                    checker,
                                    "RAT check on {} and {}",
                                    checker.clause_copy(c),
                                    checker.clause_copy(d)
                                );
                                checker.resolution_candidate = d;
                                rup(checker, d, |literal| literal != -pivot)
                            }
                    )
                });
            if !ok {
                echo!("c RAT check failed for {}", checker.clause_copy(c));
            }
            ok
        }
    })
}

fn rup(checker: &mut Checker, c: Clause, filter: impl Fn(Literal) -> bool) -> bool {
    let resolvent_is_a_tautology = checker
        .clause_range(c)
        .any(|i| filter(checker.db[i]) && checker.assignment[checker.db[i]]);

    resolvent_is_a_tautology
        || checker.clause_range(c).any(|i| {
            filter(checker.db[i])
                && propagate_literal(checker, PropagationReason::RUPCheck, -checker.db[i], c)
        })
}

/// Analyze a conflict
/// This can be called in three different scenarios
///  - formula is trivially unsat (by UP)
///  - a conflict is detected for the first time during forward checking
///  - many times during backwards checking for RUP and RAT checks
///  We build the dependency graph of the conflict and compute an LRAT line for the current lemma.
///  This can be the empty clause (first two cases) or a normal RUP/RAT lemma.
fn analyze_conflict(
    checker: &mut Checker,
    reason: PropagationReason,
    literal: Literal,
    cause: Clause,
) {
    let lemma = checker.proof_start;
    checker.clause_marked[lemma] = true;
    if checker.direction == Direction::Forward {
        // We found our conflict. Set the length of the next clause to zero, so
        // it is the empty clause, even though we didn't actually look at it.
        checker.clause_offset[lemma + 1] = checker.clause_offset[lemma];
    };
    ensure!(cause != Clause::INVALID);
    traceln!(
        checker,
        "conflict arises at lemma {} in {} while propagating {} during {:?} {:?}",
        checker.clause_copy(lemma),
        checker.clause_copy(cause),
        literal,
        checker.direction,
        reason
    );
    if reason == PropagationReason::UnitInFormula {
        checker.clause_core[lemma] = true;
    }
    ensure!(checker.implication_graph.empty());
    // perform a DFS over the conflict graph
    fn walk_conflict_graph(
        checker: &mut Checker,
        reason: PropagationReason,
        lemma: Clause,
        cause: Clause,
    ) {
        ensure!(cause != Clause::INVALID);
        if checker.implication_graph[cause] {
            return;
        }
        checker.implication_graph.push(cause, true);

        for i in checker.clause_range(cause) {
            let lit = checker.db[i];
            let why_falsified = checker.literal_cause[-lit];
            if why_falsified != Clause::INVALID && !checker.assignment[lit] {
                traceln!(
                    checker,
                    "{} was caused by {}",
                    -checker.db[i],
                    checker.clause_copy(why_falsified)
                );
                walk_conflict_graph(checker, reason, lemma, why_falsified);
            }
        }

        checker.clause_marked[cause] = true;
        if reason == PropagationReason::UnitInFormula {
            checker.clause_core[cause] = true;
        }
        if cause != lemma {
            checker.lemma_lratlemma[lemma].push(LRATLiteral::Unit(cause));
        }
    }
    if reason == PropagationReason::RUPCheck {
        if checker.resolution_candidate != Clause::INVALID {
            checker.lemma_lratlemma[lemma].push(LRATLiteral::ResolutionCandidate(
                checker.resolution_candidate,
            ));
        }
        checker.resolution_candidate = Clause::INVALID;
    }
    walk_conflict_graph(checker, reason, lemma, cause);
    checker.implication_graph.clear();
}

#[derive(Debug, PartialEq, Eq)]
enum Direction {
    Forward,
    Backward,
}

fn apply_step(checker: &mut Checker, step: ProofStep) {
    match checker.direction {
        Direction::Forward => match step {
            ProofStep::Lemma(_) => {
                if !checker.clause(checker.proof_start).empty() {
                    watches_add(checker, checker.proof_start);
                }
                checker.proof_start += 1;
            }
            ProofStep::Deletion(c) => {
                checker.clause_active[c] = false;
                watches_remove(checker, c);
            }
        },
        Direction::Backward => match step {
            ProofStep::Lemma(_) => {
                checker.proof_start -= 1;
                if !checker.clause(checker.proof_start).empty() {
                    watches_remove(checker, checker.proof_start);
                }
            }
            ProofStep::Deletion(c) => {
                checker.clause_active[c] = true;
                watches_add(checker, c);
            }
        },
    }
}

fn forward_lemma(checker: &mut Checker) -> bool {
    let lemma = checker.proof_start;
    checker.lemma_to_level[lemma] = checker.assignment.len();
    apply_step(checker, ProofStep::Lemma(lemma));
    let status = clause_status(checker.clause(lemma), &checker.assignment);
    let conflict_detected = if let ClauseStatus::Unit(literal) = status {
        propagate_literal(checker, PropagationReason::UnitInFormula, literal, lemma)
    } else {
        false
    };
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
        let conflict = propagate_all(checker);
        ensure!(!conflict);
    }
    false
}

fn forward(checker: &mut Checker) -> bool {
    traceln!(checker, "[forward]");
    defer_trace!(checker, "[forward] done\n");
    for i in 0..checker.proof.len() {
        let conflict_detected = match checker.proof[i] {
            ProofStep::Deletion(c) => {
                traceln!(checker, "[forward] del {}", checker.clause_copy(c));
                forward_deletion(checker, c)
            }
            ProofStep::Lemma(c) => {
                ensure!(c == checker.proof_start);
                traceln!(checker, "[forward] add {}", checker.clause_copy(c));
                let conflict_claimed = checker.clause(c).empty();
                if conflict_claimed {
                    warn!("conflict claimed but not detected");
                    return false;
                }
                forward_lemma(checker)
            }
        };
        if conflict_detected {
            checker.proof_steps_until_conflict = i + 1;
            return true;
        }
    }
    false
}

fn backward(checker: &mut Checker) -> bool {
    // We know that, after executing `checker.proof_steps_until_conflict` steps,
    // the formula implies a conflict.
    // First we need to analyze the conflict.
    // Clause `checker.proof_start` shall be the empty clause in the LRAT certificate.
    checker.direction = Direction::Backward;
    traceln!(checker, "[backward]");
    defer_trace!(checker, "[backward] done\n");
    for i in (0..checker.proof_steps_until_conflict).rev() {
        let accepted = match checker.proof[i] {
            ProofStep::Deletion(c) => {
                traceln!(checker, "[backward] del {}", checker.clause_copy(c));
                ensure!(
                    !checker.clause_active[c],
                    "Clause must not be deleted twice."
                );
                apply_step(checker, ProofStep::Deletion(c));
                true
            }
            ProofStep::Lemma(c) => {
                traceln!(checker, "[backward] add {}", checker.clause_copy(c));
                ensure!(c + 1 == checker.proof_start);
                apply_step(checker, ProofStep::Lemma(c));
                !checker.clause_marked[c] || {
                    let level = checker.lemma_to_level[c];
                    checker.assignment.reset(level);
                    rat(checker, c)
                }
            }
        };
        if !accepted {
            return false;
        }
    }
    true
}

fn write_lrat_certificate(checker: &mut Checker) -> Result<(), io::Error> {
    if checker.have_empty_clause {
        return Ok(());
    }
    if Clause::range(Clause(0), checker.proof_start).any(|c| !checker.clause_marked[c]) {
        write!(checker.config.lrat_file, "{} d ", checker.lrat_id)?;
        for c in Clause::range(Clause(0), checker.proof_start) {
            if !checker.clause_marked[c] {
                write!(
                    checker.config.lrat_file,
                    "{} ",
                    checker.clause_id_in_lrat[c]
                )?;
            }
        }
        write!(checker.config.lrat_file, "0\n")?;
    }
    let mut i = 0;
    while i <= checker.proof_steps_until_conflict {
        match checker.proof[i] {
            ProofStep::Lemma(lemma) => {
                if checker.clause_marked[lemma] {
                    checker.lrat_id += 1;
                    checker.clause_id_in_lrat[lemma] = checker.lrat_id;
                    write_lemma(checker, lemma)?;
                }
            }
            ProofStep::Deletion(mut lemma) => {
                if checker.clause_id_in_lrat[lemma] != Clause::INVALID {
                    write!(checker.config.lrat_file, "{} d ", checker.lrat_id)?;
                    loop {
                        write!(
                            checker.config.lrat_file,
                            "{} ",
                            checker.clause_id_in_lrat[lemma]
                        )?;
                        i += 1;
                        if i >= checker.proof_steps_until_conflict {
                            break;
                        }
                        lemma = match checker.proof[i] {
                            ProofStep::Deletion(Clause::INVALID) => break,
                            ProofStep::Deletion(lemma) => lemma,
                            _ => {
                                i -= 1;
                                break;
                            }
                        }
                    }
                    write!(checker.config.lrat_file, "0\n")?;
                }
            }
        };
        i += 1;
    }
    // if let ProofStep::Lemma(lemma) = checker.proof[checker.proof_steps_until_conflict] {
    //     checker.lrat_id += 1;
    //     checker.clause_id_in_lrat[lemma] = checker.lrat_id;
    //     write_lemma(checker, lemma)?;
    // }
    fn write_lemma(checker: &mut Checker, lemma: Clause) -> Result<(), io::Error> {
        write!(
            checker.config.lrat_file,
            "{} ",
            checker.clause_id_in_lrat[lemma],
        )?;
        checker
            .clause_copy(lemma)
            .dimacs(&mut checker.config.lrat_file)?;
        write!(checker.config.lrat_file, " ")?;
        for hint in &checker.lemma_lratlemma[lemma] {
            match hint {
                &LRATLiteral::ResolutionCandidate(c) => write!(
                    checker.config.lrat_file,
                    "-{} ",
                    checker.clause_id_in_lrat[c]
                ),
                &LRATLiteral::Unit(c) => write!(
                    checker.config.lrat_file,
                    "{} ",
                    checker.clause_id_in_lrat[c]
                ),
            }?;
        }
        write!(checker.config.lrat_file, "0\n")
    }
    Ok(())
}

pub fn check(checker: &mut Checker) -> bool {
    let ok = (checker.have_empty_clause || propagate_all(checker) || forward(checker))
        && backward(checker);
    if ok && checker.config.lrat {
        write_lrat_certificate(checker).expect("Failed to write LRAT certificate.");
    }
    ok
}
