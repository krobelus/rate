//! Proof checking

use crate::{
    assignment::Assignment,
    clause::{Clause, ClauseCopy, ProofStep},
    config::Config,
    config::NO_WATCHES,
    literal::{literal_array_len, Literal, Variable},
    memory::{Array, Slice, Stack, StackMapping},
    parser::Parser,
};
use std::{io, io::Write, ops};

pub struct Checker {
    assignment: Assignment,
    // clause_core: Array<Clause, bool>,
    clause_active: Array<Clause, bool>,
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
            // clause_core: Array::new(false, num_clauses),
            clause_active: Array::new(true, num_clauses),
            clause_id_in_lrat: Array::new(Clause::INVALID, num_clauses + 1), // allow for missing empty clause // TODO
            // TODO
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
            lemma_to_level: Array::new(usize::max_value(), num_clauses),
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
        for c in Clause::range(0, checker.proof_start) {
            if !checker.clause(c).empty() {
                watches_add(&mut checker, c);
            }
        }
        checker.have_empty_clause =
            Clause::range(0, checker.proof_start).any(|c| checker.clause(c).empty());
        checker
    }
    fn clause(&self, c: Clause) -> Slice<Literal> {
        let range = self.clause_range(c);
        self.db.as_slice().range(range.start, range.end)
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
    fn is_assigned(&self, l: Literal) -> bool {
        self.assignment[l] || self.assignment[-l]
    }
    fn clause_range(&self, c: Clause) -> ops::Range<usize> {
        self.clause_offset[c]..self.clause_offset[c + 1]
    }
}

#[derive(Debug, PartialEq, Eq)]
struct MaybeConflict(bool);
const CONFLICT: MaybeConflict = MaybeConflict(true);
const NO_CONFLICT: MaybeConflict = MaybeConflict(false);

#[derive(Debug, PartialEq, Eq)]
enum ClauseStatus {
    Satisfied,
    Falsified,
    Unknown,
    Unit(Literal),
}

fn watches_add(checker: &mut Checker, c: Clause) {
    if !NO_WATCHES {
        log!(
            checker,
            2,
            "initializing watches for {}",
            checker.clause_copy(c)
        );
        let size = checker.clause(c).len();
        ensure!(size >= 2);
        let status = clause_status(checker.clause(c), &checker.assignment);
        let range = checker.clause_range(c);
        ensure!(
            status == ClauseStatus::Unknown
                || status == ClauseStatus::Unit(checker.db[range.start])
        );
        let i0 = first_non_falsified(&checker, c, range.start);
        let l0 = checker.db[i0];
        checker.db.as_mut_slice().swap(range.start, i0);
        checker.watchlist[l0].push(Some(c));
        if !checker.is_syntactical_unit(c) {
            let i1 = first_non_falsified(&checker, c, range.start + 1);
            let l1 = checker.db[i1];
            checker.db.as_mut_slice().swap(range.start + 1, i1);
            checker.watchlist[l1].push(Some(c));
        }
        trace_watches(checker);
    }
}

fn watches_remove(checker: &mut Checker, c: Clause) -> Option<()> {
    if !NO_WATCHES {
        log!(
            checker,
            2,
            "removing watches for {}",
            checker.clause_copy(c)
        );
        let (l0, l1) = checker.watches(c);
        checker.watchlist[l0]
            .iter()
            .position(|&watched| watched == Some(c))
            .map(|i| checker.watchlist[l0][i] = None);
        if l1 != Literal::BOTTOM {
            checker.watchlist[l1]
                .iter()
                .position(|&watched| watched == Some(c))
                .map(|i| checker.watchlist[l1][i] = None);
        }
        trace_watches(checker);
        Some(())
    } else {
        None
    }
}

fn watches_update(checker: &mut Checker, l: Literal, c: Clause) {
    if !NO_WATCHES {
        log!(
            checker,
            2,
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
        let range = checker.clause_range(c);
        let falsified_watch = if l == l0 {
            range.start
        } else {
            ensure!(l == l1);
            range.start + 1
        };
        let new_index = first_non_falsified(&checker, c, range.start + 2);
        let new_literal = checker.db[new_index];
        ensure!(!new_literal.is_constant());
        checker.watchlist[new_literal].push(Some(c));
        checker.db.as_mut_slice().swap(falsified_watch, new_index);
        trace_watches(checker);
    }
}

fn first_non_falsified(checker: &Checker, c: Clause, start: usize) -> usize {
    (start..checker.clause_range(c).end)
        .find(|&i| !checker.assignment[-checker.db[i]])
        .unwrap()
}

// this needs to be a macro to place assertion failures at the caller location
macro_rules! check_watches {
    ($checker:expr) =>
    {
        if !NO_WATCHES {
            // each watch points to a clause that is neither falsified nor satisfied
            for l in Literal::all($checker.maxvar) {
                for oc in &$checker.watchlist[l] {
                    if let &Some(c) = oc {
                        let (l0, l1) = $checker.watches(c);
                        ensure!(
                            !$checker.is_assigned(-l0) ||
                            !$checker.is_assigned(-l1)
                            ,
                            format!("each watched clause needs at least one unassigned literal: violated in {} - {}", $checker.clause_copy(c),
                            $checker.assignment)
                        );
                    }
                }
            }
            // each active clause that is neither falsified nor satisfied, is watched by one or two
            // literals
            for c in Clause::range(0, $checker.proof_start)
                .filter(|&c| $checker.clause_active[c])
                {
                    match clause_status($checker.clause(c), &$checker.assignment) {
                        ClauseStatus::Unknown => {
                            let is_watched = Literal::all($checker.maxvar)
                                .any(|l|
                                     $checker.watchlist[l].iter().find(|&watched_clause| *watched_clause == Some(c)).is_some()
                                );
                            ensure!(is_watched, format!("each active undecided clause needs to be watched: violated for {} - {}",
                                                        $checker.clause_copy(c),
                                                        $checker.assignment));
                        }
                        _ =>(),
                    }
                }
        }
    }
}

fn trace_watches(checker: &Checker) {
    if checker.config.verbosity >= 3 {
        Literal::all(checker.maxvar).for_each(|l| {
            log!(
                checker,
                3,
                "w[{:}]: {}",
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
    for &l in literals {
        if is_assigned(l) {
            return ClauseStatus::Satisfied;
        }
        if !is_assigned(-l) && l != Literal::BOTTOM {
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

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
enum PropagationReason {
    UnitInFormula,
    RUPCheck,
}

fn propagate_to_clause(
    checker: &mut Checker,
    reason: PropagationReason,
    from_watchlist: Option<(Literal, usize)>,
    c: Clause,
) -> MaybeConflict {
    ensure!(from_watchlist.is_none() || checker.clause_active[c]);
    match clause_status(checker.clause(c), &checker.assignment) {
        ClauseStatus::Falsified => {
            if let Some((literal, position_in_watchlist)) = from_watchlist {
                checker.watchlist[-literal][position_in_watchlist] = None;
            }
            propagate_literal(checker, reason, Literal::BOTTOM, c)
        }
        ClauseStatus::Unit(unit_literal) => {
            if let Some((literal, position_in_watchlist)) = from_watchlist {
                checker.watchlist[-literal][position_in_watchlist] = None;
            }
            propagate_literal(checker, reason, unit_literal, c)
        }
        ClauseStatus::Unknown => {
            if let Some((literal, position_in_watchlist)) = from_watchlist {
                watches_update(checker, -literal, c);
                checker.watchlist[-literal][position_in_watchlist] = None;
            }
            NO_CONFLICT
        }
        ClauseStatus::Satisfied => NO_CONFLICT,
    }
}

fn propagate_literal(
    checker: &mut Checker,
    reason: PropagationReason,
    l: Literal,
    cause: Clause,
) -> MaybeConflict {
    checker.propcount += 1;
    if checker.assignment[l] {
        return NO_CONFLICT;
    }
    if reason == PropagationReason::UnitInFormula {
        checker.clause_unit[cause] = l;
    }
    // TODO
    if cause != Clause::INVALID {
        log!(
            checker,
            2,
            "propagating {} because of {}",
            l,
            checker.clause_copy(cause)
        );
    } else {
        log!(checker, 2, "propagating {}", l);
    }
    watches_remove(checker, cause);
    checker.literal_cause[l] = cause;
    checker.watchlist[l].clear();
    if checker.assignment[-l] {
        // TODO not
        ensure!(checker.watchlist[-l].len() == 0);
        analyze_conflict(checker, reason, l, cause);
        return CONFLICT;
    }
    checker.assignment.assign(l);
    log!(checker, 3, "{}", checker.assignment);
    if NO_WATCHES {
        propagate_all(checker)
    } else {
        let mut conflict = NO_CONFLICT;
        for i in 0..checker.watchlist[-l].len() {
            checker.watchlist[-l][i].map(|c| {
                if CONFLICT == propagate_to_clause(checker, reason, Some((l, i)), c) {
                    conflict = CONFLICT;
                }
            });
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
        if CONFLICT == conflict {
            checker.watchlist[-l].clear();
        }
        conflict
    }
}

fn propagate_all_watched(checker: &mut Checker) -> MaybeConflict {
    if NO_WATCHES {
        propagate_all(checker)
    } else {
        let reason = PropagationReason::UnitInFormula;
        let mut conflict = NO_CONFLICT;
        for l in Literal::all(checker.maxvar) {
            for i in 0..checker.watchlist[l].len() {
                if let Some(c) = checker.watchlist[l][i] {
                    if checker.clause(c)[0] == l {
                        if CONFLICT == propagate_to_clause(checker, reason, None, c) {
                            conflict = CONFLICT;
                        }
                    }
                }
            }
        }
        conflict
    }
}

fn propagate_all(checker: &mut Checker) -> MaybeConflict {
    let reason = PropagationReason::UnitInFormula;
    let mut conflict = NO_CONFLICT;
    for c in Clause::range(0, checker.proof_start) {
        if checker.clause_active[c] {
            if CONFLICT == propagate_to_clause(checker, reason, None, c) {
                conflict = CONFLICT;
            } else {
                // TODO
                // match clause_status(checker.clause(c), &checker.assignment) {
                //     ClauseStatus::Unknown => watches_add(checker, c),
                //     _ => (),
                // }
            }
        }
    }
    conflict
}

macro_rules! preserve_assignment {
    ($checker:expr, $computation:expr) => {{
        let level = $checker.assignment.len();
        let mut result = $computation;
        $checker.assignment.reset(level);
        // TODO
        if CONFLICT == propagate_all($checker) {
            result = true;
        }
        result
    }};
}

fn member(needle: Literal, literals: Slice<Literal>) -> bool {
    literals.iter().position(|&lit| needle == lit).is_some()
}

fn rat(checker: &mut Checker, c: Clause) -> bool {
    let pivot = checker.clause_pivot[c];
    check_watches!(checker);
    preserve_assignment!(checker, {
        log!(
            checker,
            1,
            "RUP check on {}, {}",
            checker.clause_copy(c),
            checker.assignment
        );
        rup(checker, c, |_| true) || {
            // TODO collect resolution candidates from the watchlists!
            let ok = Clause::range(0, checker.proof_start) //
                .all(|d| {
                    preserve_assignment!(
                        checker,
                        !member(-pivot, checker.clause(d))
                        || !checker.clause_active[d]
                            // TODO why is this broken
                            // || (!checker.config.unmarked_rat_candidates && !checker.clause_core[d])
                            || {
                                log!(
                                    checker,
                                    2,
                                    "RAT check on {} and {} with pivot {}, {}",
                                    checker.clause_copy(c),
                                    checker.clause_copy(d),
                                    pivot, checker.assignment
                                );
                                check_watches!(checker);
                                // let resolvent_is_a_tautology = checker
                                //     .clause_range(d)
                                //     .any(|i| checker.db[i] != -pivot && checker.assignment[-checker.db[i]]);
                                // if resolvent_is_a_tautology {
                                //     // TODO consolidate
                                //     checker.lemma_lratlemma[checker.proof_start].push(LRATLiteral::ResolutionCandidate(d));
                                //     true
                                // } else {
                                // checker.resolution_candidate = d;
                                // rup(checker, d, |literal| literal != -pivot)
                                // }
                                checker.resolution_candidate = d;
                                let result = rup(checker, d, |literal| literal != -pivot);
                                result
                            }
                    )
                });
            checker.resolution_candidate = Clause::INVALID;
            if !ok {
                echo!("c RAT check failed for {}", checker.clause_copy(c));
            }
            ok
        }
    })
}

fn rup(checker: &mut Checker, c: Clause, predicate: impl Fn(Literal) -> bool) -> bool {
    checker.clause_range(c).any(|i| {
        predicate(checker.db[i])
            && CONFLICT
                == propagate_literal(checker, PropagationReason::RUPCheck, -checker.db[i], c)
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
    // checker.clause_marked[lemma] = true;
    if checker.direction == Direction::Forward {
        // We found our conflict. Set the length of the next clause to zero, so
        // it is the empty clause, even though we didn't actually look at it.
        checker.clause_offset[lemma + 1] = checker.clause_offset[lemma];
    };
    ensure!(cause != Clause::INVALID);
    log!(
        checker,
        3,
        "conflict arises at lemma {} in {} while propagating {} during {:?} {:?}",
        checker.clause_copy(lemma),
        checker.clause_copy(cause),
        literal,
        checker.direction,
        reason
    );
    if reason == PropagationReason::UnitInFormula {
        // TODO
        // checker.clause_core[lemma] = true;
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
                log!(
                    checker,
                    3,
                    "{} was caused by {}",
                    -checker.db[i],
                    checker.clause_copy(why_falsified)
                );
                walk_conflict_graph(checker, reason, lemma, why_falsified);
            }
        }

        // println!("MARKING {}", cause);
        checker.clause_marked[cause] = true;
        if reason == PropagationReason::UnitInFormula {
            // TODO
            // checker.clause_core[cause] = true;
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

fn forward(checker: &mut Checker) -> MaybeConflict {
    log!(checker, 1, "[forward]");
    defer_log!(checker, 1, "[forward] done\n");
    for i in 0..checker.proof.len() {
        check_watches!(checker);
        if CONFLICT
            == match checker.proof[i] {
                ProofStep::Deletion(c) => {
                    log!(checker, 1, "[forward] del {}", checker.clause_copy(c));
                    let recorded_unit = checker.clause_unit[c];
                    let level = checker.assignment.level_prior_to_assigning(recorded_unit);
                    let handle_unit_deletion = !checker.config.skip_deletions
                        && recorded_unit != Literal::TOP
                        // && clause_status_before(checker.clause(c), &checker.assignment, level)
                        //     == ClauseStatus::Unit(recorded_unit)
                            ;
                    let was_unit =
                        clause_status_before(checker.clause(c), &checker.assignment, level)
                            == ClauseStatus::Unit(recorded_unit);
                    if !was_unit || handle_unit_deletion {
                        checker.clause_active[c] = false;
                        watches_remove(checker, c);
                    }
                    if was_unit && handle_unit_deletion {
                        checker.assignment.reset(level);
                        propagate_all(checker);
                        let conflict = propagate_all_watched(checker);
                        ensure!(conflict == NO_CONFLICT);
                        check_watches!(checker);
                    }
                    NO_CONFLICT
                }
                ProofStep::Lemma(c) => {
                    ensure!(c == checker.proof_start);
                    log!(checker, 1, "[forward] add {}", checker.clause_copy(c));
                    let conflict_claimed = checker.clause(c).empty();
                    if conflict_claimed {
                        warn!("conflict claimed but not detected");
                        return NO_CONFLICT;
                    }
                    let reason = PropagationReason::UnitInFormula;
                    checker.lemma_to_level[checker.proof_start] = checker.assignment.len();
                    checker.proof_start += 1;
                    match clause_status(checker.clause(c), &checker.assignment) {
                        ClauseStatus::Falsified => {
                            propagate_literal(checker, reason, Literal::BOTTOM, c)
                        }
                        ClauseStatus::Unit(literal) => {
                            propagate_literal(checker, reason, literal, c)
                        }
                        ClauseStatus::Satisfied => NO_CONFLICT,
                        ClauseStatus::Unknown => {
                            watches_add(checker, checker.proof_start);
                            NO_CONFLICT
                        }
                    }
                }
            }
        {
            checker.proof_steps_until_conflict = i + 1;
            trace_watches(checker);
            check_watches!(checker);
            return CONFLICT;
        }
        check_watches!(checker);
    }
    check_watches!(checker);
    NO_CONFLICT
}

fn backward(checker: &mut Checker) -> bool {
    // We know that, after executing `checker.proof_steps_until_conflict` steps,
    // the formula implies a conflict.
    // First we need to analyze the conflict.
    // Clause `checker.proof_start` shall be the empty clause in the LRAT certificate.
    checker.direction = Direction::Backward;
    log!(checker, 1, "[backward]");
    println!("{}", checker.assignment);
    defer_log!(checker, 1, "[backward] done\n");
    check_watches!(checker);
    for i in (0..checker.proof_steps_until_conflict).rev() {
        let accepted = match checker.proof[i] {
            ProofStep::Deletion(c) => {
                log!(checker, 1, "[backward] del {}", checker.clause_copy(c));
                checker.clause_active[c] = true;
                match clause_status(checker.clause(c), &checker.assignment) {
                    ClauseStatus::Falsified => {
                        ensure!(false);
                    }
                    ClauseStatus::Unit(literal) => {
                        let conflict = propagate_literal(
                            checker,
                            PropagationReason::UnitInFormula,
                            literal,
                            c,
                        );
                        ensure!(conflict == NO_CONFLICT);
                    }
                    ClauseStatus::Satisfied => (),
                    ClauseStatus::Unknown => watches_add(checker, checker.proof_start),
                }
                true
            }
            ProofStep::Lemma(c) => {
                log!(checker, 1, "[backward] add {}", checker.clause_copy(c));
                println!("proof start {}", checker.proof_start);
                checker.proof_start -= 1;
                if !checker.clause(checker.proof_start).empty() {
                    watches_remove(checker, checker.proof_start);
                }
                check_watches!(checker);
                !checker.clause_marked[c] || {
                    let level = checker.lemma_to_level[c];
                    checker.assignment.reset(level);
                    println!("{}", checker.assignment);
                    trace_watches(checker);
                    propagate_all(checker);
                    println!("{}", checker.assignment);
                    trace_watches(checker);
                    check_watches!(checker);
                    println!("resetting to level {}", level);
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
        // empty file suffices
        return Ok(());
    }
    if Clause::range(0, checker.proof_start).any(|c| !checker.clause_marked[c]) {
        write!(checker.config.lrat_file, "{} d ", checker.lrat_id)?;
        for c in Clause::range(0, checker.proof_start) {
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
                if
                // TODO
                // checker.clause_marked[lemma] &&
                // checker.clause_core[lemma] &&
                true {
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
    let ok = (checker.have_empty_clause
        || CONFLICT == propagate_all_watched(checker)
        || CONFLICT == forward(checker))
        && backward(checker);
    if ok && checker.config.lrat {
        write_lrat_certificate(checker).expect("Failed to write LRAT certificate.");
    }
    ok
}
