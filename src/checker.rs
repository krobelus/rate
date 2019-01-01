//! Proof checking

use crate::{
    assignment::Assignment,
    clause::{Clause, ClauseCopy, ProofStep},
    config::unreachable,
    config::Config,
    literal::{Literal, Variable},
    memory::{Array, Offset, Slice, Stack, StackMapping},
    parser::Parser,
};
#[cfg(feature = "flame_it")]
use flamer::flame;
use std::{fmt, fs::File, io, io::Write, ops};

#[derive(Debug)]
pub struct Checker {
    assignment: Assignment,
    clause_is_a_reason: Array<Clause, bool>,
    clause_lrat_id: Array<Clause, Clause>,
    clause_offset: Array<Clause, usize>,
    clause_scheduled: Array<Clause, bool>,
    clause_pivot: Option<Array<Clause, Literal>>,
    config: Config,
    db: Array<usize, Literal>,
    implication_graph: StackMapping<Literal, bool>,
    lemma_lratlemma: Array<Clause, Stack<LRATLiteral>>,
    lemma_newly_marked_clauses: Array<Clause, Stack<Clause>>,
    lemma_revision: Array<Clause, bool>,
    literal_reason: Array<Literal, Reason>,
    lrat_id: Clause,
    maxvar: Variable,
    num_clauses: Clause,
    proof: Array<usize, ProofStep>,
    lemma: Clause, // current lemma / first lemma of proof
    proof_steps_until_conflict: usize,
    pub propcount: usize,
    resolvent: Array<Literal, bool>,
    revisions: Stack<Revision>,
    soft_propagation: bool,
    stage: Stage,
    watchlist: Array<Literal, Watchlist>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Reason {
    Assumed,
    Forced(Clause),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum LRATLiteral {
    ResolutionCandidate(Clause),
    Unit(Clause),
}

type Watchlist = Stack<Option<Clause>>;

impl Checker {
    pub fn new(parser: Parser, config: Config) -> Checker {
        let num_clauses = parser.num_clauses;
        let maxvar = parser.maxvar;
        let mut checker = Checker {
            assignment: Assignment::new(maxvar),
            clause_is_a_reason: Array::new(false, num_clauses),
            clause_lrat_id: Array::new(Clause::INVALID, num_clauses),
            clause_offset: Array::from(parser.clause_offset),
            clause_scheduled: Array::new(false, num_clauses),
            clause_pivot: None,
            config: config,
            db: Array::from(parser.db),
            soft_propagation: false,
            implication_graph: StackMapping::with_initial_value_array_size_stack_size(
                false,
                maxvar.array_size_for_literals(),
                maxvar.as_offset() + 2, // allow for a single conflict
            ),
            lemma_lratlemma: Array::new(Stack::new(), num_clauses),
            lemma_newly_marked_clauses: Array::new(Stack::new(), num_clauses),
            lemma_revision: Array::new(false, num_clauses),
            literal_reason: Array::new(
                Reason::Forced(Clause::INVALID),
                maxvar.array_size_for_literals(),
            ),
            lrat_id: Clause(0),
            maxvar: maxvar,
            num_clauses: Clause(num_clauses),
            proof: Array::from(parser.proof),
            lemma: parser.proof_start,
            proof_steps_until_conflict: usize::max_value(),
            propcount: 0,
            resolvent: Array::new(false, maxvar.array_size_for_literals()),
            revisions: Stack::with_capacity(maxvar.array_size_for_variables()),
            stage: Stage::Preprocessing,
            watchlist: Array::new(Stack::new(), maxvar.array_size_for_literals()),
        };
        checker.literal_reason[Literal::TOP] = Reason::Assumed;
        for clause in Clause::range(0, checker.lemma) {
            checker.lrat_id += 1;
            checker.clause_lrat_id[clause] = checker.lrat_id;
        }
        if checker.config.pivot_is_first_literal {
            let mut pivots = Array::new(Literal::INVALID, num_clauses);
            for clause in Clause::range(0, num_clauses) {
                if !checker.clause(clause).empty() {
                    pivots[clause] = checker.clause(clause)[0];
                }
            }
            checker.clause_pivot = Some(pivots);
        }
        checker
    }
    fn clause(&self, clause: Clause) -> Slice<Literal> {
        let range = self.clause_range(clause);
        self.db.as_slice().range(range.start, range.end)
    }
    fn clause_copy(&self, clause: Clause) -> ClauseCopy {
        ClauseCopy::new(clause, self.clause(clause))
    }
    fn clause_range(&self, clause: Clause) -> ops::Range<usize> {
        self.clause_offset[clause]..self.clause_offset[clause + 1]
    }
    fn clause_watches(&self, clause: Clause) -> (Literal, Literal) {
        (self.clause(clause)[0], self.clause(clause)[1])
    }
}

#[derive(Debug, PartialEq, Eq)]
struct MaybeConflict(bool);
const CONFLICT: MaybeConflict = MaybeConflict(true);
const NO_CONFLICT: MaybeConflict = MaybeConflict(false);

/// Enable the question mark operator to return early on conflict.
///
/// # Examples
///
/// Here, if `propagate()` returns `CONFLICT`, then that is returned.  Otherwise, the result is
/// `NO_CONFLICT` because of the second expression.
/// ```
/// {
///     propagate()?;
///     NO_CONFLICT
/// }
/// ```
impl ops::Try for MaybeConflict {
    type Ok = ();
    type Error = ();
    fn into_result(self) -> Result<Self::Ok, Self::Error> {
        match self {
            CONFLICT => Err(()),
            _ => Ok(()),
        }
    }
    fn from_error(_: Self::Error) -> Self {
        CONFLICT
    }
    fn from_ok(_: Self::Ok) -> Self {
        NO_CONFLICT
    }
}

fn schedule(checker: &mut Checker, clause: Clause) {
    if checker.soft_propagation && !checker.clause_scheduled[clause] {
        let lemma = checker.lemma;
        checker.lemma_newly_marked_clauses[lemma].push(clause);
    }
    checker.clause_scheduled[clause] = true;
}

fn set_reason_flag(checker: &mut Checker, lit: Literal, value: bool) {
    match checker.literal_reason[lit] {
        Reason::Forced(clause) => checker.clause_is_a_reason[clause] = value,
        Reason::Assumed => (),
    }
}

fn assign(checker: &mut Checker, literal: Literal, reason: Reason) -> MaybeConflict {
    checker.propcount += 1;
    requires!(!checker.assignment[literal]);
    checker.literal_reason[literal] = reason;
    checker.assignment.push(literal);
    if !checker.soft_propagation {
        set_reason_flag(checker, literal, true);
    }
    if checker.assignment[-literal] {
        CONFLICT
    } else {
        NO_CONFLICT
    }
}

fn propagate(checker: &mut Checker) -> MaybeConflict {
    while let Some(literal) = checker.assignment.next_unprocessed() {
        // NOTE this will return upon conflict.
        propagate_literal(checker, literal)?;
        watchlist_compact(checker, literal);
    }
    NO_CONFLICT
}

fn propagate_literal(checker: &mut Checker, literal: Literal) -> MaybeConflict {
    requires!(checker.assignment[literal]);
    requires!(checker.literal_reason[literal] != Reason::Forced(Clause::INVALID));
    for i in 0..checker.watchlist[-literal].len() {
        if checker.watchlist[-literal][i].is_some() {
            watches_align(checker, -literal, i)?;
        }
    }
    NO_CONFLICT
}

macro_rules! preserve_assignment {
    ($checker:expr, $computation:expr) => {{
        let trace_length = $checker.assignment.len();
        let result = $computation;
        while $checker.assignment.len() > trace_length {
            $checker.assignment.pop();
        }
        $checker.assignment.first_unprocessed = trace_length;
        result
    }};
}

fn collect_resolution_candidates(checker: &Checker, pivot: Literal) -> Stack<Clause> {
    let mut candidates = Stack::new();
    for lit in Literal::all(checker.maxvar) {
        for i in 0..checker.watchlist[lit].len() {
            if let Some(clause) = checker.watchlist[lit][i] {
                if checker.clause(clause)[0] == lit
                    && checker
                        .clause(clause)
                        .iter()
                        .any(|&literal| literal == -pivot)
                {
                    candidates.push(clause);
                }
            }
        }
    }
    candidates.sort_unstable(); // resolution candidates in an LRAT proof have to be sorted
    candidates
}

fn rup(checker: &mut Checker, clause: Clause, pivot: Literal) -> bool {
    assignment_invariants(checker);
    requires!(checker.assignment.next_unprocessed().is_none());
    let mut conflict_literal = None;
    for offset in checker.clause_range(clause) {
        let unit = checker.db[offset];
        if unit == Literal::BOTTOM || unit == -pivot {
            continue;
        }
        if !checker.assignment[-unit] {
            if assign(checker, -unit, Reason::Assumed) == CONFLICT && conflict_literal.is_none() {
                conflict_literal = Some(-unit);
            }
        }
    }
    match conflict_literal {
        Some(literal) => {
            extract_dependencies(checker, literal);
            true
        }
        None => {
            if propagate(checker) == CONFLICT {
                extract_dependencies_for_last_literal(checker);
                true
            } else {
                false
            }
        }
    }
}

fn rat(checker: &mut Checker, pivot: Literal) -> bool {
    assignment_invariants(checker);
    let lemma = checker.lemma;
    let resolution_candidates = collect_resolution_candidates(checker, pivot);
    log!(
        checker,
        2,
        "RAT check on {} with pivot {}, {}",
        checker.clause_copy(lemma),
        pivot,
        checker.assignment
    );
    resolution_candidates.iter().all(|&resolution_candidate| {
        preserve_assignment!(
            checker,
            (!checker.config.unmarked_rat_candidates
                && !checker.clause_scheduled[resolution_candidate])
                || {
                    watch_invariants(checker);
                    // During the RUP check, -pivot was an assumption.  We need to change the
                    // reason to the clause we are resolving with to appease LRAT checkers.
                    checker.literal_reason[-pivot] = Reason::Forced(resolution_candidate);
                    log!(
                        checker,
                        2,
                        "Resolving with {}",
                        checker.clause_copy(resolution_candidate)
                    );
                    checker.lemma_lratlemma[lemma]
                        .push(LRATLiteral::ResolutionCandidate(resolution_candidate));
                    rup(checker, resolution_candidate, pivot)
                }
        )
    })
}

fn check_inference(checker: &mut Checker) -> bool {
    let lemma = checker.lemma;
    checker.soft_propagation = true;
    let copy = checker.clause_copy(lemma);
    for offset in checker.clause_range(lemma) {
        let lit = checker.db[offset];
        checker.resolvent[lit] = true;
    }
    let pivot_index = copy.iter().position(|&pivot| {
        watch_invariants(checker);
        checker.lemma_lratlemma[lemma].clear();
        pivot != Literal::BOTTOM
            && match &checker.clause_pivot {
                None => true,
                Some(pivots) => pivots[lemma] == pivot,
            }
            && preserve_assignment!(checker, rup(checker, lemma, pivot) || rat(checker, pivot))
    });
    for offset in checker.clause_range(lemma) {
        let lit = checker.db[offset];
        checker.resolvent[lit] = false;
    }
    checker.soft_propagation = false;
    if let Some(i) = pivot_index {
        // Make pivot the first literal in the LRAT proof.
        let head = checker.clause_range(lemma).start;
        checker.db.as_mut_slice().swap(head, head + i);
        true
    } else {
        echo!("c RAT check failed for {}", checker.clause_copy(lemma));
        false
    }
}

fn extract_dependencies_for_last_literal(checker: &mut Checker) {
    let last_assigned = checker.assignment.peek();
    extract_dependencies(checker, last_assigned)
}

fn extract_dependencies(checker: &mut Checker, conflict_literal: Literal) {
    let lemma = checker.lemma;
    assignment_invariants(checker);
    requires!(checker.implication_graph.empty());
    fn add_cause_of_conflict(checker: &mut Checker, literal: Literal) {
        match checker.literal_reason[literal] {
            Reason::Assumed => (),
            Reason::Forced(_clause) => {
                checker.implication_graph.push(literal, true);
            }
        }
    }
    add_cause_of_conflict(checker, conflict_literal);
    add_cause_of_conflict(checker, -conflict_literal);
    let mut i = 0;
    while i < checker.implication_graph.len() {
        let pivot = checker.implication_graph.stack_at(i);
        invariant!(checker.assignment[pivot]);
        match checker.literal_reason[pivot] {
            Reason::Assumed => {
                // log!(checker, 3, "{} was assumed", pivot);
            }
            Reason::Forced(clause) => {
                schedule(checker, clause);
                for offset in checker.clause_range(clause) {
                    let lit = checker.db[offset];
                    if lit != pivot
                        && !checker.implication_graph[-lit]
                        && checker.literal_reason[-lit] != Reason::Assumed
                    {
                        checker.implication_graph.push(-lit, true);
                    }
                }
            }
        }
        i += 1;
    }
    let mut relevant_literals = Stack::new();
    for &literal in &checker.implication_graph {
        match checker.literal_reason[literal] {
            Reason::Forced(clause) => {
                invariant!(clause < lemma);
                relevant_literals.push(literal);
            }
            Reason::Assumed => unreachable(),
        }
    }
    relevant_literals
        .sort_unstable_by_key(|&literal| checker.assignment.position_in_trace(literal));
    let num_clauses = lemma.as_offset();
    let mut reason_clauses =
        StackMapping::with_initial_value_array_size_stack_size(false, num_clauses, num_clauses);
    log!(checker, 3, "Resolution chain:");
    for &literal in &relevant_literals {
        match checker.literal_reason[literal] {
            Reason::Forced(clause) => {
                if !reason_clauses[clause] {
                    log!(checker, 3, "{}:\t{}", literal, checker.clause_copy(clause));
                    reason_clauses.push(clause, true);
                }
            }
            Reason::Assumed => unreachable(),
        }
    }
    for &clause in &reason_clauses {
        checker.lemma_lratlemma[lemma].push(LRATLiteral::Unit(clause));
    }
    checker.implication_graph.clear();
}

#[derive(Debug, PartialEq, Eq)]
enum Stage {
    Preprocessing,
    Verification,
}

fn add_premise(checker: &mut Checker, clause: Clause) -> MaybeConflict {
    watches_add(checker, clause)?;
    propagate(checker)
}

fn close_proof(checker: &mut Checker, steps_until_conflict: usize) -> bool {
    checker.proof_steps_until_conflict = steps_until_conflict;
    let clause = checker.lemma;
    checker.clause_offset[clause + 1] = checker.clause_offset[clause];
    schedule(checker, clause);
    checker.proof[checker.proof_steps_until_conflict] = ProofStep::Lemma(clause);
    true
}

#[cfg_attr(feature = "flame_it", flame)]
fn preprocess(checker: &mut Checker) -> bool {
    log!(checker, 1, "[preprocess]");
    defer_log!(checker, 1, "[preprocess] done\n");
    for clause in Clause::range(0, checker.lemma) {
        if checker.clause(clause).empty() {
            return close_proof(checker, 0);
        }
        if add_premise(checker, clause) == CONFLICT {
            extract_dependencies_for_last_literal(checker);
            return close_proof(checker, 0);
        }
    }
    for i in 0..checker.proof.len() {
        watch_invariants(checker);
        match checker.proof[i] {
            ProofStep::Deletion(clause) => {
                log!(
                    checker,
                    1,
                    "[preprocess] del {}",
                    checker.clause_copy(clause)
                );
                if checker.config.skip_deletions {
                    if !checker.clause_is_a_reason[clause] {
                        watches_remove(checker, clause);
                    }
                } else {
                    watches_remove(checker, clause);
                    if checker.clause_is_a_reason[clause] {
                        revision_create(checker, clause);
                    }
                }
            }
            ProofStep::Lemma(clause) => {
                invariant!(clause == checker.lemma);
                log!(
                    checker,
                    1,
                    "[preprocess] add {}",
                    checker.clause_copy(clause)
                );
                let conflict_claimed = checker.clause(clause).empty();
                if conflict_claimed {
                    warn!("conflict claimed but not detected");
                    return false;
                }
                checker.lemma += 1;
                watches_add(checker, clause);
                if propagate(checker) == CONFLICT {
                    extract_dependencies_for_last_literal(checker);
                    return close_proof(checker, i + 1);
                }
            }
        };
    }
    false
}

#[cfg_attr(feature = "flame_it", flame)]
fn verify(checker: &mut Checker) -> bool {
    checker.stage = Stage::Verification;
    log!(checker, 1, "[verify]");
    defer_log!(checker, 1, "[verify] done\n");
    for i in (0..checker.proof_steps_until_conflict).rev() {
        watch_invariants(checker);
        let accepted = match checker.proof[i] {
            ProofStep::Deletion(clause) => {
                log!(checker, 1, "[verify] del {}", checker.clause_copy(clause));
                if !checker.config.skip_deletions && checker.lemma_revision[clause] {
                    let mut revision = checker.revisions.pop();
                    revision_apply(checker, &mut revision);
                    watches_reset(checker, &mut revision);
                }
                watches_add(checker, clause);
                true
            }
            ProofStep::Lemma(_clause) => {
                checker.lemma -= 1;
                let lemma = checker.lemma;
                invariant!(_clause == lemma);
                watches_remove(checker, lemma);
                unpropagate_unit(checker, lemma);
                if checker.clause_scheduled[lemma] {
                    log!(checker, 1, "[verify] add {}", checker.clause_copy(lemma));
                    check_inference(checker)
                } else {
                    log!(checker, 2, "[verify] skip {}", checker.clause_copy(lemma));
                    true
                }
            }
        };
        if !accepted {
            return false;
        }
    }
    true
}

fn unpropagate_unit(checker: &mut Checker, clause: Clause) {
    if !checker.clause_is_a_reason[clause] {
        return;
    }
    checker
        .clause_range(clause)
        .find(|&offset| checker.assignment[checker.db[offset]])
        .map(|offset| {
            let unit = checker.db[offset];
            let trace_length = checker.assignment.position_in_trace(unit);
            while checker.assignment.len() > trace_length {
                let lit = checker.assignment.pop();
                set_reason_flag(checker, lit, true);
            }
            checker.assignment.first_unprocessed = trace_length;
        });
}

fn write_lrat_certificate(checker: &mut Checker) -> io::Result<()> {
    if checker.config.lrat_filename.is_empty() {
        return Ok(());
    }
    let mut file = File::create(checker.config.lrat_filename.clone())?;
    let num_clauses = checker.lemma.as_offset() + checker.proof_steps_until_conflict;
    let mut clause_deleted = Array::new(false, num_clauses);
    let empty_clause_as_premise =
        Clause::range(0, checker.lemma).any(|clause| checker.clause(clause).empty());
    if empty_clause_as_premise {
        // write an empty LRAT certificate, this is accepted by lratcheck
        return Ok(());
    }
    #[derive(Debug, PartialEq, Eq)]
    enum State {
        Lemma,
        InDeletionChain,
    };
    let mut state = State::InDeletionChain;
    open_deletion_chain(checker, &mut file, checker.lemma - 1)?;
    invariant!(checker.lrat_id == checker.clause_lrat_id[checker.lemma - 1]);
    // delete lemmas that were never used
    for clause in Clause::range(0, checker.lemma) {
        if !checker.clause_scheduled[clause] {
            write!(file, "{} ", checker.clause_lrat_id[clause])?;
            clause_deleted[clause] = true;
        }
    }
    let mut i = 0;
    while i <= checker.proof_steps_until_conflict {
        let proof_step = checker.proof[i];
        match state {
            State::Lemma => match proof_step {
                ProofStep::Lemma(lemma) => {
                    if checker.clause_scheduled[lemma] {
                        checker.lrat_id += 1;
                        checker.clause_lrat_id[lemma] = checker.lrat_id;
                        write!(file, "{} ", checker.clause_lrat_id[lemma])?;
                        checker.clause_copy(lemma).dimacs(&mut file)?;
                        write!(file, " ")?;
                        for hint in &checker.lemma_lratlemma[lemma] {
                            match hint {
                                &LRATLiteral::ResolutionCandidate(clause) => {
                                    write!(file, "-{} ", checker.clause_lrat_id[clause])
                                }
                                &LRATLiteral::Unit(clause) => {
                                    invariant!(checker.clause_scheduled[clause]);
                                    invariant!(checker.clause_lrat_id[clause] != Clause::INVALID);
                                    write!(file, "{} ", checker.clause_lrat_id[clause])
                                }
                            }?;
                        }
                        write!(file, "0\n")?;
                        open_deletion_chain(checker, &mut file, lemma)?;
                        if !checker.lemma_newly_marked_clauses[lemma].empty() {
                            for &clause in &checker.lemma_newly_marked_clauses[lemma] {
                                write_deletion(checker, &mut file, &mut clause_deleted, clause)?;
                            }
                        }
                        state = State::InDeletionChain;
                    }
                    i += 1;
                }
                ProofStep::Deletion(_clause) => unreachable(),
            },
            State::InDeletionChain => match proof_step {
                ProofStep::Lemma(lemma) => {
                    if checker.clause_scheduled[lemma] {
                        close_deletion_chain(&mut file)?;
                        state = State::Lemma;
                    } else {
                        i += 1;
                    }
                }
                ProofStep::Deletion(clause) => {
                    invariant!(
                        (checker.clause_lrat_id[clause] == Clause::INVALID)
                            == (clause >= checker.lemma && !checker.clause_scheduled[clause])
                    );
                    if checker.clause_lrat_id[clause] != Clause::INVALID {
                        write_deletion(checker, &mut file, &mut clause_deleted, clause)?;
                    }
                    i += 1;
                }
            },
        }
    }
    if state == State::InDeletionChain {
        close_deletion_chain(&mut file)?;
    }
    fn open_deletion_chain(checker: &Checker, file: &mut File, lemma: Clause) -> io::Result<()> {
        write!(file, "{} d ", checker.clause_lrat_id[lemma])
    }
    fn close_deletion_chain(file: &mut File) -> io::Result<()> {
        write!(file, "0\n")
    }
    fn write_deletion(
        checker: &Checker,
        file: &mut File,
        clause_deleted: &mut Array<Clause, bool>,
        clause: Clause,
    ) -> io::Result<()> {
        if !clause_deleted[clause] {
            clause_deleted[clause] = true;
            write!(file, "{} ", checker.clause_lrat_id[clause])
        } else {
            Ok(())
        }
    }
    Ok(())
}

pub fn check(checker: &mut Checker) -> bool {
    let ok = preprocess(checker) && verify(checker);
    if ok {
        write_lrat_certificate(checker).expect("Failed to write LRAT certificate.");
    }
    ok
}

fn watches_add(checker: &mut Checker, clause: Clause) -> MaybeConflict {
    log!(
        checker,
        2,
        "initializing watches for {}",
        checker.clause_copy(clause)
    );
    let size = checker.clause(clause).len();
    invariant!(size >= 2);
    let range = checker.clause_range(clause);
    match first_non_falsified(&checker, clause, range.start) {
        Some(i0) => {
            let l0 = checker.db[i0];
            checker.db.as_mut_slice().swap(range.start, i0);
            checker.watchlist[l0].push(Some(clause));
            let l1 = match first_non_falsified(checker, clause, range.start + 1) {
                Some(i1) => {
                    let l1 = checker.db[i1];
                    checker.db.as_mut_slice().swap(range.start + 1, i1);
                    l1
                }
                None => {
                    if !checker.assignment[l0] {
                        let result = assign(checker, l0, Reason::Forced(clause));
                        invariant!(result == NO_CONFLICT);
                    }
                    checker.db[range.start + 1]
                }
            };
            checker.watchlist[l1].push(Some(clause));
            NO_CONFLICT
        }
        None => CONFLICT,
    }
}

fn watches_remove_at(checker: &mut Checker, lit: Literal, position_in_watchlist: usize) {
    checker.watchlist[lit][position_in_watchlist] = None;
}

fn watches_find_and_remove(checker: &mut Checker, lit: Literal, clause: Clause) {
    requires!(lit != Literal::TOP);
    checker.watchlist[lit]
        .iter()
        .position(|&watched| watched == Some(clause))
        .map(|position| watches_remove_at(checker, lit, position));
}

fn watches_find_and_remove_all(checker: &mut Checker, lit: Literal, clause: Clause) {
    for i in 0..checker.watchlist[lit].len() {
        if checker.watchlist[lit][i] == Some(clause) {
            watches_remove_at(checker, lit, i);
        }
    }
}

fn watches_remove(checker: &mut Checker, clause: Clause) -> Option<()> {
    log!(
        checker,
        2,
        "removing watches for {}",
        checker.clause_copy(clause)
    );
    let (l0, l1) = checker.clause_watches(clause);
    watches_find_and_remove_all(checker, l0, clause);
    watches_find_and_remove_all(checker, l1, clause);
    Some(())
}

fn watches_align(
    checker: &mut Checker,
    literal: Literal,
    position_in_watchlist: usize,
) -> MaybeConflict {
    let clause = checker.watchlist[literal][position_in_watchlist].unwrap();
    requires!(clause < checker.lemma);
    let (l0, l1) = checker.clause_watches(clause);
    if checker.assignment[l0] || checker.assignment[l1] {
        return NO_CONFLICT;
    }
    let head = checker.clause_range(clause).start;
    if literal == l0 {
        checker.db[head] = checker.db[head + 1];
    }
    match first_non_falsified(checker, clause, head + 2) {
        Some(offset) => {
            let new = checker.db[offset];
            checker.db[offset] = literal;
            checker.db[head + 1] = new;
            watches_remove_at(checker, literal, position_in_watchlist);
            checker.watchlist[new].push(Some(clause));
            NO_CONFLICT
        }
        None => {
            checker.db[head + 1] = literal;
            let unit = checker.db[head];
            assign(checker, unit, Reason::Forced(clause))
        }
    }
}

fn watches_revise(
    checker: &mut Checker,
    lit: Literal,
    clause: Clause,
    position_in_watchlist: usize,
) {
    // NOTE swap them to simplify this
    let (l0, _l1) = checker.clause_watches(clause);
    let head = checker.clause_range(clause).start;
    let my_offset = head + if l0 == lit { 0 } else { 1 };
    let other_literal_offset = head + if l0 == lit { 1 } else { 0 };
    let other_literal = checker.db[other_literal_offset];
    if !checker.assignment[-other_literal] {
        return;
    }
    match first_non_falsified(checker, clause, head + 2) {
        None => {
            if !checker.assignment[lit] {
                assign(checker, lit, Reason::Forced(clause));
            }
        }
        Some(offset) => {
            let new_literal = checker.db[offset];
            checker.db.as_mut_slice().swap(my_offset, offset);
            watches_remove_at(checker, lit, position_in_watchlist);
            checker.watchlist[new_literal].push(Some(clause));
        }
    };
}

fn watches_reset(checker: &mut Checker, revision: &Revision) {
    for &literal in &revision.cone {
        watches_reset_list(checker, literal);
        watches_reset_list(checker, -literal);
    }
}

fn watches_reset_list(checker: &mut Checker, literal: Literal) {
    for i in 0..checker.watchlist[literal].len() {
        if checker.watchlist[literal][i].is_some() {
            watches_reset_list_at(checker, literal, i);
        }
    }
}

fn watches_reset_list_at(checker: &mut Checker, literal: Literal, position_in_watchlist: usize) {
    let clause =
        checker.watchlist[literal][position_in_watchlist].expect("can't reset - watch was deleted");
    let (l0, l1) = checker.clause_watches(clause);
    if !checker.assignment[-l0] && !checker.assignment[-l1] {
        // watches are correct
        return;
    }
    let head = checker.clause_range(clause).start;
    if literal != l0 {
        requires!(literal == l1);
        checker.db.as_mut_slice().swap(head, head + 1);
    }
    let other_lit = checker.db[head + 1];
    let offset = head;
    let mut first_offset = head;
    let mut best_offset = head;
    let mut best_position = usize::max_value();
    let ok = watch_find(
        checker,
        clause,
        &mut first_offset,
        &mut best_offset,
        &mut best_position,
    );
    invariant!(ok, "broken invariant");
    let mut second_offset = first_offset + 1;
    let ok = watch_find(
        checker,
        clause,
        &mut second_offset,
        &mut best_offset,
        &mut best_position,
    );
    if !ok {
        if first_offset > best_offset {
            second_offset = first_offset;
            first_offset = best_offset;
        } else {
            second_offset = best_offset;
        }
    }
    // At this point, we have ensured that first_offset < second_offset
    // There are four cases:
    //   A) first_offset is in 0, second_offset is in 1
    //   B) first_offset is in 0, second_offset is in >=2
    //   C) first_offset is in 1, second_offset is in >=2
    //   D) both first_offset and second_offset are in >=2
    if offset == first_offset {
        if offset + 1 == second_offset {
            // Case A: nothing to do!
            return;
        } else {
            // Case B: clause will not be watched on other_lit, but on checker.db[second_offset] instead.
            watches_find_and_remove(checker, other_lit, clause);
            let tmp = checker.db[second_offset];
            checker.db[offset + 1] = tmp;
            checker.db[second_offset] = other_lit;
            checker.watchlist[tmp].push(Some(clause));
        }
    } else {
        // Cases C and D: clause will not be watched on literal, but on *second_offset instead.
        watches_remove_at(checker, literal, position_in_watchlist);
        checker.db[offset] = checker.db[second_offset];
        checker.db[second_offset] = literal;
        checker.watchlist[checker.db[offset]].push(Some(clause)); // Case C: additionally, clause will still be watched on other_lit
        if offset + 1 != first_offset {
            // Case D: additionally, clause will not be watched on other_lit, but on checker.db[offset + 1] instead.
            watches_find_and_remove(checker, other_lit, clause);
            checker.db[offset + 1] = checker.db[first_offset];
            checker.db[first_offset] = other_lit;
            checker.watchlist[checker.db[offset + 1]].push(Some(clause));
        }
    }
}

fn watch_find<'a>(
    checker: &Checker,
    clause: Clause,
    offset: &'a mut usize,
    best_false: &'a mut usize,
    best_position: &'a mut usize,
) -> bool {
    let end = checker.clause_range(clause).end;
    while *offset < end {
        let literal = checker.db[*offset];
        if checker.assignment[-literal] {
            let position_in_trace = checker.assignment.position_in_trace(-literal);
            if position_in_trace > *best_position {
                *best_position = position_in_trace;
                *best_false = *offset;
            }
            *offset += 1;
        } else {
            return true;
        }
    }
    false
}

fn watchlist_compact(checker: &mut Checker, lit: Literal) {
    let mut i = 0;
    while i < checker.watchlist[-lit].len() {
        if checker.watchlist[-lit][i].is_none() {
            checker.watchlist[-lit].swap_remove(i);
        } else {
            i += 1;
        }
    }
}

fn watchlist_revise(checker: &mut Checker, lit: Literal) {
    (0..checker.watchlist[lit].len()).for_each(|i| {
        if let Some(clause) = checker.watchlist[lit][i] {
            watches_revise(checker, lit, clause, i)
        }
    });
    watchlist_compact(checker, lit);
}

fn first_non_falsified(checker: &Checker, clause: Clause, start: usize) -> Option<usize> {
    (start..checker.clause_range(clause).end).find(|&i| !checker.assignment[-checker.db[i]])
}

fn revision_create(checker: &mut Checker, clause: Clause) {
    log!(checker, 1, "{}", checker.assignment);
    let unit = *checker
        .clause(clause)
        .iter()
        .find(|&lit| checker.assignment[*lit])
        .unwrap();
    let unit_position = checker.assignment.position_in_trace(unit);
    checker.lemma_revision[clause] = true;
    let mut revision = Revision {
        cone: StackMapping::with_initial_value_array_size_stack_size(
            false,
            checker.maxvar.array_size_for_literals(),
            checker.maxvar.as_offset(),
        ),
        position_in_trace: Stack::new(),
        reason_clause: Stack::new(),
    };
    add_to_revision(checker, &mut revision, unit);
    let mut next_position_to_overwrite = unit_position;
    for position in unit_position + 1..checker.assignment.len() {
        let lit = checker.assignment.trace_at(position);
        if is_in_cone(checker, lit, &revision.cone) {
            add_to_revision(checker, &mut revision, lit);
        } else {
            checker
                .assignment
                .move_to(position, next_position_to_overwrite);
            next_position_to_overwrite += 1;
        }
    }
    checker.assignment.resize_trace(next_position_to_overwrite);
    for &literal in &revision.cone {
        watchlist_revise(checker, literal);
    }
    log!(checker, 1, "Created {}\n{}", revision, checker.assignment);
    checker.revisions.push(revision);
    fn add_to_revision(checker: &mut Checker, revision: &mut Revision, lit: Literal) {
        checker.assignment.unassign(lit);
        set_reason_flag(checker, lit, true);
        revision.cone.push(lit, true);
        revision
            .position_in_trace
            .push(checker.assignment.position_in_trace(lit));
        match checker.literal_reason[lit] {
            Reason::Assumed => unreachable(),
            Reason::Forced(clause) => revision.reason_clause.push(clause),
        }
    }
    fn is_in_cone(checker: &Checker, literal: Literal, cone: &StackMapping<Literal, bool>) -> bool {
        match checker.literal_reason[literal] {
            Reason::Assumed => unreachable(),
            Reason::Forced(clause) => checker
                .clause(clause)
                .iter()
                .any(|&lit| lit != literal && cone[-lit]),
        }
    }
}

#[derive(Debug)]
struct Revision {
    cone: StackMapping<Literal, bool>,
    position_in_trace: Stack<usize>,
    reason_clause: Stack<Clause>,
}

impl fmt::Display for Revision {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Revision:\n")?;
        for (i, literal) in self.cone.iter().enumerate() {
            write!(
                f,
                "\t#{}: {} [{}]\n",
                self.position_in_trace[i], literal, self.reason_clause[i]
            )?;
        }
        write!(f, "")
    }
}

fn revision_apply(checker: &mut Checker, revision: &mut Revision) {
    let mut introductions = 0;
    let mut literals_to_revise = revision.cone.len();
    for &literal in &revision.cone {
        set_reason_flag(checker, literal, false);
        if !checker.assignment[literal] {
            introductions += 1;
        }
    }
    log!(checker, 1, "Applying {}{}", revision, checker.assignment);
    let mut right_position = checker.assignment.len() + introductions;
    let mut left_position = right_position - 1 - literals_to_revise;
    checker.assignment.resize_trace(right_position);
    // Introduce the revisions in the trace, starting from the ones with the
    // highest offset in the trace.
    while literals_to_revise > 0 {
        right_position -= 1;
        let literal;
        if right_position == revision.position_in_trace[literals_to_revise - 1] {
            literals_to_revise -= 1;
            literal = revision.cone.stack_at(literals_to_revise);
            checker.literal_reason[literal] =
                Reason::Forced(revision.reason_clause[literals_to_revise]);
            set_reason_flag(checker, literal, true);
        } else {
            literal = checker.assignment.trace_at(left_position);
            left_position -= 1;
        }
        checker
            .assignment
            .set_literal_at_level(literal, right_position);
    }
    log!(checker, 1, "Applied revision:\n{}", checker.assignment);
}

fn assignment_invariants(checker: &Checker) {
    invariant!({
        for &literal in checker.assignment.into_iter() {
            match checker.literal_reason[literal] {
                Reason::Forced(clause) => invariant!(
                    clause < checker.lemma,
                    "{} is assigned because of {} in {}",
                    literal,
                    checker.clause_copy(clause),
                    checker.assignment
                ),
                Reason::Assumed => (),
            }
        }
        for position in 0..checker.assignment.len() {
            let literal = checker.assignment.trace_at(position);
            invariant!(position == checker.assignment.position_in_trace(literal));
        }
        true
    })
}

fn watch_invariants(checker: &Checker) {
    invariant!({
        fn is_assigned(checker: &Checker, lit: Literal) -> bool {
            checker.assignment[lit] || checker.assignment[-lit]
        }
        // each watch points to a clause that is neither falsified nor satisfied
        for lit in Literal::all(checker.maxvar) {
            for watch in &checker.watchlist[lit] {
                if let &Some(clause) = watch {
                    let (l0, l1) = checker.clause_watches(clause);
                    invariant!(
                        is_assigned(checker, l0) ||
                        is_assigned(checker, l1) ||
                        (!is_assigned(checker, -l0) && !is_assigned(checker, -l1))
                        ,
                        format!("each watched clause needs at least one unassigned literal: violated in {} - {}", checker.clause_copy(clause),
                        checker.assignment)
                    );
                }
            }
        }
        true
    });
}
