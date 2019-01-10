//! Proof checking

use crate::{
    assignment::Assignment,
    clause::{Clause, ClauseCopy, ProofStep},
    config::unreachable,
    config::Config,
    literal::{Literal, Variable},
    memory::{Array, Offset, Slice, Stack, StackMapping},
    parser::Parser,
    watchlist::{
        revision_apply, revision_create, watch_add, watch_invariants, watch_remove_at, watches_add,
        watches_find_and_remove_all, watches_remove, watchlist, Mode, Watchlist,
    },
};
use ansi_term::Colour;
#[cfg(feature = "flame_it")]
use flamer::flame;
use std::{fmt, fs::File, io, io::Write, ops};

#[derive(Debug)]
pub struct Checker {
    pub assignment: Assignment,
    clause_is_a_reason: Array<Clause, bool>,
    clause_lrat_id: Array<Clause, Clause>,
    clause_offset: Array<Clause, usize>,
    pub clause_scheduled: Array<Clause, bool>,
    pub clause_in_watchlist: Array<Clause, bool>,
    clause_pivot: Option<Array<Clause, Literal>>,
    pub config: Config,
    pub db: Array<usize, Literal>,
    implication_graph: StackMapping<Literal, bool>,
    lemma_lratlemma: Array<Clause, Stack<LRATLiteral>>,
    lemma_newly_marked_clauses: Array<Clause, Stack<Clause>>,
    pub lemma_revision: Array<Clause, bool>,
    pub literal_reason: Array<Literal, Reason>,
    lrat_id: Clause,
    pub maxvar: Variable,
    pub proof: Array<usize, ProofStep>,
    lemma: Clause, // current lemma / first lemma of proof
    proof_steps_until_conflict: usize,
    pub revisions: Stack<Revision>,
    soft_propagation: bool,
    stage: Stage,
    pub watchlist_noncore: Array<Literal, Watchlist>,
    pub watchlist_core: Array<Literal, Watchlist>,
    pub processed: usize,
    rejection: Rejection,

    pub premise_length: usize,
    pub rat_introductions: usize,
    pub clause_deletions: usize,
    pub skipped_deletions: usize,
    pub reason_deletions: usize,

    pub assign_count: usize,
    pub watch_reset_count: usize,
    pub watch_reset_list_count: usize,
}

#[derive(Debug)]
struct Rejection {
    failed_proof_step: usize,
    pivot: Option<Literal>,
    resolved_with: Option<Clause>,
    stable_assignment: Option<Assignment>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Reason {
    Assumed,
    Forced(Clause),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum LRATLiteral {
    ResolutionCandidate(Clause),
    Unit(Clause),
}

#[derive(Debug)]
pub struct Revision {
    pub cone: StackMapping<Literal, bool>,
    pub position_in_trace: Stack<usize>,
    pub reason_clause: Stack<Clause>,
}

impl Checker {
    pub fn new(parser: Parser, config: Config) -> Checker {
        let num_clauses = parser.num_clauses;
        let maxvar = parser.maxvar;
        let mut checker = Checker {
            assignment: Assignment::new(maxvar),
            clause_is_a_reason: Array::new(false, num_clauses),
            clause_lrat_id: Array::new(Clause::UNINITIALIZED, num_clauses),
            clause_offset: Array::from(parser.clause_offset),
            clause_scheduled: Array::new(false, num_clauses),
            clause_in_watchlist: Array::new(false, num_clauses),
            clause_pivot: parser.clause_pivot.map(Array::from),
            config: config,
            db: Array::from(parser.db),
            soft_propagation: false,
            implication_graph: StackMapping::with_array_value_size_stack_size(
                false,
                maxvar.array_size_for_literals(),
                maxvar.as_offset() + 1, // need + 1 to hold a conflicting literal
            ),
            lemma_lratlemma: Array::new(Stack::new(), num_clauses),
            lemma_newly_marked_clauses: Array::new(Stack::new(), num_clauses),
            lemma_revision: Array::new(false, num_clauses),
            literal_reason: Array::new(
                Reason::Forced(Clause::NEVER_READ),
                maxvar.array_size_for_literals(),
            ),
            lrat_id: Clause(0),
            maxvar: maxvar,
            proof: Array::from(parser.proof),
            lemma: parser.proof_start,
            proof_steps_until_conflict: usize::max_value(),
            revisions: Stack::with_capacity(maxvar.array_size_for_variables()),
            stage: Stage::Preprocessing,
            watchlist_noncore: Array::new(Stack::new(), maxvar.array_size_for_literals()),
            watchlist_core: Array::new(Stack::new(), maxvar.array_size_for_literals()),
            processed: 1, // skip Literal::TOP
            rejection: Rejection::new(),

            premise_length: parser.proof_start.as_offset(),
            rat_introductions: 0,
            clause_deletions: 0,
            skipped_deletions: 0,
            reason_deletions: 0,
            assign_count: 0,
            watch_reset_count: 0,
            watch_reset_list_count: 0,
        };
        checker.literal_reason[Literal::TOP] = Reason::Assumed;
        for clause in Clause::range(0, checker.lemma) {
            checker.lrat_id += 1;
            checker.clause_lrat_id[clause] = checker.lrat_id;
        }
        checker
    }
    pub fn clause(&self, clause: Clause) -> Slice<Literal> {
        let range = self.clause_range(clause);
        self.db.as_slice().range(range.start, range.end)
    }
    pub fn clause_copy(&self, clause: Clause) -> ClauseCopy {
        ClauseCopy::new(clause, self.clause(clause))
    }
    pub fn clause_range(&self, clause: Clause) -> ops::Range<usize> {
        self.clause_offset[clause]..self.clause_offset[clause + 1]
    }
    pub fn clause_watches(&self, clause: Clause) -> (Literal, Literal) {
        (self.clause(clause)[0], self.clause(clause)[1])
    }
    pub fn clause_mode(&self, clause: Clause) -> Mode {
        if self.config.no_core_first {
            Mode::Core
        } else {
            match self.clause_scheduled[clause] {
                true => Mode::Core,
                false => Mode::NonCore,
            }
        }
    }
    fn mode_non_core(&self) -> Mode {
        if self.config.no_core_first {
            Mode::Core
        } else {
            Mode::NonCore
        }
    }

    #[allow(dead_code)]
    fn clause_colorized(&self, clause: Clause) -> String {
        let mut result = String::new();
        for &literal in self.clause(clause) {
            let style = match (self.assignment[literal], self.assignment[-literal]) {
                (true, true) => Colour::Purple,
                (true, false) => Colour::Green,
                (false, true) => Colour::Red,
                (false, false) => Colour::Yellow,
            }
            .normal();
            result += &format!("{}", style.paint(&format!("{} ", literal)));
        }
        result
    }
}

impl Rejection {
    fn new() -> Rejection {
        Rejection {
            failed_proof_step: usize::max_value(),
            pivot: None,
            resolved_with: None,
            stable_assignment: None,
        }
    }
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

#[derive(Debug, PartialEq, Eq)]
pub struct MaybeConflict(bool);
pub const CONFLICT: MaybeConflict = MaybeConflict(true);
pub const NO_CONFLICT: MaybeConflict = MaybeConflict(false);

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

pub fn set_reason_flag(checker: &mut Checker, lit: Literal, value: bool) {
    match checker.literal_reason[lit] {
        Reason::Forced(clause) => checker.clause_is_a_reason[clause] = value,
        Reason::Assumed => (),
    }
}

pub fn assign(checker: &mut Checker, literal: Literal, reason: Reason) -> MaybeConflict {
    checker.assign_count += 1;
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
    if checker.config.no_core_first {
        propagate_no_core_first(checker)
    } else {
        propagate_core_first(checker)
    }
}

fn propagate_no_core_first(checker: &mut Checker) -> MaybeConflict {
    fn watches_align(
        checker: &mut Checker,
        mode: Mode,
        literal: Literal,
        position_in_watchlist: &mut usize,
    ) -> MaybeConflict {
        let clause = watchlist(checker, mode)[literal][*position_in_watchlist];
        requires!(clause < checker.lemma);
        let (w1, w2) = checker.clause_watches(clause);
        if checker.assignment[w1] || checker.assignment[w2] {
            return NO_CONFLICT;
        }
        let head = checker.clause_range(clause).start;
        if literal == w1 {
            checker.db[head] = checker.db[head + 1];
        }
        match first_non_falsified(checker, clause, head + 2) {
            Some(offset) => {
                let new = checker.db[offset];
                checker.db[offset] = literal;
                checker.db[head + 1] = new;
                watch_remove_at(checker, mode, literal, *position_in_watchlist);
                *position_in_watchlist = position_in_watchlist.wrapping_sub(1);
                watch_add(checker, mode, new, clause);
                NO_CONFLICT
            }
            None => {
                checker.db[head + 1] = literal;
                let unit = checker.db[head];
                assign(checker, unit, Reason::Forced(clause))
            }
        }
    }

    fn propagate_literal(checker: &mut Checker, mode: Mode, literal: Literal) -> MaybeConflict {
        requires!(checker.assignment[literal]);
        requires!(checker.literal_reason[literal] != Reason::Forced(Clause::NEVER_READ));
        let mut i = 0;
        while i < watchlist(checker, mode)[-literal].len() {
            watches_align(checker, mode, -literal, &mut i)?;
            i = i.wrapping_add(1);
        }
        NO_CONFLICT
    }

    let mode = checker.mode_non_core();
    while checker.processed < checker.assignment.len() {
        let literal = checker.assignment.trace_at(checker.processed);
        checker.processed += 1;
        propagate_literal(checker, mode, literal)?;
    }
    NO_CONFLICT
}

pub fn first_non_falsified(checker: &Checker, clause: Clause, start: usize) -> Option<usize> {
    (start..checker.clause_range(clause).end).find(|&i| !checker.assignment[-checker.db[i]])
}

// stolen from gratgen
fn propagate_core_first(checker: &mut Checker) -> MaybeConflict {
    let mut processed_core = checker.processed;
    let mut core_mode = true;
    let mut noncore_watchlist_index = 0;
    loop {
        if core_mode {
            if processed_core == checker.assignment.len() {
                core_mode = false;
                continue;
            }
            let literal = -checker.assignment.trace_at(processed_core);
            processed_core += 1;

            let mut i = 0;
            while i < checker.watchlist_core[literal].len() {
                let clause = checker.watchlist_core[literal][i];
                let (mut w1, mut w2) = checker.clause_watches(clause);
                if checker.assignment[w1] || checker.assignment[w2] {
                    i += 1;
                    continue;
                }
                let head = checker.clause_range(clause).start;
                if w1 == literal {
                    checker.db[head] = w2;
                    w1 = w2;
                    w2 = literal;
                }
                invariant!(w2 == literal);
                invariant!(checker.assignment[-w2]);
                invariant!(checker.db[head] == w1);

                match first_non_falsified(checker, clause, head + 2) {
                    Some(wo) => {
                        checker.watchlist_core[literal].swap_remove(i);
                        let w = checker.db[wo];
                        invariant!(w != literal);
                        watch_add(checker, Mode::Core, w, clause);
                        checker.db[head + 1] = w;
                        checker.db[wo] = w2;
                        continue;
                    }
                    None => (),
                }

                checker.db[head + 1] = w2;

                assign(checker, w1, Reason::Forced(clause));
                if !checker.assignment[-w1] {
                    i += 1;
                    continue;
                } else {
                    return CONFLICT;
                }
            }
        } else {
            if checker.processed == checker.assignment.len() {
                return NO_CONFLICT;
            }
            let literal = -checker.assignment.trace_at(checker.processed);
            checker.processed += 1;

            let mut i = noncore_watchlist_index;
            noncore_watchlist_index = 0;

            while i < checker.watchlist_noncore[literal].len() {
                let clause = checker.watchlist_noncore[literal][i];
                let head = checker.clause_range(clause).start;
                let (mut w1, mut w2) = checker.clause_watches(clause);
                invariant!(w1 == literal || w2 == literal);

                if checker.assignment[w1] || checker.assignment[w2] {
                    i += 1;
                    continue;
                }

                if w1 == literal {
                    checker.db[head] = w2;
                    w1 = w2;
                    w2 = literal;
                }

                invariant!(w2 == literal);
                invariant!(checker.assignment[-w2]);
                invariant!(checker.db[head] == w1);

                match first_non_falsified(checker, clause, head + 2) {
                    Some(wo) => {
                        checker.watchlist_noncore[literal].swap_remove(i);
                        let w = checker.db[wo];
                        invariant!(w != literal);
                        watch_add(checker, Mode::NonCore, w, clause);
                        checker.db[head + 1] = w;
                        checker.db[wo] = w2;
                        continue;
                    }
                    None => (),
                }

                checker.db[head + 1] = w2;

                assign(checker, w1, Reason::Forced(clause));
                if !checker.assignment[-w1] {
                    checker.processed -= 1;
                    noncore_watchlist_index = i + 1;
                    core_mode = true;
                    break;
                } else {
                    return CONFLICT;
                }
            }
        }
    }
}

fn move_to_core(checker: &mut Checker, clause: Clause) {
    if checker.clause_scheduled[clause] {
        return;
    }
    if !checker.clause_in_watchlist[clause] {
        return;
    }
    if checker.config.no_core_first {
        return;
    }

    let (w1, w2) = checker.clause_watches(clause);
    // FIXME why do we have duplicates in the watchlists?
    watches_find_and_remove_all(checker, Mode::NonCore, w1, clause);
    watches_find_and_remove_all(checker, Mode::NonCore, w2, clause);

    watch_add(checker, Mode::Core, w1, clause);
    watch_add(checker, Mode::Core, w2, clause);
}

macro_rules! preserve_assignment {
    ($checker:expr, $computation:expr) => {{
        let trace_length = $checker.assignment.len();
        let result = $computation;
        while $checker.assignment.len() > trace_length {
            $checker.assignment.pop();
        }
        $checker.processed = trace_length;
        result
    }};
}

fn collect_resolution_candidates(checker: &Checker, pivot: Literal) -> Stack<Clause> {
    let mut candidates = Stack::new();
    for lit in Literal::all(checker.maxvar) {
        for i in 0..checker.watchlist_core[lit].len() {
            let clause = checker.watchlist_core[lit][i];
            let want = if checker.config.no_core_first {
                checker.clause_scheduled[clause]
            } else {
                invariant!(checker.clause_scheduled[clause]);
                true
            };
            if want
                && checker.clause(clause)[0] == lit
                && checker
                    .clause(clause)
                    .iter()
                    .any(|&literal| literal == -pivot)
            {
                candidates.push(clause);
            }
        }
    }
    candidates.sort_unstable(); // resolution candidates in an LRAT proof have to be sorted
    candidates
}

fn rup(checker: &mut Checker, clause: Clause, pivot: Literal) -> bool {
    assignment_invariants(checker);
    requires!(checker.processed == checker.assignment.len());
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
    checker.rat_introductions += 1;
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
                    let ok = rup(checker, resolution_candidate, pivot);
                    if !ok {
                        checker.rejection.pivot = Some(pivot);
                        checker.rejection.resolved_with = Some(resolution_candidate);
                        checker.rejection.stable_assignment = Some(checker.assignment.clone());
                    }
                    ok
                }
        )
    })
}

fn check_inference(checker: &mut Checker) -> bool {
    let lemma = checker.lemma;
    checker.soft_propagation = true;
    let copy = checker.clause_copy(lemma);
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
    requires!(checker.assignment[conflict_literal]);
    requires!(checker.assignment[-conflict_literal]);
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
            Reason::Assumed => {}
            Reason::Forced(clause) => {
                move_to_core(checker, clause);
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
        StackMapping::with_array_value_size_stack_size(false, num_clauses, num_clauses);
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
    watches_add(checker, checker.mode_non_core(), clause)?;
    propagate(checker)
}

fn close_proof(checker: &mut Checker, steps_until_conflict: usize) -> bool {
    checker.proof_steps_until_conflict = steps_until_conflict;
    let clause = checker.lemma;
    checker.clause_offset[clause + 1] = checker.clause_offset[clause];
    invariant!(checker.clause(clause).empty());
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
    for i in 0..checker.proof.size() {
        watch_invariants(checker);
        match checker.proof[i] {
            ProofStep::Deletion(clause) => {
                if clause == Clause::DOES_NOT_EXIST {
                    continue;
                }
                checker.clause_deletions += 1;
                log!(
                    checker,
                    1,
                    "[preprocess] del {}",
                    checker.clause_copy(clause)
                );
                if checker.config.skip_deletions {
                    // TODO this would break stuff..
                    // let is_unit = checker
                    //     .clause_range(clause)
                    //     .filter(|&i| !checker.assignment[-checker.db[i]])
                    //     .count()
                    //     == 1;
                    // if !is_unit
                    {
                        checker.skipped_deletions += 1;
                        if checker.clause_is_a_reason[clause] {
                            checker.reason_deletions += 1;
                            if checker.config.verbosity > 0 {
                                warn!(
                                    "Ignoring deletion of (pseudo) unit clause {}",
                                    checker.clause_copy(clause)
                                );
                            }
                        } else {
                            watches_remove(checker, checker.clause_mode(clause), clause);
                        }
                    }
                } else {
                    invariant!(!checker.clause_scheduled[clause]);
                    watches_remove(checker, checker.mode_non_core(), clause);
                    if checker.clause_is_a_reason[clause] {
                        checker.reason_deletions += 1;
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
                    checker.rejection.failed_proof_step = i;
                    return false;
                }
                checker.lemma += 1;
                if add_premise(checker, clause) == CONFLICT {
                    extract_dependencies_for_last_literal(checker);
                    return close_proof(checker, i + 1);
                }
            }
        };
    }
    invariant!({
        let last_step = checker.proof[checker.proof_steps_until_conflict];
        match last_step {
            ProofStep::Lemma(clause) => checker.clause(clause).empty(),
            ProofStep::Deletion(_) => false,
        }
    });
    unreachable()
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
                if clause == Clause::DOES_NOT_EXIST {
                    continue;
                }
                log!(checker, 1, "[verify] del {}", checker.clause_copy(clause));
                if checker.config.skip_deletions {
                    if !checker.clause_is_a_reason[clause] {
                        // not actually deleted otherwise!
                        invariant!(checker.clause_mode(clause) == checker.mode_non_core());
                        watches_add(checker, checker.clause_mode(clause), clause);
                    }
                } else {
                    if checker.lemma_revision[clause] {
                        let mut revision = checker.revisions.pop();
                        revision_apply(checker, &mut revision);
                    }
                    watches_add(checker, checker.clause_mode(clause), clause);
                }
                true
            }
            ProofStep::Lemma(_clause) => {
                checker.lemma -= 1;
                let lemma = checker.lemma;
                invariant!(_clause == lemma);
                watches_remove(checker, checker.clause_mode(lemma), lemma);
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
            checker.rejection.failed_proof_step = i;
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
            checker.processed = trace_length;
        });
}

fn write_lrat_certificate(checker: &mut Checker) -> io::Result<()> {
    let mut file = match &checker.config.lrat_filename {
        Some(filename) => File::create(filename)?,
        None => return Ok(()),
    };
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
                        // NOTE this could optimised
                        checker.clause_copy(lemma).dimacs(&mut file)?;
                        write!(file, " ")?;
                        for hint in &checker.lemma_lratlemma[lemma] {
                            match hint {
                                &LRATLiteral::ResolutionCandidate(clause) => {
                                    write!(file, "-{} ", checker.clause_lrat_id[clause])
                                }
                                &LRATLiteral::Unit(clause) => {
                                    invariant!(checker.clause_scheduled[clause]);
                                    invariant!(
                                        checker.clause_lrat_id[clause] != Clause::NEVER_READ
                                    );
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
                        (checker.clause_lrat_id[clause] == Clause::UNINITIALIZED)
                            == (clause >= checker.lemma && !checker.clause_scheduled[clause])
                    );
                    if checker.clause_lrat_id[clause] != Clause::UNINITIALIZED {
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

fn write_sick_witness(checker: &Checker) -> io::Result<()> {
    let mut file = match &checker.config.sick_filename {
        Some(filename) => File::create(filename)?,
        None => return Ok(()),
    };

    let lemma = checker.lemma;
    let step = checker.rejection.failed_proof_step + checker.premise_length + 1;
    let assignment = if let Some(stable) = &checker.rejection.stable_assignment {
        stable
    } else {
        &checker.assignment
    };

    write!(file, "v ")?;
    write!(
        file,
        "{} ",
        checker
            .rejection
            .pivot
            .map_or("0".to_string(), |pivot| format!("{}", pivot))
    )?;
    write!(file, "{}\n", step)?;
    write!(file, "n ")?;
    checker.clause_copy(lemma).dimacs(&mut file)?;
    write!(file, " ")?;
    for literal in Literal::all(checker.maxvar) {
        if assignment[literal] {
            write!(file, "{} ", literal)?;
        }
    }
    write!(file, "0\n")?;
    write!(file, "r ")?;
    if let Some(resolved_with) = checker.rejection.resolved_with {
        for &literal in checker.clause(resolved_with) {
            write!(file, "{} ", literal)?;
        }
        write!(file, "0 ")?;
        for literal in Literal::all(checker.maxvar) {
            if assignment[literal] {
                write!(file, "{} ", literal)?;
            }
        }
    } else {
        write!(file, "0 ")?;
    }
    write!(file, "0\n")?;
    Ok(())
}

fn assignment_invariants(checker: &Checker) {
    if !crate::config::COSTLY_INVARIANT_CHECKING {
        return;
    }
    for &literal in checker.assignment.into_iter() {
        match checker.literal_reason[literal] {
            Reason::Forced(clause) => invariant!(
                clause < checker.lemma,
                "current lemma is {}, but literal {} is assigned because of lemma {} in {}",
                checker.lemma,
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
}

pub fn check(checker: &mut Checker) -> bool {
    let ok = preprocess(checker) && verify(checker);
    if ok {
        write_lrat_certificate(checker).expect("Failed to write LRAT certificate.");
    } else {
        write_sick_witness(checker).expect("Failed to write incorrectness witness.")
    }
    ok
}
