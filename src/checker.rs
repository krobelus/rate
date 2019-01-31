//! Proof checking

use crate::{
    assignment::Assignment,
    clause::{Clause, ClauseCopy, ProofStep},
    config::unreachable,
    config::Config,
    literal::{Literal, Variable},
    memory::{Array, BoundedStack, Offset, Slice, Stack, StackMapping},
    parser::{Parser, CLAUSE_OFFSET, DB},
    watchlist::{
        revision_apply, revision_create, watch_add, watch_invariants, watches_find_and_remove,
        watches_remove, Mode, Watchlist,
    },
};
use ansi_term::Colour;
#[cfg(feature = "profile_it")]
use cpuprofiler::PROFILER;
#[cfg(feature = "flame_it")]
use flamer::flame;
use std::{
    cmp, fmt,
    fs::File,
    io,
    io::{BufWriter, Write},
    ops,
};

#[derive(Debug)]
pub struct Checker {
    pub assignment: Assignment,
    clause_is_a_reason: Array<Clause, bool>,
    clause_lrat_id: Array<Clause, Clause>,
    clause_offset: &'static mut Stack<usize>,
    pub clause_scheduled: Array<Clause, bool>,
    pub clause_deleted_at: Array<Clause, usize>,
    pub clause_in_watchlist: Array<Clause, bool>,
    clause_pivot: Option<Array<Clause, Literal>>,
    pub config: Config,
    pub db: &'static mut Stack<Literal>,
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
    pub literal_is_in_cone: Array<Literal, bool>,
    pub literal_minimal_lifetime: Array<Literal, usize>,
    pub revisions: Stack<Revision>,
    soft_propagation: bool,
    pub watchlist_noncore: Array<Literal, Watchlist>,
    pub watchlist_core: Array<Literal, Watchlist>,
    pub processed: usize,
    rejection: Rejection,

    pub premise_length: usize,
    pub rup_introductions: usize,
    pub rat_introductions: usize,
    pub clause_deletions: usize,
    pub skipped_deletions: usize,
    pub reason_deletions: usize,

    pub assign_count: usize,
    pub satisfied_count: usize,
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
    pub cone: Stack<Literal>,
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
            clause_offset: unsafe { &mut CLAUSE_OFFSET },
            clause_scheduled: Array::new(false, num_clauses),
            clause_deleted_at: Array::from(parser.clause_deleted_at),
            clause_in_watchlist: Array::new(false, num_clauses),
            clause_pivot: parser.clause_pivot.map(Array::from),
            config: config,
            db: unsafe { &mut DB },
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
            literal_is_in_cone: Array::new(false, maxvar.array_size_for_literals()),
            literal_minimal_lifetime: Array::new(0, maxvar.array_size_for_literals()),
            revisions: Stack::with_capacity(maxvar.array_size_for_variables()),
            watchlist_noncore: Array::new(Stack::new(), maxvar.array_size_for_literals()),
            watchlist_core: Array::new(Stack::new(), maxvar.array_size_for_literals()),
            processed: 1, // skip Literal::TOP
            rejection: Rejection::new(),

            premise_length: parser.proof_start.as_offset(),
            rup_introductions: 0,
            rat_introductions: 0,
            clause_deletions: 0,
            skipped_deletions: 0,
            reason_deletions: 0,
            assign_count: 0,
            satisfied_count: 0,
        };
        checker.literal_reason[Literal::TOP] = Reason::Assumed;
        checker.literal_minimal_lifetime[Literal::TOP] = usize::max_value();
        checker.literal_reason[Literal::BOTTOM] = Reason::Assumed;
        checker.literal_minimal_lifetime[Literal::BOTTOM] = usize::max_value();
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
        self.clause_offset[clause.as_offset()]..self.clause_offset[clause.as_offset() + 1]
    }
    pub fn clause_watches(&self, clause: Clause) -> (Literal, Literal) {
        (self.clause(clause)[0], self.clause(clause)[1])
    }
    pub fn clause_mode(&self, clause: Clause) -> Mode {
        if self.config.no_core_first {
            Mode::NonCore
        } else {
            match self.clause_scheduled[clause] {
                true => Mode::Core,
                false => Mode::NonCore,
            }
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

impl Reason {
    fn as_forced_unchecked(self) -> Clause {
        match self {
            Reason::Forced(clause) => clause,
            Reason::Assumed => unreachable(),
        }
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
        let reason_clause = reason.as_forced_unchecked();
        let reason_lifetime = checker.clause_deleted_at[reason_clause];
        let reason_reason_lifetime = checker
            .clause(reason_clause)
            .iter()
            .filter(|&reason_literal| *reason_literal != literal)
            .map(|&reason_literal| checker.literal_minimal_lifetime[-reason_literal])
            .min()
            .unwrap_or(usize::max_value());
        checker.literal_minimal_lifetime[literal] =
            cmp::min(reason_lifetime, reason_reason_lifetime);
    }
    if checker.assignment[-literal] {
        CONFLICT
    } else {
        NO_CONFLICT
    }
}

// stolen from gratgen
fn propagate(checker: &mut Checker) -> MaybeConflict {
    let mut processed_core = checker.processed;
    let mut core_mode = !checker.config.no_core_first;
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
    let d1 = watches_find_and_remove(checker, Mode::NonCore, w1, clause);
    let d2 = watches_find_and_remove(checker, Mode::NonCore, w2, clause);
    invariant!(d1 || d2);

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

fn watchlist_filter_core(checker: &Checker) -> &Array<Literal, Watchlist> {
    if checker.config.no_core_first {
        &checker.watchlist_noncore
    } else {
        &checker.watchlist_core
    }
}

fn collect_resolution_candidates(checker: &Checker, pivot: Literal) -> Stack<Clause> {
    let mut candidates = Stack::new();
    for lit in Literal::all(checker.maxvar) {
        for i in 0..watchlist_filter_core(checker)[lit].len() {
            let clause = watchlist_filter_core(checker)[lit][i];
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

fn rat(checker: &mut Checker, pivot: Literal, resolution_candidates: &Stack<Clause>) -> bool {
    assignment_invariants(checker);
    checker.rat_introductions += 1;
    let lemma = checker.lemma;
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
    let trace_length = checker.assignment.len();
    let pivot_index = copy.iter().position(|&pivot| {
        watch_invariants(checker);
        checker.lemma_lratlemma[lemma].clear();
        pivot != Literal::BOTTOM
            && match &checker.clause_pivot {
                None => true,
                Some(pivots) => pivots[lemma] == pivot,
            }
            && preserve_assignment!(
                checker,
                rup(checker, lemma, pivot) && {
                    checker.rup_introductions += 1;
                    true
                } || {
                    invariant!(checker.assignment[-pivot]);
                    let pivot_falsified =
                        checker.assignment.position_in_trace(-pivot) < trace_length;
                    let resolution_candidates = collect_resolution_candidates(checker, pivot);
                    if pivot_falsified {
                        echo!(
                            "c RAT check on {} failed due to falsified pivot {}",
                            checker.clause_copy(lemma),
                            pivot
                        );
                        checker.rejection.pivot = Some(pivot);
                        invariant!(
                            !resolution_candidates.empty()
                                || (checker.config.skip_deletions
                                    && checker.clause_is_a_reason[lemma])
                        );
                        if !resolution_candidates.empty() {
                            checker.rejection.resolved_with = Some(resolution_candidates[0]);
                        }
                        checker.rejection.stable_assignment = Some(checker.assignment.clone());
                        false
                    } else {
                        rat(checker, pivot, &resolution_candidates)
                    }
                }
            )
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
    // We might be able to eliminate this by using checker.implication_graph instead.
    let mut reason_literals = BoundedStack::with_capacity(checker.implication_graph.len());
    for &literal in &checker.implication_graph {
        let reason_clause = checker.literal_reason[literal].as_forced_unchecked();
        invariant!(reason_clause < lemma);
        reason_literals.push(literal);
    }
    reason_literals.sort_unstable_by_key(|&literal| checker.assignment.position_in_trace(literal));
    log!(checker, 3, "Resolution chain:");
    for &literal in &reason_literals {
        let reason_clause = checker.literal_reason[literal].as_forced_unchecked();
        log!(
            checker,
            3,
            "{}:\t{}",
            literal,
            checker.clause_copy(reason_clause)
        );
        checker.lemma_lratlemma[lemma].push(LRATLiteral::Unit(reason_clause));
    }
    checker.implication_graph.clear();
}

#[derive(Debug, PartialEq, Eq)]
enum Stage {
    Preprocessing,
    Verification,
}

pub fn first_non_falsified(checker: &Checker, clause: Clause, start: usize) -> Option<usize> {
    (start..checker.clause_range(clause).end).find(|&i| !checker.assignment[-checker.db[i]])
}

enum NonFalsified {
    None,
    One(usize),
    Two(usize, usize),
}

fn first_two_non_falsified(checker: &Checker, clause: Clause) -> NonFalsified {
    let head = checker.clause_range(clause).start;
    match first_non_falsified(checker, clause, head) {
        None => NonFalsified::None,
        Some(i1) => match first_non_falsified(checker, clause, i1 + 1) {
            None => NonFalsified::One(i1),
            Some(i2) => NonFalsified::Two(i1, i2),
        },
    }
}

fn watches_add(checker: &mut Checker, stage: Stage, clause: Clause) -> MaybeConflict {
    log!(
        checker,
        2,
        "initializing watches for {}",
        checker.clause_copy(clause)
    );
    let head = checker.clause_range(clause).start;
    let mode = match stage {
        Stage::Preprocessing => Mode::NonCore,
        Stage::Verification => checker.clause_mode(clause),
    };
    match first_two_non_falsified(checker, clause) {
        NonFalsified::None => match stage {
            Stage::Preprocessing => {
                assign(checker, checker.db[head], Reason::Forced(clause));
                CONFLICT
            }
            Stage::Verification => unreachable(),
        },
        NonFalsified::One(i1) => {
            let w1 = checker.db[i1];
            if !checker.assignment[w1] {
                let conflict = assign(checker, w1, Reason::Forced(clause));
                invariant!(conflict == NO_CONFLICT);
            }
            if !checker.config.skip_deletions {
                checker.clause_in_watchlist[clause] = true;
                checker.db.as_mut_slice().swap(head, i1);
                watch_add(checker, mode, w1, clause);
                if stage == Stage::Verification {
                    watch_add(checker, mode, checker.db[head + 1], clause);
                }
            }
            NO_CONFLICT
        }
        NonFalsified::Two(i1, i2) => {
            let w1 = checker.db[i1];
            let w2 = checker.db[i2];
            checker.clause_in_watchlist[clause] = true;
            checker.db.as_mut_slice().swap(head, i1);
            checker.db.as_mut_slice().swap(head + 1, i2);
            watch_add(checker, mode, w1, clause);
            watch_add(checker, mode, w2, clause);
            NO_CONFLICT
        }
    }
}

fn clause_is_satisfied(checker: &Checker, clause: Clause) -> bool {
    checker
        .clause(clause)
        .iter()
        .any(|&literal| checker.assignment[literal])
}

fn clause_is_satisfied_until_its_deletion(checker: &Checker, clause: Clause) -> bool {
    checker.clause(clause).iter().any(|&literal| {
        invariant!(
            implies(
                checker.literal_minimal_lifetime[literal] > 0,
                checker.assignment[literal]
            ) || literal == Literal::BOTTOM
        );
        checker.assignment[literal] // necessary to exclude Literal::BOTTOM
            &&
        checker.literal_minimal_lifetime[literal] >=
            checker.clause_deleted_at[clause]
    })
}

fn add_premise(checker: &mut Checker, clause: Clause) -> MaybeConflict {
    log!(
        checker,
        1,
        "[preprocess] add {}",
        checker.clause_copy(clause)
    );
    let already_satisfied = if checker.config.skip_deletions {
        clause_is_satisfied(checker, clause)
    } else {
        clause_is_satisfied_until_its_deletion(checker, clause)
    };
    if already_satisfied {
        checker.satisfied_count += 1;
    } else {
        watches_add(checker, Stage::Preprocessing, clause)?;
    }
    propagate(checker)
}

fn close_proof(checker: &mut Checker, steps_until_conflict: usize) -> bool {
    checker.proof_steps_until_conflict = steps_until_conflict;
    let clause = checker.lemma;
    checker.clause_offset[clause.as_offset() + 1] = checker.clause_offset[clause.as_offset()];
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
                if checker.clause_is_a_reason[clause] {
                    checker.reason_deletions += 1;
                }
                if checker.config.skip_deletions {
                    let is_unit = checker
                        .clause_range(clause)
                        .filter(|&i| !checker.assignment[-checker.db[i]])
                        .count()
                        == 1;
                    if is_unit {
                        checker.skipped_deletions += 1;
                        if checker.config.verbosity > 0 {
                            warn!(
                                "Ignoring deletion of (pseudo) unit clause {}",
                                checker.clause_copy(clause)
                            );
                        }
                    } else {
                        watches_remove(checker, checker.clause_mode(clause), clause);
                    }
                } else {
                    invariant!(!checker.clause_scheduled[clause]);
                    watches_remove(checker, Mode::NonCore, clause);
                    if checker.clause_is_a_reason[clause] {
                        revision_create(checker, clause);
                    }
                }
            }
            ProofStep::Lemma(clause) => {
                invariant!(clause == checker.lemma);
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
                        invariant!(checker.clause_mode(clause) == Mode::NonCore);
                        watches_add(checker, Stage::Verification, clause);
                    }
                } else {
                    if checker.lemma_revision[clause] {
                        let mut revision = checker.revisions.pop();
                        revision_apply(checker, &mut revision);
                    }
                    watches_add(checker, Stage::Verification, clause);
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

#[cfg_attr(feature = "flame_it", flame)]
fn write_lrat_certificate(checker: &mut Checker) -> io::Result<()> {
    let mut file = match &checker.config.lrat_filename {
        Some(filename) => BufWriter::new(File::create(filename)?),
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
    invariant!(checker.lrat_id == lrat_id(checker, checker.lemma - 1));
    // delete lemmas that were never used
    for clause in Clause::range(0, checker.lemma) {
        if !checker.clause_scheduled[clause] {
            write!(file, "{} ", lrat_id(checker, clause))?;
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
                        write!(file, "{} ", lrat_id(checker, lemma))?;
                        write_clause(checker, &mut file, lemma)?;
                        write!(file, " ")?;
                        for hint in &checker.lemma_lratlemma[lemma] {
                            match hint {
                                &LRATLiteral::ResolutionCandidate(clause) => {
                                    write!(file, "-{} ", lrat_id(checker, clause))
                                }
                                &LRATLiteral::Unit(clause) => {
                                    invariant!(checker.clause_scheduled[clause]);
                                    invariant!(lrat_id(checker, clause) != Clause::NEVER_READ);
                                    write!(file, "{} ", lrat_id(checker, clause))
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
                        (lrat_id(checker, clause) == Clause::UNINITIALIZED)
                            == (clause >= checker.lemma && !checker.clause_scheduled[clause])
                    );
                    if false {
                        if lrat_id(checker, clause) != Clause::UNINITIALIZED {
                            write_deletion(checker, &mut file, &mut clause_deleted, clause)?;
                        }
                    }
                    i += 1;
                }
            },
        }
    }
    if state == State::InDeletionChain {
        close_deletion_chain(&mut file)?;
    }
    Ok(())
}

fn lrat_id(checker: &Checker, clause: Clause) -> Clause {
    checker.clause_lrat_id[clause]
}
fn open_deletion_chain(checker: &Checker, file: &mut impl Write, lemma: Clause) -> io::Result<()> {
    write!(file, "{} d ", checker.clause_lrat_id[lemma])
}
fn close_deletion_chain(file: &mut impl Write) -> io::Result<()> {
    write!(file, "0\n")
}
fn write_deletion(
    checker: &Checker,
    file: &mut impl Write,
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

fn write_clause(checker: &Checker, file: &mut impl Write, clause: Clause) -> io::Result<()> {
    for &literal in checker.clause(clause) {
        if literal != Literal::BOTTOM {
            write!(file, "{} ", literal)?;
        }
    }
    write!(file, "0")
}

fn write_sick_witness(checker: &Checker) -> io::Result<()> {
    let mut file = match &checker.config.sick_filename {
        Some(filename) => BufWriter::new(File::create(filename)?),
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
    write_clause(checker, &mut file, lemma)?;
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

fn implies(a: bool, b: bool) -> bool {
    !a || b
}

pub fn check(checker: &mut Checker) -> bool {
    #[cfg(feature = "profile_it")]
    PROFILER
        .lock()
        .unwrap()
        .start("check.profile")
        .expect("failed to start");
    let ok = preprocess(checker) && verify(checker);
    #[cfg(feature = "profile_it")]
    PROFILER.lock().unwrap().stop().expect("failed to stop");
    if ok {
        write_lrat_certificate(checker).expect("Failed to write LRAT certificate.");
    } else {
        write_sick_witness(checker).expect("Failed to write incorrectness witness.")
    }
    ok
}
