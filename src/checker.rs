//! Proof checking logic.

use crate::{
    assignment::{stable_under_unit_propagation, Assignment},
    clause::{Clause, GRATLiteral, LRATDependency, LRATLiteral, ProofStep, Reason},
    clausedatabase::{ClauseDatabase, WitnessDatabase},
    config::{unreachable, Config, RedundancyProperty},
    literal::{Literal, Variable},
    memory::{
        format_memory_usage, Array, BoundedStack, HeapSpace, Offset, Slice, Stack, StackMapping,
    },
    output::{self, Timer},
    parser::Parser,
};
use ansi_term::Colour;
use bitfield::bitfield;
#[cfg(feature = "flame_it")]
use flamer::flame;
use rate_macros::HeapSpace;
use std::{
    cmp, fmt,
    fs::File,
    io,
    io::{BufWriter, Write},
    ops::{self, Index},
};

pub fn check(checker: &mut Checker) -> bool {
    preprocess(checker) && verify(checker) && {
        write_lemmas(checker).unwrap_or_else(|err| die!("Failed to write lemmas: {}", err));
        write_lrat_certificate(checker)
            .unwrap_or_else(|err| die!("Failed to write LRAT certificate: {}", err));
        write_grat_certificate(checker)
            .unwrap_or_else(|err| die!("Failed to write GRAT certificate: {}", err));
        true
    } || {
        write_sick_witness(checker).expect("Failed to write incorrectness witness.");
        false
    }
}

#[derive(Debug)]
pub struct Checker {
    db: &'static mut ClauseDatabase,
    witness_db: &'static mut WitnessDatabase,
    pub proof: Array<usize, ProofStep>,
    pub config: Config,

    maxvar: Variable,
    assignment: Assignment,
    processed: usize,
    lemma: Clause, // current lemma / first lemma of proof
    proof_steps_until_conflict: usize,
    soft_propagation: bool,
    rejection: Rejection,

    implication_graph: StackMapping<usize, bool>,
    literal_is_in_cone_preprocess: Array<Literal, bool>,
    watchlist_noncore: Array<Literal, Watchlist>,
    watchlist_core: Array<Literal, Watchlist>,

    clause_pivot: Array<Clause, Literal>,
    is_in_witness: Array<Literal, bool>,

    revisions: Stack<Revision>,

    lrat: Stack<LRATLiteral>,
    clause_lrat_offset: Array<Clause, usize>,
    clause_lrat_id: Array<Clause, Clause>,
    dependencies: Stack<LRATDependency>,
    lrat_id: Clause,
    prerat_clauses: StackMapping<Clause, bool>, // Linear lookup should be fine here as well.
    optimized_proof: BoundedStack<ProofStep>,

    grat: Stack<GRATLiteral>,
    grat_conflict_clause: Clause,
    grat_in_deletion: bool,
    grat_rat_counts: Array<Literal, usize>,
    grat_pending: Stack<GRATLiteral>,
    grat_pending_deletions: Stack<Clause>,
    grat_pending_prerat: Stack<GRATLiteral>,
    grat_prerat: Array<Clause, bool>,

    #[cfg(feature = "clause_lifetime_heuristic")]
    clause_deleted_at: Array<Clause, usize>,
    #[cfg(feature = "clause_lifetime_heuristic")]
    literal_minimal_lifetime: Array<Literal, usize>,

    pub premise_length: usize,
    pub rup_introductions: usize,
    pub rat_introductions: usize,
    pub deletions: usize,
    pub skipped_deletions: usize,
    pub reason_deletions: usize,
    pub satisfied_count: usize,
}

bitfield! {
    pub struct ClauseFields(u32);
    impl Debug;
    is_scheduled, set_is_scheduled: 0;
    is_reason, set_is_reason: 1;
    in_watchlist, set_in_watchlist: 2;
    has_revision, set_has_revision: 3;
    deletion_ignored, set_deletion_ignored: 4;
    in_conflict_graph, set_in_conflict_graph: 5;
}

#[derive(Debug)]
struct Rejection {
    lemma: Stack<Literal>,
    failed_proof_step: usize,
    pivot: Option<Literal>,
    resolved_with: Option<Clause>,
    stable_assignment: Option<Assignment>,
    natural_model_length: Option<usize>,
}

// Can't derive HeapSpace for Option<T> yet.
impl HeapSpace for Rejection {
    fn heap_space(&self) -> usize {
        self.lemma.heap_space()
            + match &self.stable_assignment {
                None => 0,
                Some(assignment) => assignment.heap_space(),
            }
    }
}

#[derive(Debug, HeapSpace, Default, Clone)]
struct Revision {
    cone: Stack<Literal>,
    position_in_trail: Stack<usize>,
    reason_clause: Stack<Clause>,
    trail_length_after_removing_cone: usize,
}

impl Checker {
    pub fn new(parser: Parser, config: Config) -> Checker {
        let num_clauses = parser.clause_db.number_of_clauses() as usize;
        let num_lemmas = parser.proof.len();
        let maxvar = parser.maxvar;
        let assignment = Assignment::new(maxvar);
        let mut checker = Checker {
            processed: assignment.len(),
            assignment,
            clause_lrat_id: Array::new(Clause::UNINITIALIZED, num_clauses),
            #[cfg(feature = "clause_lifetime_heuristic")]
            clause_deleted_at: Array::from(parser.clause_deleted_at),
            clause_pivot: Array::from(parser.clause_pivot),
            dependencies: Stack::new(),
            config,
            db: parser.clause_db,
            witness_db: parser.witness_db,
            soft_propagation: false,
            implication_graph: StackMapping::with_array_value_size_stack_size(
                false,
                maxvar.array_size_for_literals(),
                maxvar.as_offset() + 1, // need + 1 to hold a conflicting literal
            ),
            is_in_witness: Array::new(false, maxvar.array_size_for_literals()),
            lrat_id: Clause::new(0),
            clause_lrat_offset: Array::new(usize::max_value(), num_clauses),
            lrat: Stack::new(),
            prerat_clauses: StackMapping::with_array_value_size_stack_size(
                false,
                num_clauses,
                cmp::min(num_clauses, maxvar.array_size_for_literals()),
            ),
            optimized_proof: BoundedStack::with_capacity(2 * num_lemmas + num_clauses),
            grat: Stack::new(),
            grat_conflict_clause: Clause::UNINITIALIZED,
            grat_in_deletion: false,
            grat_rat_counts: Array::new(0, maxvar.array_size_for_literals()),
            grat_pending: Stack::new(),
            grat_pending_prerat: Stack::new(),
            grat_pending_deletions: Stack::new(),
            grat_prerat: Array::new(false, num_clauses),
            maxvar,
            proof: Array::from(parser.proof),
            lemma: parser.proof_start,
            proof_steps_until_conflict: usize::max_value(),
            literal_is_in_cone_preprocess: Array::new(false, maxvar.array_size_for_literals()),
            #[cfg(feature = "clause_lifetime_heuristic")]
            literal_minimal_lifetime: Array::new(0, maxvar.array_size_for_literals()),
            revisions: Stack::new(),
            watchlist_noncore: Array::new(Stack::new(), maxvar.array_size_for_literals()),
            watchlist_core: Array::new(Stack::new(), maxvar.array_size_for_literals()),
            rejection: Rejection::new(),

            premise_length: parser.proof_start.as_offset(),
            rup_introductions: 0,
            rat_introductions: 0,
            deletions: 0,
            skipped_deletions: 0,
            reason_deletions: 0,
            satisfied_count: 0,
        };
        #[cfg(feature = "clause_lifetime_heuristic")]
        {
            checker.literal_minimal_lifetime[Literal::TOP] = usize::max_value();
            checker.literal_minimal_lifetime[Literal::BOTTOM] = usize::max_value();
        }
        for clause in Clause::range(0, checker.lemma) {
            checker.lrat_id += 1;
            checker.clause_lrat_id[clause] = checker.lrat_id;
        }
        checker
    }
    fn clause_to_string(&self, clause: Clause) -> String {
        self.db.clause_to_string(clause)
    }
    #[allow(dead_code)]
    fn witness_to_string(&self, clause: Clause) -> String {
        self.witness_db.witness_to_string(clause)
    }
    fn clause(&self, clause: Clause) -> Slice<Literal> {
        self.db.clause(clause)
    }
    #[allow(dead_code)]
    fn witness(&self, clause: Clause) -> Slice<Literal> {
        self.witness_db.witness(clause)
    }
    fn clause_range(&self, clause: Clause) -> ops::Range<usize> {
        self.db.clause_range(clause)
    }
    fn witness_range(&self, clause: Clause) -> ops::Range<usize> {
        self.witness_db.witness_range(clause)
    }
    fn watches(&self, head: usize) -> [Literal; 2] {
        self.db.watches(head)
    }
    fn offset2clause(&self, head: usize) -> Clause {
        self.db.offset2clause(head)
    }
    fn clause2offset(&self, clause: Clause) -> usize {
        self.db.clause2offset(clause)
    }
    fn clause_mode(&self, clause: Clause) -> Mode {
        if self.fields(clause).is_scheduled() {
            Mode::Core
        } else {
            Mode::NonCore
        }
    }
    fn fields(&self, clause: Clause) -> &ClauseFields {
        unsafe { &*(self.db.fields(clause) as *const u32 as *const ClauseFields) }
    }
    fn fields_mut(&mut self, clause: Clause) -> &mut ClauseFields {
        unsafe { &mut *(self.db.fields_mut(clause) as *mut u32 as *mut ClauseFields) }
    }
    fn fields_from_offset(&self, offset: usize) -> &ClauseFields {
        unsafe { &*(self.db.fields_from_offset(offset) as *const u32 as *const ClauseFields) }
    }
    fn fields_mut_from_offset(&mut self, offset: usize) -> &mut ClauseFields {
        unsafe { &mut *(self.db.fields_mut_from_offset(offset) as *mut u32 as *mut ClauseFields) }
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
    fn closing_empty_clause(&self) -> Clause {
        requires!(self.proof_steps_until_conflict != usize::max_value());
        let proof_step = self.proof[self.proof_steps_until_conflict];
        proof_step.clause()
    }
}

impl Rejection {
    fn new() -> Rejection {
        Rejection {
            lemma: Stack::new(),
            failed_proof_step: usize::max_value(),
            pivot: None,
            resolved_with: None,
            stable_assignment: None,
            natural_model_length: None,
        }
    }
}

impl fmt::Display for Revision {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "Revision:")?;
        for (i, literal) in self.cone.iter().enumerate() {
            writeln!(
                f,
                "\t#{}: {} [{}]",
                self.position_in_trail[i], literal, self.reason_clause[i]
            )?;
        }
        write!(f, "")
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
    if checker.soft_propagation && !checker.fields(clause).is_scheduled() {
        if checker.config.lrat_filename.is_some() {
            checker.optimized_proof.push(ProofStep::deletion(clause));
        }
        if checker.config.grat_filename.is_some() {
            checker.grat_pending_deletions.push(clause);
        }
    }
    checker.fields_mut(clause).set_is_scheduled(true);
}

fn set_reason_flag(checker: &mut Checker, reason: Reason, value: bool) {
    if !reason.is_assumed() {
        let clause = checker.offset2clause(reason.offset());
        checker.fields_mut(clause).set_is_reason(value);
    }
}

fn assign(checker: &mut Checker, literal: Literal, reason: Reason) -> MaybeConflict {
    requires!(!checker.assignment[literal]);
    checker.assignment.push(literal, reason);
    if !checker.soft_propagation {
        // This is equivalent to `set_reason_flag(checker, reason, true);` but avoids one indirection.
        invariant!(!reason.is_assumed());
        checker
            .fields_mut_from_offset(reason.offset())
            .set_is_reason(true);
        #[cfg(feature = "clause_lifetime_heuristic")]
        {
            let reason_clause = reason.offset();
            let reason_lifetime = checker.clause_deleted_at[checker.offset2clause(reason_clause)];
            let reason_reason_lifetime = checker
                .clause(checker.offset2clause(reason_clause))
                .iter()
                .filter(|&reason_literal| *reason_literal != literal)
                .map(|&reason_literal| checker.literal_minimal_lifetime[-reason_literal])
                .min()
                .unwrap_or(usize::max_value());
            checker.literal_minimal_lifetime[literal] =
                cmp::min(reason_lifetime, reason_reason_lifetime);
        }
    }
    if checker.assignment[-literal] {
        CONFLICT
    } else {
        NO_CONFLICT
    }
}

// stolen from gratgen
#[allow(clippy::cyclomatic_complexity)]
fn propagate(checker: &mut Checker) -> MaybeConflict {
    let mut processed_core = checker.processed;
    let mut core_mode = true;
    let mut noncore_watchlist_index = 0;
    loop {
        if core_mode {
            if processed_core == checker.assignment.len() {
                core_mode = false;
                continue;
            }
            let literal = -checker.assignment.trail_at(processed_core).0;
            processed_core += 1;

            let mut i = 0;
            while i < checker.watchlist_core[literal].len() {
                let head = checker.watchlist_core[literal][i];
                let [mut w1, mut w2] = checker.watches(head);
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

                if let Some(wo) = first_non_falsified_raw(checker, head + 2) {
                    checker.watchlist_core[literal].swap_remove(i);
                    let w = checker.db[wo];
                    invariant!(w != literal);
                    watch_add(checker, Mode::Core, w, head);
                    checker.db[head + 1] = w;
                    checker.db[wo] = w2;
                    continue;
                }

                checker.db[head + 1] = w2;

                assign(checker, w1, Reason::forced(head));
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
            let literal = -checker.assignment.trail_at(checker.processed).0;
            checker.processed += 1;

            let mut i = noncore_watchlist_index;
            noncore_watchlist_index = 0;

            while i < checker.watchlist_noncore[literal].len() {
                let head = checker.watchlist_noncore[literal][i];
                let [mut w1, mut w2] = checker.watches(head);
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

                if let Some(wo) = first_non_falsified_raw(checker, head + 2) {
                    checker.watchlist_noncore[literal].swap_remove(i);
                    let w = checker.db[wo];
                    invariant!(w != literal);
                    watch_add(checker, Mode::NonCore, w, head);
                    checker.db[head + 1] = w;
                    checker.db[wo] = w2;
                    continue;
                }

                checker.db[head + 1] = w2;

                assign(checker, w1, Reason::forced(head));
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

fn move_to_core(checker: &mut Checker, offset: usize) {
    if checker.fields_from_offset(offset).is_scheduled() {
        return;
    }
    if !checker.fields_from_offset(offset).in_watchlist() {
        return;
    }

    let [w1, w2] = checker.watches(offset);
    let d1 = watches_find_and_remove(checker, Mode::NonCore, w1, offset);
    let d2 = watches_find_and_remove(checker, Mode::NonCore, w2, offset);
    invariant!(d1 || d2);

    watch_add(checker, Mode::Core, w1, offset);
    watch_add(checker, Mode::Core, w2, offset);
}

macro_rules! preserve_assignment {
    ($checker:expr, $computation:expr) => {{
        let trail_length = $checker.assignment.len();
        let result = $computation;
        while $checker.assignment.len() > trail_length {
            $checker.assignment.pop();
        }
        $checker.processed = trail_length;
        result
    }};
}

fn watchlist_filter_core(checker: &Checker) -> &Array<Literal, Watchlist> {
    &checker.watchlist_core
}

fn collect_resolution_candidates(checker: &Checker, pivot: Literal) -> Stack<Clause> {
    let mut candidates = Stack::new();
    for lit in Literal::all(checker.maxvar) {
        for i in 0..watchlist_filter_core(checker)[lit].len() {
            let head = watchlist_filter_core(checker)[lit][i];
            let clause = checker.offset2clause(head);
            invariant!(checker.fields(clause).is_scheduled());
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
    candidates.sort_unstable(); // resolution candidates in an LRAT proof have to be sorted
    candidates
}

fn check_inference(checker: &mut Checker) -> bool {
    checker.soft_propagation = true;
    let ok = match checker.config.redundancy_property {
        RedundancyProperty::RAT => preserve_assignment!(checker, rup_or_rat(checker)),
        RedundancyProperty::PR => pr(checker),
    };
    if checker.config.grat_filename.is_some() {
        if !checker.grat_pending_deletions.empty() {
            checker.grat.push(GRATLiteral::DELETION);
            for &clause in &checker.grat_pending_deletions {
                checker.grat.push(GRATLiteral::from_clause(clause));
            }
            checker.grat.push(GRATLiteral::ZERO);
            checker.grat_pending_deletions.clear();
        }
        for &literal in &checker.grat_pending_prerat {
            checker.grat.push(literal);
        }
        checker.grat_pending_prerat.clear();
        for &literal in &checker.grat_pending {
            checker.grat.push(literal);
        }
        checker.grat_pending.clear();
    }
    checker.soft_propagation = false;
    ok
}

enum Reduct {
    Top,
    Clause(Stack<Literal>),
}

fn reduct(
    checker: &Checker,
    assignment: &impl Index<Literal, Output = bool>,
    clause: Clause,
) -> Reduct {
    if checker
        .clause(clause)
        .iter()
        .any(|&literal| assignment[literal])
    {
        Reduct::Top
    } else {
        Reduct::Clause(
            checker
                .clause(clause)
                .iter()
                .filter(|&literal| !assignment[-*literal])
                .cloned()
                .collect(),
        )
    }
}

fn pr(checker: &mut Checker) -> bool {
    requires!(!checker.config.grat_filename.is_some(), "TODO");
    let lemma = checker.lemma;
    let mut tmp = Stack::from_vec(checker.clause(lemma).iter().cloned().collect());
    let lemma_length = tmp.len();
    for clause in Clause::range(0, lemma) {
        for offset in checker.witness_range(lemma) {
            let literal = checker.witness_db[offset];
            invariant!(!checker.is_in_witness[literal]);
            checker.is_in_witness[literal] = true;
        }
        // C u D|w is a rup
        match reduct(checker, &checker.is_in_witness, clause) {
            Reduct::Top => (),
            Reduct::Clause(reduct_by_witness) => {
                for &literal in &reduct_by_witness {
                    tmp.push(literal);
                }
                let ok =
                    preserve_assignment!(checker, slice_rup(checker, tmp.as_slice())) == CONFLICT;
                tmp.truncate(lemma_length);
                if !ok {
                    return false;
                }
            }
        }
        for offset in checker.witness_range(lemma) {
            let literal = checker.witness_db[offset];
            invariant!(checker.is_in_witness[literal]);
            checker.is_in_witness[literal] = false;
        }
    }
    true
}

fn add_rup_conflict_for_grat(checker: &mut Checker) {
    let (conflict_literal, conflict_literal_reason) = checker.assignment.peek();
    let reason = if conflict_literal_reason.is_assumed() {
                checker
                    .assignment
                    .trail_at(
                        checker
                            .assignment
                            .position_in_trail(-conflict_literal),
                    )
                    .1
            } else {
                conflict_literal_reason
            };
    let reason_clause = checker.offset2clause(reason.offset());
    checker.grat_pending.push(GRATLiteral::from_clause(reason_clause));
}

fn rup_or_rat(checker: &mut Checker) -> bool {
    checker.dependencies.clear();
    assignment_invariants(checker);
    requires!(checker.processed == checker.assignment.len());
    let trail_length_forced = checker.assignment.len();
    let lemma = checker.lemma;
    if rup(checker, lemma, None) == CONFLICT {
        checker.rup_introductions += 1;
        if checker.config.grat_filename.is_some() {
            checker.grat_pending.push(GRATLiteral::RUP_LEMMA);
            checker.grat_pending.push(GRATLiteral::from_clause(lemma));
        }
        extract_dependencies(checker, trail_length_forced, None);
        if checker.config.grat_filename.is_some()
        {
            add_rup_conflict_for_grat(checker);
        }
        write_dependencies_for_lrat(checker, lemma, false);
        return true;
    }
    let trail_length_after_rup = checker.assignment.len();
    if checker.config.grat_filename.is_some() {
        checker.grat_pending_prerat.push(GRATLiteral::RAT_LEMMA);
        checker
            .grat_pending_prerat
            .push(GRATLiteral::from_clause(lemma));
    }
    match rat_pivot_index(checker, trail_length_forced) {
        Some(pivot_index) => {
            // Make pivot the first literal in the LRAT proof.
            let head = checker.clause_range(lemma).start;
            let pivot = checker.db[head + pivot_index];
            checker.grat_rat_counts[pivot] += 1;
            checker.db.swap(head, head + pivot_index);
            if checker.config.grat_filename.is_some() {
                for position in trail_length_forced..trail_length_after_rup {
                    let reason = checker.assignment.trail_at(position).1;
                    if !reason.is_assumed() {
                        let reason_clause = checker.offset2clause(reason.offset());
                        if checker.grat_prerat[reason_clause] {
                            checker
                                .grat_pending_prerat
                                .push(GRATLiteral::from_clause(reason_clause));
                            checker.grat_prerat[reason_clause] = false;
                        }
                    }
                }
                checker.grat_pending_prerat.push(GRATLiteral::ZERO);
                checker.grat_pending.push(GRATLiteral::ZERO);
            }
            true
        }
        None => {
            checker.rejection.natural_model_length = Some(trail_length_after_rup);
            comment!("RAT check failed for {}", checker.clause_to_string(lemma));
            false
        }
    }
}

// NOTE: lratcheck/sickcheck might require us to first assign all units before
// returning.
fn rup(checker: &mut Checker, clause: Clause, pivot: Option<Literal>) -> MaybeConflict {
    for offset in checker.clause_range(clause) {
        let unit = checker.db[offset];
        if pivot.map_or(false, |pivot| unit == -pivot) {
            continue;
        }
        if !checker.assignment[-unit] {
            invariant!(unit != Literal::BOTTOM);
            assign(checker, -unit, Reason::assumed())?;
        }
    }
    propagate(checker)
}

fn slice_rup(checker: &mut Checker, clause: Slice<Literal>) -> MaybeConflict {
    for &unit in clause {
        if !checker.assignment[-unit] {
            assign(checker, -unit, Reason::assumed())?;
        }
    }
    propagate(checker)
}

fn rat_pivot_index(checker: &mut Checker, trail_length_forced: usize) -> Option<usize> {
    let lemma = checker.lemma;
    let pivot = checker.clause_pivot[lemma];

    let pivot_falsified = checker.assignment.position_in_trail(-pivot) < trail_length_forced;
    if pivot_falsified {
        comment!(
            "RAT check on {} failed due to falsified pivot {}",
            checker.clause_to_string(lemma),
            pivot
        );
        checker.rejection.pivot = Some(pivot);
        let resolution_candidates = collect_resolution_candidates(checker, pivot);
        invariant!(
            !resolution_candidates.empty()
                || (checker.config.skip_unit_deletions && checker.fields(lemma).is_reason())
        );
        if !resolution_candidates.empty() {
            checker.rejection.resolved_with = Some(resolution_candidates[0]);
        }
        checker.rejection.stable_assignment = Some(checker.assignment.clone());
        return None;
    }

    let pivot_index = checker
        .clause(lemma)
        .iter()
        .position(|&literal| literal == pivot)
        .unwrap();

    let grat_pending_length = checker.grat_pending.len();
    let grat_pending_deletions_length = checker.grat_pending_deletions.len();
    if rat_on_pivot(checker, pivot, trail_length_forced) {
        return Some(pivot_index);
    }
    if checker.config.pivot_is_first_literal {
        return None;
    }
    checker.clause_range(lemma).position(|offset| {
        let pivot = checker.db[offset];
        if checker.config.grat_filename.is_some() {
            checker.grat_pending.truncate(grat_pending_length);
            checker
                .grat_pending_deletions
                .truncate(grat_pending_deletions_length);
        }
        pivot != Literal::BOTTOM && rat_on_pivot(checker, pivot, trail_length_forced)
    })
}

fn rat_on_pivot(checker: &mut Checker, pivot: Literal, trail_length_before_rat: usize) -> bool {
    let lemma = checker.lemma;
    log!(
        checker,
        2,
        "RAT check on {} with pivot {}, {}",
        checker.clause_to_string(lemma),
        pivot,
        checker.assignment
    );
    invariant!(checker.assignment[-pivot]);
    let resolution_candidates = collect_resolution_candidates(checker, pivot);
    rat(
        checker,
        pivot,
        resolution_candidates,
        trail_length_before_rat,
    ) && {
        checker.rat_introductions += 1;
        write_dependencies_for_lrat(checker, lemma, true);
        true
    }
}

fn rat(
    checker: &mut Checker,
    pivot: Literal,
    resolution_candidates: Stack<Clause>,
    trail_length_before_rat: usize,
) -> bool {
    assignment_invariants(checker);
    checker.dependencies.clear();
    let trail_length_before_rup = checker.assignment.len();
    resolution_candidates.iter().all(|&resolution_candidate| {
        preserve_assignment!(
            checker,
            (!checker.config.unmarked_rat_candidates
                && !checker.fields(resolution_candidate).is_scheduled())
                || {
                    watch_invariants(checker);
                    // During the RUP check, -pivot was an assumption. ACL2
                    // lrat-check does use these semantics, while lratcheck
                    // expects that -pivot was the result of propagating the
                    // resolution candidate.
                    if checker.config.lratcheck_compat {
                        let position = checker.assignment.position_in_trail(-pivot);
                        checker.assignment.set_trail_at(
                            position,
                            -pivot,
                            Reason::forced(checker.clause2offset(resolution_candidate)),
                        );
                    }
                    log!(
                        checker,
                        2,
                        "Resolving with {}",
                        checker.clause_to_string(resolution_candidate)
                    );
                    if rup(checker, resolution_candidate, Some(pivot)) == NO_CONFLICT {
                        checker.rejection.pivot = Some(pivot);
                        checker.rejection.resolved_with = Some(resolution_candidate);
                        checker.rejection.stable_assignment = Some(checker.assignment.clone());
                        false
                    } else {
                        if checker.config.lrat_filename.is_some() {
                            checker
                                .dependencies
                                .push(LRATDependency::resolution_candidate(resolution_candidate));
                        }
                        let (conflict_literal, conflict_literal_reason) = checker.assignment.peek();
                        let resolvent_is_tautological = conflict_literal_reason.is_assumed()
                            && checker
                                .assignment
                                .trail_at(checker.assignment.position_in_trail(-conflict_literal))
                                .1
                                .is_assumed();
                        if checker.config.grat_filename.is_some() {
                            if !resolvent_is_tautological {
                                checker
                                    .grat_pending
                                    .push(GRATLiteral::from_clause(resolution_candidate));
                            }
                        }
                        extract_dependencies(
                            checker,
                            trail_length_before_rup,
                            Some((trail_length_before_rat, resolvent_is_tautological)),
                        );
                        if !resolvent_is_tautological {
                            add_rup_conflict_for_grat(checker);
                        }
                        true
                    }
                }
        )
    })
}

fn add_to_conflict_graph(checker: &mut Checker, reason: Reason) {
    checker
        .fields_mut_from_offset(reason.offset())
        .set_in_conflict_graph(true);
}
fn remove_from_conflict_graph(checker: &mut Checker, reason: Reason) {
    checker
        .fields_mut_from_offset(reason.offset())
        .set_in_conflict_graph(false);
}
fn is_in_conflict_graph(checker: &Checker, reason: Reason) -> bool {
    checker
        .fields_from_offset(reason.offset())
        .in_conflict_graph()
}
fn add_cause_of_conflict(checker: &mut Checker, literal: Literal) {
    let position = checker.assignment.position_in_trail(literal);
    let reason = checker.assignment.trail_at(position).1;
    if !reason.is_assumed() {
        add_to_conflict_graph(checker, reason);
    }
}

fn extract_dependencies(
    checker: &mut Checker,
    trail_length_before_rup: usize,
    trail_length_before_rat: Option<(usize, bool)>,
) {
    let conflict_literal = checker.assignment.peek().0;
    requires!(
        conflict_literal == Literal::TOP
            || (checker.assignment[conflict_literal] && checker.assignment[-conflict_literal])
    );
    if conflict_literal != Literal::TOP {
        add_cause_of_conflict(checker, conflict_literal);
        add_cause_of_conflict(checker, -conflict_literal);
    }
    for position in (0..checker.assignment.len()).rev() {
        let (pivot, reason) = checker.assignment.trail_at(position);
        if reason.is_assumed() || !is_in_conflict_graph(checker, reason) {
            continue;
        }
        let clause = checker.offset2clause(reason.offset());
        move_to_core(checker, reason.offset());
        schedule(checker, clause);
        for lit_offset in checker.clause_range(clause) {
            let lit = checker.db[lit_offset];
            if lit == pivot {
                continue;
            }
            let negation_position = checker.assignment.position_in_trail(-lit);
            let negation_reason = checker.assignment.trail_at(negation_position).1;
            if !negation_reason.is_assumed() && !is_in_conflict_graph(checker, negation_reason) {
                add_to_conflict_graph(checker, negation_reason);
            }
        }
    }
    if checker.config.grat_filename.is_some() {
        let resolvent_is_tautological = trail_length_before_rat.map_or(false, |tuple| tuple.1);
        if !resolvent_is_tautological {
            match trail_length_before_rat {
                Some((trail_length, _resolvent_is_tautological)) => {
                    for position in trail_length..trail_length_before_rup {
                        let (_literal, reason) = checker.assignment.trail_at(position);
                        if reason.is_assumed() || !is_in_conflict_graph(checker, reason) {
                            continue;
                        }
                        let clause = checker.offset2clause(reason.offset());
                        checker.grat_prerat[clause] = true;
                    }
                }
                None => (),
            }
            for position in trail_length_before_rup..checker.assignment.len() - 1 {
                let (_literal, reason) = checker.assignment.trail_at(position);
                if reason.is_assumed() || !is_in_conflict_graph(checker, reason) {
                    continue;
                }
                let clause = checker.offset2clause(reason.offset());
                checker.grat_pending.push(GRATLiteral::from_clause(clause));
            }
            checker.grat_pending.push(GRATLiteral::ZERO);
        }
    }
    // TODO only above forced
    log!(checker, 3, "Resolution chain:");
    for position in 1..checker.assignment.len() {
        let (literal, reason) = checker.assignment.trail_at(position);
        if reason.is_assumed() || !is_in_conflict_graph(checker, reason) {
            continue;
        }
        log!(
            checker,
            3,
            "{}:\t{}",
            literal,
            checker.clause_to_string(checker.offset2clause(reason.offset()))
        );
        let clause = checker.offset2clause(reason.offset());
        let position_in_trail = checker.assignment.position_in_trail(literal);
        if checker.config.lrat_filename.is_some() {
            checker
                .dependencies
                .push(if trail_length_before_rat.is_some() {
                    if position_in_trail < trail_length_before_rup {
                        LRATDependency::forced_unit(clause)
                    } else {
                        LRATDependency::unit(clause)
                    }
                } else {
                    LRATDependency::unit(clause)
                });
        }
        remove_from_conflict_graph(checker, reason);
    }
}

fn write_dependencies_for_lrat(checker: &mut Checker, clause: Clause, is_rat: bool) {
    if checker.config.lrat_filename.is_none() {
        return;
    }
    write_dependencies_for_lrat_aux(checker, clause, is_rat);
    checker.lrat.push(LRATLiteral::zero());
}

fn write_dependencies_for_lrat_aux(checker: &mut Checker, clause: Clause, rat_check: bool) {
    checker.clause_lrat_offset[clause] = checker.lrat.len();

    if !rat_check {
        for dependency in &checker.dependencies {
            checker
                .lrat
                .push(if dependency.is_unit() || dependency.is_forced_unit() {
                    LRATLiteral::hint(dependency.clause())
                } else {
                    unreachable()
                })
        }
        return;
    }

    for i in 0..checker.dependencies.len() {
        if checker.dependencies[i].is_unit() {
            continue;
        }
        for j in (0..=i).rev() {
            let dependency = checker.dependencies[j];
            let clause = if dependency.is_unit() {
                continue;
            } else if dependency.is_forced_unit() {
                dependency.clause()
            } else {
                invariant!(dependency.is_resolution_candidate());
                break;
            };
            if !checker.prerat_clauses[clause] {
                checker.prerat_clauses.push(clause, true);
                checker.lrat.push(LRATLiteral::hint(clause));
            }
        }
    }
    checker.prerat_clauses.clear();
    for dependency in &checker.dependencies {
        checker.lrat.push(if dependency.is_unit() {
            LRATLiteral::hint(dependency.clause())
        } else if dependency.is_forced_unit() {
            continue;
        } else {
            invariant!(dependency.is_resolution_candidate());
            LRATLiteral::resolution_candidate(dependency.clause())
        });
    }
    checker.lrat.push(LRATLiteral::zero());
}

#[derive(Debug, PartialEq, Eq)]
enum Stage {
    Preprocessing,
    Verification,
}

fn first_non_falsified(checker: &Checker, clause: Clause, start: usize) -> Option<usize> {
    (start..checker.clause_range(clause).end).find(|&i| !checker.assignment[-checker.db[i]])
}

fn first_non_falsified_raw(checker: &Checker, mut start: usize) -> Option<usize> {
    while !checker.db[start].is_zero() {
        if !checker.assignment[-checker.db[start]] {
            return Some(start);
        }
        start += 1;
    }
    None
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
        checker.clause_to_string(clause)
    );
    let head = checker.clause_range(clause).start;
    let mode = match stage {
        Stage::Preprocessing => Mode::NonCore,
        Stage::Verification => checker.clause_mode(clause),
    };
    match first_two_non_falsified(checker, clause) {
        NonFalsified::None => match stage {
            Stage::Preprocessing => {
                assign(checker, checker.db[head], Reason::forced(head));
                CONFLICT
            }
            Stage::Verification => unreachable(),
        },
        NonFalsified::One(i1) => {
            let w1 = checker.db[i1];
            if !checker.assignment[w1] {
                let conflict = assign(checker, w1, Reason::forced(head));
                invariant!(conflict == NO_CONFLICT);
            }
            if !checker.config.skip_unit_deletions {
                checker.fields_mut(clause).set_in_watchlist(true);
                checker.db.swap(head, i1);
                watch_add(checker, mode, w1, head);
                if stage == Stage::Verification {
                    watch_add(checker, mode, checker.db[head + 1], head);
                }
            }
            NO_CONFLICT
        }
        NonFalsified::Two(i1, i2) => {
            let w1 = checker.db[i1];
            let w2 = checker.db[i2];
            checker.fields_mut(clause).set_in_watchlist(true);
            checker.db.swap(head, i1);
            checker.db.swap(head + 1, i2);
            watch_add(checker, mode, w1, head);
            watch_add(checker, mode, w2, head);
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

#[cfg(feature = "clause_lifetime_heuristic")]
fn clause_is_satisfied_until_its_deletion(checker: &Checker, clause: Clause) -> bool {
    fn implies(a: bool, b: bool) -> bool {
        !a || b
    }

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
        checker.clause_to_string(clause)
    );
    let already_satisfied = if checker.config.skip_unit_deletions {
        clause_is_satisfied(checker, clause)
    } else {
        #[cfg(feature = "clause_lifetime_heuristic")]
        let it = clause_is_satisfied_until_its_deletion(checker, clause);
        #[cfg(not(feature = "clause_lifetime_heuristic"))]
        let it = false;
        it
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
    let empty_clause = checker.lemma;
    checker.db.make_clause_empty(empty_clause);
    invariant!(checker.clause(empty_clause).empty());
    invariant!((checker.maxvar == Variable(0)) == (checker.assignment.peek().0 == Literal::TOP));
    // TODO
    // if checker.config.grat_filename.is_some() {
    //     checker.grat_pending.push(GRATLiteral::RUP_LEMMA);
    //     checker.grat_pending.push(GRATLiteral::from_clause(checker.lemma));
    // }
    let grat_pending_length = checker.grat_pending.len();
    extract_dependencies(checker, checker.assignment.len(), None);
    // TODO
    checker.grat_pending.truncate(grat_pending_length);
    // if checker.config.grat_filename.is_some() {
    //     checker.grat_pending.push(GRATLiteral::ZERO);
    // }
    write_dependencies_for_lrat(checker, empty_clause, false);
    schedule(checker, empty_clause);
    checker.proof[checker.proof_steps_until_conflict] = ProofStep::lemma(empty_clause);
    if checker.config.lrat_filename.is_some() {
        checker.optimized_proof.push(ProofStep::lemma(empty_clause));
    }
    if checker.config.grat_filename.is_some() {
        let reason = checker.assignment.pop().1;
        // let reason = checker.assignment.peek().1;
        if reason.is_assumed() {
            let empty_clause_in_premise = Clause::range(0, checker.lemma)
                .find(|&clause| checker.clause(clause).empty())
                .unwrap();
            schedule(checker, empty_clause_in_premise);
            checker.grat_conflict_clause = empty_clause_in_premise;
        } else {
            checker.grat_conflict_clause = checker.offset2clause(reason.offset());
        }
    }
    true
}

#[cfg_attr(feature = "flame_it", flame)]
fn preprocess(checker: &mut Checker) -> bool {
    let _timer = Timer::name("preprocessing proof");
    log!(checker, 1, "[preprocess]");
    defer_log!(checker, 1, "[preprocess] done\n");
    for clause in Clause::range(0, checker.lemma) {
        if checker.clause(clause).empty() || add_premise(checker, clause) == CONFLICT {
            return close_proof(checker, 0);
        }
    }
    for i in 0..checker.proof.size() {
        watch_invariants(checker);
        let proof_step = checker.proof[i];
        let clause = proof_step.clause();
        if proof_step.is_deletion() {
            if clause == Clause::DOES_NOT_EXIST {
                continue;
            }
            checker.deletions += 1;
            log!(
                checker,
                1,
                "[preprocess] del {}",
                checker.clause_to_string(clause)
            );
            if checker.fields(clause).is_reason() {
                checker.reason_deletions += 1;
            }
            if checker.config.skip_unit_deletions {
                let is_unit = checker
                    .clause_range(clause)
                    .filter(|&i| !checker.assignment[-checker.db[i]])
                    .count()
                    == 1;
                if is_unit {
                    checker.fields_mut(clause).set_deletion_ignored(true);
                    checker.skipped_deletions += 1;
                    if checker.config.verbosity > 0 {
                        warn!(
                            "Ignoring deletion of (pseudo) unit clause {}",
                            checker.clause_to_string(clause)
                        );
                    }
                } else {
                    watches_remove(checker, checker.clause_mode(clause), clause);
                }
            } else {
                invariant!(!checker.fields(clause).is_scheduled());
                watches_remove(checker, Mode::NonCore, clause);
                if checker.fields(clause).is_reason() {
                    revision_create(checker, clause);
                    let no_conflict = propagate(checker);
                    invariant!(no_conflict == NO_CONFLICT);
                    watch_invariants(checker);
                }
            }
        } else {
            invariant!(clause == checker.lemma);
            if checker.clause(clause).empty() {
                warn!(
                    "conflict claimed but not detected in {}",
                    checker.clause_to_string(clause)
                );
                checker.rejection.failed_proof_step = i;
                checker.rejection.natural_model_length = Some(checker.assignment.len());
                return false;
            }
            checker.lemma += 1;
            if add_premise(checker, clause) == CONFLICT {
                return close_proof(checker, i + 1);
            }
        }
    }
    invariant!({
        let last_step = checker.proof[checker.proof_steps_until_conflict];
        !last_step.is_deletion() && checker.clause(last_step.clause()).empty()
    });
    unreachable()
}

#[cfg_attr(feature = "flame_it", flame)]
fn verify(checker: &mut Checker) -> bool {
    log!(checker, 1, "[verify]");
    defer_log!(checker, 1, "[verify] done\n");
    let _timer = Timer::name("verifying proof");
    for i in (0..checker.proof_steps_until_conflict).rev() {
        let proof_step = checker.proof[i];
        let clause = proof_step.clause();
        let accepted = if proof_step.is_deletion() {
            if clause == Clause::DOES_NOT_EXIST {
                continue;
            }
            log!(
                checker,
                1,
                "[verify] del {}",
                checker.clause_to_string(clause)
            );
            if checker.config.skip_unit_deletions {
                if !checker.fields(clause).is_reason() {
                    // not actually deleted otherwise!
                    invariant!(checker.clause_mode(clause) == Mode::NonCore);
                    watches_add(checker, Stage::Verification, clause);
                }
            } else {
                if checker.fields(clause).has_revision() {
                    let mut revision = checker.revisions.pop();
                    revision_apply(checker, &mut revision);
                }
                watches_add(checker, Stage::Verification, clause);
            }
            if checker.config.grat_filename.is_some() {
                // TODO
                // if !checker.grat_in_deletion {
                checker.grat.push(GRATLiteral::DELETION);
                // checker.grat_in_deletion = true;
                // }
                checker.grat.push(GRATLiteral::from_clause(clause));
                // if checker.grat_in_deletion {
                checker.grat.push(GRATLiteral::ZERO);
                // checker.grat_in_deletion = false;
                // }
            }
            true
        } else {
            checker.lemma -= 1;
            let lemma = checker.lemma;
            invariant!(clause == lemma);
            watches_remove(checker, checker.clause_mode(lemma), lemma);
            unpropagate_unit(checker, lemma);
            if checker.fields(lemma).is_scheduled() {
                move_falsified_literals_to_end(checker, lemma);
                log!(
                    checker,
                    1,
                    "[verify] add {}",
                    checker.clause_to_string(lemma)
                );
                check_inference(checker)
            } else {
                log!(
                    checker,
                    2,
                    "[verify] skip {}",
                    checker.clause_to_string(lemma)
                );
                continue;
            }
        };
        if !accepted {
            checker.rejection.failed_proof_step = i;
            return false;
        }
        if checker.config.lrat_filename.is_some() {
            checker.optimized_proof.push(proof_step)
        }
    }
    if checker.config.grat_filename.is_some() {
        checker.grat.push(GRATLiteral::UNIT_PROP);
        for position in 1..checker.assignment.len() {
            let reason = checker.assignment.trail_at(position).1;
            if reason.is_assumed() {
                continue;
            }
            let reason_clause = checker.offset2clause(reason.offset());
            if checker.fields(reason_clause).is_scheduled() {
                checker.grat.push(GRATLiteral::from_clause(reason_clause));
            }
        }
        checker.grat.push(GRATLiteral::ZERO);
    }
    true
}

fn unpropagate_unit(checker: &mut Checker, clause: Clause) {
    if !checker.fields(clause).is_reason() {
        return;
    }
    if let Some(offset) = checker
        .clause_range(clause)
        .find(|&offset| checker.assignment[checker.db[offset]])
    {
        let unit = checker.db[offset];
        let trail_length = checker.assignment.position_in_trail(unit);
        invariant!(trail_length < checker.assignment.len());
        if checker.config.grat_filename.is_some() {
            checker.grat.push(GRATLiteral::UNIT_PROP);
            for position in trail_length..checker.assignment.len() {
                let reason = checker.assignment.trail_at(position).1;
                let reason_clause = checker.offset2clause(reason.offset());
                // TODO?
                if checker.fields(reason_clause).is_scheduled() {
                    checker.grat.push(GRATLiteral::from_clause(reason_clause));
                }
            }
            checker.grat.push(GRATLiteral::ZERO);
        }
        while checker.assignment.len() > trail_length {
            let reason = checker.assignment.pop().1;
            set_reason_flag(checker, reason, true);
        }
        checker.processed = trail_length;
    }
}

/// sortSize in drat-trim
fn move_falsified_literals_to_end(checker: &mut Checker, clause: Clause) -> usize {
    let head = checker.clause_range(clause).start;
    let mut effective_end = head;
    checker.rejection.lemma.clear();
    for offset in checker.clause_range(clause) {
        let literal = checker.db[offset];
        checker.rejection.lemma.push(literal);
        if checker.config.skip_unit_deletions {
            invariant!(!checker.assignment[literal]);
        }
        if !checker.assignment[-literal] {
            // if not falsified
            checker.db[offset] = checker.db[effective_end];
            checker.db[effective_end] = literal;
            effective_end += 1;
        }
    }
    // Sick witness would be incorrect because of this modification.
    // That's why we copy it to checker.rejection.lemma.
    for offset in effective_end..checker.clause_range(clause).end {
        checker.db[offset] = Literal::BOTTOM;
    }
    effective_end - head
}

fn write_lemmas(checker: &Checker) -> io::Result<()> {
    let mut file = match &checker.config.lemmas_filename {
        Some(filename) => BufWriter::new(File::create(filename)?),
        None => return Ok(()),
    };
    for lemma in Clause::range(checker.lemma, checker.closing_empty_clause()) {
        if checker.fields(lemma).is_scheduled() {
            write_clause(&mut file, checker.clause(lemma).iter())?;
            writeln!(file)?;
        }
    }
    Ok(())
}

fn write_grat_certificate(checker: &mut Checker) -> io::Result<()> {
    let mut file = match &checker.config.grat_filename {
        Some(filename) => BufWriter::new(File::create(filename)?),
        None => return Ok(()),
    };
    write!(file, "GRATbt {} 0\n", std::mem::size_of::<Literal>())?; // NB this needs to fit clause IDs
    write!(
        file,
        "{} {} 2\n",
        GRATLiteral::CONFLICT,
        GRATLiteral::from_clause(checker.grat_conflict_clause)
    )?;
    let mut i = 0;
    while i < checker.grat.len() {
        let item = checker.grat[i];
        let mut n = 1;
        write!(file, "{}", item)?;
        match item {
            GRATLiteral::CONFLICT => unreachable(),
            GRATLiteral::UNIT_PROP => loop {
                i += 1;
                let grat_clause = checker.grat[i];
                n += 1;
                write!(file, " {}", grat_clause)?;
                if grat_clause == GRATLiteral::ZERO {
                    break;
                }
            },
            GRATLiteral::DELETION => {
                loop {
                    i += 1;
                    let grat_clause = checker.grat[i];
                    n += 1;
                    write!(file, " {}", grat_clause)?;
                    if grat_clause == GRATLiteral::ZERO {
                        break;
                        // let next_is_deletion_too = i + 1 < checker.grat.len()
                        // && checker.grat[i + 1] == GRATLiteral::DELETION;
                        // if !next_is_deletion_too {
                        //     break
                        // }
                        // i += 1;
                    }
                }
            }
            GRATLiteral::RUP_LEMMA => {
                i += 1;
                let lemma = checker.grat[i];
                n += 1;
                write!(file, " {}", lemma)?;
                for &literal in checker.clause(lemma.to_clause()) {
                    if literal != Literal::BOTTOM {
                        n += 1;
                        write!(file, " {}", literal)?;
                    }
                }
                n += 1;
                write!(file, " 0")?;
                loop {
                    i += 1;
                    let grat_clause = checker.grat[i];
                    n += 1;
                    write!(file, " {}", grat_clause)?;
                    if grat_clause == GRATLiteral::ZERO {
                        break;
                    }
                }
                i += 1;
                n += 1;
                write!(file, " {}", checker.grat[i])?; // conflict
            }
            GRATLiteral::RAT_LEMMA => {
                i += 1;
                let lemma = checker.grat[i];
                let clause_slice = checker.clause(lemma.to_clause());
                n += 1;
                write!(file, " {}", clause_slice[0])?;
                n += 1;
                write!(file, " {}", lemma)?;
                for &literal in clause_slice {
                    if literal != Literal::BOTTOM {
                        n += 1;
                        write!(file, " {}", literal)?;
                    }
                }
                n += 1;
                write!(file, " 0")?;
                loop {
                    i += 1;
                    let unit = checker.grat[i];
                    if unit == GRATLiteral::ZERO {
                        break;
                    }
                    n += 1;
                    write!(file, " {}", unit)?;
                }
                n += 1;
                write!(file, " 0")?;
                loop {
                    i += 1;
                    let candidate = checker.grat[i];
                    if candidate == GRATLiteral::ZERO {
                        break;
                    }
                    n += 1;
                    write!(file, " {}", candidate)?;
                    loop {
                        i += 1;
                        let unit = checker.grat[i];
                        if unit == GRATLiteral::ZERO {
                            break;
                        }
                        n += 1;
                        write!(file, " {}", unit)?;
                    }
                    i += 1;
                    n += 1;
                    write!(file, " 0")?;
                    n += 1;
                    write!(file, " {}", checker.grat[i])?; // conflict
                }
                n += 1;
                write!(file, " 0")?;
            }
            GRATLiteral::RAT_COUNTS => unreachable(),
            _ => unreachable(),
        }
        writeln!(file, " {}", n)?;
        i += 1;
    }
    {
        let mut n = 1;
        write!(file, "{}", GRATLiteral::DELETION)?;
        // delete lemmas that were never used
        for clause in Clause::range(0, checker.lemma) {
            if !checker.fields(clause).is_scheduled() {
                n += 1;
                write!(file, " {}", GRATLiteral::from_clause(clause))?;
            }
        }
        n += 1;
        write!(file, " 0")?;
        writeln!(file, " {}", n)?;
    }
    {
        let mut n = 1;
        write!(file, "{}", GRATLiteral::RAT_COUNTS)?;
        for literal in Literal::all(checker.maxvar) {
            let count = checker.grat_rat_counts[literal];
            if count != 0 {
                n += 2;
                write!(file, " {} {}", literal, count)?;
            }
        }
        n += 1;
        write!(file, " 0")?;
        writeln!(file, " {}", n)?;
    }
    Ok(())
}

#[cfg_attr(feature = "flame_it", flame)]
fn write_lrat_certificate(checker: &mut Checker) -> io::Result<()> {
    let mut file = match &checker.config.lrat_filename {
        Some(filename) => BufWriter::new(File::create(filename)?),
        None => return Ok(()),
    };
    let num_clauses = checker.closing_empty_clause().as_offset() + 1;
    let mut clause_deleted = Array::new(false, num_clauses);
    let empty_clause_as_premise =
        Clause::range(0, checker.lemma).any(|clause| checker.clause(clause).empty());
    if empty_clause_as_premise {
        // write an empty LRAT certificate, this is accepted by lratcheck
        return Ok(());
    }
    #[derive(Debug, PartialEq, Eq, Clone, Copy)]
    enum State {
        Lemma,
        Deletion,
    };
    let mut state = State::Deletion;
    invariant!(checker.lrat_id == lrat_id(checker, checker.lemma - 1));
    write!(file, "{} d ", checker.lrat_id)?;
    // delete lemmas that were never used
    for clause in Clause::range(0, checker.lemma) {
        if !checker.fields(clause).is_scheduled() {
            write_lrat_deletion(checker, &mut file, &mut clause_deleted, clause)?;
        }
    }
    for i in (0..checker.optimized_proof.len()).rev() {
        let proof_step = checker.optimized_proof[i];
        let clause = proof_step.clause();
        match state {
            State::Lemma => {
                if proof_step.is_deletion() {
                    write!(file, "{} d ", checker.lrat_id)?;
                    write_lrat_deletion(checker, &mut file, &mut clause_deleted, clause)
                } else {
                    write_lrat_lemma(checker, &mut file, clause)
                }?;
            }
            State::Deletion => {
                if proof_step.is_deletion() {
                    write_lrat_deletion(checker, &mut file, &mut clause_deleted, clause)
                } else {
                    writeln!(file, "0")?;
                    write_lrat_lemma(checker, &mut file, clause)
                }?;
            }
        }
        state = if proof_step.is_deletion() {
            State::Deletion
        } else {
            State::Lemma
        };
    }
    if state == State::Deletion {
        writeln!(file, "0")?;
    }
    Ok(())
}

fn lrat_id(checker: &Checker, clause: Clause) -> Clause {
    checker.clause_lrat_id[clause]
}

fn write_lrat_lemma(
    checker: &mut Checker,
    file: &mut impl Write,
    clause: Clause,
) -> io::Result<()> {
    invariant!(checker.fields(clause).is_scheduled());
    checker.lrat_id += 1;
    checker.clause_lrat_id[clause] = checker.lrat_id;
    write!(file, "{} ", lrat_id(checker, clause))?;
    write_clause(file, checker.clause(clause).iter())?;
    write!(file, " ")?;
    let mut i = checker.clause_lrat_offset[clause];
    loop {
        let lrat_literal = checker.lrat[i];
        if lrat_literal.is_zero() {
            break;
        }
        let hint = lrat_literal.clause();
        if lrat_literal.is_resolution_candidate() {
            write!(file, "-{} ", lrat_id(checker, hint))
        } else {
            invariant!(lrat_literal.is_hint());
            invariant!(checker.fields(hint).is_scheduled());
            invariant!(lrat_id(checker, hint) != Clause::NEVER_READ);
            write!(file, "{} ", lrat_id(checker, hint))
        }?;
        i += 1;
    }
    writeln!(file, "0")
}

fn write_lrat_deletion(
    checker: &Checker,
    file: &mut impl Write,
    clause_deleted: &mut Array<Clause, bool>,
    clause: Clause,
) -> io::Result<()> {
    invariant!(clause != Clause::DOES_NOT_EXIST);
    invariant!(clause != Clause::NEVER_READ);
    invariant!(clause != Clause::UNINITIALIZED);
    invariant!(
        (lrat_id(checker, clause) == Clause::UNINITIALIZED)
            == (clause >= checker.lemma && !checker.fields(clause).is_scheduled())
    );
    if lrat_id(checker, clause) != Clause::UNINITIALIZED
        && !clause_deleted[clause]
        && !checker.fields(clause).deletion_ignored()
    {
        clause_deleted[clause] = true;
        write!(file, "{} ", checker.clause_lrat_id[clause])
    } else {
        Ok(())
    }
}

fn write_clause<'a, T>(file: &mut impl Write, clause: T) -> io::Result<()>
where
    T: Iterator<Item = &'a Literal>,
{
    for &literal in clause {
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
    let proof_format = match checker.config.redundancy_property {
        RedundancyProperty::RAT => "DRAT-arbitrary-pivot",
        RedundancyProperty::PR => "PR",
    };
    let proof_step = checker.rejection.failed_proof_step;

    let assignment = if let Some(stable) = &checker.rejection.stable_assignment {
        stable
    } else {
        &checker.assignment
    };
    let natural_model_length = checker
        .rejection
        .natural_model_length
        .unwrap_or_else(|| checker.assignment.len());
    write!(file, "# Failed to prove lemma")?;
    for &literal in &checker.rejection.lemma {
        if literal != Literal::BOTTOM {
            write!(file, " {}", literal)?;
        }
    }
    writeln!(file, " 0")?;
    writeln!(file, "proof_format   = \"{}\"", proof_format)?;
    writeln!(
        file,
        "proof_step     = {} # Failed line in the proof",
        proof_step + 1
    )?;
    write!(file, "natural_model  = [")?;
    for literal in Literal::all(checker.maxvar) {
        if assignment[literal] && assignment.position_in_trail(literal) < natural_model_length {
            write!(file, "{}, ", literal)?;
        }
    }
    writeln!(file, "]")?;
    // TODO
    if let Some(pivot) = checker.rejection.pivot {
        writeln!(file, "[[witness]]")?;
        write!(file, "failing_clause = [")?;
        if let Some(failing_clause) = checker.rejection.resolved_with {
            for &literal in checker.clause(failing_clause) {
                if literal != Literal::BOTTOM {
                    write!(file, "{}, ", literal)?;
                }
            }
        } else {
            // TODO
        }
        writeln!(file, "]")?;
        write!(file, "failing_model  = [")?;
        for literal in Literal::all(checker.maxvar) {
            if assignment[literal] && assignment.position_in_trail(literal) >= natural_model_length
            {
                write!(file, "{}, ", literal)?;
            }
        }
        writeln!(file, "]")?;
        writeln!(file, "pivot          = {}", pivot)?;
    }
    Ok(())
}

fn assignment_invariants(checker: &Checker) {
    if !crate::config::ASSIGNMENT_INVARIANTS {
        return;
    }
    for &(literal, reason) in &checker.assignment {
        if !reason.is_assumed() {
            let clause = checker.offset2clause(reason.offset());
            invariant!(
                clause < checker.lemma,
                "current lemma is {}, but literal {} is assigned because of lemma {} in {}",
                checker.lemma,
                literal,
                checker.clause_to_string(clause),
                checker.assignment
            );
        }
    }
    for position in 0..checker.assignment.len() {
        let literal = checker.assignment.trail_at(position).0;
        invariant!(position == checker.assignment.position_in_trail(literal));
    }
}

type Watchlist = Stack<usize>;

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
enum Mode {
    Core,
    NonCore,
}

fn watch_invariants(checker: &Checker) {
    if crate::config::WATCH_INVARIANTS {
        // each watch points to a clause that is neither falsified nor satisfied
        for &mode in &[Mode::Core, Mode::NonCore] {
            for lit in Literal::all(checker.maxvar) {
                for &head in &watchlist(checker, mode)[lit] {
                    watch_invariant(checker, lit, head);
                }
            }
        }
    }
}

fn watch_invariant(checker: &Checker, lit: Literal, head: usize) {
    let [w1, w2] = checker.watches(head);
    invariant!(
        lit == w1 || lit == w2,
        "watch {} not within the first two literals in [@{}]",
        lit,
        head,
    );
    invariant!(
        checker.assignment[w1]
            || checker.assignment[w2]
            || (!checker.assignment[-w1] && !checker.assignment[-w2]),
        format!(
            "watched clause needs two unassigned watches or at least one satisfied watch: violated in [@{}] - {}",
            head, checker.assignment
        )
    );
    let clause = checker.offset2clause(head);
    invariant!(
        stable_under_unit_propagation(&checker.assignment, checker.clause(clause)),
        "Model is not stable for {}",
        checker.clause_colorized(clause)
    );
}

fn watchlist(checker: &Checker, mode: Mode) -> &Array<Literal, Watchlist> {
    match mode {
        Mode::Core => &checker.watchlist_core,
        Mode::NonCore => &checker.watchlist_noncore,
    }
}

fn watchlist_mut(checker: &mut Checker, mode: Mode) -> &mut Array<Literal, Watchlist> {
    match mode {
        Mode::Core => &mut checker.watchlist_core,
        Mode::NonCore => &mut checker.watchlist_noncore,
    }
}

fn watch_remove_at(checker: &mut Checker, mode: Mode, lit: Literal, position_in_watchlist: usize) {
    log!(
        checker,
        4,
        "watchlist[{}] del [{}]: {}",
        lit,
        position_in_watchlist,
        watchlist(checker, mode)[lit][position_in_watchlist]
    );
    watchlist_mut(checker, mode)[lit].swap_remove(position_in_watchlist);
}

fn watch_add(checker: &mut Checker, mode: Mode, lit: Literal, head: usize) {
    log!(checker, 4, "watchlist[{}] add {}", lit, head);
    watchlist_mut(checker, mode)[lit].push(head)
}

fn watches_remove(checker: &mut Checker, mode: Mode, clause: Clause) {
    let head = checker.clause_range(clause).start;
    log!(checker, 4, "removing watches for [@{}]", head);
    let [w1, w2] = checker.watches(head);
    watches_find_and_remove(checker, mode, w1, head);
    watches_find_and_remove(checker, mode, w2, head);
    checker.fields_mut(clause).set_in_watchlist(false);
}

fn watches_find_and_remove(checker: &mut Checker, mode: Mode, lit: Literal, head: usize) -> bool {
    requires!(lit != Literal::TOP);
    invariant!(
        watchlist(checker, mode)[lit]
            .iter()
            .filter(|&h| *h == head)
            .count()
            <= 1,
        "duplicate clause [@{}] in watchlist of {}",
        head,
        lit
    );
    watchlist(checker, mode)[lit]
        .iter()
        .position(|&watched| watched == head)
        .map(|position| watch_remove_at(checker, mode, lit, position))
        .is_some()
}

// Revisions

fn is_in_cone(checker: &Checker, literal: Literal, reason: Reason) -> bool {
    invariant!(!reason.is_assumed());
    checker
        .clause(checker.offset2clause(reason.offset()))
        .iter()
        .any(|&lit| lit != literal && checker.literal_is_in_cone_preprocess[-lit])
}

fn revision_create(checker: &mut Checker, clause: Clause) {
    assignment_invariants(checker);
    watch_invariants(checker);
    log!(checker, 1, "{}", checker.assignment);
    let unit = *checker
        .clause(clause)
        .iter()
        .find(|&lit| checker.assignment[*lit])
        .unwrap();
    let unit_position = checker.assignment.position_in_trail(unit);
    let unit_reason = checker.assignment.trail_at(unit_position).1;
    checker.fields_mut(clause).set_has_revision(true);
    let mut revision = Revision {
        cone: Stack::new(),
        position_in_trail: Stack::new(),
        reason_clause: Stack::new(),
        trail_length_after_removing_cone: usize::max_value(),
    };
    add_to_revision(checker, &mut revision, unit, unit_reason);
    let mut next_position_to_overwrite = unit_position;
    for position in unit_position + 1..checker.assignment.len() {
        let (literal, reason) = checker.assignment.trail_at(position);
        if is_in_cone(checker, literal, reason) {
            add_to_revision(checker, &mut revision, literal, reason);
        } else {
            checker
                .assignment
                .move_to(position, next_position_to_overwrite);
            next_position_to_overwrite += 1;
        }
    }
    let length_after_removing_cone = next_position_to_overwrite;
    revision.trail_length_after_removing_cone = length_after_removing_cone;
    checker.assignment.shrink_trail(length_after_removing_cone);
    checker.processed = length_after_removing_cone;
    for &literal in &revision.cone {
        watchlist_revise(checker, literal);
    }
    log!(checker, 1, "Created {}\n{}", revision, checker.assignment);
    for &literal in &revision.cone {
        invariant!(checker.literal_is_in_cone_preprocess[literal]);
        checker.literal_is_in_cone_preprocess[literal] = false;
    }
    checker.revisions.push(revision);
    assignment_invariants(checker);
}

fn watchlist_revise(checker: &mut Checker, lit: Literal) {
    for &mode in &[Mode::Core, Mode::NonCore] {
        let mut i = 0;
        while i < watchlist(checker, mode)[lit].len() {
            let head = watchlist(checker, mode)[lit][i];
            let clause = checker.offset2clause(head);
            watches_revise(checker, mode, lit, clause, &mut i);
            i = i.wrapping_add(1);
        }
    }
}

fn watches_revise(
    checker: &mut Checker,
    mode: Mode,
    lit: Literal,
    clause: Clause,
    position_in_watchlist: &mut usize,
) {
    let head = checker.clause_range(clause).start;
    // NOTE swap them to simplify this
    let [w1, _w2] = checker.watches(head);
    let my_offset = head + if w1 == lit { 0 } else { 1 };
    let other_literal_offset = head + if w1 == lit { 1 } else { 0 };
    let other_literal = checker.db[other_literal_offset];
    if !checker.assignment[-other_literal] {
        return;
    }
    match first_non_falsified(checker, clause, head + 2) {
        None => {
            if !checker.assignment[lit] {
                assign(checker, lit, Reason::forced(head));
            }
        }
        Some(offset) => {
            let new_literal = checker.db[offset];
            // We know that  lit is the literal that was unassigned in this revision.
            // Additionally, other_literal is falsified.
            //
            // Invariant 1 states: a falsified watch implies that the other watch is satisfied.
            // If we replace lit with firstlit, then we need to ensure this, so this is
            // only possible if firstlit is satisfied.
            //
            // Otherwise we simply replace the falsified other_literal after which both watches are
            // non-falsified. (This is more expensive because we have to find the watch).

            if checker.assignment[new_literal] {
                checker.db.swap(my_offset, offset);
                watch_remove_at(checker, mode, lit, *position_in_watchlist);
                *position_in_watchlist = position_in_watchlist.wrapping_sub(1);
                invariant!(mode == checker.clause_mode(clause));
            } else {
                checker.db.swap(other_literal_offset, offset);
                let _removed = watches_find_and_remove(checker, mode, other_literal, head);
            }
            watch_add(checker, mode, new_literal, head);
        }
    };
}

fn add_to_revision(checker: &mut Checker, revision: &mut Revision, lit: Literal, reason: Reason) {
    revision.cone.push(lit);
    checker.literal_is_in_cone_preprocess[lit] = true;
    revision
        .position_in_trail
        .push(checker.assignment.position_in_trail(lit));
    invariant!(!reason.is_assumed());
    revision
        .reason_clause
        .push(checker.offset2clause(reason.offset()));
    checker.assignment.unassign(lit);
    #[cfg(feature = "clause_lifetime_heuristic")]
    {
        checker.literal_minimal_lifetime[lit] = 0;
    }
    set_reason_flag(checker, reason, false);
}

fn revision_apply(checker: &mut Checker, revision: &mut Revision) {
    assignment_invariants(checker);
    // During the forward pass, after revision_create, we propagate.
    // That propagation will assign a subset of literals that were in the cone.
    // This subset needs to be removed before applying the cone.
    // It could be done with something like this:
    // ```
    // while checker.assignment.len() > revision.trail_length_after_removing_cone {
    //     let (_literal, reason) = checker.assignment.pop();
    //     invariant!(!reason.is_assumed());
    //     set_reason_flag(checker, reason, false);
    // }
    // let introductions = revision.cone.len();
    // let mut left_position = checker.assignment.len();
    // ```
    // However, instead of popping and pushing later we do that implicitly by
    // overwriting the latter part of the stack. For this we need a different
    // value of `introductions` and `left_position`.
    // This might be an unnecessesarily complex way of doing this without any benefit.
    let mut introductions = 0;
    let mut literals_to_revise = revision.cone.len();
    for &literal in &revision.cone {
        if checker.assignment[literal] {
            let position = checker.assignment.position_in_trail(literal);
            let reason = checker.assignment.trail_at(position).1;
            invariant!(!reason.is_assumed());
            set_reason_flag(checker, reason, false);
        } else {
            introductions += 1;
        }
    }
    log!(checker, 1, "Applying {}{}", revision, checker.assignment);
    let length_after_adding_cone = checker.assignment.len() + introductions;
    let mut right_position = length_after_adding_cone - 1;
    let mut left_position = right_position - literals_to_revise + 1;
    checker.assignment.grow_trail(length_after_adding_cone);
    checker.processed = length_after_adding_cone;
    // Re-introduce the assignments that were induced by the deleted unit,
    // starting with the ones with the highest offset in the trail.
    while literals_to_revise > 0 {
        let (literal, reason) = if right_position
            == revision.position_in_trail[literals_to_revise - 1]
        {
            literals_to_revise -= 1;
            let lit = revision.cone[literals_to_revise];
            let lit_reason =
                Reason::forced(checker.clause2offset(revision.reason_clause[literals_to_revise]));
            set_reason_flag(checker, lit_reason, true);
            (lit, lit_reason)
        } else {
            invariant!(left_position > 0 && left_position <= checker.assignment.len());
            left_position -= 1;
            checker.assignment.trail_at(left_position)
        };
        checker
            .assignment
            .set_trail_at(right_position, literal, reason);
        right_position -= 1;
    }
    log!(checker, 1, "Applied revision:\n{}", checker.assignment);
    watches_reset(checker, revision);
    assignment_invariants(checker);
}

fn watches_reset(checker: &mut Checker, revision: &Revision) {
    for &literal in &revision.cone {
        watches_reset_list(checker, literal);
        watches_reset_list(checker, -literal);
    }
}

fn watches_reset_list(checker: &mut Checker, literal: Literal) {
    for &mode in &[Mode::Core, Mode::NonCore] {
        let mut i = 0;
        while i < watchlist(checker, mode)[literal].len() {
            watches_reset_list_at(checker, mode, literal, &mut i);
            i = i.wrapping_add(1);
        }
    }
}

fn watches_reset_list_at(
    checker: &mut Checker,
    mode: Mode,
    literal: Literal,
    position_in_watchlist: &mut usize,
) {
    let head = watchlist(checker, mode)[literal][*position_in_watchlist];
    let clause = checker.offset2clause(head);
    let [w1, w2] = checker.watches(head);
    if !checker.assignment[-w1] && !checker.assignment[-w2] {
        // watches are correct
        return;
    }
    let head = checker.clause_range(clause).start;
    if literal != w1 {
        requires!(literal == w2);
        checker.db.swap(head, head + 1);
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
        if offset + 1 == second_offset
            // TODO why
            || offset == second_offset
        {
            // Case A: nothing to do!
            return;
        } else {
            // Case B: clause will not be watched on other_lit, but on checker.db[second_offset] instead.
            let _removed = watches_find_and_remove(checker, mode, other_lit, head);
            let tmp = checker.db[second_offset];
            checker.db[offset + 1] = tmp;
            checker.db[second_offset] = other_lit;
            watch_add(checker, mode, tmp, head);
        }
    } else {
        // Cases C and D: clause will not be watched on literal, but on *second_offset instead.
        watch_remove_at(checker, mode, literal, *position_in_watchlist);
        *position_in_watchlist = position_in_watchlist.wrapping_sub(1);
        checker.db[offset] = checker.db[second_offset];
        checker.db[second_offset] = literal;
        watch_add(checker, mode, checker.db[offset], head); // Case C: additionally, clause will still be watched on other_lit
        if offset + 1 != first_offset {
            // Case D: additionally, clause will not be watched on other_lit, but on checker.db[offset + 1] instead.
            let _removed = watches_find_and_remove(checker, mode, other_lit, head);
            checker.db[offset + 1] = checker.db[first_offset];
            checker.db[first_offset] = other_lit;
            watch_add(checker, mode, checker.db[offset + 1], head);
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
            let position_in_trail = checker.assignment.position_in_trail(-literal);
            if position_in_trail > *best_position {
                *best_position = position_in_trail;
                *best_false = *offset;
            }
            *offset += 1;
        } else {
            return true;
        }
    }
    false
}

impl Checker {
    pub fn print_memory_usage(&self) {
        print_memory_usage(self)
    }
}

fn print_memory_usage(checker: &Checker) {
    macro_rules! heap_space {
        ($($x:expr,)*) => (vec!($(($x).heap_space()),*));
    }
    let usages = vec![
        ("db", checker.db.heap_space()),
        ("proof", checker.proof.heap_space()),
        ("optimized-proof", checker.optimized_proof.heap_space()),
        ("watchlist_core", checker.watchlist_core.heap_space()),
        ("watchlist_noncore", checker.watchlist_noncore.heap_space()),
        ("revisions", checker.revisions.heap_space()),
        ("lrat", checker.lrat.heap_space()),
        (
            "rest",
            heap_space!(
                checker.assignment,
                checker.rejection,
                checker.literal_is_in_cone_preprocess,
                checker.clause_lrat_id,
                checker.clause_lrat_offset,
                checker.clause_pivot,
            )
            .iter()
            .sum(),
        ),
    ];
    let total = usages.iter().fold(0, |sum, tuple| sum + tuple.1);
    output::value("memory (MB)", format_memory_usage(total));
    if !checker.config.memory_usage_breakdown {
        return;
    }
    for tuple in usages {
        output::value(
            &format!("memory-{}", tuple.0.replace("_", "-")),
            format_memory_usage(tuple.1),
        );
    }
}
