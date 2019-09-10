//! Proof checking logic

use crate::{
    assignment::{stable_under_unit_propagation, Assignment},
    clause::{write_clause, Clause, GRATLiteral, LRATDependency, LRATLiteral, ProofStep, Reason},
    clausedatabase::{clause_db , witness_db} ,
    config::{unreachable , Config , ProofFormat},
    literal::{Literal, Variable},
    memory::{format_memory_usage, Array, BoundedVector, HeapSpace, Offset, StackMapping, Vector},
    output::{self, Timer},
    proof::{Proof},
    sick::{Sick, Witness},
};
use ansi_term::Colour;
use bitfield::bitfield;
use rate_macros::HeapSpace;
use std::{
    cmp, fmt,
    fs::File,
    io,
    io::{BufWriter, Write},
    iter::FromIterator,
    ops::{self, Index},
};

/// The (intermediate) result of a proof checker
#[derive(PartialEq, Eq, Debug)]
pub enum Verdict {
    Verified,
    NoConflict,
    Falsified,
}

/// The proof checker
///
/// Contains most everything but the clause and witness databases.
#[derive(Debug)]
pub struct Checker {
    /// The input proof
    pub proof: Vector<ProofStep>,
    /// Flags
    pub config: Config,
    pub proof_format: ProofFormat,

    /// The highest variable that is used in the formula or proof
    maxvar: Variable,
    /// The trail storing variable assignments
    assignment: Assignment,
    /// Index of the first literal in the assignment that has not yet been propagated
    processed: usize,
    /// The current lemma
    ///
    /// Initially this is the first lemma in the proof. It will be incremented
    /// at each step in the forward pass until there is a conflict. In the
    /// backwards pass, lemma is decremented, ending with the first lemma in
    /// the proof.
    lemma: Clause,
    /// The forward pass can detect an early conflict at some proof step, this records that step
    proof_steps_until_conflict: usize,
    /// True while inside an inference check (as opposed to propagating with no assumptions)
    soft_propagation: bool,
    /// Incorrectness certificate
    rejection: Sick,
    /// The unmodified lemma that failed the inference check.
    ///
    /// We need this to produce a correct SICK certificate, because of
    /// [`move_falsified_literals_to_end`](fn.move_falsified_literals_to_end.html).
    rejection_lemma: Vector<Literal>,

    /// Contains clauses that caused a conflict
    implication_graph: StackMapping<usize, bool>,
    /// Used in the forward pass for literals that are unassigned after a reason deletion
    literal_is_in_cone_preprocess: Array<Literal, bool>,
    /// The watch-lists for non-core clauses
    watchlist_noncore: Array<Literal, Watchlist>,
    /// The watch-lists for core clauses
    watchlist_core: Array<Literal, Watchlist>,

    /// Pivot to use (or rather try first) for each clause
    clause_pivot: Array<Clause, Literal>,
    /// Used for querying the witness in PR checks
    is_in_witness: Array<Literal, bool>,

    /// Revisions to restore the trail after reason deletions in the backward pass
    revisions: Vector<Revision>,

    /// LRAT lines justifying inferences of core lemmas
    lrat: Vector<LRATLiteral>,
    /// Maps core lemmas to the start of their LRAT line in [`lrat`](#structfield.lrat)
    clause_lrat_offset: Array<Clause, usize>,
    /// Maps internal clause identifiers to LRAT clause identifiers
    clause_lrat_id: Array<Clause, Clause>,
    /// Temporary place for the dependencies of a single inference
    dependencies: Vector<LRATDependency>,
    /// The maximum LRAT clause identifier
    lrat_id: Clause,
    /// Clauses that were unit in the RUP check (before the RAT check).
    /// They need to be emitted in the LRAT proof before the units for RAT checks.
    prerat_clauses: StackMapping<Clause, bool>, // Linear lookup should be fine here as well.
    /// Core lemmas plus aggressive deletions of no-longer used lemmas
    optimized_proof: BoundedVector<ProofStep>,

    /// GRAT lines justifying inferences of core lemmas
    grat: Vector<GRATLiteral>,
    /// THe falsified clause
    grat_conflict_clause: Clause,
    /// Whether the current GRAT line is a deletion
    grat_in_deletion: bool,
    /// Number of RAT inferences for each literal
    grat_rat_counts: Array<Literal, usize>,
    /// Temporary place for GRAT hints, to be written to [`grat`](#structfield.grat)
    grat_pending: Vector<GRATLiteral>,
    /// Temporary place for GRAT deletions, to be written to [`grat`](#structfield.grat)
    grat_pending_deletions: Vector<Clause>,
    /// Temporary place for GRAT hints, to be written to [`grat`](#structfield.grat);
    /// see [`grat_prerat`](#structfield.grat_prerat)
    grat_pending_prerat: Vector<GRATLiteral>,
    /// Similar to [`prerat_clauses`](#structfield.prerat_clauses) but for GRAT
    grat_prerat: Array<Clause, bool>,

    /// Size of the input formula.
    pub premise_length: usize,
    /// Number of verified RUP inferences.
    pub rup_introductions: usize,
    /// Number of verified RAT inferences.
    pub rat_introductions: usize,
    /// Number of deletions that were applied.
    pub deletions: usize,
    /// Number of deletions that were skipped.
    pub skipped_deletions: usize,
    /// Number of reason deletions that were applied.
    pub reason_deletions: usize,
    /// Number of unique reason deletions that were applied.
    pub reason_deletions_shrinking_trail: usize,
    /// Number of clauses that were already satisfied in the forward pass,
    /// so with `--skip-unit-deletions` we do not add them to the watchlists.
    pub satisfied_count: usize,
}

bitfield! {
    /// The data to store for each clause in the metadata field of the
    /// [ClauseDatabase](../clausedatabase/struct.ClauseDatabase.html).
    pub struct ClauseFields(u32);
    impl Debug;
    /// Whether the clause is in the core (scheduled for verification).
    is_scheduled, set_is_scheduled: 0;
    /// Whether the clause is a reason in the current trail.
    is_reason, set_is_reason: 1;
    /// Whether the clause is in some watchlist.
    in_watchlist, set_in_watchlist: 2;
    /// Whether a deletion of this clause produced a revision.
    has_revision, set_has_revision: 3;
    /// Whether a deletion of this clause was ignored.
    deletion_ignored, set_deletion_ignored: 4;
    /// Whether this clause is a reason for the current conflict.
    in_conflict_graph, set_in_conflict_graph: 5;
}

/// Stores the information that was removed from the trail after a reason deletion
#[derive(Debug, HeapSpace, Default, Clone)]
struct Revision {
    /// The literals that were unassigned.
    cone: Vector<Literal>,
    /// The position of each unassigned literal.
    position_in_trail: Vector<usize>,
    /// The reason clause of each unassigned literal.
    reason_clause: Vector<Clause>,
    /// The length of the trail after unassigning literals (but before propagating).
    trail_length_after_removing_cone: usize,
}

impl Checker {
    pub fn new(proof: Proof, config: Config) -> Checker {
        let num_clauses = clause_db().number_of_clauses() as usize;
        let num_lemmas = proof.proof.len();
        let maxvar = proof.maxvar;
        let assignment = Assignment::new(maxvar);
        let lrat = config.lrat_filename.is_some();
        let grat = config.grat_filename.is_some();
        let proof_format = config.proof_format ;
        let mut checker = Checker {
            processed: assignment.len(),
            assignment,
            clause_lrat_id: if lrat {
                Array::new(Clause::UNINITIALIZED, num_clauses)
            } else {
                Array::default()
            },
            clause_pivot: Array::from(proof.pivots),
            dependencies: Stack::new(),
            config,
            proof_format ,
            soft_propagation: false,
            implication_graph: StackMapping::with_array_value_size_stack_size(
                false,
                maxvar.array_size_for_literals(),
                maxvar.as_offset() + 1, // need + 1 to hold a conflicting literal
            ),
            is_in_witness: Array::new(false, maxvar.array_size_for_literals()),
            lrat_id: if lrat {
                Clause::new(0)
            } else {
                Clause::UNINITIALIZED
            },
            clause_lrat_offset: if lrat {
                Array::new(usize::max_value(), num_clauses)
            } else {
                Array::default()
            },
            lrat: Vector::new(),
            prerat_clauses: if lrat {
                StackMapping::with_array_value_size_stack_size(
                    false,
                    num_clauses,
                    cmp::min(num_clauses, maxvar.array_size_for_literals()),
                )
            } else {
                StackMapping::default()
            },
            optimized_proof: if lrat {
                BoundedVector::with_capacity(2 * num_lemmas + num_clauses)
            } else {
                BoundedVector::default()
            },
            grat: Vector::new(),
            grat_conflict_clause: Clause::UNINITIALIZED,
            grat_in_deletion: false,
            grat_rat_counts: if grat {
                Array::new(0, maxvar.array_size_for_literals())
            } else {
                Array::default()
            },
            grat_pending: Vector::new(),
            grat_pending_prerat: Vector::new(),
            grat_pending_deletions: Vector::new(),
            grat_prerat: if grat {
                Array::new(false, num_clauses)
            } else {
                Array::default()
            },
            maxvar,
            proof: proof.proof,
            lemma: proof.proof_start,
            proof_steps_until_conflict: usize::max_value(),
            literal_is_in_cone_preprocess: Array::new(false, maxvar.array_size_for_literals()),
            revisions: Vector::new(),
            watchlist_noncore: Array::new(Vector::new(), maxvar.array_size_for_literals()),
            watchlist_core: Array::new(Vector::new(), maxvar.array_size_for_literals()),
            rejection: Sick::default(),
            rejection_lemma: Vector::new(),

            premise_length: proof.proof_start.as_offset(),
            rup_introductions: 0,
            rat_introductions: 0,
            deletions: 0,
            skipped_deletions: 0,
            reason_deletions: 0,
            reason_deletions_shrinking_trail: 0,
            satisfied_count: 0,
        };
        if lrat {
            for clause in Clause::range(0, checker.lemma) {
                checker.lrat_id += 1;
                checker.clause_lrat_id[clause] = checker.lrat_id;
            }
        }
        if checker.config.sick_filename.is_some() {
            checker.rejection.witness = Some(Vector::new())
        }
        checker
    }
    /// Run the checker.
    pub fn run(&mut self) -> Verdict {
        run(self)
    }
    /// Print memory usage statistics (after checking).
    pub fn print_memory_usage(&self) {
        print_memory_usage(self)
    }
    /// Build the DIMACS representation of the given clause.
    fn clause_to_string(&self, clause: Clause) -> String {
        clause_db().clause_to_string(clause)
    }
    /// Build the DIMACS representation of the given witness.
    #[allow(dead_code)]
    fn witness_to_string(&self, clause: Clause) -> String {
        witness_db().witness_to_string(clause)
    }
    /// The literals in the the clause.
    fn clause(&self, clause: Clause) -> &[Literal] {
        clause_db().clause(clause)
    }
    /// Access the witness by clause ID.
    #[allow(dead_code)]
    fn witness(&self, clause: Clause) -> &[Literal] {
        witness_db().witness(clause)
    }
    /// The database offsets of the literals in the the clause.
    fn clause_range(&self, clause: Clause) -> ops::Range<usize> {
        clause_db().clause_range(clause)
    }
    /// The database offsets of the literals in the the witness.
    fn witness_range(&self, clause: Clause) -> ops::Range<usize> {
        witness_db().witness_range(clause)
    }
    /// The first two literals in the clause.
    fn watches(&self, head: usize) -> [Literal; 2] {
        clause_db().watches(head)
    }
    /// Convert a clause identifier to the offset of the clause.
    fn clause2offset(&self, clause: Clause) -> usize {
        clause_db().clause2offset(clause)
    }
    /// Convert a clause offset to the identifier of the clause.
    fn offset2clause(&self, head: usize) -> Clause {
        clause_db().offset2clause(head)
    }
    /// Return whether this clause is in the core.
    fn clause_mode(&self, clause: Clause) -> Mode {
        if self.fields(clause).is_scheduled() {
            Mode::Core
        } else {
            Mode::NonCore
        }
    }
    /// Access the metadata for this clause.
    fn fields(&self, clause: Clause) -> &ClauseFields {
        unsafe { &*(clause_db().fields(clause) as *const u32 as *const ClauseFields) }
    }
    /// Access the mutable metadata for this clause.
    fn fields_mut(&mut self, clause: Clause) -> &mut ClauseFields {
        unsafe { &mut *(clause_db().fields_mut(clause) as *mut u32 as *mut ClauseFields) }
    }
    /// Access the metadata for the clause with this offset.
    /// This is possibly more efficient than [`fields()`](#method.fields).
    fn fields_from_offset(&self, offset: usize) -> &ClauseFields {
        unsafe { &*(clause_db().fields_from_offset(offset) as *const u32 as *const ClauseFields) }
    }
    /// Access the mutable metadata for the clause with this offset.
    /// This is possibly more efficient than [`fields()`](#method.fields_mut).
    fn fields_mut_from_offset(&mut self, offset: usize) -> &mut ClauseFields {
        unsafe {
            &mut *(clause_db().fields_mut_from_offset(offset) as *mut u32 as *mut ClauseFields)
        }
    }
    /// Build the DIMACS representation of this clause, but color literals
    /// according to the current assignment.
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
    /// Return the empty clause that finishes the proof.
    fn closing_empty_clause(&self) -> Clause {
        requires!(self.proof_steps_until_conflict != usize::max_value());
        let proof_step = self.proof[self.proof_steps_until_conflict];
        proof_step.clause()
    }
}

/// Run the checker.
fn run(checker: &mut Checker) -> Verdict {
    let verdict = if checker.config.forward {
        forward_check(checker)
    } else {
        let mut verdict = preprocess(checker);
        if verdict == Verdict::Verified {
            verdict = if verify(checker) {
                Verdict::Verified
            } else {
                Verdict::Falsified
            }
        }
        verdict
    };
    if verdict == Verdict::Verified {
        write_lemmas(checker).unwrap_or_else(|err| die!("Failed to write lemmas: {}", err));
        write_lrat_certificate(checker)
            .unwrap_or_else(|err| die!("Failed to write LRAT certificate: {}", err));
        write_grat_certificate(checker)
            .unwrap_or_else(|err| die!("Failed to write GRAT certificate: {}", err));
        Verdict::Verified
    } else {
        write_sick_witness(checker).expect("Failed to write incorrectness witness.");
        verdict
    }
}

/// Perform a forward check.
fn forward_check(checker: &mut Checker) -> Verdict {
    let _timer = Timer::name("forward check");
    for clause in Clause::range(0, checker.lemma) {
        if checker.clause(clause).is_empty() || add_premise(checker, clause) == CONFLICT {
            return close_proof(checker, 0);
        }
    }
    log!(checker, 1, "[forward check] added premise");
    for i in 0..checker.proof.len() {
        let proof_step = checker.proof[i];
        let clause = proof_step.clause();
        if proof_step.is_deletion() {
            forward_delete(checker, clause);
        } else {
            if !forward_preadd(checker, i, clause) {
                return Verdict::NoConflict;
            }
            if !check_inference(checker) {
                return Verdict::Falsified;
            }
            if add_premise(checker, clause) == CONFLICT {
                return close_proof(checker, i + 1);
            }
            checker.lemma += 1;
        }
    }
    Verdict::NoConflict
}

/// Delete a clause during the forward pass.
fn forward_delete(checker: &mut Checker, clause: Clause) {
    if clause == Clause::DOES_NOT_EXIST {
        return;
    }
    log!(
        checker,
        1,
        "[forward check] del {}",
        checker.clause_to_string(clause)
    );
    checker.deletions += 1;
    if checker.fields(clause).is_reason() {
        checker.reason_deletions += 1;
    }
    if checker.config.skip_unit_deletions {
        let is_unit = checker
            .clause(clause)
            .iter()
            .filter(|&&literal| !checker.assignment[-literal])
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
        watches_remove(checker, checker.clause_mode(clause), clause);
        if checker.fields(clause).is_reason() {
            let trail_length_before_creating_revision = checker.assignment.len();
            revision_create(checker, clause);
            let no_conflict = propagate(checker);
            let trail_length_after_propagating = checker.assignment.len();
            invariant!(no_conflict == NO_CONFLICT);
            if trail_length_after_propagating < trail_length_before_creating_revision {
                checker.reason_deletions_shrinking_trail += 1;
                log!(
                    checker,
                    1,
                    "reason deletion, created {}",
                    checker.revisions.last()
                );
            } else {
                log!(checker, 1, "reason deletion, but trail is unchanged");
            }
            watch_invariants(checker);
        }
    }
}

/// Must be called before adding a clause in the forward pass.
///
/// Returns true if we hit the empty clause (trivial UNSAT).
fn forward_preadd(checker: &mut Checker, step: usize, clause: Clause) -> bool {
    invariant!(clause == checker.lemma);
    if checker.clause(clause).is_empty() {
        if checker.config.sick_filename.is_some() {
            checker.rejection.proof_step = step;
        }
        extract_natural_model(checker, checker.assignment.len());
        false
    } else {
        true
    }
}

impl fmt::Display for Revision {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "revision:")?;
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

/// A boolean value that states whether a conflict has been reached by unit propagation.
///
/// We use the newtype pattern here to clearly distinguish from other
/// boolean values. We provide both constants explicitly and use `==` to compare it
/// instead of making it an enum for the lack of a good enum name.
#[derive(Debug, PartialEq, Eq)]
struct MaybeConflict(bool);
/// A conflict has been found
const CONFLICT: MaybeConflict = MaybeConflict(true);
/// No conflict has been found yet
const NO_CONFLICT: MaybeConflict = MaybeConflict(false);

/// Add the clause to the core / schedule it for verification.
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

/// Change the reason flag for some clause.
fn set_reason_flag(checker: &mut Checker, reason: Reason, value: bool) {
    if !reason.is_assumed() {
        let clause = checker.offset2clause(reason.offset());
        checker.fields_mut(clause).set_is_reason(value);
    }
}

/// Add a literal to the trail with a given reason.
///
/// The literal must not be already satisfied.
/// If the literal is falsified, return a conflict.
fn assign(checker: &mut Checker, literal: Literal, reason: Reason) -> MaybeConflict {
    requires!(!checker.assignment[literal]);
    checker.assignment.push(literal, reason);
    if !checker.soft_propagation {
        // This is equivalent to `set_reason_flag(checker, reason, true);` but avoids one indirection.
        invariant!(!reason.is_assumed());
        checker
            .fields_mut_from_offset(reason.offset())
            .set_is_reason(true);
    }
    if checker.assignment[-literal] {
        CONFLICT
    } else {
        NO_CONFLICT
    }
}

/// Perform core-first unit propagation.
///
/// This is heavily inspired by `gratgen`.
///
/// Returns a conflict if it can be found by unit propagation.
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
                    clause_db()[head] = w2;
                    w1 = w2;
                    w2 = literal;
                }
                invariant!(w2 == literal);
                invariant!(checker.assignment[-w2]);
                invariant!(clause_db()[head] == w1);

                if let Some(wo) = first_non_falsified_raw(checker, head + 2) {
                    checker.watchlist_core[literal].swap_remove(i);
                    let w = clause_db()[wo];
                    invariant!(w != literal);
                    watch_add(checker, Mode::Core, w, head);
                    clause_db()[head + 1] = w;
                    clause_db()[wo] = w2;
                    continue;
                }

                clause_db()[head + 1] = w2;

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
                    clause_db()[head] = w2;
                    w1 = w2;
                    w2 = literal;
                }

                invariant!(w2 == literal);
                invariant!(checker.assignment[-w2]);
                invariant!(clause_db()[head] == w1);

                if let Some(wo) = first_non_falsified_raw(checker, head + 2) {
                    checker.watchlist_noncore[literal].swap_remove(i);
                    let w = clause_db()[wo];
                    invariant!(w != literal);
                    watch_add(checker, Mode::NonCore, w, head);
                    clause_db()[head + 1] = w;
                    clause_db()[wo] = w2;
                    continue;
                }

                clause_db()[head + 1] = w2;

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

/// Move a clause from the non-core watchlists to the core ones.
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

/// Record the size of the trail, perform some computation, and truncate
/// the trail to the recorded size.
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

/// Create the list of all resolution candidates for a given pivot literal.
fn collect_resolution_candidates(checker: &Checker, pivot: Literal) -> Vector<Clause> {
    let mut candidates = Vector::new();
    for lit in Literal::all(checker.maxvar) {
        for i in 0..checker.watchlist_core[lit].len() {
            let head = checker.watchlist_core[lit][i];
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

/// Check the current inference.
fn check_inference(checker: &mut Checker) -> bool {
    checker.soft_propagation = true;
    // let ok = match checker.redundancy_property {
    //     RedundancyProperty::RAT => preserve_assignment!(checker, rup_or_rat(checker)),
    //     RedundancyProperty::PR => pr(checker),
    // };
    let ok = preserve_assignment!(checker , rup_or_rat(checker)) ;
    if checker.config.grat_filename.is_some() {
        if !checker.grat_pending_deletions.is_empty() {
            if !checker.grat_in_deletion {
                checker.grat.push(GRATLiteral::DELETION);
            }
            for &clause in &checker.grat_pending_deletions {
                checker.grat.push(GRATLiteral::from_clause(clause));
            }
            checker.grat.push(GRATLiteral::ZERO);
            checker.grat_in_deletion = false;
            checker.grat_pending_deletions.clear();
        }
        if checker.grat_in_deletion {
            checker.grat.push(GRATLiteral::ZERO);
            checker.grat_in_deletion = false;
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

// enum Reduct {
//     Top,
//     Clause(Stack<Literal>),
// }

// fn reduct(
//     checker: &Checker,
//     assignment: &impl Index<Literal, Output = bool>,
//     clause: Clause,
// ) -> Reduct {
//     if checker
//         .clause(clause)
//         .iter()
//         .any(|&literal| assignment[literal])
//     {
//         Reduct::Top
//     } else {
//         Reduct::Clause(
//             checker
//                 .clause(clause)
//                 .iter()
//                 .filter(|&literal| !assignment[-*literal])
//                 .cloned()
//                 .collect(),
//         )
//     }
// }

// fn pr(checker: &mut Checker) -> bool {
//     let lemma = checker.lemma;
//     let mut tmp = Stack::from_vec(checker.clause(lemma).iter().cloned().collect());
//     let lemma_length = tmp.len();
//     for clause in Clause::range(0, lemma) {
//         for offset in checker.witness_range(lemma) {
//             let literal = witness_db()[offset];
//             invariant!(!checker.is_in_witness[literal]);
//             checker.is_in_witness[literal] = true;
//         }
//         // C u D|w is a rup
//         match reduct(checker, &checker.is_in_witness, clause) {
//             Reduct::Top => (),
//             Reduct::Clause(reduct_by_witness) => {
//                 for &literal in &reduct_by_witness {
//                     tmp.push(literal);
//                 }
//                 let ok = preserve_assignment!(checker, slice_rup(checker, &tmp)) == CONFLICT;
//                 tmp.truncate(lemma_length);
//                 if !ok {
//                     return false;
//                 }
//             }
//         }
//         for offset in checker.witness_range(lemma) {
//             let literal = witness_db()[offset];
//             invariant!(checker.is_in_witness[literal]);
//             checker.is_in_witness[literal] = false;
//         }
//     }
//     true
// }

/// Call after finding a conflict during a RUP check.
///
/// Adds the clause that was found to be falsified by the literals in
/// the trail to the GRAT output.
fn add_rup_conflict_for_grat(checker: &mut Checker) {
    requires!(checker.config.grat_filename.is_some());
    let (conflict_literal, conflict_literal_reason) = checker.assignment.peek();
    let reason = if conflict_literal_reason.is_assumed() {
        checker
            .assignment
            .trail_at(checker.assignment.position_in_trail(-conflict_literal))
            .1
    } else {
        conflict_literal_reason
    };
    let reason_clause = checker.offset2clause(reason.offset());
    checker
        .grat_pending
        .push(GRATLiteral::from_clause(reason_clause));
}

/// Return true if the lemma is a RUP or RAT inference.
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
        if checker.config.grat_filename.is_some() {
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
            let pivot = clause_db()[head + pivot_index];
            if checker.config.grat_filename.is_some() {
                checker.grat_rat_counts[pivot] += 1;
            }
            clause_db().swap(head, head + pivot_index);
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
            extract_natural_model(checker, trail_length_after_rup);
            comment!("RAT check failed for {}", checker.clause_to_string(lemma));
            false
        }
    }
}

/// Returns a conflict if the clause is a reverse unit propagation (RUP) inference.
fn rup(checker: &mut Checker, clause: Clause, pivot: Option<Literal>) -> MaybeConflict {
    // NOTE: rupee's lratcheck/sickcheck might require us to first assign all units before
    // returning.
    for offset in checker.clause_range(clause) {
        let unit = clause_db()[offset];
        if pivot.map_or(false, |pivot| unit == -pivot) {
            continue;
        }
        if !checker.assignment[-unit] {
            invariant!(unit != Literal::BOTTOM);
            if assign(checker, -unit, Reason::assumed()) == CONFLICT {
                return CONFLICT;
            }
        }
    }
    propagate(checker)
}

/// Returns a conflict if the clause is a reverse unit propagation (RUP) inference.
fn slice_rup(checker: &mut Checker, clause: &[Literal]) -> MaybeConflict {
    for &unit in clause {
        if !checker.assignment[-unit] {
            if assign(checker, -unit, Reason::assumed()) == CONFLICT {
                return CONFLICT;
            }
        }
    }
    propagate(checker)
}

/// Returns the index of the pivot if the clause is a resolution asymmetric
/// tautology (RAT) inference.
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
        return None;
    }
    let grat_pending_length = checker.grat_pending.len();
    let grat_pending_deletions_length = checker.grat_pending_deletions.len();
    if let Some(witnesses) = checker.rejection.witness.as_mut() {
        witnesses.clear();
    }
    if rat_on_pivot(checker, pivot, trail_length_forced) {
        let pivot_index = checker
            .clause(lemma)
            .iter()
            .position(|&literal| literal == pivot)
            .unwrap();
        return Some(pivot_index);
    }
    if checker.proof_format.rat_first_pivot() {
        return None;
    }
    checker.clause_range(lemma).position(|offset| {
        let fallback_pivot = clause_db()[offset];
        fallback_pivot != Literal::BOTTOM && fallback_pivot != pivot && {
            if checker.config.grat_filename.is_some() {
                checker.grat_pending.truncate(grat_pending_length);
                checker
                    .grat_pending_deletions
                    .truncate(grat_pending_deletions_length);
            }
            rat_on_pivot(checker, fallback_pivot, trail_length_forced)
        }
    })
}

/// Returns true if the clause is a RAT inference on the given pivot.
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

/// Returns true if the clause is a RAT inference on the given pivot with
/// respect to the resolution candidates.
fn rat(
    checker: &mut Checker,
    pivot: Literal,
    resolution_candidates: Vector<Clause>,
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
                    log!(
                        checker,
                        2,
                        "Resolving with {}",
                        checker.clause_to_string(resolution_candidate)
                    );
                    if rup(checker, resolution_candidate, Some(pivot)) == NO_CONFLICT {
                        if checker.config.sick_filename.is_some() {
                            let failing_clause = Vector::from_iter(
                                checker
                                    .clause(resolution_candidate)
                                    .iter()
                                    .filter(|&literal| literal != &Literal::BOTTOM)
                                    .cloned(),
                            );
                            let failing_model = checker
                                .assignment
                                .iter()
                                .skip(trail_length_before_rup)
                                .map(|&(literal, _reason)| literal)
                                .collect();
                            let pivot = Some(pivot);
                            if let Some(witnesses) = checker.rejection.witness.as_mut() {
                                witnesses.push(Witness {
                                    failing_clause,
                                    failing_model,
                                    pivot,
                                })
                            }
                        }
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
                        if checker.config.grat_filename.is_some() {
                            if !resolvent_is_tautological {
                                add_rup_conflict_for_grat(checker);
                            }
                        }
                        true
                    }
                }
        )
    })
}

/// Add the reason clause to the conflict graph.
fn add_to_conflict_graph(checker: &mut Checker, reason: Reason) {
    checker
        .fields_mut_from_offset(reason.offset())
        .set_in_conflict_graph(true);
}
/// Remove the reason clause from the conflict graph.
fn remove_from_conflict_graph(checker: &mut Checker, reason: Reason) {
    checker
        .fields_mut_from_offset(reason.offset())
        .set_in_conflict_graph(false);
}
/// Returns true if the reason clause is in the conflict graph.
fn is_in_conflict_graph(checker: &Checker, reason: Reason) -> bool {
    checker
        .fields_from_offset(reason.offset())
        .in_conflict_graph()
}
/// Adds the reason for the given literal to the conflict graph.
fn add_cause_of_conflict(checker: &mut Checker, literal: Literal) {
    let position = checker.assignment.position_in_trail(literal);
    let reason = checker.assignment.trail_at(position).1;
    if !reason.is_assumed() {
        add_to_conflict_graph(checker, reason);
    }
}

/// Analyze a conflict.
///
/// This adds reasons for the conflict to the core. It performs a depth-first
/// search in the conflict graph to add only a minimal number of clauses.
///
/// The reasons for the conflict are recorded for the LRAT and GRAT outputs if applicable.
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
            let lit = clause_db()[lit_offset];
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
            if let Some((trail_length, _resolvent_is_tautological)) = trail_length_before_rat {
                for position in trail_length..trail_length_before_rup {
                    let (_literal, reason) = checker.assignment.trail_at(position);
                    if reason.is_assumed() || !is_in_conflict_graph(checker, reason) {
                        continue;
                    }
                    let clause = checker.offset2clause(reason.offset());
                    checker.grat_prerat[clause] = true;
                }
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
    if checker.config.lrat_filename.is_some() {
        for position in 1..checker.assignment.len() {
            let (_literal, reason) = checker.assignment.trail_at(position);
            if reason.is_assumed() || !is_in_conflict_graph(checker, reason) {
                continue;
            }
            let clause = checker.offset2clause(reason.offset());
            checker
                .dependencies
                .push(if trail_length_before_rat.is_some() {
                    if position < trail_length_before_rup {
                        LRATDependency::forced_unit(clause)
                    } else {
                        LRATDependency::unit(clause)
                    }
                } else {
                    LRATDependency::unit(clause)
                });
        }
    }
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
        remove_from_conflict_graph(checker, reason);
    }
}

/// Write a line of LRAT (justyfing a single inference.
fn write_dependencies_for_lrat(checker: &mut Checker, clause: Clause, rat_inference: bool) {
    if !checker.config.lrat_filename.is_some() {
        return;
    }
    write_dependencies_for_lrat_aux(checker, clause, rat_inference);
    checker.lrat.push(LRATLiteral::zero());
}

/// Write a line of LRAT (justyfing a single inference (implementation).
fn write_dependencies_for_lrat_aux(checker: &mut Checker, clause: Clause, rat_inference: bool) {
    checker.clause_lrat_offset[clause] = checker.lrat.len();

    if !rat_inference {
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

/// After failing to find a conflict in an inference check, copy the natural
/// model before the check.
fn extract_natural_model(checker: &mut Checker, trail_length: usize) {
    if checker.config.sick_filename.is_some() {
        checker.rejection.natural_model = checker
            .assignment
            .iter()
            .skip(1)
            .take(trail_length - 1)
            .map(|&(literal, _reason)| literal)
            .collect();
    }
}

/// The current phase of double-sweep checking
#[derive(Debug, PartialEq, Eq)]
enum Stage {
    /// Forward pass
    Preprocessing,
    /// Backward pass
    Verification,
}

/// Find the offset of the first non-falsified literal in the clause.
fn first_non_falsified(checker: &Checker, clause: Clause, start: usize) -> Option<usize> {
    (start..checker.clause_range(clause).end).find(|&i| !checker.assignment[-clause_db()[i]])
}

/// Find the offset of the first non-falsified literal in the clause (slightly more efficient).
fn first_non_falsified_raw(checker: &Checker, mut start: usize) -> Option<usize> {
    while !clause_db()[start].is_zero() {
        if !checker.assignment[-clause_db()[start]] {
            return Some(start);
        }
        start += 1;
    }
    None
}

/// The result of searching for two non-falsified literals
enum NonFalsified {
    /// All literals are falsified
    None,
    /// All but one literal are falsified
    One(usize),
    /// There are two non-falsified literals
    Two(usize, usize),
}

/// Find the first two non-falsified literals in the clause.
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

/// Add the clause to the watchlists.
///
/// Assigns the unit literal if the clause is unit.
/// Returns a conflict if the clause is falsified.
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
                assign(checker, clause_db()[head], Reason::forced(head));
                CONFLICT
            }
            Stage::Verification => unreachable(),
        },
        NonFalsified::One(i1) => {
            let w1 = clause_db()[i1];
            if !checker.assignment[w1] {
                let conflict = assign(checker, w1, Reason::forced(head));
                invariant!(conflict == NO_CONFLICT);
            }
            if !checker.config.skip_unit_deletions {
                checker.fields_mut(clause).set_in_watchlist(true);
                clause_db().swap(head, i1);
                watch_add(checker, mode, w1, head);
                watch_add(checker, mode, clause_db()[head + 1], head);
            }
            NO_CONFLICT
        }
        NonFalsified::Two(i1, i2) => {
            let w1 = clause_db()[i1];
            let w2 = clause_db()[i2];
            checker.fields_mut(clause).set_in_watchlist(true);
            clause_db().swap(head, i1);
            clause_db().swap(head + 1, i2);
            watch_add(checker, mode, w1, head);
            watch_add(checker, mode, w2, head);
            NO_CONFLICT
        }
    }
}

/// Returns true if the clause is satisfied.
fn clause_is_satisfied(checker: &Checker, clause: Clause) -> bool {
    checker
        .clause(clause)
        .iter()
        .any(|&literal| checker.assignment[literal])
}

/// Add a clause that is part of the input formula.
///
/// Assigns the unit literal if the clause is unit.
/// Returns a conflict if the clause is falsified.
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
        false
    };
    if already_satisfied {
        checker.satisfied_count += 1;
    } else {
        if watches_add(checker, Stage::Preprocessing, clause) == CONFLICT {
            return CONFLICT;
        }
    }
    propagate(checker)
}

/// Finish the proof at the given step.
///
/// This replaces the instruction at the given step by a RUP inference of
/// the empty clause. This works around some solvers omitting the empty clause
/// in their proofs.
fn close_proof(checker: &mut Checker, steps_until_conflict: usize) -> Verdict {
    checker.proof_steps_until_conflict = steps_until_conflict;
    let empty_clause = checker.lemma;
    clause_db().make_clause_empty(empty_clause);
    invariant!(checker.clause(empty_clause).is_empty());
    invariant!((checker.maxvar == Variable(0)) == (checker.assignment.peek().0 == Literal::TOP));
    let grat_pending_length = checker.grat_pending.len();
    extract_dependencies(checker, checker.assignment.len(), None);
    checker.grat_pending.truncate(grat_pending_length);
    write_dependencies_for_lrat(checker, empty_clause, false);
    schedule(checker, empty_clause);
    checker.proof[checker.proof_steps_until_conflict] = ProofStep::lemma(empty_clause);
    if checker.config.lrat_filename.is_some() {
        checker.optimized_proof.push(ProofStep::lemma(empty_clause));
    }
    if checker.config.grat_filename.is_some() {
        let reason = checker.assignment.pop().unwrap().1;
        // let reason = checker.assignment.peek().1;
        if reason.is_assumed() {
            let empty_clause_in_premise = Clause::range(0, checker.lemma)
                .find(|&clause| checker.clause(clause).is_empty())
                .unwrap();
            schedule(checker, empty_clause_in_premise);
            checker.grat_conflict_clause = empty_clause_in_premise;
        } else {
            checker.grat_conflict_clause = checker.offset2clause(reason.offset());
        }
    }
    Verdict::Verified
}

/// Preprocess the proof (forward pass).
///
/// This propagates after each proof step and returns a conflict as soon
/// as it arises.
fn preprocess(checker: &mut Checker) -> Verdict {
    let _timer = Timer::name("preprocessing proof");
    log!(checker, 1, "[preprocess]");
    defer_log!(checker, 1, "[preprocess] done\n");
    for clause in Clause::range(0, checker.lemma) {
        if checker.clause(clause).is_empty() || add_premise(checker, clause) == CONFLICT {
            return close_proof(checker, 0);
        }
    }
    log!(checker, 1, "[preprocess] done adding premise");
    for i in 0..checker.proof.len() {
        watch_invariants(checker);
        let proof_step = checker.proof[i];
        let clause = proof_step.clause();
        if proof_step.is_deletion() {
            forward_delete(checker, clause);
        } else {
            if !forward_preadd(checker, i, clause) {
                return Verdict::NoConflict;
            }
            checker.lemma += 1;
            if add_premise(checker, clause) == CONFLICT {
                return close_proof(checker, i + 1);
            }
        }
    }
    invariant!({
        let last_step = checker.proof[checker.proof_steps_until_conflict];
        !last_step.is_deletion() && checker.clause(last_step.clause()).is_empty()
    });
    unreachable()
}

/// Check inferences (backward pass).
#[allow(clippy::cyclomatic_complexity)]
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
                    let mut revision = checker.revisions.pop().unwrap();
                    revision_apply(checker, &mut revision);
                }
                watches_add(checker, Stage::Verification, clause);
            }
            if checker.config.grat_filename.is_some() {
                if !checker.grat_in_deletion {
                    checker.grat.push(GRATLiteral::DELETION);
                }
                checker.grat.push(GRATLiteral::from_clause(clause));
                checker.grat_in_deletion = true;
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
            if checker.config.sick_filename.is_some() {
                checker.rejection.proof_step = i;
            }
            return false;
        }
        if checker.config.lrat_filename.is_some() {
            checker.optimized_proof.push(proof_step)
        }
    }
    if checker.config.grat_filename.is_some() {
        if checker.grat_in_deletion {
            checker.grat.push(GRATLiteral::ZERO);
        }
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

/// Undo the propagations that were induced by the given reason clause.
fn unpropagate_unit(checker: &mut Checker, clause: Clause) {
    if !checker.fields(clause).is_reason() {
        return;
    }
    if let Some(offset) = checker
        .clause_range(clause)
        .find(|&offset| checker.assignment[clause_db()[offset]])
    {
        let unit = clause_db()[offset];
        let trail_length = checker.assignment.position_in_trail(unit);
        invariant!(trail_length < checker.assignment.len());
        if checker.config.grat_filename.is_some() {
            if checker.grat_in_deletion {
                checker.grat_in_deletion = false;
                checker.grat.push(GRATLiteral::ZERO);
            }
            checker.grat.push(GRATLiteral::UNIT_PROP);
            for position in trail_length..checker.assignment.len() {
                let reason = checker.assignment.trail_at(position).1;
                let reason_clause = checker.offset2clause(reason.offset());
                if checker.fields(reason_clause).is_scheduled() {
                    checker.grat.push(GRATLiteral::from_clause(reason_clause));
                }
            }
            checker.grat.push(GRATLiteral::ZERO);
        }
        while checker.assignment.len() > trail_length {
            let reason = checker.assignment.pop().unwrap().1;
            set_reason_flag(checker, reason, false);
        }
        checker.processed = trail_length;
    }
}

/// Move falsified literals to the end of the clause.
///
/// After moving them, they will effectively be deleted by being replaced by
/// `Literal::BOTTOM`.  This is done to be compatible with the verified LRAT
/// checker, which does not accept lemmas with falsified literals.
///
/// Equivalent to `sortSize()` in `drat-trim`
fn move_falsified_literals_to_end(checker: &mut Checker, clause: Clause) -> usize {
    let head = checker.clause_range(clause).start;
    let mut effective_end = head;
    if checker.config.sick_filename.is_some() {
        checker.rejection_lemma.clear();
    }
    for offset in checker.clause_range(clause) {
        let literal = clause_db()[offset];
        // The SICK witness would be incorrect when discarding falsified
        // literals like here. Copy the lemma to checker.rejection_lemma.
        if checker.config.sick_filename.is_some() {
            checker.rejection_lemma.push(literal);
        }
        if checker.config.skip_unit_deletions {
            invariant!(!checker.assignment[literal]);
        }
        if !checker.assignment[-literal] {
            // if not falsified
            clause_db()[offset] = clause_db()[effective_end];
            clause_db()[effective_end] = literal;
            effective_end += 1;
        }
    }
    // LRAT lemmas must not contain falsified literals according to the
    // verified checker, delete them.
    for offset in effective_end..checker.clause_range(clause).end {
        clause_db()[offset] = Literal::BOTTOM;
    }
    effective_end - head
}

/// Write core lemmas to a file.
fn write_lemmas(checker: &Checker) -> io::Result<()> {
    let mut file = match &checker.config.lemmas_filename {
        Some(filename) => open_file_for_writing(filename),
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

/// Write the GRAT certificate to a file.
fn write_grat_certificate(checker: &mut Checker) -> io::Result<()> {
    let mut file = match &checker.config.grat_filename {
        Some(filename) => open_file_for_writing(filename),
        None => return Ok(()),
    };
    writeln!(file, "GRATbt {} 0", std::mem::size_of::<Literal>())?; // NB this needs to fit clause IDs
    writeln!(
        file,
        "{} {} 2",
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
            GRATLiteral::DELETION => loop {
                i += 1;
                let grat_clause = checker.grat[i];
                n += 1;
                write!(file, " {}", grat_clause)?;
                if grat_clause == GRATLiteral::ZERO {
                    break;
                }
            },
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

/// Write the LRAT certificate to a file.
fn write_lrat_certificate(checker: &mut Checker) -> io::Result<()> {
    let mut file = match &checker.config.lrat_filename {
        Some(filename) => open_file_for_writing(filename),
        None => return Ok(()),
    };
    let num_clauses = checker.closing_empty_clause().as_offset() + 1;
    let mut clause_deleted = Array::new(false, num_clauses);
    let empty_clause_as_premise =
        Clause::range(0, checker.lemma).any(|clause| checker.clause(clause).is_empty());
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

/// Get the clause's LRAT id.
fn lrat_id(checker: &Checker, clause: Clause) -> Clause {
    checker.clause_lrat_id[clause]
}

/// Write the LRAT line justifying an inference.
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
            invariant!(lrat_id(checker, hint) != Clause::UNINITIALIZED);
            write!(file, "{} ", lrat_id(checker, hint))
        }?;
        i += 1;
    }
    writeln!(file, "0")
}

/// Write an LRAT line of deletions.
fn write_lrat_deletion(
    checker: &Checker,
    file: &mut impl Write,
    clause_deleted: &mut Array<Clause, bool>,
    clause: Clause,
) -> io::Result<()> {
    invariant!(clause != Clause::DOES_NOT_EXIST);
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

/// Write the SICK incorrectness witness to a file.
fn write_sick_witness(checker: &Checker) -> io::Result<()> {
    let mut file = match &checker.config.sick_filename {
        Some(filename) => open_file_for_writing(filename),
        None => return Ok(()),
    };
    // let proof_format = match checker.redundancy_property {
    //     RedundancyProperty::RAT => {
    //         if checker.config.pivot_is_first_literal {
    //             "DRAT-pivot-is-first-literal"
    //         } else {
    //             "DRAT-arbitrary-pivot"
    //         }
    //     }
    //     RedundancyProperty::PR => "PR",
    // };
    let proof_format = checker.proof_format.sick_id() ;
    let proof_step = checker.rejection.proof_step;

    write!(file, "# Failed to prove lemma")?;
    for &literal in &checker.rejection_lemma {
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
    for &literal in &checker.rejection.natural_model {
        write!(file, "{}, ", literal)?;
    }
    writeln!(file, "]")?;
    for witness in checker.rejection.witness.as_ref().unwrap() {
        writeln!(file, "[[witness]]")?;
        write!(file, "failing_clause = [")?;
        for &literal in &witness.failing_clause {
            invariant!(literal != Literal::BOTTOM);
            write!(file, "{}, ", literal)?;
        }
        writeln!(file, "]")?;
        write!(file, "failing_model  = [")?;
        for &literal in &witness.failing_model {
            write!(file, "{}, ", literal)?;
        }
        writeln!(file, "]")?;
        if let Some(pivot) = witness.pivot {
            writeln!(file, "pivot          = {}", pivot)?;
        }
    }
    Ok(())
}

/// Check invariants on the trail (expensive).
fn assignment_invariants(checker: &Checker) {
    if !crate::config::CHECK_TRAIL_INVARIANTS {
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

/// A list of watched clauses, each clause is stored by its offset in the clause database
type Watchlist = Vector<usize>;

/// The mode of a watchlist
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
enum Mode {
    /// Watchlist for core clauses
    Core,
    /// Watchlist for non-core clauses
    NonCore,
}

/// Check watch invariants (expensive).
fn watch_invariants(checker: &Checker) {
    if crate::config::CHECK_WATCH_INVARIANTS {
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

/// Check invariants for some watched clause.
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

/// Returns the watchlist for core or non-core clauses.
fn watchlist(checker: &Checker, mode: Mode) -> &Array<Literal, Watchlist> {
    match mode {
        Mode::Core => &checker.watchlist_core,
        Mode::NonCore => &checker.watchlist_noncore,
    }
}

/// Returns the mutable watchlist for core or non-core clauses.
fn watchlist_mut(checker: &mut Checker, mode: Mode) -> &mut Array<Literal, Watchlist> {
    match mode {
        Mode::Core => &mut checker.watchlist_core,
        Mode::NonCore => &mut checker.watchlist_noncore,
    }
}

/// Remove an entry in a watchlist.
fn watch_remove_at(checker: &mut Checker, mode: Mode, lit: Literal, position_in_watchlist: usize) {
    watchlist_mut(checker, mode)[lit].swap_remove(position_in_watchlist);
}

/// Add an etnry to a watchlist.
fn watch_add(checker: &mut Checker, mode: Mode, lit: Literal, head: usize) {
    watchlist_mut(checker, mode)[lit].push(head)
}

/// Remove the watchlist entries for a clause.
fn watches_remove(checker: &mut Checker, mode: Mode, clause: Clause) {
    let head = checker.clause_range(clause).start;
    let [w1, w2] = checker.watches(head);
    watches_find_and_remove(checker, mode, w1, head);
    watches_find_and_remove(checker, mode, w2, head);
    checker.fields_mut(clause).set_in_watchlist(false);
}

/// Remove the entries for a clause in the watchlist of a literal.
fn watches_find_and_remove(checker: &mut Checker, mode: Mode, lit: Literal, head: usize) -> bool {
    requires!(lit != Literal::TOP);
    if crate::config::CHECK_WATCH_INVARIANTS {
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
    }
    watchlist(checker, mode)[lit]
        .iter()
        .position(|&watched| watched == head)
        .map(|position| watch_remove_at(checker, mode, lit, position))
        .is_some()
}

// Revisions

/// Returns true if the literal was unassigned after reason deletion.
fn is_in_cone(checker: &Checker, literal: Literal, reason: Reason) -> bool {
    invariant!(!reason.is_assumed());
    checker
        .clause(checker.offset2clause(reason.offset()))
        .iter()
        .any(|&lit| lit != literal && checker.literal_is_in_cone_preprocess[-lit])
}

/// Create a revision after a reason deletion in the forward pass.
fn revision_create(checker: &mut Checker, clause: Clause) {
    assignment_invariants(checker);
    watch_invariants(checker);
    log!(checker, 2, "{}", checker.assignment);
    let unit = *checker
        .clause(clause)
        .iter()
        .find(|&lit| checker.assignment[*lit])
        .unwrap();
    let unit_position = checker.assignment.position_in_trail(unit);
    let unit_reason = checker.assignment.trail_at(unit_position).1;
    checker.fields_mut(clause).set_has_revision(true);
    let mut revision = Revision {
        cone: Vector::new(),
        position_in_trail: Vector::new(),
        reason_clause: Vector::new(),
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
    checker.assignment.resize(length_after_removing_cone);
    checker.processed = length_after_removing_cone;
    for &literal in &revision.cone {
        watchlist_revise(checker, literal);
    }
    for &literal in &revision.cone {
        invariant!(checker.literal_is_in_cone_preprocess[literal]);
        checker.literal_is_in_cone_preprocess[literal] = false;
    }
    if !checker.config.forward {
        checker.revisions.push(revision);
    }
    assignment_invariants(checker);
}

/// Fix watchlist of a literal that were unassigned after a reason deletion.
fn watchlist_revise(checker: &mut Checker, lit: Literal) {
    for &mode in &[Mode::Core, Mode::NonCore] {
        let mut i = 0;
        while i < watchlist(checker, mode)[lit].len() {
            let head = watchlist(checker, mode)[lit][i];
            let clause = checker.offset2clause(head);
            watches_revise(checker, mode, lit, clause);
            i += 1;
        }
    }
}

/// Fix the watches of some clause whose watch was unassigned after a reason deletion.
fn watches_revise(checker: &mut Checker, mode: Mode, lit: Literal, clause: Clause) {
    let head = checker.clause_range(clause).start;
    if clause_db()[head] == lit {
        clause_db().swap(head, head + 1);
    }
    let other_literal = clause_db()[head];
    if !checker.assignment[-other_literal] {
        return;
    }
    // Remember Invariant 1: one falsified watch implies that the other watch is satisfied.
    match first_non_falsified(checker, clause, head + 2) {
        None => {
            if !checker.assignment[lit] {
                assign(checker, lit, Reason::forced(head));
            }
        }
        Some(offset) => {
            let new_literal = clause_db()[offset];
            clause_db().swap(head, offset);
            let _removed = watches_find_and_remove(checker, mode, other_literal, head);
            watch_add(checker, mode, new_literal, head);
        }
    };
}

/// Add some, just unassigned literal to the revision.
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
    set_reason_flag(checker, reason, false);
}

/// Apply a revision in the backward pass.
///
/// This restores the trail to be like before
/// [revision_create](fn.revision_create.html) was called.
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
    // overwriting the latter part of the vector. For this we need a different
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
    log!(checker, 1, "applying {}", revision);
    log!(checker, 2, "{}", checker.assignment);
    let length_after_adding_cone = checker.assignment.len() + introductions;
    let mut right_position = length_after_adding_cone - 1;
    let mut left_position = right_position - literals_to_revise + 1;
    checker.assignment.resize(length_after_adding_cone);
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
    log!(checker, 2, "applied revision:\n{}", checker.assignment);
    watches_reset(checker, revision);
    assignment_invariants(checker);
}

/// Reshuffle affected watches after applying a revision.
fn watches_reset(checker: &mut Checker, revision: &Revision) {
    for &literal in &revision.cone {
        watches_reset_list(checker, literal);
        watches_reset_list(checker, -literal);
    }
}

/// Reshuffle the clauses in the given watchlist after applying a revision.
fn watches_reset_list(checker: &mut Checker, literal: Literal) {
    for &mode in &[Mode::Core, Mode::NonCore] {
        let mut i = 0;
        while i < watchlist(checker, mode)[literal].len() {
            watches_reset_list_at(checker, mode, literal, &mut i);
            i = i.wrapping_add(1);
        }
    }
}

/// Reshuffle the clause to restore watch invariants.
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
    if literal != w1 {
        requires!(literal == w2);
        clause_db().swap(head, head + 1);
    }
    let [w1, w2] = checker.watches(head);
    let offset = head;
    let mut new_w1_offset = head;
    let mut latest_falsified_offset = head;
    let mut latest_falsified_position = 0;
    let have_unassigned = find_nonfalsified_and_most_recently_falsified(
        checker,
        clause,
        &mut new_w1_offset,
        &mut latest_falsified_offset,
        &mut latest_falsified_position,
    );
    invariant!(have_unassigned, "broken invariant");
    let mut new_w2_offset = new_w1_offset + 1;
    let have_unassigned = find_nonfalsified_and_most_recently_falsified(
        checker,
        clause,
        &mut new_w2_offset,
        &mut latest_falsified_offset,
        &mut latest_falsified_position,
    );
    if !have_unassigned {
        requires!(checker.assignment[clause_db()[new_w1_offset]]);
        if new_w1_offset > latest_falsified_offset {
            new_w2_offset = new_w1_offset;
            new_w1_offset = latest_falsified_offset;
        } else {
            new_w2_offset = latest_falsified_offset;
        }
    }
    // At this point, we have ensured that new_w1_offset < new_w2_offset
    // There are four cases:
    //   A) new_w1_offset 0, new_w2_offset is 1
    //   B) new_w1_offset 0, new_w2_offset is >=2
    //   C) new_w1_offset 1, new_w2_offset is >=2
    //   D) both new_w1_offset and new_w2_offset are >=2
    if offset == new_w1_offset {
        if offset + 1 == new_w2_offset {
            // Case A: nothing to do!
            return;
        } else {
            // Case B: clause will not be watched on w2, but on clause_db()[new_w2_offset] instead.
            let _removed = watches_find_and_remove(checker, mode, w2, head);
            clause_db().swap(offset + 1, new_w2_offset);
            watch_add(checker, mode, clause_db()[offset + 1], head);
        }
    } else {
        // Cases C and D: clause will not be watched on w1, but on *new_w2_offset instead.
        watch_remove_at(checker, mode, w1, *position_in_watchlist);
        *position_in_watchlist = position_in_watchlist.wrapping_sub(1);
        clause_db().swap(offset, new_w2_offset);
        watch_add(checker, mode, clause_db()[offset], head); // Case C: additionally, clause will still be watched on w2
        if offset + 1 != new_w1_offset {
            // Case D: additionally, clause will not be watched on w2, but on clause_db()[offset + 1] instead.
            let _removed = watches_find_and_remove(checker, mode, w2, head);
            clause_db().swap(offset + 1, new_w1_offset);
            watch_add(checker, mode, clause_db()[offset + 1], head);
        }
    }
}

/// Scans a clause to find a non-falsified, or the most recently falsified literal.
///
/// Returns as soon as a non-falsified literal is found. Its location in
/// the clause database is stored in `offset`.
///
/// The location and position in trail of the most recently falsified is stored
/// in `latest_falsified_offset` and `latest_falsified_position` respectively.
fn find_nonfalsified_and_most_recently_falsified<'a>(
    checker: &Checker,
    clause: Clause,
    offset: &'a mut usize,
    latest_falsified_offset: &'a mut usize,
    latest_falsified_position: &'a mut usize,
) -> bool {
    let end = checker.clause_range(clause).end;
    while *offset < end {
        let literal = clause_db()[*offset];
        if checker.assignment[-literal] {
            let position_in_trail = checker.assignment.position_in_trail(-literal);
            if position_in_trail >= *latest_falsified_position {
                *latest_falsified_position = position_in_trail;
                *latest_falsified_offset = *offset;
            }
            *offset += 1;
        } else {
            return true;
        }
    }
    false
}

/// Print memory usage statistics (after checking)
fn print_memory_usage(checker: &Checker) {
    macro_rules! heap_space {
        ($($x:expr,)*) => (vec!($(($x).heap_space()),*));
    }
    let usages = vec![
        ("db", clause_db().heap_space()),
        ("proof", checker.proof.heap_space()),
        ("optimized_proof", checker.optimized_proof.heap_space()),
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
    let total = usages.iter().fold(0, |sum, pair| sum + pair.1);
    output::value("memory (MB)", format_memory_usage(total));
    if !checker.config.memory_usage_breakdown {
        return;
    }
    for pair in usages {
        output::value(
            &format!("memory-{}", pair.0.replace("_", "-")),
            format_memory_usage(pair.1),
        );
    }
}
