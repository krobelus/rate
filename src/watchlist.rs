use crate::{
    checker::{
        assign, first_non_falsified, set_reason_flag, Checker, MaybeConflict, Reason, Revision,
        CONFLICT, NO_CONFLICT,
    },
    clause::Clause,
    config::unreachable,
    literal::Literal,
    memory::{Array, Offset, Stack, StackMapping},
};

pub type Watchlist = Stack<Option<Clause>>;

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Mode {
    Core,
    NonCore,
}

fn is_assigned(checker: &Checker, lit: Literal) -> bool {
    checker.assignment[lit] || checker.assignment[-lit]
}

pub fn watch_invariants(checker: &Checker) {
    if crate::config::COSTLY_INVARIANT_CHECKING {
        // each watch points to a clause that is neither falsified nor satisfied
        for &mode in &[Mode::Core, Mode::NonCore] {
            for lit in Literal::all(checker.maxvar) {
                for watch in &watchlist(checker, mode)[lit] {
                    if let &Some(clause) = watch {
                        watch_invariant(checker, lit, clause);
                    }
                }
            }
        }
    }
}

pub fn watch_invariant(checker: &Checker, lit: Literal, clause: Clause) {
    let (w1, w2) = checker.clause_watches(clause);
    invariant!(
        lit == w1 || lit == w2,
        "watch {} not within the first two literals in {}",
        lit,
        checker.clause_copy(clause)
    );
    invariant!(
        is_assigned(checker, w1)
            || is_assigned(checker, w2)
            || (!is_assigned(checker, -w1) && !is_assigned(checker, -w2)),
        format!(
            "each watched clause needs at least one unassigned literal: violated in {} - {}",
            checker.clause_copy(clause),
            checker.assignment
        )
    );
}

pub fn watchlist(checker: &Checker, mode: Mode) -> &Array<Literal, Watchlist> {
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

pub fn watch_remove_at(
    checker: &mut Checker,
    mode: Mode,
    lit: Literal,
    position_in_watchlist: usize,
) {
    requires!(watchlist(checker, mode)[lit][position_in_watchlist].is_some());
    log!(
        checker,
        3,
        "watchlist[{}] del [{}]: {}",
        lit,
        position_in_watchlist,
        watchlist(checker, mode)[lit][position_in_watchlist].unwrap()
    );
    watchlist_mut(checker, mode)[lit][position_in_watchlist] = None
}

pub fn watch_add(checker: &mut Checker, mode: Mode, lit: Literal, clause: Clause) {
    log!(checker, 3, "watchlist[{}] add {}", lit, clause);
    watchlist_mut(checker, mode)[lit].push(Some(clause))
}

pub fn watches_add(checker: &mut Checker, mode: Mode, clause: Clause) -> MaybeConflict {
    log!(
        checker,
        2,
        "initializing watches for {}",
        checker.clause_copy(clause)
    );
    let size = checker.clause(clause).len();
    invariant!(size >= 2);
    let head = checker.clause_range(clause).start;
    match first_non_falsified(&checker, clause, head) {
        Some(i0) => {
            let w1 = checker.db[i0];
            checker.db.as_mut_slice().swap(head, i0);
            watch_add(checker, mode, w1, clause);
            let w2 = match first_non_falsified(checker, clause, head + 1) {
                Some(i1) => {
                    let w2 = checker.db[i1];
                    checker.db.as_mut_slice().swap(head + 1, i1);
                    w2
                }
                None => {
                    if !checker.assignment[w1] {
                        let result = assign(checker, w1, Reason::Forced(clause));
                        invariant!(result == NO_CONFLICT);
                    }
                    checker.db[head + 1]
                }
            };
            watch_add(checker, mode, w2, clause);
            checker.clause_in_watchlist[clause] = true;
            NO_CONFLICT
        }
        None => {
            // TODO does this only happen for real units
            assign(checker, checker.db[head], Reason::Forced(clause));
            CONFLICT
        }
    }
}

pub fn watches_remove(checker: &mut Checker, mode: Mode, clause: Clause) {
    log!(
        checker,
        2,
        "removing watches for {}",
        checker.clause_copy(clause)
    );
    let (w1, w2) = checker.clause_watches(clause);
    watches_find_and_remove_all(checker, mode, w1, clause);
    watches_find_and_remove_all(checker, mode, w2, clause);
    checker.clause_in_watchlist[clause] = false;
}

pub fn watches_find_and_remove_all(
    checker: &mut Checker,
    mode: Mode,
    lit: Literal,
    clause: Clause,
) {
    for i in 0..watchlist(checker, mode)[lit].len() {
        if watchlist(checker, mode)[lit][i] == Some(clause) {
            watch_remove_at(checker, mode, lit, i);
        }
    }
}

pub fn watchlist_compact(checker: &mut Checker, mode: Mode, lit: Literal) {
    let mut i = 0;
    while i < watchlist(checker, mode)[-lit].len() {
        if watchlist(checker, mode)[-lit][i].is_none() {
            watchlist_mut(checker, mode)[-lit].swap_remove(i);
        } else {
            i += 1;
        }
    }
}

// Revisions

pub fn revision_create(checker: &mut Checker, clause: Clause) {
    log!(checker, 1, "{}", checker.assignment);
    let unit = *checker
        .clause(clause)
        .iter()
        .find(|&lit| checker.assignment[*lit])
        .unwrap();
    let unit_position = checker.assignment.position_in_trace(unit);
    checker.lemma_revision[clause] = true;
    let mut revision = Revision {
        cone: StackMapping::with_array_value_size_stack_size(
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
    checker.processed = next_position_to_overwrite;
    for &literal in &revision.cone {
        watchlist_revise(checker, literal);
    }
    log!(checker, 1, "Created {}\n{}", revision, checker.assignment);
    checker.revisions.push(revision);
}

fn watchlist_revise(checker: &mut Checker, lit: Literal) {
    for &mode in &[Mode::Core, Mode::NonCore] {
        (0..watchlist(checker, mode)[lit].len()).for_each(|i| {
            if let Some(clause) = watchlist(checker, mode)[lit][i] {
                watches_revise(checker, mode, lit, clause, i)
            }
        });
        watchlist_compact(checker, mode, lit);
    }
}

pub fn watches_revise(
    checker: &mut Checker,
    mode: Mode,
    lit: Literal,
    clause: Clause,
    position_in_watchlist: usize,
) {
    // NOTE swap them to simplify this
    let (w1, _w2) = checker.clause_watches(clause);
    let head = checker.clause_range(clause).start;
    let my_offset = head + if w1 == lit { 0 } else { 1 };
    let other_literal_offset = head + if w1 == lit { 1 } else { 0 };
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
            watch_remove_at(checker, mode, lit, position_in_watchlist);
            invariant!(mode == checker.clause_mode(clause));
            watch_add(checker, mode, new_literal, clause);
        }
    };
}

fn add_to_revision(checker: &mut Checker, revision: &mut Revision, lit: Literal) {
    checker.assignment.unassign(lit);
    set_reason_flag(checker, lit, false);
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

pub fn revision_apply(checker: &mut Checker, revision: &mut Revision) {
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
    checker.processed = right_position;
    // Re-introduce the assignments that were induce by the deleted unit,
    // starting from the ones with the highest offset in the trace.
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
    watches_reset(checker, revision);
}

fn watches_reset(checker: &mut Checker, revision: &Revision) {
    for &literal in &revision.cone {
        watches_reset_list(checker, literal);
        watches_reset_list(checker, -literal);
    }
}

fn watches_reset_list(checker: &mut Checker, literal: Literal) {
    checker.watch_reset_list_count += 1;
    for &mode in &[Mode::Core, Mode::NonCore] {
        for i in 0..watchlist(checker, mode)[literal].len() {
            if watchlist(checker, mode)[literal][i].is_some() {
                checker.watch_reset_count += 1;
                watches_reset_list_at(checker, mode, literal, i);
            }
        }
    }
}

fn watches_reset_list_at(
    checker: &mut Checker,
    mode: Mode,
    literal: Literal,
    position_in_watchlist: usize,
) {
    let clause = watchlist(checker, mode)[literal][position_in_watchlist]
        .expect("can't reset - watch was deleted");
    let (w1, w2) = checker.clause_watches(clause);
    if !checker.assignment[-w1] && !checker.assignment[-w2] {
        // watches are correct
        return;
    }
    let head = checker.clause_range(clause).start;
    if literal != w1 {
        requires!(literal == w2);
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
        if offset + 1 == second_offset ||
            // TODO why
            offset == second_offset {
            // Case A: nothing to do!
            return;
        } else {
            // Case B: clause will not be watched on other_lit, but on checker.db[second_offset] instead.
            watches_find_and_remove(checker, mode, other_lit, clause);
            let tmp = checker.db[second_offset];
            checker.db[offset + 1] = tmp;
            checker.db[second_offset] = other_lit;
            watch_add(checker, mode, tmp, clause);
        }
    } else {
        // Cases C and D: clause will not be watched on literal, but on *second_offset instead.
        watch_remove_at(checker, mode, literal, position_in_watchlist);
        checker.db[offset] = checker.db[second_offset];
        checker.db[second_offset] = literal;
        watch_add(checker, mode, checker.db[offset], clause); // Case C: additionally, clause will still be watched on other_lit
        if offset + 1 != first_offset {
            // Case D: additionally, clause will not be watched on other_lit, but on checker.db[offset + 1] instead.
            watches_find_and_remove(checker, mode, other_lit, clause);
            checker.db[offset + 1] = checker.db[first_offset];
            checker.db[first_offset] = other_lit;
            watch_add(checker, mode, checker.db[offset + 1], clause);
        }
    }
}

pub fn watches_find_and_remove(checker: &mut Checker, mode: Mode, lit: Literal, clause: Clause) {
    requires!(lit != Literal::TOP);
    watchlist(checker, mode)[lit]
        .iter()
        .position(|&watched| watched == Some(clause))
        .map(|position| watch_remove_at(checker, mode, lit, position));
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
