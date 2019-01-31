use crate::{
    checker::{assign, first_non_falsified, set_reason_flag, Checker, Reason, Revision},
    clause::Clause,
    config::unreachable,
    literal::Literal,
    memory::{Array, Stack},
};

pub type Watchlist = Stack<Clause>;

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
                for &clause in &watchlist(checker, mode)[lit] {
                    watch_invariant(checker, lit, clause);
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
    log!(
        checker,
        3,
        "watchlist[{}] del [{}]: {}",
        lit,
        position_in_watchlist,
        watchlist(checker, mode)[lit][position_in_watchlist]
    );
    watchlist_mut(checker, mode)[lit].swap_remove(position_in_watchlist);
}

pub fn watch_add(checker: &mut Checker, mode: Mode, lit: Literal, clause: Clause) {
    log!(checker, 3, "watchlist[{}] add {}", lit, clause);
    watchlist_mut(checker, mode)[lit].push(clause)
}

pub fn watches_remove(checker: &mut Checker, mode: Mode, clause: Clause) {
    log!(
        checker,
        2,
        "removing watches for {}",
        checker.clause_copy(clause)
    );
    let (w1, w2) = checker.clause_watches(clause);
    watches_find_and_remove(checker, mode, w1, clause);
    watches_find_and_remove(checker, mode, w2, clause);
    checker.clause_in_watchlist[clause] = false;
}

pub fn watches_find_and_remove(
    checker: &mut Checker,
    mode: Mode,
    lit: Literal,
    clause: Clause,
) -> bool {
    requires!(lit != Literal::TOP);
    invariant!(
        watchlist(checker, mode)[lit]
            .iter()
            .filter(|&c| *c == clause)
            .count()
            <= 1,
        "duplicate clause {} in watchlist of {}",
        checker.clause_copy(clause),
        lit
    );
    watchlist(checker, mode)[lit]
        .iter()
        .position(|&watched| watched == clause)
        .map(|position| watch_remove_at(checker, mode, lit, position))
        .is_some()
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
        cone: Stack::new(),
        position_in_trace: Stack::new(),
        reason_clause: Stack::new(),
    };
    add_to_revision(checker, &mut revision, unit);
    let mut next_position_to_overwrite = unit_position;
    for position in unit_position + 1..checker.assignment.len() {
        let lit = checker.assignment.trace_at(position);
        if is_in_cone(checker, lit) {
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
    for &literal in &revision.cone {
        invariant!(checker.literal_is_in_cone[literal]);
        checker.literal_is_in_cone[literal] = false;
    }
    checker.revisions.push(revision);
}

fn watchlist_revise(checker: &mut Checker, lit: Literal) {
    for &mode in &[Mode::Core, Mode::NonCore] {
        let mut i = 0;
        while i < watchlist(checker, mode)[lit].len() {
            let clause = watchlist(checker, mode)[lit][i];
            watches_revise(checker, mode, lit, clause, &mut i);
            i = i.wrapping_add(1);
        }
    }
}

pub fn watches_revise(
    checker: &mut Checker,
    mode: Mode,
    lit: Literal,
    clause: Clause,
    position_in_watchlist: &mut usize,
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
            watch_remove_at(checker, mode, lit, *position_in_watchlist);
            *position_in_watchlist = position_in_watchlist.wrapping_sub(1);
            invariant!(mode == checker.clause_mode(clause));
            watch_add(checker, mode, new_literal, clause);
        }
    };
}

fn add_to_revision(checker: &mut Checker, revision: &mut Revision, lit: Literal) {
    checker.assignment.unassign(lit);
    checker.literal_minimal_lifetime[lit] = 0;
    set_reason_flag(checker, lit, false);
    revision.cone.push(lit);
    checker.literal_is_in_cone[lit] = true;
    revision
        .position_in_trace
        .push(checker.assignment.position_in_trace(lit));
    match checker.literal_reason[lit] {
        Reason::Assumed => unreachable(),
        Reason::Forced(clause) => revision.reason_clause.push(clause),
    }
}

fn is_in_cone(checker: &Checker, literal: Literal) -> bool {
    match checker.literal_reason[literal] {
        Reason::Assumed => unreachable(),
        Reason::Forced(clause) => checker
            .clause(clause)
            .iter()
            .any(|&lit| lit != literal && checker.literal_is_in_cone[-lit]),
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
            literal = revision.cone[literals_to_revise];
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
    let clause = watchlist(checker, mode)[literal][*position_in_watchlist];
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
            offset == second_offset
        {
            // Case A: nothing to do!
            return;
        } else {
            // Case B: clause will not be watched on other_lit, but on checker.db[second_offset] instead.
            let removed = watches_find_and_remove(checker, mode, other_lit, clause);
            invariant!(removed);
            let tmp = checker.db[second_offset];
            checker.db[offset + 1] = tmp;
            checker.db[second_offset] = other_lit;
            watch_add(checker, mode, tmp, clause);
        }
    } else {
        // Cases C and D: clause will not be watched on literal, but on *second_offset instead.
        watch_remove_at(checker, mode, literal, *position_in_watchlist);
        *position_in_watchlist = position_in_watchlist.wrapping_sub(1);
        checker.db[offset] = checker.db[second_offset];
        checker.db[second_offset] = literal;
        watch_add(checker, mode, checker.db[offset], clause); // Case C: additionally, clause will still be watched on other_lit
        if offset + 1 != first_offset {
            // Case D: additionally, clause will not be watched on other_lit, but on checker.db[offset + 1] instead.
            let removed = watches_find_and_remove(checker, mode, other_lit, clause);
            invariant!(removed);
            checker.db[offset + 1] = checker.db[first_offset];
            checker.db[first_offset] = other_lit;
            watch_add(checker, mode, checker.db[offset + 1], clause);
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
