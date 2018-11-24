/*
 * Reimplementation of Rate in plain C.
 */

#include <assert.h>
#include <ctype.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef int32_t Lit;
typedef int bool;
typedef int ClauseStatus;
typedef uint32_t Clause;
typedef uint32_t uint;

static bool *map, tracep;
static uint maxvar, proofstart, propcount, ratcalls, rupcalls;
static const ClauseStatus SATISFIED = -1, FALSIFIED = -2, UNKNOWN = -3;

#define trace(...)                   \
  do {                               \
    if (tracep) printf(__VA_ARGS__); \
  } while (0)
#define echo(...) printf(__VA_ARGS__)
#define NEW(p) (p) = malloc(p##s * sizeof(*p))
#define PUSH_NO_GROW(p, x) p[p##c++] = x;
#define PUSH(p, x)                       \
  do {                                   \
    if (p##c == p##s) {                  \
      p##s *= 2;                         \
      p = realloc(p, p##s * sizeof(*p)); \
    }                                    \
    PUSH_NO_GROW(p, x)                   \
  } while (0)
#define FOR(i, p) for (uint i = 0; i < p##c; i++)
#define FOR_FORMULA(i) for (uint i = 0, end = proofstart; i < end; i++)
#define FOR_FORMULA_AND_PROOF(i) for (uint i = 0; i < clauseheadc; i++)
#define FOR_CLAUSE(i, c)   \
  assert(clauseactive[c]); \
  for (Lit *i = db + clausehead[c]; *i; i++)
#define STACK_PRINT(p)                \
  do {                                \
    trace(#p "[%ld] :", p##c);        \
    FOR(i, p) { trace(" %d", p[i]); } \
    trace("\n");                      \
  } while (0)
#define CLAUSE_PRINT(c)                      \
  do {                                       \
    FOR_CLAUSE(_i, c) { trace("%d ", *_i); } \
    trace("0\n");                            \
  } while (0)

struct lemma {
  Clause clause : 31;
  unsigned int deletion : 1;
};
#define ADDITION(c) \
  { (c), 0 }
#define DELETION(c) \
  { (c), 1 }
#define STACK_INITIAL_SIZE 32
#define STACK(p, T) \
  static T *p;      \
  static long p##c, p##s = STACK_INITIAL_SIZE;
#include "crate-stacks.h"

static void print() {
#define STACK(p, _) STACK_PRINT(p);
#include "crate-stacks.h"
  trace("proof [%ld/%ld] :", proofc, proofs);
  FOR(i, proof) { trace(" %d[%d]", proof[i].clause, proof[i].deletion); }
  trace("\n");
}

static bool inbuffer(Lit literal) {
  FOR(i, buffer) {
    if (buffer[i] == literal) return 1;
  }
  return 0;
}

static ClauseStatus find() {
  FOR(i, clausehead) {
    Lit *it, *head = db + clausehead[i];
    bool found = 1;
    for (it = head; *it; it++) {
      found = found && inbuffer(*it);
    }
    found = found && (it - head) == bufferc;
    if (found) return i;
  }
  return -1;
}

#define MAX(a, b) ((a) > (b) ? (a) : (b))
#define VAR(var)               \
  do {                         \
    assert(var >= 0);          \
    maxvar = MAX(maxvar, var); \
  } while (0)

static void parse(const char *file, bool isproof) {
  FILE *f = fopen(file, "r");
  if (!f) {
    fprintf(stderr, "error: failed to open file: %s\n", file);
    exit(1);
  }
  int c, state = isproof ? 3 : 0, lit = 0, sign = 0, ishead = 1;
  while ((c = fgetc(f)) != EOF) {
    switch (state) {
      case 0:
        if (c == 'c')
          state = 1;
        else {
          assert(c == 'p');
          state = 2;
        }
        break;
      case 1:
        state = c != '\n';
        break;
      case 2:
        state = c == '\n' ? 3 : 2;
        break;
      case 3:
        if (c == 'd')
          state = 5;
        else if (isspace(c))
          ;
        else {
          if (ishead) {
            if (isproof) {
              struct lemma addition = ADDITION(clauseheadc);
              PUSH(proof, addition);
            }
            PUSH(clausehead, dbc);
          }
          sign = c == '-' ? -1 : 1;
          lit = isdigit(c) ? (c - '0') : 0;
          state = 4;
        }
        break;
      case 4:
        if (isdigit(c))
          lit = 10 * lit + (c - '0');
        else {
          VAR(lit);
          PUSH(db, sign * lit);
          ishead = !lit;
          state = 3;
        }
        break;
      case 5:
        assert(isspace(c));
        assert(c == ' ');
        state = 6;
        break;
      case 6:
        if (isspace(c))
          ;
        else {
          sign = c == '-' ? -1 : 1;
          lit = isdigit(c) ? (c - '0') : 0;
          state = 7;
        }
        break;
      case 7:
        if (isdigit(c))
          lit = 10 * lit + (c - '0');
        else {
          if (lit) {
            VAR(lit);
            PUSH(buffer, sign * lit);
            state = 6;
          } else {
            int clause = find();
            if (clause == -1) {
            } else {
              struct lemma deletion = DELETION(clause);
              PUSH(proof, deletion);
            }
            bufferc = 0;
            state = 3;
          }
        }
        break;
    };
  }
  switch (state) {
    case 4:
      VAR(lit);
      PUSH(db, sign * lit);
      ishead = !lit;
      state = 3;
      break;
    case 7:
      if (lit) {
        VAR(lit);
        PUSH(buffer, sign * lit);
        state = 6;
      } else {
        struct lemma deletion = DELETION(find());
        PUSH(proof, deletion);
        bufferc = 0;
        state = 3;
      }
      break;
    default:
      break;
  }
  if (!isproof) proofstart = clauseheadc;
  fclose(f);
}

static bool member(Lit literal, Clause c) {
  FOR_CLAUSE(lit, c) {
    if (*lit == literal) return 1;
  }
  return 0;
}

static void reset_assignment() {
  FOR(i, assignment) { map[assignment[i]] = 0; }
  assignmentc = 0;
}

static ClauseStatus clause_status(Clause c) {
  Lit *unit, unitc = 0;
  FOR_CLAUSE(lit, c) {
    if (map[*lit]) return SATISFIED;
    if (map[-*lit]) continue;
    unit = lit;
    unitc++;
  }
  switch (unitc) {
    case 0:
      return FALSIFIED;
    case 1:
      return unit - (db + clausehead[c]);
    default:
      return UNKNOWN;
  }
}

static bool propagate(Lit literal) {
  propcount++;
  trace("prop %d\n", literal);
  STACK_PRINT(assignment);
  if (map[-literal]) return 1;
  if (map[literal]) return 0;
  map[literal] = 1;
  PUSH_NO_GROW(assignment, literal);
  FOR_FORMULA(c) {
    if (!clauseactive[c]) continue;
    ClauseStatus status = clause_status(c);
    if (status == FALSIFIED) return 1;
    if (status >= 0) {
      if (propagate(db[clausehead[c] + status])) return 1;
    }
  }
  return 0;
}

static bool propagate_existing_units() {
  trace("propagate existing\n");
  FOR_FORMULA(c) {
    if (!clauseactive[c]) continue;
    ClauseStatus status = clause_status(c);
    if (status == FALSIFIED) return 1;
    if (status >= 0)
      if (propagate(db[clausehead[c] + status])) return 1;
  }
  return 0;
}

static bool is_rat_on(Lit pivot, Clause c, Clause d) {
  trace("is_rat_on(%d, %d) - ", c, d);
  CLAUSE_PRINT(d);
  reset_assignment();
  if (propagate_existing_units()) return 1;
  FOR_CLAUSE(lit, c) {
    if (propagate(-*lit)) return 1;
  }
  FOR_CLAUSE(lit, d) {
    if (*lit == -pivot) continue;
    if (propagate(-*lit)) return 1;
  }
  return 0;
}

static bool rat(Clause c) {
  trace("rat(%d) - ", c);
  CLAUSE_PRINT(c);
  ratcalls++;
  Lit *lit = db + clausehead[c];
  Lit pivot = *lit;
  if (!(pivot = *lit)) return 0;
  FOR_FORMULA(d) {
    if (!clauseactive[d]) continue;
    if (!member(-pivot, d)) continue;
    if (!is_rat_on(pivot, c, d)) return 0;
  }
  return 1;
}

static bool rup(Clause c) {
  trace("rup(%d) - ", c);
  CLAUSE_PRINT(c);
  rupcalls++;
  reset_assignment();
  if (propagate_existing_units()) return 1;
  trace("propagating reverse clause\n");
  FOR_CLAUSE(lit, c) {
    if (propagate(-*lit)) return 1;
  }
  return 0;
}

static bool check() {
  FOR(i, proof) {
    Clause c = proof[i].clause;
    if (proof[i].deletion) {
      clauseactive[proof[i].clause] = 0;
    } else {
      if (!rup(c) && !rat(c)) return 0;
      proofstart++;
      trace("proofstart: %ld\n", proofstart);
    }
  }
  reset_assignment();
  return propagate_existing_units();
}

int main(int argc, char *argv[]) {
#define STACK(p, _) NEW(p);
#include "crate-stacks.h"
  parse(argv[1], 0);
  parse(argv[2], 1);
  for (int i = 3; i < argc; i++) {
    tracep |= (strcmp(argv[i], "-t") == 0 || strcmp(argv[i], "--trace") == 0);
  }
  clauseactives = clauseheadc;
  NEW(clauseactive);
  assignments = maxvar;
  NEW(assignment);
  FOR_FORMULA_AND_PROOF(i) { clauseactive[i] = 1; }
  map = calloc(2 * (maxvar + 2), sizeof(*map));
  map += maxvar + 1;
  trace("proof_start: %lu\n", proofstart);
  bool ok = check();
  trace("proof_start: %lu\n", proofstart);
  trace("propcount: %lu\n", propcount);
  trace("ratcalls: %lu\n", ratcalls);
  trace("rupcalls: %lu\n", rupcalls);
  echo("s %s\n", ok ? "ACCEPTED" : "REJECTED");
  exit(ok ? 0 : 1);
}
