#!/usr/bin/env python3

import random


def lit2var(literal):
    return abs(literal)


def random_literal(maxvar):
    return random.randint(1, maxvar) * (-1 if random.random() < .5 else 1)


def random_clause(maxvar, arity):
    c = []
    while len(c) < arity:
        lit = random_literal(maxvar)
        if lit2var(lit) not in map(lit2var, c):
            c += [lit]
    return c


def random_instance(num_variables, arity, num_clauses):
    return [random_clause(num_variables, arity) for _ in range(num_clauses)]


def encode(formula):
    maxvar = max(set(lit2var(literal)
                     for clause in formula for literal in clause))
    return (f'p cnf {maxvar} {len(formula)}\n'
            + ''.join(
                ''.join(f'{literal} ' for literal in clause) + '0\n'
                for clause in formula))


print(encode(random_instance(50, 5, 2000)), end='')
