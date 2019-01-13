#!/usr/bin/env python3

import sys
import time
import os
from subprocess import Popen, PIPE
from functools import lru_cache

os.chdir(os.path.dirname(os.path.abspath(__file__)))

benchmark_location = 'benchmarks'

INITIAL_COMMIT = '39d6db9faa1b1c3c252fcd1a41b5156ffb0a97b2'


def run(command):
    assert Popen(command).wait() == 0


def build_release(commit_sha=None):
    cargo_release = ['cargo', 'build', '--release']
    if commit_sha:
        return run(['./scripts/exec-in-version.sh',
                    commit_sha] + cargo_release)
    run(cargo_release)
    run(['make'])


def rate(commit_sha=None, *, flags=[]):
    executable = './target/release/rate'
    if commit_sha:
        executable = f'./checkouts/{commit_sha}/{executable}'
    return [executable] + flags


def benchmark_cnfs():
    return (f'{dirpath}/{file}'
            for dirpath, _, files in os.walk(benchmark_location)
            for file in files
            if file.endswith('.cnf')
            and '/performance' not in dirpath
            and '/random' not in dirpath
            and '/excluded' not in dirpath
            )


def all_inputs():
    def size(cnf):
        return os.path.getsize(cnf)
    return [cnf[:-len('.cnf')]
            for cnf in sorted(benchmark_cnfs(), key=size)]


def small_inputs():
    return [name for name in all_inputs()
            # only use small formulas
            if os.path.getsize(f'{name}.cnf') < 10_0000
            ]


def ensure_executable(command):
    assert Popen(('which', command[0])).wait(
    ) == 0, f'{command[0]} not found in PATH'


def process_expansion(command):
    # we need to redirect stderr for gratgen
    return Popen(command, stdout=PIPE, stderr=PIPE).communicate()


@lru_cache(maxsize=None)
def process_expansion_cached(command):
    assert isinstance(command, tuple)
    return process_expansion(command)


def timed(f):
    def wrapper(*args, **kwargs):
        start = time.time()
        call = f.__name__ + '(' + ', '.join(str(a) for a in args)
        # (f.__name__ + '(' + newline
        #           + newline.join(str(a) for a in args))
        if kwargs:
            # call += ',' + newline + newline.join(f'{key}={str(kwargs[key])},' for key in kwargs)
            call += ',' ', '.join(
                f'{key}={str(kwargs[key])},' for key in kwargs)
        call += ')'
        result = f(*args, **kwargs)
        duration = time.time() - start
        if duration > 0.5:
            print(f'spent %3.2f in {call}' % duration)
        return result
    return wrapper


@timed
def accepts(checker, name):
    'we take name here to see the benchmark name as a test fails'
    # n.b. this assumes that the DIMACS and DRAT files do not change!
    stdout, stderr = process_expansion_cached(tuple(checker))
    accepted = b's ACCEPTED\n' in stdout or (
        'drat-trim' in checker[0] and b's VERIFIED' in stdout) or (
        'gratgen' in checker[0] and b's VERIFIED' in stderr)
    rejected = b's REJECTED\n' in stdout or (
        'drat-trim' in checker[0] and b's NOT VERIFIED' in stdout) or (
        'gratgen' in checker[0] and b's VERIFIED' not in stderr)
    assert accepted != rejected
    return accepted


@timed
def lrat_checker_accepts(checker, name):
    stdout, _ = process_expansion(checker)
    ok = b's ACCEPTED\n' in stdout or (
        'lrat-check' in checker[0] and b'c VERIFIED' in stdout)
    if not ok:
        print(str(stdout, 'utf8'))
    return ok


@timed
def sick_checker_accepts(checker, name):
    stdout, _ = process_expansion(checker)
    ok = b's ACCEPTED\n' in stdout
    if not ok:
        print(str(stdout, 'utf8'))
    return ok


def compare_acceptance(a, b, *, instances=all_inputs()):
    build_release()
    [ensure_executable(command) for command in (a, b)]
    for name in instances:
        args = [f'{name}.cnf', f'{name}.drat']

        if 'rupee' in b[0]:
            if name == 'benchmarks/crafted/bottom':
                continue  # different result
            if name == 'benchmarks/rupee/trick':
                continue  # different result
        if name == 'benchmarks/crafted/faux-conflict' and 'drat-trim' in b[0]:
            continue  # drat-trim uses binary mode here
        if name == 'benchmarks/crafted/falsified' and INITIAL_COMMIT in b[0]:
            continue  # does not skip unused lemmas
        if ((INITIAL_COMMIT in b[0] or 'crate' in b[0])
                and name in [
                'benchmarks/crafted/marked-environment',
        ]):
            print(
                f'skipping {name} as {b[0]} checks all RAT candidates (not just core)')
            continue
        if 'gratgen' in b[0]:
            if name in (
                'benchmarks/crafted/bottom',
                    'benchmarks/crafted/trivunsat'):
                continue

        assert accepts(a + args, name) == accepts(b + args, name)


def double_check(
        drat_checker,
        lrat_checker=['lratcheck'],
        *,
        instances=all_inputs()):
    build_release()
    [ensure_executable(command) for command in (drat_checker, lrat_checker)]
    for name in instances:
        args = [
            f'{name}.cnf',
            f'{name}.drat',
            '-L',
            f'{name}.lrat',
            '--recheck',
            f'{name}.sick']
        if accepts(drat_checker + args, name):
            if name == 'benchmarks/crafted/bottom' and 'lrat-check' in lrat_checker[0]:
                continue  # infinite loop
            if name == 'benchmarks/crafted/tautological' and 'lratcheck' in lrat_checker[0]:
                continue  # rejects tautological formulas
            assert lrat_checker_accepts(
                lrat_checker + [args[0], args[3]], name)
        else:
            # TODO hack sickcheck to handle some edge cases
            if name == 'benchmarks/crafted/empty':
                continue
            if name == 'benchmarks/crafted/multi-delete':
                continue
            if name == 'benchmarks/crafted/no-conflict':
                continue
            assert sick_checker_accepts(
                ['sickcheck'] + args[:2] + [args[-1]], name)


def test_quick():
    double_check(
        rate(
            flags=['--assume-pivot-is-first']),
        instances=small_inputs())


def test_quick_no_core_first():
    double_check(
        rate(
            flags=['--assume-pivot-is-first',
                   '--no-core-first']),
        instances=small_inputs())


def test_with_lrat_check():
    double_check(rate(
        flags=['--assume-pivot-is-first']), ['lrat-check'])


def test_with_lratcheck():
    double_check(
        rate(
            flags=['--assume-pivot-is-first']),
        ['lratcheck'])


def test_acceptance_initial_commit():
    build_release(INITIAL_COMMIT)
    compare_acceptance(
        rate(
            flags=['--noncore-rat-candidates']),
        rate(INITIAL_COMMIT),
        instances=small_inputs())


def test_acceptance_drat_trim():
    compare_acceptance(rate(flags=['--drat-trim']), ['drat-trim'])


def test_acceptance_rupee():
    compare_acceptance(rate(flags=['--rupee']), ['rupee'])


def test_acceptance_gratgen():
    compare_acceptance(rate(flags=['--skip-deletions']), ['gratgen'])
