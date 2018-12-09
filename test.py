#!/usr/bin/env python3

import sys
import os
from subprocess import Popen, PIPE

os.chdir(os.path.dirname(os.path.abspath(__file__)))


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


benchmark_location = 'benchmarks'


def benchmark_cnfs():
    return (f'{dirpath}/{file}'
            for dirpath, _, files in os.walk(benchmark_location)
            for file in files
            if file.endswith('.cnf')
            and '/excluded' not in dirpath)


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
    return Popen(command, stdout=PIPE).communicate()


def accepts(checker, name):
    'we take name here to see the benchmark name instantly when a test fails'
    stdout, _ = process_expansion(checker)
    accepted = b's ACCEPTED\n' in stdout or (
        'drat-trim' in checker[0] and b's VERIFIED' in stdout)
    rejected = b's REJECTED\n' in stdout or (
        'drat-trim' in checker[0] and b's NOT VERIFIED' in stdout)
    assert accepted ^ rejected
    return accepted


def lrat_checker_accepts(checker, name):
    stdout, _ = process_expansion(checker)
    ok = b's ACCEPTED\n' in stdout or (
        'lrat-checker' in checker[0] and b'c VERIFIED' in stdout)
    if not ok:
        print(str(stdout, 'utf8'))
    return ok


def compare_acceptance(a, b):
    build_release()
    [ensure_executable(command) for command in (a, b)]
    for name in small_inputs():
        args = [f'{name}.cnf', f'{name}.drat']

        if name == 'benchmarks/crafted/bottom' and 'rupee' in b[0]:
            continue  # different result
        if (('/rate' in b[0] or 'crate' in b[0])
                and name in [
                'benchmarks/crafted/marked-environment',
        ]):
            print(
                f'skipping {name} as {b[0]} checks all RAT candidates (not just core)')
            continue

        assert accepts(a + args, name) == accepts(b + args, name)


def certify_with_lrat_checker(drat_checker, lrat_checker):
    build_release()
    [ensure_executable(command) for command in (drat_checker, lrat_checker)]
    for name in small_inputs():
        args = [f'{name}.cnf', f'{name}.drat', '-L', f'{name}.lrat']
        if accepts(drat_checker + args, name):
            if name == 'benchmarks/crafted/bottom' and 'lrat-check' in lrat_checker[0]:
                continue  # infinite loop
            assert lrat_checker_accepts(
                lrat_checker + [args[0], args[3]], name)


# def test_acceptance_drat_trim():
#     compare_acceptance(rate(flags=['--drat-trim']), ['drat-trim'])


# def test_acceptance_rupee():
#     compare_acceptance(rate(), ['rupee'])


# def test_acceptance_crate():
#     compare_acceptance(rate(), ['./crate'])


# def test_acceptance_initial_commit():
#     initial_commit = '39d6db9faa1b1c3c252fcd1a41b5156ffb0a97b2'
#     build_release(initial_commit)
#     compare_acceptance(rate(), rate(initial_commit))


def test_using_lrat_check():
    certify_with_lrat_checker(rate(), ['lrat-check'])


def test_using_lratcheck():
    certify_with_lrat_checker(rate(), ['lratcheck'])
