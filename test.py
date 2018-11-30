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


def rate(commit_sha=None):
    if commit_sha:
        return f'./checkouts/{commit_sha}/{rate()}'
    return './target/release/rate'


benchmark_location = 'benchmarks'


def benchmark_cnfs():
    return (f'{dirpath}/{file}'
            for dirpath, _, files in os.walk(benchmark_location)
            for file in files
            if file.endswith('.cnf'))


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


def compare_acceptance(a, b):
    build_release()
    for checker in a, b:
        assert Popen(('which', checker)).wait(
        ) == 0, f'{checker} not found in PATH'
    for name in small_inputs():
        print(f'##### Comparing result of {a} and {b} for {name} #####')
        args = [f'{name}.cnf', f'{name}.drat']

        def accepts(checker):
            stdout = Popen([checker] + args, stdout=PIPE).communicate()[0]
            return b's ACCEPTED' in stdout
        assert accepts(a) == accepts(b)


def test_compare_trace_crate():
    return
    build_release()
    for name in small_inputs():
        print(
            f'##### Comparing output trace of rate and crate for {name} #####')
        command = (
            './scripts/diff-rate-crate.sh',
            f'{name}.cnf',
            f'{name}.drat')
        print(' '.join(command))
        assert Popen(command).wait() == 0


def test_acceptance_rupee():
    compare_acceptance(rate(), 'rupee')


def test_acceptance_crate():
    compare_acceptance(rate(), './crate')


def test_acceptance_initial_commit():
    initial_commit = '39d6db9faa1b1c3c252fcd1a41b5156ffb0a97b2'
    build_release(initial_commit)
    compare_acceptance(rate(), rate(initial_commit))
