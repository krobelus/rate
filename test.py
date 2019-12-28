#!/usr/bin/env -S python3 -m pytest

import time
import os
import distutils.spawn
from subprocess import Popen, PIPE
import sys

benchmark_location = 'benchmarks'
os.chdir(os.path.dirname(os.path.abspath(__file__)))

cnfs = [f'{dirpath}/{file}'
            for dirpath, _, files in os.walk(benchmark_location)
            for file in files
            if file.endswith('.cnf') and '/excluded' not in dirpath]

def build_release():
    cargo_release = ['cargo', 'build', '--release']
    run(cargo_release)


def rate(flags=[]):
    executable = './target/release/rate'
    return [executable] + flags


def size(cnf):
    return os.path.getsize(cnf)


def drat_inputs():
    return [
        (cnf, (cnf[:-len('cnf')] + 'drat'))
        for cnf in sorted(cnfs, key=size)
        if os.path.exists(cnf[:-len('cnf')] + 'drat')
    ]


def small_drat_inputs():
    return [
        (cnf, proof) for cnf, proof in drat_inputs()
        # only use small formulas
        if size(cnf) < 10_0000
    ]


def pr_inputs():
    return [
        (cnf, cnf[:-len('cnf')] + 'dpr') for cnf in sorted(cnfs, key=size)
        if os.path.exists(cnf[:-len('cnf')] + 'dpr')
    ]


def executable(name):
    return distutils.spawn.find_executable(name)


def ensure_executable(command):
    assert executable(command[0]), f'{command[0]} not found in PATH'


def popen(command, **kwargs):
    print(' '.join(command))
    return Popen(command, **kwargs)


def run(command):
    assert popen(command).wait() == 0


def process_expansion(command, input=None):
    # we need to redirect stderr for gratgen
    p = popen(command, stdin=PIPE, stdout=PIPE, stderr=PIPE)
    if input is not None:
        return p.communicate(input=input)
    else:
        return p.communicate()


process_expansion_cache = {}
def process_expansion_cached(command):
    assert isinstance(command, tuple)
    if command in process_expansion_cache:
        return process_expansion_cache[command]
    return process_expansion(command)


def accepts(checker, name):
    'we take name here to see the benchmark name as a test fails'
    # n.b. this assumes that the DIMACS and DRAT files do not change!
    stdout, stderr = process_expansion_cached(tuple(checker))
    accepted = b's VERIFIED\n' in stdout or (
        ('rupee' in checker[0])
        and b's ACCEPTED' in stdout) or ('gratgen' in checker[0]
                                         and b's VERIFIED' in stderr)
    rejected = b's NOT VERIFIED\n' in stdout or (
        ('rupee' in checker[0])
        and b's REJECTED' in stdout) or ('gratgen' in checker[0]
                                         and b's VERIFIED' not in stderr)
    assert accepted != rejected, str(stdout, 'utf8') + str(stderr, 'utf8')
    return accepted


def lrat_checker_accepts(checker, name):
    stdout, _ = process_expansion(checker)
    ok = (('lratcheck' in checker[0] and b's ACCEPTED\n' in stdout)
          or ('lrat-check' in checker[0] and b's VERIFIED' in stdout))
    if not ok:
        print(str(stdout, 'utf8'))
    return ok


def gratchk_accepts(grat_checker, name):
    stdout, _ = process_expansion(grat_checker)
    ok = b's VERIFIED UNSAT' in stdout
    if not ok:
        print(str(stdout, 'utf8'))
    return ok


def sick_checker_accepts(checker, name):
    stdout, _ = process_expansion(checker)
    ok = b's VERIFIED\n' in stdout
    if not ok:
        print(str(stdout, 'utf8'))
    return ok


def compare_acceptance(a, b, *, instances):
    build_release()
    [ensure_executable(command) for command in (a, b)]
    for cnf, proof in instances:
        name = cnf[:-len('.cnf')]
        args = [cnf, proof]

        if 'rupee' in b[0]:
            if name == 'benchmarks/crafted/comments':
                continue
            if name == 'benchmarks/crafted/bottom':
                continue  # different result
            if name in ('benchmarks/crafted/missing-last-zero',
                        'benchmarks/crafted/missing-last-zero2'):
                continue  # rupee rejects the proof
            if name == 'benchmarks/rupee/problem':
                continue  # rejected by rupee, see the commit that introduced this line
            if name == 'benchmarks/rupee/trick':
                continue  # different result
            if name == 'benchmarks/crafted/example1b':
                continue
            if name == 'benchmarks/crafted/rupee-broken-invariant':
                continue
        if 'drat-trim' in b[0]:
            if name in (
                'benchmarks/crafted/faux-conflict',
                'benchmarks/crafted/sick-example',
                    'benchmarks/crafted/crlf'):
                continue  # drat-trim uses binary mode here
        if 'gratgen' in b[0]:
            if name in (
                    'benchmarks/crafted/bottom',
                    'benchmarks/crafted/trivunsat',
                    'benchmarks/crafted/example1b',
            ):
                continue
        if 'dpr-trim' in b[0]:
            if name in (
                'benchmarks/sadical/emptyclause',
            ):
                continue

        assert accepts(a + args, name) == accepts(b + args, name)
        print()


def double_check(drat_checker,
                 lrat_checker=['lrat-check'],
                 grat_checker=['gratchk', 'unsat'],
                 *,
                 instances):
    build_release()
    ensure_executable(drat_checker)
    if lrat_checker is not None:
        if not executable(lrat_checker[0]):
            lrat_checker = None
    if grat_checker is not None:
        if not executable(grat_checker[0]):
            grat_checker = None
    skip_unit_deletions = any(
        '--skip-unit-deletions' in arg for arg in drat_checker)
    forward = any('--forward' in arg for arg in drat_checker)
    sick = not skip_unit_deletions and not forward
    grat = not forward
    lrat = not forward
    for cnf, proof in instances:
        name = cnf[:-len('.cnf')] if cnf.endswith('.cnf') else cnf
        pr = os.path.exists(f'{name}.dpr')
        args = [cnf]
        if pr:
            args += [f'{name}.dpr']
        else:
            args += [proof]
            if lrat:
                args += ['-L', f'{name}.lrat']
            if grat:
                args += ['-G', f'{name}.grat']
            if sick:
                args += ['-S', f'{name}.sick']
        if pr:
            assert accepts(drat_checker + args, name)
            return
        if accepts(drat_checker + args, name):
            if lrat and (lrat_checker is not None and
                         name not in {f'benchmarks/crafted/{x}' for x in (
                             'tautological',
                             'duplicate-literals',
                             'bottom',
                         )}):
                assert 'lrat-check' in lrat_checker[0]
                assert lrat_checker_accepts(
                    lrat_checker + [args[0], args[3], 'nil', 't'], name)
            if grat and (grat_checker is not None and (
                ('rate' not in drat_checker[0]) or skip_unit_deletions or
                (name not in {f'benchmarks/rupee/{x}' for x in (
                    'tricky-2',  # looks like gratchk cannot delete units
                )})
            )):
                assert gratchk_accepts(grat_checker + [args[0], args[5]], name)
        elif sick:
            assert sick_checker_accepts(
                ['target/release/sick-check'] + args[:2] + [args[-1]], name)
        print()


def test_pr():
    double_check(rate(), instances=pr_inputs())


def test_quick_default():
    double_check(
        rate(), instances=small_drat_inputs())


def test_quick_pivot_is_first():
    double_check(
        rate(flags=['--assume-pivot-is-first']), instances=small_drat_inputs())


def test_quick_skip_unit_deletions():
    double_check(
        rate(flags=['--skip-unit-deletions']),
        instances=small_drat_inputs())


def test_full():
    double_check(rate(),
                 instances=set(drat_inputs()) - set(small_drat_inputs()))


def test_compression():
    compressed_inputs = [
        (f'benchmarks/crafted/example1.cnf.{x}',
         f'benchmarks/crafted/example1.drat.{x}') for x in (
            'zst', 'gz', 'bz2', 'xz', 'lz4')]
    double_check(
        rate(),
        instances=compressed_inputs,
        lrat_checker=None,
        grat_checker=None)


def test_forward():
    double_check(
        rate(
            flags=['--forward']),
        instances=set(
            drat_inputs()) | set(
                pr_inputs()))

def test_acceptance_drat_trim():
    if executable('drat-trim'):
        compare_acceptance(
            rate(
                flags=['--skip-unit-deletions']),
            ['drat-trim'],
            instances=drat_inputs())


def test_acceptance_rupee():
    if executable('rupee'):
        compare_acceptance(
            rate(
                flags=['--assume-pivot-is-first']),
            ['rupee'],
            instances=drat_inputs())


def test_acceptance_gratgen():
    if executable('gratgen'):
        compare_acceptance(
            rate(
                flags=['--skip-unit-deletions', '--noncore-rat-candidates']),
            ['gratgen'],
            instances=drat_inputs())


def test_acceptance_dpr_trim():
    if executable('dpr-trim'):
        compare_acceptance(
            rate(),
            ['dpr-trim'],
            instances=pr_inputs())


def test_drat2bdrat_bdrat2drat():
    build_release()
    drat2bdrat = './target/release/drat2bdrat'
    bdrat2drat = './target/release/bdrat2drat'
    for benchmark in ('crafted/example1b', ):
        filename = f'benchmarks/{benchmark}.drat'
        print(filename)
        with open(filename) as f:
            content = f.read().encode()
        stdout1, stderr1 = process_expansion([bdrat2drat], input=content)
        assert stderr1 == b''
        stdout2, stderr2 = process_expansion([drat2bdrat], input=stdout1)
        assert stderr2 == b''
        assert content == stdout2
    for benchmark in (
        'crafted/uuf',
        'crafted/example1',
        'crafted/wrong-deletion',
        'crafted/strange',
    ):
        filename = f'benchmarks/{benchmark}.drat'
        print(filename)
        with open(filename) as f:
            content = f.read().encode()
        stdout1, stderr1 = process_expansion([drat2bdrat], input=content)
        assert stderr1 == b''
        stdout2, stderr2 = process_expansion([bdrat2drat], input=stdout1)
        assert stderr2 == b''
        assert content == stdout2
