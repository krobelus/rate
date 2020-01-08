#!/usr/bin/env python3

import argparse
import os
import distutils.spawn
import inspect
from subprocess import Popen, PIPE
import sys
from functools import lru_cache

LOG = []
VERBOSE = False
CNFS = []


def log(s=''):
    global LOG
    if s == '':
        LOG = []
    else:
        LOG += [s]
    if VERBOSE:
        print(s)


def require(ok, message=None, fatal=True):
    if ok:
        return
    print('# failed commands:')
    print('\n'.join(LOG))
    if fatal:
        sys.exit(1)


def popen(command, input=None, **kwargs):
    log(' '.join(command))
    return Popen(command, **kwargs)


def rate(flags=[]):
    executable = './target/release/rate'
    return [executable] + flags


def size(cnf):
    return os.path.getsize(cnf)


def inputs(*allowed_proof_extensions):
    if not allowed_proof_extensions:
        allowed_proof_extensions = ('pr', 'dpr', 'drat')
    pairs = []
    for cnf in sorted(CNFS, key=size):
        name = cnf[:-len('.cnf')]
        for ext in allowed_proof_extensions:
            if os.path.isfile(f'{name}.{ext}'):
                pairs += [(cnf, f'{name}.{ext}')]
    return pairs


def pr_inputs():
    return inputs('pr', 'dpr')


def drat_inputs():
    return inputs('drat')


@lru_cache(maxsize=None)
def executable(name):
    return distutils.spawn.find_executable(name)


def ensure_executable(command):
    log()
    require(executable(command[0]), f'{command[0]} not found in PATH')


def process_expansion(command, input=None):
    # we need to redirect stderr for gratgen
    p = popen(command, input=input, stdin=PIPE, stdout=PIPE, stderr=PIPE)
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
    require(accepted != rejected, 'checker must either accept or reject',
            str(stdout, 'utf8') + str(stderr, 'utf8'))
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
    [ensure_executable(command) for command in (a, b)]
    for cnf, proof in instances:
        log()
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

        require(
            accepts(
                a + args,
                name) == accepts(
                b + args,
                name),
            "checkers give different answer")


def double_check(drat_checker,
                 lrat_checker=['lrat-check'],
                 grat_checker=['gratchk', 'unsat'],
                 *,
                 instances):
    ensure_executable(drat_checker)
    if lrat_checker is not None:
        if not executable(lrat_checker[0]):
            lrat_checker = None
    if grat_checker is not None:
        if not executable(grat_checker[0]):
            grat_checker = None
    skip_unit_deletions = any(
        '-d' in arg for arg in drat_checker)
    forward = any(arg in ('--forward', '-f') for arg in drat_checker)
    noncore_rat_candidates = any(
        arg in ('-r', '--noncore-rat-candidates') for arg in drat_checker)
    sick = not skip_unit_deletions
    grat = not forward
    lrat = not forward and lrat_checker is not None and not noncore_rat_candidates
    for cnf, proof in instances:
        log()
        name = cnf[:-len('.cnf')] if cnf.endswith('.cnf') else cnf
        pr = proof.endswith('.dpr') or proof.endswith('.pr')
        pr2drat = pr and executable(
            'pr2drat') and not forward and not noncore_rat_candidates
        args = [cnf]
        args += [proof]
        if pr:
            if pr2drat:
                args += ['-l', f'{name}.core.dpr']
            if sick:
                args += ['-S', f'{name}.sick']
        else:
            if lrat:
                args += ['-L', f'{name}.lrat']
            if grat:
                args += ['-G', f'{name}.grat']
            if sick:
                args += ['-S', f'{name}.sick']
        if pr and accepts(drat_checker + args, name):
            if pr2drat:
                stdout, stderr = process_expansion(
                    ['pr2drat', cnf, f'{name}.core.dpr'])
                require(not stderr, name)
                with open(f'{name}.core.drat', 'wb') as f:
                    f.write(stdout)
                # drat_checker is rate with some flags, use it to convert
                # the output of pr2drat to LRAT
                stdout, stderr = process_expansion(
                    drat_checker + [cnf, f'{name}.core.drat', '-L', f'{name}.core.lrat'])
                require(not stderr, 'rate stderr should be empty')
                require(
                    b's VERIFIED' in stdout,
                    'rate should verify the converted DRAT proof, just like the PR one')
                if lrat and (name not in {f'benchmarks/sadical/{x}'
                                          for x in (
                                              'emptyclause', 'unit4', 'regr1',
                                          )}):
                    require(lrat_checker_accepts(
                        lrat_checker + [cnf, f'{name}.core.lrat', 'nil', 't'], 'lrat check failed'))
        elif accepts(drat_checker + args, name):
            if lrat and (name not in {f'benchmarks/crafted/{x}' for x in (
                'tautological',
                'duplicate-literals',
                'bottom',
            )}):
                require(lrat_checker_accepts(lrat_checker +
                                             [cnf, f'{name}.lrat', 'nil', 't'], 'lrat check failed'))
            if grat and (grat_checker is not None and (
                ('rate' not in drat_checker[0]) or skip_unit_deletions or
                (name not in {f'benchmarks/rupee/{x}' for x in (
                    'tricky-2',  # looks like gratchk cannot delete units
                )})
            )):
                require(gratchk_accepts(grat_checker +
                                        [cnf, f'{name}.grat'], 'gratchk failed'))
        elif sick:
            require(sick_checker_accepts(
                ['target/release/sick-check', cnf, proof, f'{name}.sick'], name))


def test_flags00_default():
    double_check(rate(), instances=inputs())


def test_flags01_skip_unit_deletions():
    double_check(rate(flags=['-d']), instances=inputs())


def test_flags02_forward():
    double_check(rate(flags=['-f']), instances=inputs())


def test_flags03_assume_pivot_is_first():
    double_check(
        rate(
            flags=['--assume-pivot-is-first']),
        instances=drat_inputs())


def test_flags04_noncore_rat_candidates():
    double_check(
        rate(
            flags=['--noncore-rat-candidates']),
        instances=inputs())


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


def test_acceptance_drat_trim():
    if executable('drat-trim'):
        compare_acceptance(
            rate(flags=['-d']),
            ['drat-trim'],
            instances=drat_inputs())


def test_acceptance_dpr_trim():
    if executable('dpr-trim'):
        compare_acceptance(
            rate(flags=['-d']),
            ['dpr-trim'],
            instances=pr_inputs())


def test_acceptance_gratgen():
    if executable('gratgen'):
        compare_acceptance(
            rate(
                flags=['-d', '--noncore-rat-candidates']),
            ['gratgen'],
            instances=drat_inputs())


def test_acceptance_rupee():
    if executable('rupee'):
        compare_acceptance(
            rate(
                flags=['--assume-pivot-is-first']),
            ['rupee'],
            instances=drat_inputs())


def test_drat2bdrat_bdrat2drat():
    drat2bdrat = './target/release/drat2bdrat'
    bdrat2drat = './target/release/bdrat2drat'
    for benchmark in ('crafted/example1b', ):
        log()
        filename = f'benchmarks/{benchmark}.drat'
        with open(filename) as f:
            content = f.read().encode()
        stdout1, stderr1 = process_expansion([bdrat2drat], input=content)
        require(stderr1 == b'', name)
        stdout2, stderr2 = process_expansion([drat2bdrat], input=stdout1)
        require(stderr2 == b'', name)
        require(content == stdout2, name)
    for benchmark in (
        'crafted/uuf',
        'crafted/example1',
        'crafted/wrong-deletion',
        'crafted/strange',
    ):
        log()
        filename = f'benchmarks/{benchmark}.drat'
        with open(filename) as f:
            content = f.read().encode()
        stdout1, stderr1 = process_expansion([drat2bdrat], input=content)
        require(stderr1 == b'', name)
        stdout2, stderr2 = process_expansion([bdrat2drat], input=stdout1)
        require(stderr2 == b'', name)
        require(content == stdout2, name)


if __name__ == '__main__':
    description = '''
Without options, run all tests.  Pass some paths to CNF files, or
directories containing CNF files and proofs to run tests only on those
instances. Limit the tests with -k.

    '''
    epilog = f'''Example:
    $ {sys.argv[0]} -k test_pr benchmarks/crafted benchmarks/sadical/add4.cnf
    '''
    parser = argparse.ArgumentParser(description=description, epilog=epilog)
    parser.add_argument(
        "-k",
        type=str,
        help="only run tests that contain the given string")
    parser.add_argument("-v", action='store_true', help="log all commands")
    opts, args = parser.parse_known_args()

    if not args:
        args = ['benchmarks']
    for arg in args:
        if arg.endswith('.cnf'):
            CNFS += [arg]
        else:
            arg = arg.rstrip('/')
            CNFS += [f'{dirpath}/{file}'
                     for dirpath, _, files in os.walk(arg)
                     for file in files
                     if file.endswith('.cnf')]

    testfunctions = [(name, obj) for name, obj in inspect.getmembers(
        sys.modules[__name__]) if inspect.isfunction(obj) and name.startswith('test')]
    if opts.k:
        testfunctions = [(name, f)
                         for name, f in testfunctions if opts.k in name]
    if opts.v:
        VERBOSE = True

    os.chdir(os.path.dirname(os.path.abspath(__file__)))
    require(popen(['cargo', 'build', '--release']).wait() == 0)
    for name, f in testfunctions:
        print(name)
        log()
        f()
