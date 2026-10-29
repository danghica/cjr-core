"""Build and report dispatch for the examples organized under example/."""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import re
import subprocess
import sys

from . import benchmark, docs
from .support import toolchain, metadata

ROOT = Path(os.environ.get('CJR_PROJECT_ROOT', Path(__file__).resolve().parents[2])).resolve()
NAMES = tuple(json.loads((ROOT / 'repository.json').read_text())['examples'])
PROGRAMS = tuple(p.stem for name in NAMES for p in sorted((ROOT/'example'/name/'extracted').glob('*.cj')) if name != 'quadtree')


def owner(program):
    if program.startswith('qsort_'):
        return 'qsort'
    return next((name for name in NAMES if (ROOT/'example'/name/'extracted'/(program+'.cj')).is_file()), 'misc')


def code_path(program):
    return ROOT / 'example' / owner(program) / 'extracted' / (program + '.cj')


def coq_flags():
    import shlex
    lines = (ROOT / '_CoqProject').read_text().splitlines()
    flags = []
    for line in lines:
        tokens = shlex.split(line, comments=True)
        if tokens and tokens[0] in ('-R', '-Q'):
            flags.extend([tokens[0], str(ROOT / tokens[1]), tokens[2]])
    return flags


def extract():
    coqtop = os.environ.get('COQTOP', str(Path.home() / '.opam/default/bin/coqtop'))
    query = ('From Coq Require Import String.\nFrom cjr.ROOT_NAMESPACE Require Import emit_cj.\n'
             'Open Scope string_scope.\nEval vm_compute in cj_bundle.\n')
    query = query.replace('ROOT_NAMESPACE', 'examples' if ROOT.name == 'cjr-core' else ROOT.name.removeprefix('cjr-'))
    result = subprocess.run([coqtop, '-quiet', *coq_flags()], cwd=ROOT, input=query,
                            text=True, capture_output=True, check=True)
    match = re.search(r'=\s*"(.*)"(?:%string)?\s*:\s*string', result.stdout, re.S)
    if not match:
        raise RuntimeError('Unexpected extraction response from coqtop')
    chunks = re.split(r'^@@FILE ', match.group(1).replace('""', '"'), flags=re.M)
    emitted = {}
    for chunk in chunks:
        if not chunk:
            continue
        program, code = chunk.split('\n', 1)
        if program not in PROGRAMS or program in emitted:
            raise RuntimeError('Unexpected or repeated extraction entry: ' + program)
        if 'unsupported' in code:
            raise RuntimeError('Unsupported extraction form in ' + program)
        emitted[program] = code
    if set(emitted) != set(PROGRAMS):
        raise RuntimeError('Incomplete extracted program inventory')
    for program, code in emitted.items():
        path = code_path(program); path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(code)
    for program, functions in [('array_list', ('grow', 'add', 'remove')),
                               ('hash_map', ('grow', 'add', 'remove', 'contains', 'get'))]:
        if program in emitted and any('func ' + f not in emitted[program] for f in functions):
            raise RuntimeError('Missing public method in ' + program)
    print(f'Extracted {len(emitted)} programs into their example directories.')


def readable(name, explanations):
    project = ROOT / 'example' / name
    config = json.loads((project / 'project.config.json').read_text())
    if 'documentation_sources' in config:
        sources = config['documentation_sources']
    elif name == 'quadtree':
        sources = []  # Includes the generated audit module, as before relocation.
    else:
        sources = [line.strip() for line in (project / '_CoqProject').read_text().splitlines()
                   if line.strip().endswith('.v') and not line.startswith('-')]
    command = [sys.executable, '-m', 'tools.rocq_readable', 'build', '--output', 'docs/rocq',
               '--explanations', explanations]
    if sources:
        command.extend(['--sources', *sources])
    env = os.environ.copy()
    env['PYTHONPATH'] = str(ROOT) + os.pathsep + env.get('PYTHONPATH', '')
    env['PATH'] = str(Path.home() / '.opam/default/bin') + os.pathsep + env.get('PATH', '')
    subprocess.run(command, cwd=ROOT / 'example' / name, env=env, check=True)


def runtime_tests(name):
    if name == 'quadtree':
        subprocess.run([sys.executable, 'scripts/test.py'], cwd=ROOT / 'example/quadtree', check=True)
        return
    root = ROOT / 'example' / name
    cjc, env, version = toolchain(root)
    results = root / 'test/results'; results.mkdir(parents=True, exist_ok=True)
    cases, logs, failed = [], [], False
    for test in sorted((root / 'test').glob('*_test.cj')):
        program = test.name[:-8]; binary = results / (program + '-tests')
        compile_result = subprocess.run([str(cjc), '--test', '-O2', str(code_path(program)), str(test),
                                         '-o', str(binary)], env=env, text=True, capture_output=True)
        (results / (program + '-compile.log')).write_text(compile_result.stdout + compile_result.stderr)
        if compile_result.returncode:
            failed = True; logs.append(compile_result.stdout + compile_result.stderr); continue
        result = subprocess.run([str(binary), '--no-progress', '--no-color'], env=env,
                                text=True, capture_output=True)
        output = result.stdout + result.stderr
        (results / (program + '-execution.log')).write_text(output)
        expected = len(re.findall(r'@TestCase\b', test.read_text()))
        passed = re.findall(r'\[\s*PASSED\s*\]\s+CASE:\s+(\w+)', output)
        if result.returncode or len(passed) != expected or not passed:
            failed = True
        cases.extend(program + '.' + case for case in passed)
        logs.append(output)
    data = metadata(root, version, ['--test', '-O2'])
    data.update(status='failed' if failed else 'passed', cases=cases, stdout='\n'.join(logs), stderr='')
    docs.write_json(results / 'report.json', data)
    config = root / 'project.config.json'; settings = json.loads(config.read_text())
    settings['artifacts'].update(tests='test/results/report.json', test_report='test/report.html')
    # Config is an input to provenance; finalize it before collecting source hashes.
    docs.write_json(config, settings)
    data['sources'] = docs.hashes(root); docs.write_json(results / 'report.json', data)
    docs.test_report(config)
    print(f'{name}: {len(cases)} passed cases; status {data["status"]}')
    if failed:
        raise RuntimeError('Runtime test failures in ' + name)


def benchmarks(name, run=False):
    config = ROOT / 'example' / name / 'benchmark/benchmark.config.json'
    if not config.is_file():
        print(name + ': no benchmark harness'); return
    if run:
        benchmark.run(config)
    if (config.parent / 'results/summary.json').is_file():
        benchmark.plot(config); benchmark.report(config)


def report(name, allow_stale=False):
    config = ROOT / 'example' / name / 'project.config.json'
    benchmarks(name)
    settings = json.loads(config.read_text())
    if 'tests' in settings['artifacts']:
        docs.test_report(config)
    docs.metadata(config); docs.report(config, allow_stale=allow_stale)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('command', choices=('extract', 'readable', 'test', 'benchmark', 'report'))
    parser.add_argument('--example', choices=NAMES)
    parser.add_argument('--explanations', choices=('auto', 'offline'), default='auto')
    parser.add_argument('--allow-stale', action='store_true', help='Render saved results with source-mismatch notices')
    args = parser.parse_args(argv)
    if args.command == 'extract':
        extract(); return
    failures = []
    for name in ([args.example] if args.example else NAMES):
        try:
            if args.command == 'readable': readable(name, args.explanations)
            elif args.command == 'test': runtime_tests(name)
            elif args.command == 'benchmark': benchmarks(name, run=True)
            else: report(name, allow_stale=args.allow_stale)
        except (OSError, ValueError, RuntimeError, subprocess.CalledProcessError) as exc:
            failures.append(name); print(f'{name}: {exc}', file=sys.stderr)
    if args.command == 'report' and not args.example and not failures:
        docs.metadata(ROOT / 'project.config.json'); docs.report(ROOT / 'project.config.json', allow_stale=args.allow_stale)
    if failures:
        raise SystemExit(1)


if __name__ == '__main__': main()
