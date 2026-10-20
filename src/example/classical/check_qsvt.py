#!/usr/bin/env python3
"""Rebuild QSVT and audit its declarations; this is not a certified source parser."""
import argparse
import hashlib
import re
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
EXAMPLE = ROOT / 'src/example/classical'
FILES = ['qsvt_poly.v', 'qsvt_model.v', 'qsvt.v']
THEOREMS = [
    'QSVTSynthesis.qsp_pair_converse',
    'QSVTRealCompletion.even_nonnegative_completion',
    'QSVTRealPair.real_qsp_phase_witness',
    'QSVTModel.qsvt_full_column',
    'QSVTModel.qsvt_complex_even',
    'QSVTModel.qsvt_complex_odd',
    'QSVTSVD.sv_even_svd',
    'QSVTSVD.sv_odd_svd',
    'QSVTSVD.sv_even_kernel',
    'QSVTSVD.sv_odd_kernel',
    'QSVTWords.qsvt_prefix_adjoint_even',
    'QSVTWords.qsvt_prefix_adjoint_odd',
    'QSVTRows.real_qsvt_row_even',
    'QSVTRows.real_qsvt_row_odd',
    'QSVTUniformPhase.real_polynomial_phase_witness',
    'QSVTImaginaryColumns.explicit_failure_column_even',
    'QSVTImaginaryColumns.explicit_failure_column_odd',
    'QSVTClassicalProgram.coherent_core_prefix',
    'QSVTClassicalProgram.qsvt_core_execution',
    'QSVTClassicalProgram.qsvt_core_denote',
    'QSVTClassicalProgram.qsvt_heralded_branches',
    'QSVTClassicalProgram.qsvt_heralded_total',
    'QSVTClassicalProgram.qsvt_heralded_mass',
    'AncillaHeralding.register_success_kraus',
    'QSVTFailureSemantics.register_failure_kraus',
    'QSVTPolynomialCorrectness.even_preE',
    'QSVTPolynomialCorrectness.odd_preE',
    'QSVTPolynomialCorrectness.even_correct',
    'QSVTPolynomialCorrectness.odd_correct',
    'QSVTPolynomialCorrectness.even_expect',
    'QSVTPolynomialCorrectness.odd_expect',
    'QSVTPolynomialCorrectness.qsvt_framework_and_program',
    'QSVTNativeStateCorrectness.qsvt_native_framework_contract',
    'QSVTNativeStateCorrectness.qsvt_framework_exact',
    'QSVTNormCompleteness.symmetric_antisymmetric_complete',
    'QSVTNativeCompleteness.qsvt_framework_complete',
    'QSVTNativeCompleteness.native_even_completion_gram',
    'QSVTNativeCompleteness.native_odd_completion_gram',
    'QSVTNativeCompleteness.native_even_outcome_mass',
    'QSVTNativeCompleteness.native_odd_outcome_mass',
    'QSVTNativeStateCorrectness.native_even_success_density',
    'QSVTNativeStateCorrectness.native_odd_success_density',
    'QSVTNativeStateCorrectness.native_even_success_mass',
    'QSVTNativeStateCorrectness.native_odd_success_mass',
    'QSVTNativeStateCorrectness.native_even_failure_density',
    'QSVTNativeStateCorrectness.native_odd_failure_density',
    'QSVTExamples.qsp_reflection_W_bridge',
    'QSVTExamples.qsp_example_degree_zero',
    'QSVTExamples.qsp_example_degree_one_X',
    'QSVTExamples.qsp_example_degree_one_zero',
    'QSVTExamples.qsp_example_degree_two_one',
    'QSVTExamples.qsp_example_degree_two_chebyshev',
    'QSVTExamples.qsp_example_degree_two_square',
    'QSVTEndpointConvention.qsvt_endpoint_corner_bridge',
    'QSVTRejectedParity.mixed_parity_not_admissible',
]

def command(args, cwd=ROOT, input_text=None):
    print('$ ' + ' '.join(map(str, args)), flush=True)
    subprocess.run(list(map(str, args)), cwd=cwd, input=input_text,
                   text=True, check=True)

def without_comments(text):
    depth, i, out = 0, 0, []
    while i < len(text):
        if text.startswith('(*', i):
            depth += 1
            i += 2
        elif depth and text.startswith('*)', i):
            depth -= 1
            i += 2
        else:
            out.append(text[i] if not depth or text[i] == '\n' else ' ')
            i += 1
    if depth:
        raise SystemExit('Unclosed Rocq comment')
    return ''.join(out)

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--kernel', action='store_true',
                        help='also recursively check compiled modules with rocq check')
    opts = parser.parse_args()
    branch = subprocess.check_output(['git', 'branch', '--show-current'],
                                     cwd=ROOT, text=True).strip()
    if branch != 'cqwhile+distributive':
        raise SystemExit('Expected cqwhile+distributive; found ' + branch)
    for name in FILES:
        path = EXAMPLE / name
        data = path.read_bytes()
        text = without_comments(data.decode())
        if re.search(r'\b(?:admit|Admitted|Axiom|Axioms|Conjecture)\b|^\s*Abort\s*\.',
                     text, re.MULTILINE):
            raise SystemExit('Unfinished proof/new axiom in ' + name)
        body = text[text.index('Module '):]
        if re.search(r'^\s*(?:From\s+.*\s+)?Require\b|^\s*(?:Set|Unset)\s',
                     body, re.MULTILINE):
            raise SystemExit('Imports/flags outside prelude in ' + name)
        print(name, hashlib.sha256(data).hexdigest(), flush=True)
    print('Source scans passed (ordinary executable audit).', flush=True)
    command(['git', 'rev-parse', 'HEAD'])
    command(['opam', 'exec', '--switch=coqq', '--', 'ocamlc', '-version'])
    command(['opam', 'exec', '--switch=coqq', '--', 'rocq', '-v'])
    packages = subprocess.check_output(
        ['opam', 'list', '--switch=coqq', '--installed',
         '--columns=name,version', '--short'], cwd=ROOT, text=True)
    print(packages, flush=True)
    installed = dict(line.split() for line in packages.splitlines()
                     if line.strip() and not line.startswith('#'))
    pins = dict(re.findall(r'"([^"]+)"\s*\{\s*=\s*"([^"]+)"\s*\}',
                           (ROOT / 'coq-mathcomp-quantum.opam').read_text()))
    pins['ocaml-base-compiler'] = '5.2.0'
    for package, version in pins.items():
        if installed.get(package) != version:
            raise SystemExit('Wrong dependency: ' + package + ', expected ' + version)
    dune_version = tuple(map(int, installed['dune'].split('.')[:2]))
    if not (3, 13) <= dune_version < (3, 24):
        raise SystemExit('Dune version outside repository constraint')
    print('Named switch and repository dependency pins match.', flush=True)
    command(['opam', 'exec', '--switch=coqq', '--', 'dune', 'build'])
    with tempfile.TemporaryDirectory(prefix='qsvt-final-audit-') as temp:
        temp = Path(temp)
        source = temp / 'assumptions.v'
        lines = ['From quantum.example.classical Require Import qsvt_poly qsvt_model qsvt.']
        for theorem in THEOREMS:
            lines += ['Check ' + theorem + '.', 'Print Assumptions ' + theorem + '.']
        source.write_text('\n'.join(lines) + '\n')
        command(['opam', 'exec', '--switch=coqq', '--', 'rocq', 'compile',
                 '-w', '-all', '-R', ROOT / '_build/default/src', 'quantum',
                 '-Q', temp, 'QSVTAudit', source], cwd=temp)
    if opts.kernel:
        command(['opam', 'exec', '--switch=coqq', '--', 'rocq', 'check', '-silent',
                 '-R', ROOT / '_build/default/src', 'quantum',
                 'quantum.example.classical.qsvt_poly',
                 'quantum.example.classical.qsvt_model',
                 'quantum.example.classical.qsvt'])
    print('QSVT validation passed.', flush=True)

if __name__ == '__main__':
    main()
