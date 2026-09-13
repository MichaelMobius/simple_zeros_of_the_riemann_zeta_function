#!/usr/bin/env python3
"""Generate Lean certificates for the exact rational v26 bootstrap discard layer.

The generator uses fractions.Fraction only. It does not prove anything by
itself: every generated completion-of-squares identity is rechecked by Lean's
kernel through `ring`, every SOS sign by `positivity`, and every strict target
margin by `norm_num`.
"""
from __future__ import annotations
from fractions import Fraction as Q
from pathlib import Path
import argparse, hashlib, importlib.util, json

HERE = Path(__file__).resolve().parent
VERIFIER = HERE / 'v21_rational_bootstrap_verify.py'


def load_verifier():
    spec = importlib.util.spec_from_file_location('v21_exact', VERIFIER)
    if spec is None or spec.loader is None:
        raise RuntimeError('cannot load exact verifier')
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod

v = load_verifier()
EXPECTED_CHAIN = (511, 231, 23, 5)
EXPECTED_FINAL = ('121212', '121221', '122121', '212121', '212212')
CHUNK_SIZE = 50


def qlean(x: Q) -> str:
    x = Q(x)
    if x.denominator == 1:
        return str(x.numerator)
    return f'({x.numerator} / {x.denominator} : ℝ)'


def wcode(w) -> str:
    return ''.join(map(str, w))


def ldl_exact(A):
    """Exact LDL^T for a symmetric positive-definite rational matrix."""
    n = len(A)
    L = [[Q(0) for _ in range(n)] for _ in range(n)]
    D = [Q(0) for _ in range(n)]
    for i in range(n):
        L[i][i] = Q(1)
    for j in range(n):
        D[j] = A[j][j] - sum((L[j][k] ** 2) * D[k] for k in range(j))
        assert D[j] > 0
        for i in range(j + 1, n):
            L[i][j] = (A[i][j] - sum(L[i][k] * L[j][k] * D[k]
                                      for k in range(j))) / D[j]
    for i in range(n):
        for j in range(n):
            got = sum(L[i][k] * D[k] * L[j][k] for k in range(n))
            assert got == A[i][j]
    return L, D


def block_sum(i: int, r: int) -> str:
    return ' + '.join(f'x{j}' for j in range(i, i + r))


def pressure_expr() -> str:
    return ' +\n  '.join(f'{qlean(v.p[i])} * x{i}' for i in range(6))


def quadratic_expr(word, intervals):
    M, b, c, used = v.build_Q(word, intervals)
    terms = [pressure_expr()]
    for i, r, N, alpha, eta, _rho in used:
        terms.append(
            f'{qlean(v.weights[r])} * '
            f'({qlean(alpha)} * ({block_sum(i, r)} - {qlean(v.q[N])}) ^ 2 '
            f'- {qlean(eta)})'
        )
    return '\n  + '.join(terms), M, b, c, used


def sos_expr(M, xstar):
    L, D = ldl_exact(M)
    squares = []
    for j in range(6):
        parts = []
        for i in range(j, 6):
            a = L[i][j]
            if a == 0:
                continue
            y = f'(x{i} - {qlean(xstar[i])})'
            if a == 1:
                parts.append(y)
            elif a == -1:
                parts.append(f'- {y}')
            else:
                parts.append(f'{qlean(a)} * {y}')
        lin = ' + '.join(parts).replace('+ - ', '- ')
        squares.append(f'{qlean(D[j])} * ({lin}) ^ 2')
    return '\n  + '.join(squares)


def emit_discard(word, intervals, round_name: str):
    qtxt, M, b, c, used = quadratic_expr(word, intervals)
    qmin, _inv, xstar = v.qmin_and_inverse(M, b, c)
    assert qmin >= v.delta
    nm = f'{round_name}_{wcode(word)}'
    sostxt = sos_expr(M, xstar)
    src = f'''/-- Exact rounded bootstrap quadratic for discarded word {wcode(word)}. -/
def v26Q_{nm} (x0 x1 x2 x3 x4 x5 : ℝ) : ℝ :=
  {qtxt}

def v26Qmin_{nm} : ℝ := {qlean(qmin)}

def v26SOS_{nm} (x0 x1 x2 x3 x4 x5 : ℝ) : ℝ :=
  {sostxt}

theorem v26_completion_{nm} (x0 x1 x2 x3 x4 x5 : ℝ) :
    v26Q_{nm} x0 x1 x2 x3 x4 x5 =
      v26Qmin_{nm} + v26SOS_{nm} x0 x1 x2 x3 x4 x5 := by
  unfold v26Q_{nm} v26Qmin_{nm} v26SOS_{nm}
  ring

theorem v26_sos_nonneg_{nm} (x0 x1 x2 x3 x4 x5 : ℝ) :
    0 ≤ v26SOS_{nm} x0 x1 x2 x3 x4 x5 := by
  unfold v26SOS_{nm}
  positivity

theorem v26_qmin_gt_delta_{nm} : v26Delta < v26Qmin_{nm} := by
  norm_num [v26Delta, v26Qmin_{nm}]

theorem v26_discard_{nm} (x0 x1 x2 x3 x4 x5 : ℝ) :
    v26Delta < v26Q_{nm} x0 x1 x2 x3 x4 x5 := by
  rw [v26_completion_{nm}]
  exact v26_qmin_gt_delta_{nm}.trans_le
    (le_add_of_nonneg_right (v26_sos_nonneg_{nm} x0 x1 x2 x3 x4 x5))
'''
    return src, qmin, len(used)


def exact_rounds():
    words511, _stats = v.enumerate_511()
    r0, d0 = v.run_round(words511, initial=True)
    r1, d1 = v.run_round(r0)
    r2, d2 = v.run_round(r1)
    assert (len(words511), len(r0), len(r1), len(r2)) == EXPECTED_CHAIN
    assert tuple(wcode(x[0]) for x in r2) == EXPECTED_FINAL
    return words511, (r0, d0), (r1, d1), (r2, d2)


def interval_map(round_name, inputs):
    if round_name == 'R0':
        return {tuple(w): v.initial_intervals(w) for w, _wt in inputs}
    return {tuple(item[0]): item[1] for item in inputs}


def write_chunks(out_dir: Path):
    words511, rd0, rd1, rd2 = exact_rounds()
    inputs_by_round = {'R0': words511, 'R1': rd0[0], 'R2': rd1[0]}
    data_by_round = {'R0': rd0, 'R1': rd1, 'R2': rd2}
    header = ('import HurtadoZeta23.V26WordBridge\n'
              'import Mathlib.Tactic\n\n'
              'noncomputable section\n\nnamespace HurtadoZeta23\n\n')
    footer = '\nend HurtadoZeta23\n'
    generated = []
    discard_manifest = {}
    for rn in ('R0', 'R1', 'R2'):
        _survivors, discards = data_by_round[rn]
        imap = interval_map(rn, inputs_by_round[rn])
        pieces = []
        codes = []
        for word, _margin, qmin_expected, nused_expected in discards:
            src, qmin, nused = emit_discard(word, imap[tuple(word)], rn)
            assert qmin == qmin_expected
            assert nused == nused_expected
            pieces.append(src)
            codes.append(wcode(word))
        discard_manifest[rn] = codes
        for start in range(0, len(pieces), CHUNK_SIZE):
            idx = start // CHUNK_SIZE
            mod = f'V26Bootstrap{rn}Chunk{idx}'
            path = out_dir / f'{mod}.lean'
            path.write_text(header + '\n'.join(pieces[start:start + CHUNK_SIZE]) + footer,
                            encoding='utf-8')
            generated.append(mod)
    agg = out_dir / 'V26BootstrapDiscardGenerated.lean'
    imports = '\n'.join(f'import HurtadoZeta23.{m}' for m in generated)
    agg.write_text(imports + '\n\nnamespace HurtadoZeta23\n\n'
                   '/-- Marker: every generated exact discard certificate compiled. -/\n'
                   'theorem v26_generated_bootstrap_discards_loaded : True := by trivial\n\n'
                   'end HurtadoZeta23\n', encoding='utf-8')
    manifest = {
        'chain': [44100, 511, 231, 23, 5],
        'discard_counts': {rn: len(codes) for rn, codes in discard_manifest.items()},
        'final_words': list(EXPECTED_FINAL),
        'modules': generated,
        'files': {},
    }
    for path in sorted(out_dir.glob('V26Bootstrap*.lean')):
        raw = path.read_bytes()
        manifest['files'][path.name] = {
            'bytes': len(raw), 'sha256': hashlib.sha256(raw).hexdigest()
        }
    (out_dir / 'v26_bootstrap_generated_manifest.json').write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + '\n', encoding='utf-8')
    return manifest


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--out-dir', required=True)
    ns = ap.parse_args()
    out = Path(ns.out_dir)
    out.mkdir(parents=True, exist_ok=True)
    manifest = write_chunks(out)
    print('EXACT GENERATION OK')
    print('chain:', ' -> '.join(map(str, manifest['chain'])))
    print('discard counts:', manifest['discard_counts'])
    print('final words:', ', '.join(manifest['final_words']))
    print('modules:', len(manifest['modules']))

if __name__ == '__main__':
    main()
