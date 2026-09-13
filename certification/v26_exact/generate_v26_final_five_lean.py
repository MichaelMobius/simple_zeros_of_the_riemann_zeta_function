#!/usr/bin/env python3
"""Generate kernel-checkable Lean certificates for the five final v26 quadratics.

All arithmetic used to construct the quadratic forms and stationary points is
exact `fractions.Fraction` arithmetic.  The generated Lean files recheck each
completion-of-squares identity with `ring`, nonnegativity with `positivity`,
and the strict rational margin with `norm_num`.
"""
from __future__ import annotations
from fractions import Fraction as Q
from pathlib import Path
import argparse, importlib.util, json, hashlib

HERE = Path(__file__).resolve().parent
VERIFIER = HERE / "v21_rational_bootstrap_verify.py"


def load_verifier():
    spec = importlib.util.spec_from_file_location("v21_exact_final", VERIFIER)
    if spec is None or spec.loader is None:
        raise RuntimeError("cannot load exact verifier")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


v = load_verifier()
FINAL_WORDS = [
    (1, 2, 1, 2, 1, 2),
    (1, 2, 1, 2, 2, 1),
    (1, 2, 2, 1, 2, 1),
    (2, 1, 2, 1, 2, 1),
    (2, 1, 2, 2, 1, 2),
]


def qlean(x: Q) -> str:
    x = Q(x)
    if x.denominator == 1:
        return str(x.numerator)
    return f"({x.numerator} / {x.denominator} : ℝ)"


def wcode(w) -> str:
    return "".join(map(str, w))


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
            L[i][j] = (
                A[i][j] - sum(L[i][k] * L[j][k] * D[k] for k in range(j))
            ) / D[j]
    for i in range(n):
        for j in range(n):
            assert sum(L[i][k] * D[k] * L[j][k] for k in range(n)) == A[i][j]
    return L, D


def sos_expr(M, xstar):
    L, D = ldl_exact(M)
    squares = []
    for j in range(6):
        parts = []
        for i in range(j, 6):
            a = L[i][j]
            if a == 0:
                continue
            y = f"(x{i} - {qlean(xstar[i])})"
            if a == 1:
                parts.append(y)
            elif a == -1:
                parts.append(f"- {y}")
            else:
                parts.append(f"{qlean(a)} * {y}")
        lin = " + ".join(parts).replace("+ - ", "- ")
        squares.append(f"{qlean(D[j])} * ({lin}) ^ 2")
    return "\n  + ".join(squares)


def pressure_expr():
    return " +\n  ".join(f"{qlean(v.p[i])} * x{i}" for i in range(6))


def block_sum(i, r):
    return " + ".join(f"x{j}" for j in range(i, i + r))


def final_L_expr(N, s):
    j = N - 1
    return (
        f"{qlean(v.W2[j])} - {qlean(v.R2[j])} / 20000000"
        f" + {qlean(v.D2[j])} * (({s}) - {qlean(v.a2[j])})"
        f" + ({qlean(v.m2[j])} / 2) * (({s}) - {qlean(v.a2[j])}) ^ 2"
    )


def final_quadratic(word):
    M = [[Q(0) for _ in range(6)] for _ in range(6)]
    b = [v.p[i] / 2 for i in range(6)]
    c = Q(0)
    terms = [pressure_expr()]
    for r in range(1, 7):
        for i in range(7 - r):
            N = sum(word[i : i + r])
            s = block_sum(i, r)
            terms.append(f"{qlean(v.weights[r])} * ({final_L_expr(N, s)})")
            c = v.add_final_L(M, b, c, list(range(i, i + r)), N, v.weights[r])
    qmin, _inv, xstar = v.qmin_and_inverse(M, b, c)
    return "\n  + ".join(terms), M, qmin, xstar


def emit_word(word):
    code = wcode(word)
    qtxt, M, qmin, xstar = final_quadratic(word)
    margin = qmin - v.delta
    assert margin == v.final_margin(word)
    assert margin > Q(1, 2_000_000)
    sostxt = sos_expr(M, xstar)
    src = f'''/-- Final strong-convexity rational quadratic for word `{code}`. -/
def v26FinalQ_{code} (x0 x1 x2 x3 x4 x5 : ℝ) : ℝ :=
  {qtxt}

def v26FinalQmin_{code} : ℝ := {qlean(qmin)}

def v26FinalSOS_{code} (x0 x1 x2 x3 x4 x5 : ℝ) : ℝ :=
  {sostxt}

theorem v26_final_completion_{code} (x0 x1 x2 x3 x4 x5 : ℝ) :
    v26FinalQ_{code} x0 x1 x2 x3 x4 x5 =
      v26FinalQmin_{code} + v26FinalSOS_{code} x0 x1 x2 x3 x4 x5 := by
  unfold v26FinalQ_{code} v26FinalQmin_{code} v26FinalSOS_{code}
  ring

theorem v26_final_sos_nonneg_{code} (x0 x1 x2 x3 x4 x5 : ℝ) :
    0 ≤ v26FinalSOS_{code} x0 x1 x2 x3 x4 x5 := by
  unfold v26FinalSOS_{code}
  positivity

theorem v26_final_qmin_margin_{code} :
    v26Delta + (1 / 2000000 : ℝ) < v26FinalQmin_{code} := by
  norm_num [v26Delta, v26FinalQmin_{code}]

theorem v26_final_Q_margin_{code} (x0 x1 x2 x3 x4 x5 : ℝ) :
    v26Delta + (1 / 2000000 : ℝ) <
      v26FinalQ_{code} x0 x1 x2 x3 x4 x5 := by
  rw [v26_final_completion_{code}]
  exact v26_final_qmin_margin_{code}.trans_le
    (le_add_of_nonneg_right (v26_final_sos_nonneg_{code} x0 x1 x2 x3 x4 x5))

theorem v26_final_Q_gt_delta_{code} (x0 x1 x2 x3 x4 x5 : ℝ) :
    v26Delta < v26FinalQ_{code} x0 x1 x2 x3 x4 x5 := by
  have h := v26_final_Q_margin_{code} x0 x1 x2 x3 x4 x5
  norm_num [v26Delta] at h ⊢
  linarith

'''
    return src, margin


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out-dir", required=True)
    ns = ap.parse_args()
    out = Path(ns.out_dir)
    out.mkdir(parents=True, exist_ok=True)
    header = '''import HurtadoZeta23.V26WordBridge
import Mathlib.Tactic

noncomputable section

namespace HurtadoZeta23

'''
    footer = '''end HurtadoZeta23
'''
    modules = []
    manifest = {"final_words": [], "margins": {}, "files": {}}
    for word in FINAL_WORDS:
        src, margin = emit_word(word)
        code = wcode(word)
        mod = f"V26FinalFive_{code}"
        path = out / f"{mod}.lean"
        path.write_text(header + src + footer, encoding="utf-8")
        modules.append(mod)
        manifest["final_words"].append(code)
        manifest["margins"][code] = f"{margin.numerator}/{margin.denominator}"
    agg = out / "V26FinalFiveMinimaGenerated.lean"
    agg.write_text(
        "\n".join(f"import HurtadoZeta23.{m}" for m in modules)
        + "\n\nnamespace HurtadoZeta23\n\n"
        + "/-- Marker: all five exact final quadratic minima compiled. -/\n"
        + "theorem v26_final_five_minima_loaded : True := by trivial\n\n"
        + "end HurtadoZeta23\n",
        encoding="utf-8",
    )
    for path in sorted(out.glob("V26FinalFive*.lean")):
        raw = path.read_bytes()
        manifest["files"][path.name] = {
            "bytes": len(raw),
            "sha256": hashlib.sha256(raw).hexdigest(),
        }
    (out / "v26_final_five_generated_manifest.json").write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    print("FINAL FIVE EXACT GENERATION OK")
    for word in FINAL_WORDS:
        code = wcode(word)
        print(code, manifest["margins"][code])


if __name__ == "__main__":
    main()
