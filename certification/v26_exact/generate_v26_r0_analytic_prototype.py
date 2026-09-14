#!/usr/bin/env python3
"""Generate one end-to-end analytic R0 discard bridge for word 111114.

This is the scaling prototype for Package E3.  All interval/minorant data are
recomputed with the exact historical verifier.  Python only serializes the
certificate: Lean rechecks every rational cell obligation, Q <= F, and the
contradiction with the already kernel-checked rational discard theorem.
"""
from __future__ import annotations

from fractions import Fraction as Q
from pathlib import Path
import argparse
import importlib.util

HERE = Path(__file__).resolve().parent
VERIFIER = HERE / "v21_rational_bootstrap_verify.py"
WORD = (1, 1, 1, 1, 1, 4)


def load_verifier():
    spec = importlib.util.spec_from_file_location("v26_e3_proto", VERIFIER)
    if spec is None or spec.loader is None:
        raise RuntimeError("cannot load exact verifier")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


v = load_verifier()


def ql(x: Q) -> str:
    x = Q(x)
    if x.denominator == 1:
        return str(x.numerator)
    return f"({x.numerator} / {x.denominator} : ℝ)"


def bsum(i: int, r: int) -> str:
    return " + ".join(f"x{j}" for j in range(i, i + r))


def lower_proof(i: int, r: int) -> str:
    hs = ", ".join(f"h{j}.1" for j in range(i, i + r))
    return f"(by linarith [{hs}])"


def upper_proof(i: int, r: int) -> str:
    hs = ", ".join(f"h{j}.2" for j in range(i, i + r))
    return f"(by linarith [{hs}])"


def word_type() -> str:
    vals = [0, 0, 0, 0, 0, 3]
    tys = [7, 5, 6, 6, 5, 7]
    return "(" + ", ".join(f"({a} : Fin {n})" for a, n in zip(vals, tys)) + ")"


def emit_minor(k: int, item) -> str:
    i, r, N, alpha, eta, _rho = item
    L, U = INTERVALS[(i, r)]
    x = bsum(i, r)
    low = lower_proof(i, r)
    up = upper_proof(i, r)
    hard = lower_proof(i, r)
    return f'''  have hm{k} :
      {ql(alpha)} * ({x} - {ql(v.q[N])}) ^ 2 - {ql(eta)} ≤
        limitingWeight ({x}) := by
    apply v26_certified_cell_minorant
      (N := {N}) (L := {ql(L)}) (U := {ql(U)}) (x := {x})
      (alpha := {ql(alpha)}) (eta := {ql(eta)})
      (by norm_num) (by norm_num) {hard} {low} {up}
    all_goals norm_num [v26CellLstar, v26CellEps, v26CellRho, v26Mrat, v21RootRight,
      v26Araw, v26AmplitudeFloor, v26ChordCoeff, v26Fold, v26P7, v26d0]
'''


INTERVALS = v.initial_intervals(WORD)
_M, _b, _c, USED = v.build_Q(WORD, INTERVALS)
USED_KEYS = {(i, r) for i, r, *_ in USED}


def emit() -> str:
    minors = "\n".join(emit_minor(k, item) for k, item in enumerate(USED))
    omitted = []
    for r in range(1, 7):
        for i in range(7 - r):
            if (i, r) not in USED_KEYS:
                x = bsum(i, r)
                omitted.append(
                    f"  have hn_{i}_{r} := v26_limitingWeight_nonneg ({x})"
                )
    hm_names = ", ".join(f"hm{k}" for k in range(len(USED)))
    hn_names = ", ".join(f"hn_{i}_{r}" for r in range(1, 7)
                         for i in range(7 - r) if (i, r) not in USED_KEYS)
    extra = hm_names + (", " + hn_names if hn_names else "")
    return f'''import HurtadoZeta23.V26Round0Prototype
import HurtadoZeta23.V26OneBodyCellTools
import HurtadoZeta23.V26BasinInterface
import Mathlib.Tactic

noncomputable section
namespace HurtadoZeta23

/-- Concrete A-B-C-C-B-A word with published code 111114. -/
def v26E3Word111114 : V26BasinWord := {word_type()}

/-- The historical rounded R0 quadratic is an analytic lower bound for the
actual six-gap functional throughout the Package-D basin box. -/
theorem v26_E3_R0_111114_Q_le_gapF
    (x0 x1 x2 x3 x4 x5 : ℝ)
    (hbox : v26InWordBox v26E3Word111114 x0 x1 x2 x3 x4 x5) :
    v26R0Q111114 x0 x1 x2 x3 x4 x5 ≤
      v26GapF limitingWeight x0 x1 x2 x3 x4 x5 := by
  norm_num [v26InWordBox, v26E3Word111114,
    v26InA, v26InB, v26InC,
    v26ALo, v26AHi, v26BLo, v26BHi, v26CLo, v26CHi] at hbox
  rcases hbox with ⟨h0, h1, h2, h3, h4, h5⟩
{minors}
{chr(10).join(omitted)}
  unfold v26R0Q111114 v26GapF
  simp [v26Pressure, Matrix.cons_val_succ']
  linarith [{extra}]

/-- Hence the discarded word 111114 contains no strict counterexample. -/
theorem v26_E3_R0_111114_no_counterexample
    (x0 x1 x2 x3 x4 x5 : ℝ)
    (hbox : v26InWordBox v26E3Word111114 x0 x1 x2 x3 x4 x5) :
    ¬ v26GapF limitingWeight x0 x1 x2 x3 x4 x5 < v26Delta := by
  intro hbad
  have hdom := v26_E3_R0_111114_Q_le_gapF x0 x1 x2 x3 x4 x5 hbox
  have hdiscard := v26_R0_111114_discard x0 x1 x2 x3 x4 x5
  linarith

end HurtadoZeta23
'''


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--out-dir", required=True)
    ns = ap.parse_args()
    out = Path(ns.out_dir)
    out.mkdir(parents=True, exist_ok=True)
    src = emit()
    path = out / "V26Round0AnalyticPrototypeGenerated.lean"
    path.write_text(src, encoding="utf-8")
    print("E3 R0 ANALYTIC PROTOTYPE GENERATION OK")
    print("word: 111114")
    print("used minorants:", len(USED))
    print("omitted nonnegative terms:", 21 - len(USED))


if __name__ == "__main__":
    main()
