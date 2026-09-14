#!/usr/bin/env python3
"""Generate one end-to-end analytic R0 discard bridge for word 111114.

This is the scaling prototype for Package E3.  Exact analytic cell proofs are
reused from the deduplicated R0 catalog; the generated theorem only derives the
21 block bounds from the Package-D basin box, assembles them into Q <= F, and
combines that with the already kernel-checked rational discard certificate.
"""
from __future__ import annotations

from fractions import Fraction as Q
from pathlib import Path
import argparse
import importlib.util
import generate_v26_r0_cell_catalog as catalog

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


def block_name(r: int, i: int) -> str:
    return f"b{r - 1}{i}"


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


def minor_expr(N: int, alpha: Q, eta: Q, x: str) -> str:
    return f"{ql(alpha)} * (({x}) - {ql(v.q[N])}) ^ 2 - {ql(eta)}"


def assembled_lower(exprs: list[str]) -> str:
    assert len(exprs) == 21
    p = [f"({e})" for e in exprs]
    pressure = " +\n      ".join(f"v26Pressure {i} * x{i}" for i in range(6))
    return (
        pressure
        + " +\n      (1 / 3 : ℝ) * (" + " + ".join(p[0:6]) + ")"
        + " +\n      (2 / 5 : ℝ) * (" + " + ".join(p[6:11]) + ")"
        + " +\n      (1 / 2 : ℝ) * (" + " + ".join(p[11:15]) + ")"
        + " +\n      (2 / 3 : ℝ) * (" + " + ".join(p[15:18]) + ")"
        + " +\n      " + p[18] + " + " + p[19] + " + 2 * " + p[20]
    )


INTERVALS = v.initial_intervals(WORD)
_M, _b, _c, USED = v.build_Q(WORD, INTERVALS)
USED_BY_KEY = {(i, r): (N, alpha, eta) for i, r, N, alpha, eta, _rho in USED}


def emit() -> str:
    proofs = []
    exprs = []
    hnames = []
    bassign = []
    k = 0
    for r in range(1, 7):
        for i in range(7 - r):
            x = bsum(i, r)
            if (i, r) in USED_BY_KEY:
                N, alpha, eta = USED_BY_KEY[(i, r)]
                L, U = INTERVALS[(i, r)]
                key = catalog.cell_key(L, U, N, alpha, eta)
                idx = catalog.CELL_INDEX[key]
                hname = f"hm{k}"
                expr = minor_expr(N, alpha, eta, x)
                proofs.append(
                    f"  have {hname} := v26_R0_cell_{idx:03d} (x := {x})\n"
                    f"    {lower_proof(i, r)} {upper_proof(i, r)}"
                )
                k += 1
            else:
                hname = f"hn_{i}_{r}"
                expr = "0"
                proofs.append(f"  have {hname} := v26_limitingWeight_nonneg ({x})")
            exprs.append(expr)
            hnames.append(hname)
            bassign.append(f"    ({block_name(r, i)} := {expr})")

    assert len(exprs) == 21
    assert k == len(USED) == 19
    lower = assembled_lower(exprs)
    return f'''import HurtadoZeta23.V26Round0Prototype
import HurtadoZeta23.V26R0CellCatalogGenerated
import HurtadoZeta23.V26GapBlockLower
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
    v26ALo, v26AHi, v26BLo, v26BHi, v26CLo, v26CHi,
    Matrix.cons_val_succ'] at hbox
  rcases hbox with ⟨h0, h1, h2, h3, h4, h5⟩
{chr(10).join(proofs)}
  have hdom := v26_gapF_lower_of_block_lowers
    (weight := limitingWeight)
    (g0 := x0) (g1 := x1) (g2 := x2) (g3 := x3) (g4 := x4) (g5 := x5)
{chr(10).join(bassign)}
    {' '.join(hnames)}
  calc
    v26R0Q111114 x0 x1 x2 x3 x4 x5 =
      {lower} := by
        unfold v26R0Q111114
        simp [v26Pressure, Matrix.cons_val_succ']
        ring
    _ ≤ v26GapF limitingWeight x0 x1 x2 x3 x4 x5 := hdom

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
    print("used catalog minorants:", len(USED))
    print("omitted nonnegative terms:", 21 - len(USED))


if __name__ == "__main__":
    main()
