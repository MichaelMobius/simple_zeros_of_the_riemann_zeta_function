#!/usr/bin/env python3
"""Generate the final-five Lean bridge from R2 boxes to the exact quadratics.

For each of the five final words this emits:
  * the exact contracted 21-block-sum box from the rational bootstrap;
  * Q_final <= v26GapF limitingWeight on that box, using the ten strong
    convexity lower bounds;
  * impossibility of v26GapF < delta on that box, using the already
    kernel-checked exact final quadratic margin.

All box data are recomputed with fractions.Fraction by the historical exact
verifier. Lean rechecks the actual inequalities.  The final assembly is split
into a generic symbolic positive weighted sum and a `ring` identity, avoiding
large nonlinear arithmetic search.
"""
from __future__ import annotations

from fractions import Fraction as Q
from pathlib import Path
import argparse
import importlib.util

HERE = Path(__file__).resolve().parent
VERIFIER = HERE / "v21_rational_bootstrap_verify.py"


def load_verifier():
    spec = importlib.util.spec_from_file_location("v26_bridge_verifier", VERIFIER)
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


def code(w) -> str:
    return "".join(map(str, w))


def bsum(i: int, r: int) -> str:
    return " + ".join(f"x{j}" for j in range(i, i + r))


def block_name(r: int, i: int) -> str:
    return f"b{r - 1}{i}"


def final_lower_expr(N: int, s: str) -> str:
    j = N - 1
    return (
        f"{ql(v.W2[j])} - {ql(v.R2[j])} / 20000000"
        f" + {ql(v.D2[j])} * (({s}) - {ql(v.a2[j])})"
        f" + ({ql(v.m2[j])} / 2) * (({s}) - {ql(v.a2[j])}) ^ 2"
    )


def final_survivors():
    words511, _ = v.enumerate_511()
    r0, _ = v.run_round(words511, initial=True)
    r1, _ = v.run_round(r0)
    r2, _ = v.run_round(r1)
    assert len(r2) == 5
    return r2


def box_def(w, intervals) -> str:
    pieces = []
    for r in range(1, 7):
        for i in range(7 - r):
            L, U = intervals[(i, r)]
            s = bsum(i, r)
            pieces.append(f"({ql(L)} ≤ {s} ∧ {s} ≤ {ql(U)})")
    return " ∧\n    ".join(pieces)


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


def emit_word(w, intervals) -> str:
    wc = code(w)
    hs = []
    strong = []
    bassign = []
    lower_exprs = []
    k = 0
    for r in range(1, 7):
        for i in range(7 - r):
            N = sum(w[i:i+r])
            L, U = intervals[(i, r)]
            JL, JU = v.J[N]
            assert JL <= L <= U <= JU
            s = bsum(i, r)
            expr = final_lower_expr(N, s)
            hs.append(f"h{k}")
            lower_exprs.append(expr)
            bassign.append(f"    ({block_name(r, i)} := {expr})")
            strong.append(
                f"  have hw{k} := v26_final_weight_lower_N{N} (x := {s})\n"
                f"    (by linarith [h{k}.1]) (by linarith [h{k}.2])"
            )
            k += 1
    assert k == 21
    rcases = ", ".join(hs)
    hws = " ".join(f"hw{i}" for i in range(21))
    lower = assembled_lower(lower_exprs)
    return f'''/-- Exact R2 contracted box for final word `{wc}`. -/
def v26FinalBox_{wc} (x0 x1 x2 x3 x4 x5 : ℝ) : Prop :=
    {box_def(w, intervals)}

/-- On the exact R2 box, the final strong-convexity quadratic is a lower
bound for the six-gap functional.  The 21 nonlinear block estimates are first
assembled by the generic symbolic positive-weight lemma, then the historical
quadratic is identified with that assembly by `ring`. -/
theorem v26_final_Q_le_gapF_{wc}
    (x0 x1 x2 x3 x4 x5 : ℝ)
    (hbox : v26FinalBox_{wc} x0 x1 x2 x3 x4 x5) :
    v26FinalQ_{wc} x0 x1 x2 x3 x4 x5 ≤
      v26GapF limitingWeight x0 x1 x2 x3 x4 x5 := by
  rcases hbox with ⟨{rcases}⟩
{chr(10).join(strong)}
  have hdom := v26_gapF_lower_of_block_lowers
    (weight := limitingWeight)
    (g0 := x0) (g1 := x1) (g2 := x2) (g3 := x3) (g4 := x4) (g5 := x5)
{chr(10).join(bassign)}
    {hws}
  calc
    v26FinalQ_{wc} x0 x1 x2 x3 x4 x5 =
      {lower} := by
        unfold v26FinalQ_{wc}
        simp [v26Pressure, Matrix.cons_val_succ']
        ring
    _ ≤ v26GapF limitingWeight x0 x1 x2 x3 x4 x5 := hdom

/-- The exact R2 box for `{wc}` contains no strict counterexample. -/
theorem v26_no_counterexample_final_{wc}
    (x0 x1 x2 x3 x4 x5 : ℝ)
    (hbox : v26FinalBox_{wc} x0 x1 x2 x3 x4 x5) :
    ¬ v26GapF limitingWeight x0 x1 x2 x3 x4 x5 < v26Delta := by
  intro hbad
  have hdom := v26_final_Q_le_gapF_{wc} x0 x1 x2 x3 x4 x5 hbox
  have hQ := v26_final_Q_gt_delta_{wc} x0 x1 x2 x3 x4 x5
  linarith
'''


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--out-dir", required=True)
    ns = ap.parse_args()
    out = Path(ns.out_dir)
    out.mkdir(parents=True, exist_ok=True)

    r2 = final_survivors()
    imports = [
        "import HurtadoZeta23.V26FinalStrongLowerGenerated",
        "import HurtadoZeta23.V26FinalFiveMinimaGenerated",
        "import HurtadoZeta23.V26GapBlockLower",
        "import Mathlib.Tactic",
    ]
    src = "\n".join(imports) + "\n\nnoncomputable section\nnamespace HurtadoZeta23\n\n"
    for w, intervals, _qmin, _nused in r2:
        src += emit_word(w, intervals) + "\n"
    src += "/-- Marker: all five final analytic bridges compiled. -/\n"
    src += "theorem v26_final_bridges_loaded : True := by trivial\n\n"
    src += "end HurtadoZeta23\n"
    (out / "V26FinalBridgeGenerated.lean").write_text(src, encoding="utf-8")
    print("FINAL FIVE BRIDGE GENERATION OK")
    print("words:", ", ".join(code(x[0]) for x in r2))


if __name__ == "__main__":
    main()
