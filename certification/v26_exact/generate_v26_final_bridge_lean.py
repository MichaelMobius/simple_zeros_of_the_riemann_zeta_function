#!/usr/bin/env python3
"""Generate the final-five Lean bridge from R2 boxes to the exact quadratics.

Each final word is emitted in its own Lean module.  To keep elaboration small,
the proof is factored into:
  * 21 independent block lower-bound lemmas;
  * one exact algebraic identity Q_final = assembled lower form;
  * one purely linear assembled-form domination theorem;
  * the short Q <= F and no-counterexample consequences.

All interval data are recomputed with fractions.Fraction by the historical exact
verifier.  Python is not in the trust boundary: Lean rechecks every inequality
and every polynomial identity.
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
        f"{ql(v.W2[j])} - {ql(v.R2[j])} * (1 / 20000000 : ℝ)"
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


def box_def(intervals) -> str:
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


def emit_block_theorem(wc: str, k: int, N: int, L: Q, U: Q) -> str:
    expr = final_lower_expr(N, "x")
    return f'''/-- Final word `{wc}`, block #{k}: certified strong lower bound. -/
theorem v26_final_block_{wc}_{k:02d} {{x : ℝ}}
    (hL : {ql(L)} ≤ x) (hU : x ≤ {ql(U)}) :
    {expr} ≤ limitingWeight x := by
  exact v26_final_weight_lower_N{N} (x := x)
    (by linarith) (by linarith)
'''


def emit_word_module(w, intervals) -> tuple[str, str]:
    wc = code(w)
    block_theorems = []
    block_calls = []
    bassign = []
    lower_exprs = []
    hs = []
    hws = []
    k = 0
    for r in range(1, 7):
        for i in range(7 - r):
            N = sum(w[i:i+r])
            L, U = intervals[(i, r)]
            JL, JU = v.J[N]
            assert JL <= L <= U <= JU
            s = bsum(i, r)
            expr = final_lower_expr(N, s)
            block_theorems.append(emit_block_theorem(wc, k, N, L, U))
            block_calls.append(
                f"  have hw{k} := v26_final_block_{wc}_{k:02d} (x := {s}) h{k}.1 h{k}.2"
            )
            bassign.append(f"    ({block_name(r, i)} := {expr})")
            lower_exprs.append(expr)
            hs.append(f"h{k}")
            hws.append(f"hw{k}")
            k += 1
    assert k == 21
    lower = assembled_lower(lower_exprs)
    rcases = ", ".join(hs)

    src = '''import HurtadoZeta23.V26FinalStrongLowerGenerated
import HurtadoZeta23.V26FinalFiveMinimaGenerated
import HurtadoZeta23.V26GapBlockLower
import Mathlib.Tactic

noncomputable section
namespace HurtadoZeta23

'''
    src += f'''/-- Exact R2 contracted box for final word `{wc}`. -/
def v26FinalBox_{wc} (x0 x1 x2 x3 x4 x5 : ℝ) : Prop :=
    {box_def(intervals)}

'''
    src += "\n".join(block_theorems)
    src += f'''\n/-- The assembled 21-block strong lower form for `{wc}`. -/
def v26FinalAssembled_{wc} (x0 x1 x2 x3 x4 x5 : ℝ) : ℝ :=
  {lower}

/-- Pure algebra: the exact historical final quadratic is the assembled
strong-convexity block lower form. -/
theorem v26_final_Q_eq_assembled_{wc}
    (x0 x1 x2 x3 x4 x5 : ℝ) :
    v26FinalQ_{wc} x0 x1 x2 x3 x4 x5 =
      v26FinalAssembled_{wc} x0 x1 x2 x3 x4 x5 := by
  unfold v26FinalQ_{wc} v26FinalAssembled_{wc}
  simp [v26Pressure, Matrix.cons_val_succ']
  ring

/-- The assembled lower form is below the actual six-gap functional on the
exact R2 box.  This theorem uses only the 21 already-certified block bounds
and the generic positive-weight assembly lemma. -/
theorem v26_final_assembled_le_gapF_{wc}
    (x0 x1 x2 x3 x4 x5 : ℝ)
    (hbox : v26FinalBox_{wc} x0 x1 x2 x3 x4 x5) :
    v26FinalAssembled_{wc} x0 x1 x2 x3 x4 x5 ≤
      v26GapF limitingWeight x0 x1 x2 x3 x4 x5 := by
  rcases hbox with ⟨{rcases}⟩
{chr(10).join(block_calls)}
  unfold v26FinalAssembled_{wc}
  exact v26_gapF_lower_of_block_lowers
    (weight := limitingWeight)
    (g0 := x0) (g1 := x1) (g2 := x2) (g3 := x3) (g4 := x4) (g5 := x5)
{chr(10).join(bassign)}
    {' '.join(hws)}

/-- On the exact R2 box, the historical final quadratic is below the actual
six-gap functional. -/
theorem v26_final_Q_le_gapF_{wc}
    (x0 x1 x2 x3 x4 x5 : ℝ)
    (hbox : v26FinalBox_{wc} x0 x1 x2 x3 x4 x5) :
    v26FinalQ_{wc} x0 x1 x2 x3 x4 x5 ≤
      v26GapF limitingWeight x0 x1 x2 x3 x4 x5 := by
  rw [v26_final_Q_eq_assembled_{wc}]
  exact v26_final_assembled_le_gapF_{wc} x0 x1 x2 x3 x4 x5 hbox

/-- The exact R2 box for `{wc}` contains no strict counterexample. -/
theorem v26_no_counterexample_final_{wc}
    (x0 x1 x2 x3 x4 x5 : ℝ)
    (hbox : v26FinalBox_{wc} x0 x1 x2 x3 x4 x5) :
    ¬ v26GapF limitingWeight x0 x1 x2 x3 x4 x5 < v26Delta := by
  intro hbad
  have hdom := v26_final_Q_le_gapF_{wc} x0 x1 x2 x3 x4 x5 hbox
  have hQ := v26_final_Q_gt_delta_{wc} x0 x1 x2 x3 x4 x5
  linarith

end HurtadoZeta23
'''
    return f"V26FinalBridge{wc}Generated", src


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--out-dir", required=True)
    ns = ap.parse_args()
    out = Path(ns.out_dir)
    out.mkdir(parents=True, exist_ok=True)

    modules = []
    r2 = final_survivors()
    for w, intervals, _qmin, _nused in r2:
        name, src = emit_word_module(w, intervals)
        (out / f"{name}.lean").write_text(src, encoding="utf-8")
        modules.append(name)

    agg = "\n".join(f"import HurtadoZeta23.{name}" for name in modules)
    agg += '''

namespace HurtadoZeta23
/-- Marker: all five final analytic bridges compiled. -/
theorem v26_final_bridges_loaded : True := by trivial
end HurtadoZeta23
'''
    (out / "V26FinalBridgeGenerated.lean").write_text(agg, encoding="utf-8")
    print("FINAL FIVE BRIDGE GENERATION OK")
    print("words:", ", ".join(code(x[0]) for x in r2))
    print("modules:", len(modules))


if __name__ == "__main__":
    main()
