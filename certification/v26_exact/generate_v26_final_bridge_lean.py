#!/usr/bin/env python3
"""Generate the final-five Lean bridge from R2 boxes to the exact quadratics.

For each of the five final words this emits:
  * the exact contracted 21-block-sum box from the rational bootstrap;
  * Q_final <= v26GapF limitingWeight on that box, using the ten strong
    convexity lower bounds;
  * impossibility of v26GapF < delta on that box, using the already
    kernel-checked exact final quadratic margin.

All box data are recomputed with fractions.Fraction by the historical exact
verifier.  Lean rechecks the actual inequalities.
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


def emit_word(w, intervals) -> str:
    wc = code(w)
    hs = []
    strong = []
    k = 0
    for r in range(1, 7):
        for i in range(7 - r):
            N = sum(w[i:i+r])
            L, U = intervals[(i, r)]
            JL, JU = v.J[N]
            assert JL <= L <= U <= JU
            s = bsum(i, r)
            hs.append(f"h{k}")
            strong.append(
                f"  have hw{k} := v26_final_weight_lower_N{N} (x := {s})\n"
                f"    (by linarith [h{k}.1]) (by linarith [h{k}.2])"
            )
            k += 1
    assert k == 21
    rcases = ", ".join(hs)
    hws = ", ".join(f"hw{i}" for i in range(21))
    return f'''/-- Exact R2 contracted box for final word `{wc}`. -/
def v26FinalBox_{wc} (x0 x1 x2 x3 x4 x5 : ℝ) : Prop :=
    {box_def(w, intervals)}

/-- On the exact R2 box, the final strong-convexity quadratic is a lower
bound for the six-gap functional.  After the 21 block lower bounds are
instantiated, this is a purely linear positive weighted sum of inequalities. -/
theorem v26_final_Q_le_gapF_{wc}
    (x0 x1 x2 x3 x4 x5 : ℝ)
    (hbox : v26FinalBox_{wc} x0 x1 x2 x3 x4 x5) :
    v26FinalQ_{wc} x0 x1 x2 x3 x4 x5 ≤
      v26GapF limitingWeight x0 x1 x2 x3 x4 x5 := by
  rcases hbox with ⟨{rcases}⟩
{chr(10).join(strong)}
  unfold v26FinalQ_{wc} v26GapF
  simp [v26Pressure, Matrix.cons_val_succ']
  linarith [{hws}]

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
