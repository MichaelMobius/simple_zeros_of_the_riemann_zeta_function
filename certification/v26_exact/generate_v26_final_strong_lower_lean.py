#!/usr/bin/env python3
"""Generate the ten Lean strong-convexity lower bounds for the final J-cells.

This generator contains no floating-point computation.  It only serializes the
published rational tables and composes already kernel-checked theorems:
  * v26_curvature_Nk
  * v26_anchor_weight_Nk
  * v26_anchor_deriv_Nk
  * v26_limitingWeight_strong_lower

The generated Lean file is the proof object; Python is not part of the trust
boundary.
"""
from __future__ import annotations

from fractions import Fraction as Q
from pathlib import Path
import argparse

J = [None,
     (Q(1023,1000),Q(1061,1000)), (Q(1950,1000),Q(2018,1000)),
     (Q(2991,1000),Q(3061,1000)), (Q(3950,1000),Q(4084,1000)),
     (Q(4962,1000),Q(5050,1000)), (Q(5975,1000),Q(6086,1000)),
     (Q(6967,1000),Q(7101,1000)), (Q(7993,1000),Q(8080,1000)),
     (Q(9013,1000),Q(9108,1000)), (Q(10025,1000),Q(10078,1000))]

M = [None,
     Q(37,25), Q(723,2000), Q(17,125), Q(173,2500), Q(507,10000),
     Q(31,1000), Q(213,10000), Q(181,10000), Q(1,80), Q(117,10000)]

A = [None,
     Q(1043,1000), Q(1984,1000), Q(3026,1000), Q(4018,1000),
     Q(5004,1000), Q(6045,1000), Q(7034,1000), Q(8036,1000),
     Q(9074,1000), Q(10052,1000)]

W = [None,
     Q(16195,100_000_000), Q(39121,100_000_000), Q(254,100_000_000),
     Q(32,100_000_000), Q(186,100_000_000), Q(2278,100_000_000),
     Q(886,100_000_000), Q(853,100_000_000), Q(3712,100_000_000),
     Q(1420,100_000_000)]

D = [None,
     Q(-230346,10_000_000), Q(-172761,10_000_000), Q(8840,10_000_000),
     Q(2381,10_000_000), Q(-4542,10_000_000), Q(12962,10_000_000),
     Q(6976,10_000_000), Q(5985,10_000_000), Q(10801,10_000_000),
     Q(6120,10_000_000)]

R = [None,
     Q(20,1000), Q(34,1000), Q(35,1000), Q(68,1000), Q(46,1000),
     Q(70,1000), Q(67,1000), Q(44,1000), Q(61,1000), Q(27,1000)]

EPS = Q(1, 20_000_000)


def ql(x: Q) -> str:
    x = Q(x)
    if x.denominator == 1:
        return str(x.numerator)
    return f"({x.numerator} / {x.denominator} : ℝ)"


def theorem(N: int) -> str:
    L, U = J[N]
    return f'''/-- Certified historical strong-convexity lower bound on J_{N}. -/
theorem v26_final_weight_lower_N{N} {{x : ℝ}}
    (hL : {ql(L)} ≤ x) (hU : x ≤ {ql(U)}) :
    {ql(W[N])} - {ql(R[N])} * {ql(EPS)} +
        {ql(D[N])} * (x - {ql(A[N])}) +
        ({ql(M[N])} / 2) * (x - {ql(A[N])}) ^ 2 ≤ limitingWeight x := by
  apply v26_limitingWeight_strong_lower
    (L := {ql(L)}) (U := {ql(U)})
    (a := {ql(A[N])}) (m := {ql(M[N])})
    (W := {ql(W[N])}) (D := {ql(D[N])})
    (eps := {ql(EPS)}) (R := {ql(R[N])})
  · norm_num
  · constructor <;> norm_num
  · exact ⟨hL, hU⟩
  · intro y hy
    exact v26_curvature_N{N} hy.1 hy.2
  · exact v26_anchor_weight_N{N}
  · exact v26_anchor_deriv_N{N}
  · norm_num
  · norm_num
  · rw [abs_le]
    constructor <;> linarith
'''


def write(out_dir: Path) -> None:
    out_dir.mkdir(parents=True, exist_ok=True)
    src = '''import HurtadoZeta23.V26FinalNumericGenerated
import HurtadoZeta23.V26StrongConvexityTransfer
import Mathlib.Tactic

noncomputable section
namespace HurtadoZeta23

'''
    src += "\n".join(theorem(N) for N in range(1, 11))
    src += '''
/-- Marker: all ten final-cell strong-convexity lower bounds compiled. -/
theorem v26_final_strong_lower_loaded : True := by trivial

end HurtadoZeta23
'''
    (out_dir / "V26FinalStrongLowerGenerated.lean").write_text(src, encoding="utf-8")


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--out-dir", required=True)
    ns = ap.parse_args()
    write(Path(ns.out_dir))
    print("FINAL STRONG LOWER GENERATION OK")
    print("cells: 10")


if __name__ == "__main__":
    main()
