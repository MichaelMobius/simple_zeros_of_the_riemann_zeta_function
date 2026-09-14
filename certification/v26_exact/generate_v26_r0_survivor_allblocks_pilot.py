#!/usr/bin/env python3
"""Extend the first R0 survivor pilot from x0 to all 21 block functionals.

This generator deliberately imports the already kernel-checked one-block pilot
and adds one small contraction theorem per consecutive block.  Every radius,
center and final interval is recomputed with exact Fraction arithmetic and
asserted equal to the historical R0 contraction table before Lean code is
emitted.
"""
from __future__ import annotations

from fractions import Fraction as Q
from pathlib import Path
import argparse

import generate_v26_r0_survivor_pilot as pilot

v = pilot.v
ql = pilot.ql
bsum = pilot.bsum
z_expr = pilot.z_expr
forward_solve_unit_lower = pilot.forward_solve_unit_lower


def contraction_data(intervals, contracted, inv, xstar, L, D, gap, i, r):
    ell = [Q(1) if i <= j < i + r else Q(0) for j in range(6)]
    a = forward_solve_unit_lower(L, ell)
    invell = v.matvec(inv, ell)
    coeff = sum((a[j] * a[j] / D[j] for j in range(6)), Q(0))
    assert coeff == v.dot(ell, invell)
    rad2 = gap * coeff
    radius = v.sqrt_upper_rational(rad2, 10_000)
    center = v.dot(ell, xstar)
    oldL, oldU = intervals[(i, r)]
    lo0 = v.floor_frac(center - radius, 10_000)
    hi0 = v.ceil_frac(center + radius, 10_000)
    expected = (max(oldL, lo0), min(oldU, hi0))
    assert expected == contracted[(i, r)]
    assert rad2 < radius * radius
    return ell, a, rad2, radius, center, oldL, oldU, expected


def energy_expr(D, z):
    return " +\n      ".join(f"{ql(D[j])} * ({z[j]}) ^ 2" for j in range(6))


def emit_contraction(i, r, intervals, contracted, inv, xstar, L, D, gap, z):
    _ell, a, rad2, radius, center, oldL, oldU, (newL, newU) = contraction_data(
        intervals, contracted, inv, xstar, L, D, gap, i, r)
    s = bsum(i, r)
    lin = " + ".join(f"{ql(a[j])} * ({z[j]})" for j in range(6))
    coeff = " + ".join(f"({ql(a[j])}) ^ 2 / {ql(D[j])}" for j in range(6))
    cauchy_args = "\n".join(
        [f"    (a{j} := {ql(a[j])})" for j in range(6)]
        + [f"    (y{j} := {z[j]})" for j in range(6)]
        + [f"    (d{j} := {ql(D[j])})" for j in range(6)]
        + [f"    (gap := {ql(gap)})"]
    )
    involved_l = ", ".join(f"h{j}.1" for j in range(i, i + r))
    involved_u = ", ".join(f"h{j}.2" for j in range(i, i + r))
    return f'''theorem v26_E3_R0_survivor_pilot_contract_b{r-1}{i}
    (x0 x1 x2 x3 x4 x5 : ℝ)
    (hbox : v26InWordBox v26E3R0SurvivorPilotWord x0 x1 x2 x3 x4 x5)
    (hbad : v26GapF limitingWeight x0 x1 x2 x3 x4 x5 < v26Delta) :
    {ql(newL)} ≤ ({s}) ∧ ({s}) ≤ {ql(newU)} := by
  have hsoslt := v26_E3_R0_survivor_pilot_energy_lt x0 x1 x2 x3 x4 x5 hbox hbad
  have henergy :
      {energy_expr(D, z)} ≤ {ql(gap)} := by
    have h := le_of_lt hsoslt
    simpa [v26E3R0SurvivorPilotSOS] using h
  have hcs := v26_weighted_cauchy6_of_energy
{cauchy_args}
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    henergy
  have hsq : (({s}) - {ql(center)}) ^ 2 ≤ {ql(rad2)} := by
    calc
      (({s}) - {ql(center)}) ^ 2 = ({lin}) ^ 2 := by ring
      _ ≤ {ql(gap)} * ({coeff}) := hcs
      _ = {ql(rad2)} := by norm_num
  have habs : |({s}) - {ql(center)}| < {ql(radius)} := by
    exact v26_abs_lt_radius_of_sq_le
      (z := ({s}) - {ql(center)}) (rad2 := {ql(rad2)}) (R := {ql(radius)})
      (by norm_num) hsq (by norm_num)
  have hbox' := hbox
  simp [v26InWordBox, v26E3R0SurvivorPilotWord,
    v26InA, v26InB, v26InC,
    v26ALo, v26AHi, v26BLo, v26BHi, v26CLo, v26CHi] at hbox'
  norm_num at hbox'
  rcases hbox' with ⟨h0, h1, h2, h3, h4, h5⟩
  have holdL : {ql(oldL)} ≤ ({s}) := by linarith [{involved_l}]
  have holdU : ({s}) ≤ {ql(oldU)} := by linarith [{involved_u}]
  have hr := abs_lt.mp habs
  constructor <;> linarith [holdL, holdU, hr.1, hr.2]
'''


def emit():
    (word, intervals, contracted, _qtxt, M, b, c, used, qmin, xstar,
     L, D, _a0, gap, _rad20, _radius0, _center0) = pilot.pilot_data()
    qmin2, inv, xstar2 = v.qmin_and_inverse(M, b, c)
    assert qmin2 == qmin and xstar2 == xstar
    z = [z_expr(L, xstar, j) for j in range(6)]

    theorems = []
    names = []
    conjuncts = []
    for r in range(1, 7):
        for i in range(7 - r):
            theorems.append(emit_contraction(
                i, r, intervals, contracted, inv, xstar, L, D, gap, z))
            nm = f"v26_E3_R0_survivor_pilot_contract_b{r-1}{i}"
            names.append(nm)
            s = bsum(i, r)
            lo, hi = contracted[(i, r)]
            conjuncts.append(f"({ql(lo)} ≤ ({s}) ∧ ({s}) ≤ {ql(hi)})")

    prop = " ∧\n    ".join(conjuncts)
    calls = []
    for idx, nm in enumerate(names):
        calls.append(
            f"  have hc{idx:02d} := {nm} x0 x1 x2 x3 x4 x5 hbox hbad")
    tuple_terms = ", ".join(f"hc{idx:02d}" for idx in range(len(names)))

    return f'''import HurtadoZeta23.V26R0SurvivorPilotGenerated
import Mathlib.Tactic

noncomputable section
namespace HurtadoZeta23

{chr(10).join(theorems)}

/-- Exact historical R0 contracted 21-block box for survivor {pilot.wcode(word)}. -/
def v26E3R0SurvivorPilotContractedBox
    (x0 x1 x2 x3 x4 x5 : ℝ) : Prop :=
    {prop}

/-- The first R0 survivor contracts, under the strict-counterexample
hypothesis, to exactly the full 21-block historical box. -/
theorem v26_E3_R0_survivor_pilot_contract_all
    (x0 x1 x2 x3 x4 x5 : ℝ)
    (hbox : v26InWordBox v26E3R0SurvivorPilotWord x0 x1 x2 x3 x4 x5)
    (hbad : v26GapF limitingWeight x0 x1 x2 x3 x4 x5 < v26Delta) :
    v26E3R0SurvivorPilotContractedBox x0 x1 x2 x3 x4 x5 := by
{chr(10).join(calls)}
  unfold v26E3R0SurvivorPilotContractedBox
  exact ⟨{tuple_terms}⟩

end HurtadoZeta23
'''


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out-dir", required=True)
    ns = ap.parse_args()
    out = Path(ns.out_dir)
    out.mkdir(parents=True, exist_ok=True)
    src = emit()
    (out / "V26R0SurvivorAllBlocksPilotGenerated.lean").write_text(src, encoding="utf-8")
    word, *_ = pilot.pilot_data()
    print("R0 SURVIVOR ALL-BLOCK PILOT GENERATION OK")
    print("word:", pilot.wcode(word))
    print("contracted blocks: 21")


if __name__ == "__main__":
    main()
