#!/usr/bin/env python3
"""Generate a kernel-checkable R0 survivor-contraction pilot.

The pilot selects the first exact R0 survivor produced by the historical
Fraction-only verifier. It proves:
  * the survivor's rounded quadratic is an analytic lower bound for v26GapF;
  * its exact LDL completion-of-squares identity;
  * a strict counterexample bounds the SOS energy by delta-qmin;
  * weighted Cauchy contracts the first one-body block to the exact historical
    R0 interval.

This is deliberately a one-word/one-block pilot before scaling to all 231
survivors and all 21 block functionals.
"""
from __future__ import annotations

from fractions import Fraction as Q
from pathlib import Path
import argparse

import generate_v26_bootstrap_lean as boot
import generate_v26_r0_cell_catalog as catalog

v = boot.v


def ql(x: Q) -> str:
    x = Q(x)
    if x.denominator == 1:
        return str(x.numerator)
    return f"({x.numerator} / {x.denominator} : ℝ)"


def wcode(w) -> str:
    return "".join(map(str, w))


def word_value(w) -> str:
    tys = [7, 5, 6, 6, 5, 7]
    vals = [d - 1 for d in w]
    return "(" + ", ".join(f"({a} : Fin {n})" for a, n in zip(vals, tys)) + ")"


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


def minor_expr(N: int, alpha: Q, eta: Q, x: str) -> str:
    return f"{ql(alpha)} * (({x}) - v21RootRight {N}) ^ 2 - {ql(eta)}"


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


def z_expr(L, xstar, j: int) -> str:
    parts = []
    for i in range(j, 6):
        a = L[i][j]
        if a == 0:
            continue
        y = f"(x{i} - {ql(xstar[i])})"
        if a == 1:
            parts.append(y)
        elif a == -1:
            parts.append(f"- {y}")
        else:
            parts.append(f"{ql(a)} * {y}")
    return " + ".join(parts).replace("+ - ", "- ")


def forward_solve_unit_lower(L, ell):
    a = [Q(0) for _ in range(6)]
    for i in range(6):
        a[i] = ell[i] - sum((L[i][j] * a[j] for j in range(i)), Q(0))
    for i in range(6):
        assert sum((L[i][j] * a[j] for j in range(i + 1)), Q(0)) == ell[i]
    return a


def pilot_data():
    words511, _ = v.enumerate_511()
    survivors, _discards = v.run_round(words511, initial=True)
    assert len(survivors) == 231
    word, contracted, qmin_expected, nused_expected = survivors[0]
    intervals = v.initial_intervals(word)
    qtxt, M, b, c, used = boot.quadratic_expr(word, intervals)
    qmin, inv, xstar = v.qmin_and_inverse(M, b, c)
    assert qmin == qmin_expected
    assert len(used) == nused_expected
    L, D = boot.ldl_exact(M)

    # Pilot block: first one-body gap x0.
    i, r = 0, 1
    ell = [Q(1), Q(0), Q(0), Q(0), Q(0), Q(0)]
    a = forward_solve_unit_lower(L, ell)
    gap = v.delta - qmin
    assert gap > 0
    radcoeff = sum((a[j] * a[j] / D[j] for j in range(6)), Q(0))
    invell = v.matvec(inv, ell)
    assert radcoeff == v.dot(ell, invell)
    rad2 = gap * radcoeff
    radius = v.sqrt_upper_rational(rad2, 10_000)
    center = v.dot(ell, xstar)
    oldL, oldU = intervals[(i, r)]
    lo0 = v.floor_frac(center - radius, 10_000)
    hi0 = v.ceil_frac(center + radius, 10_000)
    expected = (max(oldL, lo0), min(oldU, hi0))
    assert expected == contracted[(i, r)]
    assert rad2 < radius * radius
    return word, intervals, contracted, qtxt, M, b, c, used, qmin, xstar, L, D, a, gap, rad2, radius, center


def emit_block_theorem(idx21: int, i: int, r: int, expr: str,
                       cell_idx: int | None, intervals) -> str:
    s = bsum(i, r)
    target = f"{expr} ≤ limitingWeight ({s})"
    if cell_idx is None:
        proof = f"  exact v26_limitingWeight_nonneg ({s})"
    else:
        proof = (
            f"  exact v26_R0_cell_{cell_idx:03d} (x := {s})\n"
            f"    {lower_proof(i, r)} {upper_proof(i, r)}"
        )
    bounds = []
    for j in range(6):
        L, U = intervals[(j, 1)]
        bounds.append(f"    (h{j} : {ql(L)} ≤ x{j} ∧ x{j} ≤ {ql(U)})")
    return f'''theorem v26_E3_R0_survivor_pilot_block_{idx21:02d}
    (x0 x1 x2 x3 x4 x5 : ℝ)
{chr(10).join(bounds)} :
    {target} := by
{proof}
'''


def emit() -> str:
    (word, intervals, contracted, qtxt, M, b, c, used, qmin, xstar,
     L, D, a, gap, rad2, radius, center) = pilot_data()
    wc = wcode(word)
    used_by_key = {(i, r): (N, alpha, eta) for i, r, N, alpha, eta, _rho in used}

    block_theorems = []
    hnames = []
    bassign = []
    exprs = []
    idx21 = 0
    used_count = 0
    for r in range(1, 7):
        for i in range(7 - r):
            s = bsum(i, r)
            if (i, r) in used_by_key:
                N, alpha, eta = used_by_key[(i, r)]
                cellL, cellU = intervals[(i, r)]
                key = catalog.cell_key(cellL, cellU, N, alpha, eta)
                cell_idx = catalog.CELL_INDEX[key]
                expr = minor_expr(N, alpha, eta, s)
                used_count += 1
            else:
                cell_idx = None
                expr = "0"
            block_theorems.append(
                emit_block_theorem(idx21, i, r, expr, cell_idx, intervals))
            hn = f"hb{idx21:02d}"
            hnames.append(hn)
            bassign.append(f"    ({block_name(r, i)} := {expr})")
            exprs.append(expr)
            idx21 += 1

    assert idx21 == 21
    assert used_count == len(used)
    assembly = assembled_lower(exprs)
    sostxt = boot.sos_expr(M, xstar)
    z = [z_expr(L, xstar, j) for j in range(6)]
    energy = " +\n      ".join(f"{ql(D[j])} * ({z[j]}) ^ 2" for j in range(6))
    lin = " + ".join(f"{ql(a[j])} * ({z[j]})" for j in range(6))
    coeff = " + ".join(f"({ql(a[j])}) ^ 2 / {ql(D[j])}" for j in range(6))
    newL, newU = contracted[(0, 1)]
    block_calls = "\n".join(
        f"  have {hn} := v26_E3_R0_survivor_pilot_block_{j:02d} x0 x1 x2 x3 x4 x5 h0 h1 h2 h3 h4 h5"
        for j, hn in enumerate(hnames)
    )
    cauchy_args = "\n".join(
        [f"    (a{j} := {ql(a[j])})" for j in range(6)]
        + [f"    (y{j} := {z[j]})" for j in range(6)]
        + [f"    (d{j} := {ql(D[j])})" for j in range(6)]
        + [f"    (gap := {ql(gap)})"]
    )
    positive_ds = " ".join("(by norm_num)" for _ in range(6))

    return f'''import HurtadoZeta23.V26R0CellCatalogGenerated
import HurtadoZeta23.V26GapBlockLower
import HurtadoZeta23.V26BasinInterface
import HurtadoZeta23.V26QuadraticSix
import Mathlib.Tactic

noncomputable section
namespace HurtadoZeta23

/-- First exact R0 survivor selected by the Fraction-only verifier: code {wc}. -/
def v26E3R0SurvivorPilotWord : V26BasinWord := {word_value(word)}

/-- Exact rounded R0 quadratic for the survivor pilot. -/
def v26E3R0SurvivorPilotQ (x0 x1 x2 x3 x4 x5 : ℝ) : ℝ :=
  {qtxt}

def v26E3R0SurvivorPilotQmin : ℝ := {ql(qmin)}

def v26E3R0SurvivorPilotSOS (x0 x1 x2 x3 x4 x5 : ℝ) : ℝ :=
  {sostxt}

/-- Exact LDL completion of squares for the survivor pilot. -/
theorem v26_E3_R0_survivor_pilot_completion
    (x0 x1 x2 x3 x4 x5 : ℝ) :
    v26E3R0SurvivorPilotQ x0 x1 x2 x3 x4 x5 =
      v26E3R0SurvivorPilotQmin +
        v26E3R0SurvivorPilotSOS x0 x1 x2 x3 x4 x5 := by
  unfold v26E3R0SurvivorPilotQ v26E3R0SurvivorPilotQmin v26E3R0SurvivorPilotSOS
  ring

/-- Symbolic-root analytic assembly matching the survivor pilot quadratic. -/
def v26E3R0SurvivorPilotAssembled (x0 x1 x2 x3 x4 x5 : ℝ) : ℝ :=
  {assembly}

theorem v26_E3_R0_survivor_pilot_Q_eq_assembled
    (x0 x1 x2 x3 x4 x5 : ℝ) :
    v26E3R0SurvivorPilotQ x0 x1 x2 x3 x4 x5 =
      v26E3R0SurvivorPilotAssembled x0 x1 x2 x3 x4 x5 := by
  unfold v26E3R0SurvivorPilotQ v26E3R0SurvivorPilotAssembled
  simp [v26Pressure, v21RootRight]
  ring

{chr(10).join(block_theorems)}

theorem v26_E3_R0_survivor_pilot_assembled_le_gapF
    (x0 x1 x2 x3 x4 x5 : ℝ)
    (hbox : v26InWordBox v26E3R0SurvivorPilotWord x0 x1 x2 x3 x4 x5) :
    v26E3R0SurvivorPilotAssembled x0 x1 x2 x3 x4 x5 ≤
      v26GapF limitingWeight x0 x1 x2 x3 x4 x5 := by
  simp [v26InWordBox, v26E3R0SurvivorPilotWord,
    v26InA, v26InB, v26InC,
    v26ALo, v26AHi, v26BLo, v26BHi, v26CLo, v26CHi] at hbox
  norm_num at hbox
  rcases hbox with ⟨h0, h1, h2, h3, h4, h5⟩
{block_calls}
  unfold v26E3R0SurvivorPilotAssembled
  exact v26_gapF_lower_of_block_lowers
    (weight := limitingWeight)
    (g0 := x0) (g1 := x1) (g2 := x2) (g3 := x3) (g4 := x4) (g5 := x5)
{chr(10).join(bassign)}
    {' '.join(hnames)}

theorem v26_E3_R0_survivor_pilot_Q_le_gapF
    (x0 x1 x2 x3 x4 x5 : ℝ)
    (hbox : v26InWordBox v26E3R0SurvivorPilotWord x0 x1 x2 x3 x4 x5) :
    v26E3R0SurvivorPilotQ x0 x1 x2 x3 x4 x5 ≤
      v26GapF limitingWeight x0 x1 x2 x3 x4 x5 := by
  rw [v26_E3_R0_survivor_pilot_Q_eq_assembled]
  exact v26_E3_R0_survivor_pilot_assembled_le_gapF x0 x1 x2 x3 x4 x5 hbox

/-- Any strict counterexample in the pilot survivor has SOS energy below the
exact rational bootstrap gap. -/
theorem v26_E3_R0_survivor_pilot_energy_lt
    (x0 x1 x2 x3 x4 x5 : ℝ)
    (hbox : v26InWordBox v26E3R0SurvivorPilotWord x0 x1 x2 x3 x4 x5)
    (hbad : v26GapF limitingWeight x0 x1 x2 x3 x4 x5 < v26Delta) :
    v26E3R0SurvivorPilotSOS x0 x1 x2 x3 x4 x5 < {ql(gap)} := by
  have hdom := v26_E3_R0_survivor_pilot_Q_le_gapF x0 x1 x2 x3 x4 x5 hbox
  rw [v26_E3_R0_survivor_pilot_completion] at hdom
  norm_num [v26Delta, v26E3R0SurvivorPilotQmin] at hdom hbad ⊢
  linarith

/-- Pilot ellipsoid contraction: a strict counterexample forces the first gap
into exactly the historical R0 contracted interval. -/
theorem v26_E3_R0_survivor_pilot_contract_x0
    (x0 x1 x2 x3 x4 x5 : ℝ)
    (hbox : v26InWordBox v26E3R0SurvivorPilotWord x0 x1 x2 x3 x4 x5)
    (hbad : v26GapF limitingWeight x0 x1 x2 x3 x4 x5 < v26Delta) :
    {ql(newL)} ≤ x0 ∧ x0 ≤ {ql(newU)} := by
  have hsoslt := v26_E3_R0_survivor_pilot_energy_lt x0 x1 x2 x3 x4 x5 hbox hbad
  have henergy :
      {energy} ≤ {ql(gap)} := by
    have h := le_of_lt hsoslt
    simpa [v26E3R0SurvivorPilotSOS] using h
  have hcs := v26_weighted_cauchy6_of_energy
{cauchy_args}
    {positive_ds}
    henergy
  have hsq : (x0 - {ql(center)}) ^ 2 ≤ {ql(rad2)} := by
    calc
      (x0 - {ql(center)}) ^ 2 = ({lin}) ^ 2 := by ring
      _ ≤ {ql(gap)} * ({coeff}) := hcs
      _ = {ql(rad2)} := by norm_num
  have habs : |x0 - {ql(center)}| < {ql(radius)} := by
    exact v26_abs_lt_radius_of_sq_le
      (z := x0 - {ql(center)}) (rad2 := {ql(rad2)}) (R := {ql(radius)})
      (by norm_num) hsq (by norm_num)
  have hbox' := hbox
  simp [v26InWordBox, v26E3R0SurvivorPilotWord,
    v26InA, v26InB, v26InC,
    v26ALo, v26AHi, v26BLo, v26BHi, v26CLo, v26CHi] at hbox'
  norm_num at hbox'
  rcases hbox' with ⟨h0, h1, h2, h3, h4, h5⟩
  have hr := abs_lt.mp habs
  constructor <;> linarith [h0.1, h0.2, hr.1, hr.2]

end HurtadoZeta23
'''


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out-dir", required=True)
    ns = ap.parse_args()
    out = Path(ns.out_dir)
    out.mkdir(parents=True, exist_ok=True)
    data = pilot_data()
    word = data[0]
    path = out / "V26R0SurvivorPilotGenerated.lean"
    path.write_text(emit(), encoding="utf-8")
    contracted = data[2]
    print("R0 SURVIVOR CONTRACTION PILOT GENERATION OK")
    print("word:", wcode(word))
    print("contracted x0:", v.qstr(contracted[(0, 1)][0]), v.qstr(contracted[(0, 1)][1]))


if __name__ == "__main__":
    main()
