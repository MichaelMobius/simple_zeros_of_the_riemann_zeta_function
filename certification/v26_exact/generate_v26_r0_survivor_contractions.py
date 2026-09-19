#!/usr/bin/env python3
"""Generate full Package-E3 R0 survivor contraction certificates.

For each of the 231 exact R0 survivors this generator emits one independent
Lean module proving, under the actual Package-D basin box and strict
counterexample hypothesis:

  * the historical rounded R0 quadratic is below `v26GapF limitingWeight`;
  * its exact LDL completion gives a single six-term SOS energy bound;
  * all 21 consecutive block sums lie in exactly the historical contracted
    rational intervals used as the R1 input.

The generator uses `fractions.Fraction` only.  Generated files are intended to
remain ephemeral CI artefacts; every algebraic identity, analytic implication,
weighted-Cauchy step and radius comparison is kernel checked by Lean.
"""
from __future__ import annotations

from fractions import Fraction as Q
from pathlib import Path
import argparse
import hashlib
import json

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


def forward_solve_lower(L, ell):
    a = [Q(0) for _ in range(6)]
    for i in range(6):
        a[i] = ell[i] - sum((L[i][j] * a[j] for j in range(i)), Q(0))
    for i in range(6):
        assert sum((L[i][j] * a[j] for j in range(i + 1)), Q(0)) == ell[i]
    return a


def initial_bound_types(intervals):
    out = []
    for j in range(6):
        L, U = intervals[(j, 1)]
        out.append(f"({ql(L)} ≤ x{j} ∧ x{j} ≤ {ql(U)})")
    return out


def bound_binders(intervals):
    return "\n".join(
        f"    (h{j} : {typ})" for j, typ in enumerate(initial_bound_types(intervals))
    )


def lower_proof(i, r):
    hs = ", ".join(f"h{j}.1" for j in range(i, i + r))
    return f"(by linarith [{hs}])"


def upper_proof(i, r):
    hs = ", ".join(f"h{j}.2" for j in range(i, i + r))
    return f"(by linarith [{hs}])"


def contraction_data(intervals, contracted, inv, xstar, L, D, gap, i, r):
    ell = [Q(1) if i <= j < i + r else Q(0) for j in range(6)]
    a = forward_solve_lower(L, ell)
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
    return a, rad2, radius, center, oldL, oldU, expected


def emit_survivor(word, contracted, qmin_expected, nused_expected):
    wc = wcode(word)
    intervals = v.initial_intervals(word)
    qtxt, M, b, c, used = boot.quadratic_expr(word, intervals)
    qmin, inv, xstar = v.qmin_and_inverse(M, b, c)
    assert qmin == qmin_expected
    assert len(used) == nused_expected
    assert qmin < v.delta
    gap = v.delta - qmin
    L, D = boot.ldl_exact(M)
    zraw = [z_expr(L, xstar, j) for j in range(6)]

    stem = f"v26E3R0_{wc}"
    word_def = f"{stem}Word"
    q_def = f"{stem}Q"
    qmin_def = f"{stem}Qmin"
    assembly_def = f"{stem}Assembled"
    energy_def = f"{stem}Energy"
    zdefs = [f"{stem}Z{j}" for j in range(6)]
    box_def = f"{stem}ContractedBox"

    z_decl = "\n\n".join(
        f"def {zdefs[j]} (x0 x1 x2 x3 x4 x5 : ℝ) : ℝ :=\n  {zraw[j]}"
        for j in range(6)
    )
    zcall = [f"{zdefs[j]} x0 x1 x2 x3 x4 x5" for j in range(6)]
    energy_expr = " +\n      ".join(f"{ql(D[j])} * ({zcall[j]}) ^ 2" for j in range(6))

    used_by_key = {(i, r): (N, alpha, eta) for i, r, N, alpha, eta, _rho in used}
    exprs = []
    bassign = []
    block_theorems = []
    block_hnames = []
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
                proof = (
                    f"  exact v26_R0_cell_{cell_idx:03d} (x := {s})\n"
                    f"    {lower_proof(i, r)} {upper_proof(i, r)}"
                )
                used_count += 1
            else:
                expr = "0"
                proof = f"  exact v26_limitingWeight_nonneg ({s})"
            thm = f"v26_E3_R0_{wc}_minor_{idx21:02d}"
            block_theorems.append(f'''theorem {thm}
    (x0 x1 x2 x3 x4 x5 : ℝ)
{bound_binders(intervals)} :
    {expr} ≤ limitingWeight ({s}) := by
{proof}
''')
            hn = f"hm{idx21:02d}"
            block_hnames.append(hn)
            exprs.append(expr)
            bassign.append(f"    ({block_name(r, i)} := {expr})")
            idx21 += 1
    assert idx21 == 21 and used_count == len(used)
    assembly = assembled_lower(exprs)

    bounds_prop = " ∧\n      ".join(initial_bound_types(intervals))
    bounds_thm = f'''theorem v26_E3_R0_{wc}_bounds_of_box
    (x0 x1 x2 x3 x4 x5 : ℝ)
    (hbox : v26InWordBox {word_def} x0 x1 x2 x3 x4 x5) :
    {bounds_prop} := by
  simp [v26InWordBox, {word_def},
    v26InA, v26InB, v26InC,
    v26ALo, v26AHi, v26BLo, v26BHi, v26CLo, v26CHi] at hbox
  norm_num at hbox
  exact hbox
'''

    block_calls = "\n".join(
        f"  have {block_hnames[j]} := v26_E3_R0_{wc}_minor_{j:02d} x0 x1 x2 x3 x4 x5 h0 h1 h2 h3 h4 h5"
        for j in range(21)
    )

    contract_theorems = []
    contract_names = []
    contracted_props = []
    idx21 = 0
    for r in range(1, 7):
        for i in range(7 - r):
            a, rad2, radius, center, oldL, oldU, (newL, newU) = contraction_data(
                intervals, contracted, inv, xstar, L, D, gap, i, r)
            s = bsum(i, r)
            lin = " + ".join(f"{ql(a[j])} * ({zcall[j]})" for j in range(6))
            coeff = " + ".join(f"({ql(a[j])}) ^ 2 / {ql(D[j])}" for j in range(6))
            cargs = "\n".join(
                [f"    (a{j} := {ql(a[j])})" for j in range(6)]
                + [f"    (y{j} := {zcall[j]})" for j in range(6)]
                + [f"    (d{j} := {ql(D[j])})" for j in range(6)]
                + [f"    (gap := {ql(gap)})"]
            )
            involved_l = ", ".join(f"h{j}.1" for j in range(i, i + r))
            involved_u = ", ".join(f"h{j}.2" for j in range(i, i + r))
            thm = f"v26_E3_R0_{wc}_contract_b{r-1}{i}"
            contract_names.append(thm)
            contracted_props.append(f"({ql(newL)} ≤ ({s}) ∧ ({s}) ≤ {ql(newU)})")
            contract_theorems.append(f'''theorem {thm}
    (x0 x1 x2 x3 x4 x5 : ℝ)
{bound_binders(intervals)}
    (henergy : {energy_def} x0 x1 x2 x3 x4 x5 ≤ {ql(gap)}) :
    {ql(newL)} ≤ ({s}) ∧ ({s}) ≤ {ql(newU)} := by
  have henergy' :
      {energy_expr} ≤ {ql(gap)} := by
    simpa [{energy_def}] using henergy
  have hcs := v26_weighted_cauchy6_of_energy
{cargs}
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    henergy'
  have hsq : (({s}) - {ql(center)}) ^ 2 ≤ {ql(rad2)} := by
    calc
      (({s}) - {ql(center)}) ^ 2 = ({lin}) ^ 2 := by
        unfold {' '.join(zdefs)}
        ring
      _ ≤ {ql(gap)} * ({coeff}) := hcs
      _ = {ql(rad2)} := by norm_num
  have habs : |({s}) - {ql(center)}| < {ql(radius)} := by
    exact v26_abs_lt_radius_of_sq_le
      (z := ({s}) - {ql(center)}) (rad2 := {ql(rad2)}) (R := {ql(radius)})
      (by norm_num) hsq (by norm_num)
  have holdL : {ql(oldL)} ≤ ({s}) := by linarith [{involved_l}]
  have holdU : ({s}) ≤ {ql(oldU)} := by linarith [{involved_u}]
  have hr := abs_lt.mp habs
  constructor <;> linarith [holdL, holdU, hr.1, hr.2]
''')
            idx21 += 1
    assert idx21 == 21

    contracted_prop = " ∧\n      ".join(contracted_props)
    contract_calls = "\n".join(
        f"  have hc{j:02d} := {contract_names[j]} x0 x1 x2 x3 x4 x5 h0 h1 h2 h3 h4 h5 henergy"
        for j in range(21)
    )
    contract_tuple = ", ".join(f"hc{j:02d}" for j in range(21))

    return f'''import HurtadoZeta23.V26R0CellCatalogGenerated
import HurtadoZeta23.V26GapBlockLower
import HurtadoZeta23.V26BasinInterface
import HurtadoZeta23.V26QuadraticSix
import Mathlib.Tactic

noncomputable section
namespace HurtadoZeta23

/-- R0 survivor `{wc}` as an exact basin word. -/
def {word_def} : V26BasinWord := {word_value(word)}

/-- Historical rounded R0 quadratic for survivor `{wc}`. -/
def {q_def} (x0 x1 x2 x3 x4 x5 : ℝ) : ℝ :=
  {qtxt}

def {qmin_def} : ℝ := {ql(qmin)}

{z_decl}

def {energy_def} (x0 x1 x2 x3 x4 x5 : ℝ) : ℝ :=
  {energy_expr}

/-- Exact LDL completion for R0 survivor `{wc}`. -/
theorem v26_E3_R0_{wc}_completion
    (x0 x1 x2 x3 x4 x5 : ℝ) :
    {q_def} x0 x1 x2 x3 x4 x5 =
      {qmin_def} + {energy_def} x0 x1 x2 x3 x4 x5 := by
  unfold {q_def} {qmin_def} {energy_def} {' '.join(zdefs)}
  ring

/-- Symbolic-root 21-block analytic assembly for R0 survivor `{wc}`. -/
def {assembly_def} (x0 x1 x2 x3 x4 x5 : ℝ) : ℝ :=
  {assembly}

theorem v26_E3_R0_{wc}_Q_eq_assembled
    (x0 x1 x2 x3 x4 x5 : ℝ) :
    {q_def} x0 x1 x2 x3 x4 x5 =
      {assembly_def} x0 x1 x2 x3 x4 x5 := by
  unfold {q_def} {assembly_def}
  simp [v26Pressure, v21RootRight]
  ring

{bounds_thm}

{chr(10).join(block_theorems)}

theorem v26_E3_R0_{wc}_assembled_le_gapF
    (x0 x1 x2 x3 x4 x5 : ℝ)
    (hbox : v26InWordBox {word_def} x0 x1 x2 x3 x4 x5) :
    {assembly_def} x0 x1 x2 x3 x4 x5 ≤
      v26GapF limitingWeight x0 x1 x2 x3 x4 x5 := by
  rcases v26_E3_R0_{wc}_bounds_of_box x0 x1 x2 x3 x4 x5 hbox with
    ⟨h0, h1, h2, h3, h4, h5⟩
{block_calls}
  unfold {assembly_def}
  exact v26_gapF_lower_of_block_lowers
    (weight := limitingWeight)
    (g0 := x0) (g1 := x1) (g2 := x2) (g3 := x3) (g4 := x4) (g5 := x5)
{chr(10).join(bassign)}
    {' '.join(block_hnames)}

theorem v26_E3_R0_{wc}_Q_le_gapF
    (x0 x1 x2 x3 x4 x5 : ℝ)
    (hbox : v26InWordBox {word_def} x0 x1 x2 x3 x4 x5) :
    {q_def} x0 x1 x2 x3 x4 x5 ≤
      v26GapF limitingWeight x0 x1 x2 x3 x4 x5 := by
  rw [v26_E3_R0_{wc}_Q_eq_assembled]
  exact v26_E3_R0_{wc}_assembled_le_gapF x0 x1 x2 x3 x4 x5 hbox

/-- Strict counterexamples in survivor `{wc}` have energy below the exact
bootstrap gap `delta - qmin`. -/
theorem v26_E3_R0_{wc}_energy_lt
    (x0 x1 x2 x3 x4 x5 : ℝ)
    (hbox : v26InWordBox {word_def} x0 x1 x2 x3 x4 x5)
    (hbad : v26GapF limitingWeight x0 x1 x2 x3 x4 x5 < v26Delta) :
    {energy_def} x0 x1 x2 x3 x4 x5 < {ql(gap)} := by
  have hdom := v26_E3_R0_{wc}_Q_le_gapF x0 x1 x2 x3 x4 x5 hbox
  rw [v26_E3_R0_{wc}_completion] at hdom
  norm_num [v26Delta, {qmin_def}] at hdom hbad ⊢
  linarith

theorem v26_E3_R0_{wc}_energy_le
    (x0 x1 x2 x3 x4 x5 : ℝ)
    (hbox : v26InWordBox {word_def} x0 x1 x2 x3 x4 x5)
    (hbad : v26GapF limitingWeight x0 x1 x2 x3 x4 x5 < v26Delta) :
    {energy_def} x0 x1 x2 x3 x4 x5 ≤ {ql(gap)} :=
  le_of_lt (v26_E3_R0_{wc}_energy_lt x0 x1 x2 x3 x4 x5 hbox hbad)

{chr(10).join(contract_theorems)}

def {box_def} (x0 x1 x2 x3 x4 x5 : ℝ) : Prop :=
  {contracted_prop}

/-- Full exact 21-block R0 contraction for survivor `{wc}`. -/
theorem v26_E3_R0_{wc}_contract_all
    (x0 x1 x2 x3 x4 x5 : ℝ)
    (hbox : v26InWordBox {word_def} x0 x1 x2 x3 x4 x5)
    (hbad : v26GapF limitingWeight x0 x1 x2 x3 x4 x5 < v26Delta) :
    {box_def} x0 x1 x2 x3 x4 x5 := by
  rcases v26_E3_R0_{wc}_bounds_of_box x0 x1 x2 x3 x4 x5 hbox with
    ⟨h0, h1, h2, h3, h4, h5⟩
  have henergy := v26_E3_R0_{wc}_energy_le x0 x1 x2 x3 x4 x5 hbox hbad
{contract_calls}
  unfold {box_def}
  exact ⟨{contract_tuple}⟩

end HurtadoZeta23
'''


def exact_r0_survivors():
    words511, _ = v.enumerate_511()
    survivors, discards = v.run_round(words511, initial=True)
    assert len(survivors) == 231 and len(discards) == 280
    return survivors


def write(out_dir: Path):
    out_dir.mkdir(parents=True, exist_ok=True)
    survivors = exact_r0_survivors()
    modules = []
    codes = []
    files = {}
    for word, contracted, qmin, nused in survivors:
        wc = wcode(word)
        mod = f"V26R0Survivor{wc}Generated"
        path = out_dir / f"{mod}.lean"
        path.write_text(emit_survivor(word, contracted, qmin, nused), encoding="utf-8")
        modules.append(mod)
        codes.append(wc)
        raw = path.read_bytes()
        files[path.name] = {"bytes": len(raw), "sha256": hashlib.sha256(raw).hexdigest()}

    agg = out_dir / "V26R0SurvivorContractionsGenerated.lean"
    agg.write_text(
        "\n".join(f"import HurtadoZeta23.{m}" for m in modules)
        + "\n\nnamespace HurtadoZeta23\n"
        + "/-- Marker: all 231 R0 survivor contraction modules compiled. -/\n"
        + "theorem v26_E3_R0_all_survivor_contractions_loaded : True := by trivial\n"
        + "end HurtadoZeta23\n",
        encoding="utf-8",
    )
    manifest = {
        "survivor_count": len(survivors),
        "codes": codes,
        "modules": modules,
        "files": files,
    }
    (out_dir / "v26_r0_survivor_contractions_manifest.json").write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return manifest


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out-dir", required=True)
    ns = ap.parse_args()
    manifest = write(Path(ns.out_dir))
    print("R0 SURVIVOR CONTRACTION GENERATION OK")
    print("survivors:", manifest["survivor_count"])
    print("modules:", len(manifest["modules"]))


if __name__ == "__main__":
    main()
