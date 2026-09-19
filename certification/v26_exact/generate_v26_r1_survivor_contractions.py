#!/usr/bin/env python3
"""Generate full Package-E3 R1 survivor contraction certificates.

R1 starts from the 231 exact R0-contracted boxes.  Exactly 23 words survive
that round.  For each survivor this generator kernelizes the same historical
rational-bootstrap step used by the exact verifier:

* the R1 symbolic-root 21-block quadratic is below the true gap functional on
  the already-certified R0 contracted box;
* an exact LDL completion turns a strict counterexample into an energy bound;
* weighted Cauchy contracts all 21 consecutive block sums to the exact rational
  intervals used as input to the next (23 -> 5) round.

Python only emits exact rational identities.  Every analytic inequality,
polynomial identity and contraction implication is rechecked by Lean.
"""
from __future__ import annotations

from fractions import Fraction as Q
from pathlib import Path
import argparse
import hashlib
import json

import generate_v26_bootstrap_lean as boot
import generate_v26_r0_survivor_contractions as common
import generate_v26_r1_cell_catalog as catalog

v = boot.v

ql = common.ql
wcode = common.wcode
bsum = common.bsum
block_name = common.block_name
minor_expr = common.minor_expr
assembled_lower = common.assembled_lower
z_expr = common.z_expr
contraction_data = common.contraction_data


def input_box_prop(intervals) -> str:
    pieces = []
    for r in range(1, 7):
        for i in range(7 - r):
            L, U = intervals[(i, r)]
            s = bsum(i, r)
            pieces.append(f"({ql(L)} ≤ ({s}) ∧ ({s}) ≤ {ql(U)})")
    assert len(pieces) == 21
    return " ∧\n      ".join(pieces)


def exact_r1_survivors():
    words511, _ = v.enumerate_511()
    r0, d0 = v.run_round(words511, initial=True)
    r1, d1 = v.run_round(r0)
    assert len(r0) == 231 and len(d0) == 280
    assert len(r1) == 23 and len(d1) == 208
    r0_map = {tuple(word): intervals for word, intervals, _qmin, _nused in r0}
    out = []
    for word, contracted, qmin, nused in r1:
        out.append((word, r0_map[tuple(word)], contracted, qmin, nused))
    return out


def emit_survivor(word, intervals, contracted, qmin_expected, nused_expected):
    wc = wcode(word)
    qtxt, M, b, c, used = boot.quadratic_expr(word, intervals)
    qmin, inv, xstar = v.qmin_and_inverse(M, b, c)
    assert qmin == qmin_expected
    assert len(used) == nused_expected
    assert qmin < v.delta
    gap = v.delta - qmin
    L, D = boot.ldl_exact(M)
    zraw = [z_expr(L, xstar, j) for j in range(6)]

    stem = f"v26E3R1_{wc}"
    q_def = f"{stem}Q"
    qmin_def = f"{stem}Qmin"
    assembly_def = f"{stem}Assembled"
    energy_def = f"{stem}Energy"
    zdefs = [f"{stem}Z{j}" for j in range(6)]
    input_box = f"v26E3R0_{wc}ContractedBox"
    output_box = f"{stem}ContractedBox"

    z_decl = "\n\n".join(
        f"def {zdefs[j]} (x0 x1 x2 x3 x4 x5 : ℝ) : ℝ :=\n  {zraw[j]}"
        for j in range(6)
    )
    zcall = [f"{zdefs[j]} x0 x1 x2 x3 x4 x5" for j in range(6)]
    energy_expr = " +\n      ".join(
        f"{ql(D[j])} * ({zcall[j]}) ^ 2" for j in range(6)
    )

    used_by_key = {(i, r): (N, alpha, eta) for i, r, N, alpha, eta, _rho in used}
    exprs = []
    bassign = []
    minor_theorems = []
    minor_calls = []
    catalog_modules = set()
    idx21 = 0
    used_count = 0
    for r in range(1, 7):
        for i in range(7 - r):
            s = bsum(i, r)
            oldL, oldU = intervals[(i, r)]
            hblock = f"hb{idx21:02d}"
            if (i, r) in used_by_key:
                N, alpha, eta = used_by_key[(i, r)]
                key = catalog.cell_key(oldL, oldU, N, alpha, eta)
                cell_idx = catalog.CELL_INDEX[key]
                catalog_modules.add(cell_idx // catalog.CHUNK_SIZE)
                expr = minor_expr(N, alpha, eta, s)
                proof = (
                    f"  exact v26_R1_cell_{cell_idx:04d} (x := {s}) hblock.1 hblock.2"
                )
                used_count += 1
            else:
                expr = "0"
                proof = f"  exact v26_limitingWeight_nonneg ({s})"
            thm = f"v26_E3_R1_{wc}_minor_{idx21:02d}"
            minor_theorems.append(f'''theorem {thm}
    (x0 x1 x2 x3 x4 x5 : ℝ)
    (hblock : {ql(oldL)} ≤ ({s}) ∧ ({s}) ≤ {ql(oldU)}) :
    {expr} ≤ limitingWeight ({s}) := by
{proof}
''')
            minor_calls.append(
                f"  have hm{idx21:02d} := {thm} x0 x1 x2 x3 x4 x5 {hblock}"
            )
            exprs.append(expr)
            bassign.append(f"    ({block_name(r, i)} := {expr})")
            idx21 += 1
    assert idx21 == 21 and used_count == len(used)
    assembly = assembled_lower(exprs)
    hb_names = ", ".join(f"hb{i:02d}" for i in range(21))
    hm_names = " ".join(f"hm{i:02d}" for i in range(21))

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
            thm = f"v26_E3_R1_{wc}_contract_b{r-1}{i}"
            contract_names.append(thm)
            contracted_props.append(f"({ql(newL)} ≤ ({s}) ∧ ({s}) ≤ {ql(newU)})")
            contract_theorems.append(f'''theorem {thm}
    (x0 x1 x2 x3 x4 x5 : ℝ)
    (hblock : {ql(oldL)} ≤ ({s}) ∧ ({s}) ≤ {ql(oldU)})
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
  have hr := abs_lt.mp habs
  constructor <;> linarith [hblock.1, hblock.2, hr.1, hr.2]
''')
            idx21 += 1
    assert idx21 == 21

    contracted_prop = " ∧\n      ".join(contracted_props)
    contract_calls = "\n".join(
        f"  have hc{j:02d} := {contract_names[j]} x0 x1 x2 x3 x4 x5 hb{j:02d} henergy"
        for j in range(21)
    )
    contract_tuple = ", ".join(f"hc{j:02d}" for j in range(21))

    imports = {
        f"import HurtadoZeta23.V26R0Survivor{wc}Generated",
        "import HurtadoZeta23.V26GapBlockLower",
        "import HurtadoZeta23.V26QuadraticSix",
        "import Mathlib.Tactic",
    }
    for m in catalog_modules:
        imports.add(f"import HurtadoZeta23.V26R1CellCatalog{m:03d}Generated")

    src = "\n".join(sorted(imports)) + '''

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

noncomputable section
namespace HurtadoZeta23

'''
    src += f'''/-- Historical rounded R1 quadratic for survivor `{wc}`. -/
def {q_def} (x0 x1 x2 x3 x4 x5 : ℝ) : ℝ :=
  {qtxt}

def {qmin_def} : ℝ := {ql(qmin)}

{z_decl}

def {energy_def} (x0 x1 x2 x3 x4 x5 : ℝ) : ℝ :=
  {energy_expr}

/-- Exact LDL completion for R1 survivor `{wc}`. -/
theorem v26_E3_R1_{wc}_completion
    (x0 x1 x2 x3 x4 x5 : ℝ) :
    {q_def} x0 x1 x2 x3 x4 x5 =
      {qmin_def} + {energy_def} x0 x1 x2 x3 x4 x5 := by
  unfold {q_def} {qmin_def} {energy_def} {' '.join(zdefs)}
  ring

/-- Symbolic-root 21-block analytic assembly for R1 survivor `{wc}`. -/
def {assembly_def} (x0 x1 x2 x3 x4 x5 : ℝ) : ℝ :=
  {assembly}

/-- Pure algebra: the rounded R1 quadratic is the symbolic block assembly. -/
theorem v26_E3_R1_{wc}_Q_eq_assembled
    (x0 x1 x2 x3 x4 x5 : ℝ) :
    {q_def} x0 x1 x2 x3 x4 x5 =
      {assembly_def} x0 x1 x2 x3 x4 x5 := by
  unfold {q_def} {assembly_def}
  simp [v26Pressure, v21RootRight]
  ring

{chr(10).join(minor_theorems)}

theorem v26_E3_R1_{wc}_assembled_le_gapF
    (x0 x1 x2 x3 x4 x5 : ℝ)
    (hbox : {input_box} x0 x1 x2 x3 x4 x5) :
    {assembly_def} x0 x1 x2 x3 x4 x5 ≤
      v26GapF limitingWeight x0 x1 x2 x3 x4 x5 := by
  unfold {input_box} at hbox
  rcases hbox with ⟨{hb_names}⟩
{chr(10).join(minor_calls)}
  unfold {assembly_def}
  exact v26_gapF_lower_of_block_lowers
    (weight := limitingWeight)
    (g0 := x0) (g1 := x1) (g2 := x2) (g3 := x3) (g4 := x4) (g5 := x5)
{chr(10).join(bassign)}
    {hm_names}

theorem v26_E3_R1_{wc}_Q_le_gapF
    (x0 x1 x2 x3 x4 x5 : ℝ)
    (hbox : {input_box} x0 x1 x2 x3 x4 x5) :
    {q_def} x0 x1 x2 x3 x4 x5 ≤
      v26GapF limitingWeight x0 x1 x2 x3 x4 x5 := by
  rw [v26_E3_R1_{wc}_Q_eq_assembled]
  exact v26_E3_R1_{wc}_assembled_le_gapF x0 x1 x2 x3 x4 x5 hbox

/-- Strict counterexamples in survivor `{wc}` have energy below delta-qmin. -/
theorem v26_E3_R1_{wc}_energy_lt
    (x0 x1 x2 x3 x4 x5 : ℝ)
    (hbox : {input_box} x0 x1 x2 x3 x4 x5)
    (hbad : v26GapF limitingWeight x0 x1 x2 x3 x4 x5 < v26Delta) :
    {energy_def} x0 x1 x2 x3 x4 x5 < {ql(gap)} := by
  have hdom := v26_E3_R1_{wc}_Q_le_gapF x0 x1 x2 x3 x4 x5 hbox
  rw [v26_E3_R1_{wc}_completion] at hdom
  norm_num [v26Delta, {qmin_def}] at hdom hbad ⊢
  linarith

theorem v26_E3_R1_{wc}_energy_le
    (x0 x1 x2 x3 x4 x5 : ℝ)
    (hbox : {input_box} x0 x1 x2 x3 x4 x5)
    (hbad : v26GapF limitingWeight x0 x1 x2 x3 x4 x5 < v26Delta) :
    {energy_def} x0 x1 x2 x3 x4 x5 ≤ {ql(gap)} :=
  le_of_lt (v26_E3_R1_{wc}_energy_lt x0 x1 x2 x3 x4 x5 hbox hbad)

{chr(10).join(contract_theorems)}

def {output_box} (x0 x1 x2 x3 x4 x5 : ℝ) : Prop :=
  {contracted_prop}

/-- Full exact 21-block R1 contraction for survivor `{wc}`. -/
theorem v26_E3_R1_{wc}_contract_all
    (x0 x1 x2 x3 x4 x5 : ℝ)
    (hbox : {input_box} x0 x1 x2 x3 x4 x5)
    (hbad : v26GapF limitingWeight x0 x1 x2 x3 x4 x5 < v26Delta) :
    {output_box} x0 x1 x2 x3 x4 x5 := by
  have henergy := v26_E3_R1_{wc}_energy_le x0 x1 x2 x3 x4 x5 hbox hbad
  unfold {input_box} at hbox
  rcases hbox with ⟨{hb_names}⟩
{contract_calls}
  unfold {output_box}
  exact ⟨{contract_tuple}⟩

end HurtadoZeta23
'''
    return src


def write(out_dir: Path):
    out_dir.mkdir(parents=True, exist_ok=True)
    survivors = exact_r1_survivors()
    modules = []
    codes = []
    files = {}
    for word, intervals, contracted, qmin, nused in survivors:
        wc = wcode(word)
        mod = f"V26R1Survivor{wc}Generated"
        path = out_dir / f"{mod}.lean"
        path.write_text(
            emit_survivor(word, intervals, contracted, qmin, nused),
            encoding="utf-8",
        )
        modules.append(mod)
        codes.append(wc)
        raw = path.read_bytes()
        files[path.name] = {
            "bytes": len(raw),
            "sha256": hashlib.sha256(raw).hexdigest(),
        }

    assert len(modules) == 23
    agg = out_dir / "V26R1SurvivorContractionsGenerated.lean"
    agg.write_text(
        "\n".join(f"import HurtadoZeta23.{m}" for m in modules)
        + "\n\nnamespace HurtadoZeta23\n"
        + "/-- Marker: all 23 R1 survivor contraction modules compiled. -/\n"
        + "theorem v26_E3_R1_all_survivor_contractions_loaded : True := by trivial\n"
        + "end HurtadoZeta23\n",
        encoding="utf-8",
    )
    manifest = {
        "survivor_count": len(survivors),
        "codes": codes,
        "modules": modules,
        "files": files,
    }
    (out_dir / "v26_r1_survivor_contractions_manifest.json").write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return manifest


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out-dir", required=True)
    ns = ap.parse_args()
    manifest = write(Path(ns.out_dir))
    print("R1 SURVIVOR CONTRACTION GENERATION OK")
    print("survivors:", manifest["survivor_count"])
    print("codes:", ", ".join(manifest["codes"]))
    print("modules:", len(manifest["modules"]))


if __name__ == "__main__":
    main()
