#!/usr/bin/env python3
"""Generate the reusable analytic-cell catalog for Package E3 round R2.

R2 starts from the exact 23 contracted boxes produced by R1.  Across those
23 words we deduplicate every rational one-body/block minorant used by the
historical third bootstrap pass.  Each generated Lean theorem is rechecked
through `v26_certified_cell_minorant`, with the phase center kept symbolically
as `v21RootRight N`.

This catalog is only the reusable analytic layer for the 23 -> 5 reduction;
it does not by itself prove that reduction.
"""
from __future__ import annotations

from fractions import Fraction as Q
from pathlib import Path
import argparse
import importlib.util
import json
import hashlib

HERE = Path(__file__).resolve().parent
VERIFIER = HERE / "v21_rational_bootstrap_verify.py"
CHUNK_SIZE = 25


def load_verifier():
    spec = importlib.util.spec_from_file_location("v26_r2_catalog", VERIFIER)
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


def cell_key(L, U, N, alpha, eta):
    return (Q(L), Q(U), int(N), Q(alpha), Q(eta))


def r2_cells():
    words511, _ = v.enumerate_511()
    r0, d0 = v.run_round(words511, initial=True)
    r1, d1 = v.run_round(r0)
    r2, d2 = v.run_round(r1)
    assert len(r0) == 231 and len(d0) == 280
    assert len(r1) == 23 and len(d1) == 208
    assert len(r2) == 5 and len(d2) == 18

    cells = set()
    uses = 0
    for word, intervals, _qmin, _nused in r1:
        _M, _b, _c, used = v.build_Q(word, intervals)
        uses += len(used)
        for i, r, N, alpha, eta, _rho in used:
            L, U = intervals[(i, r)]
            cells.add(cell_key(L, U, N, alpha, eta))

    out = sorted(cells, key=lambda z: (z[2], z[0], z[1], z[3], z[4]))
    assert 0 < len(out) <= uses <= 23 * 21
    return out, uses


CELLS, USES = r2_cells()
CELL_INDEX = {cell: i for i, cell in enumerate(CELLS)}


def theorem(i: int, cell) -> str:
    L, U, N, alpha, eta = cell
    return f'''/-- R2 analytic cell #{i}: phase index {N}. -/
theorem v26_R2_cell_{i:04d} {{x : ℝ}}
    (hL : {ql(L)} ≤ x) (hU : x ≤ {ql(U)}) :
    {ql(alpha)} * (x - v21RootRight {N}) ^ 2 - {ql(eta)} ≤ limitingWeight x := by
  apply v26_certified_cell_minorant
    (N := {N}) (L := {ql(L)}) (U := {ql(U)}) (x := x)
    (alpha := {ql(alpha)}) (eta := {ql(eta)})
    (by norm_num) (by norm_num) (by linarith) hL hU
  all_goals norm_num [v26CellLstar, v26CellEps, v26CellRho, v26Mrat, v21RootRight,
    v26Araw, v26AmplitudeFloor, v26ChordCoeff, v26Fold, v26P7, v26d0]
'''


def write(out_dir: Path):
    out_dir.mkdir(parents=True, exist_ok=True)
    module_names = []
    files = {}
    for chunk, start in enumerate(range(0, len(CELLS), CHUNK_SIZE)):
        subset = CELLS[start:start + CHUNK_SIZE]
        name = f"V26R2CellCatalog{chunk:03d}Generated"
        module_names.append(name)
        src = '''import HurtadoZeta23.V26OneBodyCellTools
import Mathlib.Tactic

noncomputable section
namespace HurtadoZeta23

'''
        src += "\n".join(theorem(start + j, cell) for j, cell in enumerate(subset))
        src += "\nend HurtadoZeta23\n"
        path = out_dir / f"{name}.lean"
        path.write_text(src, encoding="utf-8")
        raw = path.read_bytes()
        files[path.name] = {
            "bytes": len(raw),
            "sha256": hashlib.sha256(raw).hexdigest(),
        }

    agg = "\n".join(f"import HurtadoZeta23.{name}" for name in module_names)
    agg += '''

namespace HurtadoZeta23
/-- Marker: all distinct R2 analytic cells are kernel available. -/
theorem v26_R2_cell_catalog_loaded : True := by trivial
end HurtadoZeta23
'''
    agg_path = out_dir / "V26R2CellCatalogGenerated.lean"
    agg_path.write_text(agg, encoding="utf-8")
    raw = agg_path.read_bytes()
    files[agg_path.name] = {
        "bytes": len(raw),
        "sha256": hashlib.sha256(raw).hexdigest(),
    }

    manifest = {
        "round2_input_words": 23,
        "round3_survivors": 5,
        "round2_discards": 18,
        "distinct_cells": len(CELLS),
        "historical_uses": USES,
        "chunk_size": CHUNK_SIZE,
        "modules": module_names,
        "files": files,
    }
    (out_dir / "v26_r2_cell_catalog_manifest.json").write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    return manifest


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out-dir", required=True)
    ns = ap.parse_args()
    m = write(Path(ns.out_dir))
    print("R2 ANALYTIC CELL CATALOG GENERATION OK")
    print("input words:", m["round2_input_words"])
    print("distinct cells:", m["distinct_cells"])
    print("historical R2 uses:", m["historical_uses"])
    print("modules:", len(m["modules"]))


if __name__ == "__main__":
    main()
