#!/usr/bin/env python3
"""Generate the reusable analytic-cell catalog for Package E3 round R0.

The historical R0 pass uses thousands of block minorants across 511 words, but
only a small set of distinct rational cells.  This generator deduplicates the
exact `(L,U,N,alpha,eta)` data computed by `v21_rational_bootstrap_verify.py`
and emits one kernel-checkable Lean theorem per distinct cell.

Python is not trusted: every emitted theorem rechecks the rational analytic
minorant through `v26_certified_cell_minorant`.
"""
from __future__ import annotations

from fractions import Fraction as Q
from pathlib import Path
import argparse
import importlib.util

HERE = Path(__file__).resolve().parent
VERIFIER = HERE / "v21_rational_bootstrap_verify.py"
CHUNK_SIZE = 20


def load_verifier():
    spec = importlib.util.spec_from_file_location("v26_r0_catalog", VERIFIER)
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


def r0_cells():
    words511, _ = v.enumerate_511()
    cells = set()
    uses = 0
    for word, _wt in words511:
        intervals = v.initial_intervals(word)
        _M, _b, _c, used = v.build_Q(word, intervals)
        uses += len(used)
        for i, r, N, alpha, eta, _rho in used:
            L, U = intervals[(i, r)]
            cells.add(cell_key(L, U, N, alpha, eta))
    out = sorted(cells, key=lambda z: (z[2], z[0], z[1], z[3], z[4]))
    assert len(out) == 190, len(out)
    assert uses == 9081, uses
    return out, uses


CELLS, USES = r0_cells()
CELL_INDEX = {cell: i for i, cell in enumerate(CELLS)}


def theorem(i: int, cell) -> str:
    L, U, N, alpha, eta = cell
    return f'''/-- R0 analytic cell #{i}: phase index {N}. -/
theorem v26_R0_cell_{i:03d} {{x : ℝ}}
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
    for chunk, start in enumerate(range(0, len(CELLS), CHUNK_SIZE), start=1):
        subset = CELLS[start:start + CHUNK_SIZE]
        name = f"V26R0CellCatalog{chunk:02d}Generated"
        module_names.append(name)
        src = '''import HurtadoZeta23.V26OneBodyCellTools
import Mathlib.Tactic

noncomputable section
namespace HurtadoZeta23

'''
        src += "\n".join(theorem(start + j, cell) for j, cell in enumerate(subset))
        src += "\nend HurtadoZeta23\n"
        (out_dir / f"{name}.lean").write_text(src, encoding="utf-8")

    agg = "\n".join(f"import HurtadoZeta23.{name}" for name in module_names)
    agg += '''

namespace HurtadoZeta23
/-- Marker: all distinct R0 analytic cells are kernel available. -/
theorem v26_R0_cell_catalog_loaded : True := by trivial
end HurtadoZeta23
'''
    (out_dir / "V26R0CellCatalogGenerated.lean").write_text(agg, encoding="utf-8")
    return module_names


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out-dir", required=True)
    ns = ap.parse_args()
    mods = write(Path(ns.out_dir))
    print("R0 ANALYTIC CELL CATALOG GENERATION OK")
    print("distinct cells:", len(CELLS))
    print("historical R0 uses:", USES)
    print("modules:", len(mods))


if __name__ == "__main__":
    main()
