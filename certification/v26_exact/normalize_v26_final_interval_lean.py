#!/usr/bin/env python3
"""Normalize generated v26 final interval Lean certificates.

The exact interval generator historically emitted local declarations of the form

    have h : v26Ball VALUE _ _ := by
      simpa [...] using hraw

or

    have h : v26Ball VALUE _ _ := by
      convert hraw using 1 <;> ring

Lean 4.24 does not infer the centre/radius metavariables from the proof body in
such annotated `have`s.  This post-pass preserves the exact same proof data but
lets centre and radius be inferred from `hraw`, then transports only the value
across an exact equality using `v26_ball_congr_value`.

No numerical data are changed and no proposition is assumed by Python.  Every
transport equality and every interval inequality is still kernel-checked by
Lean.
"""
from __future__ import annotations

import argparse
from pathlib import Path
import re

HAVE_RE = re.compile(r"^(?P<indent>\s*)have\s+(?P<name>[A-Za-z0-9_']+)\s*:\s*v26Ball\s+(?P<rest>.*)$")


def equality_tactic(name: str, proof_line: str) -> tuple[str, str]:
    """Return (source expression, equality tactic) for one generated transport."""
    s = proof_line.strip()
    if s.startswith("simpa ") and " using " in s:
        left, source = s.split(" using ", 1)
        simp_spec = left[len("simpa "):]
        return source.strip(), f"by simp {simp_spec}"
    if s.startswith("convert ") and s.endswith(" using 1 <;> ring"):
        source = s[len("convert "):-len(" using 1 <;> ring")].strip()
        special = {
            "hH": "by unfold v21RootH v26LocalPhase; ring",
            "hM1": "by unfold v26LocalM1; ring",
            "hM2": "by unfold v26LocalM2 v21P2 v21Q2; ring",
            "hDb": "by unfold v21D; ring",
        }
        return source, special.get(name, "by ring")
    raise RuntimeError(f"unsupported generated ball proof for {name}: {proof_line!r}")


def normalize_file(path: Path) -> int:
    lines = path.read_text(encoding="utf-8").splitlines()
    out: list[str] = []
    i = 0
    changed = 0
    while i < len(lines):
        m = HAVE_RE.match(lines[i])
        if not m:
            out.append(lines[i])
            i += 1
            continue

        indent = m.group("indent")
        name = m.group("name")
        type_parts = [m.group("rest")]
        j = i
        while ":= by" not in type_parts[-1]:
            j += 1
            if j >= len(lines):
                raise RuntimeError(f"unterminated v26Ball declaration in {path}:{i+1}")
            type_parts.append(lines[j].strip())

        joined = " ".join(type_parts)
        marker = " _ _ := by"
        if marker not in joined:
            out.extend(lines[i:j+1])
            i = j + 1
            continue

        target = joined.split(marker, 1)[0].strip()
        if not target:
            raise RuntimeError(f"empty v26Ball target in {path}:{i+1}")

        proof_idx = j + 1
        if proof_idx >= len(lines):
            raise RuntimeError(f"missing v26Ball proof in {path}:{i+1}")
        source, eq_tac = equality_tactic(name, lines[proof_idx])
        out.append(
            f"{indent}have {name} := v26_ball_congr_value ({source}) "
            f"(y := {target}) ({eq_tac})"
        )
        changed += 1
        i = proof_idx + 1

    text = "\n".join(out) + "\n"
    path.write_text(text, encoding="utf-8")
    leftovers = [(k + 1, line) for k, line in enumerate(out) if " _ _ := by" in line]
    for line_no, line in leftovers:
        print(f"RESIDUAL {path.name}:{line_no}: {line}")
    return changed


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--dir", required=True)
    ns = ap.parse_args()
    root = Path(ns.dir)
    files = sorted(root.glob("V26FinalNumericN*Generated.lean"))
    if len(files) != 10:
        raise SystemExit(f"expected 10 generated numeric modules, found {len(files)}")
    total = 0
    residual = 0
    for path in files:
        n = normalize_file(path)
        text = path.read_text(encoding="utf-8")
        residual += text.count(" _ _ := by")
        print(f"{path.name}: normalized {n} ball transports")
        total += n
    if total == 0:
        raise SystemExit("no generated ball transports were normalized")
    print(f"NORMALIZATION: {total} transports; residual placeholders: {residual}")


if __name__ == "__main__":
    main()
