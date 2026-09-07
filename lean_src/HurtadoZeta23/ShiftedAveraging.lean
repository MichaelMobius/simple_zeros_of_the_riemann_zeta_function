import HurtadoZeta23.BlockStability
import Mathlib.Tactic

namespace HurtadoZeta23

/--
Algebraic core of shifted-block averaging.

This isolates the combinatorial asymptotic statement proved in the paper:
  D(M°) ≥ (A₀/m) S - ((m-1)/(500m)) N - error.
The theorem rewrites those coefficients to the exact rationals used by the
final endgame.
-/
theorem shifted_block_coefficients
    {gramDefect simpleCount totalCount err : ℝ}
    (h : A0 / blockLength * simpleCount
          - (((blockLength - 1 : ℕ) : ℝ) / (500 * (blockLength : ℝ))) * totalCount
          - err ≤ gramDefect) :
    alpha * simpleCount - pressureCost * totalCount - err ≤ gramDefect := by
  rw [alpha_eq_A0_div_m, pressureCost_eq]
  exact h

/--
Combining the Zeta23 Montgomery--Taylor baseline with a shifted-block Gram
lower bound gives the raw global refinement inequality.
-/
theorem combine_baseline_and_defect
    {N S D errBase errBlock : ℝ}
    (hBase : HMT * N + D - errBase ≤ S)
    (hBlock : alpha * S - pressureCost * N - errBlock ≤ D) :
    HMT * N + alpha * S - pressureCost * N - (errBase + errBlock) ≤ S := by
  linarith

end HurtadoZeta23
