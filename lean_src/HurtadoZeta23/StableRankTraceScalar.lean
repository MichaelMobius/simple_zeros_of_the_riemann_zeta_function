import HurtadoZeta23.BlockDefect
import Zeta23.Assembly
import Mathlib.Tactic

noncomputable section

open Matrix Finset RHLinalg

namespace HurtadoZeta23

/-- Scalar core of the stability-enhanced rank--trace inequality.
For fixed `p ≥ 0`, the function `(p-n)^2 + 4n` on `n ≥ 0` is bounded below
by `2p - 1 + psi p`.  This is the exact scalar minimisation used in the paper. -/
theorem stable_scalar_min {p n : ℝ} (hp : 0 ≤ p) (hn : 0 ≤ n) :
    2 * p - 1 + psi p ≤ (p - n)^2 + 4 * n := by
  by_cases hp2 : p ≤ 2
  · rw [psi_eq_sq hp2]
    have h : 0 ≤ n * (2 * (2 - p) + n) := by positivity
    nlinarith
  · have hp2' : 2 < p := lt_of_not_ge hp2
    rw [psi_eq_linear hp2']
    have hsq : 0 ≤ (n - (p - 2))^2 := sq_nonneg _
    nlinarith

/-- Summed scalar lower bound used after von Neumann's trace inequality.
This contains no matrix theory: once paired eigenvalues `p_i,n_i` are known,
the stability defect sums term-by-term. -/
theorem stable_scalar_sum
    {ι : Type*} [Fintype ι]
    (p n : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i)
    (hn : ∀ i, 0 ≤ n i) :
    ∑ i, (2 * p i - 1 + psi (p i))
      ≤ ∑ i, ((p i - n i)^2 + 4 * n i) := by
  apply Finset.sum_le_sum
  intro i hi
  exact stable_scalar_min (hp i) (hn i)

/-- Algebraic finishing step for the enhanced rank--trace inequality.

The genuinely spectral/matrix input has been compressed to `hminus_plus`.
The final use of `tr P ≤ r` is exactly the one appearing in the article. -/
theorem stable_rank_trace_finish
    {trP trQ trA frA defect : ℝ} {r b : ℕ}
    (htrA : trA = trP + trQ)
    (htrP : trP ≤ r)
    (hminus_plus :
      4 * trA - 2 * trP - (r : ℝ) - 4 * (b : ℝ) + defect ≤ frA) :
    4 * trA - 3 * (r : ℝ) - 4 * (b : ℝ) + defect ≤ frA := by
  linarith

/-- Convert the enhanced Frobenius lower bound into the fixed-`T` simple-zero
core used by `StableCoreAt`.

This is the algebra of the article with `r = s₁` and `b = s₂+p`:
`r + 2b ≤ N(I')` turns

`4 tr A - 3r - 4b + D ≤ ‖A‖²`

into

`4 tr A - 2N(I') - ‖A‖² + D ≤ r`.
-/
theorem stable_zeroside_core_finish
    {trA frA defect NI' : ℝ} {r b : ℕ}
    (henh : 4 * trA - 3 * (r : ℝ) - 4 * (b : ℝ) + defect ≤ frA)
    (hNcount : (r : ℝ) + 2 * (b : ℝ) ≤ NI') :
    4 * trA - 2 * NI' - frA + defect ≤ r := by
  linarith

end HurtadoZeta23
