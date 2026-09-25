import HurtadoZeta23.ResearchWeightedPressure289
import HurtadoZeta23.ResearchStrongBlock289
import Mathlib.Tactic

noncomputable section

open Matrix Finset
open scoped BigOperators ComplexOrder

namespace HurtadoZeta23

/-!
# Conditional finite interfaces for the research `m = 289` hybrid

This file does **not** assert the pinned nine-point certificate.  Instead it
packages exactly the finite consequences that must be supplied after the
independent 96/96 replay and internal certificate formalization.

There are 288 adjacent gaps in a 289-point block.  For each gap `r`, `q r` is
the local certificate capacity and `g r` is the nonnegative gap parameter.
-/

/-- Summing the one-gap actual-window pressure inequality over all 288 gaps
produces the weighted block inequality from the four finite interfaces:
capacity bounds, exact total capacity, adjacent-band control, and pressure
control. -/
theorem research9_weighted_block_pressure_fin288
    (q g : Fin 288 → ℝ)
    {D P : ℝ}
    (hq0 : ∀ r, 0 ≤ q r)
    (hqβ : ∀ r, q r ≤ research9Beta)
    (hg : ∀ r, 0 ≤ g r)
    (hqsum : ∑ r, q r = research9Q)
    (hband : ∑ r, research9WindowWeightAt (g r) ≤ D)
    (hpressure : ∑ r, q r * g r ≤ P) :
    research9t * research9g0 * research9Q ≤ D + research9t * P := by
  have hlocal : ∀ r : Fin 288,
      research9t * q r * research9g0 ≤
        research9WindowWeightAt (g r) + research9t * q r * g r := by
    intro r
    exact research9_window_one_gap_pressure (hq0 r) (hqβ r) (hg r)

  have hsum :
      (∑ r : Fin 288, research9t * q r * research9g0) ≤
        ∑ r : Fin 288,
          (research9WindowWeightAt (g r) + research9t * q r * g r) := by
    exact Finset.sum_le_sum fun r hr => hlocal r

  have hleft :
      (∑ r : Fin 288, research9t * q r * research9g0) =
        research9t * research9g0 * research9Q := by
    calc
      (∑ r : Fin 288, research9t * q r * research9g0)
          = ∑ r : Fin 288, (research9t * research9g0) * q r := by
              apply Finset.sum_congr rfl
              intro r hr
              ring
      _ = (research9t * research9g0) * ∑ r : Fin 288, q r := by
            rw [Finset.mul_sum]
      _ = research9t * research9g0 * research9Q := by rw [hqsum]

  have hright :
      (∑ r : Fin 288,
          (research9WindowWeightAt (g r) + research9t * q r * g r)) =
        (∑ r : Fin 288, research9WindowWeightAt (g r)) +
          research9t * (∑ r : Fin 288, q r * g r) := by
    rw [Finset.sum_add_distrib]
    congr 1
    calc
      (∑ r : Fin 288, research9t * q r * g r)
          = ∑ r : Fin 288, research9t * (q r * g r) := by
              apply Finset.sum_congr rfl
              intro r hr
              ring
      _ = research9t * (∑ r : Fin 288, q r * g r) := by
            rw [Finset.mul_sum]

  have ht0 : 0 ≤ research9t := by norm_num [research9t]
  have hpressure_scaled :
      research9t * (∑ r : Fin 288, q r * g r) ≤ research9t * P :=
    mul_le_mul_of_nonneg_left hpressure ht0

  rw [hleft, hright] at hsum
  linarith

/-- Matrix-facing conditional strong-block theorem.  Once the certificate and
adjacent-pair layer provide the stated finite interfaces, all weighted scalar
algebra and the `289/288` PSD spectral threshold are internal. -/
theorem research9_strong_block_289_from_finite_interfaces
    (G : Matrix (Fin 289) (Fin 289) ℂ)
    (hG : G.PosSemidef)
    (hdiag : ∀ i : Fin 289, (G i i).re ≤ 1)
    (q g : Fin 288 → ℝ)
    {P : ℝ}
    (hq0 : ∀ r, 0 ≤ q r)
    (hqβ : ∀ r, q r ≤ research9Beta)
    (hg : ∀ r, 0 ≤ g r)
    (hqsum : ∑ r, q r = research9Q)
    (hEP : research9A ≤ offDiagonalEnergy G + P)
    (hband :
      ∑ r, research9WindowWeightAt (g r) ≤ gramSpectralDefect G hG)
    (hpressure : ∑ r, q r * g r ≤ P) :
    research9A ≤ gramSpectralDefect G hG + P := by
  have hweighted :
      research9t * research9g0 * research9Q ≤
        gramSpectralDefect G hG + research9t * P :=
    research9_weighted_block_pressure_fin288
      q g hq0 hqβ hg hqsum hband hpressure
  exact research9_strong_block_289_of_matrix_interfaces
    G hG hdiag hEP hweighted

end HurtadoZeta23
