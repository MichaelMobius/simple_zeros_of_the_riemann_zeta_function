import Mathlib.Tactic

noncomputable section

open scoped BigOperators

namespace HurtadoZeta23

/-- A sum of nonnegative square terms lies above its constant part. -/
theorem v26_sos_lower {ι : Type*} [Fintype ι]
    (q : ℝ) (d y : ι → ℝ) (hd : ∀ i, 0 ≤ d i) :
    q ≤ q + ∑ i, d i * (y i) ^ 2 := by
  have hs : 0 ≤ ∑ i, d i * (y i) ^ 2 := by
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hd i) (sq_nonneg (y i))
  linarith

/-- Weighted Cauchy--Schwarz in the exact form needed for the ellipsoid
contractions.  The proof uses no square roots. -/
theorem v26_weighted_cauchy {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a y d : ι → ℝ) (hd : ∀ i, 0 < d i) :
    (∑ i, a i * y i) ^ 2 ≤
      (∑ i, d i * (y i) ^ 2) * (∑ i, (a i) ^ 2 / d i) := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
  · intro i hi
    exact mul_nonneg (hd i).le (sq_nonneg (y i))
  · intro i hi
    exact div_nonneg (sq_nonneg (a i)) (hd i).le
  · intro i hi
    calc
      (a i * y i) ^ 2 = (a i) ^ 2 * (y i) ^ 2 := by ring
      _ = (d i * (y i) ^ 2) * ((a i) ^ 2 / d i) := by
        field_simp [(hd i).ne']
        <;> ring
      _ ≤ _ := le_rfl

/-- If the SOS energy is bounded by `gap`, weighted Cauchy gives the squared
linear-functional radius used by every rational contraction. -/
theorem v26_weighted_cauchy_of_energy {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a y d : ι → ℝ) (hd : ∀ i, 0 < d i) (gap : ℝ)
    (henergy : (∑ i, d i * (y i) ^ 2) ≤ gap) :
    (∑ i, a i * y i) ^ 2 ≤
      gap * (∑ i, (a i) ^ 2 / d i) := by
  have hc := v26_weighted_cauchy a y d hd
  have hnorm : 0 ≤ ∑ i, (a i) ^ 2 / d i := by
    exact Finset.sum_nonneg fun i _ => div_nonneg (sq_nonneg (a i)) (hd i).le
  exact hc.trans (mul_le_mul_of_nonneg_right henergy hnorm)

/-- Turn a strict rational squared-radius certificate into the usual absolute
value bound. -/
theorem v26_abs_lt_radius_of_sq_le {z rad2 R : ℝ}
    (hR : 0 ≤ R) (hz : z ^ 2 ≤ rad2) (hrad : rad2 < R ^ 2) :
    |z| < R := by
  have hsq : z ^ 2 < R ^ 2 := lt_of_le_of_lt hz hrad
  rw [sq_lt_sq] at hsq
  simpa [abs_of_nonneg hR] using hsq

end HurtadoZeta23
