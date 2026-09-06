import Mathlib.Tactic

noncomputable section

namespace HurtadoZeta23

/-- Squaring is 2-Lipschitz on `[0,1]`.  This is the scalar mechanism behind
turning an overlap error `eps` into the lower squared-entry loss `2*eps`. -/
theorem v17_sq_lower_of_abs_sub_le
    {a b eps : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (heps : 0 ≤ eps)
    (hab : |a - b| ≤ eps) :
    b ^ 2 - 2 * eps ≤ a ^ 2 := by
  by_cases hba : b ≤ a
  · have hsq : b ^ 2 ≤ a ^ 2 := by nlinarith
    linarith
  · have habpos : 0 ≤ b - a := by linarith
    have hdiff : b - a ≤ eps := by
      have h := le_trans (le_abs_self (b - a)) ?_
      · simpa [abs_sub_comm] using hab
      · exact h
    have hsum : a + b ≤ 2 := by linarith
    have hprod : (b - a) * (a + b) ≤ eps * 2 := by
      exact mul_le_mul hdiff hsum (by positivity) habpos
    nlinarith

/-- A convenient complex-valued corollary.  If the modulus of a complex
number is within `eps` of a kernel modulus in `[0,1]`, its squared modulus is
at least the kernel square minus `2*eps`. -/
theorem v17_norm_sq_lower_of_kernel_modulus_error
    {z : ℂ} {b eps : ℝ}
    (hz1 : ‖z‖ ≤ 1)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (heps : 0 ≤ eps)
    (herr : |‖z‖ - b| ≤ eps) :
    b ^ 2 - 2 * eps ≤ ‖z‖ ^ 2 := by
  exact v17_sq_lower_of_abs_sub_le (norm_nonneg z) hz1 hb0 hb1 heps herr

end HurtadoZeta23
