import HurtadoZeta23.ResearchWindowKernel086v2
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

noncomputable section

open Real Set MeasureTheory intervalIntegral
open scoped Real Interval

namespace HurtadoZeta23

/-!
# Integral bridge for the nine-point research window

The first step is a reusable exact formula for the overlap of two cosine
frequencies on `[-1/2,1/2]`.
-/

private lemma research9_integral_cos_mul_cos
    (a b : ℝ) (hsub : a - b ≠ 0) (hadd : a + b ≠ 0) :
    (∫ s in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
        Real.cos (a * s) * Real.cos (b * s))
      = Real.sin ((a - b) / 2) / (a - b)
        + Real.sin ((a + b) / 2) / (a + b) := by
  let F : ℝ → ℝ := fun s =>
    (Real.sin ((a - b) * s) / (a - b)
      + Real.sin ((a + b) * s) / (a + b)) / 2
  have hderiv : ∀ s : ℝ,
      HasDerivAt F (Real.cos (a * s) * Real.cos (b * s)) s := by
    intro s
    have h1 :=
      ((Real.hasDerivAt_sin ((a - b) * s)).comp s
        (hasDerivAt_const_mul (a - b))).div_const (a - b)
    have h2 :=
      ((Real.hasDerivAt_sin ((a + b) * s)).comp s
        (hasDerivAt_const_mul (a + b))).div_const (a + b)
    have h := (h1.add h2).div_const (2 : ℝ)
    have hF :
        HasDerivAt F
          ((Real.cos ((a - b) * s) + Real.cos ((a + b) * s)) / 2) s := by
      simpa [F, hsub, hadd] using h
    have hp := Real.two_mul_cos_mul_cos (a * s) (b * s)
    have hminus : a * s - b * s = (a - b) * s := by ring
    have hplus : a * s + b * s = (a + b) * s := by ring
    rw [hminus, hplus] at hp
    convert hF using 1
    nlinarith [hp]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt]
  · dsimp [F]
    ring_nf
    simp only [Real.sin_neg]
    ring
  · intro s _
    exact hderiv s
  · exact Continuous.intervalIntegrable (by fun_prop) _ _

/-- Sanity check at two rational frequencies. -/
theorem research9_integral_cos_mul_cos_sanity :
    (∫ s in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
        Real.cos (3 * s) * Real.cos (2 * s))
      = Real.sin (1 / 2) + Real.sin (5 / 2) / 5 := by
  have h := research9_integral_cos_mul_cos (3 : ℝ) (2 : ℝ) (by norm_num) (by norm_num)
  norm_num at h ⊢
  exact h

end HurtadoZeta23
