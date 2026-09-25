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

/-- Exact overlap of two nonresonant cosine frequencies on `[-1/2,1/2]`. -/
theorem research9_integral_cos_mul_cos
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
  · change F (1 / 2 : ℝ) - F (-1 / 2 : ℝ) =
      Real.sin ((a - b) / 2) / (a - b) +
        Real.sin ((a + b) / 2) / (a + b)
    simp only [F]
    have h1p : (a - b) * (1 / 2 : ℝ) = (a - b) / 2 := by ring
    have h2p : (a + b) * (1 / 2 : ℝ) = (a + b) / 2 := by ring
    have h1m : (a - b) * (-1 / 2 : ℝ) = -((a - b) / 2) := by ring
    have h2m : (a + b) * (-1 / 2 : ℝ) = -((a + b) / 2) := by ring
    rw [h1p, h2p, h1m, h2m, Real.sin_neg, Real.sin_neg]
    ring
  · intro s _
    exact hderiv s
  · exact Continuous.intervalIntegrable (by fun_prop) _ _

/-- The one-frequency normalization integral. -/
theorem research9_integral_cos
    (a : ℝ) (ha : a ≠ 0) :
    (∫ s in (-1 / 2 : ℝ)..(1 / 2 : ℝ), Real.cos (a * s))
      = 2 * Real.sin (a / 2) / a := by
  have h := research9_integral_cos_mul_cos a 0 (by simpa using ha) (by simpa using ha)
  have h' :
      (∫ s in (-1 / 2 : ℝ)..(1 / 2 : ℝ), Real.cos (a * s))
        = Real.sin (a / 2) / a + Real.sin (a / 2) / a := by
    simpa using h
  calc
    (∫ s in (-1 / 2 : ℝ)..(1 / 2 : ℝ), Real.cos (a * s))
        = Real.sin (a / 2) / a + Real.sin (a / 2) / a := h'
    _ = 2 * Real.sin (a / 2) / a := by ring

/-- Every nonzero integer Fourier mode has zero mean on the unit interval. -/
theorem research9_integral_integer_cos
    (n : ℕ) (hn : 0 < n) :
    (∫ s in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
        Real.cos ((2 * Real.pi * n) * s)) = 0 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have ha : (2 * Real.pi * (n : ℝ)) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) hpi) hn0
  rw [research9_integral_cos (2 * Real.pi * (n : ℝ)) ha]
  have harg : (2 * Real.pi * (n : ℝ)) / 2 = (n : ℝ) * Real.pi := by ring
  rw [harg]
  simp

/-- Sanity check at two rational frequencies. -/
theorem research9_integral_cos_mul_cos_sanity :
    (∫ s in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
        Real.cos (3 * s) * Real.cos (2 * s))
      = Real.sin (1 / 2) + Real.sin (5 / 2) / 5 := by
  have h := research9_integral_cos_mul_cos (3 : ℝ) (2 : ℝ) (by norm_num) (by norm_num)
  norm_num at h ⊢
  exact h

end HurtadoZeta23
