import HurtadoZeta23.V21KernelCellTools
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic

noncomputable section

namespace HurtadoZeta23

/-- The normalized kernel as a function of the phase variable `b = π x`. -/
def v21KernelB (b : ℝ) : ℝ :=
  (v21C * b * Real.sin b - (1 / 2 : ℝ) * Real.cos b) /
    (b ^ 2 - (1 / 2 : ℝ))

/-- Numerator of the first derivative of `v21KernelB`, after clearing the
square of the denominator. -/
def v21M1 (b : ℝ) : ℝ :=
  (v21C * b ^ 3 - (1 / 2 : ℝ) * v21C * b + b) * Real.cos b +
    (-v21C * b ^ 2 + (1 / 2 : ℝ) * b ^ 2 -
      (1 / 2 : ℝ) * v21C - (1 / 4 : ℝ)) * Real.sin b

/-- Cosine coefficient of the second-derivative numerator. -/
def v21P2 (b : ℝ) : ℝ :=
  (-2 * v21C + (1 / 2 : ℝ)) * b ^ 4 -
    (7 / 2 : ℝ) * b ^ 2 + (1 / 2 : ℝ) * v21C - (3 / 8 : ℝ)

/-- Sine coefficient of the second-derivative numerator. -/
def v21Q2 (b : ℝ) : ℝ :=
  -v21C * b ^ 5 + 3 * v21C * b ^ 3 - 2 * b ^ 3 +
    (11 / 4 : ℝ) * v21C * b + b

/-- Numerator of the second derivative of `v21KernelB`, after clearing the
cube of the denominator. -/
def v21M2 (b : ℝ) : ℝ :=
  v21P2 b * Real.cos b + v21Q2 b * Real.sin b

/-- The x-space normalized kernel is exactly `v21KernelB` evaluated at `π x`. -/
theorem v21_limitingk_eq_kernelB {x : ℝ}
    (hx : v21A < v21B x) :
    limitingk x = v21KernelB (v21B x) := by
  simpa [v21KernelB] using v21_limitingk_normalized (x := x) hx

/-- Exact first derivative of the phase-normalized kernel.  This is kept in
factored-denominator form so sign arguments can avoid quotient expansion. -/
theorem v21_kernelB_hasDerivAt {b : ℝ}
    (hD : b ^ 2 - (1 / 2 : ℝ) ≠ 0) :
    HasDerivAt v21KernelB
      (v21M1 b / (b ^ 2 - (1 / 2 : ℝ)) ^ 2) b := by
  have hraw :=
    ((((hasDerivAt_const b v21C).mul (hasDerivAt_id b)).mul
        (Real.hasDerivAt_sin b)).sub
      ((hasDerivAt_const b (1 / 2 : ℝ)).mul
        (Real.hasDerivAt_cos b)))
  have hrawDeriv := hraw.congr_deriv
    (g' := v21C * Real.sin b + v21C * b * Real.cos b +
      (1 / 2 : ℝ) * Real.sin b) (by
      simp only [Pi.mul_apply, id_eq]
      ring)
  have hnum :
      HasDerivAt
        (fun t : ℝ =>
          v21C * t * Real.sin t - (1 / 2 : ℝ) * Real.cos t)
        (v21C * Real.sin b + v21C * b * Real.cos b +
          (1 / 2 : ℝ) * Real.sin b) b := by
    refine hrawDeriv.congr_of_eventuallyEq ?_
    filter_upwards with t
    simp only [Pi.mul_apply, Pi.sub_apply, id_eq]
  have hdenRaw := ((hasDerivAt_id b).pow 2).sub_const (1 / 2 : ℝ)
  have hdenRaw' := hdenRaw.congr_deriv (g' := 2 * b) (by
    simp only [id_eq]
    ring)
  have hden :
      HasDerivAt
        (fun t : ℝ => t ^ 2 - (1 / 2 : ℝ))
        (2 * b) b := by
    refine hdenRaw'.congr_of_eventuallyEq ?_
    filter_upwards with t
    simp only [Pi.pow_apply, id_eq]
  change HasDerivAt
    (fun t : ℝ =>
      (v21C * t * Real.sin t - (1 / 2 : ℝ) * Real.cos t) /
        (t ^ 2 - (1 / 2 : ℝ)))
    (v21M1 b / (b ^ 2 - (1 / 2 : ℝ)) ^ 2) b
  have hq := hnum.div hden hD
  apply hq.congr_deriv
  unfold v21M1
  field_simp [hD]
  ring

end HurtadoZeta23
