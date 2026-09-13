import HurtadoZeta23.V21KernelIntervalCurvature
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic

noncomputable section

open Set

namespace HurtadoZeta23

/-- First derivative of the squared normalized kernel in physical x-space. -/
def v26WeightXPrime (x : ℝ) : ℝ :=
  2 * v21KernelX x * v21KernelXPrime x

/-- Second derivative of the squared normalized kernel in physical x-space. -/
def v26WeightXSecond (x : ℝ) : ℝ :=
  2 * ((v21KernelXPrime x) ^ 2 + v21KernelX x * v21KernelXSecond x)

/-- On the certified hard core, the article's nonnegative weight is exactly
    the square of the differentiable normalized kernel. -/
theorem v26_limitingWeight_eq_kernelX_sq {x : ℝ}
    (hx : v17KernelCertPoint < x) :
    limitingWeight x = (v21KernelX x) ^ 2 := by
  unfold limitingWeight
  rw [v21_limitingk_eq_kernelB (v21_A_lt_B_of_cert_lt hx)]
  rfl

/-- Exact first derivative of the squared kernel. -/
theorem v26_weightX_hasDerivAt {x : ℝ}
    (hD : (v21B x) ^ 2 - (1 / 2 : ℝ) ≠ 0) :
    HasDerivAt (fun y : ℝ => (v21KernelX y) ^ 2) (v26WeightXPrime x) x := by
  have h := (v21_kernelX_hasDerivAt hD).pow 2
  exact h.congr_deriv (g' := v26WeightXPrime x) (by
    unfold v26WeightXPrime
    norm_num
    ring)

/-- Exact second derivative of the squared kernel. -/
theorem v26_weightXPrime_hasDerivAt {x : ℝ}
    (hD : (v21B x) ^ 2 - (1 / 2 : ℝ) ≠ 0) :
    HasDerivAt v26WeightXPrime (v26WeightXSecond x) x := by
  have hk := v21_kernelX_hasDerivAt hD
  have hkp := v21_kernelXPrime_hasDerivAt hD
  have h := (hk.const_mul 2).mul hkp
  have h' := h.congr_deriv (g' := v26WeightXSecond x) (by
    unfold v26WeightXSecond
    ring)
  simpa only [v26WeightXPrime, Pi.mul_apply] using h'

end HurtadoZeta23
