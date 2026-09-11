import HurtadoZeta23.V21KernelDerivatives
import Mathlib.Tactic

noncomputable section

namespace HurtadoZeta23

/-- The explicit derivative of the cleared first-derivative numerator. -/
def v21M1Prime (b : ℝ) : ℝ :=
  (-v21C * b ^ 3 - (3 / 2 : ℝ) * v21C * b) * Real.sin b +
    (2 * v21C * b ^ 2 - v21C + (1 / 2 : ℝ) * b ^ 2 + (3 / 4 : ℝ)) *
      Real.cos b

/-- The first derivative of the phase-normalized kernel, exposed as a
function so that the second derivative can be certified independently. -/
def v21KernelBPrime (b : ℝ) : ℝ :=
  v21M1 b / (b ^ 2 - (1 / 2 : ℝ)) ^ 2

/-- Exact derivative of `v21M1`. -/
theorem v21_M1_hasDerivAt (b : ℝ) :
    HasDerivAt v21M1 (v21M1Prime b) b := by
  have hR0 :=
    ((((hasDerivAt_id b).pow 3).const_mul v21C).sub
      ((hasDerivAt_id b).const_mul ((1 / 2 : ℝ) * v21C))).add
      (hasDerivAt_id b)
  have hR :
      HasDerivAt
        (fun t : ℝ => v21C * t ^ 3 - (1 / 2 : ℝ) * v21C * t + t)
        (3 * v21C * b ^ 2 - (1 / 2 : ℝ) * v21C + 1) b := by
    apply hR0.congr_deriv
    ring

  have hS0 :=
    (((((hasDerivAt_id b).pow 2).const_mul (-v21C)).add
      (((hasDerivAt_id b).pow 2).const_mul (1 / 2 : ℝ))).sub_const
      ((1 / 2 : ℝ) * v21C + (1 / 4 : ℝ)))
  have hS :
      HasDerivAt
        (fun t : ℝ =>
          -v21C * t ^ 2 + (1 / 2 : ℝ) * t ^ 2 -
            (1 / 2 : ℝ) * v21C - (1 / 4 : ℝ))
        (-2 * v21C * b + b) b := by
    apply hS0.congr_deriv
    ring

  have hprod :=
    (hR.mul (Real.hasDerivAt_cos b)).add
      (hS.mul (Real.hasDerivAt_sin b))
  unfold v21M1 v21M1Prime
  apply hprod.congr_deriv
  ring

/-- The algebraic identity responsible for the compact second derivative:
`M₂ = M₁' D - 4 b M₁`. -/
lemma v21_M2_factor_identity (b : ℝ) :
    v21M2 b =
      v21M1Prime b * (b ^ 2 - (1 / 2 : ℝ)) - 4 * b * v21M1 b := by
  unfold v21M2 v21M1Prime v21M1 v21P2 v21Q2
  ring

/-- Exact second derivative of the normalized kernel in phase space. -/
theorem v21_kernelBPrime_hasDerivAt {b : ℝ}
    (hD : b ^ 2 - (1 / 2 : ℝ) ≠ 0) :
    HasDerivAt v21KernelBPrime
      (v21M2 b / (b ^ 2 - (1 / 2 : ℝ)) ^ 3) b := by
  have hm := v21_M1_hasDerivAt b
  have hd :
      HasDerivAt
        (fun t : ℝ => t ^ 2 - (1 / 2 : ℝ))
        (2 * b) b := by
    apply (((hasDerivAt_id b).pow 2).sub_const (1 / 2 : ℝ)).congr_deriv
    ring
  have hd2 := hd.pow 2
  have hq := hm.div hd2 (pow_ne_zero 2 hD)
  unfold v21KernelBPrime
  apply hq.congr_deriv
  rw [v21_M2_factor_identity]
  field_simp [hD]
  ring

end HurtadoZeta23
