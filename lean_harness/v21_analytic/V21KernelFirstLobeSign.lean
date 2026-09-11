import HurtadoZeta23.V21KernelDerivatives
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

noncomputable section

namespace HurtadoZeta23

/-- On the first oscillatory lobe the cleared first-derivative numerator is
strictly negative.  The proof uses only `C > 1/2` and the elementary signs
of sine and cosine on `(π/2, π)`. -/
lemma v21_M1_neg_first_lobe {b : ℝ}
    (hblo : Real.pi / 2 < b) (hbhi : b < Real.pi) :
    v21M1 b < 0 := by
  have hCpos : 0 < v21C := by
    nlinarith [v21_C_gt_half]
  have hbpos : 0 < b := by
    nlinarith [Real.pi_pos, hblo]
  have hb1 : 1 < b := by
    nlinarith [Real.pi_gt_three, hblo]
  have hbsq : 1 < b ^ 2 := by
    nlinarith [sq_nonneg (b - 1)]
  have hDpos : 0 < b ^ 2 - (1 / 2 : ℝ) := by
    nlinarith

  have hRpos :
      0 < v21C * b ^ 3 - (1 / 2 : ℝ) * v21C * b + b := by
    have hprod : 0 < v21C * b * (b ^ 2 - (1 / 2 : ℝ)) :=
      mul_pos (mul_pos hCpos hbpos) hDpos
    nlinarith

  have hcoef : (1 / 2 : ℝ) - v21C < 0 := by
    linarith [v21_C_gt_half]
  have hquad :
      ((1 / 2 : ℝ) - v21C) * b ^ 2 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (le_of_lt hcoef) (sq_nonneg b)
  have htail : -(1 / 2 : ℝ) * v21C - (1 / 4 : ℝ) < 0 := by
    nlinarith [v21_C_gt_half]
  have hSneg :
      -v21C * b ^ 2 + (1 / 2 : ℝ) * b ^ 2 -
          (1 / 2 : ℝ) * v21C - (1 / 4 : ℝ) < 0 := by
    nlinarith [hquad, htail]

  have hsin : 0 < Real.sin b :=
    Real.sin_pos_of_pos_of_lt_pi hbpos hbhi
  have hcos : Real.cos b < 0 := by
    apply Real.cos_neg_of_pi_div_two_lt_of_lt hblo
    nlinarith [Real.pi_pos, hbhi]
  have hleft :
      (v21C * b ^ 3 - (1 / 2 : ℝ) * v21C * b + b) * Real.cos b < 0 :=
    mul_neg_of_pos_of_neg hRpos hcos
  have hright :
      (-v21C * b ^ 2 + (1 / 2 : ℝ) * b ^ 2 -
          (1 / 2 : ℝ) * v21C - (1 / 4 : ℝ)) * Real.sin b < 0 :=
    mul_neg_of_neg_of_pos hSneg hsin
  unfold v21M1
  linarith

/-- Consequently the phase-normalized kernel has strictly negative
first derivative throughout the first lobe, away from the algebraic pole. -/
lemma v21_kernelB_deriv_neg_first_lobe {b : ℝ}
    (hblo : Real.pi / 2 < b) (hbhi : b < Real.pi) :
    v21M1 b / (b ^ 2 - (1 / 2 : ℝ)) ^ 2 < 0 := by
  have hM := v21_M1_neg_first_lobe hblo hbhi
  have hb1 : 1 < b := by
    nlinarith [Real.pi_gt_three, hblo]
  have hbsq : 1 < b ^ 2 := by
    nlinarith [sq_nonneg (b - 1)]
  have hD : 0 < b ^ 2 - (1 / 2 : ℝ) := by
    nlinarith
  exact div_neg_of_neg_of_pos hM (sq_pos_of_pos hD)

end HurtadoZeta23
