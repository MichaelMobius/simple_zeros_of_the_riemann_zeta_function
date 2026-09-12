import HurtadoZeta23.V21OneBodyFloors
import HurtadoZeta23.V21KernelRootWeight
import Mathlib.Tactic

noncomputable section

namespace HurtadoZeta23

/-- The short type-C tail after the sixth retained basin is ruled out by the
already-certified sixth-root quadratic.  The lower quadratic is frozen at
`x = 6.078`, where it still leaves a positive rational margin over the type-C
one-body threshold. -/
theorem v21_oneBody_C_tail6 {j : Fin 6} {x : ℝ}
    (hp : (3553 / 10000000 : ℝ) ≤ pressure j)
    (hxL : (6078 / 1000 : ℝ) ≤ x)
    (hxU : x ≤ (21700 / 3553 : ℝ)) :
    (2170 / 1000000 : ℝ) ≤ v21OneBody j x := by
  let U : ℝ := 21700 / 3553
  let L : ℝ := 6078 / 1000
  have hx0 : 0 ≤ x := by nlinarith
  have hxU' : x ≤ U := by simpa [U] using hxU
  have hxCellL : (6 : ℝ) - (1 / 20 : ℝ) ≤ x := by
    dsimp [L] at hxL
    nlinarith
  have hxCellU : x ≤ (6 : ℝ) + (151 / 1000 : ℝ) := by
    have hcap : U ≤ (6 : ℝ) + (151 / 1000 : ℝ) := by
      dsimp [U]
      norm_num
    exact hxU'.trans hcap
  have hw := v21_weight_ge_root_quadratic
    (n := 6) (x := x) (U := U)
    (by norm_num) (by norm_num) hxCellL hxCellU hxU'
  have hLm : 0 ≤ L - v21RootMid 6 := by
    dsimp [L]
    norm_num [v21RootMid, v21RootLeft, v21RootRight]
  have hdist : L - v21RootMid 6 ≤ x - v21RootMid 6 := by
    dsimp [L] at hxL ⊢
    linarith
  have hsq :
      (L - v21RootMid 6) ^ 2 ≤ (x - v21RootMid 6) ^ 2 :=
    pow_le_pow_left₀ hLm hdist 2
  have hqform :
      (99 / 100 : ℝ) * (L - v21RootMid 6) ^ 2 -
          99 * (1 / 200000 : ℝ) ^ 2 ≤
        (99 / 100 : ℝ) * (x - v21RootMid 6) ^ 2 -
          99 * (1 / 200000 : ℝ) ^ 2 := by
    nlinarith
  have hcoef0 :
      0 ≤ ((7 * (6 : ℝ)) ^ 2 / (v21RootDenCap U) ^ 2) := by
    positivity
  have hw' :
      ((7 * (6 : ℝ)) ^ 2 / (v21RootDenCap U) ^ 2) *
          ((99 / 100 : ℝ) * (x - v21RootMid 6) ^ 2 -
            99 * (1 / 200000 : ℝ) ^ 2) ≤
        limitingWeight x := by
    calc
      ((7 * (6 : ℝ)) ^ 2 / (v21RootDenCap U) ^ 2) *
          ((99 / 100 : ℝ) * (x - v21RootMid 6) ^ 2 -
            99 * (1 / 200000 : ℝ) ^ 2) =
        (((7 * (6 : ℝ)) ^ 2) *
          ((99 / 100 : ℝ) * (x - v21RootMid 6) ^ 2 -
            99 * (1 / 200000 : ℝ) ^ 2)) /
          (v21RootDenCap U) ^ 2 := by ring
      _ ≤ limitingWeight x := hw
  have hwconst :
      ((7 * (6 : ℝ)) ^ 2 / (v21RootDenCap U) ^ 2) *
          ((99 / 100 : ℝ) * (L - v21RootMid 6) ^ 2 -
            99 * (1 / 200000 : ℝ) ^ 2) ≤
        limitingWeight x := by
    exact (mul_le_mul_of_nonneg_left hqform hcoef0).trans hw'
  have hpressureL :
      (3553 / 10000000 : ℝ) * L ≤
        (3553 / 10000000 : ℝ) * x := by
    apply mul_le_mul_of_nonneg_left
    · simpa [L] using hxL
    · norm_num
  have hpressure :
      (3553 / 10000000 : ℝ) * x ≤ pressure j * x :=
    mul_le_mul_of_nonneg_right hp hx0
  have harith :
      (2170 / 1000000 : ℝ) ≤
        (3553 / 10000000 : ℝ) * L +
          (1 / 3 : ℝ) *
            (((7 * (6 : ℝ)) ^ 2 / (v21RootDenCap U) ^ 2) *
              ((99 / 100 : ℝ) * (L - v21RootMid 6) ^ 2 -
                99 * (1 / 200000 : ℝ) ^ 2)) := by
    dsimp [L, U]
    norm_num [v21RootDenCap, v21RootMid, v21RootLeft,
      v21RootRight, v21RootPiU]
  unfold v21OneBody
  nlinarith

end HurtadoZeta23
