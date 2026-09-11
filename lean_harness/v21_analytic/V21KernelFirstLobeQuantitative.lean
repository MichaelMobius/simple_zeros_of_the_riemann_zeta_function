import HurtadoZeta23.V21KernelFirstLobeSign
import Mathlib.Tactic

noncomputable section

namespace HurtadoZeta23

/-- A deliberately coarse lower bound for the normalized profile constant.
It is much weaker than `v21_C_lower`, but convenient in polynomial sign
estimates. -/
lemma v21_C_ge_four_fifths : (4 / 5 : ℝ) ≤ v21C := by
  have hrat : (4 / 5 : ℝ) ≤ 88280819 / 106683860 := by norm_num
  exact hrat.trans v21_C_lower

/-- On the whole first hard-core band, the phase derivative of the normalized
kernel is uniformly bounded away from zero.  The constant `1/200` is chosen
for proof slack, not sharpness. -/
lemma v21_kernelB_deriv_le_first_band {x : ℝ}
    (hxlo : (89 / 100 : ℝ) ≤ x) (hxhi : x ≤ (19 / 20 : ℝ)) :
    v21M1 (v21B x) /
        ((v21B x) ^ 2 - (1 / 2 : ℝ)) ^ 2 ≤ -(1 / 200 : ℝ) := by
  let b : ℝ := v21B x
  have hxpos : 0 < x := by norm_num at hxlo ⊢; linarith
  have hxlt1 : x < 1 := by norm_num at hxhi ⊢; linarith

  have hbpos : 0 < b := by
    dsimp [b, v21B]
    exact mul_pos Real.pi_pos hxpos
  have hb267 : (267 / 100 : ℝ) < b := by
    have h3x : 3 * x < Real.pi * x :=
      mul_lt_mul_of_pos_right Real.pi_gt_three hxpos
    dsimp [b, v21B]
    nlinarith
  have hb3 : b < 3 := by
    have hmono : Real.pi * x ≤ Real.pi * (19 / 20 : ℝ) :=
      mul_le_mul_of_nonneg_left hxhi Real.pi_pos.le
    have hpi := v21_pi_upper
    dsimp [b, v21B]
    nlinarith
  have hbpi2 : Real.pi / 2 < b := by
    have hxhalf : (1 / 2 : ℝ) < x := by norm_num at hxlo ⊢; linarith
    have h := mul_lt_mul_of_pos_left hxhalf Real.pi_pos
    dsimp [b, v21B]
    nlinarith
  have hbpi : b < Real.pi := by
    have h := mul_lt_mul_of_pos_left hxlt1 Real.pi_pos
    dsimp [b, v21B]
    simpa using h

  have hb2gt7 : (7 : ℝ) < b ^ 2 := by
    have hs := sq_nonneg (b - (267 / 100 : ℝ))
    nlinarith
  have hDpos : 0 < b ^ 2 - (1 / 2 : ℝ) := by
    nlinarith

  have hC : (4 / 5 : ℝ) ≤ v21C := v21_C_ge_four_fifths
  have hscale :
      (4 / 5 : ℝ) * (b ^ 2 + (1 / 2 : ℝ)) ≤
        v21C * (b ^ 2 + (1 / 2 : ℝ)) := by
    exact mul_le_mul_of_nonneg_right hC (by positivity)
  have hS :
      -v21C * b ^ 2 + (1 / 2 : ℝ) * b ^ 2 -
          (1 / 2 : ℝ) * v21C - (1 / 4 : ℝ) ≤ -(11 / 4 : ℝ) := by
    nlinarith [hscale, hb2gt7]

  have hphaseLower : (3 / 20 : ℝ) < v21Phase1 x := by
    have hgap : (1 / 20 : ℝ) ≤ 1 - x := by
      norm_num at hxhi ⊢
      linarith
    have hmul := mul_le_mul_of_nonneg_left hgap Real.pi_pos.le
    dsimp [v21Phase1]
    nlinarith [Real.pi_gt_three]
  have hphaseUpper : v21Phase1 x ≤ Real.pi / 2 := by
    have hgap : 1 - x ≤ (11 / 100 : ℝ) := by
      norm_num at hxlo ⊢
      linarith
    have hmul := mul_le_mul_of_nonneg_left hgap Real.pi_pos.le
    dsimp [v21Phase1]
    nlinarith [Real.pi_pos]

  have hsinTaylor :=
    v20_sin_lower7 (x := (3 / 20 : ℝ)) (by norm_num) (by norm_num)
  have hsinRat :
      (7 / 50 : ℝ) <
        (3 / 20 : ℝ) - (3 / 20 : ℝ) ^ 3 / 6 +
          (3 / 20 : ℝ) ^ 5 / 120 - (3 / 20 : ℝ) ^ 7 / 5040 := by
    norm_num
  have hsinBase : (7 / 50 : ℝ) < Real.sin (3 / 20 : ℝ) :=
    hsinRat.trans_le hsinTaylor
  have hsinMono :
      Real.sin (3 / 20 : ℝ) ≤ Real.sin (v21Phase1 x) := by
    apply Real.sin_le_sin_of_le_of_le_pi_div_two
    · nlinarith [Real.pi_pos]
    · exact hphaseUpper
    · exact le_of_lt hphaseLower
  have hsinPhase : (7 / 50 : ℝ) < Real.sin (v21Phase1 x) :=
    hsinBase.trans_le hsinMono
  have hsinB : (7 / 50 : ℝ) < Real.sin b := by
    dsimp [b]
    rw [v21_sinB_phase1]
    exact hsinPhase

  have hCpos : 0 < v21C := by nlinarith [v21_C_gt_half]
  have hRpos :
      0 < v21C * b ^ 3 - (1 / 2 : ℝ) * v21C * b + b := by
    have hprod : 0 < v21C * b * (b ^ 2 - (1 / 2 : ℝ)) :=
      mul_pos (mul_pos hCpos hbpos) hDpos
    nlinarith
  have hcos : Real.cos b < 0 :=
    Real.cos_neg_of_pi_div_two_lt_of_lt hbpi2 (by nlinarith [Real.pi_pos, hbpi])
  have hleft :
      (v21C * b ^ 3 - (1 / 2 : ℝ) * v21C * b + b) * Real.cos b ≤ 0 :=
    (mul_neg_of_pos_of_neg hRpos hcos).le

  have hsinB0 : 0 ≤ Real.sin b := by nlinarith [hsinB]
  have hright1 :
      (-v21C * b ^ 2 + (1 / 2 : ℝ) * b ^ 2 -
          (1 / 2 : ℝ) * v21C - (1 / 4 : ℝ)) * Real.sin b ≤
        -(11 / 4 : ℝ) * Real.sin b :=
    mul_le_mul_of_nonneg_right hS hsinB0
  have hright2 :
      -(11 / 4 : ℝ) * Real.sin b ≤ -(77 / 200 : ℝ) := by
    have h := mul_le_mul_of_nonpos_left (le_of_lt hsinB)
      (by norm_num : -(11 / 4 : ℝ) ≤ 0)
    norm_num at h ⊢
    exact h
  have hM : v21M1 b ≤ -(77 / 200 : ℝ) := by
    unfold v21M1
    nlinarith [hleft, hright1, hright2]

  have h9mb2 : 0 < 9 - b ^ 2 := by
    have hprod := mul_pos (sub_pos.mpr hb3) (add_pos (by norm_num) hbpos)
    nlinarith
  have hDlt : b ^ 2 - (1 / 2 : ℝ) < (17 / 2 : ℝ) := by
    nlinarith
  have hDsqLt73 : (b ^ 2 - (1 / 2 : ℝ)) ^ 2 < 73 := by
    have hprod := mul_pos (sub_pos.mpr hDlt)
      (add_pos (by norm_num : (0 : ℝ) < 17 / 2) hDpos)
    nlinarith
  have hDsqPos : 0 < (b ^ 2 - (1 / 2 : ℝ)) ^ 2 :=
    sq_pos_of_pos hDpos

  dsimp [b] at hM hDsqLt73 hDsqPos ⊢
  apply (div_le_iff₀ hDsqPos).2
  nlinarith [hM, hDsqLt73]

end HurtadoZeta23
