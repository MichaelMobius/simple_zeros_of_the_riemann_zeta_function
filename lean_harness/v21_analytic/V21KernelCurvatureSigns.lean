import HurtadoZeta23.V21KernelSecondDerivativeSigns
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic

noncomputable section

namespace HurtadoZeta23

/-- The second-lobe phase stays in the central cosine-positive strip. -/
lemma v21_phase15_mem_halfpi {x : ℝ}
    (hxlo : (6 / 5 : ℝ) ≤ x) (hxhi : x ≤ (179 / 100 : ℝ)) :
    v21Phase15 x ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
  have hleft : -(1 / 2 : ℝ) ≤ x - (3 / 2 : ℝ) := by linarith
  have hright : x - (3 / 2 : ℝ) ≤ (1 / 2 : ℝ) := by linarith
  have hl := mul_le_mul_of_nonneg_left hleft Real.pi_pos.le
  have hr := mul_le_mul_of_nonneg_left hright Real.pi_pos.le
  unfold v21Phase15
  constructor <;> nlinarith

/-- The third-lobe phase likewise stays in the central cosine-positive strip. -/
lemma v21_phase25_mem_halfpi {x : ℝ}
    (hxlo : (237 / 100 : ℝ) ≤ x) (hxhi : x ≤ (261 / 100 : ℝ)) :
    v21Phase25 x ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
  have hleft : -(1 / 2 : ℝ) ≤ x - (5 / 2 : ℝ) := by linarith
  have hright : x - (5 / 2 : ℝ) ≤ (1 / 2 : ℝ) := by linarith
  have hl := mul_le_mul_of_nonneg_left hleft Real.pi_pos.le
  have hr := mul_le_mul_of_nonneg_left hright Real.pi_pos.le
  unfold v21Phase25
  constructor <;> nlinarith

lemma v21_B_gt_two_second_band {x : ℝ} (hx : (6 / 5 : ℝ) ≤ x) :
    2 < v21B x := by
  have hxpos : 0 < x := by linarith
  have h := mul_lt_mul_of_pos_right Real.pi_gt_three hxpos
  unfold v21B
  nlinarith

lemma v21_B_gt_two_third_band {x : ℝ} (hx : (237 / 100 : ℝ) ≤ x) :
    2 < v21B x := by
  have hxpos : 0 < x := by linarith
  have h := mul_lt_mul_of_pos_right Real.pi_gt_three hxpos
  unfold v21B
  nlinarith

/-- On the right half of the second lobe the phase is at most one radian. -/
lemma v21_phase15_right_bounds {x : ℝ}
    (hxlo : (3 / 2 : ℝ) ≤ x) (hxhi : x ≤ (179 / 100 : ℝ)) :
    0 ≤ v21Phase15 x ∧ v21Phase15 x ≤ 1 := by
  have hgap0 : 0 ≤ x - (3 / 2 : ℝ) := by linarith
  have hgap1 : x - (3 / 2 : ℝ) ≤ (29 / 100 : ℝ) := by linarith
  have h0 := mul_nonneg Real.pi_pos.le hgap0
  have hu := mul_le_mul_of_nonneg_left hgap1 Real.pi_pos.le
  have hpi := v21_pi_upper
  unfold v21Phase15
  constructor
  · exact h0
  · nlinarith

/-- On the right half of the third lobe the phase is at most one half radian. -/
lemma v21_phase25_right_bounds {x : ℝ}
    (hxlo : (5 / 2 : ℝ) ≤ x) (hxhi : x ≤ (261 / 100 : ℝ)) :
    0 ≤ v21Phase25 x ∧ v21Phase25 x ≤ (1 / 2 : ℝ) := by
  have hgap0 : 0 ≤ x - (5 / 2 : ℝ) := by linarith
  have hgap1 : x - (5 / 2 : ℝ) ≤ (11 / 100 : ℝ) := by linarith
  have h0 := mul_nonneg Real.pi_pos.le hgap0
  have hu := mul_le_mul_of_nonneg_left hgap1 Real.pi_pos.le
  have hpi := v21_pi_upper
  unfold v21Phase25
  constructor
  · exact h0
  · nlinarith

/-- Elementary phase comparison used on the right half of the second lobe. -/
lemma v21_sin_phase15_le_two_cos {x : ℝ}
    (hxlo : (3 / 2 : ℝ) ≤ x) (hxhi : x ≤ (179 / 100 : ℝ)) :
    Real.sin (v21Phase15 x) ≤ 2 * Real.cos (v21Phase15 x) := by
  obtain ⟨ht0, ht1⟩ := v21_phase15_right_bounds hxlo hxhi
  have hprod : 0 ≤ v21Phase15 x * (1 - v21Phase15 x) :=
    mul_nonneg ht0 (sub_nonneg.mpr ht1)
  have hsq : (v21Phase15 x) ^ 2 ≤ 1 := by nlinarith
  have hcos := Real.one_sub_sq_div_two_le_cos (x := v21Phase15 x)
  have hcoshalf : (1 / 2 : ℝ) ≤ Real.cos (v21Phase15 x) := by
    nlinarith
  have hsin := Real.sin_le_one (v21Phase15 x)
  nlinarith

/-- Elementary phase comparison used on the right half of the third lobe. -/
lemma v21_sin_phase25_le_cos {x : ℝ}
    (hxlo : (5 / 2 : ℝ) ≤ x) (hxhi : x ≤ (261 / 100 : ℝ)) :
    Real.sin (v21Phase25 x) ≤ Real.cos (v21Phase25 x) := by
  obtain ⟨ht0, ht12⟩ := v21_phase25_right_bounds hxlo hxhi
  have hprod :
      0 ≤ v21Phase25 x * ((1 / 2 : ℝ) - v21Phase25 x) :=
    mul_nonneg ht0 (sub_nonneg.mpr ht12)
  have hsq : (v21Phase25 x) ^ 2 ≤ (1 / 4 : ℝ) := by nlinarith
  have hcos := Real.one_sub_sq_div_two_le_cos (x := v21Phase25 x)
  have hcoshalf : (1 / 2 : ℝ) ≤ Real.cos (v21Phase25 x) := by
    nlinarith
  have habs := Real.abs_sin_le_abs (x := v21Phase25 x)
  have hsleabs : Real.sin (v21Phase25 x) ≤ |Real.sin (v21Phase25 x)| :=
    le_abs_self _
  rw [abs_of_nonneg ht0] at habs
  have hsinh : Real.sin (v21Phase25 x) ≤ (1 / 2 : ℝ) := by
    linarith
  linarith

/-- Cleared second-derivative numerator is nonnegative throughout the second
excluded band `[1.20,1.79]`. -/
lemma v21_M2_nonneg_second_band {x : ℝ}
    (hxlo : (6 / 5 : ℝ) ≤ x) (hxhi : x ≤ (179 / 100 : ℝ)) :
    0 ≤ v21M2 (v21B x) := by
  have hb2 := v21_B_gt_two_second_band hxlo
  have hP : v21P2 (v21B x) < 0 := v21_P2_neg_of_two_lt hb2
  have hQ : v21Q2 (v21B x) < 0 := v21_Q2_neg_of_two_lt hb2
  have hphase := v21_phase15_mem_halfpi hxlo hxhi
  have hcos : 0 ≤ Real.cos (v21Phase15 x) :=
    Real.cos_nonneg_of_mem_Icc hphase
  unfold v21M2
  rw [v21_cosB_phase15, v21_sinB_phase15]
  by_cases hxmid : x ≤ (3 / 2 : ℝ)
  · have ht0 : v21Phase15 x ≤ 0 := by
      unfold v21Phase15
      exact mul_nonpos_of_nonneg_of_nonpos Real.pi_pos.le (sub_nonpos.mpr hxmid)
    have htpi : -Real.pi ≤ v21Phase15 x := by
      linarith [hphase.1, Real.pi_pos]
    have hsin : Real.sin (v21Phase15 x) ≤ 0 :=
      Real.sin_nonpos_of_nonpos_of_neg_pi_le ht0 htpi
    have hps :
        0 ≤ v21P2 (v21B x) * Real.sin (v21Phase15 x) :=
      mul_nonneg_of_nonpos_of_nonpos hP.le hsin
    have hqc :
        v21Q2 (v21B x) * Real.cos (v21Phase15 x) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hQ.le hcos
    nlinarith
  · have hxmid' : (3 / 2 : ℝ) ≤ x := le_of_not_ge hxmid
    have hsc := v21_sin_phase15_le_two_cos hxmid' hxhi
    have hb47 : (47 / 10 : ℝ) ≤ v21B x := by
      have hm := mul_le_mul_of_nonneg_left hxmid' Real.pi_pos.le
      have hpi := v21_pi_lower
      unfold v21B at hm ⊢
      nlinarith
    have hQP := v21_Q2_le_two_P2 hb47
    have hp0 : 0 ≤ -v21P2 (v21B x) := by linarith
    have hqcomp : -2 * v21P2 (v21B x) ≤ -v21Q2 (v21B x) := by
      linarith
    have h1 := mul_le_mul_of_nonneg_left hsc hp0
    have h2 := mul_le_mul_of_nonneg_right hqcomp hcos
    nlinarith

/-- Cleared second-derivative numerator is nonpositive throughout the third
excluded band `[2.37,2.61]`. -/
lemma v21_M2_nonpos_third_band {x : ℝ}
    (hxlo : (237 / 100 : ℝ) ≤ x) (hxhi : x ≤ (261 / 100 : ℝ)) :
    v21M2 (v21B x) ≤ 0 := by
  have hb2 := v21_B_gt_two_third_band hxlo
  have hP : v21P2 (v21B x) < 0 := v21_P2_neg_of_two_lt hb2
  have hQ : v21Q2 (v21B x) < 0 := v21_Q2_neg_of_two_lt hb2
  have hphase := v21_phase25_mem_halfpi hxlo hxhi
  have hcos : 0 ≤ Real.cos (v21Phase25 x) :=
    Real.cos_nonneg_of_mem_Icc hphase
  unfold v21M2
  rw [v21_cosB_phase25, v21_sinB_phase25]
  by_cases hxmid : x ≤ (5 / 2 : ℝ)
  · have ht0 : v21Phase25 x ≤ 0 := by
      unfold v21Phase25
      exact mul_nonpos_of_nonneg_of_nonpos Real.pi_pos.le (sub_nonpos.mpr hxmid)
    have htpi : -Real.pi ≤ v21Phase25 x := by
      linarith [hphase.1, Real.pi_pos]
    have hsin : Real.sin (v21Phase25 x) ≤ 0 :=
      Real.sin_nonpos_of_nonpos_of_neg_pi_le ht0 htpi
    have hps :
        0 ≤ v21P2 (v21B x) * Real.sin (v21Phase25 x) :=
      mul_nonneg_of_nonpos_of_nonpos hP.le hsin
    have hqc :
        v21Q2 (v21B x) * Real.cos (v21Phase25 x) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hQ.le hcos
    nlinarith
  · have hxmid' : (5 / 2 : ℝ) ≤ x := le_of_not_ge hxmid
    have hsc := v21_sin_phase25_le_cos hxmid' hxhi
    have hb74 : (74 / 10 : ℝ) ≤ v21B x := by
      have hm := mul_le_mul_of_nonneg_left hxmid' Real.pi_pos.le
      unfold v21B at hm ⊢
      nlinarith [Real.pi_gt_three]
    have hQP := v21_Q2_le_P2 hb74
    have hp0 : 0 ≤ -v21P2 (v21B x) := by linarith
    have hqcomp : -v21P2 (v21B x) ≤ -v21Q2 (v21B x) := by linarith
    have h1 := mul_le_mul_of_nonneg_left hsc hp0
    have h2 := mul_le_mul_of_nonneg_right hqcomp hcos
    nlinarith

end HurtadoZeta23
