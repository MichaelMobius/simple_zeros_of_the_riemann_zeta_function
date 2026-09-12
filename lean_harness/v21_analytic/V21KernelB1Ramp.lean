import HurtadoZeta23.V21KernelB1Convex
import Mathlib.Analysis.Convex.Slope
import Mathlib.Tactic

noncomputable section

open Set

namespace HurtadoZeta23

private def v21B1Slope : ℝ := 29 / 40
private def v21B1Left : ℝ := v21RootLeft 1
private def v21B1Right : ℝ := v21RootRight 1
private def v21B1Mid : ℝ := v21RootMid 1
private def v21B1Upper : ℝ := 6 / 5

lemma v21_kernelX_eq_limitingk {x : ℝ} (hx : v17KernelCertPoint < x) :
    v21KernelX x = limitingk x := by
  symm
  simpa [v21KernelX] using v21_limitingk_eq_kernelB (v21_A_lt_B_of_cert_lt hx)

lemma v21_B1_left_gt_cert : v17KernelCertPoint < v21B1Left := by
  norm_num [v21B1Left, v21RootLeft, v17KernelCertPoint]

lemma v21_B1_right_gt_cert : v17KernelCertPoint < v21B1Right := by
  norm_num [v21B1Right, v21RootRight, v17KernelCertPoint]

lemma v21_B1_upper_gt_cert : v17KernelCertPoint < v21B1Upper := by
  norm_num [v21B1Upper, v17KernelCertPoint]

lemma v21_k_B1_left_nonneg : 0 ≤ limitingk v21B1Left := by
  have hH := v21_root_left_sign (n := 1) (by norm_num) (by norm_num)
  have hH0 : v21RootH 1 v21B1Left ≤ 0 := by
    simpa [v21B1Left] using hH.trans (by norm_num : (-(7 / 100000 : ℝ)) ≤ 0)
  have hA := v21_A_lt_B_of_cert_lt v21_B1_left_gt_cert
  have hD : 0 < v21D v21B1Left := v21_D_pos hA
  rw [v21_limitingk_eq_sign_rootH_div (n := 1) v21_B1_left_gt_cert]
  norm_num
  exact div_nonneg (neg_nonneg.mpr hH0) hD.le

lemma v21_k_B1_right_nonpos : limitingk v21B1Right ≤ 0 := by
  have hH := v21_root_right_sign (n := 1) (by norm_num) (by norm_num)
  have hH0 : 0 ≤ v21RootH 1 v21B1Right := by
    simpa [v21B1Right] using (by
      have : (0 : ℝ) ≤ (1 / 100000 : ℝ) := by norm_num
      exact this.trans hH)
  have hA := v21_A_lt_B_of_cert_lt v21_B1_right_gt_cert
  have hD : 0 < v21D v21B1Right := v21_D_pos hA
  rw [v21_limitingk_eq_sign_rootH_div (n := 1) v21_B1_right_gt_cert]
  norm_num
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hH0) hD.le

lemma v21_rootH_one_at_120_lower :
    (71 / 50 : ℝ) ≤ v21RootH 1 (6 / 5 : ℝ) := by
  calc
    (71 / 50 : ℝ) ≤
        v21RootCL * v21RootPiL * (6 / 5 : ℝ) *
            v21RootSinLower7 (v21RootPiL * (1 / 5 : ℝ)) -
          (1 / 2 : ℝ) *
            v21RootCosUpper8 (v21RootPiL * (1 / 5 : ℝ)) := by
      norm_num [v21RootCL, v21RootPiL, v21RootSinLower7,
        v21RootCosUpper8]
    _ ≤ v21RootH 1 (6 / 5 : ℝ) := by
      exact v21_rootH_lower_bound
        (n := 1) (x := (6 / 5 : ℝ)) (e := (1 / 5 : ℝ))
        (by norm_num) (by norm_num) (by norm_num [v21RootPiU])

lemma v21_D_120_upper :
    v21D (6 / 5 : ℝ) ≤ (343 / 25 : ℝ) := by
  calc
    v21D (6 / 5 : ℝ) ≤ v21RootDenCap (6 / 5 : ℝ) :=
      v21_D_le_rootDenCap (by norm_num) (by norm_num)
    _ ≤ (343 / 25 : ℝ) := by
      norm_num [v21RootDenCap, v21RootPiU]

lemma v21_k_B1_upper_endpoint :
    limitingk v21B1Upper ≤
      -v21B1Slope * (v21B1Upper - v21B1Left) := by
  have hA := v21_A_lt_B_of_cert_lt v21_B1_upper_gt_cert
  have hD : 0 < v21D v21B1Upper := v21_D_pos hA
  have hH : (71 / 50 : ℝ) ≤ v21RootH 1 v21B1Upper := by
    simpa [v21B1Upper] using v21_rootH_one_at_120_lower
  have hDup : v21D v21B1Upper ≤ (343 / 25 : ℝ) := by
    simpa [v21B1Upper] using v21_D_120_upper
  have hratio : (71 / 686 : ℝ) ≤
      v21RootH 1 v21B1Upper / v21D v21B1Upper := by
    apply (le_div_iff₀ hD).2
    calc
      (71 / 686 : ℝ) * v21D v21B1Upper ≤
          (71 / 686 : ℝ) * (343 / 25 : ℝ) :=
        mul_le_mul_of_nonneg_left hDup (by norm_num)
      _ = (71 / 50 : ℝ) := by norm_num
      _ ≤ v21RootH 1 v21B1Upper := hH
  have hslope :
      v21B1Slope * (v21B1Upper - v21B1Left) ≤ (71 / 686 : ℝ) := by
    norm_num [v21B1Slope, v21B1Upper, v21B1Left, v21RootLeft]
  have hcompare :
      v21B1Slope * (v21B1Upper - v21B1Left) ≤
        v21RootH 1 v21B1Upper / v21D v21B1Upper :=
    hslope.trans hratio
  have hneg :
      -(v21RootH 1 v21B1Upper / v21D v21B1Upper) ≤
        -v21B1Slope * (v21B1Upper - v21B1Left) := by
    calc
      -(v21RootH 1 v21B1Upper / v21D v21B1Upper) ≤
          -(v21B1Slope * (v21B1Upper - v21B1Left)) := neg_le_neg hcompare
      _ = -v21B1Slope * (v21B1Upper - v21B1Left) := by ring
  rw [v21_limitingk_eq_sign_rootH_div (n := 1) v21_B1_upper_gt_cert]
  norm_num
  simpa [neg_div] using hneg

lemma v21_kernelX_B1_left_nonneg : 0 ≤ v21KernelX v21B1Left := by
  rw [v21_kernelX_eq_limitingk v21_B1_left_gt_cert]
  exact v21_k_B1_left_nonneg

lemma v21_kernelX_B1_right_nonpos : v21KernelX v21B1Right ≤ 0 := by
  rw [v21_kernelX_eq_limitingk v21_B1_right_gt_cert]
  exact v21_k_B1_right_nonpos

lemma v21_kernelX_B1_upper_endpoint :
    v21KernelX v21B1Upper ≤
      -v21B1Slope * (v21B1Upper - v21B1Left) := by
  rw [v21_kernelX_eq_limitingk v21_B1_upper_gt_cert]
  exact v21_k_B1_upper_endpoint

lemma v21_k_B1_left_linear {x : ℝ}
    (hxlo : (19 / 20 : ℝ) ≤ x) (hxL : x ≤ v21B1Left) :
    v21B1Slope * (v21B1Left - x) ≤ limitingk x := by
  by_cases hxeq : x = v21B1Left
  · subst x
    simp [v21_k_B1_left_nonneg]
  have hxlt : x < v21B1Left := lt_of_le_of_ne hxL hxeq
  have hLU : v21B1Left < v21B1Upper := by
    norm_num [v21B1Left, v21B1Upper, v21RootLeft]
  have hxU : x ≤ v21B1Upper := hxL.trans hLU.le
  have hxmem : x ∈ Icc (19 / 20 : ℝ) (6 / 5 : ℝ) := by
    exact ⟨hxlo, by simpa [v21B1Upper] using hxU⟩
  have hLmem : v21B1Left ∈ Icc (19 / 20 : ℝ) (6 / 5 : ℝ) := by
    norm_num [v21B1Left, v21RootLeft]
  have hUmem : v21B1Upper ∈ Icc (19 / 20 : ℝ) (6 / 5 : ℝ) := by
    norm_num [v21B1Upper]
  have hsec := v21_kernelX_convex_B1.slope_mono_adjacent
    hxmem hUmem hxlt hLU
  have hright :
      (v21KernelX v21B1Upper - v21KernelX v21B1Left) /
          (v21B1Upper - v21B1Left) ≤ -v21B1Slope := by
    apply (div_le_iff₀ (sub_pos.mpr hLU)).2
    have hU := v21_kernelX_B1_upper_endpoint
    have hL := v21_kernelX_B1_left_nonneg
    nlinarith
  have hslope := hsec.trans hright
  have hden : 0 < v21B1Left - x := sub_pos.mpr hxlt
  have hmul := (div_le_iff₀ hden).1 hslope
  have hL := v21_kernelX_B1_left_nonneg
  have hxcert : v17KernelCertPoint < x := by
    have : (89 / 100 : ℝ) < x := by nlinarith
    simpa [v17KernelCertPoint] using this
  rw [v21_kernelX_eq_limitingk hxcert] at hmul
  nlinarith

lemma v21_k_B1_right_linear {x : ℝ}
    (hxR : v21B1Right ≤ x) (hxhi : x ≤ v21B1Upper) :
    limitingk x ≤ -v21B1Slope * (x - v21B1Right) := by
  by_cases hxR_eq : x = v21B1Right
  · subst x
    simpa using v21_k_B1_right_nonpos
  by_cases hxU_eq : x = v21B1Upper
  · subst x
    have hU := v21_k_B1_upper_endpoint
    have hLR : v21B1Left ≤ v21B1Right := by
      norm_num [v21B1Left, v21B1Right, v21RootLeft, v21RootRight]
    have hS0 : 0 ≤ v21B1Slope := by norm_num [v21B1Slope]
    have hgap : v21B1Upper - v21B1Right ≤ v21B1Upper - v21B1Left := by linarith
    have hneg :
        -v21B1Slope * (v21B1Upper - v21B1Left) ≤
          -v21B1Slope * (v21B1Upper - v21B1Right) := by
      exact mul_le_mul_of_nonpos_left hgap (by nlinarith)
    exact hU.trans hneg
  have hRx : v21B1Right < x := lt_of_le_of_ne hxR (Ne.symm hxR_eq)
  have hxU : x < v21B1Upper := lt_of_le_of_ne hxhi hxU_eq
  have hRmem : v21B1Right ∈ Icc (19 / 20 : ℝ) (6 / 5 : ℝ) := by
    norm_num [v21B1Right, v21RootRight]
  have hUmem : v21B1Upper ∈ Icc (19 / 20 : ℝ) (6 / 5 : ℝ) := by
    norm_num [v21B1Upper]
  have haux := v21_kernelX_convex_B1.secant_mono_aux1
    hRmem hUmem hRx hxU
  have hR := v21_kernelX_B1_right_nonpos
  have hU := v21_kernelX_B1_upper_endpoint
  have hUx0 : 0 ≤ v21B1Upper - x := sub_nonneg.mpr hxhi
  have hxR0 : 0 ≤ x - v21B1Right := sub_nonneg.mpr hxR
  have htermR :
      (v21B1Upper - x) * v21KernelX v21B1Right ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hUx0 hR
  have htermU :
      (x - v21B1Right) * v21KernelX v21B1Upper ≤
        (x - v21B1Right) *
          (-v21B1Slope * (v21B1Upper - v21B1Left)) :=
    mul_le_mul_of_nonneg_left hU hxR0
  have hchord :
      (v21B1Upper - v21B1Right) * v21KernelX x ≤
        (-v21B1Slope * (x - v21B1Right)) *
          (v21B1Upper - v21B1Left) := by
    calc
      (v21B1Upper - v21B1Right) * v21KernelX x ≤
          (v21B1Upper - x) * v21KernelX v21B1Right +
            (x - v21B1Right) * v21KernelX v21B1Upper := haux
      _ ≤ 0 + (x - v21B1Right) *
            (-v21B1Slope * (v21B1Upper - v21B1Left)) :=
        add_le_add htermR htermU
      _ = (-v21B1Slope * (x - v21B1Right)) *
            (v21B1Upper - v21B1Left) := by ring
  have hLR : v21B1Left ≤ v21B1Right := by
    norm_num [v21B1Left, v21B1Right, v21RootLeft, v21RootRight]
  have hlen :
      v21B1Upper - v21B1Right ≤ v21B1Upper - v21B1Left := by
    linarith
  have hnegcoef : -v21B1Slope * (x - v21B1Right) ≤ 0 := by
    have hS0 : 0 ≤ v21B1Slope := by norm_num [v21B1Slope]
    nlinarith
  have hscale :
      (-v21B1Slope * (x - v21B1Right)) *
          (v21B1Upper - v21B1Left) ≤
        (-v21B1Slope * (x - v21B1Right)) *
          (v21B1Upper - v21B1Right) :=
    mul_le_mul_of_nonpos_left hlen hnegcoef
  have hmain := hchord.trans hscale
  have hUR : 0 < v21B1Upper - v21B1Right := by
    norm_num [v21B1Upper, v21B1Right, v21RootRight]
  have hkX :
      v21KernelX x ≤ -v21B1Slope * (x - v21B1Right) := by
    nlinarith
  have hxcert : v17KernelCertPoint < x := by
    have hRcert := v21_B1_right_gt_cert
    exact hRcert.trans_le hxR
  rwa [v21_kernelX_eq_limitingk hxcert] at hkX

/-- Strong absolute-value ramp on the entire first survivor band. -/
lemma v21_k_abs_ge_B1_ramp {x : ℝ}
    (hxlo : (19 / 20 : ℝ) ≤ x) (hxhi : x ≤ (6 / 5 : ℝ)) :
    v21B1Slope * v21RootRamp 1 x ≤ |limitingk x| := by
  by_cases hleft : x ≤ v21B1Left
  · rw [v21_root_ramp_eq_left (n := 1) (by norm_num) (by norm_num) hleft]
    exact (v21_k_B1_left_linear hxlo hleft).trans (le_abs_self _)
  · have hLx : v21B1Left ≤ x := le_of_not_ge hleft
    by_cases hright : v21B1Right ≤ x
    · rw [v21_root_ramp_eq_right (n := 1) (by norm_num) (by norm_num) hright]
      have hk := v21_k_B1_right_linear hright (by simpa [v21B1Upper] using hxhi)
      have hneg : v21B1Slope * (x - v21B1Right) ≤ -limitingk x := by
        linarith
      have hnegabs : -limitingk x ≤ |limitingk x| := neg_le_abs _
      simpa [v21B1Right] using hneg.trans hnegabs
    · have hxR : x ≤ v21B1Right := le_of_not_ge hright
      rw [v21_root_ramp_eq_zero_of_mem_bracket (n := 1)
        (by norm_num) (by norm_num) hLx hxR, mul_zero]
      exact abs_nonneg _

lemma v21_weight_ge_B1_ramp_sq {x : ℝ}
    (hxlo : (19 / 20 : ℝ) ≤ x) (hxhi : x ≤ (6 / 5 : ℝ)) :
    v21B1Slope ^ 2 * (v21RootRamp 1 x) ^ 2 ≤ limitingWeight x := by
  have habs := v21_k_abs_ge_B1_ramp hxlo hxhi
  have hleft0 : 0 ≤ v21B1Slope * v21RootRamp 1 x :=
    mul_nonneg (by norm_num [v21B1Slope]) (v21_root_ramp_nonneg 1 x)
  have hs := pow_le_pow_left₀ hleft0 habs 2
  unfold limitingWeight
  simpa [mul_pow] using hs

lemma v21_ramp_sq_ge_quadratic_999 (z : ℝ) :
    (999 / 1000 : ℝ) * z ^ 2 -
        999 * (1 / 200000 : ℝ) ^ 2 ≤
      (max (|z| - (1 / 200000 : ℝ)) 0) ^ 2 := by
  by_cases hz : |z| ≤ (1 / 200000 : ℝ)
  · have hmax : max (|z| - (1 / 200000 : ℝ)) 0 = 0 :=
      max_eq_right (sub_nonpos.mpr hz)
    rw [hmax]
    have hp :
        0 ≤ ((1 / 200000 : ℝ) - |z|) *
          ((1 / 200000 : ℝ) + |z|) := by
      apply mul_nonneg
      · exact sub_nonneg.mpr hz
      · positivity
    have habs : |z| ^ 2 = z ^ 2 := sq_abs z
    nlinarith
  · have hz' : (1 / 200000 : ℝ) ≤ |z| := le_of_not_ge hz
    rw [max_eq_left (sub_nonneg.mpr hz')]
    have habs : |z| ^ 2 = z ^ 2 := sq_abs z
    nlinarith [sq_nonneg (|z| - 1000 * (1 / 200000 : ℝ))]

/-- Strong B1 one-body kernel floor, centered entirely at the rational bracket
midpoint.  The small constant is the explicit price of not choosing a root. -/
lemma v21_one_third_weight_B1_quadratic {x : ℝ}
    (hxlo : (19 / 20 : ℝ) ≤ x) (hxhi : x ≤ (6 / 5 : ℝ)) :
    (7 / 40 : ℝ) * (x - v21B1Mid) ^ 2 -
        (280053 / 64000000000000 : ℝ) ≤
      (1 / 3 : ℝ) * limitingWeight x := by
  have hw := v21_weight_ge_B1_ramp_sq hxlo hxhi
  have hq := v21_ramp_sq_ge_quadratic_999 (x - v21B1Mid)
  have hscale :
      v21B1Slope ^ 2 *
          ((999 / 1000 : ℝ) * (x - v21B1Mid) ^ 2 -
            999 * (1 / 200000 : ℝ) ^ 2) ≤
        v21B1Slope ^ 2 * (v21RootRamp 1 x) ^ 2 := by
    simpa [v21RootRamp, v21RootHalfWidth, v21B1Mid] using
      mul_le_mul_of_nonneg_left hq (sq_nonneg v21B1Slope)
  have hcombined := hscale.trans hw
  have hthird := mul_le_mul_of_nonneg_left hcombined (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hcoef :
      (7 / 40 : ℝ) ≤
        (1 / 3 : ℝ) * v21B1Slope ^ 2 * (999 / 1000 : ℝ) := by
    norm_num [v21B1Slope]
  have herr :
      (1 / 3 : ℝ) * v21B1Slope ^ 2 *
          999 * (1 / 200000 : ℝ) ^ 2 =
        (280053 / 64000000000000 : ℝ) := by
    norm_num [v21B1Slope]
  nlinarith [sq_nonneg (x - v21B1Mid)]

end HurtadoZeta23