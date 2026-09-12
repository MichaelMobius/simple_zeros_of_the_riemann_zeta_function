import HurtadoZeta23.V21KernelRootWeight
import HurtadoZeta23.V21KernelIntervalCurvature
import Mathlib.Tactic

noncomputable section

open Set

namespace HurtadoZeta23

/-- On the left half of the first survivor band the Fourier phase lies in the
simple rational window `2.98 ≤ b ≤ 3.142`. -/
lemma v21_B1_left_b_bounds {x : ℝ}
    (hxlo : (19 / 20 : ℝ) ≤ x) (hxhi : x ≤ 1) :
    (149 / 50 : ℝ) ≤ v21B x ∧ v21B x ≤ (1571 / 500 : ℝ) := by
  have hpiL : v21RootPiL ≤ Real.pi := by
    simpa [v21RootPiL] using (le_of_lt v21_pi_lower)
  have hpiU : Real.pi ≤ v21RootPiU := by
    simpa [v21RootPiU] using (le_of_lt v21_pi_upper)
  have hx0 : 0 ≤ x := by linarith
  have hlow :
      v21RootPiL * (19 / 20 : ℝ) ≤ Real.pi * x := by
    exact mul_le_mul hpiL hxlo (by norm_num) Real.pi_pos.le
  have hupp :
      Real.pi * x ≤ v21RootPiU * (1 : ℝ) := by
    exact mul_le_mul hpiU hxhi hx0 (by norm_num [v21RootPiU])
  unfold v21B
  constructor
  · calc
      (149 / 50 : ℝ) ≤ v21RootPiL * (19 / 20 : ℝ) := by
        norm_num [v21RootPiL]
      _ ≤ Real.pi * x := hlow
  · calc
      Real.pi * x ≤ v21RootPiU * (1 : ℝ) := hupp
      _ ≤ (1571 / 500 : ℝ) := by norm_num [v21RootPiU]

/-- Very coarse upper bound for the cosine coefficient of the cleared second
derivative.  The large slack is intentional. -/
lemma v21_P2_le_neg100_B1_left {x : ℝ}
    (hxlo : (19 / 20 : ℝ) ≤ x) (hxhi : x ≤ 1) :
    v21P2 (v21B x) ≤ -(100 : ℝ) := by
  let b : ℝ := v21B x
  obtain ⟨hbL, hbU⟩ := v21_B1_left_b_bounds hxlo hxhi
  have hb0 : 0 ≤ b := by dsimp [b]; linarith
  have hClo : (4 / 5 : ℝ) ≤ v21C := by
    have hrat : (4 / 5 : ℝ) ≤ v21RootCL := by norm_num [v21RootCL]
    exact hrat.trans (by simpa [v21RootCL] using v21_C_lower)
  have hCU : v21C ≤ v21RootCU := by
    simpa [v21RootCU] using v21_C_upper
  have hcoef : -2 * v21C + (1 / 2 : ℝ) ≤ -(11 / 10 : ℝ) := by
    linarith
  have hb2L : (149 / 50 : ℝ) ^ 2 ≤ b ^ 2 :=
    pow_le_pow_left₀ (by norm_num) hbL 2
  have hb4L : (149 / 50 : ℝ) ^ 4 ≤ b ^ 4 :=
    pow_le_pow_left₀ (by norm_num) hbL 4
  have hterm4a :
      (-2 * v21C + (1 / 2 : ℝ)) * b ^ 4 ≤
        -(11 / 10 : ℝ) * b ^ 4 :=
    mul_le_mul_of_nonneg_right hcoef (pow_nonneg hb0 4)
  have hterm4b :
      -(11 / 10 : ℝ) * b ^ 4 ≤
        -(11 / 10 : ℝ) * (149 / 50 : ℝ) ^ 4 :=
    mul_le_mul_of_nonpos_left hb4L (by norm_num)
  have hterm2 :
      -(7 / 2 : ℝ) * b ^ 2 ≤
        -(7 / 2 : ℝ) * (149 / 50 : ℝ) ^ 2 :=
    mul_le_mul_of_nonpos_left hb2L (by norm_num)
  have htermC :
      (1 / 2 : ℝ) * v21C ≤ (1 / 2 : ℝ) * v21RootCU :=
    mul_le_mul_of_nonneg_left hCU (by norm_num)
  have hrat :
      -(11 / 10 : ℝ) * (149 / 50 : ℝ) ^ 4 -
          (7 / 2 : ℝ) * (149 / 50 : ℝ) ^ 2 +
          (1 / 2 : ℝ) * v21RootCU - (3 / 8 : ℝ) ≤ -(100 : ℝ) := by
    norm_num [v21RootCU]
  dsimp [b] at hterm4a hterm4b hterm2 ⊢
  unfold v21P2
  linarith

/-- Coarse lower bound for the sine coefficient on the same half-band.  This
uses the sharp rational enclosure for `C`, but still leaves over a quarter of
a unit of slack against `-250`. -/
lemma v21_Q2_ge_neg250_B1_left {x : ℝ}
    (hxlo : (19 / 20 : ℝ) ≤ x) (hxhi : x ≤ 1) :
    -(250 : ℝ) ≤ v21Q2 (v21B x) := by
  let b : ℝ := v21B x
  obtain ⟨hbL, hbU⟩ := v21_B1_left_b_bounds hxlo hxhi
  have hb0 : 0 ≤ b := by dsimp [b]; linarith
  have hCL : v21RootCL ≤ v21C := by
    simpa [v21RootCL] using v21_C_lower
  have hCU : v21C ≤ v21RootCU := by
    simpa [v21RootCU] using v21_C_upper
  have hC0 : 0 ≤ v21C := by nlinarith [v21_C_gt_half]
  have hCL0 : 0 ≤ v21RootCL := by norm_num [v21RootCL]
  have hCU0 : 0 ≤ v21RootCU := by norm_num [v21RootCU]
  have hb3L : (149 / 50 : ℝ) ^ 3 ≤ b ^ 3 :=
    pow_le_pow_left₀ (by norm_num) hbL 3
  have hb3U : b ^ 3 ≤ (1571 / 500 : ℝ) ^ 3 :=
    pow_le_pow_left₀ hb0 hbU 3
  have hb5U : b ^ 5 ≤ (1571 / 500 : ℝ) ^ 5 :=
    pow_le_pow_left₀ hb0 hbU 5
  have hCb5a : v21C * b ^ 5 ≤ v21RootCU * b ^ 5 :=
    mul_le_mul_of_nonneg_right hCU (pow_nonneg hb0 5)
  have hCb5b : v21RootCU * b ^ 5 ≤
      v21RootCU * (1571 / 500 : ℝ) ^ 5 :=
    mul_le_mul_of_nonneg_left hb5U hCU0
  have hCb3a : v21RootCL * (149 / 50 : ℝ) ^ 3 ≤
      v21C * (149 / 50 : ℝ) ^ 3 :=
    mul_le_mul_of_nonneg_right hCL (by positivity)
  have hCb3b : v21C * (149 / 50 : ℝ) ^ 3 ≤ v21C * b ^ 3 :=
    mul_le_mul_of_nonneg_left hb3L hC0
  have hlin0 :
      0 ≤ (11 / 4 : ℝ) * v21C * b + b := by positivity
  have hrat :
      -(250 : ℝ) ≤
        -v21RootCU * (1571 / 500 : ℝ) ^ 5 +
          3 * v21RootCL * (149 / 50 : ℝ) ^ 3 -
          2 * (1571 / 500 : ℝ) ^ 3 := by
    norm_num [v21RootCL, v21RootCU]
  dsimp [b] at hCb5a hCb5b hCb3a hCb3b hb3U hlin0 ⊢
  unfold v21Q2
  nlinarith

lemma v21_B1_left_phase_bounds {x : ℝ}
    (hxlo : (19 / 20 : ℝ) ≤ x) (hxhi : x ≤ 1) :
    0 ≤ v21Phase1 x ∧ v21Phase1 x ≤ v21RootPiU / 20 := by
  have hpiU : Real.pi ≤ v21RootPiU := by
    simpa [v21RootPiU] using (le_of_lt v21_pi_upper)
  have hgap0 : 0 ≤ 1 - x := by linarith
  have hgapU : 1 - x ≤ (1 / 20 : ℝ) := by linarith
  unfold v21Phase1
  constructor
  · exact mul_nonneg Real.pi_pos.le hgap0
  · calc
      Real.pi * (1 - x) ≤ v21RootPiU * (1 - x) :=
        mul_le_mul_of_nonneg_right hpiU hgap0
      _ ≤ v21RootPiU * (1 / 20 : ℝ) :=
        mul_le_mul_of_nonneg_left hgapU (by norm_num [v21RootPiU])
      _ = v21RootPiU / 20 := by ring

lemma v21_B1_left_trig_bounds {x : ℝ}
    (hxlo : (19 / 20 : ℝ) ≤ x) (hxhi : x ≤ 1) :
    (49 / 50 : ℝ) ≤ Real.cos (v21Phase1 x) ∧
      0 ≤ Real.sin (v21Phase1 x) ∧
      Real.sin (v21Phase1 x) ≤ (4 / 25 : ℝ) := by
  obtain ⟨ht0, htU⟩ := v21_B1_left_phase_bounds hxlo hxhi
  have hUrat : v21RootPiU / 20 ≤ (4 / 25 : ℝ) := by
    norm_num [v21RootPiU]
  have ht16 : v21Phase1 x ≤ (4 / 25 : ℝ) := htU.trans hUrat
  have htPi : v21Phase1 x ≤ Real.pi := by
    nlinarith [Real.pi_gt_three, ht16]
  have hsin0 : 0 ≤ Real.sin (v21Phase1 x) :=
    Real.sin_nonneg_of_nonneg_of_le_pi ht0 htPi
  have hsinU : Real.sin (v21Phase1 x) ≤ (4 / 25 : ℝ) :=
    (Real.sin_le ht0).trans ht16
  have hsq : (v21Phase1 x) ^ 2 ≤ (4 / 25 : ℝ) ^ 2 :=
    pow_le_pow_left₀ ht0 ht16 2
  have hcos0 := Real.one_sub_sq_div_two_le_cos (x := v21Phase1 x)
  have hcos : (49 / 50 : ℝ) ≤ Real.cos (v21Phase1 x) := by
    calc
      (49 / 50 : ℝ) ≤ 1 - (4 / 25 : ℝ) ^ 2 / 2 := by norm_num
      _ ≤ 1 - (v21Phase1 x) ^ 2 / 2 := by nlinarith
      _ ≤ Real.cos (v21Phase1 x) := hcos0
  exact ⟨hcos, hsin0, hsinU⟩

/-- The cleared second-derivative numerator is nonnegative on `[0.95,1]`. -/
lemma v21_M2_nonneg_B1_left {x : ℝ}
    (hxlo : (19 / 20 : ℝ) ≤ x) (hxhi : x ≤ 1) :
    0 ≤ v21M2 (v21B x) := by
  have hP := v21_P2_le_neg100_B1_left hxlo hxhi
  have hQ := v21_Q2_ge_neg250_B1_left hxlo hxhi
  obtain ⟨hcos, hsin0, hsinU⟩ := v21_B1_left_trig_bounds hxlo hxhi
  have hPneg : (100 : ℝ) ≤ -v21P2 (v21B x) := by linarith
  have hP0 : 0 ≤ -v21P2 (v21B x) := by linarith
  have hpc : (98 : ℝ) ≤
      (-v21P2 (v21B x)) * Real.cos (v21Phase1 x) := by
    have := mul_le_mul hPneg hcos (by norm_num) hP0
    norm_num at this ⊢
    exact this
  have hqs1 :
      -(250 : ℝ) * Real.sin (v21Phase1 x) ≤
        v21Q2 (v21B x) * Real.sin (v21Phase1 x) :=
    mul_le_mul_of_nonneg_right hQ hsin0
  have hqs2 :
      -(40 : ℝ) ≤ -(250 : ℝ) * Real.sin (v21Phase1 x) := by
    nlinarith
  unfold v21M2
  rw [v21_cosB_phase1, v21_sinB_phase1]
  nlinarith

lemma v21_B1_right_phase_mem {x : ℝ}
    (hxlo : (1 : ℝ) ≤ x) (hxhi : x ≤ (6 / 5 : ℝ)) :
    v21Phase1 x ∈ Set.Icc (-(Real.pi / 2)) 0 := by
  have hgap0 : 1 - x ≤ 0 := by linarith
  have hgapL : -(1 / 5 : ℝ) ≤ 1 - x := by linarith
  have ht0 : v21Phase1 x ≤ 0 := by
    unfold v21Phase1
    exact mul_nonpos_of_nonneg_of_nonpos Real.pi_pos.le hgap0
  have htL : -(Real.pi / 2) ≤ v21Phase1 x := by
    unfold v21Phase1
    have hm := mul_le_mul_of_nonneg_left hgapL Real.pi_pos.le
    nlinarith [Real.pi_pos]
  exact ⟨htL, ht0⟩

/-- On `[1,1.2]` both terms in the phase-rewritten `M₂` have the correct
sign, so no quantitative polynomial estimate is needed. -/
lemma v21_M2_nonneg_B1_right {x : ℝ}
    (hxlo : (1 : ℝ) ≤ x) (hxhi : x ≤ (6 / 5 : ℝ)) :
    0 ≤ v21M2 (v21B x) := by
  have hxpos : 0 < x := by linarith
  have hb2 : 2 < v21B x := by
    unfold v21B
    nlinarith [mul_lt_mul_of_pos_right Real.pi_gt_three hxpos]
  have hP := v21_P2_neg_of_two_lt hb2
  have hQ := v21_Q2_neg_of_two_lt hb2
  have hphase := v21_B1_right_phase_mem hxlo hxhi
  have hcos : 0 ≤ Real.cos (v21Phase1 x) := by
    have hmem : v21Phase1 x ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
      ⟨hphase.1, hphase.2.trans (by positivity)⟩
    exact Real.cos_nonneg_of_mem_Icc hmem
  have hsin : Real.sin (v21Phase1 x) ≤ 0 := by
    have hnegpi : -Real.pi ≤ v21Phase1 x := by
      nlinarith [hphase.1, Real.pi_pos]
    exact Real.sin_nonpos_of_nonpos_of_neg_pi_le hphase.2 hnegpi
  have htermP : 0 ≤ v21P2 (v21B x) * (-Real.cos (v21Phase1 x)) :=
    mul_nonneg_of_nonpos_of_nonpos hP.le (neg_nonpos.mpr hcos)
  have htermQ : 0 ≤ v21Q2 (v21B x) * Real.sin (v21Phase1 x) :=
    mul_nonneg_of_nonpos_of_nonpos hQ.le hsin
  unfold v21M2
  rw [v21_cosB_phase1, v21_sinB_phase1]
  exact add_nonneg htermP htermQ

lemma v21_M2_nonneg_B1 {x : ℝ}
    (hxlo : (19 / 20 : ℝ) ≤ x) (hxhi : x ≤ (6 / 5 : ℝ)) :
    0 ≤ v21M2 (v21B x) := by
  by_cases hx : x ≤ 1
  · exact v21_M2_nonneg_B1_left hxlo hx
  · exact v21_M2_nonneg_B1_right (le_of_not_ge hx) hxhi

lemma v21_kernelXSecond_nonneg_B1 {x : ℝ}
    (hxlo : (19 / 20 : ℝ) ≤ x) (hxhi : x ≤ (6 / 5 : ℝ)) :
    0 ≤ v21KernelXSecond x := by
  have hxcert : v17KernelCertPoint < x := by
    have : (89 / 100 : ℝ) < x := by nlinarith
    simpa [v17KernelCertPoint] using this
  have hden := v21_kernel_den_pos_of_cert_lt hxcert
  have hm := v21_M2_nonneg_B1 hxlo hxhi
  have hquot :
      0 ≤ v21M2 (v21B x) / ((v21B x) ^ 2 - (1 / 2 : ℝ)) ^ 3 :=
    div_nonneg hm (pow_nonneg hden.le 3)
  unfold v21KernelXSecond
  exact mul_nonneg (sq_nonneg Real.pi) hquot

/-- The normalized kernel is convex on the whole first survivor band. -/
theorem v21_kernelX_convex_B1 :
    ConvexOn ℝ (Icc (19 / 20 : ℝ) (6 / 5 : ℝ)) v21KernelX := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _)
  · intro x hx
    have hxcert : v17KernelCertPoint < x := by
      have : (89 / 100 : ℝ) < x := by nlinarith [hx.1]
      simpa [v17KernelCertPoint] using this
    exact (v21_kernelX_hasDerivAt (v21_kernel_den_ne_of_cert_lt hxcert)).continuousAt.continuousWithinAt
  · intro x hx
    have hxIcc : x ∈ Icc (19 / 20 : ℝ) (6 / 5 : ℝ) := interior_subset hx
    have hxcert : v17KernelCertPoint < x := by
      have : (89 / 100 : ℝ) < x := by nlinarith [hxIcc.1]
      simpa [v17KernelCertPoint] using this
    exact (v21_kernelX_hasDerivAt (v21_kernel_den_ne_of_cert_lt hxcert)).hasDerivWithinAt
  · intro x hx
    have hxIcc : x ∈ Icc (19 / 20 : ℝ) (6 / 5 : ℝ) := interior_subset hx
    have hxcert : v17KernelCertPoint < x := by
      have : (89 / 100 : ℝ) < x := by nlinarith [hxIcc.1]
      simpa [v17KernelCertPoint] using this
    exact (v21_kernelXPrime_hasDerivAt (v21_kernel_den_ne_of_cert_lt hxcert)).hasDerivWithinAt
  · intro x hx
    have hxIcc : x ∈ Icc (19 / 20 : ℝ) (6 / 5 : ℝ) := interior_subset hx
    exact v21_kernelXSecond_nonneg_B1 hxIcc.1 hxIcc.2

end HurtadoZeta23