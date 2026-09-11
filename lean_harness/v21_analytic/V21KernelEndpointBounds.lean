import HurtadoZeta23.V21KernelCellTools
import Mathlib.Tactic

noncomputable section

namespace HurtadoZeta23

/-- A rational lower certificate for the right endpoint of the first
hard-core exclusion interval.  The proof uses only rational π bounds,
Taylor inequalities already proved in v20, and the elementary antitonicity
of the two denominator factors. -/
theorem v21_k_at_095_lower :
    (523 / 5000 : ℝ) < limitingk (19 / 20 : ℝ) := by
  let x : ℝ := 19 / 20
  let bU : ℝ := (19 / 20 : ℝ) * (31415927 / 10000000 : ℝ)
  let tL : ℝ := (31415926 / 10000000 : ℝ) / 20
  let tU : ℝ := (31415927 / 10000000 : ℝ) / 20

  have hxcert : v17KernelCertPoint < x := by
    norm_num [v17KernelCertPoint, x]
  have hxA : v21A < v21B x :=
    v21_A_lt_B_of_cert_lt hxcert
  have hB1 : 1 < v21B x := by
    dsimp [x, v21B]
    nlinarith [Real.pi_gt_three]
  have hBU : v21B x ≤ bU := by
    dsimp [x, bU, v21B]
    nlinarith [v21_pi_upper]

  have hratioRaw :=
    v21_ratio_factor_lower (b := v21B x) (u := bU) hB1 hBU
  have hratio :
      (3549898 / 10000000 : ℝ) ≤ v21B x / v21D x := by
    have hrat :
        (3549898 / 10000000 : ℝ) ≤
          bU / (bU ^ 2 - (1 / 2 : ℝ)) := by
      norm_num [bU]
    exact hrat.trans (by simpa [v21D] using hratioRaw)

  have hrecipRaw :=
    v21_recip_factor_lower (b := v21B x) (u := bU) hB1 hBU
  have hrecip :
      (1189439 / 10000000 : ℝ) ≤ 1 / v21D x := by
    have hrat :
        (1189439 / 10000000 : ℝ) ≤
          1 / (bU ^ 2 - (1 / 2 : ℝ)) := by
      norm_num [bU]
    exact hrat.trans (by simpa [v21D] using hrecipRaw)

  have hC : (8274992 / 10000000 : ℝ) ≤ v21C := by
    nlinarith [v21_C_lower]

  have htL0 : 0 ≤ tL := by norm_num [tL]
  have htL1 : tL ≤ 1 := by norm_num [tL]
  have hphaseL : tL ≤ v21Phase1 x := by
    dsimp [tL, x, v21Phase1]
    nlinarith [v21_pi_lower]
  have hsinTaylor := v20_sin_lower7 (x := tL) htL0 htL1
  have hsinRat :
      (1564344 / 10000000 : ℝ) <
        tL - tL ^ 3 / 6 + tL ^ 5 / 120 - tL ^ 7 / 5040 := by
    norm_num [tL]
  have hsinMono : Real.sin tL ≤ Real.sin (v21Phase1 x) := by
    apply Real.sin_le_sin_of_le_of_le_pi_div_two
    · nlinarith [Real.pi_pos, htL0]
    · dsimp [x, v21Phase1]
      nlinarith [Real.pi_pos]
    · exact hphaseL
  have hsin :
      (1564344 / 10000000 : ℝ) ≤ Real.sin (v21Phase1 x) := by
    exact le_of_lt (hsinRat.trans_le (hsinTaylor.trans hsinMono))

  have htU0 : 0 ≤ tU := by norm_num [tU]
  have htU1 : tU ≤ 1 := by norm_num [tU]
  have hphaseU : v21Phase1 x ≤ tU := by
    dsimp [tU, x, v21Phase1]
    nlinarith [v21_pi_upper]
  have hcosTaylor := v20_cos_lower10 (x := tU) htU0 htU1
  have hcosRat :
      (9876883 / 10000000 : ℝ) <
        1 - tU ^ 2 / 2 + tU ^ 4 / 24 - tU ^ 6 / 720 +
          tU ^ 8 / 40320 - tU ^ 10 / 3628800 := by
    norm_num [tU]
  have hcosMono : Real.cos tU ≤ Real.cos (v21Phase1 x) := by
    apply Real.cos_le_cos_of_nonneg_of_le_pi
    · dsimp [x, v21Phase1]
      positivity
    · nlinarith [Real.pi_gt_three, htU1]
    · exact hphaseU
  have hcos :
      (9876883 / 10000000 : ℝ) ≤ Real.cos (v21Phase1 x) := by
    exact le_of_lt (hcosRat.trans_le (hcosTaylor.trans hcosMono))

  have hC0 : (0 : ℝ) ≤ 8274992 / 10000000 := by norm_num
  have hratio0 : (0 : ℝ) ≤ 3549898 / 10000000 := by norm_num
  have hrecip0 : (0 : ℝ) ≤ 1189439 / 10000000 := by norm_num
  have hsin0 : (0 : ℝ) ≤ 1564344 / 10000000 := by norm_num
  have hcos0 : (0 : ℝ) ≤ 9876883 / 10000000 := by norm_num
  have hCnonneg : 0 ≤ v21C := hC0.trans hC
  have hratioNonneg : 0 ≤ v21B x / v21D x := hratio0.trans hratio
  have hrecipNonneg : 0 ≤ 1 / v21D x := hrecip0.trans hrecip

  have hterm1 :
      (8274992 / 10000000 : ℝ) * (3549898 / 10000000 : ℝ) *
          (1564344 / 10000000 : ℝ) ≤
        v21C * (v21B x / v21D x) * Real.sin (v21Phase1 x) := by
    have hprod :
        (8274992 / 10000000 : ℝ) * (3549898 / 10000000 : ℝ) ≤
          v21C * (v21B x / v21D x) :=
      mul_le_mul hC hratio hratio0 hCnonneg
    exact mul_le_mul hprod hsin hsin0 (mul_nonneg hCnonneg hratioNonneg)

  have hterm2 :
      (1 / 2 : ℝ) * (1189439 / 10000000 : ℝ) *
          (9876883 / 10000000 : ℝ) ≤
        (1 / 2 : ℝ) * (1 / v21D x) * Real.cos (v21Phase1 x) := by
    have hhalf :
        (1 / 2 : ℝ) * (1189439 / 10000000 : ℝ) ≤
          (1 / 2 : ℝ) * (1 / v21D x) :=
      mul_le_mul_of_nonneg_left hrecip (by norm_num)
    exact mul_le_mul hhalf hcos hcos0 (mul_nonneg (by norm_num) hrecipNonneg)

  have hsum := add_le_add hterm1 hterm2
  have hratFinal :
      (523 / 5000 : ℝ) <
        (8274992 / 10000000 : ℝ) * (3549898 / 10000000 : ℝ) *
            (1564344 / 10000000 : ℝ) +
          (1 / 2 : ℝ) * (1189439 / 10000000 : ℝ) *
            (9876883 / 10000000 : ℝ) := by
    norm_num
  rw [v21_k_phase1 hxA]
  exact hratFinal.trans_le hsum

end HurtadoZeta23
