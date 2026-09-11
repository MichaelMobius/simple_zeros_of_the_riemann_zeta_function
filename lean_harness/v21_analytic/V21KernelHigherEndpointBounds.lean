import HurtadoZeta23.V21KernelCellTools
import Mathlib.Tactic

noncomputable section

namespace HurtadoZeta23

/-- Rational certificate at the left endpoint of the second excluded band. -/
theorem v21_negk_at_120_lower :
    (521 / 5000 : ℝ) < -limitingk (6 / 5 : ℝ) := by
  let x : ℝ := 6 / 5
  let bL : ℝ := (6 / 5 : ℝ) * (31415926 / 10000000 : ℝ)
  let bU : ℝ := (6 / 5 : ℝ) * (31415927 / 10000000 : ℝ)
  let u : ℝ := (3 / 10 : ℝ) * Real.pi
  let tU : ℝ := (3 / 10 : ℝ) * (31415927 / 10000000 : ℝ)

  have hxcert : v17KernelCertPoint < x := by
    norm_num [v17KernelCertPoint, x]
  have hxA : v21A < v21B x := v21_A_lt_B_of_cert_lt hxcert
  have hB1 : 1 < v21B x := by
    dsimp [x, v21B]
    nlinarith [Real.pi_gt_three]
  have hbL1 : 1 < bL := by norm_num [bL]
  have hbL : bL ≤ v21B x := by
    dsimp [bL, x, v21B]
    nlinarith [v21_pi_lower]
  have hbU : v21B x ≤ bU := by
    dsimp [bU, x, v21B]
    nlinarith [v21_pi_upper]

  have hratioRaw :=
    v21_ratio_factor_lower (b := v21B x) (u := bU) hB1 hbU
  have hratio :
      (2700829 / 10000000 : ℝ) ≤ v21B x / v21D x := by
    have hrat :
        (2700829 / 10000000 : ℝ) ≤
          bU / (bU ^ 2 - (1 / 2 : ℝ)) := by
      norm_num [bU]
    exact hrat.trans (by simpa [v21D] using hratioRaw)

  have hrecipRaw :=
    v21_recip_factor_lower (b := bL) (u := v21B x) hbL1 hbL
  have hrecip :
      1 / v21D x ≤ (732199 / 10000000 : ℝ) := by
    have hrat :
        1 / (bL ^ 2 - (1 / 2 : ℝ)) ≤
          (732199 / 10000000 : ℝ) := by
      norm_num [bL]
    exact (by simpa [v21D] using hrecipRaw).trans hrat

  have hC : (8274992 / 10000000 : ℝ) ≤ v21C := by
    nlinarith [v21_C_lower]

  have hphase : v21Phase15 x = -u := by
    dsimp [x, u, v21Phase15]
    ring
  have hu0 : 0 ≤ u := by
    dsimp [u]
    positivity
  have huPi : u ≤ Real.pi := by
    dsimp [u]
    nlinarith [Real.pi_pos]
  have hu_tU : u ≤ tU := by
    dsimp [u, tU]
    nlinarith [v21_pi_upper]
  have htU0 : 0 ≤ tU := by norm_num [tU]
  have htU1 : tU ≤ 1 := by norm_num [tU]

  have hcosTaylor := v21_cos_lower10 (x := tU) htU0 htU1
  have hcosRat :
      (5877852 / 10000000 : ℝ) <
        1 - tU ^ 2 / 2 + tU ^ 4 / 24 - tU ^ 6 / 720 +
          tU ^ 8 / 40320 - tU ^ 10 / 3628800 := by
    norm_num [tU]
  have hcosMono : Real.cos tU ≤ Real.cos u := by
    apply Real.cos_le_cos_of_nonneg_of_le_pi
    · exact hu0
    · nlinarith [Real.pi_gt_three, htU1]
    · exact hu_tU
  have hcos :
      (5877852 / 10000000 : ℝ) ≤ Real.cos u := by
    exact le_of_lt (hcosRat.trans_le (hcosTaylor.trans hcosMono))

  have hsinTaylor := v21_sin_upper9 (x := tU) htU0 htU1
  have hsinRat :
      tU - tU ^ 3 / 6 + tU ^ 5 / 120 - tU ^ 7 / 5040 +
          tU ^ 9 / 362880 ≤ (8090170 / 10000000 : ℝ) := by
    norm_num [tU]
  have hsinMono : Real.sin u ≤ Real.sin tU := by
    apply Real.sin_le_sin_of_le_of_le_pi_div_two
    · nlinarith [Real.pi_pos, hu0]
    · nlinarith [Real.pi_gt_three, htU1]
    · exact hu_tU
  have hsin : Real.sin u ≤ (8090170 / 10000000 : ℝ) :=
    hsinMono.trans (hsinTaylor.trans hsinRat)

  have hC0 : (0 : ℝ) ≤ 8274992 / 10000000 := by norm_num
  have hratio0 : (0 : ℝ) ≤ 2700829 / 10000000 := by norm_num
  have hcos0 : (0 : ℝ) ≤ 5877852 / 10000000 := by norm_num
  have hrecip0 : 0 ≤ 1 / v21D x := by
    exact le_of_lt (one_div_pos.mpr (v21_D_pos hxA))
  have hsinu0 : 0 ≤ Real.sin u :=
    Real.sin_nonneg_of_nonneg_of_le_pi hu0 huPi
  have hCnonneg : 0 ≤ v21C := hC0.trans hC
  have hratioNonneg : 0 ≤ v21B x / v21D x := hratio0.trans hratio

  have hterm1 :
      (8274992 / 10000000 : ℝ) * (2700829 / 10000000 : ℝ) *
          (5877852 / 10000000 : ℝ) ≤
        v21C * (v21B x / v21D x) * Real.cos u := by
    have hprod :
        (8274992 / 10000000 : ℝ) * (2700829 / 10000000 : ℝ) ≤
          v21C * (v21B x / v21D x) :=
      mul_le_mul hC hratio hratio0 hCnonneg
    exact mul_le_mul hprod hcos hcos0 (mul_nonneg hCnonneg hratioNonneg)

  have hhalfrecip :
      (1 / 2 : ℝ) * (1 / v21D x) ≤
        (1 / 2 : ℝ) * (732199 / 10000000 : ℝ) :=
    mul_le_mul_of_nonneg_left hrecip (by norm_num)
  have hterm2 :
      (1 / 2 : ℝ) * (1 / v21D x) * Real.sin u ≤
        (1 / 2 : ℝ) * (732199 / 10000000 : ℝ) *
          (8090170 / 10000000 : ℝ) := by
    exact mul_le_mul hhalfrecip hsin hsinu0
      (mul_nonneg (by norm_num) hrecip0)

  have hratFinal :
      (521 / 5000 : ℝ) <
        (8274992 / 10000000 : ℝ) * (2700829 / 10000000 : ℝ) *
            (5877852 / 10000000 : ℝ) -
          (1 / 2 : ℝ) * (732199 / 10000000 : ℝ) *
            (8090170 / 10000000 : ℝ) := by
    norm_num

  rw [v21_negk_phase15 hxA, hphase, Real.cos_neg, Real.sin_neg]
  nlinarith

/-- Rational certificate at the right endpoint of the second excluded band. -/
theorem v21_negk_at_179_lower :
    (521 / 5000 : ℝ) < -limitingk (179 / 100 : ℝ) := by
  let x : ℝ := 179 / 100
  let bU : ℝ := (179 / 100 : ℝ) * (31415927 / 10000000 : ℝ)
  let u : ℝ := (29 / 100 : ℝ) * Real.pi
  let tL : ℝ := (29 / 100 : ℝ) * (31415926 / 10000000 : ℝ)
  let tU : ℝ := (29 / 100 : ℝ) * (31415927 / 10000000 : ℝ)

  have hxcert : v17KernelCertPoint < x := by
    norm_num [v17KernelCertPoint, x]
  have hxA : v21A < v21B x := v21_A_lt_B_of_cert_lt hxcert
  have hB1 : 1 < v21B x := by
    dsimp [x, v21B]
    nlinarith [Real.pi_gt_three]
  have hbU : v21B x ≤ bU := by
    dsimp [bU, x, v21B]
    nlinarith [v21_pi_upper]

  have hratioRaw :=
    v21_ratio_factor_lower (b := v21B x) (u := bU) hB1 hbU
  have hratio :
      (1806514 / 10000000 : ℝ) ≤ v21B x / v21D x := by
    have hrat :
        (1806514 / 10000000 : ℝ) ≤
          bU / (bU ^ 2 - (1 / 2 : ℝ)) := by
      norm_num [bU]
    exact hrat.trans (by simpa [v21D] using hratioRaw)

  have hrecipRaw :=
    v21_recip_factor_lower (b := v21B x) (u := bU) hB1 hbU
  have hrecip :
      (321267 / 10000000 : ℝ) ≤ 1 / v21D x := by
    have hrat :
        (321267 / 10000000 : ℝ) ≤
          1 / (bU ^ 2 - (1 / 2 : ℝ)) := by
      norm_num [bU]
    exact hrat.trans (by simpa [v21D] using hrecipRaw)

  have hC : (8274992 / 10000000 : ℝ) ≤ v21C := by
    nlinarith [v21_C_lower]

  have hphase : v21Phase15 x = u := by
    dsimp [x, u, v21Phase15]
    ring
  have hu0 : 0 ≤ u := by
    dsimp [u]
    positivity
  have huPi : u ≤ Real.pi := by
    dsimp [u]
    nlinarith [Real.pi_pos]
  have htL0 : 0 ≤ tL := by norm_num [tL]
  have htL1 : tL ≤ 1 := by norm_num [tL]
  have htU0 : 0 ≤ tU := by norm_num [tU]
  have htU1 : tU ≤ 1 := by norm_num [tU]
  have htL_u : tL ≤ u := by
    dsimp [tL, u]
    nlinarith [v21_pi_lower]
  have hu_tU : u ≤ tU := by
    dsimp [u, tU]
    nlinarith [v21_pi_upper]

  have hcosTaylor := v21_cos_lower10 (x := tU) htU0 htU1
  have hcosRat :
      (6129070 / 10000000 : ℝ) <
        1 - tU ^ 2 / 2 + tU ^ 4 / 24 - tU ^ 6 / 720 +
          tU ^ 8 / 40320 - tU ^ 10 / 3628800 := by
    norm_num [tU]
  have hcosMono : Real.cos tU ≤ Real.cos u := by
    apply Real.cos_le_cos_of_nonneg_of_le_pi
    · exact hu0
    · nlinarith [Real.pi_gt_three, htU1]
    · exact hu_tU
  have hcos : (6129070 / 10000000 : ℝ) ≤ Real.cos u := by
    exact le_of_lt (hcosRat.trans_le (hcosTaylor.trans hcosMono))

  have hsinTaylor := v21_sin_lower7 (x := tL) htL0 htL1
  have hsinRat :
      (7901550 / 10000000 : ℝ) <
        tL - tL ^ 3 / 6 + tL ^ 5 / 120 - tL ^ 7 / 5040 := by
    norm_num [tL]
  have hsinMono : Real.sin tL ≤ Real.sin u := by
    apply Real.sin_le_sin_of_le_of_le_pi_div_two
    · nlinarith [Real.pi_pos, htL0]
    · dsimp [u]
      nlinarith [Real.pi_pos]
    · exact htL_u
  have hsin : (7901550 / 10000000 : ℝ) ≤ Real.sin u := by
    exact le_of_lt (hsinRat.trans_le (hsinTaylor.trans hsinMono))

  have hC0 : (0 : ℝ) ≤ 8274992 / 10000000 := by norm_num
  have hratio0 : (0 : ℝ) ≤ 1806514 / 10000000 := by norm_num
  have hrecip0 : (0 : ℝ) ≤ 321267 / 10000000 := by norm_num
  have hcos0 : (0 : ℝ) ≤ 6129070 / 10000000 := by norm_num
  have hsin0 : (0 : ℝ) ≤ 7901550 / 10000000 := by norm_num
  have hCnonneg : 0 ≤ v21C := hC0.trans hC
  have hratioNonneg : 0 ≤ v21B x / v21D x := hratio0.trans hratio
  have hrecipNonneg : 0 ≤ 1 / v21D x := hrecip0.trans hrecip

  have hterm1 :
      (8274992 / 10000000 : ℝ) * (1806514 / 10000000 : ℝ) *
          (6129070 / 10000000 : ℝ) ≤
        v21C * (v21B x / v21D x) * Real.cos u := by
    have hprod :
        (8274992 / 10000000 : ℝ) * (1806514 / 10000000 : ℝ) ≤
          v21C * (v21B x / v21D x) :=
      mul_le_mul hC hratio hratio0 hCnonneg
    exact mul_le_mul hprod hcos hcos0 (mul_nonneg hCnonneg hratioNonneg)

  have hterm2 :
      (1 / 2 : ℝ) * (321267 / 10000000 : ℝ) *
          (7901550 / 10000000 : ℝ) ≤
        (1 / 2 : ℝ) * (1 / v21D x) * Real.sin u := by
    have hhalf :
        (1 / 2 : ℝ) * (321267 / 10000000 : ℝ) ≤
          (1 / 2 : ℝ) * (1 / v21D x) :=
      mul_le_mul_of_nonneg_left hrecip (by norm_num)
    exact mul_le_mul hhalf hsin hsin0 (mul_nonneg (by norm_num) hrecipNonneg)

  have hratFinal :
      (521 / 5000 : ℝ) <
        (8274992 / 10000000 : ℝ) * (1806514 / 10000000 : ℝ) *
            (6129070 / 10000000 : ℝ) +
          (1 / 2 : ℝ) * (321267 / 10000000 : ℝ) *
            (7901550 / 10000000 : ℝ) := by
    norm_num

  rw [v21_negk_phase15 hxA, hphase]
  nlinarith

end HurtadoZeta23
