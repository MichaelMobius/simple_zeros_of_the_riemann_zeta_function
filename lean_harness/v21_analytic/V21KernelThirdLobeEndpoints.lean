import HurtadoZeta23.V21KernelCellTools
import Mathlib.Tactic

noncomputable section

namespace HurtadoZeta23

/-- Rational certificate at the left endpoint of the third excluded band. -/
theorem v21_k_at_237_lower :
    (993 / 10000 : ℝ) < limitingk (237 / 100 : ℝ) := by
  let x : ℝ := 237 / 100
  let bL : ℝ := (237 / 100 : ℝ) * (31415926 / 10000000 : ℝ)
  let bU : ℝ := (237 / 100 : ℝ) * (31415927 / 10000000 : ℝ)
  let u : ℝ := (13 / 100 : ℝ) * Real.pi
  let tU : ℝ := (13 / 100 : ℝ) * (31415927 / 10000000 : ℝ)

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
      (1355303 / 10000000 : ℝ) ≤ v21B x / v21D x := by
    have hrat :
        (1355303 / 10000000 : ℝ) ≤
          bU / (bU ^ 2 - (1 / 2 : ℝ)) := by
      norm_num [bU]
    exact hrat.trans (by simpa [v21D] using hratioRaw)

  have hrecipRaw :=
    v21_recip_factor_lower (b := bL) (u := v21B x) hbL1 hbL
  have hrecipRaw' :
      1 / v21D x ≤ 1 / (bL ^ 2 - (1 / 2 : ℝ)) := by
    simpa [v21D] using hrecipRaw
  have hrecip :
      1 / v21D x ≤ (182029 / 10000000 : ℝ) := by
    have hrat :
        1 / (bL ^ 2 - (1 / 2 : ℝ)) ≤
          (182029 / 10000000 : ℝ) := by
      norm_num [bL]
    exact hrecipRaw'.trans hrat

  have hC : (8274992 / 10000000 : ℝ) ≤ v21C := by
    nlinarith [v21_C_lower]

  have hphase : v21Phase25 x = -u := by
    dsimp [x, u, v21Phase25]
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
      (9177546 / 10000000 : ℝ) <
        1 - tU ^ 2 / 2 + tU ^ 4 / 24 - tU ^ 6 / 720 +
          tU ^ 8 / 40320 - tU ^ 10 / 3628800 := by
    norm_num [tU]
  have hcosMono : Real.cos tU ≤ Real.cos u := by
    apply Real.cos_le_cos_of_nonneg_of_le_pi
    · exact hu0
    · nlinarith [Real.pi_gt_three, htU1]
    · exact hu_tU
  have hcos : (9177546 / 10000000 : ℝ) ≤ Real.cos u := by
    exact le_of_lt (hcosRat.trans_le (hcosTaylor.trans hcosMono))

  have hsinTaylor := v21_sin_upper9 (x := tU) htU0 htU1
  have hsinRat :
      tU - tU ^ 3 / 6 + tU ^ 5 / 120 - tU ^ 7 / 5040 +
          tU ^ 9 / 362880 ≤ (3971482 / 10000000 : ℝ) := by
    norm_num [tU]
  have hsinMono : Real.sin u ≤ Real.sin tU := by
    apply Real.sin_le_sin_of_le_of_le_pi_div_two
    · nlinarith [Real.pi_pos, hu0]
    · nlinarith [Real.pi_gt_three, htU1]
    · exact hu_tU
  have hsin : Real.sin u ≤ (3971482 / 10000000 : ℝ) :=
    hsinMono.trans (hsinTaylor.trans hsinRat)

  have hC0 : (0 : ℝ) ≤ 8274992 / 10000000 := by norm_num
  have hratio0 : (0 : ℝ) ≤ 1355303 / 10000000 := by norm_num
  have hcos0 : (0 : ℝ) ≤ 9177546 / 10000000 := by norm_num
  have hrecip0 : 0 ≤ 1 / v21D x :=
    le_of_lt (one_div_pos.mpr (v21_D_pos hxA))
  have hsinu0 : 0 ≤ Real.sin u :=
    Real.sin_nonneg_of_nonneg_of_le_pi hu0 huPi
  have hCnonneg : 0 ≤ v21C := hC0.trans hC
  have hratioNonneg : 0 ≤ v21B x / v21D x := hratio0.trans hratio

  have hterm1 :
      (8274992 / 10000000 : ℝ) * (1355303 / 10000000 : ℝ) *
          (9177546 / 10000000 : ℝ) ≤
        v21C * (v21B x / v21D x) * Real.cos u := by
    have hprod :
        (8274992 / 10000000 : ℝ) * (1355303 / 10000000 : ℝ) ≤
          v21C * (v21B x / v21D x) :=
      mul_le_mul hC hratio hratio0 hCnonneg
    exact mul_le_mul hprod hcos hcos0 (mul_nonneg hCnonneg hratioNonneg)

  have hhalfrecip :
      (1 / 2 : ℝ) * (1 / v21D x) ≤
        (1 / 2 : ℝ) * (182029 / 10000000 : ℝ) :=
    mul_le_mul_of_nonneg_left hrecip (by norm_num)
  have hterm2 :
      (1 / 2 : ℝ) * (1 / v21D x) * Real.sin u ≤
        (1 / 2 : ℝ) * (182029 / 10000000 : ℝ) *
          (3971482 / 10000000 : ℝ) := by
    exact mul_le_mul hhalfrecip hsin hsinu0 (by norm_num)

  have hratFinal :
      (993 / 10000 : ℝ) <
        (8274992 / 10000000 : ℝ) * (1355303 / 10000000 : ℝ) *
            (9177546 / 10000000 : ℝ) -
          (1 / 2 : ℝ) * (182029 / 10000000 : ℝ) *
            (3971482 / 10000000 : ℝ) := by
    norm_num

  rw [v21_k_phase25 hxA, hphase, Real.cos_neg, Real.sin_neg]
  nlinarith

/-- Rational certificate at the split point `2.55` in the third lobe. -/
theorem v21_k_at_255_lower :
    (993 / 10000 : ℝ) < limitingk (51 / 20 : ℝ) := by
  let x : ℝ := 51 / 20
  let bU : ℝ := (51 / 20 : ℝ) * (31415927 / 10000000 : ℝ)
  let u : ℝ := (1 / 20 : ℝ) * Real.pi
  let tL : ℝ := (1 / 20 : ℝ) * (31415926 / 10000000 : ℝ)
  let tU : ℝ := (1 / 20 : ℝ) * (31415927 / 10000000 : ℝ)

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
      (1258075 / 10000000 : ℝ) ≤ v21B x / v21D x := by
    have hrat :
        (1258075 / 10000000 : ℝ) ≤
          bU / (bU ^ 2 - (1 / 2 : ℝ)) := by
      norm_num [bU]
    exact hrat.trans (by simpa [v21D] using hratioRaw)

  have hrecipRaw :=
    v21_recip_factor_lower (b := v21B x) (u := bU) hB1 hbU
  have hrecip :
      (157042 / 10000000 : ℝ) ≤ 1 / v21D x := by
    have hrat :
        (157042 / 10000000 : ℝ) ≤
          1 / (bU ^ 2 - (1 / 2 : ℝ)) := by
      norm_num [bU]
    exact hrat.trans (by simpa [v21D] using hrecipRaw)

  have hC : (8274992 / 10000000 : ℝ) ≤ v21C := by
    nlinarith [v21_C_lower]
  have hphase : v21Phase25 x = u := by
    dsimp [x, u, v21Phase25]
    ring
  have hu0 : 0 ≤ u := by
    dsimp [u]
    positivity
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
      (9876883 / 10000000 : ℝ) <
        1 - tU ^ 2 / 2 + tU ^ 4 / 24 - tU ^ 6 / 720 +
          tU ^ 8 / 40320 - tU ^ 10 / 3628800 := by
    norm_num [tU]
  have hcosMono : Real.cos tU ≤ Real.cos u := by
    apply Real.cos_le_cos_of_nonneg_of_le_pi
    · exact hu0
    · nlinarith [Real.pi_gt_three, htU1]
    · exact hu_tU
  have hcos : (9876883 / 10000000 : ℝ) ≤ Real.cos u := by
    exact le_of_lt (hcosRat.trans_le (hcosTaylor.trans hcosMono))

  have hsinTaylor := v21_sin_lower7 (x := tL) htL0 htL1
  have hsinRat :
      (1564344 / 10000000 : ℝ) <
        tL - tL ^ 3 / 6 + tL ^ 5 / 120 - tL ^ 7 / 5040 := by
    norm_num [tL]
  have hsinMono : Real.sin tL ≤ Real.sin u := by
    apply Real.sin_le_sin_of_le_of_le_pi_div_two
    · nlinarith [Real.pi_pos, htL0]
    · dsimp [u]
      nlinarith [Real.pi_pos]
    · exact htL_u
  have hsin : (1564344 / 10000000 : ℝ) ≤ Real.sin u := by
    exact le_of_lt (hsinRat.trans_le (hsinTaylor.trans hsinMono))

  have hC0 : (0 : ℝ) ≤ 8274992 / 10000000 := by norm_num
  have hratio0 : (0 : ℝ) ≤ 1258075 / 10000000 := by norm_num
  have hrecip0 : (0 : ℝ) ≤ 157042 / 10000000 := by norm_num
  have hcos0 : (0 : ℝ) ≤ 9876883 / 10000000 := by norm_num
  have hsin0 : (0 : ℝ) ≤ 1564344 / 10000000 := by norm_num
  have hCnonneg : 0 ≤ v21C := hC0.trans hC
  have hratioNonneg : 0 ≤ v21B x / v21D x := hratio0.trans hratio
  have hrecipNonneg : 0 ≤ 1 / v21D x := hrecip0.trans hrecip

  have hterm1 :
      (8274992 / 10000000 : ℝ) * (1258075 / 10000000 : ℝ) *
          (9876883 / 10000000 : ℝ) ≤
        v21C * (v21B x / v21D x) * Real.cos u := by
    have hprod :
        (8274992 / 10000000 : ℝ) * (1258075 / 10000000 : ℝ) ≤
          v21C * (v21B x / v21D x) :=
      mul_le_mul hC hratio hratio0 hCnonneg
    exact mul_le_mul hprod hcos hcos0 (mul_nonneg hCnonneg hratioNonneg)

  have hterm2 :
      (1 / 2 : ℝ) * (157042 / 10000000 : ℝ) *
          (1564344 / 10000000 : ℝ) ≤
        (1 / 2 : ℝ) * (1 / v21D x) * Real.sin u := by
    have hhalf :
        (1 / 2 : ℝ) * (157042 / 10000000 : ℝ) ≤
          (1 / 2 : ℝ) * (1 / v21D x) :=
      mul_le_mul_of_nonneg_left hrecip (by norm_num)
    exact mul_le_mul hhalf hsin hsin0 (mul_nonneg (by norm_num) hrecipNonneg)

  have hratFinal :
      (993 / 10000 : ℝ) <
        (8274992 / 10000000 : ℝ) * (1258075 / 10000000 : ℝ) *
            (9876883 / 10000000 : ℝ) +
          (1 / 2 : ℝ) * (157042 / 10000000 : ℝ) *
            (1564344 / 10000000 : ℝ) := by
    norm_num

  rw [v21_k_phase25 hxA, hphase]
  nlinarith

/-- Rational certificate at the right endpoint of the third excluded band. -/
theorem v21_k_at_261_lower :
    (491 / 5000 : ℝ) < limitingk (261 / 100 : ℝ) := by
  let x : ℝ := 261 / 100
  let bU : ℝ := (261 / 100 : ℝ) * (31415927 / 10000000 : ℝ)
  let u : ℝ := (11 / 100 : ℝ) * Real.pi
  let tL : ℝ := (11 / 100 : ℝ) * (31415926 / 10000000 : ℝ)
  let tU : ℝ := (11 / 100 : ℝ) * (31415927 / 10000000 : ℝ)

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
      (1228715 / 10000000 : ℝ) ≤ v21B x / v21D x := by
    have hrat :
        (1228715 / 10000000 : ℝ) ≤
          bU / (bU ^ 2 - (1 / 2 : ℝ)) := by
      norm_num [bU]
    exact hrat.trans (by simpa [v21D] using hratioRaw)

  have hrecipRaw :=
    v21_recip_factor_lower (b := v21B x) (u := bU) hB1 hbU
  have hrecip :
      (149851 / 10000000 : ℝ) ≤ 1 / v21D x := by
    have hrat :
        (149851 / 10000000 : ℝ) ≤
          1 / (bU ^ 2 - (1 / 2 : ℝ)) := by
      norm_num [bU]
    exact hrat.trans (by simpa [v21D] using hrecipRaw)

  have hC : (8274992 / 10000000 : ℝ) ≤ v21C := by
    nlinarith [v21_C_lower]
  have hphase : v21Phase25 x = u := by
    dsimp [x, u, v21Phase25]
    ring
  have hu0 : 0 ≤ u := by
    dsimp [u]
    positivity
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
      (9408807 / 10000000 : ℝ) <
        1 - tU ^ 2 / 2 + tU ^ 4 / 24 - tU ^ 6 / 720 +
          tU ^ 8 / 40320 - tU ^ 10 / 3628800 := by
    norm_num [tU]
  have hcosMono : Real.cos tU ≤ Real.cos u := by
    apply Real.cos_le_cos_of_nonneg_of_le_pi
    · exact hu0
    · nlinarith [Real.pi_gt_three, htU1]
    · exact hu_tU
  have hcos : (9408807 / 10000000 : ℝ) ≤ Real.cos u := by
    exact le_of_lt (hcosRat.trans_le (hcosTaylor.trans hcosMono))

  have hsinTaylor := v21_sin_lower7 (x := tL) htL0 htL1
  have hsinRat :
      (3387378 / 10000000 : ℝ) <
        tL - tL ^ 3 / 6 + tL ^ 5 / 120 - tL ^ 7 / 5040 := by
    norm_num [tL]
  have hsinMono : Real.sin tL ≤ Real.sin u := by
    apply Real.sin_le_sin_of_le_of_le_pi_div_two
    · nlinarith [Real.pi_pos, htL0]
    · dsimp [u]
      nlinarith [Real.pi_pos]
    · exact htL_u
  have hsin : (3387378 / 10000000 : ℝ) ≤ Real.sin u := by
    exact le_of_lt (hsinRat.trans_le (hsinTaylor.trans hsinMono))

  have hC0 : (0 : ℝ) ≤ 8274992 / 10000000 := by norm_num
  have hratio0 : (0 : ℝ) ≤ 1228715 / 10000000 := by norm_num
  have hrecip0 : (0 : ℝ) ≤ 149851 / 10000000 := by norm_num
  have hcos0 : (0 : ℝ) ≤ 9408807 / 10000000 := by norm_num
  have hsin0 : (0 : ℝ) ≤ 3387378 / 10000000 := by norm_num
  have hCnonneg : 0 ≤ v21C := hC0.trans hC
  have hratioNonneg : 0 ≤ v21B x / v21D x := hratio0.trans hratio
  have hrecipNonneg : 0 ≤ 1 / v21D x := hrecip0.trans hrecip

  have hterm1 :
      (8274992 / 10000000 : ℝ) * (1228715 / 10000000 : ℝ) *
          (9408807 / 10000000 : ℝ) ≤
        v21C * (v21B x / v21D x) * Real.cos u := by
    have hprod :
        (8274992 / 10000000 : ℝ) * (1228715 / 10000000 : ℝ) ≤
          v21C * (v21B x / v21D x) :=
      mul_le_mul hC hratio hratio0 hCnonneg
    exact mul_le_mul hprod hcos hcos0 (mul_nonneg hCnonneg hratioNonneg)

  have hterm2 :
      (1 / 2 : ℝ) * (149851 / 10000000 : ℝ) *
          (3387378 / 10000000 : ℝ) ≤
        (1 / 2 : ℝ) * (1 / v21D x) * Real.sin u := by
    have hhalf :
        (1 / 2 : ℝ) * (149851 / 10000000 : ℝ) ≤
          (1 / 2 : ℝ) * (1 / v21D x) :=
      mul_le_mul_of_nonneg_left hrecip (by norm_num)
    exact mul_le_mul hhalf hsin hsin0 (mul_nonneg (by norm_num) hrecipNonneg)

  have hratFinal :
      (491 / 5000 : ℝ) <
        (8274992 / 10000000 : ℝ) * (1228715 / 10000000 : ℝ) *
            (9408807 / 10000000 : ℝ) +
          (1 / 2 : ℝ) * (149851 / 10000000 : ℝ) *
            (3387378 / 10000000 : ℝ) := by
    norm_num

  rw [v21_k_phase25 hxA, hphase]
  nlinarith

end HurtadoZeta23
