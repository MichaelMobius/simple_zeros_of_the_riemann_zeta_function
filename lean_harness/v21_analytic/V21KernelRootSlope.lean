import HurtadoZeta23.V21KernelRootBracketsHigh
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic

noncomputable section

namespace HurtadoZeta23

/-- Exact derivative of the cleared root numerator. -/
def v21RootHDeriv (n : ℕ) (x : ℝ) : ℝ :=
  v21C * Real.pi * Real.sin (Real.pi * (x - (n : ℝ))) +
  v21C * Real.pi ^ 2 * x * Real.cos (Real.pi * (x - (n : ℝ))) +
  (1 / 2 : ℝ) * Real.pi * Real.sin (Real.pi * (x - (n : ℝ)))

lemma v21_rootH_hasDerivAt (n : ℕ) (x : ℝ) :
    HasDerivAt (v21RootH n) (v21RootHDeriv n x) x := by
  have hphase :
      HasDerivAt (fun t : ℝ => Real.pi * (t - (n : ℝ))) Real.pi x := by
    simpa using ((hasDerivAt_id x).sub_const (n : ℝ)).const_mul Real.pi
  have hsin :
      HasDerivAt
        (fun t : ℝ => Real.sin (Real.pi * (t - (n : ℝ))))
        (Real.cos (Real.pi * (x - (n : ℝ))) * Real.pi) x := by
    exact (Real.hasDerivAt_sin (Real.pi * (x - (n : ℝ)))).comp x hphase
  have hcos :
      HasDerivAt
        (fun t : ℝ => Real.cos (Real.pi * (t - (n : ℝ))))
        (-Real.sin (Real.pi * (x - (n : ℝ))) * Real.pi) x := by
    exact (Real.hasDerivAt_cos (Real.pi * (x - (n : ℝ)))).comp x hphase
  have hraw :=
    (((hasDerivAt_id x).const_mul (v21C * Real.pi)).mul hsin).sub
      (hcos.const_mul (1 / 2 : ℝ))
  have hraw' := hraw.congr_deriv (g' := v21RootHDeriv n x) (by
    unfold v21RootHDeriv
    ring)
  refine hraw'.congr_of_eventuallyEq ?_
  filter_upwards with t
  unfold v21RootH
  ring

/-- A rational cosine floor on the positive part of every root cell used by
our bootstrap. -/
lemma v21_root_cos_pos_floor {e : ℝ}
    (he0 : 0 ≤ e) (heU : e ≤ (151 / 1000 : ℝ)) :
    (887 / 1000 : ℝ) ≤ Real.cos (Real.pi * e) := by
  have hpiU : Real.pi ≤ v21RootPiU := by
    simpa [v21RootPiU] using (le_of_lt v21_pi_upper)
  have ht0 : 0 ≤ Real.pi * e := mul_nonneg Real.pi_pos.le he0
  have htU : Real.pi * e ≤ v21RootPiU * (151 / 1000 : ℝ) := by
    calc
      Real.pi * e ≤ v21RootPiU * e :=
        mul_le_mul_of_nonneg_right hpiU he0
      _ ≤ v21RootPiU * (151 / 1000 : ℝ) := by
        exact mul_le_mul_of_nonneg_left heU (by norm_num [v21RootPiU])
  have hsq :
      (Real.pi * e) ^ 2 ≤
        (v21RootPiU * (151 / 1000 : ℝ)) ^ 2 := by
    nlinarith [sq_nonneg (v21RootPiU * (151 / 1000 : ℝ) - Real.pi * e)]
  calc
    (887 / 1000 : ℝ) ≤
        1 - (v21RootPiU * (151 / 1000 : ℝ)) ^ 2 / 2 := by
      norm_num [v21RootPiU]
    _ ≤ 1 - (Real.pi * e) ^ 2 / 2 := by nlinarith
    _ ≤ Real.cos (Real.pi * e) := Real.one_sub_sq_div_two_le_cos

/-- A rational cosine floor on the short negative part of every root cell. -/
lemma v21_root_cos_neg_floor {e : ℝ}
    (heL : -(1 / 20 : ℝ) ≤ e) (he0 : e ≤ 0) :
    (987 / 1000 : ℝ) ≤ Real.cos (Real.pi * e) := by
  have hpiU : Real.pi ≤ v21RootPiU := by
    simpa [v21RootPiU] using (le_of_lt v21_pi_upper)
  let B : ℝ := v21RootPiU / 20
  let t : ℝ := Real.pi * e
  have hB0 : 0 ≤ B := by dsimp [B]; norm_num [v21RootPiU]
  have ht0 : t ≤ 0 := by
    dsimp [t]
    exact mul_nonpos_of_nonneg_of_nonpos Real.pi_pos.le he0
  have htL : -B ≤ t := by
    dsimp [B, t]
    have h1 : -(v21RootPiU / 20) ≤ -(Real.pi / 20) := by nlinarith
    have heL' : 0 ≤ e + 1 / 20 := by linarith
    have h2 : -(Real.pi / 20) ≤ Real.pi * e := by
      nlinarith [mul_nonneg Real.pi_pos.le heL']
    exact h1.trans h2
  have hsq : t ^ 2 ≤ B ^ 2 := by
    have hp : 0 ≤ (B - t) * (B + t) := by
      apply mul_nonneg
      · linarith
      · linarith
    nlinarith
  calc
    (987 / 1000 : ℝ) ≤ 1 - B ^ 2 / 2 := by
      dsimp [B]
      norm_num [v21RootPiU]
    _ ≤ 1 - t ^ 2 / 2 := by nlinarith
    _ ≤ Real.cos t := Real.one_sub_sq_div_two_le_cos

/-- On the negative side, sine is bounded below by the left endpoint phase. -/
lemma v21_root_sin_neg_floor {e : ℝ}
    (heL : -(1 / 20 : ℝ) ≤ e) (he0 : e ≤ 0) :
    -(v21RootPiU / 20) ≤ Real.sin (Real.pi * e) := by
  have hpiU : Real.pi ≤ v21RootPiU := by
    simpa [v21RootPiU] using (le_of_lt v21_pi_upper)
  have ht0 : Real.pi * e ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos Real.pi_pos.le he0
  have htL : -(v21RootPiU / 20) ≤ Real.pi * e := by
    have h1 : -(v21RootPiU / 20) ≤ -(Real.pi / 20) := by nlinarith
    have heL' : 0 ≤ e + 1 / 20 := by linarith
    have h2 : -(Real.pi / 20) ≤ Real.pi * e := by
      nlinarith [mul_nonneg Real.pi_pos.le heL']
    exact h1.trans h2
  exact htL.trans (Real.le_sin ht0)

private lemma v21_root_Cpi2_lower :
    v21RootCL * v21RootPiL ^ 2 ≤ v21C * Real.pi ^ 2 := by
  have hCL : v21RootCL ≤ v21C := by
    simpa [v21RootCL] using v21_C_lower
  have hpiL : v21RootPiL ≤ Real.pi := by
    simpa [v21RootPiL] using (le_of_lt v21_pi_lower)
  have hpiL0 : 0 ≤ v21RootPiL := by norm_num [v21RootPiL]
  have hpiSq : v21RootPiL ^ 2 ≤ Real.pi ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hpiL)
      (add_nonneg Real.pi_pos.le hpiL0)]
  have hC0 : 0 ≤ v21C := by nlinarith [v21_C_gt_half]
  exact mul_le_mul hCL hpiSq (sq_nonneg v21RootPiL) hC0

private lemma v21_root_slope_pos_side {n : ℕ} (hn : 1 ≤ n) {x : ℝ}
    (hx0 : (n : ℝ) ≤ x)
    (hxU : x ≤ (n : ℝ) + (151 / 1000 : ℝ)) :
    (6 : ℝ) * (n : ℝ) ≤ v21RootHDeriv n x := by
  let e : ℝ := x - (n : ℝ)
  have he0 : 0 ≤ e := by dsimp [e]; linarith
  have heU : e ≤ (151 / 1000 : ℝ) := by dsimp [e]; linarith
  have hcos := v21_root_cos_pos_floor he0 heU
  have ht0 : 0 ≤ Real.pi * e := mul_nonneg Real.pi_pos.le he0
  have he1 : e ≤ 1 := by linarith
  have htPi : Real.pi * e ≤ Real.pi := by
    simpa [mul_one] using mul_le_mul_of_nonneg_left he1 Real.pi_pos.le
  have hsin0 : 0 ≤ Real.sin (Real.pi * e) :=
    Real.sin_nonneg_of_nonneg_of_le_pi ht0 htPi
  have hCpi := v21_root_Cpi2_lower
  have hn0 : 0 ≤ (n : ℝ) := by positivity
  have hright0 : 0 ≤ v21C * Real.pi ^ 2 := by
    have hC0 : 0 ≤ v21C := by nlinarith [v21_C_gt_half]
    positivity
  have hprod1 :
      v21RootCL * v21RootPiL ^ 2 * (n : ℝ) ≤
        v21C * Real.pi ^ 2 * x :=
    mul_le_mul hCpi hx0 hn0 hright0
  have hright1 : 0 ≤ v21C * Real.pi ^ 2 * x :=
    mul_nonneg hright0 (le_trans hn0 hx0)
  have hcosTerm :
      v21RootCL * v21RootPiL ^ 2 * (n : ℝ) * (887 / 1000 : ℝ) ≤
        v21C * Real.pi ^ 2 * x * Real.cos (Real.pi * e) :=
    mul_le_mul hprod1 hcos (by norm_num) hright1
  have hcoef :
      (6 : ℝ) ≤ v21RootCL * v21RootPiL ^ 2 * (887 / 1000 : ℝ) := by
    norm_num [v21RootCL, v21RootPiL]
  have hrat :
      (6 : ℝ) * (n : ℝ) ≤
        v21RootCL * v21RootPiL ^ 2 * (n : ℝ) * (887 / 1000 : ℝ) := by
    have := mul_le_mul_of_nonneg_right hcoef hn0
    nlinarith
  have hC0 : 0 ≤ v21C := by nlinarith [v21_C_gt_half]
  have hsinTerm1 : 0 ≤ v21C * Real.pi * Real.sin (Real.pi * e) := by
    positivity
  have hsinTerm2 :
      0 ≤ (1 / 2 : ℝ) * Real.pi * Real.sin (Real.pi * e) := by
    positivity
  unfold v21RootHDeriv
  dsimp [e] at hcosTerm hsinTerm1 hsinTerm2
  nlinarith

private lemma v21_root_slope_neg_side {n : ℕ} (hn : 1 ≤ n) {x : ℝ}
    (hxL : (n : ℝ) - (1 / 20 : ℝ) ≤ x)
    (hx0 : x ≤ (n : ℝ)) :
    (6 : ℝ) * (n : ℝ) ≤ v21RootHDeriv n x := by
  let e : ℝ := x - (n : ℝ)
  have heL : -(1 / 20 : ℝ) ≤ e := by dsimp [e]; linarith
  have he0 : e ≤ 0 := by dsimp [e]; linarith
  have hcos := v21_root_cos_neg_floor heL he0
  have hsin := v21_root_sin_neg_floor heL he0
  have ht0 : Real.pi * e ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos Real.pi_pos.le he0
  have heNegOne : -(1 : ℝ) ≤ e := by linarith
  have hnegPi : -Real.pi ≤ Real.pi * e := by
    nlinarith [mul_nonneg Real.pi_pos.le (show 0 ≤ e + 1 by linarith)]
  have hsinNonpos : Real.sin (Real.pi * e) ≤ 0 :=
    Real.sin_nonpos_of_nonpos_of_neg_pi_le ht0 hnegPi
  have hpiU : Real.pi ≤ v21RootPiU := by
    simpa [v21RootPiU] using (le_of_lt v21_pi_upper)
  have hCU : v21C ≤ v21RootCU := by
    simpa [v21RootCU] using v21_C_upper
  have hsum : v21C + (1 / 2 : ℝ) ≤ v21RootCU + (1 / 2 : ℝ) := by
    linarith
  have hsum0 : 0 ≤ v21C + (1 / 2 : ℝ) := by
    nlinarith [v21_C_gt_half]
  have hpiU0 : 0 ≤ v21RootPiU := by norm_num [v21RootPiU]
  have hcoefUpper :
      Real.pi * (v21C + (1 / 2 : ℝ)) ≤
        v21RootPiU * (v21RootCU + (1 / 2 : ℝ)) :=
    mul_le_mul hpiU hsum hsum0 hpiU0
  have hA0 :
      0 ≤ v21RootPiU * (v21RootCU + (1 / 2 : ℝ)) := by
    norm_num [v21RootPiU, v21RootCU]
  have hsin1 :
      v21RootPiU * (v21RootCU + (1 / 2 : ℝ)) *
          Real.sin (Real.pi * e) ≤
        Real.pi * (v21C + (1 / 2 : ℝ)) *
          Real.sin (Real.pi * e) :=
    mul_le_mul_of_nonpos_right hcoefUpper hsinNonpos
  have hsin2 :
      v21RootPiU * (v21RootCU + (1 / 2 : ℝ)) *
          (-(v21RootPiU / 20)) ≤
        v21RootPiU * (v21RootCU + (1 / 2 : ℝ)) *
          Real.sin (Real.pi * e) :=
    mul_le_mul_of_nonneg_left hsin hA0
  have hsinTerm :
      -(v21RootPiU * (v21RootCU + (1 / 2 : ℝ)) *
          (v21RootPiU / 20)) ≤
        Real.pi * (v21C + (1 / 2 : ℝ)) *
          Real.sin (Real.pi * e) := by
    nlinarith
  have hCpi := v21_root_Cpi2_lower
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnLeft0 : 0 ≤ (n : ℝ) - (1 / 20 : ℝ) := by linarith
  have hright0 : 0 ≤ v21C * Real.pi ^ 2 := by
    have hC0 : 0 ≤ v21C := by nlinarith [v21_C_gt_half]
    positivity
  have hprod1 :
      v21RootCL * v21RootPiL ^ 2 * ((n : ℝ) - (1 / 20 : ℝ)) ≤
        v21C * Real.pi ^ 2 * x :=
    mul_le_mul hCpi hxL hnLeft0 hright0
  have hxNonneg : 0 ≤ x := le_trans hnLeft0 hxL
  have hright1 : 0 ≤ v21C * Real.pi ^ 2 * x :=
    mul_nonneg hright0 hxNonneg
  have hcosTerm :
      v21RootCL * v21RootPiL ^ 2 * ((n : ℝ) - (1 / 20 : ℝ)) *
          (987 / 1000 : ℝ) ≤
        v21C * Real.pi ^ 2 * x * Real.cos (Real.pi * e) :=
    mul_le_mul hprod1 hcos (by norm_num) hright1
  have hrat :
      (6 : ℝ) * (n : ℝ) ≤
        v21RootCL * v21RootPiL ^ 2 * ((n : ℝ) - (1 / 20 : ℝ)) *
          (987 / 1000 : ℝ) -
        v21RootPiU * (v21RootCU + (1 / 2 : ℝ)) *
          (v21RootPiU / 20) := by
    norm_num [v21RootCL, v21RootPiL, v21RootPiU, v21RootCU]
    nlinarith
  unfold v21RootHDeriv
  dsimp [e] at hcosTerm hsinTerm
  nlinarith

/-- Uniform slope bound on the entire root-cell range needed by the analytic
quadratic bootstrap. -/
lemma v21_rootHDeriv_ge_six_mul {n : ℕ} (hn : 1 ≤ n) {x : ℝ}
    (hxL : (n : ℝ) - (1 / 20 : ℝ) ≤ x)
    (hxU : x ≤ (n : ℝ) + (151 / 1000 : ℝ)) :
    (6 : ℝ) * (n : ℝ) ≤ v21RootHDeriv n x := by
  by_cases hx0 : (n : ℝ) ≤ x
  · exact v21_root_slope_pos_side hn hx0 hxU
  · exact v21_root_slope_neg_side hn hxL (le_of_not_ge hx0)

end HurtadoZeta23
