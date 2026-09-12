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
  have ht0 : t ≤ 0 := by dsimp [t]; exact mul_nonpos_of_nonneg_of_nonpos Real.pi_pos.le he0
  have htL : -B ≤ t := by
    dsimp [B, t]
    have h1 : -(v21RootPiU / 20) ≤ -(Real.pi / 20) := by
      nlinarith
    have h2 : -(Real.pi / 20) ≤ Real.pi * e := by
      nlinarith [mul_nonneg Real.pi_pos.le (sub_nonneg.mpr (show e + 1 / 20 ≥ 0 by linarith))]
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
    have h2 : -(Real.pi / 20) ≤ Real.pi * e := by
      nlinarith [mul_nonneg Real.pi_pos.le (sub_nonneg.mpr (show e + 1 / 20 ≥ 0 by linarith))]
    exact h1.trans h2
  exact htL.trans (Real.le_sin ht0)

end HurtadoZeta23
