import HurtadoZeta23.V21KernelRootGrowth
import Mathlib.Tactic

noncomputable section

namespace HurtadoZeta23

def v21RootHalfWidth : ℝ := 1 / 200000

def v21RootRamp (n : ℕ) (x : ℝ) : ℝ :=
  max (|x - v21RootMid n| - v21RootHalfWidth) 0

lemma v21_root_halfwidth_nonneg : 0 ≤ v21RootHalfWidth := by
  norm_num [v21RootHalfWidth]

lemma v21_root_ramp_nonneg (n : ℕ) (x : ℝ) : 0 ≤ v21RootRamp n x := by
  unfold v21RootRamp
  exact le_max_right _ _

lemma v21_root_ramp_eq_left {n : ℕ} (hn1 : 1 ≤ n) (hn12 : n ≤ 12) {x : ℝ}
    (hx : x ≤ v21RootLeft n) :
    v21RootRamp n x = v21RootLeft n - x := by
  have hmid := v21_root_mid_sub_left hn1 hn12
  have hxmid : x ≤ v21RootMid n := by
    norm_num [v21RootHalfWidth] at hmid
    linarith
  have hdist : 0 ≤ v21RootLeft n - x := sub_nonneg.mpr hx
  unfold v21RootRamp v21RootHalfWidth
  rw [abs_of_nonpos (sub_nonpos.mpr hxmid)]
  have heq : -(x - v21RootMid n) - 1 / 200000 = v21RootLeft n - x := by
    linarith [v21_root_mid_sub_left hn1 hn12]
  rw [heq, max_eq_left hdist]

lemma v21_root_ramp_eq_right {n : ℕ} (hn1 : 1 ≤ n) (hn12 : n ≤ 12) {x : ℝ}
    (hx : v21RootRight n ≤ x) :
    v21RootRamp n x = x - v21RootRight n := by
  have hmid := v21_root_right_sub_mid hn1 hn12
  have hmidx : v21RootMid n ≤ x := by
    norm_num [v21RootHalfWidth] at hmid
    linarith
  have hdist : 0 ≤ x - v21RootRight n := sub_nonneg.mpr hx
  unfold v21RootRamp v21RootHalfWidth
  rw [abs_of_nonneg (sub_nonneg.mpr hmidx)]
  have heq : x - v21RootMid n - 1 / 200000 = x - v21RootRight n := by
    linarith [v21_root_right_sub_mid hn1 hn12]
  rw [heq, max_eq_left hdist]

lemma v21_root_ramp_eq_zero_of_mem_bracket {n : ℕ}
    (hn1 : 1 ≤ n) (hn12 : n ≤ 12) {x : ℝ}
    (hxL : v21RootLeft n ≤ x) (hxR : x ≤ v21RootRight n) :
    v21RootRamp n x = 0 := by
  have hML := v21_root_mid_sub_left hn1 hn12
  have hRM := v21_root_right_sub_mid hn1 hn12
  have habs : |x - v21RootMid n| ≤ v21RootHalfWidth := by
    rw [abs_le]
    constructor
    · norm_num [v21RootHalfWidth] at hRM ⊢
      linarith
    · norm_num [v21RootHalfWidth] at hML ⊢
      linarith
  unfold v21RootRamp
  rw [max_eq_right]
  linarith

/-- The endpoint signs plus the uniform slope control the absolute numerator
by the distance outside the rational root bracket. -/
lemma v21_rootH_abs_ge_ramp {n : ℕ} (hn1 : 1 ≤ n) (hn12 : n ≤ 12) {x : ℝ}
    (hxL : (n : ℝ) - (1 / 20 : ℝ) ≤ x)
    (hxU : x ≤ (n : ℝ) + (151 / 1000 : ℝ)) :
    (7 : ℝ) * (n : ℝ) * v21RootRamp n x ≤ |v21RootH n x| := by
  by_cases hleft : x ≤ v21RootLeft n
  · rw [v21_root_ramp_eq_left hn1 hn12 hleft]
    exact v21_rootH_abs_left hn1 hn12 hxL hleft
  · have hLx : v21RootLeft n ≤ x := le_of_not_ge hleft
    by_cases hright : v21RootRight n ≤ x
    · rw [v21_root_ramp_eq_right hn1 hn12 hright]
      exact v21_rootH_abs_right hn1 hn12 hright hxU
    · have hxR : x ≤ v21RootRight n := le_of_not_ge hright
      rw [v21_root_ramp_eq_zero_of_mem_bracket hn1 hn12 hLx hxR, mul_zero]
      exact abs_nonneg _

/-- A purely algebraic minorant converting a bracket ramp into a global
quadratic centered at the rational midpoint. -/
lemma v21_ramp_sq_ge_quadratic (z : ℝ) :
    (99 / 100 : ℝ) * z ^ 2 -
        99 * (1 / 200000 : ℝ) ^ 2 ≤
      (max (|z| - (1 / 200000 : ℝ)) 0) ^ 2 := by
  by_cases hz : |z| ≤ (1 / 200000 : ℝ)
  · have hmax : max (|z| - (1 / 200000 : ℝ)) 0 = 0 := by
      exact max_eq_right (sub_nonpos.mpr hz)
    rw [hmax]
    have hp :
        0 ≤ ((1 / 200000 : ℝ) - |z|) * ((1 / 200000 : ℝ) + |z|) := by
      apply mul_nonneg
      · exact sub_nonneg.mpr hz
      · positivity
    have habs : |z| ^ 2 = z ^ 2 := sq_abs z
    nlinarith
  · have hz' : (1 / 200000 : ℝ) ≤ |z| := (le_of_not_ge hz).le
    rw [max_eq_left (sub_nonneg.mpr hz')]
    have habs : |z| ^ 2 = z ^ 2 := sq_abs z
    nlinarith [sq_nonneg (|z| / 10 - 10 * (1 / 200000 : ℝ))]

/-- Root-free quadratic minorant for the cleared numerator.  Everything on
the left is rational apart from the variable `x`; no IVT root and no arctan
appears in the statement. -/
lemma v21_rootH_sq_ge_quadratic {n : ℕ} (hn1 : 1 ≤ n) (hn12 : n ≤ 12) {x : ℝ}
    (hxL : (n : ℝ) - (1 / 20 : ℝ) ≤ x)
    (hxU : x ≤ (n : ℝ) + (151 / 1000 : ℝ)) :
    ((7 : ℝ) * (n : ℝ)) ^ 2 *
        ((99 / 100 : ℝ) * (x - v21RootMid n) ^ 2 -
          99 * (1 / 200000 : ℝ) ^ 2) ≤
      (v21RootH n x) ^ 2 := by
  have habs := v21_rootH_abs_ge_ramp hn1 hn12 hxL hxU
  have hcoef0 : 0 ≤ (7 : ℝ) * (n : ℝ) := by positivity
  have hramp0 := v21_root_ramp_nonneg n x
  have habs0 : 0 ≤ |v21RootH n x| := abs_nonneg _
  have hfac :
      0 ≤ (|v21RootH n x| - (7 : ℝ) * (n : ℝ) * v21RootRamp n x) *
        (|v21RootH n x| + (7 : ℝ) * (n : ℝ) * v21RootRamp n x) := by
    apply mul_nonneg
    · exact sub_nonneg.mpr habs
    · exact add_nonneg habs0 (mul_nonneg hcoef0 hramp0)
  have hsquare :
      (((7 : ℝ) * (n : ℝ)) * v21RootRamp n x) ^ 2 ≤
        |v21RootH n x| ^ 2 := by
    nlinarith
  have hquad := v21_ramp_sq_ge_quadratic (x - v21RootMid n)
  have hscaled := mul_le_mul_of_nonneg_left hquad
    (sq_nonneg ((7 : ℝ) * (n : ℝ)))
  have habssq : |v21RootH n x| ^ 2 = (v21RootH n x) ^ 2 := sq_abs _
  unfold v21RootRamp v21RootHalfWidth at hsquare
  rw [habssq] at hsquare
  nlinarith

end HurtadoZeta23
