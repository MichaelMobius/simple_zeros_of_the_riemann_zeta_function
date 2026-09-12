import HurtadoZeta23.V21KernelRootCatalog
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

noncomputable section

open Set

namespace HurtadoZeta23

/-- Quantitative monotonicity of the cleared root numerator on every cell used
by the bootstrap.  No root is chosen: this is a direct mean-value estimate. -/
lemma v21_rootH_growth {n : ℕ} (hn : 1 ≤ n) {x y : ℝ}
    (hxL : (n : ℝ) - (1 / 20 : ℝ) ≤ x)
    (hyU : y ≤ (n : ℝ) + (151 / 1000 : ℝ))
    (hxy : x ≤ y) :
    (7 : ℝ) * (n : ℝ) * (y - x) ≤ v21RootH n y - v21RootH n x := by
  let D : Set ℝ := Icc ((n : ℝ) - (1 / 20 : ℝ))
    ((n : ℝ) + (151 / 1000 : ℝ))
  have hxU : x ≤ (n : ℝ) + (151 / 1000 : ℝ) := hxy.trans hyU
  have hyL : (n : ℝ) - (1 / 20 : ℝ) ≤ y := hxL.trans hxy
  have hxD : x ∈ D := by exact ⟨hxL, hxU⟩
  have hyD : y ∈ D := by exact ⟨hyL, hyU⟩
  have hcont : ContinuousOn (v21RootH n) D := by
    intro z hz
    exact (v21_rootH_hasDerivAt n z).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ (v21RootH n) (interior D) := by
    intro z hz
    exact (v21_rootH_hasDerivAt n z).differentiableAt.differentiableWithinAt
  have hder : ∀ z ∈ interior D,
      (7 : ℝ) * (n : ℝ) ≤ deriv (v21RootH n) z := by
    intro z hz
    have hzD : z ∈ D := interior_subset hz
    rw [(v21_rootH_hasDerivAt n z).deriv]
    exact v21_rootHDeriv_ge_seven_mul hn hzD.1 hzD.2
  exact (convex_Icc _ _).mul_sub_le_image_sub_of_le_deriv
    hcont hdiff hder x hxD y hyD hxy

lemma v21_root_left_le_right {n : ℕ} (hn1 : 1 ≤ n) (hn12 : n ≤ 12) :
    v21RootLeft n ≤ v21RootRight n := by
  have h := v21_root_width hn1 hn12
  linarith

lemma v21_root_left_upper_cell {n : ℕ} (hn1 : 1 ≤ n) (hn12 : n ≤ 12) :
    v21RootLeft n ≤ (n : ℝ) + (151 / 1000 : ℝ) := by
  exact (v21_root_left_le_right hn1 hn12).trans
    (v21_root_right_cell hn1 hn12)

lemma v21_root_right_lower_cell {n : ℕ} (hn1 : 1 ≤ n) (hn12 : n ≤ 12) :
    (n : ℝ) - (1 / 20 : ℝ) ≤ v21RootRight n := by
  exact (v21_root_left_cell hn1 hn12).trans
    (v21_root_left_le_right hn1 hn12)

/-- Left of the certified bracket, the numerator is quantitatively negative. -/
lemma v21_rootH_left_linear {n : ℕ} (hn1 : 1 ≤ n) (hn12 : n ≤ 12) {x : ℝ}
    (hxCell : (n : ℝ) - (1 / 20 : ℝ) ≤ x)
    (hx : x ≤ v21RootLeft n) :
    (7 : ℝ) * (n : ℝ) * (v21RootLeft n - x) + (7 / 100000 : ℝ)
      ≤ -v21RootH n x := by
  have hg := v21_rootH_growth hn1 hxCell
    (v21_root_left_upper_cell hn1 hn12) hx
  have hs := v21_root_left_sign hn1 hn12
  linarith

/-- Right of the certified bracket, the numerator is quantitatively positive. -/
lemma v21_rootH_right_linear {n : ℕ} (hn1 : 1 ≤ n) (hn12 : n ≤ 12) {x : ℝ}
    (hx : v21RootRight n ≤ x)
    (hxCell : x ≤ (n : ℝ) + (151 / 1000 : ℝ)) :
    (7 : ℝ) * (n : ℝ) * (x - v21RootRight n) + (1 / 100000 : ℝ)
      ≤ v21RootH n x := by
  have hg := v21_rootH_growth hn1
    (v21_root_right_lower_cell hn1 hn12) hxCell hx
  have hs := v21_root_right_sign hn1 hn12
  linarith

/-- Absolute-value form of the left linear estimate. -/
lemma v21_rootH_abs_left {n : ℕ} (hn1 : 1 ≤ n) (hn12 : n ≤ 12) {x : ℝ}
    (hxCell : (n : ℝ) - (1 / 20 : ℝ) ≤ x)
    (hx : x ≤ v21RootLeft n) :
    (7 : ℝ) * (n : ℝ) * (v21RootLeft n - x) ≤ |v21RootH n x| := by
  have hlin := v21_rootH_left_linear hn1 hn12 hxCell hx
  have hn0 : 0 ≤ (n : ℝ) := by positivity
  have hdist : 0 ≤ v21RootLeft n - x := sub_nonneg.mpr hx
  have hnonpos : v21RootH n x ≤ 0 := by
    nlinarith [mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 7) hn0) hdist]
  rw [abs_of_nonpos hnonpos]
  nlinarith

/-- Absolute-value form of the right linear estimate. -/
lemma v21_rootH_abs_right {n : ℕ} (hn1 : 1 ≤ n) (hn12 : n ≤ 12) {x : ℝ}
    (hx : v21RootRight n ≤ x)
    (hxCell : x ≤ (n : ℝ) + (151 / 1000 : ℝ)) :
    (7 : ℝ) * (n : ℝ) * (x - v21RootRight n) ≤ |v21RootH n x| := by
  have hlin := v21_rootH_right_linear hn1 hn12 hx hxCell
  have hn0 : 0 ≤ (n : ℝ) := by positivity
  have hdist : 0 ≤ x - v21RootRight n := sub_nonneg.mpr hx
  have hnonneg : 0 ≤ v21RootH n x := by
    nlinarith [mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 7) hn0) hdist]
  rw [abs_of_nonneg hnonneg]
  nlinarith

end HurtadoZeta23
