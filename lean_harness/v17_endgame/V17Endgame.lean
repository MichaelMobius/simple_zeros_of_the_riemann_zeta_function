import HurtadoZeta23.Constants
import Zeta23.Assembly
import Mathlib.Tactic

noncomputable section

open Filter Asymptotics

namespace HurtadoZeta23

private def v17N (T : ℝ) : ℝ := (Zeta23.Ncount T (2 * T) : ℝ)
private def v17S (T : ℝ) : ℝ := (Zeta23.N0simple T (2 * T) : ℝ)

/-- v17 coefficient `A/m = (4329/2500)/450`. -/
def v17Alpha : ℝ := 481 / 125000

/-- v17 exact-pressure global cost `Q/m = (111/125)/450`. -/
def v17PressureCost : ℝ := 37 / 18750

/-- Exact constant displayed in the v17 paper. -/
def v17PublishedConstant : ℝ :=
  (1125000 * HMT - 2220) / 1120671

lemma v17_oneMinusAlpha_pos : 0 < 1 - v17Alpha := by
  norm_num [v17Alpha]

lemma v17_alpha_eq_A_div_m :
    v17Alpha = (4329 / 2500 : ℝ) / 450 := by
  norm_num [v17Alpha]

lemma v17_pressureCost_eq_Q_div_m :
    v17PressureCost = (111 / 125 : ℝ) / 450 := by
  norm_num [v17PressureCost]

lemma v17_publishedConstant_eq_ratio :
    v17PublishedConstant =
      (HMT - v17PressureCost) / (1 - v17Alpha) := by
  unfold v17PublishedConstant v17PressureCost v17Alpha
  field_simp
  ring

/-- The sole global input required by the v17 endgame once the block analysis
and shifted exact-pressure averaging have been formalized. -/
structure V17GlobalRefinement where
  err : ℝ → ℝ
  err_small : err =o[atTop] v17N
  bound : ∀ᶠ T in atTop,
    HMT * v17N T + v17Alpha * v17S T - v17PressureCost * v17N T - err T
      ≤ v17S T

lemma v17_normalized_eventual_bound (h : V17GlobalRefinement) :
    ∀ᶠ T in atTop,
      ((HMT - v17PressureCost) / (1 - v17Alpha)) * v17N T
        - (1 - v17Alpha)⁻¹ * h.err T ≤ v17S T := by
  have hd : 0 < 1 - v17Alpha := v17_oneMinusAlpha_pos
  filter_upwards [h.bound] with T hT
  have hdiff :
      HMT * v17N T + v17Alpha * v17S T - v17PressureCost * v17N T
          - h.err T - v17S T ≤ 0 := by
    linarith
  have hid :
      ((HMT - v17PressureCost) / (1 - v17Alpha)) * v17N T
          - (1 - v17Alpha)⁻¹ * h.err T - v17S T
        = (1 - v17Alpha)⁻¹ *
            (HMT * v17N T + v17Alpha * v17S T - v17PressureCost * v17N T
              - h.err T - v17S T) := by
    field_simp [ne_of_gt hd]
    ring
  rw [← sub_nonpos, hid]
  exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr hd.le) hdiff

lemma v17_normalized_error_small (h : V17GlobalRefinement) :
    (fun T => (1 - v17Alpha)⁻¹ * h.err T) =o[atTop] v17N :=
  h.err_small.const_mul_left _

/-- Kernel-checked v17 endgame in epsilon form. -/
theorem v17_eps_form_from_global_refinement (h : V17GlobalRefinement) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (((HMT - v17PressureCost) / (1 - v17Alpha)) - ε) *
          (Zeta23.Ncount T (2 * T) : ℝ)
        ≤ Zeta23.N0simple T (2 * T) := by
  exact Zeta23.Assembly.eps_form_of_isLittleO
    (v17_normalized_eventual_bound h)
    (Eventually.of_forall fun T => Nat.cast_nonneg _)
    (v17_normalized_error_small h)

/-- The same theorem with the exact v17 published constant. -/
theorem v17_published_eps_form_from_global_refinement (h : V17GlobalRefinement) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (v17PublishedConstant - ε) * (Zeta23.Ncount T (2 * T) : ℝ)
        ≤ Zeta23.N0simple T (2 * T) := by
  rw [v17_publishedConstant_eq_ratio]
  exact v17_eps_form_from_global_refinement h

end HurtadoZeta23
