import HurtadoZeta23.ResearchShiftedAssembly289
import HurtadoZeta23.ResearchLiminfEndpoint
import Zeta23.Assembly
import Mathlib.Tactic

noncomputable section

open Filter Asymptotics

namespace HurtadoZeta23

private def research9N (T : ℝ) : ℝ :=
  (Zeta23.Ncount T (2 * T) : ℝ)

private def research9S (T : ℝ) : ℝ :=
  (Zeta23.N0simple T (2 * T) : ℝ)

lemma research9_oneMinusAlpha_pos : 0 < 1 - research9Alpha := by
  norm_num [research9Alpha, research9A]

/-- Exact projected constant as the normalized global coefficient. -/
theorem research9_projectedConstant_eq_ratio :
    research9ProjectedBound =
      (research9Hcert - research9PressureCost) / (1 - research9Alpha) := by
  exact research9_projectedBound_eq_global_coefficients

/-- The sole global input required by the research endgame once the local
block analysis, shifted assembly, and independent window baseline have been
established. -/
structure Research9GlobalRefinement where
  err : ℝ → ℝ
  err_small : err =o[atTop] research9N
  bound : ∀ᶠ T in atTop,
    research9Hcert * research9N T
      + research9Alpha * research9S T
      - research9PressureCost * research9N T
      - err T ≤ research9S T

lemma research9_normalized_eventual_bound (h : Research9GlobalRefinement) :
    ∀ᶠ T in atTop,
      ((research9Hcert - research9PressureCost) / (1 - research9Alpha)) *
          research9N T
        - (1 - research9Alpha)⁻¹ * h.err T
      ≤ research9S T := by
  have hd : 0 < 1 - research9Alpha := research9_oneMinusAlpha_pos
  filter_upwards [h.bound] with T hT
  have hdiff :
      research9Hcert * research9N T
          + research9Alpha * research9S T
          - research9PressureCost * research9N T
          - h.err T - research9S T ≤ 0 := by
    linarith
  have hid :
      ((research9Hcert - research9PressureCost) / (1 - research9Alpha)) *
            research9N T
          - (1 - research9Alpha)⁻¹ * h.err T - research9S T
        = (1 - research9Alpha)⁻¹ *
            (research9Hcert * research9N T
              + research9Alpha * research9S T
              - research9PressureCost * research9N T
              - h.err T - research9S T) := by
    field_simp [ne_of_gt hd]
    ring
  rw [← sub_nonpos, hid]
  exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr hd.le) hdiff

lemma research9_normalized_error_small (h : Research9GlobalRefinement) :
    (fun T => (1 - research9Alpha)⁻¹ * h.err T)
      =o[atTop] research9N :=
  h.err_small.const_mul_left _

/-- Research endgame in epsilon form. -/
theorem research9_eps_form_from_global_refinement
    (h : Research9GlobalRefinement) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (((research9Hcert - research9PressureCost) /
          (1 - research9Alpha)) - ε) *
          (Zeta23.Ncount T (2 * T) : ℝ)
        ≤ Zeta23.N0simple T (2 * T) := by
  exact Zeta23.Assembly.eps_form_of_isLittleO
    (research9_normalized_eventual_bound h)
    (Eventually.of_forall fun T => Nat.cast_nonneg _)
    (research9_normalized_error_small h)

/-- Exact candidate-constant epsilon form. -/
theorem research9_projected_eps_form_from_global_refinement
    (h : Research9GlobalRefinement) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (research9ProjectedBound - ε) *
          (Zeta23.Ncount T (2 * T) : ℝ)
        ≤ Zeta23.N0simple T (2 * T) := by
  rw [research9_projectedConstant_eq_ratio]
  exact research9_eps_form_from_global_refinement h

/-- Literal liminf endpoint at the exact projected rational constant. -/
theorem research9_projected_liminf_from_global_refinement
    (h : Research9GlobalRefinement) :
    research9ProjectedBound ≤
      Filter.liminf research9SimpleRatio Filter.atTop := by
  exact research9_liminf_of_eps_form
    (research9_projected_eps_form_from_global_refinement h)

end HurtadoZeta23
