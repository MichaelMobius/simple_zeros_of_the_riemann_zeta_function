import HurtadoZeta23.Constants
import Zeta23.Assembly

noncomputable section

open Filter Asymptotics

namespace HurtadoZeta23

private def N (T : ℝ) : ℝ := (Zeta23.Ncount T (2 * T) : ℝ)
private def S (T : ℝ) : ℝ := (Zeta23.N0simple T (2 * T) : ℝ)

/--
The exact new global input required beyond Zeta23.

It is the Lean form of
  N₀ˢ ≥ H_MT N + α N₀ˢ - pressureCost N - o(N).

Everything analytic already present in Zeta23 is deliberately *not* repeated here.
The remaining formalization task is to derive this structure from the position-weighted
seven-point certificate and shifted-block averaging.
-/
structure GlobalRefinement where
  err : ℝ → ℝ
  err_small : err =o[atTop] N
  bound : ∀ᶠ T in atTop,
    HMT * N T + alpha * S T - pressureCost * N T - err T ≤ S T

/-- Pure algebra: normalize the raw refined inequality by moving α S to the left. -/
lemma normalized_eventual_bound (h : GlobalRefinement) :
    ∀ᶠ T in atTop,
      ((HMT - pressureCost) / (1 - alpha)) * N T
        - (1 - alpha)⁻¹ * h.err T ≤ S T := by
  have hd : 0 < 1 - alpha := oneMinusAlpha_pos
  filter_upwards [h.bound] with T hT
  have hdiff :
      HMT * N T + alpha * S T - pressureCost * N T - h.err T - S T ≤ 0 := by
    linarith
  have hid :
      ((HMT - pressureCost) / (1 - alpha)) * N T
          - (1 - alpha)⁻¹ * h.err T - S T
        = (1 - alpha)⁻¹ *
            (HMT * N T + alpha * S T - pressureCost * N T - h.err T - S T) := by
    field_simp [ne_of_gt hd]
    ring
  rw [← sub_nonpos, hid]
  exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr hd.le) hdiff

/-- The o(N) error survives division by the positive constant 1-α. -/
lemma normalized_error_small (h : GlobalRefinement) :
    (fun T => (1 - alpha)⁻¹ * h.err T) =o[atTop] N :=
  h.err_small.const_mul_left _

/--
Kernel-checked endgame: the new global refinement implies the ε-form of the
published lower bound, using Zeta23's counting functions.
-/
theorem eps_form_from_global_refinement (h : GlobalRefinement) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (((HMT - pressureCost) / (1 - alpha)) - ε) *
          (Zeta23.Ncount T (2 * T) : ℝ)
        ≤ Zeta23.N0simple T (2 * T) := by
  exact Zeta23.Assembly.eps_form_of_isLittleO
    (normalized_eventual_bound h)
    (Eventually.of_forall fun T => Nat.cast_nonneg _)
    (normalized_error_small h)

/-- Same theorem with exactly the constant displayed in the paper. -/
theorem published_eps_form_from_global_refinement (h : GlobalRefinement) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (publishedConstant - ε) * (Zeta23.Ncount T (2 * T) : ℝ)
        ≤ Zeta23.N0simple T (2 * T) := by
  rw [publishedConstant_eq_ratio]
  exact eps_form_from_global_refinement h

end HurtadoZeta23
