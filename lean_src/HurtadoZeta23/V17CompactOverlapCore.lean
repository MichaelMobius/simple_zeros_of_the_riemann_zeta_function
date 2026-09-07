import HurtadoZeta23.V17ArticleSynthesisOverlapCore
import HurtadoZeta23.V17PoissonGramBound
import HurtadoZeta23.FourierL1
import HurtadoZeta23.CompactOverlapLimit
import HurtadoZeta23.ConcreteGridTailBound
import HurtadoZeta23.FiniteGridEndpointBridge
import Mathlib.Tactic

noncomputable section

namespace HurtadoZeta23

open Real Filter Topology
open scoped BigOperators

/-!
# Lightweight quantitative overlap data for v17

This file retains only the block-length-free quantitative definitions and
scalar bounds required by the 450-point bridge.  It deliberately avoids the
historical finite-T shifted-pinching closure and its external certificate
frontier.
-/

/-- Explicit raw two-sided p=4 tail majorant for the article window. -/
def v17ArticleRawTailBound (T : ℝ) (M : ℕ) : ℝ :=
  2 *
    ((((Zeta23.ThmD.cDT articleParams.ϱ 1) / articleParams.w) ^ 2 /
        (articleCriticalStep T) ^ 4) *
      p4Tail M)

/-- Explicit normalized compact-overlap error used by the v17 bridge. -/
def v17ArticleCompactError (T : ℝ) (M : ℕ) : ℝ :=
  v17ArticleRawTailBound T M /
      (|phiDMean articleParams.ϱ 1 (articleParams.L T) articleParams.w| *
        (articleParams.L T) ^ 2)
    +
  20 * (articleParams.w / articleParams.L T) / limitingK 0

/-- The scalar p=4 tail is nonnegative. -/
theorem v17_p4Tail_nonneg (M : ℕ) : 0 ≤ p4Tail M := by
  unfold p4Tail
  apply tsum_nonneg
  intro k
  unfold p4Majorant
  positivity

/-- The explicit v17 compact-overlap error is nonnegative in the positive
height regime. -/
theorem v17ArticleCompactError_nonneg
    {T : ℝ} (hl : 0 < Zeta23.l T) (M : ℕ) :
    0 ≤ v17ArticleCompactError T M := by
  have hL : 0 < articleParams.L T := by
    simpa [articleParams_L_eq_zeta_l] using hl
  have hw : 0 ≤ articleParams.w := by
    linarith [articleParams_valid.one_le_w]
  have hK : 0 < limitingK 0 := limitingK_zero_pos
  have hp4 : 0 ≤ p4Tail M := v17_p4Tail_nonneg M
  have hraw : 0 ≤ v17ArticleRawTailBound T M := by
    unfold v17ArticleRawTailBound
    positivity
  have hden :
      0 ≤
        |phiDMean articleParams.ϱ 1 (articleParams.L T) articleParams.w| *
          (articleParams.L T) ^ 2 := by
    positivity
  have hfirst :
      0 ≤
        v17ArticleRawTailBound T M /
          (|phiDMean articleParams.ϱ 1 (articleParams.L T) articleParams.w| *
            (articleParams.L T) ^ 2) :=
    div_nonneg hraw hden
  have hsecond :
      0 ≤ 20 * (articleParams.w / articleParams.L T) / limitingK 0 := by
    positivity
  unfold v17ArticleCompactError
  linarith

/-- The normalized limiting overlap satisfies `|limitingk x| ≤ 1`. -/
theorem v17_limitingk_abs_le_one (x : ℝ) : |limitingk x| ≤ 1 := by
  have hK : |limitingK x| ≤ limitingK 0 :=
    limitingKernelMajorization_proved x
  have hK0 : 0 < limitingK 0 := limitingK_zero_pos
  unfold limitingk
  rw [abs_div, abs_of_pos hK0]
  apply (div_le_iff₀ hK0).2
  simpa using hK

end HurtadoZeta23
