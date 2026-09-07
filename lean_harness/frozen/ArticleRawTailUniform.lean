import HurtadoZeta23.ArticleTailRate
import HurtadoZeta23.ConcreteFiniteClosure
import Mathlib.Tactic

noncomputable section

open Real Filter Topology

namespace HurtadoZeta23

/-!
# Uniform raw-tail bound along the article margin

The factor `articleCriticalStep(T)^(-4)` grows like `l(T)^4`, while the
chosen p=4 tail decays like `l(T)^(-4)`.  This file records the exact
cancellation as a uniform constant.
-/

/-- T-independent constant controlling the raw finite-grid tail. -/
def articleRawTailConst : ℝ :=
  32 *
      ((Zeta23.ThmD.cDT articleParams.ϱ 1 / articleParams.w) ^ 2) *
      p2ShiftSum /
    (2 * Real.pi) ^ 4

theorem articleRawTailConst_nonneg :
    0 ≤ articleRawTailConst := by

  have hw :
      0 < articleParams.w := by
    linarith [articleParams_valid.one_le_w]

  have hsum :
      0 ≤ p2ShiftSum :=
    p2ShiftSum_nonneg

  unfold articleRawTailConst
  positivity

/--
For `l(T) ≥ 2`, the raw finite-grid tail along the chosen margin is bounded
by a constant independent of `T`.
-/
theorem articleRawTailBound_margin_le_const
    {T : ℝ}
    (hl2 : 2 ≤ Zeta23.l T) :
    articleRawTailBound T (articleTailMargin T)
      ≤
    articleRawTailConst := by

  have hlpos :
      0 < Zeta23.l T := by
    linarith

  have hstep :
      0 < articleCriticalStep T := by
    exact articleCriticalStep_pos hlpos

  have htail :
      p4Tail (articleTailMargin T)
        ≤
      16 * p2ShiftSum / (Zeta23.l T) ^ 4 :=
    p4Tail_articleTailMargin_le hl2

  have hfac :
      0 ≤
        2 *
          (((Zeta23.ThmD.cDT articleParams.ϱ 1 /
                articleParams.w) ^ 2 /
              (articleCriticalStep T) ^ 4)) := by
    positivity

  have hmul :
      (2 *
          (((Zeta23.ThmD.cDT articleParams.ϱ 1 /
                articleParams.w) ^ 2 /
              (articleCriticalStep T) ^ 4))) *
          p4Tail (articleTailMargin T)
        ≤
      (2 *
          (((Zeta23.ThmD.cDT articleParams.ϱ 1 /
                articleParams.w) ^ 2 /
              (articleCriticalStep T) ^ 4))) *
          (16 * p2ShiftSum / (Zeta23.l T) ^ 4) :=
    mul_le_mul_of_nonneg_left htail hfac

  have hwpos :
      0 < articleParams.w := by
    linarith [articleParams_valid.one_le_w]

  calc
    articleRawTailBound T (articleTailMargin T)
        =
      (2 *
          (((Zeta23.ThmD.cDT articleParams.ϱ 1 /
                articleParams.w) ^ 2 /
              (articleCriticalStep T) ^ 4))) *
          p4Tail (articleTailMargin T) := by
            unfold articleRawTailBound
            ring

    _ ≤
      (2 *
          (((Zeta23.ThmD.cDT articleParams.ϱ 1 /
                articleParams.w) ^ 2 /
              (articleCriticalStep T) ^ 4))) *
          (16 * p2ShiftSum / (Zeta23.l T) ^ 4) :=
      hmul

    _ =
      articleRawTailConst := by

      unfold articleRawTailConst
      unfold articleCriticalStep

      field_simp [
        ne_of_gt hlpos,
        ne_of_gt hwpos,
        Real.pi_ne_zero
      ] <;> ring

/-- Eventual uniform form. -/
theorem eventually_articleRawTailBound_margin_le_const :
    ∀ᶠ T : ℝ in atTop,
      articleRawTailBound T (articleTailMargin T)
        ≤
      articleRawTailConst := by

  filter_upwards [eventually_two_le_zeta_l] with T hl2

  exact articleRawTailBound_margin_le_const hl2

end HurtadoZeta23
