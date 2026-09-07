import HurtadoZeta23.V17CompactOverlapCore
import HurtadoZeta23.ArticleTailRate
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic

noncomputable section

open Real Filter Asymptotics Topology

namespace HurtadoZeta23

/-!
# Lightweight v17 compact-error limit

This is the asymptotic part of the compact-overlap estimate needed by the
length-450 closure.  It deliberately avoids `ConcreteFiniteClosure` and the
historical 262-point synthesis assembly, so the v17 lightweight analytic core
can coexist with the final asymptotic argument without duplicate declarations.
-/

/-- T-independent constant controlling the v17 raw finite-grid tail. -/
def v17ArticleRawTailConst : ℝ :=
  32 *
      ((Zeta23.ThmD.cDT articleParams.ϱ 1 / articleParams.w) ^ 2) *
      p2ShiftSum /
    (2 * Real.pi) ^ 4

theorem v17ArticleRawTailConst_nonneg :
    0 ≤ v17ArticleRawTailConst := by
  have hw : 0 < articleParams.w := by
    linarith [articleParams_valid.one_le_w]
  have hsum : 0 ≤ p2ShiftSum := p2ShiftSum_nonneg
  unfold v17ArticleRawTailConst
  positivity

/-- Along the chosen article margin the v17 raw tail is uniformly bounded. -/
theorem v17ArticleRawTailBound_margin_le_const
    {T : ℝ}
    (hl2 : 2 ≤ Zeta23.l T) :
    v17ArticleRawTailBound T (articleTailMargin T)
      ≤ v17ArticleRawTailConst := by
  have hlpos : 0 < Zeta23.l T := by linarith
  have hstep : 0 < articleCriticalStep T := articleCriticalStep_pos hlpos
  have htail :
      p4Tail (articleTailMargin T)
        ≤ 16 * p2ShiftSum / (Zeta23.l T) ^ 4 :=
    p4Tail_articleTailMargin_le hl2
  have hfac :
      0 ≤
        2 *
          (((Zeta23.ThmD.cDT articleParams.ϱ 1 / articleParams.w) ^ 2 /
              (articleCriticalStep T) ^ 4)) := by
    positivity
  have hmul :
      (2 *
          (((Zeta23.ThmD.cDT articleParams.ϱ 1 / articleParams.w) ^ 2 /
              (articleCriticalStep T) ^ 4))) *
          p4Tail (articleTailMargin T)
        ≤
      (2 *
          (((Zeta23.ThmD.cDT articleParams.ϱ 1 / articleParams.w) ^ 2 /
              (articleCriticalStep T) ^ 4))) *
          (16 * p2ShiftSum / (Zeta23.l T) ^ 4) :=
    mul_le_mul_of_nonneg_left htail hfac
  have hwpos : 0 < articleParams.w := by
    linarith [articleParams_valid.one_le_w]
  calc
    v17ArticleRawTailBound T (articleTailMargin T)
        =
      (2 *
          (((Zeta23.ThmD.cDT articleParams.ϱ 1 / articleParams.w) ^ 2 /
              (articleCriticalStep T) ^ 4))) *
          p4Tail (articleTailMargin T) := by
            unfold v17ArticleRawTailBound
            ring
    _ ≤
      (2 *
          (((Zeta23.ThmD.cDT articleParams.ϱ 1 / articleParams.w) ^ 2 /
              (articleCriticalStep T) ^ 4))) *
          (16 * p2ShiftSum / (Zeta23.l T) ^ 4) := hmul
    _ = v17ArticleRawTailConst := by
      unfold v17ArticleRawTailConst
      unfold articleCriticalStep
      field_simp [ne_of_gt hlpos, ne_of_gt hwpos, Real.pi_ne_zero] <;> ring

/-- A simple explicit upper envelope for the v17 compact-overlap error. -/
def v17ArticleCompactUpper (T : ℝ) : ℝ :=
  (2 * v17ArticleRawTailConst / limitingK 0) *
      ((Zeta23.l T)⁻¹) ^ 2
    +
  (20 * articleParams.w / limitingK 0) *
      (Zeta23.l T)⁻¹

theorem v17ArticleCompactUpper_nonneg
    {T : ℝ}
    (hl : 0 < Zeta23.l T) :
    0 ≤ v17ArticleCompactUpper T := by
  have hK : 0 < limitingK 0 := limitingK_zero_pos
  have hw : 0 < articleParams.w := by
    linarith [articleParams_valid.one_le_w]
  have hC : 0 ≤ v17ArticleRawTailConst := v17ArticleRawTailConst_nonneg
  unfold v17ArticleCompactUpper
  positivity

/-- Pointwise envelope once the standard large-height window conditions hold. -/
theorem v17ArticleCompactError_margin_le_upper
    {T : ℝ}
    (hl2 : 2 ≤ Zeta23.l T)
    (hwL : 8 * articleParams.w ≤ articleParams.L T)
    (hsmall :
      4 * articleParams.w / articleParams.L T ≤ limitingK 0 / 2) :
    v17ArticleCompactError T (articleTailMargin T)
      ≤ v17ArticleCompactUpper T := by
  have hlpos : 0 < Zeta23.l T := by linarith
  have hLpos : 0 < articleParams.L T := by
    simpa [articleParams_L_eq_zeta_l] using hlpos
  have hK : 0 < limitingK 0 := limitingK_zero_pos
  have hKhalf : 0 < limitingK 0 / 2 := by positivity
  have hmeanLower :
      limitingK 0 / 2
        ≤
      |phiDMean articleParams.ϱ 1 (articleParams.L T) articleParams.w| :=
    phiDMean_abs_lower
      articleParams_valid.taper
      articleParams_valid.one_le_w
      hwL hsmall
  have hmeanPos :
      0 < |phiDMean articleParams.ϱ 1 (articleParams.L T) articleParams.w| :=
    lt_of_lt_of_le hKhalf hmeanLower
  have hdenPos :
      0 <
        |phiDMean articleParams.ϱ 1 (articleParams.L T) articleParams.w| *
          (articleParams.L T) ^ 2 := by
    positivity
  have hLsq :
      (articleParams.L T) ^ 2 = (Zeta23.l T) ^ 2 := by
    rw [articleParams_L_eq_zeta_l]
  have hdenLower :
      (limitingK 0 / 2) * (Zeta23.l T) ^ 2
        ≤
      |phiDMean articleParams.ϱ 1 (articleParams.L T) articleParams.w| *
        (articleParams.L T) ^ 2 := by
    calc
      (limitingK 0 / 2) * (Zeta23.l T) ^ 2
          = (limitingK 0 / 2) * (articleParams.L T) ^ 2 := by
              rw [hLsq]
      _ ≤
        |phiDMean articleParams.ϱ 1 (articleParams.L T) articleParams.w| *
          (articleParams.L T) ^ 2 :=
            mul_le_mul_of_nonneg_right hmeanLower (sq_nonneg _)
  have hrawLe :
      v17ArticleRawTailBound T (articleTailMargin T)
        ≤ v17ArticleRawTailConst :=
    v17ArticleRawTailBound_margin_le_const hl2
  have hfirstA :
      v17ArticleRawTailBound T (articleTailMargin T) /
          (|phiDMean articleParams.ϱ 1 (articleParams.L T) articleParams.w| *
            (articleParams.L T) ^ 2)
        ≤
      v17ArticleRawTailConst /
          (|phiDMean articleParams.ϱ 1 (articleParams.L T) articleParams.w| *
            (articleParams.L T) ^ 2) :=
    div_le_div_of_nonneg_right hrawLe (le_of_lt hdenPos)
  have hlowerDenPos :
      0 < (limitingK 0 / 2) * (Zeta23.l T) ^ 2 := by
    positivity
  have hfirstB :
      v17ArticleRawTailConst /
          (|phiDMean articleParams.ϱ 1 (articleParams.L T) articleParams.w| *
            (articleParams.L T) ^ 2)
        ≤
      v17ArticleRawTailConst /
          ((limitingK 0 / 2) * (Zeta23.l T) ^ 2) :=
    div_le_div_of_nonneg_left
      v17ArticleRawTailConst_nonneg hlowerDenPos hdenLower
  have hfirst :
      v17ArticleRawTailBound T (articleTailMargin T) /
          (|phiDMean articleParams.ϱ 1 (articleParams.L T) articleParams.w| *
            (articleParams.L T) ^ 2)
        ≤
      (2 * v17ArticleRawTailConst / limitingK 0) *
        ((Zeta23.l T)⁻¹) ^ 2 := by
    calc
      v17ArticleRawTailBound T (articleTailMargin T) /
          (|phiDMean articleParams.ϱ 1 (articleParams.L T) articleParams.w| *
            (articleParams.L T) ^ 2)
          ≤
        v17ArticleRawTailConst /
          (|phiDMean articleParams.ϱ 1 (articleParams.L T) articleParams.w| *
            (articleParams.L T) ^ 2) := hfirstA
      _ ≤
        v17ArticleRawTailConst /
          ((limitingK 0 / 2) * (Zeta23.l T) ^ 2) := hfirstB
      _ =
        (2 * v17ArticleRawTailConst / limitingK 0) *
          ((Zeta23.l T)⁻¹) ^ 2 := by
            field_simp [ne_of_gt hK, ne_of_gt hlpos]
  have hsecond :
      20 * (articleParams.w / articleParams.L T) / limitingK 0
        =
      (20 * articleParams.w / limitingK 0) * (Zeta23.l T)⁻¹ := by
    rw [articleParams_L_eq_zeta_l]
    field_simp [ne_of_gt hK, ne_of_gt hlpos]
  unfold v17ArticleCompactError
  unfold v17ArticleCompactUpper
  rw [hsecond]
  exact add_le_add_left hfirst _

/-- Eventually the window-size condition `8w ≤ L(T)` holds in the v17 path. -/
theorem eventually_v17_article_hwL :
    ∀ᶠ T : ℝ in atTop,
      8 * articleParams.w ≤ articleParams.L T := by
  have h := tendsto_zeta_l_atTop.eventually_ge_atTop (8 * articleParams.w)
  simpa [articleParams_L_eq_zeta_l] using h

/-- Eventually the small-window condition needed for the mean lower bound holds. -/
theorem eventually_v17_article_hsmall :
    ∀ᶠ T : ℝ in atTop,
      4 * articleParams.w / articleParams.L T ≤ limitingK 0 / 2 := by
  have hK : 0 < limitingK 0 := limitingK_zero_pos
  have hlarge :=
    tendsto_zeta_l_atTop.eventually_ge_atTop
      (8 * articleParams.w / limitingK 0)
  filter_upwards [hlarge, eventually_two_le_zeta_l] with T hT hl2
  have hlpos : 0 < Zeta23.l T := by linarith
  have hmul :
      8 * articleParams.w ≤ Zeta23.l T * limitingK 0 :=
    (div_le_iff₀ hK).mp hT
  rw [articleParams_L_eq_zeta_l]
  apply (div_le_iff₀ hlpos).2
  nlinarith

/-- Eventual pointwise upper envelope. -/
theorem eventually_v17ArticleCompactError_margin_le_upper :
    ∀ᶠ T : ℝ in atTop,
      v17ArticleCompactError T (articleTailMargin T)
        ≤ v17ArticleCompactUpper T := by
  filter_upwards
    [eventually_two_le_zeta_l,
     eventually_v17_article_hwL,
     eventually_v17_article_hsmall]
    with T hl2 hwL hsmall
  exact v17ArticleCompactError_margin_le_upper hl2 hwL hsmall

/-- The explicit v17 upper envelope tends to zero. -/
theorem tendsto_v17ArticleCompactUpper_zero :
    Tendsto v17ArticleCompactUpper atTop (𝓝 0) := by
  have hinv :
      Tendsto (fun T : ℝ => (Zeta23.l T)⁻¹) atTop (𝓝 0) :=
    tendsto_zeta_l_atTop.inv_tendsto_atTop
  have hinvSq :
      Tendsto (fun T : ℝ => ((Zeta23.l T)⁻¹) ^ 2) atTop (𝓝 0) := by
    simpa using hinv.pow 2
  have hfirst :
      Tendsto
        (fun T : ℝ =>
          (2 * v17ArticleRawTailConst / limitingK 0) *
            ((Zeta23.l T)⁻¹) ^ 2)
        atTop (𝓝 0) := by
    simpa using
      hinvSq.const_mul (2 * v17ArticleRawTailConst / limitingK 0)
  have hsecond :
      Tendsto
        (fun T : ℝ =>
          (20 * articleParams.w / limitingK 0) * (Zeta23.l T)⁻¹)
        atTop (𝓝 0) := by
    simpa using
      hinv.const_mul (20 * articleParams.w / limitingK 0)
  have hadd := hfirst.add hsecond
  change Tendsto (fun T : ℝ => v17ArticleCompactUpper T) atTop (𝓝 0)
  simpa only [v17ArticleCompactUpper, zero_add] using hadd

/-- The complete v17 quantitative compact-overlap error vanishes along the margin. -/
theorem tendsto_v17ArticleCompactError_margin_zero :
    Tendsto
      (fun T : ℝ => v17ArticleCompactError T (articleTailMargin T))
      atTop (𝓝 0) := by
  refine
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds
      tendsto_v17ArticleCompactUpper_zero
      ?_
      eventually_v17ArticleCompactError_margin_le_upper
  filter_upwards [eventually_two_le_zeta_l] with T hl2
  exact
    v17ArticleCompactError_nonneg
      (by linarith : 0 < Zeta23.l T)
      (articleTailMargin T)

end HurtadoZeta23