import HurtadoZeta23.ArticleRawTailUniform
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic

noncomputable section

open Real Filter Asymptotics Topology

namespace HurtadoZeta23

/-!
# Vanishing of the quantitative compact-overlap error

Along the article margin, the raw finite-grid tail is uniformly bounded.
The normalization contributes an additional `l(T)^2` in the denominator,
while the window approximation contributes only `O(1/l(T))`.

Hence the complete quantitative Input-IV error tends to zero.
-/

/-- A simple explicit upper envelope for the compact-overlap error. -/
def articleCompactUpper (T : ℝ) : ℝ :=
  (2 * articleRawTailConst / limitingK 0) *
      ((Zeta23.l T)⁻¹) ^ 2
    +
  (20 * articleParams.w / limitingK 0) *
      (Zeta23.l T)⁻¹

theorem articleCompactUpper_nonneg
    {T : ℝ}
    (hl : 0 < Zeta23.l T) :
    0 ≤ articleCompactUpper T := by

  have hK :
      0 < limitingK 0 :=
    limitingK_zero_pos

  have hw :
      0 < articleParams.w := by
    linarith [articleParams_valid.one_le_w]

  have hC :
      0 ≤ articleRawTailConst :=
    articleRawTailConst_nonneg

  unfold articleCompactUpper
  positivity

/--
Pointwise envelope once the standard large-`T` window conditions hold.
-/
theorem articleCompactError_margin_le_upper
    {T : ℝ}
    (hl2 : 2 ≤ Zeta23.l T)
    (hwL :
      8 * articleParams.w ≤ articleParams.L T)
    (hsmall :
      4 * articleParams.w / articleParams.L T
        ≤ limitingK 0 / 2) :
    articleCompactError T (articleTailMargin T)
      ≤
    articleCompactUpper T := by

  have hlpos :
      0 < Zeta23.l T := by
    linarith

  have hLpos :
      0 < articleParams.L T := by
    simpa [articleParams_L_eq_zeta_l] using hlpos

  have hK :
      0 < limitingK 0 :=
    limitingK_zero_pos

  have hKhalf :
      0 < limitingK 0 / 2 := by
    positivity

  have hmeanLower :
      limitingK 0 / 2
        ≤
      |phiDMean
          articleParams.ϱ
          1
          (articleParams.L T)
          articleParams.w| :=
    phiDMean_abs_lower
      articleParams_valid.taper
      articleParams_valid.one_le_w
      hwL
      hsmall

  have hmeanPos :
      0 <
      |phiDMean
          articleParams.ϱ
          1
          (articleParams.L T)
          articleParams.w| :=
    lt_of_lt_of_le hKhalf hmeanLower

  have hdenPos :
      0 <
        |phiDMean
            articleParams.ϱ
            1
            (articleParams.L T)
            articleParams.w| *
          (articleParams.L T) ^ 2 := by
    positivity

  have hLsq :
      (articleParams.L T) ^ 2
        =
      (Zeta23.l T) ^ 2 := by
    rw [articleParams_L_eq_zeta_l]

  have hdenLower :
      (limitingK 0 / 2) * (Zeta23.l T) ^ 2
        ≤
      |phiDMean
          articleParams.ϱ
          1
          (articleParams.L T)
          articleParams.w| *
        (articleParams.L T) ^ 2 := by

    calc
      (limitingK 0 / 2) * (Zeta23.l T) ^ 2
          =
        (limitingK 0 / 2) * (articleParams.L T) ^ 2 := by
          rw [hLsq]
      _ ≤
        |phiDMean
            articleParams.ϱ
            1
            (articleParams.L T)
            articleParams.w| *
          (articleParams.L T) ^ 2 := by
            exact
              mul_le_mul_of_nonneg_right
                hmeanLower
                (sq_nonneg _)

  have hrawLe :
      articleRawTailBound
          T
          (articleTailMargin T)
        ≤
      articleRawTailConst :=
    articleRawTailBound_margin_le_const hl2

  have hfirstA :
      articleRawTailBound T (articleTailMargin T) /
          (|phiDMean
              articleParams.ϱ
              1
              (articleParams.L T)
              articleParams.w| *
            (articleParams.L T) ^ 2)
        ≤
      articleRawTailConst /
          (|phiDMean
              articleParams.ϱ
              1
              (articleParams.L T)
              articleParams.w| *
            (articleParams.L T) ^ 2) := by

    exact
      div_le_div_of_nonneg_right
        hrawLe
        (le_of_lt hdenPos)

  have hlowerDenPos :
      0 <
        (limitingK 0 / 2) *
          (Zeta23.l T) ^ 2 := by
    positivity

  have hfirstB :
      articleRawTailConst /
          (|phiDMean
              articleParams.ϱ
              1
              (articleParams.L T)
              articleParams.w| *
            (articleParams.L T) ^ 2)
        ≤
      articleRawTailConst /
          ((limitingK 0 / 2) *
            (Zeta23.l T) ^ 2) := by

    exact
      div_le_div_of_nonneg_left
        articleRawTailConst_nonneg
        hlowerDenPos
        hdenLower

  have hfirst :
      articleRawTailBound T (articleTailMargin T) /
          (|phiDMean
              articleParams.ϱ
              1
              (articleParams.L T)
              articleParams.w| *
            (articleParams.L T) ^ 2)
        ≤
      (2 * articleRawTailConst / limitingK 0) *
        ((Zeta23.l T)⁻¹) ^ 2 := by

    calc
      articleRawTailBound T (articleTailMargin T) /
          (|phiDMean
              articleParams.ϱ
              1
              (articleParams.L T)
              articleParams.w| *
            (articleParams.L T) ^ 2)
          ≤
        articleRawTailConst /
          (|phiDMean
              articleParams.ϱ
              1
              (articleParams.L T)
              articleParams.w| *
            (articleParams.L T) ^ 2) :=
        hfirstA

      _ ≤
        articleRawTailConst /
          ((limitingK 0 / 2) *
            (Zeta23.l T) ^ 2) :=
        hfirstB

      _ =
        (2 * articleRawTailConst / limitingK 0) *
          ((Zeta23.l T)⁻¹) ^ 2 := by

        field_simp [
          ne_of_gt hK,
          ne_of_gt hlpos
        ]

  have hsecond :
      20 *
          (articleParams.w / articleParams.L T) /
          limitingK 0
        =
      (20 * articleParams.w / limitingK 0) *
        (Zeta23.l T)⁻¹ := by

    rw [articleParams_L_eq_zeta_l]

    field_simp [
      ne_of_gt hK,
      ne_of_gt hlpos
    ]

  unfold articleCompactError
  unfold articleCompactUpper

  rw [hsecond]

  exact add_le_add_left hfirst _

/-- Eventually the window-size condition `8w ≤ L(T)` holds. -/
theorem eventually_article_hwL :
    ∀ᶠ T : ℝ in atTop,
      8 * articleParams.w ≤ articleParams.L T := by

  have h :=
    tendsto_zeta_l_atTop.eventually_ge_atTop
      (8 * articleParams.w)

  simpa [articleParams_L_eq_zeta_l] using h

/--
Eventually the small-window condition used by `phiDMean_abs_lower` holds.
-/
theorem eventually_article_hsmall :
    ∀ᶠ T : ℝ in atTop,
      4 * articleParams.w / articleParams.L T
        ≤ limitingK 0 / 2 := by

  have hK :
      0 < limitingK 0 :=
    limitingK_zero_pos

  have hlarge :=
    tendsto_zeta_l_atTop.eventually_ge_atTop
      (8 * articleParams.w / limitingK 0)

  filter_upwards
    [hlarge, eventually_two_le_zeta_l]
    with T hT hl2

  have hlpos :
      0 < Zeta23.l T := by
    linarith

  have hmul :
      8 * articleParams.w
        ≤
      Zeta23.l T * limitingK 0 := by

    exact
      (div_le_iff₀ hK).mp hT

  rw [articleParams_L_eq_zeta_l]

  apply (div_le_iff₀ hlpos).2

  nlinarith

/-- Eventual pointwise upper envelope. -/
theorem eventually_articleCompactError_margin_le_upper :
    ∀ᶠ T : ℝ in atTop,
      articleCompactError T (articleTailMargin T)
        ≤
      articleCompactUpper T := by

  filter_upwards
    [eventually_two_le_zeta_l,
     eventually_article_hwL,
     eventually_article_hsmall]
    with T hl2 hwL hsmall

  exact
    articleCompactError_margin_le_upper
      hl2 hwL hsmall

/-- The explicit upper envelope tends to zero. -/
theorem tendsto_articleCompactUpper_zero :
    Tendsto articleCompactUpper atTop (𝓝 0) := by

  have hinv :
      Tendsto
        (fun T : ℝ => (Zeta23.l T)⁻¹)
        atTop
        (𝓝 0) :=
    tendsto_zeta_l_atTop.inv_tendsto_atTop

  have hinvSq :
      Tendsto
        (fun T : ℝ =>
          ((Zeta23.l T)⁻¹) ^ 2)
        atTop
        (𝓝 0) := by
    simpa using hinv.pow 2

  have hfirst :
      Tendsto
        (fun T : ℝ =>
          (2 * articleRawTailConst / limitingK 0) *
            ((Zeta23.l T)⁻¹) ^ 2)
        atTop
        (𝓝 0) := by

    simpa using
      hinvSq.const_mul
        (2 * articleRawTailConst / limitingK 0)

  have hsecond :
      Tendsto
        (fun T : ℝ =>
          (20 * articleParams.w / limitingK 0) *
            (Zeta23.l T)⁻¹)
        atTop
        (𝓝 0) := by

    simpa using
      hinv.const_mul
        (20 * articleParams.w / limitingK 0)

  have hadd :=
    hfirst.add hsecond

  change
    Tendsto
      (fun T : ℝ => articleCompactUpper T)
      atTop
      (𝓝 0)

  simpa only [articleCompactUpper, zero_add] using hadd

/--
The complete quantitative compact-overlap error vanishes along the chosen
article margin.
-/
theorem tendsto_articleCompactError_margin_zero :
    Tendsto
      (fun T : ℝ =>
        articleCompactError T (articleTailMargin T))
      atTop
      (𝓝 0) := by

  refine
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds
      tendsto_articleCompactUpper_zero
      ?_
      eventually_articleCompactError_margin_le_upper

  filter_upwards [eventually_two_le_zeta_l] with T hl2

  exact
    articleCompactError_nonneg
      (by linarith : 0 < Zeta23.l T)
      (articleTailMargin T)

end HurtadoZeta23