import HurtadoZeta23.ArticleTailMargin
import Mathlib.Tactic

noncomputable section

open Real Filter Topology

namespace HurtadoZeta23

/-!
# Tail rate along the article margin

This file combines the two already-separated ingredients

* `p4Tail M ≤ p2ShiftSum / M^2`,
* `l(T)^2 / 4 ≤ articleTailMargin T`,

to eliminate the integer floor from the asymptotic analysis.
-/

/--
Along the chosen article margin,

`p4Tail (articleTailMargin T) ≤ 16 * p2ShiftSum / l(T)^4`

once `l(T) ≥ 2`.
-/
theorem p4Tail_articleTailMargin_le
    {T : ℝ}
    (hl2 : 2 ≤ Zeta23.l T) :
    p4Tail (articleTailMargin T)
      ≤
    16 * p2ShiftSum / (Zeta23.l T) ^ 4 := by

  have hM1 :
      1 ≤ articleTailMargin T :=
    one_le_articleTailMargin hl2

  have htail :
      p4Tail (articleTailMargin T)
        ≤
      p2ShiftSum /
        ((articleTailMargin T : ℝ) ^ 2) :=
    p4Tail_le_p2ShiftSum_div_sq hM1

  have hlpos :
      0 < Zeta23.l T := by
    linarith

  have hmargin :
      (Zeta23.l T) ^ 2 / 4
        ≤
      (articleTailMargin T : ℝ) :=
    quarter_sq_le_articleTailMargin hl2

  have hmargin0 :
      0 ≤ (articleTailMargin T : ℝ) := by
    positivity

  have hbase0 :
      0 ≤ (Zeta23.l T) ^ 2 / 4 := by
    positivity

  have hsquare :
      ((Zeta23.l T) ^ 2 / 4) ^ 2
        ≤
      (articleTailMargin T : ℝ) ^ 2 := by
    nlinarith [sq_nonneg
      ((articleTailMargin T : ℝ) -
        (Zeta23.l T) ^ 2 / 4)]

  have hden :
      (Zeta23.l T) ^ 4 / 16
        ≤
      (articleTailMargin T : ℝ) ^ 2 := by
    calc
      (Zeta23.l T) ^ 4 / 16
          =
        ((Zeta23.l T) ^ 2 / 4) ^ 2 := by
          ring
      _ ≤
        (articleTailMargin T : ℝ) ^ 2 :=
          hsquare

  have hdenpos :
      0 < (Zeta23.l T) ^ 4 / 16 := by
    positivity

  have hinv :
      1 / ((articleTailMargin T : ℝ) ^ 2)
        ≤
      16 / (Zeta23.l T) ^ 4 := by

    have h :=
      one_div_le_one_div_of_le
        hdenpos
        hden

    calc
      1 / ((articleTailMargin T : ℝ) ^ 2)
          ≤
        1 / ((Zeta23.l T) ^ 4 / 16) :=
          h
      _ =
        16 / (Zeta23.l T) ^ 4 := by
          field_simp

  have hsum0 :
      0 ≤ p2ShiftSum :=
    p2ShiftSum_nonneg

  have hscaled :
      p2ShiftSum /
          ((articleTailMargin T : ℝ) ^ 2)
        ≤
      p2ShiftSum *
          (16 / (Zeta23.l T) ^ 4) := by

    rw [div_eq_mul_inv]

    have hinv' :
        ((articleTailMargin T : ℝ) ^ 2)⁻¹
          ≤
        16 / (Zeta23.l T) ^ 4 := by
      simpa [one_div] using hinv

    exact
      mul_le_mul_of_nonneg_left
        hinv'
        hsum0

  calc
    p4Tail (articleTailMargin T)
        ≤
      p2ShiftSum /
        ((articleTailMargin T : ℝ) ^ 2) :=
      htail

    _ ≤
      p2ShiftSum *
        (16 / (Zeta23.l T) ^ 4) :=
      hscaled

    _ =
      16 * p2ShiftSum /
        (Zeta23.l T) ^ 4 := by
      ring

/-- Eventual form used by the compact-error asymptotics. -/
theorem eventually_p4Tail_articleTailMargin_le :
    ∀ᶠ T : ℝ in atTop,
      p4Tail (articleTailMargin T)
        ≤
      16 * p2ShiftSum / (Zeta23.l T) ^ 4 := by

  filter_upwards [eventually_two_le_zeta_l] with T hl2

  exact p4Tail_articleTailMargin_le hl2

end HurtadoZeta23
