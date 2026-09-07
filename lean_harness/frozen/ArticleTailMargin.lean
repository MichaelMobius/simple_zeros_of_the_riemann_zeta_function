import HurtadoZeta23.P4TailRate
import HurtadoZeta23.InteriorBoundaryBridge
import Mathlib.Tactic

noncomputable section

open Filter Asymptotics Topology

namespace HurtadoZeta23

/-!
# Article endpoint margin

For the asymptotic Input-IV closure we choose

  M(T) = floor(l(T)^2 / 2).

This is deliberately a little smaller than the full retained `l(T)^2` strip.
It gives a clean two-cell endpoint cushion and, at the same time, remains
comparable with `l(T)^2`.
-/

/-- Integer endpoint margin used in the final compact-overlap estimate. -/
def articleTailMargin (T : ℝ) : ℕ :=
  ⌊(Zeta23.l T) ^ 2 / 2⌋₊

/-- The floor margin is at most half the square logarithmic scale. -/
theorem articleTailMargin_le_half_sq
    {T : ℝ}
    (hl0 : 0 ≤ Zeta23.l T) :
    (articleTailMargin T : ℝ)
      ≤
    (Zeta23.l T) ^ 2 / 2 := by

  unfold articleTailMargin

  have hx0 :
      0 ≤ (Zeta23.l T) ^ 2 / 2 := by
    positivity

  exact Nat.floor_le hx0

/--
Once `l(T) >= 2`, the floor margin still contains at least one quarter of
`l(T)^2`.
-/
theorem quarter_sq_le_articleTailMargin
    {T : ℝ}
    (hl2 : 2 ≤ Zeta23.l T) :
    (Zeta23.l T) ^ 2 / 4
      ≤
    (articleTailMargin T : ℝ) := by

  let x : ℝ :=
    (Zeta23.l T) ^ 2 / 2

  have hx2 :
      2 ≤ x := by
    dsimp [x]
    nlinarith [sq_nonneg (Zeta23.l T - 2)]

  have hfloor :
      x < (articleTailMargin T : ℝ) + 1 := by
    dsimp [articleTailMargin, x]
    exact Nat.lt_floor_add_one _

  have hxhalf :
      (Zeta23.l T) ^ 2 / 4 = x / 2 := by
    dsimp [x]
    ring

  rw [hxhalf]

  linarith

/-- The chosen margin is nonzero, indeed at least one, for `l(T) >= 2`. -/
theorem one_le_articleTailMargin
    {T : ℝ}
    (hl2 : 2 ≤ Zeta23.l T) :
    1 ≤ articleTailMargin T := by

  have hq :
      (Zeta23.l T) ^ 2 / 4
        ≤
      (articleTailMargin T : ℝ) :=
    quarter_sq_le_articleTailMargin hl2

  have hq1 :
      (1 : ℝ) ≤ (Zeta23.l T) ^ 2 / 4 := by
    nlinarith [sq_nonneg (Zeta23.l T - 2)]

  have hreal :
      (1 : ℝ) ≤ (articleTailMargin T : ℝ) :=
    hq1.trans hq

  exact_mod_cast hreal

/--
The conservative two-cell endpoint condition required by the discrete
centrality bridge.
-/
theorem articleTailMargin_add_two_le_sq
    {T : ℝ}
    (hl2 : 2 ≤ Zeta23.l T) :
    (articleTailMargin T : ℝ) + 2
      ≤
    (Zeta23.l T) ^ 2 := by

  have hl0 :
      0 ≤ Zeta23.l T := by
    linarith

  have hupper :=
    articleTailMargin_le_half_sq hl0

  have hsq4 :
      4 ≤ (Zeta23.l T) ^ 2 := by
    nlinarith [sq_nonneg (Zeta23.l T - 2)]

  nlinarith

/-- Eventually `l(T) >= 2`. -/
theorem eventually_two_le_zeta_l :
    ∀ᶠ T : ℝ in atTop,
      (2 : ℝ) ≤ Zeta23.l T :=
  tendsto_zeta_l_atTop.eventually_ge_atTop 2

/-- Eventually the margin is at least one. -/
theorem eventually_one_le_articleTailMargin :
    ∀ᶠ T : ℝ in atTop,
      1 ≤ articleTailMargin T := by

  filter_upwards [eventually_two_le_zeta_l] with T hl2

  exact one_le_articleTailMargin hl2

/-- Eventually the two-cell endpoint condition holds. -/
theorem eventually_articleTailMargin_add_two_le_sq :
    ∀ᶠ T : ℝ in atTop,
      (articleTailMargin T : ℝ) + 2
        ≤
      (Zeta23.l T) ^ 2 := by

  filter_upwards [eventually_two_le_zeta_l] with T hl2

  exact articleTailMargin_add_two_le_sq hl2

/-- Eventually the margin is quantitatively comparable to `l(T)^2`. -/
theorem eventually_quarter_sq_le_articleTailMargin :
    ∀ᶠ T : ℝ in atTop,
      (Zeta23.l T) ^ 2 / 4
        ≤
      (articleTailMargin T : ℝ) := by

  filter_upwards [eventually_two_le_zeta_l] with T hl2

  exact quarter_sq_le_articleTailMargin hl2

end HurtadoZeta23
