import HurtadoZeta23.P4Tail
import Mathlib.Tactic

noncomputable section

namespace HurtadoZeta23

open Real Filter Topology
open scoped BigOperators

/-- Convert the geometric `C/(step^4*n^4)` omitted-grid bound into the
`A * p4Majorant n` interface consumed by `P4Tail`. -/
theorem shiftedP4Majorized_of_uniformHalfTail
    {summand : ℕ → ℝ} {C step : ℝ} {M : ℕ}
    (h : UniformHalfTailMajorized summand C step M) :
    ShiftedP4Majorized summand (C / step ^ 4) M := by
  rcases h with ⟨hstep, hC, hpoint⟩
  refine ⟨div_nonneg hC (by positivity), ?_⟩
  intro k
  have hk := hpoint (k + M) (Nat.le_add_left M k)
  unfold p4Majorant
  calc
    |summand (k + M)|
        ≤ C / (step ^ 4 * (((k + M : ℕ) : ℝ) ^ 4)) := hk
    _ = (C / step ^ 4) * (1 / (((k + M : ℕ) : ℝ) ^ 4)) := by
          field_simp

/-- A two-sided omitted grid, represented by its left and right half-tail. -/
def twoSidedTail (left right : ℕ → ℝ) (M : ℕ) : ℝ :=
  shiftedTail left M + shiftedTail right M

/-- Triangle inequality for the two omitted half-grids. -/
theorem abs_twoSidedTail_le
    (left right : ℕ → ℝ) (M : ℕ) :
    |twoSidedTail left right M|
      ≤ |shiftedTail left M| + |shiftedTail right M| := by
  unfold twoSidedTail
  exact abs_add_le _ _

/-- If both omitted half-grids have the same p=4 prefactor, their total tail
is uniformly small for sufficiently large endpoint margin `M`. -/
theorem eventually_abs_twoSidedTail_lt
    {A eps : ℝ} (hA : 0 ≤ A) (heps : 0 < eps) :
    ∀ᶠ M : ℕ in atTop,
      ∀ left right : ℕ → ℝ,
        ShiftedP4Majorized left A M →
        ShiftedP4Majorized right A M →
        |twoSidedTail left right M| < eps := by
  have hhalf := eventually_abs_shiftedTail_lt hA (half_pos heps)
  filter_upwards [hhalf] with M hM
  intro left right hleft hright
  have hl := hM left hleft
  have hr := hM right hright
  have htri := abs_twoSidedTail_le left right M
  have hsum : |shiftedTail left M| + |shiftedTail right M| < eps := by
    linarith
  exact lt_of_le_of_lt htri hsum

/-- Zeta23/geometry version of the preceding theorem.  A common Fourier-decay
constant `C` and lattice step `step` yield the same p=4 prefactor on both
sides, hence a uniform two-sided truncation bound. -/
theorem eventually_abs_twoSidedTail_lt_of_geometry
    {C step eps : ℝ}
    (hC : 0 ≤ C) (hstep : 0 < step) (heps : 0 < eps) :
    ∀ᶠ M : ℕ in atTop,
      ∀ left right : ℕ → ℝ,
        UniformHalfTailMajorized left C step M →
        UniformHalfTailMajorized right C step M →
        |twoSidedTail left right M| < eps := by
  have hA : 0 ≤ C / step ^ 4 := div_nonneg hC (by positivity)
  have htail := eventually_abs_twoSidedTail_lt hA heps
  filter_upwards [htail] with M hM
  intro left right hleft hright
  exact hM left right
    (shiftedP4Majorized_of_uniformHalfTail hleft)
    (shiftedP4Majorized_of_uniformHalfTail hright)

/-- If an integer-valued margin function tends to infinity, the same uniform
p=4 argument makes the two-sided omitted grid tend to zero along the ambient
asymptotic parameter.  This is the form needed when the paper chooses an
endpoint margin of order `L^2`. -/
theorem twoSidedTail_vanishes_along_margin
    {α : Type*} [Preorder α]
    {l : Filter α} {margin : α → ℕ}
    (hmargin : Tendsto margin l atTop)
    {C step : ℝ} (hC : 0 ≤ C) (hstep : 0 < step)
    {left right : α → ℕ → ℝ}
    (hleft : ∀ᶠ a in l, UniformHalfTailMajorized (left a) C step (margin a))
    (hright : ∀ᶠ a in l, UniformHalfTailMajorized (right a) C step (margin a)) :
    Tendsto (fun a => twoSidedTail (left a) (right a) (margin a)) l (nhds 0) := by
  rw [Metric.tendsto_nhds]
  intro eps heps
  have hev := eventually_abs_twoSidedTail_lt_of_geometry hC hstep heps
  have hev' : ∀ᶠ a in l,
      ∀ L R : ℕ → ℝ,
        UniformHalfTailMajorized L C step (margin a) →
        UniformHalfTailMajorized R C step (margin a) →
        |twoSidedTail L R (margin a)| < eps := hmargin.eventually hev
  filter_upwards [hev', hleft, hright] with a ha hLa hRa
  simpa [Real.dist_eq] using ha (left a) (right a) hLa hRa

end HurtadoZeta23
