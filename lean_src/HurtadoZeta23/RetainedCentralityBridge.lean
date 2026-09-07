import HurtadoZeta23.ConcreteCompactOverlapAssembly
import HurtadoZeta23.CriticalLatticeGeometry
import HurtadoZeta23.RetainedSpanBridge
import Mathlib.Tactic

noncomputable section

open Matrix Finset
open scoped BigOperators ComplexOrder

namespace HurtadoZeta23

/-!
# Retained centrality bridge

The retained set was defined by deleting ordinary-ordinate boundary strips of
width

  `interiorBoundaryWidth T = 2π * l(T)`.

For the critical step

  `h = 2π / l(T)`,

this width is exactly `h * l(T)^2`.  Hence every retained zero, and therefore
every zero appearing in a consecutive retained block, is at least `l(T)^2`
critical-lattice cells from both continuous endpoints `T` and `2T`.

This file isolates that exact geometric fact.  The remaining discrete seam is
only the rounding from the continuous endpoints to the integer grid endpoints
`kMin` and `kMax`.
-/

/-- Critical-lattice step used by the article. -/
def articleCriticalStep (T : ℝ) : ℝ :=
  2 * Real.pi / Zeta23.l T

/-- The critical step is positive whenever `l(T)` is positive. -/
theorem articleCriticalStep_pos
    {T : ℝ}
    (hl : 0 < Zeta23.l T) :
    0 < articleCriticalStep T := by
  unfold articleCriticalStep
  positivity

/--
Exact conversion between `l(T)^2` grid cells and the ordinary-ordinate
boundary width.
-/
theorem articleCriticalStep_mul_l_sq
    {T : ℝ}
    (hl : 0 < Zeta23.l T) :
    articleCriticalStep T * (Zeta23.l T) ^ 2
      =
    interiorBoundaryWidth T := by

  unfold articleCriticalStep

  exact
    grid_L2_width_eq_interiorBoundaryWidth
      (ne_of_gt hl)

/-- Every ordered retained zero lies in the literal central ordinate band. -/
theorem orderedRetainedZero_im_central
    (T : ℝ)
    (i : Fin (articleRetainedCard T)) :
    T + interiorBoundaryWidth T
        ≤ (orderedRetainedZero T i).im
      ∧
    (orderedRetainedZero T i).im
        ≤ 2 * T - interiorBoundaryWidth T := by

  have hmem :=
    orderedRetainedZero_mem_retained T i

  have hband :
      orderedRetainedZero T i
        ∈ retainedOrdinateBand T :=
    hmem.2

  simpa [retainedOrdinateBand] using hband

/-- Every zero in every actual consecutive retained block is central. -/
theorem consecutiveZero_im_central
    (T : ℝ)
    (s : ℕ)
    (hs : s + blockLength ≤ articleRetainedCard T)
    (i : Fin blockLength) :
    T + interiorBoundaryWidth T
        ≤ (consecutiveZero T s hs i).im
      ∧
    (consecutiveZero T s hs i).im
        ≤ 2 * T - interiorBoundaryWidth T := by

  rw [consecutiveZero_eq_ordered]

  exact
    orderedRetainedZero_im_central
      T
      (consecutiveRetainedRank T s hs i)

/--
A retained block point is at least `l(T)^2` continuous critical-grid cells
to the right of the left endpoint `T`.
-/
theorem consecutiveZero_left_L2_margin
    {T : ℝ}
    (hl : 0 < Zeta23.l T)
    (s : ℕ)
    (hs : s + blockLength ≤ articleRetainedCard T)
    (i : Fin blockLength) :
    articleCriticalStep T * (Zeta23.l T) ^ 2
      ≤
    (consecutiveZero T s hs i).im - T := by

  have hc :=
    (consecutiveZero_im_central T s hs i).1

  rw [articleCriticalStep_mul_l_sq hl]

  linarith

/--
A retained block point is at least `l(T)^2` continuous critical-grid cells
to the left of the right endpoint `2T`.
-/
theorem consecutiveZero_right_L2_margin
    {T : ℝ}
    (hl : 0 < Zeta23.l T)
    (s : ℕ)
    (hs : s + blockLength ≤ articleRetainedCard T)
    (i : Fin blockLength) :
    articleCriticalStep T * (Zeta23.l T) ^ 2
      ≤
    2 * T - (consecutiveZero T s hs i).im := by

  have hc :=
    (consecutiveZero_im_central T s hs i).2

  rw [articleCriticalStep_mul_l_sq hl]

  linarith

/--
The two continuous endpoint margins packaged together.
-/
theorem consecutiveZero_L2_cell_margins
    {T : ℝ}
    (hl : 0 < Zeta23.l T)
    (s : ℕ)
    (hs : s + blockLength ≤ articleRetainedCard T)
    (i : Fin blockLength) :
    articleCriticalStep T * (Zeta23.l T) ^ 2
        ≤ (consecutiveZero T s hs i).im - T
      ∧
    articleCriticalStep T * (Zeta23.l T) ^ 2
        ≤ 2 * T - (consecutiveZero T s hs i).im := by

  exact
    ⟨consecutiveZero_left_L2_margin hl s hs i,
     consecutiveZero_right_L2_margin hl s hs i⟩

end HurtadoZeta23
