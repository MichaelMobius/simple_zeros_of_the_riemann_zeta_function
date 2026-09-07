import Mathlib.Tactic

noncomputable section

namespace HurtadoZeta23

/-- Algebraic closure of the two-matching argument.

`evenE` is the energy on `(0,1),(2,3),...,(448,449)`, `oddE` is the energy
on `(1,2),(3,4),...,(447,448)`, and `wrapE` is the extra rotated pair
`(449,0)`.  Once each matching costs at most one copy of the spectral defect,
the union of the 449 non-wrapping adjacent edges costs at most one copy. -/
theorem v17_two_matchings_close_adjacent_band
    {D evenE oddE wrapE bandE : ℝ}
    (heven : 2 * evenE ≤ D)
    (hrot : 2 * (oddE + wrapE) ≤ D)
    (hwrap : 0 ≤ wrapE)
    (hband : bandE = evenE + oddE) :
    bandE ≤ D := by
  rw [hband]
  linarith

end HurtadoZeta23
