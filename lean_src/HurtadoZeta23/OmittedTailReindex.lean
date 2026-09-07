import HurtadoZeta23.ExactTsumDecomposition
import HurtadoZeta23.CriticalLatticeGeometry
import HurtadoZeta23.P4Tail
import Mathlib.Tactic

noncomputable section

namespace HurtadoZeta23

open Real Filter Topology
open scoped BigOperators

/-!
# Exact reindexing of the omitted half-grids

`ExactTsumDecomposition` writes the two omitted parts as `leftInfiniteTail`
and `rightInfiniteTail`.  The p=4 machinery writes the same tails as
`shiftedTail` starting at a natural margin `M`.

This file proves that these are literally the same sums for the critical
lattice.  No estimate is used here.
-/

/-- The literal left omitted integer tail is exactly the shifted natural tail. -/
theorem leftInfiniteTail_phiD_eq_shiftedTail
    (ϱ : ℝ → ℝ) (lam L w T τ τ' : ℝ)
    (kMin : ℤ) (M : ℕ) :
    leftInfiniteTail
        (phiDGridSummand ϱ lam L w T τ τ')
        kMin
      =
    shiftedTail
      (leftOmittedPhiDSummand
        ϱ lam L w T (2 * Real.pi / L) τ τ' kMin M)
      M := by
  unfold leftInfiniteTail shiftedTail
  apply tsum_congr
  intro k
  simp [
    phiDGridSummand,
    leftOmittedPhiDSummand,
    leftOmittedIndex,
    criticalGridPoint
  ]

/-- The literal right omitted integer tail is exactly the shifted natural tail. -/
theorem rightInfiniteTail_phiD_eq_shiftedTail
    (ϱ : ℝ → ℝ) (lam L w T τ τ' : ℝ)
    (kMax : ℤ) (M : ℕ) :
    rightInfiniteTail
        (phiDGridSummand ϱ lam L w T τ τ')
        kMax
      =
    shiftedTail
      (rightOmittedPhiDSummand
        ϱ lam L w T (2 * Real.pi / L) τ τ' kMax M)
      M := by
  unfold rightInfiniteTail shiftedTail
  apply tsum_congr
  intro k
  simp [
    phiDGridSummand,
    rightOmittedPhiDSummand,
    rightOmittedIndex,
    criticalGridPoint
  ]

/-- Two omitted tails, after the exact reindexing, are precisely `twoSidedTail`. -/
theorem omittedPhiDTails_eq_twoSidedTail
    (ϱ : ℝ → ℝ) (lam L w T τ τ' : ℝ)
    (kMin kMax : ℤ) (M : ℕ) :
    leftInfiniteTail
        (phiDGridSummand ϱ lam L w T τ τ')
        kMin
      +
    rightInfiniteTail
        (phiDGridSummand ϱ lam L w T τ τ')
        kMax
      =
    twoSidedTail
      (leftOmittedPhiDSummand
        ϱ lam L w T (2 * Real.pi / L) τ τ' kMin M)
      (rightOmittedPhiDSummand
        ϱ lam L w T (2 * Real.pi / L) τ τ' kMax M)
      M := by
  rw [
    leftInfiniteTail_phiD_eq_shiftedTail,
    rightInfiniteTail_phiD_eq_shiftedTail
  ]
  rfl

end HurtadoZeta23
