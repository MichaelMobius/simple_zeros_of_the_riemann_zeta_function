import HurtadoZeta23.OmittedTailReindex
import HurtadoZeta23.FiniteGridEndpointBridge
import Mathlib.Tactic

noncomputable section

namespace HurtadoZeta23

open Real Filter Topology
open scoped BigOperators

/-!
# Quantitative finite-grid tail bound

This combines:
* the exact full/finite lattice decomposition;
* exact reindexing of both omitted half-grids;
* `CriticalGridCentrality`;
* the `r^{-2}` Fourier decay, hence the p=4 product majorant.

The result is a literal, finite-T bound for the raw unnormalized overlap.
-/

/-- Generic quantitative two-sided p=4 bound for the actual `phiD` summand. -/
theorem intervalFiniteGridOverlap_error_le_p4
    {ϱ : ℝ → ℝ} {lam L w T τ τ' : ℝ}
    {kMin kMax : ℤ} {M : ℕ}
    (hϱ : Zeta23.TaperProfile ϱ)
    (h0 : 0 < lam) (h1 : lam ≤ 1)
    (hw : 1 ≤ w) (hwL : 8 * w ≤ L)
    (hkk : kMin ≤ kMax)
    (hM1 : 1 ≤ M)
    (hcτ :
      CriticalGridCentrality
        T (2 * Real.pi / L) kMin kMax M τ)
    (hcτ' :
      CriticalGridCentrality
        T (2 * Real.pi / L) kMin kMax M τ') :
    |intervalFiniteGridOverlap ϱ lam L w T τ τ' kMin kMax -
        fullGridOverlap ϱ lam L w τ τ'|
      ≤
    2 *
      ((((Zeta23.ThmD.cDT ϱ lam) / w) ^ 2 /
          (2 * Real.pi / L) ^ 4) *
        p4Tail M) := by

  let left :=
    leftOmittedPhiDSummand
      ϱ lam L w T (2 * Real.pi / L) τ τ' kMin M

  let right :=
    rightOmittedPhiDSummand
      ϱ lam L w T (2 * Real.pi / L) τ τ' kMax M

  let A : ℝ :=
    (((Zeta23.ThmD.cDT ϱ lam) / w) ^ 2 /
      (2 * Real.pi / L) ^ 4)

  have hleftU :
      UniformHalfTailMajorized left
        (((Zeta23.ThmD.cDT ϱ lam) / w) ^ 2)
        (2 * Real.pi / L) M := by
    dsimp [left]
    exact
      leftOmittedPhiD_majorized
        hϱ h0 h1 hw hwL hM1 hcτ hcτ'

  have hrightU :
      UniformHalfTailMajorized right
        (((Zeta23.ThmD.cDT ϱ lam) / w) ^ 2)
        (2 * Real.pi / L) M := by
    dsimp [right]
    exact
      rightOmittedPhiD_majorized
        hϱ h0 h1 hw hwL hM1 hcτ hcτ'

  have hleft :
      |shiftedTail left M| ≤ A * p4Tail M := by
    dsimp [A]
    exact
      abs_shiftedTail_le_p4Tail
        (shiftedP4Majorized_of_uniformHalfTail hleftU)

  have hright :
      |shiftedTail right M| ≤ A * p4Tail M := by
    dsimp [A]
    exact
      abs_shiftedTail_le_p4Tail
        (shiftedP4Majorized_of_uniformHalfTail hrightU)

  rw [
    intervalFiniteGridOverlap_error_eq_tails_proved
      hϱ h0 h1 hw hwL T τ τ' hkk,
    omittedPhiDTails_eq_twoSidedTail
      ϱ lam L w T τ τ' kMin kMax M
  ]

  calc
    |twoSidedTail left right M|
        ≤ |shiftedTail left M| + |shiftedTail right M| :=
      abs_twoSidedTail_le left right M
    _ ≤ A * p4Tail M + A * p4Tail M :=
      add_le_add hleft hright
    _ = 2 * (A * p4Tail M) := by ring
    _ = _ := by rfl

end HurtadoZeta23
