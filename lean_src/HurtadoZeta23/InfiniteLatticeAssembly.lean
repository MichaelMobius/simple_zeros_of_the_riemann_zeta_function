import HurtadoZeta23.IntegerLatticePartition
import HurtadoZeta23.TwoSidedGridTail
import Mathlib.Tactic

noncomputable section

namespace HurtadoZeta23

open Real Filter Topology
open scoped BigOperators

/-- Literal left omitted half-line, indexed from the closest omitted point. -/
def leftInfiniteTail (f : ℤ → ℝ) (kMin : ℤ) : ℝ :=
  ∑' j : ℕ, f (kMin - 1 - Int.ofNat j)

/-- Literal right omitted half-line, indexed from the closest omitted point. -/
def rightInfiniteTail (f : ℤ → ℝ) (kMax : ℤ) : ℝ :=
  ∑' j : ℕ, f (kMax + 1 + Int.ofNat j)

/-- The retained finite contribution. -/
def middleFiniteSum (f : ℤ → ℝ) (kMin kMax : ℤ) : ℝ :=
  Finset.sum (retainedIndexSet kMin kMax) f

/-- Exact decomposition, rewritten with named left/middle/right pieces. -/
def ExactThreeWayTsumDecomposition
    (f : ℤ → ℝ) (kMin kMax : ℤ) : Prop :=
  (∑' k : ℤ, f k) =
    leftInfiniteTail f kMin +
      middleFiniteSum f kMin kMax +
      rightInfiniteTail f kMax

/-- The named three-way decomposition is exactly the literal decomposition
introduced in `IntegerLatticePartition`. -/
lemma exactThreeWay_iff_exactInfinite
    (f : ℤ → ℝ) (kMin kMax : ℤ) :
    ExactThreeWayTsumDecomposition f kMin kMax ↔
      ExactInfiniteLatticeDecomposition f kMin kMax := by
  simp only [
    ExactThreeWayTsumDecomposition,
    ExactInfiniteLatticeDecomposition,
    leftInfiniteTail,
    middleFiniteSum,
    rightInfiniteTail
  ]

/-- Once the exact integer-lattice reindexing is known, the finite retained
sum is the full sum minus the two omitted half-lines. -/
theorem middle_eq_full_sub_tails
    {f : ℤ → ℝ} {kMin kMax : ℤ}
    (h : ExactThreeWayTsumDecomposition f kMin kMax) :
    middleFiniteSum f kMin kMax =
      (∑' k : ℤ, f k) -
        (leftInfiniteTail f kMin + rightInfiniteTail f kMax) := by
  unfold ExactThreeWayTsumDecomposition at h
  linarith

/-- Consequently the absolute truncation error is exactly the absolute value
of the combined omitted tails. -/
theorem abs_middle_sub_full_eq_abs_tails
    {f : ℤ → ℝ} {kMin kMax : ℤ}
    (h : ExactThreeWayTsumDecomposition f kMin kMax) :
    |middleFiniteSum f kMin kMax - (∑' k : ℤ, f k)| =
      |leftInfiniteTail f kMin + rightInfiniteTail f kMax| := by
  rw [middle_eq_full_sub_tails h]
  have hinside :
      ((∑' k : ℤ, f k) -
          (leftInfiniteTail f kMin + rightInfiniteTail f kMax)) -
          (∑' k : ℤ, f k)
        =
      -(leftInfiniteTail f kMin + rightInfiniteTail f kMax) := by
    ring
  rw [hinside, abs_neg]

/-- The preceding identity specialized to the actual Montgomery--Taylor
critical-lattice summand. -/
theorem intervalFiniteGridOverlap_sub_tsum_eq_tails
    {ϱ : ℝ → ℝ} {lam L w T τ τ' : ℝ} {kMin kMax : ℤ}
    (hdec : ExactThreeWayTsumDecomposition
      (phiDGridSummand ϱ lam L w T τ τ') kMin kMax) :
    |intervalFiniteGridOverlap ϱ lam L w T τ τ' kMin kMax -
        (∑' k : ℤ, phiDGridSummand ϱ lam L w T τ τ' k)| =
      |leftInfiniteTail (phiDGridSummand ϱ lam L w T τ τ') kMin +
        rightInfiniteTail (phiDGridSummand ϱ lam L w T τ τ') kMax| := by
  simpa [intervalFiniteGridOverlap, middleFiniteSum] using
    (abs_middle_sub_full_eq_abs_tails (h := hdec))

/-- Zeta23 identifies the full lattice `tsum` with the Poisson overlap. -/
theorem tsum_phiD_eq_fullGridOverlap
    {ϱ : ℝ → ℝ} {lam L w : ℝ}
    (hϱ : Zeta23.TaperProfile ϱ)
    (h0 : 0 < lam) (h1 : lam ≤ 1)
    (hw : 1 ≤ w) (hwL : 8 * w ≤ L)
    (T τ τ' : ℝ) :
    (∑' k : ℤ, phiDGridSummand ϱ lam L w T τ τ' k) =
      fullGridOverlap ϱ lam L w τ τ' := by
  exact (hasSum_phiD_full_grid hϱ h0 h1 hw hwL T τ τ').tsum_eq

/-- Exact finite-vs-full error identity, conditional only on the exact
integer-lattice decomposition. -/
theorem intervalFiniteGridOverlap_error_eq_tails
    {ϱ : ℝ → ℝ} {lam L w : ℝ}
    (hϱ : Zeta23.TaperProfile ϱ)
    (h0 : 0 < lam) (h1 : lam ≤ 1)
    (hw : 1 ≤ w) (hwL : 8 * w ≤ L)
    (T τ τ' : ℝ) {kMin kMax : ℤ}
    (hdec : ExactThreeWayTsumDecomposition
      (phiDGridSummand ϱ lam L w T τ τ') kMin kMax) :
    |intervalFiniteGridOverlap ϱ lam L w T τ τ' kMin kMax -
        fullGridOverlap ϱ lam L w τ τ'| =
      |leftInfiniteTail (phiDGridSummand ϱ lam L w T τ τ') kMin +
        rightInfiniteTail (phiDGridSummand ϱ lam L w T τ τ') kMax| := by
  rw [← tsum_phiD_eq_fullGridOverlap hϱ h0 h1 hw hwL T τ τ']
  exact intervalFiniteGridOverlap_sub_tsum_eq_tails hdec

/-- Any bound on the two omitted half-lines is automatically a bound on the
actual finite-grid truncation error. -/
theorem intervalFiniteGridOverlap_error_le_of_tails
    {ϱ : ℝ → ℝ} {lam L w : ℝ}
    (hϱ : Zeta23.TaperProfile ϱ)
    (h0 : 0 < lam) (h1 : lam ≤ 1)
    (hw : 1 ≤ w) (hwL : 8 * w ≤ L)
    (T τ τ' : ℝ) {kMin kMax : ℤ} {eps : ℝ}
    (hdec : ExactThreeWayTsumDecomposition
      (phiDGridSummand ϱ lam L w T τ τ') kMin kMax)
    (htail :
      |leftInfiniteTail (phiDGridSummand ϱ lam L w T τ τ') kMin +
        rightInfiniteTail (phiDGridSummand ϱ lam L w T τ τ') kMax| ≤ eps) :
    |intervalFiniteGridOverlap ϱ lam L w T τ τ' kMin kMax -
        fullGridOverlap ϱ lam L w τ τ'| ≤ eps := by
  rw [intervalFiniteGridOverlap_error_eq_tails
    hϱ h0 h1 hw hwL T τ τ' hdec]
  exact htail

end HurtadoZeta23
