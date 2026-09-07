import HurtadoZeta23.IntegerHalfLineEquiv
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Tactic

noncomputable section

namespace HurtadoZeta23

open Real Filter Topology
open scoped BigOperators

/-- Indicator pieces of the three-way partition of `ℤ`. -/
def leftIndicator (f : ℤ → ℝ) (kMin : ℤ) : ℤ → ℝ :=
  fun k => if k < kMin then f k else 0

def middleIndicator (f : ℤ → ℝ) (kMin kMax : ℤ) : ℤ → ℝ :=
  fun k => if kMin ≤ k ∧ k ≤ kMax then f k else 0

def rightIndicator (f : ℤ → ℝ) (kMax : ℤ) : ℤ → ℝ :=
  fun k => if kMax < k then f k else 0

/-- The left `if`-indicator is exactly the set indicator of `Iio kMin`. -/
lemma leftIndicator_eq_setIndicator
    (f : ℤ → ℝ) (kMin : ℤ) :
    leftIndicator f kMin = (Set.Iio kMin).indicator f := by
  funext k
  by_cases hk : k < kMin
  · simp [leftIndicator, hk]
  · simp [leftIndicator, hk]

/-- The middle `if`-indicator is exactly the set indicator of
`Icc kMin kMax`. -/
lemma middleIndicator_eq_setIndicator
    (f : ℤ → ℝ) (kMin kMax : ℤ) :
    middleIndicator f kMin kMax = (Set.Icc kMin kMax).indicator f := by
  funext k
  by_cases hk : kMin ≤ k ∧ k ≤ kMax
  · simp [middleIndicator, hk]
  · simp [middleIndicator, hk]

/-- The right `if`-indicator is exactly the set indicator of `Ioi kMax`. -/
lemma rightIndicator_eq_setIndicator
    (f : ℤ → ℝ) (kMax : ℤ) :
    rightIndicator f kMax = (Set.Ioi kMax).indicator f := by
  funext k
  by_cases hk : kMax < k
  · simp [rightIndicator, hk]
  · simp [rightIndicator, hk]

lemma function_three_way_partition
    (f : ℤ → ℝ) {kMin kMax : ℤ} (hkk : kMin ≤ kMax) :
    f = fun k => leftIndicator f kMin k +
      middleIndicator f kMin kMax k + rightIndicator f kMax k := by
  funext k
  exact summand_region_decomposition hkk f


/-- Identity equivalence between our named left-half-line subtype and
Mathlib's `Set.Iio` subtype.  They have the same elements propositionally,
but are not definitionally the same type. -/
def leftHalfLineSetEquiv (kMin : ℤ) :
    leftHalfLine kMin ≃ Set.Iio kMin where
  toFun k := ⟨k.1, k.2⟩
  invFun k := ⟨k.1, k.2⟩
  left_inv := by intro k; rfl
  right_inv := by intro k; rfl

/-- Identity equivalence between our named right-half-line subtype and
Mathlib's `Set.Ioi` subtype. -/
def rightHalfLineSetEquiv (kMax : ℤ) :
    rightHalfLine kMax ≃ Set.Ioi kMax where
  toFun k := ⟨k.1, k.2⟩
  invFun k := ⟨k.1, k.2⟩
  left_inv := by intro k; rfl
  right_inv := by intro k; rfl

/-- The middle indicator tsum is exactly the retained finite sum. -/
theorem tsum_middleIndicator_eq_middleFiniteSum
    (f : ℤ → ℝ) {kMin kMax : ℤ} (_hkk : kMin ≤ kMax) :
    (∑' k : ℤ, middleIndicator f kMin kMax k) =
      middleFiniteSum f kMin kMax := by
  rw [middleIndicator_eq_setIndicator]
  have h :=
    (sum_eq_tsum_indicator f (retainedIndexSet kMin kMax)).symm
  simpa [middleFiniteSum, retainedIndexSet] using h

/-- The left indicator tsum is the literal left omitted tail. -/
theorem tsum_leftIndicator_eq_leftInfiniteTail
    (f : ℤ → ℝ) (kMin : ℤ) :
    (∑' k : ℤ, leftIndicator f kMin k) = leftInfiniteTail f kMin := by
  rw [leftIndicator_eq_setIndicator]
  calc
    (∑' k : ℤ, (Set.Iio kMin).indicator f k)
        = (∑' k : Set.Iio kMin, f k.1) :=
            (tsum_subtype (Set.Iio kMin) f).symm
    _ = (∑' k : leftHalfLine kMin, f k.1) := by
          rw [← Equiv.tsum_eq (leftHalfLineSetEquiv kMin)]
          apply tsum_congr
          intro c
          change f c.1 = f c.1
          rfl
    _ = leftInfiniteTail f kMin :=
      tsum_leftHalfLine_eq_leftInfiniteTail f kMin

/-- The right indicator tsum is the literal right omitted tail. -/
theorem tsum_rightIndicator_eq_rightInfiniteTail
    (f : ℤ → ℝ) (kMax : ℤ) :
    (∑' k : ℤ, rightIndicator f kMax k) = rightInfiniteTail f kMax := by
  rw [rightIndicator_eq_setIndicator]
  calc
    (∑' k : ℤ, (Set.Ioi kMax).indicator f k)
        = (∑' k : Set.Ioi kMax, f k.1) :=
            (tsum_subtype (Set.Ioi kMax) f).symm
    _ = (∑' k : rightHalfLine kMax, f k.1) := by
          rw [← Equiv.tsum_eq (rightHalfLineSetEquiv kMax)]
          apply tsum_congr
          intro c
          change f c.1 = f c.1
          rfl
    _ = rightInfiniteTail f kMax :=
      tsum_rightHalfLine_eq_rightInfiniteTail f kMax

/-- Exact decomposition of an unconditionally summable integer series into
left omitted tail, retained finite interval, and right omitted tail. -/
theorem exactThreeWayTsumDecomposition_of_summable
    {f : ℤ → ℝ} {kMin kMax : ℤ}
    (hkk : kMin ≤ kMax) (hf : Summable f) :
    ExactThreeWayTsumDecomposition f kMin kMax := by
  have hL : Summable (leftIndicator f kMin) := by
    rw [leftIndicator_eq_setIndicator]
    exact hf.indicator (Set.Iio kMin)

  have hM : Summable (middleIndicator f kMin kMax) := by
    rw [middleIndicator_eq_setIndicator]
    exact hf.indicator (Set.Icc kMin kMax)

  have hR : Summable (rightIndicator f kMax) := by
    rw [rightIndicator_eq_setIndicator]
    exact hf.indicator (Set.Ioi kMax)

  have hsum :
      (∑' k : ℤ, f k) =
        (∑' k : ℤ,
          ((leftIndicator f kMin k +
            middleIndicator f kMin kMax k) +
            rightIndicator f kMax k)) := by
    apply tsum_congr
    intro k
    exact summand_region_decomposition hkk f

  have hsplit :
      (∑' k : ℤ,
        ((leftIndicator f kMin k +
          middleIndicator f kMin kMax k) +
          rightIndicator f kMax k)) =
        (∑' k : ℤ, leftIndicator f kMin k) +
        (∑' k : ℤ, middleIndicator f kMin kMax k) +
        (∑' k : ℤ, rightIndicator f kMax k) := by
    rw [(hL.add hM).tsum_add hR]
    rw [hL.tsum_add hM]

  unfold ExactThreeWayTsumDecomposition
  calc
    (∑' k : ℤ, f k)
        =
      (∑' k : ℤ,
        ((leftIndicator f kMin k +
          middleIndicator f kMin kMax k) +
          rightIndicator f kMax k)) := hsum
    _ =
      (∑' k : ℤ, leftIndicator f kMin k) +
      (∑' k : ℤ, middleIndicator f kMin kMax k) +
      (∑' k : ℤ, rightIndicator f kMax k) := hsplit
    _ =
      leftInfiniteTail f kMin +
      middleFiniteSum f kMin kMax +
      rightInfiniteTail f kMax := by
        rw [tsum_leftIndicator_eq_leftInfiniteTail]
        rw [tsum_middleIndicator_eq_middleFiniteSum f hkk]
        rw [tsum_rightIndicator_eq_rightInfiniteTail]

/-- For the actual Montgomery--Taylor grid summand, Zeta23's `HasSum` theorem
supplies summability, hence the exact lattice decomposition requires no extra
hypothesis. -/
theorem phiD_exactThreeWayTsumDecomposition
    {ϱ : ℝ → ℝ} {lam L w : ℝ}
    (hϱ : Zeta23.TaperProfile ϱ)
    (h0 : 0 < lam) (h1 : lam ≤ 1)
    (hw : 1 ≤ w) (hwL : 8 * w ≤ L)
    (T τ τ' : ℝ) {kMin kMax : ℤ} (hkk : kMin ≤ kMax) :
    ExactThreeWayTsumDecomposition
      (phiDGridSummand ϱ lam L w T τ τ') kMin kMax := by
  apply exactThreeWayTsumDecomposition_of_summable hkk
  exact (hasSum_phiD_full_grid hϱ h0 h1 hw hwL T τ τ').summable

/-- The finite-vs-full overlap identity is now unconditional for the actual
Zeta23 window, apart from the natural ordering `kMin ≤ kMax`. -/
theorem intervalFiniteGridOverlap_error_eq_tails_proved
    {ϱ : ℝ → ℝ} {lam L w : ℝ}
    (hϱ : Zeta23.TaperProfile ϱ)
    (h0 : 0 < lam) (h1 : lam ≤ 1)
    (hw : 1 ≤ w) (hwL : 8 * w ≤ L)
    (T τ τ' : ℝ) {kMin kMax : ℤ} (hkk : kMin ≤ kMax) :
    |intervalFiniteGridOverlap ϱ lam L w T τ τ' kMin kMax -
        fullGridOverlap ϱ lam L w τ τ'| =
      |leftInfiniteTail (phiDGridSummand ϱ lam L w T τ τ') kMin +
        rightInfiniteTail (phiDGridSummand ϱ lam L w T τ τ') kMax| := by
  exact intervalFiniteGridOverlap_error_eq_tails
    hϱ h0 h1 hw hwL T τ τ'
    (phiD_exactThreeWayTsumDecomposition hϱ h0 h1 hw hwL T τ τ' hkk)

end HurtadoZeta23
