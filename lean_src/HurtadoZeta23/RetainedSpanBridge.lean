import HurtadoZeta23.RetainedCardinalityBridge
import HurtadoZeta23.ShiftedPinching
import HurtadoZeta23.WindowCombinatorics
import Mathlib.Tactic

noncomputable section

open Finset Set
open scoped BigOperators

namespace HurtadoZeta23

/-!
# Concrete span bridge for retained consecutive blocks

This file supplies the exact finite `hspan` input for
`shifted_pinching_exact`.

The retained columns are already ordered by ordinate.  We extend their
normalized ordinates to a function on `ℕ`, define the global gap sequence,
and use the compiled combinatorial theorem `sum_slidingBlockSpan_le`.

No analytic approximation and no seven-point certificate enters here.
-/

/-- At the article endpoint `λ = 1`, the taper scale is exactly `l(T)`. -/
@[simp] theorem articleParams_L_eq_zeta_l (T : ℝ) :
    articleParams.L T = Zeta23.l T := by
  change (1 : ℝ) * Zeta23.l T = Zeta23.l T
  ring

/-- The ordered retained normalized ordinate, extended by zero outside its
finite range. -/
noncomputable def articleRetainedYNat
    (T : ℝ) (q : ℕ) : ℝ :=
  if hq : q < articleRetainedCard T then
    orderedRetainedY T ⟨q, hq⟩
  else
    0

@[simp] theorem articleRetainedYNat_eq
    (T : ℝ) {q : ℕ}
    (hq : q < articleRetainedCard T) :
    articleRetainedYNat T q =
      orderedRetainedY T ⟨q, hq⟩ := by
  unfold articleRetainedYNat
  rw [dif_pos hq]

/-- Global adjacent-gap sequence of the ordered retained normalized
ordinates. -/
noncomputable def articleRetainedGap
    (T : ℝ) (q : ℕ) : ℝ :=
  articleRetainedYNat T (q + 1)
    - articleRetainedYNat T q

/-- On the actual retained range, all adjacent gaps are nonnegative. -/
theorem articleRetainedGap_nonneg
    (T : ℝ)
    (hL : 0 ≤ articleParams.L T)
    {q : ℕ}
    (hq : q < articleRetainedCard T - 1) :
    0 ≤ articleRetainedGap T q := by

  have hq0 :
      q < articleRetainedCard T := by
    omega

  have hq1 :
      q + 1 < articleRetainedCard T := by
    omega

  rw [
    articleRetainedGap,
    articleRetainedYNat_eq T hq1,
    articleRetainedYNat_eq T hq0
  ]

  exact
    sub_nonneg.mpr
      (orderedRetainedY_mono
        hL
        (by
          change q ≤ q + 1
          omega))

/-- `articleRetainedYNat` evaluated at a local block rank is exactly the
already-defined local normalized coordinate. -/
theorem articleRetainedYNat_blockRank
    (T : ℝ) (s : ℕ)
    (hs : s + blockLength ≤ articleRetainedCard T)
    (i : Fin blockLength) :
    articleRetainedYNat T (s + i.1)
      =
    orderedRetainedY T
      (consecutiveRetainedRank T s hs i) := by

  have hfit :
      s + i.1 < articleRetainedCard T := by
    have hi := i.2
    omega

  rw [articleRetainedYNat_eq T hfit]

  congr 1

/-- A sliding span of the global gap sequence is literally the geometric span
of the corresponding consecutive retained Gram block. -/
theorem slidingBlockSpan_articleRetainedGap_eq
    (T : ℝ) (s : ℕ)
    (hs : s + blockLength ≤ articleRetainedCard T) :
    slidingBlockSpan
        (articleRetainedGap T)
        blockLength s
      =
    consecutiveBlockSpan T s hs := by

  have htel :=
    telescoping_gap_sum
      (fun i : ℕ =>
        articleRetainedYNat T (s + i))
      (blockLength - 1)

  have hsum :
      slidingBlockSpan
          (articleRetainedGap T)
          blockLength s
        =
      articleRetainedYNat T
          (s + (blockLength - 1))
        -
      articleRetainedYNat T s := by

    unfold slidingBlockSpan articleRetainedGap

    calc
      (∑ i ∈ Finset.range (blockLength - 1),
        (articleRetainedYNat T (s + i + 1)
          - articleRetainedYNat T (s + i)))
        =
      (∑ i ∈ Finset.range (blockLength - 1),
        (articleRetainedYNat T (s + (i + 1))
          - articleRetainedYNat T (s + i))) := by
            apply Finset.sum_congr rfl
            intro i hi
            congr 2 <;> omega
      _ =
        articleRetainedYNat T
            (s + (blockLength - 1))
          -
        articleRetainedYNat T (s + 0) := by
            simpa using htel
      _ =
        articleRetainedYNat T
            (s + (blockLength - 1))
          -
        articleRetainedYNat T s := by
            simp

  rw [hsum]

  have h0 :
      (0 : ℕ) < blockLength := by
    norm_num [blockLength]

  have hlast :
      blockLength - 1 < blockLength := by
    omega

  have hfirst :
      articleRetainedYNat T s =
        orderedRetainedY T
          (consecutiveRetainedRank T s hs ⟨0, h0⟩) := by
    simpa only [Nat.add_zero] using
      (articleRetainedYNat_blockRank
        T s hs ⟨0, h0⟩)

  rw [
    articleRetainedYNat_blockRank
      T s hs ⟨blockLength - 1, hlast⟩,
    hfirst
  ]

  unfold consecutiveBlockSpan

  rw [
    consecutiveY_eq T s hs hlast,
    consecutiveY_eq T s hs h0
  ]

/-- The canonical total retained span in gap coordinates. -/
noncomputable def articleRetainedTotalSpan
    (T : ℝ) : ℝ :=
  totalGapSpan
    (articleRetainedGap T)
    (articleRetainedCard T)

/-- The canonical sum of spans over all consecutive full 262-point blocks. -/
noncomputable def articleConsecutiveSpanSum
    (T : ℝ) : ℝ :=
  ∑ s ∈ Finset.range
      (articleRetainedCard T - blockLength + 1),
    slidingBlockSpan
      (articleRetainedGap T)
      blockLength s

/-- Exact finite shifted-span inequality:
every global gap is used in at most `blockLength - 1 = 261` blocks. -/
theorem articleConsecutiveSpanSum_le
    (T : ℝ)
    (hS : blockLength ≤ articleRetainedCard T)
    (hL : 0 ≤ articleParams.L T) :
    articleConsecutiveSpanSum T
      ≤
    ((blockLength - 1 : ℕ) : ℝ)
      * articleRetainedTotalSpan T := by

  unfold
    articleConsecutiveSpanSum
    articleRetainedTotalSpan

  exact
    sum_slidingBlockSpan_le
      (S := articleRetainedCard T)
      (m := blockLength)
      (by norm_num [blockLength])
      hS
      (articleRetainedGap T)
      (by
        intro q hq
        exact articleRetainedGap_nonneg T hL hq)

/-- A full article block forces the retained set to be nonempty. -/
theorem articleRetainedCard_pos_of_blockLength_le
    (T : ℝ)
    (hS : blockLength ≤ articleRetainedCard T) :
    0 < articleRetainedCard T := by
  have hm : 0 < blockLength := by
    norm_num [blockLength]
  omega

/-- Under the same hypothesis, the predecessor of the retained cardinal is a
valid final retained rank. -/
theorem articleRetainedCard_pred_lt_of_blockLength_le
    (T : ℝ)
    (hS : blockLength ≤ articleRetainedCard T) :
    articleRetainedCard T - 1 < articleRetainedCard T := by
  have hpos := articleRetainedCard_pos_of_blockLength_le T hS
  omega

/-- The total gap span telescopes to the last retained normalized ordinate
minus the first. -/
theorem articleRetainedTotalSpan_eq_endpoints
    (T : ℝ)
    (hS : blockLength ≤ articleRetainedCard T) :
    articleRetainedTotalSpan T
      =
    orderedRetainedY T
        ⟨articleRetainedCard T - 1,
          articleRetainedCard_pred_lt_of_blockLength_le T hS⟩
      -
    orderedRetainedY T
        ⟨0, articleRetainedCard_pos_of_blockLength_le T hS⟩ := by

  have htel :=
    telescoping_gap_sum
      (articleRetainedYNat T)
      (articleRetainedCard T - 1)

  unfold
    articleRetainedTotalSpan
    totalGapSpan
    articleRetainedGap

  rw [htel]

  have hlast :
      articleRetainedCard T - 1
        < articleRetainedCard T :=
    articleRetainedCard_pred_lt_of_blockLength_le T hS

  have hzero :
      0 < articleRetainedCard T :=
    articleRetainedCard_pos_of_blockLength_le T hS

  rw [
    articleRetainedYNat_eq T hlast,
    articleRetainedYNat_eq T hzero
  ]

/-- Every ordered retained zero belongs to the literal central retained set. -/
theorem orderedRetainedZero_mem_retained
    (T : ℝ)
    (i : Fin (articleRetainedCard T)) :
    orderedRetainedZero T i
      ∈ retainedSimpleCriticalSet T := by

  have hmem :=
    articleRetainedColumn_mem
      (articleRetainedOrderIso T i)

  simpa [
    orderedRetainedZero,
    orderedRetainedColumn,
    articleRetainedCard
  ] using hmem

/-- In particular every ordered retained ordinate is inside the original
dyadic window `(T,2T]`. -/
theorem orderedRetainedZero_im_bounds
    (T : ℝ)
    (i : Fin (articleRetainedCard T)) :
    T < (orderedRetainedZero T i).im
      ∧
    (orderedRetainedZero T i).im ≤ 2 * T := by

  have hmem :=
    orderedRetainedZero_mem_retained T i

  have hdy :
      orderedRetainedZero T i
        ∈ dyadicSimpleCriticalSet T :=
    hmem.1

  have hz :
      orderedRetainedZero T i
        ∈ Zeta23.zerosIn T (2 * T) :=
    hdy.1.1

  exact ⟨hz.2.1, hz.2.2⟩

/-- Endpoint span in `orderedRetainedY` is exactly the normalized ordinary
ordinate span from `SpanGeometry`. -/
theorem orderedRetainedY_endpoint_sub_eq_normalizedSpan
    (T : ℝ)
    (hS : blockLength ≤ articleRetainedCard T) :
    orderedRetainedY T
        ⟨articleRetainedCard T - 1,
          articleRetainedCard_pred_lt_of_blockLength_le T hS⟩
      -
    orderedRetainedY T
        ⟨0, articleRetainedCard_pos_of_blockLength_le T hS⟩
      =
    normalizedOrdinateSpan
      T
      (orderedRetainedZero T
        ⟨0, articleRetainedCard_pos_of_blockLength_le T hS⟩).im
      (orderedRetainedZero T
        ⟨articleRetainedCard T - 1,
          articleRetainedCard_pred_lt_of_blockLength_le T hS⟩).im := by

  unfold orderedRetainedY normalizedOrdinateSpan

  rw [articleParams_L_eq_zeta_l]

  ring

/-- The actual retained total normalized span is bounded by the universal
sampling span `T*l(T)/(2π)`. -/
theorem articleRetainedTotalSpan_le_samplingSpanScale
    (T : ℝ)
    (hS : blockLength ≤ articleRetainedCard T)
    (hT : 0 ≤ T)
    (hl : 0 ≤ Zeta23.l T) :
    articleRetainedTotalSpan T
      ≤ samplingSpanScale T := by

  rw [
    articleRetainedTotalSpan_eq_endpoints T hS,
    orderedRetainedY_endpoint_sub_eq_normalizedSpan T hS
  ]

  have hcard_pos :=
    articleRetainedCard_pos_of_blockLength_le T hS

  have hcard_pred :=
    articleRetainedCard_pred_lt_of_blockLength_le T hS

  have hfirst :=
    (orderedRetainedZero_im_bounds
      T ⟨0, hcard_pos⟩).1

  have hlast :=
    (orderedRetainedZero_im_bounds
      T
      ⟨articleRetainedCard T - 1, hcard_pred⟩).2

  exact
    normalizedOrdinateSpan_le_samplingSpanScale
      hT hl
      (le_of_lt hfirst)
      hlast

/-- Nonnegativity of the canonical total span, needed by
`shifted_pinching_exact`. -/
theorem articleRetainedTotalSpan_nonneg
    (T : ℝ)
    (hS : blockLength ≤ articleRetainedCard T)
    (hl : 0 ≤ Zeta23.l T) :
    0 ≤ articleRetainedTotalSpan T := by

  rw [articleRetainedTotalSpan_eq_endpoints T hS]

  apply sub_nonneg.mpr
  apply orderedRetainedY_mono

  ·
    rw [articleParams_L_eq_zeta_l]
    exact hl

  ·
    change 0 ≤ articleRetainedCard T - 1
    exact Nat.zero_le _

/-- Published `261 × sampling span` form of the finite span estimate. -/
theorem articleConsecutiveSpanSum_le_sampling
    (T : ℝ)
    (hS : blockLength ≤ articleRetainedCard T)
    (hT : 0 ≤ T)
    (hl : 0 ≤ Zeta23.l T) :
    articleConsecutiveSpanSum T
      ≤
    ((blockLength - 1 : ℕ) : ℝ)
      * samplingSpanScale T := by

  have hL :
      0 ≤ articleParams.L T := by
    rw [articleParams_L_eq_zeta_l]
    exact hl

  calc
    articleConsecutiveSpanSum T
      ≤
    ((blockLength - 1 : ℕ) : ℝ)
      * articleRetainedTotalSpan T :=
        articleConsecutiveSpanSum_le T hS hL

    _ ≤
    ((blockLength - 1 : ℕ) : ℝ)
      * samplingSpanScale T := by
        exact
          mul_le_mul_of_nonneg_left
            (articleRetainedTotalSpan_le_samplingSpanScale
              T hS hT hl)
            (by positivity)

end HurtadoZeta23
