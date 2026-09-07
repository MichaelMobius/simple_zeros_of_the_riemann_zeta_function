import HurtadoZeta23.RetainedSpanBridge
import HurtadoZeta23.ShiftedRetainedPinching
import Mathlib.Tactic

noncomputable section

open Filter Asymptotics Finset
open scoped BigOperators

namespace HurtadoZeta23

/-!
# Concrete finite shifted-pinching bridge

This file combines the two finite pieces that are now fully concrete:

* the span-counting estimate from `RetainedSpanBridge`;
* the shifted Gram pinching estimate from `ShiftedRetainedPinching`.

Thus the only remaining finite input is the summed uniform block-stability
lower bound.  This is precisely the finite form of the manuscript's
"Uniform block stability" lemma.
-/

/-- Canonical sum of the spectral defects of all consecutive full retained
`blockLength = 262` blocks. -/
noncomputable def articleConsecutiveBlockDefectSum (T : ℝ) : ℝ :=
  if hS : blockLength ≤ articleRetainedCard T then
    ∑ s : Fin (articleRetainedCard T - blockLength + 1),
      consecutiveBlockDefect
        T s.1
        (by
          have hs := s.2
          omega)
  else
    0

/-- The already-proved shifted pinching theorem in the canonical-sum notation. -/
theorem articleConsecutiveBlockDefectSum_le_stable
    (T : ℝ)
    (hS : blockLength ≤ articleRetainedCard T) :
    articleConsecutiveBlockDefectSum T
      ≤ (blockLength : ℝ) * articleStableDefect T := by
  simp only [articleConsecutiveBlockDefectSum, dif_pos hS]
  exact sum_all_consecutiveBlockDefect_le_stable T hS

/-- Nonnegativity of the universal sampling span used in the article. -/
theorem samplingSpanScale_nonneg
    (T : ℝ)
    (hT : 0 ≤ T)
    (hl : 0 ≤ Zeta23.l T) :
    0 ≤ samplingSpanScale T := by
  unfold samplingSpanScale
  positivity

/--
Exact finite article-level shifted pinching.

The hypothesis `hblocks` is the summed form of uniform block stability.  Its
error is written as `blockLength * blockErr`, because `shifted_pinching_exact`
divides the summed error by the number of shifts.  Consequently the final
error is exactly `blockErr`, matching `RvMShiftedPinchingInputs`.
-/
theorem article_shifted_pinching_finite
    (T blockErr : ℝ)
    (hS : blockLength ≤ articleRetainedCard T)
    (hT : 0 ≤ T)
    (hl : 0 ≤ Zeta23.l T)
    (hblocks :
      A0 *
          ((slidingBlockCount
              (articleRetainedCard T)
              blockLength : ℕ) : ℝ)
        - beta * articleConsecutiveSpanSum T
        - (blockLength : ℝ) * blockErr
        ≤ articleConsecutiveBlockDefectSum T) :
    alpha * (articleRetainedCard T : ℝ)
      - pressureCost * samplingSpanScale T
      - endpointCorrection
      - blockErr
      ≤ articleStableDefect T := by

  have hspan0 :
      0 ≤ samplingSpanScale T :=
    samplingSpanScale_nonneg T hT hl

  have hspan :
      articleConsecutiveSpanSum T
        ≤ ((blockLength - 1 : ℕ) : ℝ) * samplingSpanScale T :=
    articleConsecutiveSpanSum_le_sampling T hS hT hl

  have hpinch :
      articleConsecutiveBlockDefectSum T
        ≤ (blockLength : ℝ) * articleStableDefect T :=
    articleConsecutiveBlockDefectSum_le_stable T hS

  have h :=
    shifted_pinching_exact
      (S := articleRetainedCard T)
      (D := articleStableDefect T)
      (spanSum := articleConsecutiveSpanSum T)
      (totalSpan := samplingSpanScale T)
      (err := (blockLength : ℝ) * blockErr)
      (blockSum := articleConsecutiveBlockDefectSum T)
      hS
      hspan0
      hspan
      hblocks
      hpinch

  have hcancel :
      ((blockLength : ℝ) * blockErr) / blockLength = blockErr := by
    norm_num [blockLength]

  rw [hcancel] at h
  exact h

/-- Same finite theorem with the published rational coefficients displayed
literally. -/
theorem article_shifted_pinching_finite_published
    (T blockErr : ℝ)
    (hS : blockLength ≤ articleRetainedCard T)
    (hT : 0 ≤ T)
    (hl : 0 ≤ Zeta23.l T)
    (hblocks :
      A0 *
          ((slidingBlockCount
              (articleRetainedCard T)
              blockLength : ℕ) : ℝ)
        - beta * articleConsecutiveSpanSum T
        - (blockLength : ℝ) * blockErr
        ≤ articleConsecutiveBlockDefectSum T) :
    (312 / 81875 : ℝ) * (articleRetainedCard T : ℝ)
      - (261 / 131000 : ℝ) * samplingSpanScale T
      - endpointCorrection
      - blockErr
      ≤ articleStableDefect T := by
  simpa [alpha, pressureCost] using
    article_shifted_pinching_finite
      T blockErr hS hT hl hblocks

end HurtadoZeta23
