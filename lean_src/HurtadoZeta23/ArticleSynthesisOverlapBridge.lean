import HurtadoZeta23.ConcreteGridTailBound
import HurtadoZeta23.ConsecutiveGramBlocks
import HurtadoZeta23.CompactOverlapLimit
import Mathlib.Tactic

noncomputable section

namespace HurtadoZeta23

open Matrix Finset
open scoped BigOperators ComplexOrder

/-!
# Exact synthesis/finite-overlap seam

The analytic Input-IV modules work with `normalizedIntervalOverlap`.
The matrix chain works with entries of `consecutiveGramBlock`.

This file isolates the exact source-level identity between those two objects.
It does not postulate it as an axiom: `ArticleSynthesisOverlapIdentity` is a
plain proposition which the next source-level proof must establish by unfolding
`ZeroSide.evalVec`, `Params.atD_phi`, and the simple-column normalization.
-/

/--
Exact identity needed to identify a concrete Gram entry with the finite
Montgomery--Taylor lattice overlap.

The order `(j,i)` is chosen so that the limiting argument is exactly
`y_j - y_i`.
-/
def ArticleSynthesisOverlapIdentity : Prop :=
  ∀ (T : ℝ) (s : ℕ)
    (hs : s + blockLength ≤ articleRetainedCard T)
    (i j : Fin blockLength),
    (consecutiveGramBlock T s hs i j).re
      =
    normalizedIntervalOverlap
      articleParams.ϱ
      (articleParams.L T)
      articleParams.w
      T
      (consecutiveZero T s hs j).im
      (consecutiveZero T s hs i).im
      0
      (articleLastGridIndex T)

/-- Difference of local normalized coordinates equals the scaled ordinate
difference used in `compactOverlap_quantitative`. -/
theorem consecutiveY_sub_eq_scaled_im_sub
    (T : ℝ) (s : ℕ)
    (hs : s + blockLength ≤ articleRetainedCard T)
    (i j : Fin blockLength) :
    consecutiveY T s hs j.1 -
        consecutiveY T s hs i.1
      =
    articleParams.L T *
        ((consecutiveZero T s hs j).im -
          (consecutiveZero T s hs i).im) /
      (2 * Real.pi) := by
  rw [
    consecutiveY_eq T s hs j.2,
    consecutiveY_eq T s hs i.2
  ]
  unfold orderedRetainedY
  rw [
    consecutiveZero_eq_ordered T s hs j,
    consecutiveZero_eq_ordered T s hs i
  ]
  ring

/--
Once the exact synthesis identity is supplied, any quantitative normalized
finite-overlap estimate transfers verbatim to the actual Gram entry.
-/
theorem consecutiveGram_compact_of_normalized
    (hId : ArticleSynthesisOverlapIdentity)
    (T eps : ℝ)
    (s : ℕ)
    (hs : s + blockLength ≤ articleRetainedCard T)
    (i j : Fin blockLength)
    (hquant :
      |normalizedIntervalOverlap
          articleParams.ϱ
          (articleParams.L T)
          articleParams.w
          T
          (consecutiveZero T s hs j).im
          (consecutiveZero T s hs i).im
          0
          (articleLastGridIndex T)
        -
        limitingk
          (articleParams.L T *
            ((consecutiveZero T s hs j).im -
              (consecutiveZero T s hs i).im) /
            (2 * Real.pi))|
        ≤ eps) :
    |(consecutiveGramBlock T s hs i j).re -
        limitingk
          (consecutiveY T s hs j.1 -
            consecutiveY T s hs i.1)|
      ≤ eps := by
  rw [hId T s hs i j]
  rw [consecutiveY_sub_eq_scaled_im_sub T s hs i j]
  exact hquant

end HurtadoZeta23
