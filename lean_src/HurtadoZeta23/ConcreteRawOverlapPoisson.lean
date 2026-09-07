import HurtadoZeta23.ConcreteRawOverlapReduction
import HurtadoZeta23.PoissonGramUnitBound
import Mathlib.Tactic

noncomputable section

open Matrix Finset
open scoped BigOperators ComplexOrder

namespace HurtadoZeta23

/-!
# Poisson-closed raw overlap

This module combines:

* the Poisson column normalization;
* the resulting Gram entry unit bound;
* the normalized limiting-kernel unit bound.

Therefore the raw pointwise overlap package is reduced to the single genuine
Input-IV estimate

  `|Re G_ab - limitingk(y_b-y_a)| ≤ eps`

on the retained 262-point block.
-/

/--
For an actual consecutive retained block, `RawPointwiseOverlapApproximation262`
follows from the genuine compact-overlap estimate alone, once the already
formalized Poisson normalization hypotheses are supplied.
-/
theorem rawPointwiseOverlapApproximation262_consecutive_of_compact
    (T eps : ℝ)
    (hPois :
      Zeta23.ZeroSide.PoissonSq T (articleParams.atD T))
    (hc :
      0 <
        (articleParams.atD T).a T *
          (articleParams.atD T).L T ^ 2)
    (s : ℕ)
    (hs : s + blockLength ≤ articleRetainedCard T)
    (heps : 0 ≤ eps)
    (hcompact :
      ∀ a b (ha : a < blockLength) (hb : b < blockLength),
        |(consecutiveGramBlock T s hs ⟨a, ha⟩ ⟨b, hb⟩).re
            -
          limitingk
            (consecutiveY T s hs b - consecutiveY T s hs a)|
          ≤ eps) :
    RawPointwiseOverlapApproximation262
      (consecutiveY T s hs)
      (consecutiveGramOverlap T s hs)
      eps := by

  apply
    rawPointwiseOverlapApproximation262_consecutive_of_bounds
      T eps s hs heps

  · intro a b ha hb
    exact
      consecutiveGramBlock_re_abs_le_one
        T hPois hc s hs ⟨a, ha⟩ ⟨b, hb⟩

  · exact hcompact

/--
Finite sliding-block form matching the overlap used by
`ConcreteGramClosedAssembly`.
-/
theorem articleConsecutiveGramOverlap_raw_of_compact
    (T eps : ℝ)
    (hS : blockLength ≤ articleRetainedCard T)
    (hPois :
      Zeta23.ZeroSide.PoissonSq T (articleParams.atD T))
    (hc :
      0 <
        (articleParams.atD T).a T *
          (articleParams.atD T).L T ^ 2)
    (heps : 0 ≤ eps)
    (s : Fin (articleRetainedCard T - blockLength + 1))
    (hcompact :
      ∀ a b
        (ha : a < blockLength)
        (hb : b < blockLength),
        |(consecutiveGramBlock
            T
            s.1
            (by
              have hs := s.2
              omega)
            ⟨a, ha⟩
            ⟨b, hb⟩).re
            -
          limitingk
            (consecutiveY
                T
                s.1
                (by
                  have hs := s.2
                  omega)
                b
              -
             consecutiveY
                T
                s.1
                (by
                  have hs := s.2
                  omega)
                a)|
          ≤ eps) :
    RawPointwiseOverlapApproximation262
      (consecutiveY
        T
        s.1
        (by
          have hs := s.2
          omega))
      (articleConsecutiveGramOverlap T hS s)
      eps := by

  let hs :
      s.1 + blockLength ≤ articleRetainedCard T := by
    have hs0 := s.2
    omega

  change
    RawPointwiseOverlapApproximation262
      (consecutiveY T s.1 hs)
      (consecutiveGramOverlap T s.1 hs)
      eps

  apply
    rawPointwiseOverlapApproximation262_consecutive_of_compact
      T eps hPois hc s.1 hs heps

  intro a b ha hb

  simpa only using hcompact a b ha hb

end HurtadoZeta23
