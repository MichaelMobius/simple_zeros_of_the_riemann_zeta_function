import HurtadoZeta23.ConcreteGramClosedAssembly
import HurtadoZeta23.ConcreteRawOverlapPoisson
import Mathlib.Tactic

noncomputable section

open Matrix Finset
open scoped BigOperators ComplexOrder

namespace HurtadoZeta23

/-!
# Compact-overlap closed assembly

This removes `hraw` from the global shifted-pinching interface.

The raw-overlap package is now built internally from:

* Poisson column normalization;
* the Gram unit bound;
* the limiting-kernel unit bound;
* the single genuine compact-overlap estimate `hcompact`.

Thus the only local block inputs left are `hcompact` and the seven-point
certificate `hcert`.
-/

/--
Global shifted pinching with `hblock`, `hGram`, and `hraw` all discharged.
-/
theorem article_shifted_pinching_of_uniform_compact_overlap
    (T eps : ℝ)
    (hS : blockLength ≤ articleRetainedCard T)
    (hT : 0 ≤ T)
    (hl : 0 ≤ Zeta23.l T)
    (hPois :
      Zeta23.ZeroSide.PoissonSq T (articleParams.atD T))
    (hc :
      0 <
        (articleParams.atD T).a T *
          (articleParams.atD T).L T ^ 2)
    (heps : 0 ≤ eps)
    (hcert :
      ∀ s : Fin (articleRetainedCard T - blockLength + 1),
        SevenPointCertificate
          (limitingWeightOnPoints
            (consecutiveY
              T s.1
              (by
                have hs := s.2
                omega)))
          (consecutiveY
            T s.1
            (by
              have hs := s.2
              omega))
          blockLength)
    (hcompact :
      ∀ s : Fin (articleRetainedCard T - blockLength + 1),
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
    alpha * (articleRetainedCard T : ℝ)
      - pressureCost * samplingSpanScale T
      - endpointCorrection
      - articleAveragedBlockError T (136764 * eps)
      ≤
    articleStableDefect T := by

  apply
    article_shifted_pinching_of_uniform_raw_overlap_gram_closed
      T eps hS hT hl hcert

  intro s

  exact
    articleConsecutiveGramOverlap_raw_of_compact
      T eps hS hPois hc heps s
      (hcompact s)

/--
Published-coefficient form with the same reduced interface.
-/
theorem article_shifted_pinching_of_uniform_compact_overlap_published
    (T eps : ℝ)
    (hS : blockLength ≤ articleRetainedCard T)
    (hT : 0 ≤ T)
    (hl : 0 ≤ Zeta23.l T)
    (hPois :
      Zeta23.ZeroSide.PoissonSq T (articleParams.atD T))
    (hc :
      0 <
        (articleParams.atD T).a T *
          (articleParams.atD T).L T ^ 2)
    (heps : 0 ≤ eps)
    (hcert :
      ∀ s : Fin (articleRetainedCard T - blockLength + 1),
        SevenPointCertificate
          (limitingWeightOnPoints
            (consecutiveY
              T s.1
              (by
                have hs := s.2
                omega)))
          (consecutiveY
            T s.1
            (by
              have hs := s.2
              omega))
          blockLength)
    (hcompact :
      ∀ s : Fin (articleRetainedCard T - blockLength + 1),
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
    (312 / 81875 : ℝ) * (articleRetainedCard T : ℝ)
      - (261 / 131000 : ℝ) * samplingSpanScale T
      - endpointCorrection
      - articleAveragedBlockError T (136764 * eps)
      ≤
    articleStableDefect T := by

  simpa [alpha, pressureCost] using
    article_shifted_pinching_of_uniform_compact_overlap
      T eps hS hT hl hPois hc heps hcert hcompact

end HurtadoZeta23
