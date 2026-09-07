import HurtadoZeta23.ConcreteBlockDefect
import HurtadoZeta23.GramPairEnergyIdentity
import Mathlib.Tactic

noncomputable section

open Matrix Finset
open scoped BigOperators ComplexOrder

namespace HurtadoZeta23

/-!
# Concrete Gram-closed assembly

This file removes the `hGram` interface from the global shifted-pinching
theorem.

For every consecutive retained 262-point block we use the canonical total
overlap `consecutiveGramOverlap`.  The exact identity

`globalPairEnergyNat = offDiagonalEnergy`

is supplied by `GramPairEnergyIdentity`, while the matrix Block-defect input
is already discharged by `ConcreteBlockDefect`.

Consequently the only remaining local inputs are:

* `hcert`: the seven-point certificate;
* `hraw`: the compact/raw overlap approximation for the canonical Gram overlap.
-/

/--
Canonical total overlap attached to a block indexed by the finite sliding
window index.
-/
noncomputable def articleConsecutiveGramOverlap
    (T : ℝ)
    (hS : blockLength ≤ articleRetainedCard T)
    (s : Fin (articleRetainedCard T - blockLength + 1)) :
    ℕ → ℕ → ℝ :=
  consecutiveGramOverlap
    T
    s.1
    (by
      have hs := s.2
      omega)

/--
The canonical block overlap has exactly the required off-diagonal Gram energy.
Thus `hGram` is no longer an external hypothesis.
-/
theorem articleConsecutiveGramOverlap_energy
    (T : ℝ)
    (hS : blockLength ≤ articleRetainedCard T)
    (s : Fin (articleRetainedCard T - blockLength + 1)) :
    globalPairEnergyNat blockLength
        (fun a b => articleConsecutiveGramOverlap T hS s a b ^ 2)
      =
    offDiagonalEnergy
      (consecutiveGramBlock
        T
        s.1
        (by
          have hs := s.2
          omega)) := by

  unfold articleConsecutiveGramOverlap

  exact
    globalPairEnergyNat_consecutiveGramOverlap_eq_offDiagonalEnergy
      T
      s.1
      (by
        have hs := s.2
        omega)

/--
Global shifted pinching with both structural matrix interfaces (`hblock` and
`hGram`) discharged automatically.

Only the seven-point certificate and the raw compact-overlap approximation
remain as local analytic/computational inputs.
-/
theorem article_shifted_pinching_of_uniform_raw_overlap_gram_closed
    (T eps : ℝ)
    (hS : blockLength ≤ articleRetainedCard T)
    (hT : 0 ≤ T)
    (hl : 0 ≤ Zeta23.l T)
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
    (hraw :
      ∀ s : Fin (articleRetainedCard T - blockLength + 1),
        RawPointwiseOverlapApproximation262
          (consecutiveY
            T s.1
            (by
              have hs := s.2
              omega))
          (articleConsecutiveGramOverlap T hS s)
          eps) :
    alpha * (articleRetainedCard T : ℝ)
      - pressureCost * samplingSpanScale T
      - endpointCorrection
      - articleAveragedBlockError T (136764 * eps)
      ≤
    articleStableDefect T := by

  apply
    article_shifted_pinching_of_uniform_raw_overlap_block_closed
      T
      eps
      hS
      hT
      hl
      (articleConsecutiveGramOverlap T hS)
      hcert
      hraw

  intro s

  exact articleConsecutiveGramOverlap_energy T hS s

/--
Published-coefficient version with both `hblock` and `hGram` fully closed.
-/
theorem article_shifted_pinching_of_uniform_raw_overlap_gram_closed_published
    (T eps : ℝ)
    (hS : blockLength ≤ articleRetainedCard T)
    (hT : 0 ≤ T)
    (hl : 0 ≤ Zeta23.l T)
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
    (hraw :
      ∀ s : Fin (articleRetainedCard T - blockLength + 1),
        RawPointwiseOverlapApproximation262
          (consecutiveY
            T s.1
            (by
              have hs := s.2
              omega))
          (articleConsecutiveGramOverlap T hS s)
          eps) :
    (312 / 81875 : ℝ) * (articleRetainedCard T : ℝ)
      - (261 / 131000 : ℝ) * samplingSpanScale T
      - endpointCorrection
      - articleAveragedBlockError T (136764 * eps)
      ≤
    articleStableDefect T := by

  simpa [alpha, pressureCost] using
    article_shifted_pinching_of_uniform_raw_overlap_gram_closed
      T eps hS hT hl hcert hraw

end HurtadoZeta23
