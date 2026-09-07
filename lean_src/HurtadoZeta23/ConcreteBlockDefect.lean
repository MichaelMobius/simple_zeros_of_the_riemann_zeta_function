import HurtadoZeta23.ConsecutiveBlockStabilityBridge
import HurtadoZeta23.GramPinchingVariational
import HurtadoZeta23.SpectralFrobenius
import Zeta23.LinAlg.RankTrace
import Mathlib.LinearAlgebra.Matrix.Vec
import Mathlib.Tactic

noncomputable section

open Matrix Finset
open scoped BigOperators ComplexOrder

namespace HurtadoZeta23

/-!
# Concrete Block Defect

This file closes the `hblock` interface used by
`ConsecutiveBlockStabilityBridge`.

The key observation is that the base zeta-23 development already proves the
standard Hermitian identity

`RHLinalg.frobSq A = ∑ᵢ λᵢ(A)^2`

and supplies the spectral functional calculus `RHLinalg.specMap`.  Therefore
the only entrywise bookkeeping needed here is the elementary identification

`frobeniusDeviationSq G = RHLinalg.frobSq (G - I)`.

After that, the previously proved spectral Block-defect theorem applies
directly to every consecutive retained Gram block.
-/

section FrobeniusBridge

variable {n : Type*} [Fintype n] [DecidableEq n]

/--
For an arbitrary complex matrix, the project Frobenius square is the entrywise
sum of squared norms.

The proof goes through `Matrix.star_vec_dotProduct_vec`, so it never expands
matrix multiplication or conjugate transpose entrywise.
-/
theorem frobSq_eq_sum_norm_sq
    (A : Matrix n n ℂ) :
    RHLinalg.frobSq A
      =
    ∑ i : n, ∑ j : n, ‖A i j‖ ^ 2 := by
  classical

  unfold RHLinalg.frobSq

  rw [← Matrix.star_vec_dotProduct_vec A A]

  unfold dotProduct

  rw [map_sum]

  simp only [
    Pi.star_apply,
    RCLike.star_def,
    RCLike.conj_mul
  ]

  rw [Fintype.sum_prod_type]

  simp only [Matrix.vec]

  rw [Finset.sum_comm]

  apply Finset.sum_congr rfl
  intro i hi

  apply Finset.sum_congr rfl
  intro j hj

  exact RCLike.re_ofReal_pow (K := ℂ) (‖A i j‖) 2

/--
Entrywise description of subtraction of the identity.
-/
lemma sub_one_apply
    (G : Matrix n n ℂ)
    (i j : n) :
    (G - (1 : Matrix n n ℂ)) i j
      =
    G i j - (if i = j then (1 : ℂ) else 0) := by
  simp only [Matrix.sub_apply, Matrix.one_apply]

/--
The entrywise squared distance from the identity is exactly the squared
Frobenius norm `Re tr((G-I)ᴴ(G-I))` used by the base linear-algebra library.
-/
theorem frobeniusDeviationSq_eq_frobSq_shiftOne
    (G : Matrix n n ℂ) :
    frobeniusDeviationSq G
      =
    RHLinalg.frobSq (G - (1 : Matrix n n ℂ)) := by
  classical

  rw [frobSq_eq_sum_norm_sq]

  unfold frobeniusDeviationSq

  apply Finset.sum_congr rfl
  intro i hi

  apply Finset.sum_congr rfl
  intro j hj

  rw [sub_one_apply]

/--
The Frobenius/spectral identity required by `BlockDefect` is not an extra
axiom: it follows from the already formalized spectral functional calculus.
-/
theorem frobeniusSpectralIdentity_proved
    (G : Matrix n n ℂ)
    (hG : G.IsHermitian) :
    FrobeniusSpectralIdentity G hG := by

  unfold FrobeniusSpectralIdentity spectralDeviationSq

  rw [frobeniusDeviationSq_eq_frobSq_shiftOne]

  have hspec :
      RHLinalg.specMap hG (fun x : ℝ => x - 1)
        =
      G - (1 : Matrix n n ℂ) := by
    simpa using
      (specMap_sub_const G hG 1)

  rw [← hspec]
  exact RHLinalg.frobSq_specMap hG (fun x : ℝ => x - 1)

/--
Fully proved matrix Block defect for an arbitrary complex PSD matrix.
-/
theorem gramSpectralDefect_block_defect_proved
    (G : Matrix n n ℂ)
    (hG : G.PosSemidef) :
    min 1 (offDiagonalEnergy G)
      ≤
    gramSpectralDefect G hG := by

  unfold gramSpectralDefect

  rw [
    ← RHLinalg.sum_eigenvalues_reindex
      hG.isHermitian
      psi
  ]

  exact
    block_defect_of_frobenius_spectral
      G
      hG.isHermitian
      hG
      (frobeniusSpectralIdentity_proved G hG.isHermitian)

end FrobeniusBridge

/--
Concrete Block-defect inequality for every actual consecutive retained
262-point Gram block.
-/
theorem consecutiveGramBlock_block_defect
    (T : ℝ)
    (s : ℕ)
    (hs : s + blockLength ≤ articleRetainedCard T) :
    min 1 (offDiagonalEnergy (consecutiveGramBlock T s hs))
      ≤
    consecutiveBlockDefect T s hs := by

  unfold consecutiveBlockDefect

  exact
    gramSpectralDefect_block_defect_proved
      (consecutiveGramBlock T s hs)
      (consecutiveGramBlock_posSemidef T s hs)

/--
The shifted-pinching theorem with the Block-defect input discharged
automatically.

The only remaining local interfaces are now:

* `hcert`: seven-point certificate;
* `hraw`: compact/raw overlap approximation;
* `hGram`: identification of the chosen overlap squares with the actual
  off-diagonal Gram energy.
-/
theorem article_shifted_pinching_of_uniform_raw_overlap_block_closed
    (T eps : ℝ)
    (hS : blockLength ≤ articleRetainedCard T)
    (hT : 0 ≤ T)
    (hl : 0 ≤ Zeta23.l T)
    (overlap :
      Fin (articleRetainedCard T - blockLength + 1) →
        ℕ → ℕ → ℝ)
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
          (overlap s)
          eps)
    (hGram :
      ∀ s : Fin (articleRetainedCard T - blockLength + 1),
        globalPairEnergyNat blockLength
            (fun a b => overlap s a b ^ 2)
          =
        offDiagonalEnergy
          (consecutiveGramBlock
            T s.1
            (by
              have hs := s.2
              omega))) :
    alpha * (articleRetainedCard T : ℝ)
      - pressureCost * samplingSpanScale T
      - endpointCorrection
      - articleAveragedBlockError T (136764 * eps)
      ≤
    articleStableDefect T := by

  apply
    article_shifted_pinching_of_uniform_raw_overlap
      T eps hS hT hl overlap hcert hraw

  · intro s
    exact
      consecutiveGramBlock_block_defect
        T
        s.1
        (by
          have hs := s.2
          omega)

  · exact hGram

/-- Published-coefficient version with Block defect fully closed. -/
theorem article_shifted_pinching_of_uniform_raw_overlap_block_closed_published
    (T eps : ℝ)
    (hS : blockLength ≤ articleRetainedCard T)
    (hT : 0 ≤ T)
    (hl : 0 ≤ Zeta23.l T)
    (overlap :
      Fin (articleRetainedCard T - blockLength + 1) →
        ℕ → ℕ → ℝ)
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
          (overlap s)
          eps)
    (hGram :
      ∀ s : Fin (articleRetainedCard T - blockLength + 1),
        globalPairEnergyNat blockLength
            (fun a b => overlap s a b ^ 2)
          =
        offDiagonalEnergy
          (consecutiveGramBlock
            T s.1
            (by
              have hs := s.2
              omega))) :
    (312 / 81875 : ℝ) * (articleRetainedCard T : ℝ)
      - (261 / 131000 : ℝ) * samplingSpanScale T
      - endpointCorrection
      - articleAveragedBlockError T (136764 * eps)
      ≤
    articleStableDefect T := by

  simpa [alpha, pressureCost] using
    article_shifted_pinching_of_uniform_raw_overlap_block_closed
      T eps hS hT hl overlap hcert hraw hGram

end HurtadoZeta23
