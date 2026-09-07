import HurtadoZeta23.ConsecutiveGramBlocks
import HurtadoZeta23.GramPinchingFinitePartition
import Mathlib.Tactic

noncomputable section

open Matrix Finset
open scoped ComplexOrder BigOperators

namespace HurtadoZeta23

/-!
# Retained Gram pinching

The global article defect is the spectral defect of the Gram matrix over all
simple critical-line zeros in the dyadic zero-side block.  The shifted local
argument uses only the central retained simple zeros.

This file proves the exact monotonicity needed to pass between them:

  D(M_retained) ≤ D(M_global) = articleStableDefect.

It is a single Boolean Gram pinching: retained columns versus their complement.
-/

/-- The global simple-zero Gram at the article endpoint. -/
abbrev articleGlobalSimpleGram (T : ℝ) :
    Matrix (ArticleSimpleColumn T) (ArticleSimpleColumn T) ℂ :=
  zeroSideSimpleGram
    Zeta23.zetaZeroConfig
    (articleParams.atD T)
    T
    (articlePhiHatConj T)

/-- PSD witness for the global simple Gram. -/
theorem articleGlobalSimpleGram_posSemidef (T : ℝ) :
    (articleGlobalSimpleGram T).PosSemidef := by
  exact
    zeroSideSimpleGram_posSemidef
      Zeta23.zetaZeroConfig
      (articleParams.atD T)
      T
      (articlePhiHatConj T)

/-- Boolean label selecting the concrete retained simple columns. -/
noncomputable def articleRetainedLabel (T : ℝ) :
    ArticleSimpleColumn T → Bool := by
  classical
  exact fun z =>
    decide
      (articleColumnZero z ∈ retainedSimpleCriticalSet T)

/-- The retained principal Gram, indexed by the concrete retained-column type. -/
abbrev articleRetainedGram (T : ℝ) :
    Matrix (ArticleRetainedColumn T) (ArticleRetainedColumn T) ℂ :=
  principalGramBlock
    (articleGlobalSimpleGram T)
    (fun z : ArticleRetainedColumn T => z.1)

/-- The retained principal Gram is PSD. -/
theorem articleRetainedGram_posSemidef (T : ℝ) :
    (articleRetainedGram T).PosSemidef := by
  exact
    principal_submatrix_posSemidef
      (articleGlobalSimpleGram T)
      (articleGlobalSimpleGram_posSemidef T)
      (fun z : ArticleRetainedColumn T => z.1)

/-- Spectral defect of the retained central Gram. -/
noncomputable def articleRetainedDefect (T : ℝ) : ℝ :=
  gramSpectralDefect
    (articleRetainedGram T)
    (articleRetainedGram_posSemidef T)

/-- The `true` Boolean fiber is canonically the concrete retained-column type. -/
noncomputable def retainedTrueFiberEquiv (T : ℝ) :
    BlockFiber (articleRetainedLabel T) true
      ≃ ArticleRetainedColumn T where

  toFun z := by
    classical
    have hzset :
        articleColumnZero z.1 ∈ retainedSimpleCriticalSet T := by
      simpa [articleRetainedLabel] using z.2
    refine ⟨z.1, ?_⟩
    unfold articleRetainedColumnsFinset
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ z.1, hzset⟩

  invFun z := by
    classical
    refine ⟨z.1, ?_⟩
    have hzset :=
      articleRetainedColumn_mem z
    simpa [articleRetainedLabel] using hzset

  left_inv z := by
    apply Subtype.ext
    rfl

  right_inv z := by
    apply Subtype.ext
    rfl

/-- Reindexing the retained Boolean block gives exactly `articleRetainedGram`. -/
theorem retainedTrueBlock_reindex
    (T : ℝ) :
    Matrix.reindex
        (retainedTrueFiberEquiv T)
        (retainedTrueFiberEquiv T)
        (partitionBlock
          (articleRetainedLabel T)
          (articleGlobalSimpleGram T)
          true)
      =
    articleRetainedGram T := by
  ext i j
  rfl

/-- The retained defect is exactly the defect of the `true` Boolean block. -/
theorem articleRetainedDefect_eq_trueBlockDefect
    (T : ℝ) :
    articleRetainedDefect T
      =
    gramSpectralDefect
      (partitionBlock
        (articleRetainedLabel T)
        (articleGlobalSimpleGram T)
        true)
      (principal_submatrix_posSemidef
        (articleGlobalSimpleGram T)
        (articleGlobalSimpleGram_posSemidef T)
        (fun i :
          BlockFiber (articleRetainedLabel T) true =>
            i.1)) := by

  let B :=
    partitionBlock
      (articleRetainedLabel T)
      (articleGlobalSimpleGram T)
      true

  let hB :
      B.PosSemidef :=
    principal_submatrix_posSemidef
      (articleGlobalSimpleGram T)
      (articleGlobalSimpleGram_posSemidef T)
      (fun i :
        BlockFiber (articleRetainedLabel T) true =>
          i.1)

  let e := retainedTrueFiberEquiv T

  have hreindex :
      gramSpectralDefect
          (Matrix.reindex e e B)
          (posSemidef_reindex e B hB)
        =
      gramSpectralDefect B hB :=
    gramSpectralDefect_reindex e B hB

  have hmat :
      Matrix.reindex e e B =
        articleRetainedGram T := by
    simpa [B, e] using retainedTrueBlock_reindex T

  have hdep :
      gramSpectralDefect
          (Matrix.reindex e e B)
          (posSemidef_reindex e B hB)
        =
      gramSpectralDefect
          (articleRetainedGram T)
          (articleRetainedGram_posSemidef T) :=
    gramSpectralDefect_eq_of_matrix_eq
      (posSemidef_reindex e B hB)
      (articleRetainedGram_posSemidef T)
      hmat

  unfold articleRetainedDefect
  change
    gramSpectralDefect
        (articleRetainedGram T)
        (articleRetainedGram_posSemidef T)
      =
    gramSpectralDefect B hB

  exact hdep.symm.trans hreindex

/-- The retained central Gram defect cannot exceed the global simple Gram
defect. -/
theorem articleRetainedDefect_le_global
    (T : ℝ) :
    articleRetainedDefect T
      ≤
    gramSpectralDefect
      (articleGlobalSimpleGram T)
      (articleGlobalSimpleGram_posSemidef T) := by

  have hp :=
    gramDefectPinching_bool_proved
      (articleRetainedLabel T)
      (articleGlobalSimpleGram T)
      (articleGlobalSimpleGram_posSemidef T)

  unfold GramDefectPinchingPartition at hp
  rw [Fintype.sum_bool] at hp

  let hfalse :
      (partitionBlock
        (articleRetainedLabel T)
        (articleGlobalSimpleGram T)
        false).PosSemidef :=
    principal_submatrix_posSemidef
      (articleGlobalSimpleGram T)
      (articleGlobalSimpleGram_posSemidef T)
      (fun i :
        BlockFiber (articleRetainedLabel T) false =>
          i.1)

  have hfalse0 :
      0 ≤
      gramSpectralDefect
        (partitionBlock
          (articleRetainedLabel T)
          (articleGlobalSimpleGram T)
          false)
        hfalse :=
    gramSpectralDefect_nonneg _ hfalse

  have htrue :
      articleRetainedDefect T
        =
      gramSpectralDefect
        (partitionBlock
          (articleRetainedLabel T)
          (articleGlobalSimpleGram T)
          true)
        (principal_submatrix_posSemidef
          (articleGlobalSimpleGram T)
          (articleGlobalSimpleGram_posSemidef T)
          (fun i :
            BlockFiber (articleRetainedLabel T) true =>
              i.1)) :=
    articleRetainedDefect_eq_trueBlockDefect T

  rw [htrue]

  linarith

/-- The global Gram defect here is definitionally the same defect used by the
concrete stable seam. -/
theorem articleGlobalSimpleDefect_eq_stableDefect
    (T : ℝ) :
    gramSpectralDefect
      (articleGlobalSimpleGram T)
      (articleGlobalSimpleGram_posSemidef T)
      =
    articleStableDefect T := by
  rfl

/-- Main retained-vs-global bridge used by shifted pinching. -/
theorem articleRetainedDefect_le_articleStableDefect
    (T : ℝ) :
    articleRetainedDefect T
      ≤ articleStableDefect T := by
  rw [← articleGlobalSimpleDefect_eq_stableDefect T]
  exact articleRetainedDefect_le_global T

/-- Nonnegativity of the retained defect. -/
theorem articleRetainedDefect_nonneg
    (T : ℝ) :
    0 ≤ articleRetainedDefect T := by
  exact
    gramSpectralDefect_nonneg
      (articleRetainedGram T)
      (articleRetainedGram_posSemidef T)

end HurtadoZeta23
