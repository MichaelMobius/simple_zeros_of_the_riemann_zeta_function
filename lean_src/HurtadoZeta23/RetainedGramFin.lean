import HurtadoZeta23.RetainedGramPinching
import Mathlib.Tactic

noncomputable section

open Matrix Finset
open scoped ComplexOrder BigOperators

namespace HurtadoZeta23

/-!
# Retained Gram on `Fin S`

The retained Gram is naturally indexed by the subtype `ArticleRetainedColumn T`.
For shifted block decompositions it is much more convenient to reindex it by
the canonical increasing-order ranks `Fin S`, where

`S = Fintype.card (ArticleRetainedColumn T)`.

This file proves that the already-compiled `consecutiveGramBlock` is literally
the corresponding consecutive principal submatrix of this `Fin S` Gram.
-/

/-- Equivalence from retained columns to their increasing-order ranks. -/
noncomputable abbrev articleRetainedRankEquiv (T : ℝ) :
    ArticleRetainedColumn T ≃ Fin (articleRetainedCard T) :=
  (articleRetainedOrderIso T).toEquiv.symm

@[simp] theorem articleRetainedRankEquiv_symm_apply
    (T : ℝ) (i : Fin (articleRetainedCard T)) :
    (articleRetainedRankEquiv T).symm i =
      articleRetainedOrderIso T i := by
  rfl

@[simp] theorem articleRetainedRankEquiv_symm_consecutiveRank
    (T : ℝ) (s : ℕ)
    (hs : s + blockLength ≤ articleRetainedCard T)
    (i : Fin blockLength) :
    (articleRetainedRankEquiv T).symm
        (consecutiveRetainedRank T s hs i)
      =
    consecutiveRetainedColumn T s hs i := by
  rfl

/-- Retained Gram reindexed by increasing ordinate rank. -/
noncomputable abbrev articleRetainedGramFin (T : ℝ) :
    Matrix (Fin (articleRetainedCard T))
      (Fin (articleRetainedCard T)) ℂ :=
  Matrix.reindex
    (articleRetainedRankEquiv T)
    (articleRetainedRankEquiv T)
    (articleRetainedGram T)

theorem articleRetainedGram_apply
    (T : ℝ)
    (i j : ArticleRetainedColumn T) :
    articleRetainedGram T i j =
      articleGlobalSimpleGram T i.1 j.1 := by
  rfl

/-- PSD survives the rank reindexing. -/
theorem articleRetainedGramFin_posSemidef (T : ℝ) :
    (articleRetainedGramFin T).PosSemidef := by
  exact
    posSemidef_reindex
      (articleRetainedRankEquiv T)
      (articleRetainedGram T)
      (articleRetainedGram_posSemidef T)

/-- Reindexing does not change the retained spectral defect. -/
theorem articleRetainedGramFin_defect_eq
    (T : ℝ) :
    gramSpectralDefect
      (articleRetainedGramFin T)
      (articleRetainedGramFin_posSemidef T)
      =
    articleRetainedDefect T := by

  have h :=
    gramSpectralDefect_reindex
      (articleRetainedRankEquiv T)
      (articleRetainedGram T)
      (articleRetainedGram_posSemidef T)

  unfold articleRetainedDefect

  exact h

/-- Consecutive principal submatrix of the rank-indexed retained Gram. -/
noncomputable abbrev consecutiveRetainedGramFinBlock
    (T : ℝ) (s : ℕ)
    (hs : s + blockLength ≤ articleRetainedCard T) :
    Matrix (Fin blockLength) (Fin blockLength) ℂ :=
  (articleRetainedGramFin T).submatrix
    (consecutiveRetainedRank T s hs)
    (consecutiveRetainedRank T s hs)

/-- Every consecutive principal submatrix of the retained Gram is PSD. -/
theorem consecutiveRetainedGramFinBlock_posSemidef
    (T : ℝ) (s : ℕ)
    (hs : s + blockLength ≤ articleRetainedCard T) :
    (consecutiveRetainedGramFinBlock T s hs).PosSemidef := by

  exact
    principal_submatrix_posSemidef
      (articleRetainedGramFin T)
      (articleRetainedGramFin_posSemidef T)
      (consecutiveRetainedRank T s hs)

/-- Entrywise identification with the concrete zero-side consecutive block. -/
theorem consecutiveRetainedGramFinBlock_eq
    (T : ℝ) (s : ℕ)
    (hs : s + blockLength ≤ articleRetainedCard T) :
    consecutiveRetainedGramFinBlock T s hs
      =
    consecutiveGramBlock T s hs := by

  ext i j

  change
    articleRetainedGram T
      ((articleRetainedRankEquiv T).symm
        (consecutiveRetainedRank T s hs i))
      ((articleRetainedRankEquiv T).symm
        (consecutiveRetainedRank T s hs j))
      =
    articleGlobalSimpleGram T
      (consecutiveSimpleColumn T s hs i)
      (consecutiveSimpleColumn T s hs j)

  rw [
    articleRetainedRankEquiv_symm_consecutiveRank,
    articleRetainedRankEquiv_symm_consecutiveRank,
    articleRetainedGram_apply
  ]

  rfl

/-- The spectral defect of the rank-principal block is exactly the already
defined `consecutiveBlockDefect`. -/
theorem consecutiveRetainedGramFinBlock_defect_eq
    (T : ℝ) (s : ℕ)
    (hs : s + blockLength ≤ articleRetainedCard T) :
    gramSpectralDefect
      (consecutiveRetainedGramFinBlock T s hs)
      (consecutiveRetainedGramFinBlock_posSemidef T s hs)
      =
    consecutiveBlockDefect T s hs := by

  unfold consecutiveBlockDefect

  exact
    gramSpectralDefect_eq_of_matrix_eq
      (consecutiveRetainedGramFinBlock_posSemidef T s hs)
      (consecutiveGramBlock_posSemidef T s hs)
      (consecutiveRetainedGramFinBlock_eq T s hs)

end HurtadoZeta23
