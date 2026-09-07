import HurtadoZeta23.GramPinchingVariational
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

noncomputable section

open Matrix Finset Polynomial
open scoped ComplexOrder

universe u

namespace HurtadoZeta23

/-!
# Binary block-diagonal additivity for the Gram spectral defect

Downstream code needs only two exported facts from this file:

* `rootsPsiGramBridge_proved`, used for reindex invariance;
* `gramDefectPinching_bool_proved`, the complete Boolean two-block estimate.

The proof is purely finite-dimensional:
Boolean pinching is reindexed to an explicit `Matrix.fromBlocks A 0 0 B`,
Mathlib factors its characteristic polynomial, and the root multiset therefore
splits as the sum of the two block root multisets.
-/

/-! ## Characteristic-root representation of the defect -/

section RootsPsi

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- Sum `psi` over all characteristic roots, with algebraic multiplicity. -/
noncomputable def rootsPsiSum (M : Matrix ι ι ℂ) : ℝ :=
  (M.charpoly.roots.map (fun z : ℂ => psi z.re)).sum

/-- Root-sum formulation of the Gram spectral defect. -/
def RootsPsiGramBridge : Prop :=
  ∀ {κ : Type u} [Fintype κ] [DecidableEq κ]
      (M : Matrix κ κ ℂ) (hM : M.PosSemidef),
    rootsPsiSum M = gramSpectralDefect M hM

/-- For PSD/Hermitian matrices, Mathlib identifies the characteristic roots
with the real eigenvalues `eigenvalues₀`, including multiplicity. -/
theorem rootsPsiGramBridge_proved :
    RootsPsiGramBridge.{u} := by
  intro κ _ _ M hM
  unfold rootsPsiSum gramSpectralDefect
  rw [hM.isHermitian.roots_charpoly_eq_eigenvalues₀]
  simpa [Function.comp_def] using
    (List.sum_ofFn
      (f := fun j => psi (hM.isHermitian.eigenvalues₀ j)))

/-- Root-psi sums are additive when the characteristic polynomial factors. -/
theorem rootsPsiSum_add_of_charpoly_mul
    {κ₁ κ₂ κ : Type u}
    [Fintype κ₁] [DecidableEq κ₁]
    [Fintype κ₂] [DecidableEq κ₂]
    [Fintype κ] [DecidableEq κ]
    (A : Matrix κ₁ κ₁ ℂ)
    (B : Matrix κ₂ κ₂ ℂ)
    (M : Matrix κ κ ℂ)
    (hfac : M.charpoly = A.charpoly * B.charpoly) :
    rootsPsiSum M = rootsPsiSum A + rootsPsiSum B := by
  unfold rootsPsiSum
  rw [hfac]
  have hA0 : A.charpoly ≠ 0 := (Matrix.charpoly_monic A).ne_zero
  have hB0 : B.charpoly ≠ 0 := (Matrix.charpoly_monic B).ne_zero
  have hne : A.charpoly * B.charpoly ≠ 0 := mul_ne_zero hA0 hB0
  rw [Polynomial.roots_mul hne]
  simp [Multiset.map_add, Multiset.sum_add]

end RootsPsi

/-! ## Reindexing a Boolean partition to an explicit block diagonal -/

section BoolReindex

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- Explicit equivalence between the original index type and its false/true
Boolean fibers. -/
def boolFiberEquiv (label : ι → Bool) :
    ι ≃ (BlockFiber label false ⊕ BlockFiber label true) where
  toFun i :=
    if h : label i = false then
      Sum.inl ⟨i, h⟩
    else
      Sum.inr ⟨i, Bool.eq_true_of_not_eq_false h⟩
  invFun s := Sum.elim Subtype.val Subtype.val s
  left_inv i := by
    dsimp
    by_cases h : label i = false
    · rw [dif_pos h]
      rfl
    · rw [dif_neg h]
      rfl
  right_inv s := by
    cases s with
    | inl i =>
        dsimp
        rw [dif_pos i.property]
    | inr i =>
        have hfalse : label i.1 ≠ false := by
          intro hf
          have hbad : false = true := hf.symm.trans i.property
          exact Bool.false_ne_true hbad
        dsimp
        rw [dif_neg hfalse]

@[simp] theorem boolFiberEquiv_symm_inl
    (label : ι → Bool) (i : BlockFiber label false) :
    (boolFiberEquiv label).symm (Sum.inl i) = i.1 := by
  rfl

@[simp] theorem boolFiberEquiv_symm_inr
    (label : ι → Bool) (i : BlockFiber label true) :
    (boolFiberEquiv label).symm (Sum.inr i) = i.1 := by
  rfl

/-- Under `boolFiberEquiv`, Boolean pinching is literally block diagonal. -/
theorem boolPinch_reindex_eq_fromBlocks
    (label : ι → Bool) (M : Matrix ι ι ℂ) :
    Matrix.reindex (boolFiberEquiv label) (boolFiberEquiv label)
        (partitionPinch label M) =
      Matrix.fromBlocks
        (partitionBlock label M false) 0 0
        (partitionBlock label M true) := by
  ext i j
  cases i with
  | inl i =>
      cases j with
      | inl j =>
          have hij : label i.1 = label j.1 :=
            i.property.trans j.property.symm
          simp [Matrix.reindex_apply, partitionPinch, partitionBlock,
            principalGramBlock, hij]
      | inr j =>
          have hij : label i.1 ≠ label j.1 := by
            intro h
            have hbad : false = true := i.property.symm.trans (h.trans j.property)
            exact Bool.false_ne_true hbad
          simp [Matrix.reindex_apply, partitionPinch, partitionBlock,
            principalGramBlock, hij]
  | inr i =>
      cases j with
      | inl j =>
          have hij : label i.1 ≠ label j.1 := by
            intro h
            have hbad : false = true := j.property.symm.trans (h.symm.trans i.property)
            exact Bool.false_ne_true hbad
          simp [Matrix.reindex_apply, partitionPinch, partitionBlock,
            principalGramBlock, hij]
      | inr j =>
          have hij : label i.1 = label j.1 :=
            i.property.trans j.property.symm
          simp [Matrix.reindex_apply, partitionPinch, partitionBlock,
            principalGramBlock, hij]

/-- Characteristic polynomial of a Boolean pinch factors into the two
principal-block characteristic polynomials. -/
theorem twoBlockCharpolyFactorization_proved
    (label : ι → Bool) (M : Matrix ι ι ℂ) :
    (partitionPinch label M).charpoly =
      (partitionBlock label M false).charpoly *
      (partitionBlock label M true).charpoly := by
  let e := boolFiberEquiv label
  have hre :
      Matrix.reindex e e (partitionPinch label M) =
        Matrix.fromBlocks
          (partitionBlock label M false) 0 0
          (partitionBlock label M true) := by
    simpa [e] using boolPinch_reindex_eq_fromBlocks label M
  have hcp :
      (Matrix.reindex e e (partitionPinch label M)).charpoly =
        (partitionPinch label M).charpoly := by
    simpa using Matrix.charpoly_reindex e (partitionPinch label M)
  calc
    (partitionPinch label M).charpoly =
        (Matrix.reindex e e (partitionPinch label M)).charpoly := hcp.symm
    _ =
        (Matrix.fromBlocks
          (partitionBlock label M false) 0 0
          (partitionBlock label M true)).charpoly := by
            rw [hre]
    _ =
        (partitionBlock label M false).charpoly *
          (partitionBlock label M true).charpoly := by
            simp

end BoolReindex

/-! ## Direct-sum defect additivity and binary pinching -/

section BoolBlocks

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- The Gram defect of the Boolean pinched matrix is exactly the sum of the
defects of its two principal blocks. -/
theorem blockDiagonalDefectAdditivity_bool_proved
    (label : ι → Bool) (M : Matrix ι ι ℂ) (hM : M.PosSemidef) :
    BlockDiagonalDefectAdditivity M hM label := by
  intro hPM
  let hfalse :
      (partitionBlock label M false).PosSemidef :=
    principal_submatrix_posSemidef M hM
      (fun i : BlockFiber label false => i.1)
  let htrue :
      (partitionBlock label M true).PosSemidef :=
    principal_submatrix_posSemidef M hM
      (fun i : BlockFiber label true => i.1)

  have hadd :=
    rootsPsiSum_add_of_charpoly_mul
      (partitionBlock label M false)
      (partitionBlock label M true)
      (partitionPinch label M)
      (twoBlockCharpolyFactorization_proved label M)

  have hPMbridge :=
    rootsPsiGramBridge_proved (partitionPinch label M) hPM
  have hFbridge :=
    rootsPsiGramBridge_proved (partitionBlock label M false) hfalse
  have hTbridge :=
    rootsPsiGramBridge_proved (partitionBlock label M true) htrue

  rw [hPMbridge, hFbridge, hTbridge] at hadd
  rw [Fintype.sum_bool]
  exact Eq.trans hadd (add_comm _ _)

/-- Complete Boolean Gram-defect pinching theorem. -/
theorem gramDefectPinching_bool_proved
    (label : ι → Bool) (M : Matrix ι ι ℂ) (hM : M.PosSemidef) :
    GramDefectPinchingPartition M hM label := by
  exact gramDefectPinchingPartition_of_standard_facts M hM label
    (spectralGramPinching_bool_proved label M hM)
    (blockDiagonalDefectAdditivity_bool_proved label M hM)

end BoolBlocks

end HurtadoZeta23
