import HurtadoZeta23.PrincipalGramBlocks
import Mathlib.Tactic

noncomputable section

open Matrix Finset
open scoped ComplexOrder

namespace HurtadoZeta23

/-!
# Gram pinching by an actual partition

Version 5.0 stated the global defect inequality for an arbitrary family of
blocks.  That statement was too broad: repeated/overlapping blocks need not
satisfy the claimed sum bound.  The paper only uses disjoint block partitions.

This file fixes the interface by representing a partition with a label map
`label : ι → β`.  Its fibers are automatically disjoint and cover `ι`.
The associated pinching operator deletes cross-block entries.
-/

section Definitions

variable {ι β : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype β] [DecidableEq β]

/-- Matrix pinching associated to the partition into fibers of `label`. -/
def partitionPinch (label : ι → β) (M : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  fun i j => if label i = label j then M i j else 0

@[simp] theorem partitionPinch_apply_same
    (label : ι → β) (M : Matrix ι ι ℂ) {i j : ι}
    (h : label i = label j) :
    partitionPinch label M i j = M i j := by
  simp [partitionPinch, h]

@[simp] theorem partitionPinch_apply_cross
    (label : ι → β) (M : Matrix ι ι ℂ) {i j : ι}
    (h : label i ≠ label j) :
    partitionPinch label M i j = 0 := by
  simp [partitionPinch, h]

/-- The fiber of one block label. -/
abbrev BlockFiber (label : ι → β) (b : β) := {i : ι // label i = b}

/-- Principal block corresponding to one fiber of the partition. -/
def partitionBlock (label : ι → β) (M : Matrix ι ι ℂ) (b : β) :
    Matrix (BlockFiber label b) (BlockFiber label b) ℂ :=
  principalGramBlock M (fun i => i.1)

/-- On each diagonal block, pinching leaves the matrix unchanged. -/
theorem partitionBlock_of_pinch
    (label : ι → β) (M : Matrix ι ι ℂ) (b : β) :
    partitionBlock label (partitionPinch label M) b = partitionBlock label M b := by
  ext i j
  simp [partitionBlock, principalGramBlock, partitionPinch, i.property, j.property]

end Definitions

section TwoBlocks

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The ±1 phase attached to a two-block (`Bool`) partition. -/
def blockSign (label : ι → Bool) (i : ι) : ℂ :=
  if label i then 1 else -1

/-- Entrywise form of conjugation by the diagonal sign unitary. -/
def signConjugate (label : ι → Bool) (M : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  fun i j => blockSign label i * M i j * blockSign label j

@[simp] lemma blockSign_sq (label : ι → Bool) (i : ι) :
    blockSign label i * blockSign label i = 1 := by
  by_cases h : label i
  · simp [blockSign, h]
  · simp [blockSign, h]

/-- A two-block pinching is the midpoint of the matrix and its diagonal-sign
conjugate.  This is the finite-dimensional conditional-expectation formula
behind the convex pinching inequality. -/
theorem partitionPinch_bool_eq_midpoint_signConjugate
    (label : ι → Bool) (M : Matrix ι ι ℂ) :
    partitionPinch label M =
      (2 : ℂ)⁻¹ • (M + signConjugate label M) := by
  ext i j
  cases hi : label i <;> cases hj : label j <;>
    simp [partitionPinch, signConjugate, blockSign, hi, hj] <;> ring

end TwoBlocks

section CorrectPinchingInterface

variable {ι β : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype β] [DecidableEq β]

/-- Standard spectral pinching inequality in the exact form needed here.
Unlike the v5.0 interface, the blocks are the disjoint fibers of `label`. -/
def SpectralGramPinching
    (M : Matrix ι ι ℂ) (hM : M.PosSemidef) (label : ι → β) : Prop :=
  ∃ hPM : (partitionPinch label M).PosSemidef,
    gramSpectralDefect (partitionPinch label M) hPM ≤ gramSpectralDefect M hM

/-- Standard direct-sum additivity of the spectral defect for the block
matrix produced by pinching. -/
def BlockDiagonalDefectAdditivity
    (M : Matrix ι ι ℂ) (hM : M.PosSemidef) (label : ι → β) : Prop :=
  ∀ hPM : (partitionPinch label M).PosSemidef,
    gramSpectralDefect (partitionPinch label M) hPM =
      ∑ b : β,
        gramSpectralDefect
          (partitionBlock label M b)
          (principal_submatrix_posSemidef M hM (fun i : BlockFiber label b => i.1))

/-- **Corrected Gram-defect pinching statement.**  The sum is over an actual
partition (the fibers of `label`), so overlapping/repeated blocks are excluded
by construction. -/
def GramDefectPinchingPartition
    (M : Matrix ι ι ℂ) (hM : M.PosSemidef) (label : ι → β) : Prop :=
  (∑ b : β,
      gramSpectralDefect
        (partitionBlock label M b)
        (principal_submatrix_posSemidef M hM (fun i : BlockFiber label b => i.1)))
    ≤ gramSpectralDefect M hM

/-- The corrected block inequality follows immediately from spectral pinching
plus direct-sum additivity.  This theorem isolates the two standard
matrix-analysis facts still to be discharged. -/
theorem gramDefectPinchingPartition_of_standard_facts
    (M : Matrix ι ι ℂ) (hM : M.PosSemidef) (label : ι → β)
    (hpinch : SpectralGramPinching M hM label)
    (hadd : BlockDiagonalDefectAdditivity M hM label) :
    GramDefectPinchingPartition M hM label := by
  rcases hpinch with ⟨hPM, hle⟩
  unfold GramDefectPinchingPartition
  rw [← hadd hPM]
  exact hle

end CorrectPinchingInterface

end HurtadoZeta23
