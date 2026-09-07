import HurtadoZeta23.GramPinchingConvex
import HurtadoZeta23.RootMultisetGramBridge
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Tactic

noncomputable section

open Matrix Finset
open scoped ComplexOrder

universe u

namespace HurtadoZeta23

/-!
# Spectral invariance for two-block sign conjugation

This file proves that the diagonal ±1 sign conjugation used in the
two-block pinching argument preserves positive semidefiniteness and the
Gram spectral defect.

The proof is deliberately based on Mathlib's diagonal-matrix identities,
rather than expanding matrix products as finite sums.
-/

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- Diagonal ±1 matrix implementing the two-block sign conjugation. -/
def signDiagonal (label : ι → Bool) : Matrix ι ι ℂ :=
  Matrix.diagonal (blockSign label)

/-- Entrywise form of the sign diagonal. -/
@[simp] theorem signDiagonal_apply
    (label : ι → Bool) (i j : ι) :
    signDiagonal label i j = if i = j then blockSign label i else 0 := by
  by_cases hij : i = j
  · subst j
    simp [signDiagonal]
  · have hji : j ≠ i := by
      intro h
      exact hij h.symm
    simp [signDiagonal, hij, hji]

/-- The sign diagonal is an involution. -/
theorem signDiagonal_mul_self (label : ι → Bool) :
    signDiagonal label * signDiagonal label = 1 := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [signDiagonal, blockSign_sq]
  · have hji : j ≠ i := by
      intro h
      exact hij h.symm
    simp [signDiagonal, hij, hji]

/-- Entrywise sign conjugation is ordinary conjugation by the diagonal
sign involution. -/
theorem signConjugate_eq_diagonal_mul
    (label : ι → Bool) (M : Matrix ι ι ℂ) :
    signConjugate label M =
      signDiagonal label * M * signDiagonal label := by
  ext i j
  simp [signConjugate, signDiagonal]

/-- Sign conjugation preserves the characteristic polynomial. -/
theorem signConjugate_charpoly_eq
    (label : ι → Bool) (M : Matrix ι ι ℂ) :
    (signConjugate label M).charpoly = M.charpoly := by
  rw [signConjugate_eq_diagonal_mul]
  let D : Matrix ι ι ℂ := signDiagonal label
  have hD2 : D * D = 1 := by
    simpa [D] using signDiagonal_mul_self (label := label)
  calc
    (D * M * D).charpoly = (D * (D * M)).charpoly := by
      exact Matrix.charpoly_mul_comm (D * M) D
    _ = ((D * D) * M).charpoly := by
      rw [Matrix.mul_assoc]
    _ = M.charpoly := by
      rw [hD2, Matrix.one_mul]

/-- Therefore sign conjugation preserves characteristic roots with algebraic
multiplicity. -/
theorem signConjugate_roots_eq
    (label : ι → Bool) (M : Matrix ι ι ℂ) :
    (signConjugate label M).charpoly.roots = M.charpoly.roots := by
  rw [signConjugate_charpoly_eq]

/-- The signs ±1 are fixed by complex conjugation. -/
@[simp] theorem star_blockSign
    (label : ι → Bool) (i : ι) :
    star (blockSign label i) = blockSign label i := by
  by_cases h : label i
  · simp [blockSign, h]
  · simp [blockSign, h]

/-- The diagonal sign matrix is Hermitian. -/
theorem signDiagonal_conjTranspose
    (label : ι → Bool) :
    (signDiagonal label).conjTranspose = signDiagonal label := by
  simpa [signDiagonal] using
    (Matrix.diagonal_conjTranspose (blockSign label))

/-- Congruence by the sign diagonal preserves positive semidefiniteness. -/
theorem signConjugate_posSemidef
    (label : ι → Bool) (M : Matrix ι ι ℂ)
    (hM : M.PosSemidef) :
    (signConjugate label M).PosSemidef := by
  have h := hM.mul_mul_conjTranspose_same (signDiagonal label)
  rw [signDiagonal_conjTranspose] at h
  rw [signConjugate_eq_diagonal_mul]
  exact h

/-- Characteristic-polynomial invariance plus the already-proved
root-multiset bridge gives invariance of the Gram spectral defect. -/
theorem signConjugate_defect_eq_of_posSemidef
    (label : ι → Bool) (M : Matrix ι ι ℂ)
    (hM : M.PosSemidef)
    (hU : (signConjugate label M).PosSemidef) :
    gramSpectralDefect (signConjugate label M) hU =
      gramSpectralDefect M hM := by
  have hroots :
      nonzeroHermitianEigenRoots hU.isHermitian =
        nonzeroHermitianEigenRoots hM.isHermitian := by
    rw [← nonzeroCharpolyRoots_eq_eigenvalues₀,
        ← nonzeroCharpolyRoots_eq_eigenvalues₀]
    unfold nonzeroCharpolyRoots
    rw [signConjugate_charpoly_eq]
  have hbridge :=
    rootMultisetToDefectBridge_proved
      (signConjugate label M) hU M hM hroots
  simpa [matrixSpectralDefect, gramSpectralDefect, spectralDefect,
    sum_psi_eq_support_plus_zeros] using hbridge

/-- Sign-conjugation invariance is unconditional. -/
theorem signConjugateDefectInvariance_proved :
    SignConjugateDefectInvariance.{u} := by
  intro κ _ _ label M hM
  let hU : (signConjugate label M).PosSemidef :=
    signConjugate_posSemidef label M hM
  exact
    ⟨hU, signConjugate_defect_eq_of_posSemidef label M hM hU⟩

/-- Majorization-style midpoint Jensen interface. -/
def HermitianSpectralMidpointJensen : Prop :=
  ∀ {κ : Type u} [Fintype κ] [DecidableEq κ]
      (A B : Matrix κ κ ℂ)
      (hA : A.PosSemidef) (hB : B.PosSemidef)
      (hMid : (((2 : ℂ)⁻¹) • (A + B)).PosSemidef),
    gramSpectralDefect (((2 : ℂ)⁻¹) • (A + B)) hMid
      ≤ (gramSpectralDefect A hA + gramSpectralDefect B hB) / 2

/-- The majorization-facing interface is exactly the midpoint-convexity
interface at the same universe level. -/
theorem gramDefectMidpointConvexity_of_spectralJensen
    (h : HermitianSpectralMidpointJensen.{u}) :
    GramDefectMidpointConvexity.{u} := by
  intro κ _ _ A B hA hB hMid
  exact h A B hA hB hMid

end HurtadoZeta23
