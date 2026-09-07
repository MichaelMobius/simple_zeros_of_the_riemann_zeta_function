import HurtadoZeta23.MatrixEnergy
import HurtadoZeta23.BlockDefect
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Tactic

noncomputable section

namespace HurtadoZeta23

open scoped ComplexOrder BigOperators

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Spectral square deviation from the identity. -/
def spectralDeviationSq
    {G : Matrix n n ℂ}
    (hG : G.IsHermitian) : ℝ :=
  ∑ i : n, (hG.eigenvalues i - 1)^2

/--
On the small-spectrum branch, the scalar defect sum is exactly the
spectral square deviation. This part is purely scalar.
-/
lemma sum_psi_eq_spectralDeviationSq_of_le_two
    {G : Matrix n n ℂ}
    (hG : G.IsHermitian)
    (hsmall : ∀ i : n, hG.eigenvalues i ≤ 2) :
    (∑ i : n, psi (hG.eigenvalues i))
      =
    spectralDeviationSq hG := by
  unfold spectralDeviationSq
  apply Finset.sum_congr rfl
  intro i hi
  exact psi_eq_sq (hsmall i)

/--
The exact remaining unitary-invariance statement.

It says that the entrywise Frobenius square of `G - I` equals the sum of
squared deviations of the Hermitian eigenvalues.
-/
def FrobeniusSpectralIdentity
    (G : Matrix n n ℂ)
    (hG : G.IsHermitian) : Prop :=
  frobeniusDeviationSq G = spectralDeviationSq hG

/--
The small-spectrum bridge is derived from the unconditional
Frobenius spectral identity.
-/
lemma small_frobenius_from_spectral_identity
    (G : Matrix n n ℂ)
    (hG : G.IsHermitian)
    {D : ℝ}
    (hD :
      D = ∑ i : n, psi (hG.eigenvalues i))
    (hFS :
      FrobeniusSpectralIdentity G hG)
    (hsmall :
      ∀ i : n, hG.eigenvalues i ≤ 2) :
    D = frobeniusDeviationSq G := by
  rw [hD]
  rw [sum_psi_eq_spectralDeviationSq_of_le_two hG hsmall]
  exact hFS.symm

/--
Matrix-level Block defect reduced to the standard spectral/Frobenius
identity.

All `psi` case splitting and PSD eigenvalue positivity are internal to the
previous Block-defect layer.
-/
theorem block_defect_matrix_from_frobenius_spectral
    (G : Matrix n n ℂ)
    (hG : G.IsHermitian)
    (hPSD : G.PosSemidef)
    {D : ℝ}
    (hD :
      D = ∑ i : n, psi (hG.eigenvalues i))
    (hFS :
      FrobeniusSpectralIdentity G hG) :
    min 1 (offDiagonalEnergy G) ≤ D := by
  apply block_defect_matrix_core
      G
      hG
      hPSD
      hD

  intro hsmall

  exact
    small_frobenius_from_spectral_identity
      G
      hG
      hD
      hFS
      hsmall

/--
Once the standard Frobenius spectral identity is available, the exact
Block-defect inequality used by the paper follows for any Hermitian PSD Gram
matrix.
-/
theorem block_defect_of_frobenius_spectral
    (G : Matrix n n ℂ)
    (hG : G.IsHermitian)
    (hPSD : G.PosSemidef)
    (hFS :
      FrobeniusSpectralIdentity G hG) :
    min 1 (offDiagonalEnergy G)
      ≤
    ∑ i : n, psi (hG.eigenvalues i) := by

  exact
    block_defect_matrix_from_frobenius_spectral
      G
      hG
      hPSD
      rfl
      hFS

end HurtadoZeta23
