import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic

noncomputable section

namespace HurtadoZeta23

open scoped BigOperators

section Frobenius

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Squared Frobenius distance from the identity, written entrywise. -/
def frobeniusDeviationSq (G : Matrix n n ℂ) : ℝ :=
  ∑ i : n, ∑ j : n,
    ‖G i j - (if i = j then (1 : ℂ) else 0)‖ ^ 2

/-- Squared diagonal deviation from the identity. -/
def diagonalDeviationSq (G : Matrix n n ℂ) : ℝ :=
  ∑ i : n, ‖G i i - 1‖ ^ 2

/-- Directed off-diagonal Frobenius energy.  For Hermitian `G` this is
`2 * ∑_{i<j} ‖G i j‖²`. -/
def offDiagonalEnergy (G : Matrix n n ℂ) : ℝ :=
  ∑ i : n, ∑ j ∈ (Finset.univ.erase i), ‖G i j‖ ^ 2

lemma diagonalDeviationSq_nonneg (G : Matrix n n ℂ) :
    0 ≤ diagonalDeviationSq G := by
  unfold diagonalDeviationSq
  positivity

lemma offDiagonalEnergy_nonneg (G : Matrix n n ℂ) :
    0 ≤ offDiagonalEnergy G := by
  unfold offDiagonalEnergy
  positivity

/-- Entrywise Frobenius decomposition into diagonal and off-diagonal parts. -/
theorem frobeniusDeviationSq_eq_diag_add_offdiag (G : Matrix n n ℂ) :
    frobeniusDeviationSq G = diagonalDeviationSq G + offDiagonalEnergy G := by
  classical
  unfold frobeniusDeviationSq diagonalDeviationSq offDiagonalEnergy
  have hrow : ∀ i : n,
      (∑ j : n, ‖G i j - (if i = j then (1 : ℂ) else 0)‖ ^ 2) =
        ‖G i i - 1‖ ^ 2 +
          ∑ j ∈ (Finset.univ.erase i), ‖G i j‖ ^ 2 := by
    intro i
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    congr 1
    · simp
    · apply Finset.sum_congr rfl
      intro j hj
      have hji : j ≠ i := Finset.ne_of_mem_erase hj
      simp [hji, Ne.symm hji]
  calc
    (∑ i : n, ∑ j : n, ‖G i j - (if i = j then (1 : ℂ) else 0)‖ ^ 2)
        = ∑ i : n, (‖G i i - 1‖ ^ 2 +
            ∑ j ∈ (Finset.univ.erase i), ‖G i j‖ ^ 2) := by
              apply Finset.sum_congr rfl
              intro i hi
              exact hrow i
    _ = (∑ i : n, ‖G i i - 1‖ ^ 2) +
          ∑ i : n, ∑ j ∈ (Finset.univ.erase i), ‖G i j‖ ^ 2 := by
            rw [Finset.sum_add_distrib]

/-- The off-diagonal energy is bounded by the full Frobenius deviation. -/
theorem offDiagonalEnergy_le_frobeniusDeviationSq (G : Matrix n n ℂ) :
    offDiagonalEnergy G ≤ frobeniusDeviationSq G := by
  rw [frobeniusDeviationSq_eq_diag_add_offdiag]
  nlinarith [diagonalDeviationSq_nonneg G]

end Frobenius

section Spectrum

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Spectral positive semidefiniteness for a complex Hermitian matrix. -/
def SpectrallyPosSemidef
    {G : Matrix n n ℂ}
    (hG : G.IsHermitian) : Prop :=
  ∀ i : n, (0 : ℝ) ≤ hG.eigenvalues i

lemma SpectrallyPosSemidef.eigenvalues_nonneg
    {G : Matrix n n ℂ}
    {hG : G.IsHermitian}
    (hPSD : SpectrallyPosSemidef hG)
    (i : n) :
    (0 : ℝ) ≤ hG.eigenvalues i :=
  hPSD i

end Spectrum

end HurtadoZeta23
