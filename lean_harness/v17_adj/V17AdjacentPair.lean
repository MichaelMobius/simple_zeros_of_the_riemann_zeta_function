import HurtadoZeta23.GramPinchingFinitePartition
import Mathlib.LinearAlgebra.Matrix.Vec
import Mathlib.Tactic

noncomputable section

open Matrix Finset
open scoped BigOperators ComplexOrder

namespace HurtadoZeta23

/-!
# v17 adjacent-pair spectral defect

This module supplies the matrix-theoretic ingredient used by the v17
pressure-preserving refinement.  The first closed lemma identifies the defect
of a PSD 2-by-2 Gram block with twice its off-diagonal squared norm.
-/

section Frobenius

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Entrywise formula for the project Frobenius square. -/
theorem v17_frobSq_eq_sum_norm_sq
    (A : Matrix n n ℂ) :
    RHLinalg.frobSq A = ∑ i : n, ∑ j : n, ‖A i j‖ ^ 2 := by
  classical
  unfold RHLinalg.frobSq
  rw [← Matrix.star_vec_dotProduct_vec A A]
  unfold dotProduct
  rw [map_sum]
  simp only [Pi.star_apply, RCLike.star_def, RCLike.conj_mul]
  rw [Fintype.sum_prod_type]
  simp only [Matrix.vec]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  exact RCLike.re_ofReal_pow (K := ℂ) (‖A i j‖) 2

end Frobenius

section TwoByTwo

/-- A PSD 2-by-2 matrix with diagonal one has all eigenvalues in `[0,2]`. -/
theorem v17_fin2_eigenvalue_le_two
    (M : Matrix (Fin 2) (Fin 2) ℂ)
    (hM : M.PosSemidef)
    (h00 : M 0 0 = 1)
    (h11 : M 1 1 = 1) :
    ∀ i : Fin 2, hM.isHermitian.eigenvalues i ≤ 2 := by
  have htrace : RHLinalg.rtrace M = 2 := by
    unfold RHLinalg.rtrace Matrix.trace
    simp [Fin.sum_univ_two, h00, h11]
  have hsum : ∑ i : Fin 2, hM.isHermitian.eigenvalues i = 2 := by
    rw [← RHLinalg.rtrace_eq_sum_eigenvalues hM.isHermitian, htrace]
  have h0 := hM.eigenvalues_nonneg (0 : Fin 2)
  have h1 := hM.eigenvalues_nonneg (1 : Fin 2)
  intro i
  fin_cases i <;> simp only [Fin.sum_univ_two] at hsum <;> linarith

/-- Exact defect of a 2-by-2 Gram block. -/
theorem v17_fin2_gram_defect_eq_two_offdiag
    (M : Matrix (Fin 2) (Fin 2) ℂ)
    (hM : M.PosSemidef)
    (h00 : M 0 0 = 1)
    (h11 : M 1 1 = 1) :
    gramSpectralDefect M hM = 2 * ‖M 0 1‖ ^ 2 := by
  have hle := v17_fin2_eigenvalue_le_two M hM h00 h11
  have hle0 : ∀ k : Fin 2, hM.isHermitian.eigenvalues₀ k ≤ 2 := by
    intro k
    rw [← RHLinalg.eigenvalues_eigEquiv hM.isHermitian k]
    exact hle _
  have habove : aboveTwoSpectralEnergy M hM = 0 := by
    unfold aboveTwoSpectralEnergy aboveTwo
    apply Finset.sum_eq_zero
    intro k hk
    have hk2 : hM.isHermitian.eigenvalues₀ k - 2 ≤ 0 := by
      linarith [hle0 k]
    rw [max_eq_right hk2]
    norm_num
  have h10 : ‖M 1 0‖ = ‖M 0 1‖ := by
    have hherm := hM.isHermitian.apply (0 : Fin 2) (1 : Fin 2)
    have hn := congrArg norm hherm
    simpa using hn
  rw [gramSpectralDefect_eq_centered_sub_aboveTwo M hM, habove, sub_zero]
  rw [centeredSpectralEnergy_eq_frobSq_shiftOne M hM]
  rw [v17_frobSq_eq_sum_norm_sq]
  simp only [Fin.sum_univ_two]
  simp [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, h00, h11, h10]
  ring

end TwoByTwo

end HurtadoZeta23
