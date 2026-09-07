import HurtadoZeta23.GramPinchingVariational
import HurtadoZeta23.SpectralFrobenius
import Zeta23.LinAlg.RankTrace
import Mathlib.LinearAlgebra.Matrix.Vec
import Mathlib.Tactic

noncomputable section

open Matrix Finset
open scoped BigOperators ComplexOrder

namespace HurtadoZeta23

section FrobeniusBridge

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Project Frobenius square as the entrywise sum of squared norms.  This is
the generic part of `ConcreteBlockDefect`, isolated here so the v17 spectral
threshold does not depend on the old 262-point block assembly. -/
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

lemma v17_sub_one_apply
    (G : Matrix n n ℂ)
    (i j : n) :
    (G - (1 : Matrix n n ℂ)) i j =
      G i j - (if i = j then (1 : ℂ) else 0) := by
  simp only [Matrix.sub_apply, Matrix.one_apply]

/-- Entrywise squared distance from the identity equals the project
Frobenius norm of `G-I`. -/
theorem v17_frobeniusDeviationSq_eq_frobSq_shiftOne
    (G : Matrix n n ℂ) :
    frobeniusDeviationSq G =
      RHLinalg.frobSq (G - (1 : Matrix n n ℂ)) := by
  classical
  rw [v17_frobSq_eq_sum_norm_sq]
  unfold frobeniusDeviationSq
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [v17_sub_one_apply]

/-- Standard Hermitian Frobenius/spectral identity, isolated from all
consecutive-block machinery. -/
theorem v17_frobeniusSpectralIdentity_proved
    (G : Matrix n n ℂ)
    (hG : G.IsHermitian) :
    FrobeniusSpectralIdentity G hG := by
  unfold FrobeniusSpectralIdentity spectralDeviationSq
  rw [v17_frobeniusDeviationSq_eq_frobSq_shiftOne]
  have hspec :
      RHLinalg.specMap hG (fun x : ℝ => x - 1) =
        G - (1 : Matrix n n ℂ) := by
    simpa using (specMap_sub_const G hG 1)
  rw [← hspec]
  exact RHLinalg.frobSq_specMap hG (fun x : ℝ => x - 1)

end FrobeniusBridge

end HurtadoZeta23
