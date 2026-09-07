import HurtadoZeta23.GramPairEnergyIdentity
import HurtadoZeta23.V17AnalyticBridge450
import Mathlib.Tactic

noncomputable section

open Matrix Finset
open scoped BigOperators ComplexOrder

namespace HurtadoZeta23

/-!
# Exact finite Gram-energy identity for v17 length 450

This file closes the purely finite seam between the natural-number pair-band
energy used by the local certificate and the directed off-diagonal Frobenius
energy used by the spectral argument.
-/

/-- Totalized squared matrix entry on natural indices.  The pair-energy
machinery only samples the branch `a,b<450`. -/
def v17MatrixNormSqNat450
    (G : Matrix (Fin 450) (Fin 450) ℂ)
    (a b : ℕ) : ℝ :=
  if ha : a < 450 then
    if hb : b < 450 then
      ‖G ⟨a, ha⟩ ⟨b, hb⟩‖ ^ 2
    else 0
  else 0

/-- The strict upper triangle of a `Fin 450` matrix is exactly the natural
strict-upper pair energy of its totalized squared entries. -/
theorem v17_strictUpperMatrixEnergy_eq_strictUpperPairEnergyNat450
    (G : Matrix (Fin 450) (Fin 450) ℂ) :
    (∑ p ∈ strictUpperPairsFin 450, ‖G p.1 p.2‖ ^ 2)
      =
    strictUpperPairEnergyNat 450 (v17MatrixNormSqNat450 G) := by
  unfold strictUpperPairEnergyNat
  apply
    Finset.sum_bij
      (fun p hp => (p.1.1, p.2.1))

  · intro p hp
    simp only [
      strictUpperPairsFin,
      strictUpperPairsNat,
      Finset.mem_filter,
      Finset.mem_product,
      Finset.mem_univ,
      Finset.mem_range,
      true_and,
      Prod.fst,
      Prod.snd
    ] at hp ⊢
    exact ⟨⟨p.1.2, p.2.2⟩, hp⟩

  · intro p₁ hp₁ p₂ hp₂ h
    apply Prod.ext
    · apply Fin.ext
      exact congrArg Prod.fst h
    · apply Fin.ext
      exact congrArg Prod.snd h

  · intro q hq
    simp only [
      strictUpperPairsNat,
      Finset.mem_filter,
      Finset.mem_product,
      Finset.mem_range,
      Prod.fst,
      Prod.snd
    ] at hq
    rcases hq with ⟨⟨ha, hb⟩, hab⟩
    let i : Fin 450 := ⟨q.1, ha⟩
    let j : Fin 450 := ⟨q.2, hb⟩
    refine ⟨(i, j), ?_, ?_⟩
    · simp only [
        strictUpperPairsFin,
        Finset.mem_filter,
        Finset.mem_product,
        Finset.mem_univ,
        true_and,
        i,
        j
      ]
      exact hab
    · apply Prod.ext <;> rfl

  · intro p hp
    simp [v17MatrixNormSqNat450, p.1.2, p.2.2]

/-- For any 450-by-450 matrix with symmetric squared entry norms, natural
pair-band energy equals directed off-diagonal energy exactly. -/
theorem v17_globalPairEnergyNat_matrixNormSq450_eq_offDiagonalEnergy
    (G : Matrix (Fin 450) (Fin 450) ℂ)
    (hcomm : ∀ i j, ‖G i j‖ ^ 2 = ‖G j i‖ ^ 2) :
    globalPairEnergyNat 450 (v17MatrixNormSqNat450 G)
      = offDiagonalEnergy G := by
  rw [globalPairEnergyNat_eq_two_mul_strictUpper]
  rw [← v17_strictUpperMatrixEnergy_eq_strictUpperPairEnergyNat450 G]
  rw [offDiagonalEnergy_eq_pairSum]
  symm
  exact
    sum_offDiagonalPairs_eq_two_mul_upper_of_comm
      450
      (fun i j => ‖G i j‖ ^ 2)
      hcomm

/-- Squared entry norms of the actual v17 principal Gram block are symmetric,
as a direct consequence of Hermitianity. -/
theorem v17Gram450_norm_sq_comm
    (T : ℝ)
    (s : ℕ)
    (hs : s + 450 ≤ articleRetainedCard T)
    (i j : Fin 450) :
    ‖v17Gram450 T s hs i j‖ ^ 2
      = ‖v17Gram450 T s hs j i‖ ^ 2 := by
  have hPSD : (v17Gram450 T s hs).PosSemidef := by
    unfold v17Gram450
    exact
      principal_submatrix_posSemidef
        (articleGlobalSimpleGram T)
        (articleGlobalSimpleGram_posSemidef T)
        (v17SimpleColumn450 T s hs)
  have hHerm : (v17Gram450 T s hs).IsHermitian := hPSD.isHermitian
  calc
    ‖v17Gram450 T s hs i j‖ ^ 2
        = ‖star (v17Gram450 T s hs j i)‖ ^ 2 := by
            rw [(hHerm.apply i j).symm]
    _ = ‖v17Gram450 T s hs j i‖ ^ 2 := by simp

/-- Exact structural identity for the actual 450-point principal Gram block. -/
theorem v17_globalPairEnergyNat_Gram450_eq_offDiagonalEnergy
    (T : ℝ)
    (s : ℕ)
    (hs : s + 450 ≤ articleRetainedCard T) :
    globalPairEnergyNat 450
        (v17MatrixNormSqNat450 (v17Gram450 T s hs))
      =
    offDiagonalEnergy (v17Gram450 T s hs) := by
  exact
    v17_globalPairEnergyNat_matrixNormSq450_eq_offDiagonalEnergy
      (v17Gram450 T s hs)
      (v17Gram450_norm_sq_comm T s hs)

/-- Analytic compact-overlap control plus the exact finite pair reindexing gives
the off-diagonal energy lower bound needed by the spectral step. -/
theorem v17_Gram450_kernel_pair_energy_lower_offDiagonal
    {T : ℝ}
    (hPois : Zeta23.ZeroSide.PoissonSq T (articleParams.atD T))
    (hnorm :
      0 <
        (articleParams.atD T).a T *
          (articleParams.atD T).L T ^ 2)
    (hl : 0 < Zeta23.l T)
    (hwL : 8 * articleParams.w ≤ articleParams.L T)
    (hsmall :
      4 * articleParams.w / articleParams.L T
        ≤ limitingK 0 / 2)
    {M : ℕ}
    (hM1 : 1 ≤ M)
    (hM2 : (M : ℝ) + 2 ≤ (Zeta23.l T) ^ 2)
    (hkk : (0 : ℤ) ≤ articleLastGridIndex T)
    (s : ℕ)
    (hs : s + 450 ≤ articleRetainedCard T) :
    globalPairEnergyNat 450 (limitingWeightOnPoints (v17Y450 T s hs)) -
        404100 * articleCompactError T M
      ≤
    offDiagonalEnergy (v17Gram450 T s hs) := by
  have h :=
    v17_Gram450_global_pair_energy_lower
      hPois hnorm hl hwL hsmall hM1 hM2 hkk s hs
  change
    globalPairEnergyNat 450 (limitingWeightOnPoints (v17Y450 T s hs)) -
        404100 * articleCompactError T M
      ≤
    globalPairEnergyNat 450
      (v17MatrixNormSqNat450 (v17Gram450 T s hs)) at h
  rw [v17_globalPairEnergyNat_Gram450_eq_offDiagonalEnergy T s hs] at h
  exact h

end HurtadoZeta23
