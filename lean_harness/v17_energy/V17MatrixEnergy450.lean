import HurtadoZeta23.GramPairEnergyIdentity
import Mathlib.Tactic

noncomputable section

open Matrix Finset
open scoped BigOperators ComplexOrder

namespace HurtadoZeta23

/-!
# Pure finite 450-by-450 matrix energy

This module contains only the finite reindexing needed to identify the
natural-number pair energy with the directed off-diagonal matrix energy.  It
has no zeta, retained-column, or compact-overlap dependencies.
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

end HurtadoZeta23
