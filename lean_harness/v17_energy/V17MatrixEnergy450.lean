import HurtadoZeta23.V17PairBandReindexCore
import HurtadoZeta23.MatrixEnergy
import Mathlib.Tactic

noncomputable section

open Matrix Finset
open scoped BigOperators ComplexOrder

set_option linter.constructorNameAsVariable false

namespace HurtadoZeta23

/-!
# Pure finite 450-by-450 matrix energy

This module contains only finite reindexing.  It identifies the natural pair
energy with the directed off-diagonal matrix energy and has no retained-column,
zeta, compact-overlap, or historical block-length dependencies.
-/

/-- Ordered off-diagonal pairs of `Fin m`. -/
def v17OffDiagonalPairsFin (m : ℕ) : Finset (Fin m × Fin m) :=
  (Finset.univ ×ˢ Finset.univ).filter (fun p => p.1 ≠ p.2)

/-- Strict upper triangle of `Fin m`. -/
def v17StrictUpperPairsFin (m : ℕ) : Finset (Fin m × Fin m) :=
  (Finset.univ ×ˢ Finset.univ).filter (fun p => p.1 < p.2)

/-- Strict lower triangle of `Fin m`. -/
def v17StrictLowerPairsFin (m : ℕ) : Finset (Fin m × Fin m) :=
  (Finset.univ ×ˢ Finset.univ).filter (fun p => p.2 < p.1)

/-- The nested off-diagonal energy is a single ordered pair sum. -/
theorem v17_offDiagonalEnergy_eq_pairSum
    (m : ℕ) (G : Matrix (Fin m) (Fin m) ℂ) :
    offDiagonalEnergy G =
      ∑ p ∈ v17OffDiagonalPairsFin m, ‖G p.1 p.2‖ ^ 2 := by
  unfold offDiagonalEnergy
  symm
  apply
    Finset.sum_finset_product'
      (r := v17OffDiagonalPairsFin m)
      (s := Finset.univ)
      (t := fun i => Finset.univ.erase i)
      (f := fun i j => ‖G i j‖ ^ 2)
  intro p
  simp only [
    v17OffDiagonalPairsFin,
    Finset.mem_filter,
    Finset.mem_product,
    Finset.mem_univ,
    true_and,
    Finset.mem_erase
  ]
  constructor
  · intro hp
    exact ⟨hp.symm, trivial⟩
  · rintro ⟨hp, _⟩
    exact hp.symm

/-- Every ordered off-diagonal pair lies in exactly one strict triangle. -/
theorem v17_offDiagonalPairsFin_eq_upper_union_lower
    (m : ℕ) :
    v17OffDiagonalPairsFin m =
      v17StrictUpperPairsFin m ∪ v17StrictLowerPairsFin m := by
  ext p
  simp only [
    v17OffDiagonalPairsFin,
    v17StrictUpperPairsFin,
    v17StrictLowerPairsFin,
    Finset.mem_filter,
    Finset.mem_product,
    Finset.mem_univ,
    true_and,
    Finset.mem_union
  ]
  constructor
  · intro hne
    exact lt_or_gt_of_ne hne
  · rintro (hlt | hgt)
    · exact ne_of_lt hlt
    · exact ne_of_gt hgt

/-- The strict upper and lower triangles are disjoint. -/
theorem v17_strictUpperPairsFin_disjoint_lower
    (m : ℕ) :
    Disjoint (v17StrictUpperPairsFin m) (v17StrictLowerPairsFin m) := by
  apply Finset.disjoint_left.2
  intro p hpU hpL
  simp only [
    v17StrictUpperPairsFin,
    v17StrictLowerPairsFin,
    Finset.mem_filter,
    Finset.mem_product,
    Finset.mem_univ,
    true_and
  ] at hpU hpL
  exact (not_lt_of_ge (le_of_lt hpU)) hpL

/-- For a symmetric weight, lower- and upper-triangle sums coincide. -/
theorem v17_sum_strictLower_eq_sum_strictUpper_of_comm
    (m : ℕ) (w : Fin m → Fin m → ℝ)
    (hcomm : ∀ i j, w i j = w j i) :
    (∑ p ∈ v17StrictLowerPairsFin m, w p.1 p.2) =
      ∑ p ∈ v17StrictUpperPairsFin m, w p.1 p.2 := by
  apply Finset.sum_bij (fun p hp => (p.2, p.1))
  · intro p hp
    simp only [
      v17StrictLowerPairsFin,
      v17StrictUpperPairsFin,
      Finset.mem_filter,
      Finset.mem_product,
      Finset.mem_univ,
      true_and,
      Prod.fst,
      Prod.snd
    ] at hp ⊢
    exact hp
  · intro p₁ hp₁ p₂ hp₂ h
    apply Prod.ext
    · exact congrArg Prod.snd h
    · exact congrArg Prod.fst h
  · intro q hq
    refine ⟨(q.2, q.1), ?_, ?_⟩
    · simp only [
        v17StrictLowerPairsFin,
        v17StrictUpperPairsFin,
        Finset.mem_filter,
        Finset.mem_product,
        Finset.mem_univ,
        true_and,
        Prod.fst,
        Prod.snd
      ] at hq ⊢
      exact hq
    · rfl
  · intro p hp
    exact hcomm p.1 p.2

/-- For a symmetric weight, the ordered off-diagonal sum is twice the strict
upper-triangle sum. -/
theorem v17_sum_offDiagonalPairs_eq_two_mul_upper_of_comm
    (m : ℕ) (w : Fin m → Fin m → ℝ)
    (hcomm : ∀ i j, w i j = w j i) :
    (∑ p ∈ v17OffDiagonalPairsFin m, w p.1 p.2) =
      2 * ∑ p ∈ v17StrictUpperPairsFin m, w p.1 p.2 := by
  rw [v17_offDiagonalPairsFin_eq_upper_union_lower]
  rw [Finset.sum_union (v17_strictUpperPairsFin_disjoint_lower m)]
  rw [v17_sum_strictLower_eq_sum_strictUpper_of_comm m w hcomm]
  ring

/-- Totalized squared matrix entry on natural indices. -/
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
    (∑ p ∈ v17StrictUpperPairsFin 450, ‖G p.1 p.2‖ ^ 2) =
      v17StrictUpperPairEnergyNat 450 (v17MatrixNormSqNat450 G) := by
  unfold v17StrictUpperPairEnergyNat
  apply Finset.sum_bij (fun p hp => (p.1.1, p.2.1))
  · intro p hp
    simp only [
      v17StrictUpperPairsFin,
      v17StrictUpperPairsNat,
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
      v17StrictUpperPairsNat,
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
        v17StrictUpperPairsFin,
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

/-- For any Hermitian-style symmetric squared-entry weight, the natural pair
energy equals directed off-diagonal energy exactly. -/
theorem v17_globalPairEnergyNat_matrixNormSq450_eq_offDiagonalEnergy
    (G : Matrix (Fin 450) (Fin 450) ℂ)
    (hcomm : ∀ i j, ‖G i j‖ ^ 2 = ‖G j i‖ ^ 2) :
    globalPairEnergyNat 450 (v17MatrixNormSqNat450 G) =
      offDiagonalEnergy G := by
  rw [v17_globalPairEnergyNat_eq_two_mul_strictUpper]
  rw [← v17_strictUpperMatrixEnergy_eq_strictUpperPairEnergyNat450 G]
  rw [v17_offDiagonalEnergy_eq_pairSum]
  symm
  exact
    v17_sum_offDiagonalPairs_eq_two_mul_upper_of_comm
      450 (fun i j => ‖G i j‖ ^ 2) hcomm

end HurtadoZeta23
