import HurtadoZeta23.PairBandReindex
import Mathlib.Tactic

noncomputable section

open Matrix Finset
open scoped BigOperators ComplexOrder

namespace HurtadoZeta23

/-!
# Gram pair-energy identity

This file closes the remaining structural `hGram` interface.

For a symmetric real Gram block:

1. `offDiagonalEnergy` is the sum over all ordered off-diagonal pairs;
2. the ordered off-diagonal pairs split into strict upper and strict lower
   triangles;
3. symmetry identifies the lower-triangle sum with the upper-triangle sum;
4. `PairBandReindex` identifies `globalPairEnergyNat` with twice the strict
   upper-triangle sum.

Hence the two energies are exactly equal.
-/

/-- Ordered off-diagonal pairs of `Fin m`. -/
def offDiagonalPairsFin (m : ℕ) : Finset (Fin m × Fin m) :=
  (Finset.univ ×ˢ Finset.univ).filter (fun p => p.1 ≠ p.2)

/-- Strict upper triangle of `Fin m`. -/
def strictUpperPairsFin (m : ℕ) : Finset (Fin m × Fin m) :=
  (Finset.univ ×ˢ Finset.univ).filter (fun p => p.1 < p.2)

/-- Strict lower triangle of `Fin m`. -/
def strictLowerPairsFin (m : ℕ) : Finset (Fin m × Fin m) :=
  (Finset.univ ×ˢ Finset.univ).filter (fun p => p.2 < p.1)

/-- The nested definition of off-diagonal energy is a single pair sum. -/
theorem offDiagonalEnergy_eq_pairSum
    (m : ℕ)
    (G : Matrix (Fin m) (Fin m) ℂ) :
    offDiagonalEnergy G
      =
    ∑ p ∈ offDiagonalPairsFin m, ‖G p.1 p.2‖ ^ 2 := by

  unfold offDiagonalEnergy

  symm

  apply
    Finset.sum_finset_product'
      (r := offDiagonalPairsFin m)
      (s := Finset.univ)
      (t := fun i => Finset.univ.erase i)
      (f := fun i j => ‖G i j‖ ^ 2)

  intro p

  simp only [
    offDiagonalPairsFin,
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
theorem offDiagonalPairsFin_eq_upper_union_lower
    (m : ℕ) :
    offDiagonalPairsFin m
      =
    strictUpperPairsFin m ∪ strictLowerPairsFin m := by

  ext p

  simp only [
    offDiagonalPairsFin,
    strictUpperPairsFin,
    strictLowerPairsFin,
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
theorem strictUpperPairsFin_disjoint_lower
    (m : ℕ) :
    Disjoint (strictUpperPairsFin m) (strictLowerPairsFin m) := by

  apply Finset.disjoint_left.2

  intro p hpU hpL

  simp only [
    strictUpperPairsFin,
    strictLowerPairsFin,
    Finset.mem_filter,
    Finset.mem_product,
    Finset.mem_univ,
    true_and
  ] at hpU hpL

  exact (not_lt_of_ge (le_of_lt hpU)) hpL

/--
For a symmetric weight, the strict lower-triangle sum equals the strict
upper-triangle sum.
-/
theorem sum_strictLower_eq_sum_strictUpper_of_comm
    (m : ℕ)
    (w : Fin m → Fin m → ℝ)
    (hcomm : ∀ i j, w i j = w j i) :
    (∑ p ∈ strictLowerPairsFin m, w p.1 p.2)
      =
    ∑ p ∈ strictUpperPairsFin m, w p.1 p.2 := by

  apply
    Finset.sum_bij
      (fun p hp => (p.2, p.1))

  · intro p hp

    simp only [
      strictLowerPairsFin,
      strictUpperPairsFin,
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
        strictLowerPairsFin,
        strictUpperPairsFin,
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

/--
For a symmetric weight, the ordered off-diagonal sum is twice the strict
upper-triangle sum.
-/
theorem sum_offDiagonalPairs_eq_two_mul_upper_of_comm
    (m : ℕ)
    (w : Fin m → Fin m → ℝ)
    (hcomm : ∀ i j, w i j = w j i) :
    (∑ p ∈ offDiagonalPairsFin m, w p.1 p.2)
      =
    2 * ∑ p ∈ strictUpperPairsFin m, w p.1 p.2 := by

  rw [offDiagonalPairsFin_eq_upper_union_lower]

  rw [
    Finset.sum_union
      (strictUpperPairsFin_disjoint_lower m)
  ]

  rw [sum_strictLower_eq_sum_strictUpper_of_comm m w hcomm]

  ring

set_option linter.constructorNameAsVariable false

/--
The strict upper triangle of the actual Gram block is exactly the natural
strict-upper pair energy of `consecutiveGramOverlapNat`.
-/
theorem strictUpperGramEnergy_eq_strictUpperPairEnergyNat
    (T : ℝ)
    (s : ℕ)
    (hs : s + blockLength ≤ articleRetainedCard T) :
    (∑ p ∈ strictUpperPairsFin blockLength,
        ‖consecutiveGramBlock T s hs p.1 p.2‖ ^ 2)
      =
    strictUpperPairEnergyNat blockLength
      (fun a b => consecutiveGramOverlapNat T s hs a b ^ 2) := by

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

    let i : Fin blockLength := ⟨q.1, ha⟩
    let j : Fin blockLength := ⟨q.2, hb⟩

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

    have ha : p.1.1 < blockLength := p.1.2
    have hb : p.2.1 < blockLength := p.2.2

    symm

    exact
      consecutiveGramOverlapNat_sq_eq_norm_sq
        T s hs ha hb

set_option linter.constructorNameAsVariable true

/--
The real Gram weight is symmetric.
-/
theorem consecutiveGramNormSq_comm
    (T : ℝ)
    (s : ℕ)
    (hs : s + blockLength ≤ articleRetainedCard T)
    (i j : Fin blockLength) :
    ‖consecutiveGramBlock T s hs i j‖ ^ 2
      =
    ‖consecutiveGramBlock T s hs j i‖ ^ 2 := by

  rw [consecutiveGramBlock_apply_comm T s hs i j]

/--
Exact structural identity required as `hGram` by the uniform block theorem.
-/
theorem globalPairEnergyNat_consecutiveGramOverlap_eq_offDiagonalEnergy
    (T : ℝ)
    (s : ℕ)
    (hs : s + blockLength ≤ articleRetainedCard T) :
    globalPairEnergyNat blockLength
        (fun a b => consecutiveGramOverlap T s hs a b ^ 2)
      =
    offDiagonalEnergy (consecutiveGramBlock T s hs) := by

  rw [globalPairEnergyNat_consecutiveGramOverlap_eq_nat]

  rw [
    globalPairEnergyNat_eq_two_mul_strictUpper
      blockLength
      (fun a b => consecutiveGramOverlapNat T s hs a b ^ 2)
  ]

  rw [← strictUpperGramEnergy_eq_strictUpperPairEnergyNat T s hs]

  rw [offDiagonalEnergy_eq_pairSum]

  symm

  exact
    sum_offDiagonalPairs_eq_two_mul_upper_of_comm
      blockLength
      (fun i j => ‖consecutiveGramBlock T s hs i j‖ ^ 2)
      (consecutiveGramNormSq_comm T s hs)

end HurtadoZeta23
