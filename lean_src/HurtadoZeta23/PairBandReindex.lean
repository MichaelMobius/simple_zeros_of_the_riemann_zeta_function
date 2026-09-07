import HurtadoZeta23.ConsecutiveGramOverlapBridge
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic

noncomputable section

open Finset
open scoped BigOperators

namespace HurtadoZeta23

/-!
# Pair-band reindexing

The diagonal-band coordinates used by `globalPairEnergyNat`

`(r0, a) ↦ (a, a + r0 + 1)`

parametrize the strict upper triangle `0 ≤ a < b < m` exactly once.

This file proves that statement independently of any matrix.  The later Gram
bridge therefore only has to identify twice the strict-upper-triangle energy
with the directed off-diagonal Frobenius energy.
-/

/-- Admissible `(separation-1, left endpoint)` indices for all pair bands. -/
def bandIndexPairs (m : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (m - 1)) ×ˢ (Finset.range m)).filter
    (fun p => p.2 < m - (p.1 + 1))

/-- Natural-number strict upper triangle below `m`. -/
def strictUpperPairsNat (m : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range m) ×ˢ (Finset.range m)).filter
    (fun p => p.1 < p.2)

/-- Sum of a weight over the strict upper triangle. -/
def strictUpperPairEnergyNat
    (m : ℕ)
    (w : ℕ → ℕ → ℝ) : ℝ :=
  ∑ p ∈ strictUpperPairsNat m, w p.1 p.2

/--
The nested band sum is the sum over the single finite set `bandIndexPairs`.
-/
theorem sum_pairBandEnergy_eq_bandIndexPairs
    (m : ℕ)
    (w : ℕ → ℕ → ℝ) :
    (∑ r0 ∈ Finset.range (m - 1), pairBandEnergy m r0 w)
      =
    ∑ p ∈ bandIndexPairs m, w p.2 (p.2 + p.1 + 1) := by

  unfold pairBandEnergy

  symm

  apply
    Finset.sum_finset_product'
      (r := bandIndexPairs m)
      (s := Finset.range (m - 1))
      (t := fun r0 => Finset.range (m - (r0 + 1)))
      (f := fun r0 a => w a (a + r0 + 1))

  intro p

  simp only [
    bandIndexPairs,
    Finset.mem_filter,
    Finset.mem_product,
    Finset.mem_range
  ]

  constructor
  · intro hp
    exact ⟨hp.1.1, hp.2⟩
  · rintro ⟨hr, ha⟩
    constructor
    · constructor
      · exact hr
      · omega
    · exact ha

/--
The band-coordinate map lands in the strict upper triangle.
-/
lemma bandToUpper_mem
    (m : ℕ)
    (p : ℕ × ℕ)
    (hp : p ∈ bandIndexPairs m) :
    (p.2, p.2 + p.1 + 1) ∈ strictUpperPairsNat m := by

  rcases p with ⟨r0, a⟩

  simp only [
    bandIndexPairs,
    strictUpperPairsNat,
    Finset.mem_filter,
    Finset.mem_product,
    Finset.mem_range,
    Prod.fst,
    Prod.snd
  ] at hp ⊢

  rcases hp with ⟨⟨hr, haM⟩, ha⟩

  constructor
  · constructor
    · exact haM
    · omega
  · omega

/--
The band-coordinate map is injective on admissible indices.
-/
lemma bandToUpper_inj
    (m : ℕ)
    (p₁ : ℕ × ℕ)
    (hp₁ : p₁ ∈ bandIndexPairs m)
    (p₂ : ℕ × ℕ)
    (hp₂ : p₂ ∈ bandIndexPairs m)
    (h :
      (p₁.2, p₁.2 + p₁.1 + 1)
        =
      (p₂.2, p₂.2 + p₂.1 + 1)) :
    p₁ = p₂ := by

  rcases p₁ with ⟨r₁, a₁⟩
  rcases p₂ with ⟨r₂, a₂⟩

  have ha :
      a₁ = a₂ :=
    congrArg Prod.fst h

  have hb :
      a₁ + r₁ + 1 = a₂ + r₂ + 1 :=
    congrArg Prod.snd h

  have hr :
      r₁ = r₂ := by
    omega

  subst a₂
  subst r₂

  rfl

/--
Every strict-upper-triangle pair has a unique band coordinate.
-/
lemma bandToUpper_surj
    (m : ℕ)
    (q : ℕ × ℕ)
    (hq : q ∈ strictUpperPairsNat m) :
    ∃ p : ℕ × ℕ,
      ∃ hp : p ∈ bandIndexPairs m,
        (p.2, p.2 + p.1 + 1) = q := by

  rcases q with ⟨a, b⟩

  simp only [
    strictUpperPairsNat,
    Finset.mem_filter,
    Finset.mem_product,
    Finset.mem_range,
    Prod.fst,
    Prod.snd
  ] at hq

  rcases hq with ⟨⟨ha, hb⟩, hab⟩

  let r0 : ℕ := b - a - 1

  have hr :
      r0 < m - 1 := by
    dsimp [r0]
    omega

  have hleft :
      a < m - (r0 + 1) := by
    dsimp [r0]
    omega

  have hp :
      (r0, a) ∈ bandIndexPairs m := by

    simp only [
      bandIndexPairs,
      Finset.mem_filter,
      Finset.mem_product,
      Finset.mem_range,
      Prod.fst,
      Prod.snd
    ]

    constructor
    · exact ⟨hr, ha⟩
    · exact hleft

  refine ⟨(r0, a), hp, ?_⟩

  apply Prod.ext
  · rfl
  · dsimp [r0]
    omega

/--
The diagonal-band parametrization is exactly the strict upper triangle.
-/
theorem bandIndexPairs_sum_eq_strictUpper
    (m : ℕ)
    (w : ℕ → ℕ → ℝ) :
    (∑ p ∈ bandIndexPairs m, w p.2 (p.2 + p.1 + 1))
      =
    strictUpperPairEnergyNat m w := by

  unfold strictUpperPairEnergyNat

  apply
    Finset.sum_bij
      (fun p hp => (p.2, p.2 + p.1 + 1))

  · intro p hp
    exact bandToUpper_mem m p hp

  · intro p₁ hp₁ p₂ hp₂ h
    exact bandToUpper_inj m p₁ hp₁ p₂ hp₂ h

  · intro q hq
    exact bandToUpper_surj m q hq

  · intro p hp
    rfl

/--
`globalPairEnergyNat` is twice the strict-upper-triangle pair energy.
-/
theorem globalPairEnergyNat_eq_two_mul_strictUpper
    (m : ℕ)
    (w : ℕ → ℕ → ℝ) :
    globalPairEnergyNat m w
      =
    2 * strictUpperPairEnergyNat m w := by

  unfold globalPairEnergyNat

  rw [sum_pairBandEnergy_eq_bandIndexPairs]
  rw [bandIndexPairs_sum_eq_strictUpper]

end HurtadoZeta23
