import HurtadoZeta23.DirectRedistribution
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic

noncomputable section

open Finset
open scoped BigOperators

namespace HurtadoZeta23

/-!
# Lightweight pair-band reindexing core

This is the purely finite content of the historical `PairBandReindex` module,
with its import reduced to `DirectRedistribution`, where `pairBandEnergy` and
`globalPairEnergyNat` are actually defined.  No consecutive-block or 262-point
infrastructure is involved.
-/

/-- Admissible `(separation-1, left endpoint)` indices for all pair bands. -/
def v17BandIndexPairs (m : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (m - 1)) ×ˢ (Finset.range m)).filter
    (fun p => p.2 < m - (p.1 + 1))

/-- Natural-number strict upper triangle below `m`. -/
def v17StrictUpperPairsNat (m : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range m) ×ˢ (Finset.range m)).filter
    (fun p => p.1 < p.2)

/-- Sum of a weight over the strict upper triangle. -/
def v17StrictUpperPairEnergyNat
    (m : ℕ) (w : ℕ → ℕ → ℝ) : ℝ :=
  ∑ p ∈ v17StrictUpperPairsNat m, w p.1 p.2

/-- The nested band sum is the sum over one finite index set. -/
theorem v17_sum_pairBandEnergy_eq_bandIndexPairs
    (m : ℕ) (w : ℕ → ℕ → ℝ) :
    (∑ r0 ∈ Finset.range (m - 1), pairBandEnergy m r0 w) =
      ∑ p ∈ v17BandIndexPairs m, w p.2 (p.2 + p.1 + 1) := by
  unfold pairBandEnergy
  symm
  apply
    Finset.sum_finset_product'
      (r := v17BandIndexPairs m)
      (s := Finset.range (m - 1))
      (t := fun r0 => Finset.range (m - (r0 + 1)))
      (f := fun r0 a => w a (a + r0 + 1))
  intro p
  simp only [
    v17BandIndexPairs,
    Finset.mem_filter,
    Finset.mem_product,
    Finset.mem_range
  ]
  constructor
  · intro hp
    exact ⟨hp.1.1, hp.2⟩
  · rintro ⟨hr, ha⟩
    constructor
    · exact ⟨hr, by omega⟩
    · exact ha

lemma v17_bandToUpper_mem
    (m : ℕ) (p : ℕ × ℕ) (hp : p ∈ v17BandIndexPairs m) :
    (p.2, p.2 + p.1 + 1) ∈ v17StrictUpperPairsNat m := by
  rcases p with ⟨r0, a⟩
  simp only [
    v17BandIndexPairs,
    v17StrictUpperPairsNat,
    Finset.mem_filter,
    Finset.mem_product,
    Finset.mem_range,
    Prod.fst,
    Prod.snd
  ] at hp ⊢
  rcases hp with ⟨⟨hr, haM⟩, ha⟩
  constructor
  · exact ⟨haM, by omega⟩
  · omega

lemma v17_bandToUpper_inj
    (m : ℕ)
    (p₁ : ℕ × ℕ) (hp₁ : p₁ ∈ v17BandIndexPairs m)
    (p₂ : ℕ × ℕ) (hp₂ : p₂ ∈ v17BandIndexPairs m)
    (h : (p₁.2, p₁.2 + p₁.1 + 1) =
      (p₂.2, p₂.2 + p₂.1 + 1)) :
    p₁ = p₂ := by
  rcases p₁ with ⟨r₁, a₁⟩
  rcases p₂ with ⟨r₂, a₂⟩
  have ha : a₁ = a₂ := congrArg Prod.fst h
  have hb : a₁ + r₁ + 1 = a₂ + r₂ + 1 := congrArg Prod.snd h
  have hr : r₁ = r₂ := by omega
  subst a₂
  subst r₂
  rfl

lemma v17_bandToUpper_surj
    (m : ℕ) (q : ℕ × ℕ) (hq : q ∈ v17StrictUpperPairsNat m) :
    ∃ p : ℕ × ℕ, ∃ hp : p ∈ v17BandIndexPairs m,
      (p.2, p.2 + p.1 + 1) = q := by
  rcases q with ⟨a, b⟩
  simp only [
    v17StrictUpperPairsNat,
    Finset.mem_filter,
    Finset.mem_product,
    Finset.mem_range,
    Prod.fst,
    Prod.snd
  ] at hq
  rcases hq with ⟨⟨ha, hb⟩, hab⟩
  let r0 : ℕ := b - a - 1
  have hr : r0 < m - 1 := by
    dsimp [r0]
    omega
  have hleft : a < m - (r0 + 1) := by
    dsimp [r0]
    omega
  have hp : (r0, a) ∈ v17BandIndexPairs m := by
    simp only [
      v17BandIndexPairs,
      Finset.mem_filter,
      Finset.mem_product,
      Finset.mem_range,
      Prod.fst,
      Prod.snd
    ]
    exact ⟨⟨hr, ha⟩, hleft⟩
  refine ⟨(r0, a), hp, ?_⟩
  apply Prod.ext
  · rfl
  · dsimp [r0]
    omega

/-- Band coordinates parametrize the strict upper triangle exactly once. -/
theorem v17_bandIndexPairs_sum_eq_strictUpper
    (m : ℕ) (w : ℕ → ℕ → ℝ) :
    (∑ p ∈ v17BandIndexPairs m, w p.2 (p.2 + p.1 + 1)) =
      v17StrictUpperPairEnergyNat m w := by
  unfold v17StrictUpperPairEnergyNat
  apply Finset.sum_bij (fun p hp => (p.2, p.2 + p.1 + 1))
  · intro p hp
    exact v17_bandToUpper_mem m p hp
  · intro p₁ hp₁ p₂ hp₂ h
    exact v17_bandToUpper_inj m p₁ hp₁ p₂ hp₂ h
  · intro q hq
    exact v17_bandToUpper_surj m q hq
  · intro p hp
    rfl

/-- `globalPairEnergyNat` is twice the natural strict-upper pair energy. -/
theorem v17_globalPairEnergyNat_eq_two_mul_strictUpper
    (m : ℕ) (w : ℕ → ℕ → ℝ) :
    globalPairEnergyNat m w = 2 * v17StrictUpperPairEnergyNat m w := by
  unfold globalPairEnergyNat
  rw [v17_sum_pairBandEnergy_eq_bandIndexPairs]
  rw [v17_bandIndexPairs_sum_eq_strictUpper]

end HurtadoZeta23
