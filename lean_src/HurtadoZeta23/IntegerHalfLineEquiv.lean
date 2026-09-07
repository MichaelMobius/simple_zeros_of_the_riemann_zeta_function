import HurtadoZeta23.InfiniteLatticeAssembly
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic

noncomputable section

namespace HurtadoZeta23

open Real Filter Topology
open scoped BigOperators

/-- Left omitted indices as a subtype. -/
def leftHalfLine (kMin : ℤ) := {k : ℤ // k < kMin}

/-- Right omitted indices as a subtype. -/
def rightHalfLine (kMax : ℤ) := {k : ℤ // kMax < k}

/-- Enumeration of the left half-line starting at the closest omitted point. -/
def leftHalfLineMap (kMin : ℤ) (j : ℕ) : leftHalfLine kMin :=
  ⟨kMin - 1 - Int.ofNat j, by
    change kMin - 1 - (j : ℤ) < kMin
    have hj : (0 : ℤ) ≤ (j : ℤ) := Int.natCast_nonneg j
    omega⟩

/-- Enumeration of the right half-line starting at the closest omitted point. -/
def rightHalfLineMap (kMax : ℤ) (j : ℕ) : rightHalfLine kMax :=
  ⟨kMax + 1 + Int.ofNat j, by
    change kMax < kMax + 1 + (j : ℤ)
    have hj : (0 : ℤ) ≤ (j : ℤ) := Int.natCast_nonneg j
    omega⟩

lemma leftHalfLineMap_injective (kMin : ℤ) :
    Function.Injective (leftHalfLineMap kMin) := by
  intro a b h
  have hv := congrArg Subtype.val h
  change kMin - 1 - (a : ℤ) = kMin - 1 - (b : ℤ) at hv
  have habZ : (a : ℤ) = (b : ℤ) := by omega
  exact_mod_cast habZ

lemma rightHalfLineMap_injective (kMax : ℤ) :
    Function.Injective (rightHalfLineMap kMax) := by
  intro a b h
  have hv := congrArg Subtype.val h
  change kMax + 1 + (a : ℤ) = kMax + 1 + (b : ℤ) at hv
  have habZ : (a : ℤ) = (b : ℤ) := by omega
  exact_mod_cast habZ

/-- Every integer strictly to the left of `kMin` occurs uniquely as
`kMin - 1 - j`. -/
lemma leftHalfLineMap_surjective (kMin : ℤ) :
    Function.Surjective (leftHalfLineMap kMin) := by
  intro k
  let z : ℤ := kMin - 1 - k.1
  let j : ℕ := z.toNat
  have hklt : k.1 < kMin := k.2
  have hz : 0 ≤ z := by
    dsimp [z]
    omega
  have hzcast : ((j : ℕ) : ℤ) = z := by
    dsimp [j]
    exact Int.toNat_of_nonneg hz
  refine ⟨j, ?_⟩
  apply Subtype.ext
  change kMin - 1 - (j : ℤ) = k.1
  rw [hzcast]
  dsimp [z]
  ring

/-- Every integer strictly to the right of `kMax` occurs uniquely as
`kMax + 1 + j`. -/
lemma rightHalfLineMap_surjective (kMax : ℤ) :
    Function.Surjective (rightHalfLineMap kMax) := by
  intro k
  let z : ℤ := k.1 - kMax - 1
  let j : ℕ := z.toNat
  have hkgt : kMax < k.1 := k.2
  have hz : 0 ≤ z := by
    dsimp [z]
    omega
  have hzcast : ((j : ℕ) : ℤ) = z := by
    dsimp [j]
    exact Int.toNat_of_nonneg hz
  refine ⟨j, ?_⟩
  apply Subtype.ext
  change kMax + 1 + (j : ℤ) = k.1
  rw [hzcast]
  dsimp [z]
  ring

/-- Canonical equivalence between `ℕ` and the omitted left half-line. -/
def leftHalfLineEquiv (kMin : ℤ) : ℕ ≃ leftHalfLine kMin :=
  Equiv.ofBijective (leftHalfLineMap kMin)
    ⟨leftHalfLineMap_injective kMin, leftHalfLineMap_surjective kMin⟩

/-- Canonical equivalence between `ℕ` and the omitted right half-line. -/
def rightHalfLineEquiv (kMax : ℤ) : ℕ ≃ rightHalfLine kMax :=
  Equiv.ofBijective (rightHalfLineMap kMax)
    ⟨rightHalfLineMap_injective kMax, rightHalfLineMap_surjective kMax⟩

@[simp] lemma leftHalfLineEquiv_apply (kMin : ℤ) (j : ℕ) :
    (leftHalfLineEquiv kMin j).1 = kMin - 1 - Int.ofNat j := by
  rfl

@[simp] lemma rightHalfLineEquiv_apply (kMax : ℤ) (j : ℕ) :
    (rightHalfLineEquiv kMax j).1 = kMax + 1 + Int.ofNat j := by
  rfl

/-- Reindexing the left subtype sum gives exactly `leftInfiniteTail`. -/
theorem tsum_leftHalfLine_eq_leftInfiniteTail
    (f : ℤ → ℝ) (kMin : ℤ) :
    (∑' k : leftHalfLine kMin, f k.1) = leftInfiniteTail f kMin := by
  rw [← Equiv.tsum_eq (leftHalfLineEquiv kMin)]
  unfold leftInfiniteTail
  apply tsum_congr
  intro j
  rw [leftHalfLineEquiv_apply]

/-- Reindexing the right subtype sum gives exactly `rightInfiniteTail`. -/
theorem tsum_rightHalfLine_eq_rightInfiniteTail
    (f : ℤ → ℝ) (kMax : ℤ) :
    (∑' k : rightHalfLine kMax, f k.1) = rightInfiniteTail f kMax := by
  rw [← Equiv.tsum_eq (rightHalfLineEquiv kMax)]
  unfold rightInfiniteTail
  apply tsum_congr
  intro j
  rw [rightHalfLineEquiv_apply]

end HurtadoZeta23
