import HurtadoZeta23.ConsecutiveGramRealEntries
import Mathlib.Tactic

noncomputable section

open Matrix Finset
open scoped BigOperators ComplexOrder

namespace HurtadoZeta23

/-!
# Consecutive Gram overlap bridge

`RawPointwiseOverlapApproximation262` is phrased on functions `ℕ → ℕ → ℝ`,
even though the global pair energy only consumes indices `< blockLength`.

The raw Gram overlap should therefore not be extended by zero outside the
262-point block: doing so would impose an artificial approximation condition
there.  Instead we extend it by the limiting kernel itself.  Consequently:

* on the actual block it is exactly the real Gram entry;
* outside the block the compact-overlap error is exactly zero;
* `globalPairEnergyNat` is unchanged, since it only samples in-range pairs.

This is the natural totalization of the finite block overlap.
-/

/-- Real Gram symmetry for every consecutive block. -/
theorem consecutiveGramBlock_apply_comm
    (T : ℝ)
    (s : ℕ)
    (hs : s + blockLength ≤ articleRetainedCard T)
    (i j : Fin blockLength) :
    consecutiveGramBlock T s hs i j
      =
    consecutiveGramBlock T s hs j i := by

  have hHerm :
      (consecutiveGramBlock T s hs).IsHermitian :=
    (consecutiveGramBlock_posSemidef T s hs).isHermitian

  calc
    consecutiveGramBlock T s hs i j
        = star (consecutiveGramBlock T s hs j i) := by
            exact (hHerm.apply i j).symm
    _ = consecutiveGramBlock T s hs j i := by
          exact star_consecutiveGramBlock_apply T s hs j i

/-- Symmetry of the real in-block overlap. -/
theorem consecutiveGramOverlapNat_comm
    (T : ℝ)
    (s : ℕ)
    (hs : s + blockLength ≤ articleRetainedCard T)
    {a b : ℕ}
    (ha : a < blockLength)
    (hb : b < blockLength) :
    consecutiveGramOverlapNat T s hs a b
      =
    consecutiveGramOverlapNat T s hs b a := by

  rw [
    consecutiveGramOverlapNat_eq T s hs ha hb,
    consecutiveGramOverlapNat_eq T s hs hb ha
  ]

  rw [consecutiveGramBlock_apply_comm T s hs ⟨a, ha⟩ ⟨b, hb⟩]

/--
Total raw overlap attached to a consecutive Gram block.

Inside the block it is the real Gram entry. Outside the block we set it equal
to the limiting kernel itself, so the raw compact-overlap error vanishes
identically there.
-/
noncomputable def consecutiveGramOverlap
    (T : ℝ)
    (s : ℕ)
    (hs : s + blockLength ≤ articleRetainedCard T)
    (a b : ℕ) :
    ℝ :=
  if ha : a < blockLength then
    if hb : b < blockLength then
      (consecutiveGramBlock T s hs ⟨a, ha⟩ ⟨b, hb⟩).re
    else
      limitingk (consecutiveY T s hs b - consecutiveY T s hs a)
  else
    limitingk (consecutiveY T s hs b - consecutiveY T s hs a)

@[simp] theorem consecutiveGramOverlap_eq
    (T : ℝ)
    (s : ℕ)
    (hs : s + blockLength ≤ articleRetainedCard T)
    {a b : ℕ}
    (ha : a < blockLength)
    (hb : b < blockLength) :
    consecutiveGramOverlap T s hs a b
      =
    (consecutiveGramBlock T s hs ⟨a, ha⟩ ⟨b, hb⟩).re := by

  simp [consecutiveGramOverlap, ha, hb]

/-- The total overlap agrees with the earlier in-range natural-number overlap. -/
theorem consecutiveGramOverlap_eq_nat
    (T : ℝ)
    (s : ℕ)
    (hs : s + blockLength ≤ articleRetainedCard T)
    {a b : ℕ}
    (ha : a < blockLength)
    (hb : b < blockLength) :
    consecutiveGramOverlap T s hs a b
      =
    consecutiveGramOverlapNat T s hs a b := by

  rw [
    consecutiveGramOverlap_eq T s hs ha hb,
    consecutiveGramOverlapNat_eq T s hs ha hb
  ]

/--
Outside the actual 262-point block, the total overlap is exactly the limiting
kernel, hence contributes zero raw approximation error.
-/
theorem consecutiveGramOverlap_eq_limitingk_of_outside
    (T : ℝ)
    (s : ℕ)
    (hs : s + blockLength ≤ articleRetainedCard T)
    (a b : ℕ)
    (hout : ¬(a < blockLength ∧ b < blockLength)) :
    consecutiveGramOverlap T s hs a b
      =
    limitingk (consecutiveY T s hs b - consecutiveY T s hs a) := by

  by_cases ha : a < blockLength
  · have hb : ¬ b < blockLength := by
      intro hb
      exact hout ⟨ha, hb⟩
    simp [consecutiveGramOverlap, ha, hb]
  · simp [consecutiveGramOverlap, ha]

/--
The totalization does not change the global pair energy: every pair sampled by
`globalPairEnergyNat blockLength` lies inside the block.
-/
theorem globalPairEnergyNat_consecutiveGramOverlap_eq_nat
    (T : ℝ)
    (s : ℕ)
    (hs : s + blockLength ≤ articleRetainedCard T) :
    globalPairEnergyNat blockLength
        (fun a b => consecutiveGramOverlap T s hs a b ^ 2)
      =
    globalPairEnergyNat blockLength
        (fun a b => consecutiveGramOverlapNat T s hs a b ^ 2) := by

  unfold globalPairEnergyNat

  apply congrArg (fun x : ℝ => 2 * x)

  apply Finset.sum_congr rfl
  intro r0 hr0

  unfold pairBandEnergy

  apply Finset.sum_congr rfl
  intro a ha

  have hr0lt :
      r0 < blockLength - 1 :=
    Finset.mem_range.mp hr0

  have halt :
      a < blockLength - (r0 + 1) :=
    Finset.mem_range.mp ha

  have haBlock :
      a < blockLength := by
    omega

  have hbBlock :
      a + r0 + 1 < blockLength := by
    omega

  have hval :
      consecutiveGramOverlap T s hs a (a + r0 + 1)
        =
      consecutiveGramOverlapNat T s hs a (a + r0 + 1) :=
    consecutiveGramOverlap_eq_nat
      T s hs haBlock hbBlock

  change
    consecutiveGramOverlap T s hs a (a + r0 + 1) ^ 2
      =
    consecutiveGramOverlapNat T s hs a (a + r0 + 1) ^ 2

  exact congrArg (fun x : ℝ => x ^ 2) hval

/--
Raw overlap approximation is reduced to the actual in-block compact-overlap
estimate.  Outside the block, the approximation part is automatic.

The unit bounds are kept explicit because they are analytic inputs used by the
square-error reduction in `PoissonGaborBridge`.
-/
theorem rawPointwiseOverlapApproximation262_of_inrange
    (T eps : ℝ)
    (s : ℕ)
    (hs : s + blockLength ≤ articleRetainedCard T)
    (heps : 0 ≤ eps)
    (hGramBound :
      ∀ a b (ha : a < blockLength) (hb : b < blockLength),
        |(consecutiveGramBlock T s hs ⟨a, ha⟩ ⟨b, hb⟩).re| ≤ 1)
    (hKernelBound :
      ∀ a b,
        |limitingk
          (consecutiveY T s hs b - consecutiveY T s hs a)| ≤ 1)
    (hcompact :
      ∀ a b (ha : a < blockLength) (hb : b < blockLength),
        |(consecutiveGramBlock T s hs ⟨a, ha⟩ ⟨b, hb⟩).re
            -
          limitingk
            (consecutiveY T s hs b - consecutiveY T s hs a)|
          ≤ eps) :
    RawPointwiseOverlapApproximation262
      (consecutiveY T s hs)
      (consecutiveGramOverlap T s hs)
      eps := by

  constructor
  · exact heps

  constructor
  · intro a b
    by_cases hab : a < blockLength ∧ b < blockLength
    · rcases hab with ⟨ha, hb⟩
      rw [consecutiveGramOverlap_eq T s hs ha hb]
      exact hGramBound a b ha hb
    · rw [consecutiveGramOverlap_eq_limitingk_of_outside T s hs a b hab]
      exact hKernelBound a b

  constructor
  · exact hKernelBound

  · intro a b
    by_cases hab : a < blockLength ∧ b < blockLength
    · rcases hab with ⟨ha, hb⟩
      rw [consecutiveGramOverlap_eq T s hs ha hb]
      exact hcompact a b ha hb
    · rw [consecutiveGramOverlap_eq_limitingk_of_outside T s hs a b hab]
      simp
      exact heps

end HurtadoZeta23
