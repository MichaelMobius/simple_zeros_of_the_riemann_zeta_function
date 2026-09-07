import HurtadoZeta23.ConcreteGramClosedAssembly
import HurtadoZeta23.FourierL1
import Mathlib.Tactic

noncomputable section

open Matrix Finset
open scoped BigOperators ComplexOrder

namespace HurtadoZeta23

/-!
# Lightweight raw-overlap reduction

This deliberately avoids a generic Cauchy--Schwarz proof over arbitrary
matrices.  That algebraic bound will be proved separately from the concrete
Poisson column estimate.

Here we only internalize the already available limiting-kernel unit bound and
reduce `RawPointwiseOverlapApproximation262` to the two genuinely block-local
statements:

* `|Re G_ab| ≤ 1`;
* `|Re G_ab - limitingk(y_b-y_a)| ≤ eps`.
-/

/-- The normalized limiting overlap satisfies `|limitingk x| ≤ 1`. -/
theorem limitingk_abs_le_one_lite
    (x : ℝ) :
    |limitingk x| ≤ 1 := by

  have hK :
      |limitingK x| ≤ limitingK 0 :=
    limitingKernelMajorization_proved x

  have hK0 :
      0 < limitingK 0 :=
    limitingK_zero_pos

  unfold limitingk

  rw [abs_div, abs_of_pos hK0]

  apply (div_le_iff₀ hK0).2

  simpa using hK

/--
Lightweight reduction of `hraw`.

The total overlap outside the block is already handled by
`rawPointwiseOverlapApproximation262_of_inrange`; therefore only in-range Gram
bounds and the genuine compact-overlap estimate remain.
-/
theorem rawPointwiseOverlapApproximation262_consecutive_of_bounds
    (T eps : ℝ)
    (s : ℕ)
    (hs : s + blockLength ≤ articleRetainedCard T)
    (heps : 0 ≤ eps)
    (hGramBound :
      ∀ a b (ha : a < blockLength) (hb : b < blockLength),
        |(consecutiveGramBlock T s hs ⟨a, ha⟩ ⟨b, hb⟩).re| ≤ 1)
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

  apply
    rawPointwiseOverlapApproximation262_of_inrange
      T eps s hs heps

  · exact hGramBound

  · intro a b
    exact limitingk_abs_le_one_lite _

  · exact hcompact

end HurtadoZeta23
