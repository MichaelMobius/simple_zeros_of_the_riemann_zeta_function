import HurtadoZeta23.BlockDefect
import HurtadoZeta23.MatrixEnergy
import HurtadoZeta23.LimitingKernel
import Mathlib.Tactic

noncomputable section

namespace HurtadoZeta23

open scoped BigOperators

/--
Monotonicity of the finite pair energy, with no positivity assumption.
-/
lemma globalPairEnergyNat_mono
    {m : ℕ}
    {w g : ℕ → ℕ → ℝ}
    (h : ∀ a b, w a b ≤ g a b) :
    globalPairEnergyNat m w ≤ globalPairEnergyNat m g := by
  unfold globalPairEnergyNat pairBandEnergy
  apply mul_le_mul_of_nonneg_left
  · apply Finset.sum_le_sum
    intro r0 hr
    apply Finset.sum_le_sum
    intro a ha
    exact h a (a + r0 + 1)
  · norm_num

/--
For the fixed block length 262, the total number of unordered pairs in the
diagonal parametrization is 34191.
-/
lemma pairMultiplicitySumNat_262 :
    (∑ x ∈ Finset.range 261, (262 - (1 + x))) = 34191 := by
  native_decide

/--
The real-valued version of the same finite counting identity.
-/
lemma pairMultiplicitySum_262 :
    (∑ x ∈ Finset.range 261,
      ((262 - (1 + x) : ℕ) : ℝ)) = 34191 := by
  exact_mod_cast pairMultiplicitySumNat_262

/--
For the fixed block length 262, subtracting `eta` from every unordered pair
subtracts exactly

  68382 * eta

from the directed global pair energy.

There are 34191 unordered pairs and `globalPairEnergyNat` carries an overall
factor 2.
-/
lemma globalPairEnergyNat_sub_uniform_262
    (w : ℕ → ℕ → ℝ)
    (eta : ℝ) :
    globalPairEnergyNat blockLength (fun a b => w a b - eta)
      =
    globalPairEnergyNat blockLength w - 68382 * eta := by

  unfold globalPairEnergyNat pairBandEnergy

  norm_num [blockLength]

  have hsum :
      (∑ x ∈ Finset.range 261,
        ((262 - (x + 1) : ℕ) : ℝ))
        =
      34191 := by
    have h :
        (∑ x ∈ Finset.range 261,
          ((262 - (1 + x) : ℕ) : ℝ))
          =
        34191 :=
      pairMultiplicitySum_262
    simpa [Nat.add_comm] using h

  have hcount :
      (∑ x ∈ Finset.range 261,
        ((262 - (x + 1) : ℕ) : ℝ) * eta)
        =
      34191 * eta := by
    calc
      (∑ x ∈ Finset.range 261,
        ((262 - (x + 1) : ℕ) : ℝ) * eta)
          =
        (∑ x ∈ Finset.range 261,
          ((262 - (x + 1) : ℕ) : ℝ)) * eta := by
            rw [← Finset.sum_mul]

      _ = 34191 * eta := by
            rw [hsum]

  rw [hcount]

  ring

/--
A uniform lower approximation of every squared Gram entry gives the
aggregate kernel bridge for the fixed 262-point block.
-/
theorem aggregate_kernel_lower_262
    (w gramSq : ℕ → ℕ → ℝ)
    (eta : ℝ)
    (hpoint : ∀ a b, w a b - eta ≤ gramSq a b) :
    globalPairEnergyNat blockLength w - 68382 * eta
      ≤ globalPairEnergyNat blockLength gramSq := by

  rw [← globalPairEnergyNat_sub_uniform_262 w eta]

  exact globalPairEnergyNat_mono hpoint

/--
The exact pointwise compact-overlap statement needed for a 262-point block.

`gramSq a b` should represent the squared Gram entry. The weight is the
limiting kernel evaluated at the normalized ordinate separation.
-/
def PointwiseKernelApproximation262
    (y : ℕ → ℝ)
    (gramSq : ℕ → ℕ → ℝ)
    (eta : ℝ) : Prop :=
  0 ≤ eta ∧
  ∀ a b,
    limitingWeightOnPoints y a b - eta ≤ gramSq a b

/--
Pointwise compact-uniform control implies the finite aggregate bridge.
-/
theorem kernel_bridge_262_of_pointwise
    (y : ℕ → ℝ)
    (gramSq : ℕ → ℕ → ℝ)
    (eta : ℝ)
    (h : PointwiseKernelApproximation262 y gramSq eta) :
    globalPairEnergyNat blockLength (limitingWeightOnPoints y)
        - 68382 * eta
      ≤
    globalPairEnergyNat blockLength gramSq := by

  exact
    aggregate_kernel_lower_262
      (limitingWeightOnPoints y)
      gramSq
      eta
      h.2

/--
Abstract normalization retained for compatibility with the block-stability
API.

`pairEnergy` is the finite Montgomery--Taylor energy,
`gramOffDiag` the actual Gram off-diagonal Frobenius energy,
and `err` the accumulated kernel error.
-/
structure KernelBridgeData where
  pairEnergy : ℝ
  gramOffDiag : ℝ
  err : ℝ
  err_nonneg : 0 ≤ err
  lower : pairEnergy - err ≤ gramOffDiag

/--
The exact inequality consumed by uniform block stability.
-/
theorem kernel_bridge_lower
    (K : KernelBridgeData) :
    K.pairEnergy - K.err ≤ K.gramOffDiag :=
  K.lower

/--
Specialized finite-block interface.
-/
def Block262KernelBridge
    (w : ℕ → ℕ → ℝ)
    (gramOffDiag err : ℝ) : Prop :=
  0 ≤ err ∧
  globalPairEnergyNat blockLength w - err ≤ gramOffDiag

/--
The pointwise overlap estimate yields `Block262KernelBridge` once the actual
Gram off-diagonal energy is identified with `globalPairEnergyNat gramSq`.
-/
theorem block262KernelBridge_of_pointwise
    (y : ℕ → ℝ)
    (gramSq : ℕ → ℕ → ℝ)
    (eta gramOffDiag : ℝ)
    (heta : 0 ≤ eta)
    (hpoint :
      ∀ a b,
        limitingWeightOnPoints y a b - eta ≤ gramSq a b)
    (hGram :
      globalPairEnergyNat blockLength gramSq = gramOffDiag) :
    Block262KernelBridge
      (limitingWeightOnPoints y)
      gramOffDiag
      (68382 * eta) := by

  constructor

  · positivity

  · rw [← hGram]

    exact
      aggregate_kernel_lower_262
        (limitingWeightOnPoints y)
        gramSq
        eta
        hpoint

/--
A Block-262 kernel bridge feeds directly into the scalar stability theorem.
-/
theorem block_stability_262_of_kernel_bridge
    (y : ℕ → ℝ)
    (w : ℕ → ℕ → ℝ)
    (hw : ∀ a b, 0 ≤ w a b)
    (hcert :
      SevenPointCertificate w y blockLength)
    (hmono :
      ∀ q < blockLength - 1,
        y q ≤ y (q + 1))
    (hspan0 :
      0 ≤ y (blockLength - 1) - y 0)
    {D gramOffDiag err : ℝ}
    (hD0 : 0 ≤ D)
    (hblock :
      min 1 gramOffDiag ≤ D)
    (hkernel :
      Block262KernelBridge
        w
        gramOffDiag
        err) :
    A0 - err
      ≤
    D + beta *
      (y (blockLength - 1) - y 0) := by

  rcases hkernel with ⟨herr, hbridge⟩

  exact
    block_stability_262_from_block_defect
      y
      w
      hw
      hcert
      hmono
      hspan0
      hD0
      herr
      hblock
      hbridge

/--
The concrete limiting-kernel version: only the certificate, Gram defect,
and compact-overlap approximation remain.
-/
theorem block_stability_262_of_pointwise_kernel
    (y : ℕ → ℝ)
    (gramSq : ℕ → ℕ → ℝ)
    (hcert :
      SevenPointCertificate
        (limitingWeightOnPoints y)
        y
        blockLength)
    (hmono :
      ∀ q < blockLength - 1,
        y q ≤ y (q + 1))
    (hspan0 :
      0 ≤ y (blockLength - 1) - y 0)
    {D gramOffDiag eta : ℝ}
    (hD0 : 0 ≤ D)
    (hblock :
      min 1 gramOffDiag ≤ D)
    (heta : 0 ≤ eta)
    (hpoint :
      ∀ a b,
        limitingWeightOnPoints y a b - eta ≤ gramSq a b)
    (hGram :
      globalPairEnergyNat blockLength gramSq = gramOffDiag) :
    A0 - 68382 * eta
      ≤
    D + beta *
      (y (blockLength - 1) - y 0) := by

  apply
    block_stability_262_of_kernel_bridge
      y
      (limitingWeightOnPoints y)
      (limitingWeightOnPoints_nonneg y)
      hcert
      hmono
      hspan0
      hD0
      hblock

  exact
    block262KernelBridge_of_pointwise
      y
      gramSq
      eta
      gramOffDiag
      heta
      hpoint
      hGram

end HurtadoZeta23