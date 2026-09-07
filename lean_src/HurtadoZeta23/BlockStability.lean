import HurtadoZeta23.DirectRedistribution
import Mathlib.Tactic

namespace HurtadoZeta23

/--
Scalar core of the paper's Uniform block stability lemma.

`E` is the seven-point/global pair energy of a block, `span` its normalized
span, `D` its Gram defect, and `err ≥ 0` bounds the uniform kernel error from
below.  The hypotheses are exactly the two inequalities used in the paper:

* pressure redistribution: `A0 ≤ E + beta * span`;
* block defect + kernel approximation: `min 1 (E - err) ≤ D`.

The conclusion is `A0 - err ≤ D + beta * span`.
-/
theorem block_stability_scalar
    {D E span err : ℝ}
    (hD0 : 0 ≤ D)
    (hspan0 : 0 ≤ span)
    (herr : 0 ≤ err)
    (henergy : A0 ≤ E + beta * span)
    (hdefect : min 1 (E - err) ≤ D) :
    A0 - err ≤ D + beta * span := by
  by_cases hlarge : A0 ≤ beta * span
  · linarith
  · have hE : A0 - beta * span ≤ E := by
      linarith
    have htarget_one : A0 - beta * span - err ≤ 1 := by
      have hA := A0_lt_one
      have hbeta : 0 ≤ beta := by norm_num [beta]
      have hpress : 0 ≤ beta * span := mul_nonneg hbeta hspan0
      linarith
    have htarget_E : A0 - beta * span - err ≤ E - err := by
      linarith
    have htarget_min : A0 - beta * span - err ≤ min 1 (E - err) := by
      exact le_min htarget_one htarget_E
    linarith

/--
The `m = 262` block-stability consequence of the explicit seven-point
certificate and pressure redistribution.

The only remaining Gram/kernel input is `hdefect`: after bounding the uniform
kernel error by a nonnegative `err`, the actual Gram defect `D` dominates
`min 1 (E - err)`.
-/
theorem block_stability_262
    (y : ℕ → ℝ)
    (w : ℕ → ℕ → ℝ)
    (hw : ∀ a b, 0 ≤ w a b)
    (hcert : SevenPointCertificate w y blockLength)
    (hmono : ∀ q < blockLength - 1, y q ≤ y (q + 1))
    (hspan0 : 0 ≤ y (blockLength - 1) - y 0)
    {D err : ℝ}
    (hD0 : 0 ≤ D)
    (herr : 0 ≤ err)
    (hdefect :
      min 1 (globalPairEnergyNat blockLength w - err) ≤ D) :
    A0 - err ≤ D + beta * (y (blockLength - 1) - y 0) := by
  have henergy := pressure_redistribution_262 y hmono w hw hcert
  exact block_stability_scalar hD0 hspan0 herr henergy hdefect

/-- The numerical margin below one used in the compact-separation branch. -/
lemma five_hundred_mul_A0_lt_five_hundred : 500 * A0 < 500 := by
  nlinarith [A0_lt_one]

/-- If the pressure term alone does not prove stability, the block span is < 500. -/
lemma span_lt_five_hundred_of_pressure_small
    {span : ℝ} (hspan0 : 0 ≤ span) (hsmall : beta * span < A0) :
    span < 500 := by
  norm_num [beta] at hsmall ⊢
  nlinarith [A0_lt_one]

end HurtadoZeta23
