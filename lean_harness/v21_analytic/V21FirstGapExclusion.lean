import HurtadoZeta23.V21HardCoreGeometry
import HurtadoZeta23.V21KernelFirstLobeQuantitative
import HurtadoZeta23.V21KernelEndpointBounds
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

noncomputable section

open Set

namespace HurtadoZeta23

/-- The normalized kernel viewed directly as a function of the gap variable. -/
def v21KernelX (x : ℝ) : ℝ := v21KernelB (v21B x)

/-- Every point of the closed first hard-core band lies safely beyond the
removable singularity of the elementary kernel formula. -/
lemma v21_A_lt_B_first_band {x : ℝ}
    (hxlo : (89 / 100 : ℝ) ≤ x) :
    v21A < v21B x := by
  have hxpos : 0 < x := by norm_num at hxlo ⊢; linarith
  have h3x : 3 * x < Real.pi * x :=
    mul_lt_mul_of_pos_right Real.pi_gt_three hxpos
  have hB : 1 < v21B x := by
    unfold v21B
    nlinarith
  exact v21_A_lt_one.trans hB

lemma v21_B_hasDerivAt (x : ℝ) :
    HasDerivAt v21B Real.pi x := by
  unfold v21B
  exact hasDerivAt_const_mul (x := x) Real.pi

/-- Exact derivative in the gap variable `x`. -/
lemma v21_kernelX_hasDerivAt {x : ℝ}
    (hxlo : (89 / 100 : ℝ) ≤ x) :
    HasDerivAt v21KernelX
      ((v21M1 (v21B x) /
          ((v21B x) ^ 2 - (1 / 2 : ℝ)) ^ 2) * Real.pi) x := by
  have hxA := v21_A_lt_B_first_band hxlo
  have hD : (v21B x) ^ 2 - (1 / 2 : ℝ) ≠ 0 := by
    have hpos := v21_D_pos hxA
    simpa [v21D] using hpos.ne'
  have hk := v21_kernelB_hasDerivAt (b := v21B x) hD
  have hB := v21_B_hasDerivAt x
  simpa [v21KernelX] using hk.comp x hB

/-- The coarse phase derivative estimate becomes a uniform x-derivative
bound after multiplying by `π > 3`. -/
lemma v21_kernelX_deriv_le_first_band {x : ℝ}
    (hxlo : (89 / 100 : ℝ) ≤ x) (hxhi : x ≤ (19 / 20 : ℝ)) :
    deriv v21KernelX x ≤ -(3 / 200 : ℝ) := by
  have hk := v21_kernelX_hasDerivAt hxlo
  rw [hk.deriv]
  have hphase := v21_kernelB_deriv_le_first_band hxlo hxhi
  have hmul := mul_le_mul_of_nonneg_right hphase Real.pi_pos.le
  have hpi : -(1 / 200 : ℝ) * Real.pi ≤ -(3 / 200 : ℝ) := by
    nlinarith [Real.pi_gt_three]
  exact hmul.trans hpi

/-- Quantitative first-lobe transfer: moving left from `0.95` increases the
kernel by at least `3/200` times the displacement. -/
lemma v21_kernelX_first_band_linear_lower {x : ℝ}
    (hxlo : (89 / 100 : ℝ) ≤ x) (hxhi : x ≤ (19 / 20 : ℝ)) :
    v21KernelX (19 / 20 : ℝ) +
        (3 / 200 : ℝ) * ((19 / 20 : ℝ) - x) ≤ v21KernelX x := by
  let D : Set ℝ := Icc (89 / 100 : ℝ) (19 / 20 : ℝ)
  have hxD : x ∈ D := by exact ⟨hxlo, hxhi⟩
  have heD : (19 / 20 : ℝ) ∈ D := by
    constructor <;> norm_num
  have hdiffClosed : DifferentiableOn ℝ v21KernelX D := by
    intro z hz
    exact (v21_kernelX_hasDerivAt hz.1).differentiableAt.differentiableWithinAt
  have hcont : ContinuousOn v21KernelX D := hdiffClosed.continuousOn
  have hdiffInt : DifferentiableOn ℝ v21KernelX (interior D) :=
    hdiffClosed.mono interior_subset
  have hder :
      ∀ z ∈ interior D, deriv v21KernelX z ≤ -(3 / 200 : ℝ) := by
    intro z hz
    have hzD : z ∈ D := interior_subset hz
    exact v21_kernelX_deriv_le_first_band hzD.1 hzD.2
  have hslope :=
    (convex_Icc : Convex ℝ D).image_sub_le_mul_sub_of_deriv_le
      hcont hdiffInt hder x hxD (19 / 20 : ℝ) heD hxhi
  dsimp [D] at hslope
  linarith

/-- Uniform lower bound on the signed kernel throughout the first exclusion
interval, including the linear gain away from the right endpoint. -/
lemma v21_k_first_band_linear_lower {x : ℝ}
    (hxcert : v17KernelCertPoint < x)
    (hxhi : x ≤ (19 / 20 : ℝ)) :
    (523 / 5000 : ℝ) +
        (3 / 200 : ℝ) * ((19 / 20 : ℝ) - x) ≤ limitingk x := by
  have hxlo : (89 / 100 : ℝ) ≤ x := by
    simpa [v17KernelCertPoint] using le_of_lt hxcert
  have htransfer := v21_kernelX_first_band_linear_lower hxlo hxhi
  have heA := v21_A_lt_B_first_band (x := (19 / 20 : ℝ)) (by norm_num)
  have heqEnd : limitingk (19 / 20 : ℝ) = v21KernelX (19 / 20 : ℝ) := by
    simpa [v21KernelX] using
      (v21_limitingk_eq_kernelB (x := (19 / 20 : ℝ)) heA)
  have hend : (523 / 5000 : ℝ) < v21KernelX (19 / 20 : ℝ) := by
    rw [← heqEnd]
    exact v21_k_at_095_lower
  have hxA := v21_A_lt_B_of_cert_lt hxcert
  have heqx : limitingk x = v21KernelX x := by
    simpa [v21KernelX] using v21_limitingk_eq_kernelB (x := x) hxA
  rw [heqx]
  linarith

/-- The first complementary interval `(0.89,0.95)` is excluded internally:
its weakest one-body contribution already reaches the target `delta`. -/
theorem v21_first_gap_exclusion :
    ∀ x : ℝ, v17KernelCertPoint < x → x < (19 / 20 : ℝ) →
      delta ≤ v21MinOneBody x := by
  intro x hxcert hx95
  have hxhi : x ≤ (19 / 20 : ℝ) := le_of_lt hx95
  let d : ℝ := (19 / 20 : ℝ) - x
  let q : ℝ := (523 / 5000 : ℝ) + (3 / 200 : ℝ) * d

  have hd0 : 0 ≤ d := by
    dsimp [d]
    linarith
  have hq0 : 0 ≤ q := by
    dsimp [q]
    positivity
  have hkraw := v21_k_first_band_linear_lower hxcert hxhi
  have hk : q ≤ limitingk x := by
    simpa [q, d] using hkraw
  have hw : q ^ 2 ≤ limitingWeight x :=
    v21_weight_lower_of_k_lower hq0 hk

  have hendmargin :
      delta ≤
        (2714 / 10000000 : ℝ) * (19 / 20 : ℝ) +
          (1 / 3 : ℝ) * (523 / 5000 : ℝ) ^ 2 := by
    norm_num [delta]
  have hcoef :
      0 ≤
        (2 * (523 / 5000 : ℝ) * (3 / 200 : ℝ) / 3) -
          (2714 / 10000000 : ℝ) := by
    norm_num
  have hpoly :
      delta ≤
        (2714 / 10000000 : ℝ) * x + (1 / 3 : ℝ) * q ^ 2 := by
    have hid :
        (2714 / 10000000 : ℝ) * x + (1 / 3 : ℝ) * q ^ 2 =
          (2714 / 10000000 : ℝ) * (19 / 20 : ℝ) +
            (1 / 3 : ℝ) * (523 / 5000 : ℝ) ^ 2 +
            d *
              ((2 * (523 / 5000 : ℝ) * (3 / 200 : ℝ) / 3) -
                (2714 / 10000000 : ℝ)) +
            (1 / 3 : ℝ) * (3 / 200 : ℝ) ^ 2 * d ^ 2 := by
      dsimp [q, d]
      ring
    rw [hid]
    have hlin :
        0 ≤ d *
          ((2 * (523 / 5000 : ℝ) * (3 / 200 : ℝ) / 3) -
            (2714 / 10000000 : ℝ)) :=
      mul_nonneg hd0 hcoef
    have hquad :
        0 ≤ (1 / 3 : ℝ) * (3 / 200 : ℝ) ^ 2 * d ^ 2 := by positivity
    linarith

  unfold v21MinOneBody
  nlinarith

end HurtadoZeta23
