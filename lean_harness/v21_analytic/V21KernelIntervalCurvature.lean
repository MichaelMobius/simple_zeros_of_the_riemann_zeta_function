import HurtadoZeta23.V21KernelCurvatureSigns
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic

noncomputable section

open Set

namespace HurtadoZeta23

/-- The normalized kernel pulled back from phase space by `b = π x`. -/
def v21KernelX (x : ℝ) : ℝ := v21KernelB (v21B x)

/-- First derivative of `v21KernelX`. -/
def v21KernelXPrime (x : ℝ) : ℝ :=
  Real.pi * v21KernelBPrime (v21B x)

/-- Second derivative of `v21KernelX`. -/
def v21KernelXSecond (x : ℝ) : ℝ :=
  Real.pi ^ 2 *
    (v21M2 (v21B x) / ((v21B x) ^ 2 - (1 / 2 : ℝ)) ^ 3)

lemma v21_B_hasDerivAt_interval (x : ℝ) : HasDerivAt v21B Real.pi x := by
  unfold v21B
  exact hasDerivAt_const_mul (x := x) Real.pi

lemma v21_kernel_den_ne_of_cert_lt {x : ℝ}
    (hx : v17KernelCertPoint < x) :
    (v21B x) ^ 2 - (1 / 2 : ℝ) ≠ 0 := by
  have hpos := v21_D_pos (v21_A_lt_B_of_cert_lt hx)
  simpa [v21D] using ne_of_gt hpos

lemma v21_kernel_den_pos_of_cert_lt {x : ℝ}
    (hx : v17KernelCertPoint < x) :
    0 < (v21B x) ^ 2 - (1 / 2 : ℝ) := by
  simpa [v21D] using v21_D_pos (v21_A_lt_B_of_cert_lt hx)

/-- Exact first derivative after returning to the physical separation variable. -/
theorem v21_kernelX_hasDerivAt {x : ℝ}
    (hD : (v21B x) ^ 2 - (1 / 2 : ℝ) ≠ 0) :
    HasDerivAt v21KernelX (v21KernelXPrime x) x := by
  have hcomp := (v21_kernelB_hasDerivAt hD).comp x (v21_B_hasDerivAt_interval x)
  simpa [v21KernelX, v21KernelXPrime, Function.comp_apply, mul_comm] using hcomp

/-- Exact second derivative after returning to the physical separation variable. -/
theorem v21_kernelXPrime_hasDerivAt {x : ℝ}
    (hD : (v21B x) ^ 2 - (1 / 2 : ℝ) ≠ 0) :
    HasDerivAt v21KernelXPrime (v21KernelXSecond x) x := by
  have hcomp := (v21_kernelBPrime_hasDerivAt hD).comp x (v21_B_hasDerivAt_interval x)
  have hscaled :
      HasDerivAt
        (fun y : ℝ => Real.pi * v21KernelBPrime (v21B y))
        (Real.pi *
          ((v21M2 (v21B x) /
            ((v21B x) ^ 2 - (1 / 2 : ℝ)) ^ 3) * Real.pi)) x := by
    simpa only [Function.comp_apply] using hcomp.const_mul Real.pi
  simpa [v21KernelXPrime, v21KernelXSecond, Function.comp_apply, pow_two,
    mul_comm, mul_left_comm, mul_assoc] using hscaled

lemma v21_kernelXSecond_nonneg_second_band {x : ℝ}
    (hx1 : (6 / 5 : ℝ) ≤ x) (hx2 : x ≤ (179 / 100 : ℝ)) :
    0 ≤ v21KernelXSecond x := by
  have hxcert : v17KernelCertPoint < x := by
    have : (89 / 100 : ℝ) < x := by nlinarith
    simpa [v17KernelCertPoint] using this
  have hden := v21_kernel_den_pos_of_cert_lt hxcert
  have hm := v21_M2_nonneg_second_band hx1 hx2
  have hquot :
      0 ≤ v21M2 (v21B x) / ((v21B x) ^ 2 - (1 / 2 : ℝ)) ^ 3 :=
    div_nonneg hm (pow_nonneg hden.le 3)
  unfold v21KernelXSecond
  exact mul_nonneg (sq_nonneg Real.pi) hquot

lemma v21_kernelXSecond_nonpos_third_band {x : ℝ}
    (hx1 : (237 / 100 : ℝ) ≤ x) (hx2 : x ≤ (261 / 100 : ℝ)) :
    v21KernelXSecond x ≤ 0 := by
  have hxcert : v17KernelCertPoint < x := by
    have : (89 / 100 : ℝ) < x := by nlinarith
    simpa [v17KernelCertPoint] using this
  have hden := v21_kernel_den_pos_of_cert_lt hxcert
  have hm := v21_M2_nonpos_third_band hx1 hx2
  have hquot :
      v21M2 (v21B x) / ((v21B x) ^ 2 - (1 / 2 : ℝ)) ^ 3 ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg hm (pow_nonneg hden.le 3)
  unfold v21KernelXSecond
  exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg Real.pi) hquot

/-- The normalized kernel is convex on the second excluded band. -/
theorem v21_kernelX_convex_second_band :
    ConvexOn ℝ (Icc (6 / 5 : ℝ) (179 / 100 : ℝ)) v21KernelX := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _)
  · intro x hx
    have hxcert : v17KernelCertPoint < x := by
      have : (89 / 100 : ℝ) < x := by nlinarith [hx.1]
      simpa [v17KernelCertPoint] using this
    exact (v21_kernelX_hasDerivAt (v21_kernel_den_ne_of_cert_lt hxcert)).continuousAt.continuousWithinAt
  · intro x hx
    have hxIcc : x ∈ Icc (6 / 5 : ℝ) (179 / 100 : ℝ) := interior_subset hx
    have hxcert : v17KernelCertPoint < x := by
      have : (89 / 100 : ℝ) < x := by nlinarith [hxIcc.1]
      simpa [v17KernelCertPoint] using this
    exact (v21_kernelX_hasDerivAt (v21_kernel_den_ne_of_cert_lt hxcert)).hasDerivWithinAt
  · intro x hx
    have hxIcc : x ∈ Icc (6 / 5 : ℝ) (179 / 100 : ℝ) := interior_subset hx
    have hxcert : v17KernelCertPoint < x := by
      have : (89 / 100 : ℝ) < x := by nlinarith [hxIcc.1]
      simpa [v17KernelCertPoint] using this
    exact (v21_kernelXPrime_hasDerivAt (v21_kernel_den_ne_of_cert_lt hxcert)).hasDerivWithinAt
  · intro x hx
    have hxIcc : x ∈ Icc (6 / 5 : ℝ) (179 / 100 : ℝ) := interior_subset hx
    exact v21_kernelXSecond_nonneg_second_band hxIcc.1 hxIcc.2

/-- Hence the signed second-lobe kernel `-k` is concave. -/
theorem v21_negKernelX_concave_second_band :
    ConcaveOn ℝ (Icc (6 / 5 : ℝ) (179 / 100 : ℝ)) (-v21KernelX) :=
  v21_kernelX_convex_second_band.neg

/-- The normalized kernel itself is concave on the third excluded band. -/
theorem v21_kernelX_concave_third_band :
    ConcaveOn ℝ (Icc (237 / 100 : ℝ) (261 / 100 : ℝ)) v21KernelX := by
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc _ _)
  · intro x hx
    have hxcert : v17KernelCertPoint < x := by
      have : (89 / 100 : ℝ) < x := by nlinarith [hx.1]
      simpa [v17KernelCertPoint] using this
    exact (v21_kernelX_hasDerivAt (v21_kernel_den_ne_of_cert_lt hxcert)).continuousAt.continuousWithinAt
  · intro x hx
    have hxIcc : x ∈ Icc (237 / 100 : ℝ) (261 / 100 : ℝ) := interior_subset hx
    have hxcert : v17KernelCertPoint < x := by
      have : (89 / 100 : ℝ) < x := by nlinarith [hxIcc.1]
      simpa [v17KernelCertPoint] using this
    exact (v21_kernelX_hasDerivAt (v21_kernel_den_ne_of_cert_lt hxcert)).hasDerivWithinAt
  · intro x hx
    have hxIcc : x ∈ Icc (237 / 100 : ℝ) (261 / 100 : ℝ) := interior_subset hx
    have hxcert : v17KernelCertPoint < x := by
      have : (89 / 100 : ℝ) < x := by nlinarith [hxIcc.1]
      simpa [v17KernelCertPoint] using this
    exact (v21_kernelXPrime_hasDerivAt (v21_kernel_den_ne_of_cert_lt hxcert)).hasDerivWithinAt
  · intro x hx
    have hxIcc : x ∈ Icc (237 / 100 : ℝ) (261 / 100 : ℝ) := interior_subset hx
    exact v21_kernelXSecond_nonpos_third_band hxIcc.1 hxIcc.2

end HurtadoZeta23