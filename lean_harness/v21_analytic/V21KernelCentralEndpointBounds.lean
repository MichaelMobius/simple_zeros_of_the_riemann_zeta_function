import HurtadoZeta23.V21KernelCentralLobes
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic

noncomputable section

open Set

namespace HurtadoZeta23

/-- Removing the alternating lobe sign leaves exactly the root-cell numerator
`H_n` divided by the positive normalized-kernel denominator. -/
lemma v21_signedKernel_eq_rootH_div (n : ℕ) (x : ℝ) :
    v21SignedKernel n x = v21RootH n x / v21D x := by
  unfold v21SignedKernel v21KernelX
  rw [v21_kernelB_eq_sign_rootH_div n x]
  have hs : ((-1 : ℝ) ^ n) ^ 2 = 1 := by
    simpa using (sq_abs ((-1 : ℝ) ^ n)).symm
  calc
    (-1 : ℝ) ^ n *
        (((-1 : ℝ) ^ n * v21RootH n x) / v21D x) =
      ((((-1 : ℝ) ^ n) ^ 2) * v21RootH n x) / v21D x := by ring
    _ = v21RootH n x / v21D x := by rw [hs, one_mul]

/-- A root-free lower bound for the sine factor in an integer cell.  It is
centered at the half-integer where the sine is maximal and uses only the
global elementary inequality `1 - t^2/2 ≤ cos t` plus the rational upper
bound for π. -/
lemma v21_sin_cell_lower_of_deviation {n : ℕ} {x r : ℝ}
    (hr0 : 0 ≤ r)
    (hdev : |x - ((n : ℝ) + (1 / 2 : ℝ))| ≤ r) :
    1 - (v21RootPiU * r) ^ 2 / 2 ≤
      Real.sin (Real.pi * (x - (n : ℝ))) := by
  let z : ℝ := Real.pi * (x - ((n : ℝ) + (1 / 2 : ℝ)))
  have hpiU : Real.pi ≤ v21RootPiU := by
    simpa [v21RootPiU] using (le_of_lt v21_pi_upper)
  have hpiU0 : 0 ≤ v21RootPiU := by norm_num [v21RootPiU]
  have hcap0 : 0 ≤ v21RootPiU * r := mul_nonneg hpiU0 hr0
  have hzabs : |z| ≤ v21RootPiU * r := by
    dsimp [z]
    rw [abs_mul, abs_of_pos Real.pi_pos]
    exact mul_le_mul hpiU hdev (abs_nonneg _) hpiU0
  have hsqAbs := pow_le_pow_left₀ (abs_nonneg z) hzabs 2
  have hsq : z ^ 2 ≤ (v21RootPiU * r) ^ 2 := by
    simpa using hsqAbs
  have hcos := Real.one_sub_sq_div_two_le_cos (x := z)
  have hzphase :
      z = Real.pi * (x - (n : ℝ)) - Real.pi / 2 := by
    dsimp [z]
    ring
  rw [hzphase] at hsq
  rw [hzphase, Real.cos_sub_pi_div_two] at hcos
  linarith

/-- Central-cell lower bound for the cleared numerator.  The only
transcendental input is the elementary cosine lower bound packaged above;
all constants on the left are rational. -/
lemma v21_rootH_central_lower {n : ℕ} {x r : ℝ}
    (hx0 : 0 ≤ x) (hr0 : 0 ≤ r)
    (hdev : |x - ((n : ℝ) + (1 / 2 : ℝ))| ≤ r)
    (hslow0 : 0 ≤ 1 - (v21RootPiU * r) ^ 2 / 2) :
    v21RootCL * v21RootPiL * x *
          (1 - (v21RootPiU * r) ^ 2 / 2) - (1 / 2 : ℝ) ≤
      v21RootH n x := by
  have hs := v21_sin_cell_lower_of_deviation (n := n) hr0 hdev
  have hpiL : v21RootPiL ≤ Real.pi := by
    simpa [v21RootPiL] using (le_of_lt v21_pi_lower)
  have hCL : v21RootCL ≤ v21C := by
    simpa [v21RootCL] using v21_C_lower
  have hpiL0 : 0 ≤ v21RootPiL := by norm_num [v21RootPiL]
  have hCL0 : 0 ≤ v21RootCL := by norm_num [v21RootCL]
  have hC0 : 0 ≤ v21C := by nlinarith [v21_C_gt_half]
  have hCpi : v21RootCL * v21RootPiL ≤ v21C * Real.pi :=
    mul_le_mul hCL hpiL hpiL0 hC0
  have hcoef :
      v21RootCL * v21RootPiL * x ≤ v21C * Real.pi * x :=
    mul_le_mul_of_nonneg_right hCpi hx0
  have hcoefL0 : 0 ≤ v21RootCL * v21RootPiL * x :=
    mul_nonneg (mul_nonneg hCL0 hpiL0) hx0
  have hs0 : 0 ≤ Real.sin (Real.pi * (x - (n : ℝ))) :=
    hslow0.trans hs
  have hterm1 :
      v21RootCL * v21RootPiL * x *
          (1 - (v21RootPiU * r) ^ 2 / 2) ≤
        v21RootCL * v21RootPiL * x *
          Real.sin (Real.pi * (x - (n : ℝ))) :=
    mul_le_mul_of_nonneg_left hs hcoefL0
  have hterm2 :
      v21RootCL * v21RootPiL * x *
          Real.sin (Real.pi * (x - (n : ℝ))) ≤
        v21C * Real.pi * x *
          Real.sin (Real.pi * (x - (n : ℝ))) :=
    mul_le_mul_of_nonneg_right hcoef hs0
  have hcos : Real.cos (Real.pi * (x - (n : ℝ))) ≤ 1 :=
    Real.cos_le_one _
  unfold v21RootH
  linarith

/-- Transfer a rational lower bound on the cleared numerator to the signed
kernel, using a rational upper cap for the positive denominator. -/
lemma v21_signedKernel_lower_of_rootH_cap {n : ℕ} {x U q : ℝ}
    (hxcert : v17KernelCertPoint < x)
    (hx0 : 0 ≤ x) (hxU : x ≤ U) (hq0 : 0 ≤ q)
    (hH : q * v21RootDenCap U ≤ v21RootH n x) :
    q ≤ v21SignedKernel n x := by
  rw [v21_signedKernel_eq_rootH_div]
  have hD : 0 < v21D x := v21_D_pos (v21_A_lt_B_of_cert_lt hxcert)
  apply (le_div_iff₀ hD).2
  calc
    q * v21D x ≤ q * v21RootDenCap U :=
      mul_le_mul_of_nonneg_left (v21_D_le_rootDenCap hx0 hxU) hq0
    _ ≤ v21RootH n x := hH

/-- One-shot rational endpoint certificate for the central part of a lobe.
After supplying rational `x`, `r`, and `q`, the last hypothesis is typically
closed by `norm_num`. -/
lemma v21_signedKernel_central_lower {n : ℕ} {x r q : ℝ}
    (hxcert : v17KernelCertPoint < x)
    (hx0 : 0 ≤ x) (hr0 : 0 ≤ r) (hq0 : 0 ≤ q)
    (hdev : |x - ((n : ℝ) + (1 / 2 : ℝ))| ≤ r)
    (hslow0 : 0 ≤ 1 - (v21RootPiU * r) ^ 2 / 2)
    (hq : q * v21RootDenCap x ≤
      v21RootCL * v21RootPiL * x *
        (1 - (v21RootPiU * r) ^ 2 / 2) - (1 / 2 : ℝ)) :
    q ≤ v21SignedKernel n x := by
  apply v21_signedKernel_lower_of_rootH_cap
    (n := n) hxcert hx0 le_rfl hq0
  exact hq.trans (v21_rootH_central_lower hx0 hr0 hdev hslow0)

/-- Uniform box version of the preceding endpoint certificate.  This is
useful for a short tail that extends past the concavity strip: the numerator
is frozen at the rational left endpoint `L` and the denominator at `U`. -/
lemma v21_signedKernel_central_box_lower {n : ℕ} {L U r q x : ℝ}
    (hxcert : v17KernelCertPoint < x)
    (hL0 : 0 ≤ L) (hLx : L ≤ x) (hxU : x ≤ U)
    (hr0 : 0 ≤ r) (hq0 : 0 ≤ q)
    (hdev : |x - ((n : ℝ) + (1 / 2 : ℝ))| ≤ r)
    (hslow0 : 0 ≤ 1 - (v21RootPiU * r) ^ 2 / 2)
    (hq : q * v21RootDenCap U ≤
      v21RootCL * v21RootPiL * L *
        (1 - (v21RootPiU * r) ^ 2 / 2) - (1 / 2 : ℝ)) :
    q ≤ v21SignedKernel n x := by
  have hx0 : 0 ≤ x := hL0.trans hLx
  apply v21_signedKernel_lower_of_rootH_cap
    (n := n) hxcert hx0 hxU hq0
  have hroot := v21_rootH_central_lower
    (n := n) hx0 hr0 hdev hslow0
  have hcoef0 : 0 ≤ v21RootCL * v21RootPiL := by
    norm_num [v21RootCL, v21RootPiL]
  have hLX :
      v21RootCL * v21RootPiL * L ≤
        v21RootCL * v21RootPiL * x :=
    mul_le_mul_of_nonneg_left hLx hcoef0
  have hmul :
      v21RootCL * v21RootPiL * L *
          (1 - (v21RootPiU * r) ^ 2 / 2) ≤
        v21RootCL * v21RootPiL * x *
          (1 - (v21RootPiU * r) ^ 2 / 2) :=
    mul_le_mul_of_nonneg_right hLX hslow0
  linarith

/-- Concavity turns two endpoint certificates into a certificate on the
whole subinterval. -/
lemma v21_signedKernel_lower_on_central_interval {n : ℕ} (hn1 : 1 ≤ n)
    {a b q x : ℝ}
    (ha : a ∈ Icc ((n : ℝ) + (3 / 20 : ℝ))
      ((n : ℝ) + (17 / 20 : ℝ)))
    (hb : b ∈ Icc ((n : ℝ) + (3 / 20 : ℝ))
      ((n : ℝ) + (17 / 20 : ℝ)))
    (hx : x ∈ Icc a b)
    (hqa : q ≤ v21SignedKernel n a)
    (hqb : q ≤ v21SignedKernel n b) :
    q ≤ v21SignedKernel n x := by
  have hmin := (v21_signedKernel_concave_central hn1).min_le_of_mem_Icc
    ha hb hx
  exact (le_min hqa hqb).trans hmin

/-- The squared signed kernel is exactly the kernel weight once we are beyond
the already-certified normalization threshold. -/
lemma v21_limitingWeight_eq_signedKernel_sq {n : ℕ} {x : ℝ}
    (hxcert : v17KernelCertPoint < x) :
    limitingWeight x = (v21SignedKernel n x) ^ 2 := by
  have hk : limitingk x = v21KernelX x := by
    simpa [v21KernelX] using
      (v21_limitingk_eq_kernelB (v21_A_lt_B_of_cert_lt hxcert))
  have hs : ((-1 : ℝ) ^ n) ^ 2 = 1 := by
    simpa using (sq_abs ((-1 : ℝ) ^ n)).symm
  unfold limitingWeight v21SignedKernel
  rw [hk, mul_pow, hs, one_mul]

lemma v21_weight_lower_of_signedKernel_lower {n : ℕ} {x q : ℝ}
    (hxcert : v17KernelCertPoint < x) (hq0 : 0 ≤ q)
    (hq : q ≤ v21SignedKernel n x) :
    q ^ 2 ≤ limitingWeight x := by
  have hs := pow_le_pow_left₀ hq0 hq 2
  rw [v21_limitingWeight_eq_signedKernel_sq hxcert]
  exact hs

end HurtadoZeta23
