import HurtadoZeta23.V21KernelCentralLobes
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic

noncomputable section

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
  rw [hzphase, Real.cos_sub_pi_div_two] at hcos
  nlinarith

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

end HurtadoZeta23
