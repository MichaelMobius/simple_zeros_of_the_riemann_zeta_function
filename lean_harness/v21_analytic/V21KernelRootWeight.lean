import HurtadoZeta23.V21KernelRootQuadratic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

noncomputable section

namespace HurtadoZeta23

/-- Rational upper cap for the positive normalized-kernel denominator on
`0 ≤ x ≤ U`. -/
def v21RootDenCap (U : ℝ) : ℝ :=
  (v21RootPiU * U) ^ 2 - (1 / 2 : ℝ)

/-- The normalized kernel numerator differs from the cell-centered numerator
only by the exact sign `(-1)^n`. -/
lemma v21_root_numerator_eq (n : ℕ) (x : ℝ) :
    v21C * v21B x * Real.sin (v21B x) -
        (1 / 2 : ℝ) * Real.cos (v21B x) =
      (-1 : ℝ) ^ n * v21RootH n x := by
  let t : ℝ := Real.pi * (x - (n : ℝ))
  have hB : v21B x = t + (n : ℝ) * Real.pi := by
    dsimp [t]
    unfold v21B
    ring
  have hsin :
      Real.sin (v21B x) = (-1 : ℝ) ^ n * Real.sin t := by
    rw [hB]
    simpa using Real.sin_add_nat_mul_pi t n
  have hcos :
      Real.cos (v21B x) = (-1 : ℝ) ^ n * Real.cos t := by
    rw [hB]
    simpa using Real.cos_add_nat_mul_pi t n
  rw [hsin, hcos]
  dsimp [t]
  unfold v21B v21RootH
  ring

/-- Squaring removes the cell sign. -/
lemma v21_root_numerator_sq (n : ℕ) (x : ℝ) :
    (v21C * v21B x * Real.sin (v21B x) -
        (1 / 2 : ℝ) * Real.cos (v21B x)) ^ 2 =
      (v21RootH n x) ^ 2 := by
  rw [v21_root_numerator_eq n x, mul_pow]
  have hsignsq : ((-1 : ℝ) ^ n) ^ 2 = 1 := by
    simpa using (sq_abs ((-1 : ℝ) ^ n)).symm
  rw [hsignsq, one_mul]

/-- Exact signed root-cell form of the phase-normalized kernel. -/
lemma v21_kernelB_eq_sign_rootH_div (n : ℕ) (x : ℝ) :
    v21KernelB (v21B x) =
      (-1 : ℝ) ^ n * v21RootH n x / v21D x := by
  unfold v21KernelB v21D
  rw [v21_root_numerator_eq n x]

/-- Exact signed root-cell form of the physical normalized kernel. -/
lemma v21_limitingk_eq_sign_rootH_div {n : ℕ} {x : ℝ}
    (hx : v17KernelCertPoint < x) :
    limitingk x = (-1 : ℝ) ^ n * v21RootH n x / v21D x := by
  rw [v21_limitingk_eq_kernelB (v21_A_lt_B_of_cert_lt hx)]
  exact v21_kernelB_eq_sign_rootH_div n x

/-- Exact root-cell representation of the limiting weight. -/
lemma v21_limitingWeight_eq_rootH_sq_div {n : ℕ} {x : ℝ}
    (hx : v17KernelCertPoint < x) :
    limitingWeight x = (v21RootH n x) ^ 2 / (v21D x) ^ 2 := by
  have hA := v21_A_lt_B_of_cert_lt hx
  rw [v21_limitingWeight_normalized hA]
  rw [div_pow]
  unfold v21D
  rw [v21_root_numerator_sq n x]

/-- The positive denominator is bounded above by a rational cap whenever
`0 ≤ x ≤ U`. -/
lemma v21_D_le_rootDenCap {x U : ℝ}
    (hx0 : 0 ≤ x) (hxU : x ≤ U) :
    v21D x ≤ v21RootDenCap U := by
  have hpiU : Real.pi ≤ v21RootPiU := by
    simpa [v21RootPiU] using (le_of_lt v21_pi_upper)
  have hPiU0 : 0 ≤ v21RootPiU := by norm_num [v21RootPiU]
  have hU0 : 0 ≤ U := hx0.trans hxU
  have hB0 : 0 ≤ v21B x := by
    unfold v21B
    positivity
  have hcapB0 : 0 ≤ v21RootPiU * U := mul_nonneg hPiU0 hU0
  have hB : v21B x ≤ v21RootPiU * U := by
    unfold v21B
    calc
      Real.pi * x ≤ v21RootPiU * x :=
        mul_le_mul_of_nonneg_right hpiU hx0
      _ ≤ v21RootPiU * U :=
        mul_le_mul_of_nonneg_left hxU hPiU0
  have hsq : (v21B x) ^ 2 ≤ (v21RootPiU * U) ^ 2 := by
    have hp :
        0 ≤ (v21RootPiU * U - v21B x) *
          (v21RootPiU * U + v21B x) :=
      mul_nonneg (sub_nonneg.mpr hB) (add_nonneg hcapB0 hB0)
    nlinarith
  unfold v21D v21RootDenCap
  linarith

lemma v21_D_sq_le_rootDenCap_sq {x U : ℝ}
    (hx : v17KernelCertPoint < x)
    (hx0 : 0 ≤ x) (hxU : x ≤ U) :
    (v21D x) ^ 2 ≤ (v21RootDenCap U) ^ 2 := by
  have hA := v21_A_lt_B_of_cert_lt hx
  have hDpos := v21_D_pos hA
  have hle := v21_D_le_rootDenCap hx0 hxU
  have hcap0 : 0 ≤ v21RootDenCap U := hDpos.le.trans hle
  have hp :
      0 ≤ (v21RootDenCap U - v21D x) *
        (v21RootDenCap U + v21D x) :=
    mul_nonneg (sub_nonneg.mpr hle) (add_nonneg hcap0 hDpos.le)
  nlinarith

/-- Generic quotient transfer: a lower bound for the squared root numerator
becomes a lower bound for the limiting weight after replacing the denominator
by its rational upper cap. -/
lemma v21_weight_lower_of_rootH_sq {n : ℕ} {x U Q : ℝ}
    (hx : v17KernelCertPoint < x)
    (hx0 : 0 ≤ x) (hxU : x ≤ U)
    (hQ : Q ≤ (v21RootH n x) ^ 2) :
    Q / (v21RootDenCap U) ^ 2 ≤ limitingWeight x := by
  rw [v21_limitingWeight_eq_rootH_sq_div (n := n) hx]
  have hA := v21_A_lt_B_of_cert_lt hx
  have hDpos := v21_D_pos hA
  have hDsqpos : 0 < (v21D x) ^ 2 := pow_pos hDpos 2
  have hDsq := v21_D_sq_le_rootDenCap_sq hx hx0 hxU
  have hcapPos : 0 < v21RootDenCap U :=
    hDpos.trans_le (v21_D_le_rootDenCap hx0 hxU)
  have hcapSqPos : 0 < (v21RootDenCap U) ^ 2 := pow_pos hcapPos 2
  by_cases hQ0 : Q ≤ 0
  · have hleft : Q / (v21RootDenCap U) ^ 2 ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg hQ0 hcapSqPos.le
    have hright : 0 ≤ (v21RootH n x) ^ 2 / (v21D x) ^ 2 :=
      div_nonneg (sq_nonneg _) hDsqpos.le
    exact hleft.trans hright
  · have hQpos : 0 < Q := lt_of_not_ge hQ0
    rw [div_le_div_iff₀ hcapSqPos hDsqpos]
    calc
      Q * (v21D x) ^ 2 ≤ Q * (v21RootDenCap U) ^ 2 :=
        mul_le_mul_of_nonneg_left hDsq hQpos.le
      _ ≤ (v21RootH n x) ^ 2 * (v21RootDenCap U) ^ 2 :=
        mul_le_mul_of_nonneg_right hQ (sq_nonneg _)

/-- Direct rational weight minorant obtained from the root-free quadratic. -/
lemma v21_weight_ge_root_quadratic {n : ℕ} (hn1 : 1 ≤ n) (hn12 : n ≤ 12)
    {x U : ℝ}
    (hxL : (n : ℝ) - (1 / 20 : ℝ) ≤ x)
    (hxCellU : x ≤ (n : ℝ) + (151 / 1000 : ℝ))
    (hxU : x ≤ U) :
    (((7 : ℝ) * (n : ℝ)) ^ 2 *
        ((99 / 100 : ℝ) * (x - v21RootMid n) ^ 2 -
          99 * (1 / 200000 : ℝ) ^ 2)) /
        (v21RootDenCap U) ^ 2 ≤ limitingWeight x := by
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hx0 : 0 ≤ x := by nlinarith
  have hx89 : (89 / 100 : ℝ) < x := by nlinarith
  have hxcert : v17KernelCertPoint < x := by
    simpa [v17KernelCertPoint] using hx89
  exact v21_weight_lower_of_rootH_sq hxcert hx0 hxU
    (v21_rootH_sq_ge_quadratic hn1 hn12 hxL hxCellU)

end HurtadoZeta23
