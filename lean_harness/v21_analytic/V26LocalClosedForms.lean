import HurtadoZeta23.V26FinalConvexityCore
import HurtadoZeta23.V21KernelRootWeight
import Mathlib.Tactic

noncomputable section

namespace HurtadoZeta23

/-- Phase relative to the integer root cell. -/
def v26LocalPhase (N : ℕ) (x : ℝ) : ℝ :=
  Real.pi * (x - (N : ℝ))

/-- First-derivative numerator with the common integer-cell sign removed. -/
def v26LocalM1 (N : ℕ) (x : ℝ) : ℝ :=
  (v21C * (v21B x) ^ 3 - (1 / 2 : ℝ) * v21C * v21B x + v21B x) *
      Real.cos (v26LocalPhase N x) +
    (-v21C * (v21B x) ^ 2 + (1 / 2 : ℝ) * (v21B x) ^ 2 -
      (1 / 2 : ℝ) * v21C - (1 / 4 : ℝ)) *
      Real.sin (v26LocalPhase N x)

/-- Second-derivative numerator with the common integer-cell sign removed. -/
def v26LocalM2 (N : ℕ) (x : ℝ) : ℝ :=
  v21P2 (v21B x) * Real.cos (v26LocalPhase N x) +
    v21Q2 (v21B x) * Real.sin (v26LocalPhase N x)

lemma v26_B_eq_local_add (N : ℕ) (x : ℝ) :
    v21B x = v26LocalPhase N x + (N : ℝ) * Real.pi := by
  unfold v21B v26LocalPhase
  ring

lemma v26_sinB_local (N : ℕ) (x : ℝ) :
    Real.sin (v21B x) = (-1 : ℝ) ^ N * Real.sin (v26LocalPhase N x) := by
  rw [v26_B_eq_local_add N x]
  simpa using Real.sin_add_nat_mul_pi (v26LocalPhase N x) N

lemma v26_cosB_local (N : ℕ) (x : ℝ) :
    Real.cos (v21B x) = (-1 : ℝ) ^ N * Real.cos (v26LocalPhase N x) := by
  rw [v26_B_eq_local_add N x]
  simpa using Real.cos_add_nat_mul_pi (v26LocalPhase N x) N

lemma v26_M1_local (N : ℕ) (x : ℝ) :
    v21M1 (v21B x) = (-1 : ℝ) ^ N * v26LocalM1 N x := by
  unfold v21M1 v26LocalM1
  rw [v26_sinB_local N x, v26_cosB_local N x]
  ring

lemma v26_M2_local (N : ℕ) (x : ℝ) :
    v21M2 (v21B x) = (-1 : ℝ) ^ N * v26LocalM2 N x := by
  unfold v21M2 v26LocalM2
  rw [v26_sinB_local N x, v26_cosB_local N x]
  ring

lemma v26_sign_sq (N : ℕ) : (((-1 : ℝ) ^ N) ^ 2) = 1 := by
  rw [← sq_abs, abs_neg_one_pow]
  norm_num

/-- Local root-cell closed form for the exact first derivative of the weight. -/
theorem v26_weightXPrime_local_closed {N : ℕ} {x : ℝ}
    (hD : v21D x ≠ 0) :
    v26WeightXPrime x =
      2 * Real.pi * v21RootH N x * v26LocalM1 N x / (v21D x) ^ 3 := by
  unfold v26WeightXPrime v21KernelXPrime v21KernelX
  unfold v21KernelBPrime v21KernelB
  have hnum := v21_root_numerator_eq N x
  have hm1 := v26_M1_local N x
  have hs := v26_sign_sq N
  unfold v21D at hD ⊢
  rw [hnum, hm1]
  field_simp [hD]
  rw [hs]
  ring

/-- Local root-cell closed form for the exact second derivative of the weight. -/
theorem v26_weightXSecond_local_closed {N : ℕ} {x : ℝ}
    (hD : v21D x ≠ 0) :
    v26WeightXSecond x =
      2 * Real.pi ^ 2 *
        ((v26LocalM1 N x) ^ 2 + v21RootH N x * v26LocalM2 N x) /
        (v21D x) ^ 4 := by
  unfold v26WeightXSecond v21KernelXPrime v21KernelXSecond v21KernelX
  unfold v21KernelBPrime v21KernelB
  have hnum := v21_root_numerator_eq N x
  have hm1 := v26_M1_local N x
  have hm2 := v26_M2_local N x
  have hs := v26_sign_sq N
  unfold v21D at hD ⊢
  rw [hnum, hm1, hm2]
  field_simp [hD]
  rw [hs]
  ring

end HurtadoZeta23
