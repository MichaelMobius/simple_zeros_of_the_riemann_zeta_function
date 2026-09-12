import HurtadoZeta23.V21KernelCellTools
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Tactic

noncomputable section

open Filter Finset Real
open scoped BigOperators Topology

namespace HurtadoZeta23

private def v21RootCosTerm (x : ℝ) (n : ℕ) : ℝ :=
  x ^ (2 * n) / ((2 * n).factorial : ℝ)

private lemma v21RootCosTerm_antitone {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Antitone (v21RootCosTerm x) := by
  refine antitone_nat_of_succ_le ?_
  intro n
  unfold v21RootCosTerm
  have hpow : x ^ (2 * (n + 1)) ≤ x ^ (2 * n) :=
    pow_le_pow_of_le_one hx0 hx1 (by omega)
  have hden :
      ((2 * n).factorial : ℝ) ≤ ((2 * (n + 1)).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le (by omega : 2 * n ≤ 2 * (n + 1))
  calc
    x ^ (2 * (n + 1)) / ((2 * (n + 1)).factorial : ℝ)
        ≤ x ^ (2 * n) / ((2 * (n + 1)).factorial : ℝ) :=
      div_le_div_of_nonneg_right hpow (by positivity)
    _ ≤ x ^ (2 * n) / ((2 * n).factorial : ℝ) :=
      div_le_div_of_nonneg_left (pow_nonneg hx0 _) (by positivity) hden

/-- Five-term alternating Taylor upper bound for cosine on `[0,1]`. -/
lemma v21_cos_upper8 {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.cos x ≤
      1 - x^2 / 2 + x^4 / 24 - x^6 / 720 + x^8 / 40320 := by
  have ht :
      Tendsto
        (fun n : ℕ => ∑ i ∈ range n, (-1 : ℝ)^i * v21RootCosTerm x i)
        atTop (𝓝 (Real.cos x)) := by
    simpa [v21RootCosTerm, mul_div_assoc] using (Real.hasSum_cos x).tendsto_sum_nat
  have h := (v21RootCosTerm_antitone hx0 hx1).tendsto_le_alternating_series ht 2
  norm_num [v21RootCosTerm, sum_range_succ, Nat.factorial] at h ⊢
  linarith

/-- Rational lower enclosure for the profile sinc, used only to obtain a
matching upper enclosure for the normalized kernel constant. -/
lemma v21_sincA_lower_root :
    (37043 / 40320 : ℝ) ≤ v21SincA := by
  have hs := v21_sin_lower7 (x := v21A) v21_A_pos.le (le_of_lt v21_A_lt_one)
  unfold v21SincA
  apply (le_div_iff₀ v21_A_pos).2
  calc
    (37043 / 40320 : ℝ) * v21A =
        v21A - v21A^3 / 6 + v21A^5 / 120 - v21A^7 / 5040 := by
      rw [v21_A_pow3, v21_A_pow5, v21_A_pow7]
      ring
    _ ≤ Real.sin v21A := hs

/-- Rational upper enclosure for `cos(1/sqrt 2)`. -/
lemma v21_cosA_upper_root :
    Real.cos v21A ≤ (163483 / 215040 : ℝ) := by
  have hc := v21_cos_upper8 (x := v21A) v21_A_pos.le (le_of_lt v21_A_lt_one)
  calc
    Real.cos v21A ≤
        1 - v21A^2 / 2 + v21A^4 / 24 - v21A^6 / 720 +
          v21A^8 / 40320 := hc
    _ = (163483 / 215040 : ℝ) := by
      rw [v21_A_sq, v21_A_pow4, v21_A_pow6, v21_A_pow8]
      norm_num

/-- Matching rational upper enclosure for the sole profile constant. -/
lemma v21_C_upper :
    v21C ≤ (490449 / 592688 : ℝ) := by
  rw [v21_C_eq_cos_div_sinc]
  apply (div_le_iff₀ v21_sincA_pos).2
  have hscaled := mul_le_mul_of_nonneg_left v21_sincA_lower_root
    (show (0 : ℝ) ≤ 490449 / 592688 by norm_num)
  have hexact :
      (490449 / 592688 : ℝ) * (37043 / 40320 : ℝ) =
        (163483 / 215040 : ℝ) := by
    norm_num
  rw [hexact] at hscaled
  exact v21_cosA_upper_root.trans hscaled

def v21RootPiL : ℝ := 31415926 / 10000000
def v21RootPiU : ℝ := 31415927 / 10000000
def v21RootCL : ℝ := 88280819 / 106683860
def v21RootCU : ℝ := 490449 / 592688

def v21RootSinLower7 (t : ℝ) : ℝ :=
  t - t^3 / 6 + t^5 / 120 - t^7 / 5040

def v21RootSinUpper9 (t : ℝ) : ℝ :=
  t - t^3 / 6 + t^5 / 120 - t^7 / 5040 + t^9 / 362880

def v21RootCosLower10 (t : ℝ) : ℝ :=
  1 - t^2 / 2 + t^4 / 24 - t^6 / 720 + t^8 / 40320 - t^10 / 3628800

def v21RootCosUpper8 (t : ℝ) : ℝ :=
  1 - t^2 / 2 + t^4 / 24 - t^6 / 720 + t^8 / 40320

/-- Cleared numerator around the integer cell `n`. Its zero is the positive
kernel zero in that cell. -/
def v21RootH (n : ℕ) (x : ℝ) : ℝ :=
  v21C * Real.pi * x * Real.sin (Real.pi * (x - (n : ℝ))) -
    (1 / 2 : ℝ) * Real.cos (Real.pi * (x - (n : ℝ)))

lemma v21_rootH_upper_bound {n : ℕ} {x e : ℝ}
    (hx : x = (n : ℝ) + e)
    (he0 : 0 ≤ e)
    (heu : v21RootPiU * e ≤ 1) :
    v21RootH n x ≤
      v21RootCU * v21RootPiU * x *
          v21RootSinUpper9 (v21RootPiU * e) -
        (1 / 2 : ℝ) * v21RootCosLower10 (v21RootPiU * e) := by
  have hpiU : Real.pi ≤ v21RootPiU := by
    simpa [v21RootPiU] using (le_of_lt v21_pi_upper)
  have hC : v21C ≤ v21RootCU := by
    simpa [v21RootCU] using v21_C_upper
  have hCU0 : 0 ≤ v21RootCU := by norm_num [v21RootCU]
  have hpiU0 : 0 ≤ v21RootPiU := by norm_num [v21RootPiU]
  have hx0 : 0 ≤ x := by rw [hx]; positivity
  let t : ℝ := Real.pi * e
  let u : ℝ := v21RootPiU * e
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have hu0 : 0 ≤ u := by dsimp [u, v21RootPiU]; positivity
  have htu : t ≤ u := by
    dsimp [t, u]
    exact mul_le_mul_of_nonneg_right hpiU he0
  have hu1 : u ≤ 1 := by simpa [u] using heu
  have huPi2 : u ≤ Real.pi / 2 := by
    nlinarith [Real.pi_gt_three]
  have huPi : u ≤ Real.pi := by
    nlinarith [Real.pi_pos, huPi2]
  have hsinMono : Real.sin t ≤ Real.sin u := by
    apply Real.sin_le_sin_of_le_of_le_pi_div_two
    · nlinarith [Real.pi_pos, ht0]
    · exact huPi2
    · exact htu
  have hsinTaylor := v21_sin_upper9 (x := u) hu0 hu1
  have hsinTaylor' : Real.sin u ≤ v21RootSinUpper9 u := by
    simpa [v21RootSinUpper9] using hsinTaylor
  have hsin : Real.sin t ≤ v21RootSinUpper9 u :=
    hsinMono.trans hsinTaylor'
  have hcosMono : Real.cos u ≤ Real.cos t := by
    apply Real.cos_le_cos_of_nonneg_of_le_pi
    · exact ht0
    · exact huPi
    · exact htu
  have hcosTaylor := v21_cos_lower10 (x := u) hu0 hu1
  have hcosTaylor' : v21RootCosLower10 u ≤ Real.cos u := by
    simpa [v21RootCosLower10] using hcosTaylor
  have hcos : v21RootCosLower10 u ≤ Real.cos t :=
    hcosTaylor'.trans hcosMono
  have htPi : t ≤ Real.pi := htu.trans huPi
  have hsint0 : 0 ≤ Real.sin t :=
    Real.sin_nonneg_of_nonneg_of_le_pi ht0 htPi
  have hCpi : v21C * Real.pi ≤ v21RootCU * v21RootPiU :=
    mul_le_mul hC hpiU Real.pi_pos.le hCU0
  have hcoef : v21C * Real.pi * x ≤ v21RootCU * v21RootPiU * x :=
    mul_le_mul_of_nonneg_right hCpi hx0
  have hterm1a :
      v21C * Real.pi * x * Real.sin t ≤
        v21RootCU * v21RootPiU * x * Real.sin t :=
    mul_le_mul_of_nonneg_right hcoef hsint0
  have hcoefU0 : 0 ≤ v21RootCU * v21RootPiU * x :=
    mul_nonneg (mul_nonneg hCU0 hpiU0) hx0
  have hterm1b :
      v21RootCU * v21RootPiU * x * Real.sin t ≤
        v21RootCU * v21RootPiU * x * v21RootSinUpper9 u :=
    mul_le_mul_of_nonneg_left hsin hcoefU0
  have hxe : x - (n : ℝ) = e := by rw [hx]; ring
  unfold v21RootH
  rw [hxe]
  dsimp [t, u] at hterm1a hterm1b hcos ⊢
  nlinarith

lemma v21_rootH_lower_bound {n : ℕ} {x e : ℝ}
    (hx : x = (n : ℝ) + e)
    (he0 : 0 ≤ e)
    (heu : v21RootPiU * e ≤ 1) :
    v21RootCL * v21RootPiL * x *
          v21RootSinLower7 (v21RootPiL * e) -
        (1 / 2 : ℝ) * v21RootCosUpper8 (v21RootPiL * e) ≤
      v21RootH n x := by
  have hpiL : v21RootPiL ≤ Real.pi := by
    simpa [v21RootPiL] using (le_of_lt v21_pi_lower)
  have hpiU : Real.pi ≤ v21RootPiU := by
    simpa [v21RootPiU] using (le_of_lt v21_pi_upper)
  have hCL : v21RootCL ≤ v21C := by
    simpa [v21RootCL] using v21_C_lower
  have hCL0 : 0 ≤ v21RootCL := by norm_num [v21RootCL]
  have hpiL0 : 0 ≤ v21RootPiL := by norm_num [v21RootPiL]
  have hC0 : 0 ≤ v21C := by nlinarith [v21_C_gt_half]
  have hx0 : 0 ≤ x := by rw [hx]; positivity
  let l : ℝ := v21RootPiL * e
  let t : ℝ := Real.pi * e
  let u : ℝ := v21RootPiU * e
  have hl0 : 0 ≤ l := by dsimp [l, v21RootPiL]; positivity
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have hlu : l ≤ t := by
    dsimp [l, t]
    exact mul_le_mul_of_nonneg_right hpiL he0
  have htu : t ≤ u := by
    dsimp [t, u]
    exact mul_le_mul_of_nonneg_right hpiU he0
  have hu1 : u ≤ 1 := by simpa [u] using heu
  have hl1 : l ≤ 1 := hlu.trans (htu.trans hu1)
  have htPi2 : t ≤ Real.pi / 2 := by
    have ht1 : t ≤ 1 := htu.trans hu1
    nlinarith [Real.pi_gt_three, ht1]
  have htPi : t ≤ Real.pi := by nlinarith [Real.pi_pos, htPi2]
  have hsinMono : Real.sin l ≤ Real.sin t := by
    apply Real.sin_le_sin_of_le_of_le_pi_div_two
    · nlinarith [Real.pi_pos, hl0]
    · exact htPi2
    · exact hlu
  have hsinTaylor := v21_sin_lower7 (x := l) hl0 hl1
  have hsinTaylor' : v21RootSinLower7 l ≤ Real.sin l := by
    simpa [v21RootSinLower7] using hsinTaylor
  have hsin : v21RootSinLower7 l ≤ Real.sin t :=
    hsinTaylor'.trans hsinMono
  have hcosMono : Real.cos t ≤ Real.cos l := by
    apply Real.cos_le_cos_of_nonneg_of_le_pi
    · exact hl0
    · exact htPi
    · exact hlu
  have hcosTaylor := v21_cos_upper8 (x := l) hl0 hl1
  have hcosTaylor' : Real.cos l ≤ v21RootCosUpper8 l := by
    simpa [v21RootCosUpper8] using hcosTaylor
  have hcos : Real.cos t ≤ v21RootCosUpper8 l :=
    hcosMono.trans hcosTaylor'
  have hsint0 : 0 ≤ Real.sin t :=
    Real.sin_nonneg_of_nonneg_of_le_pi ht0 htPi
  have hCpi : v21RootCL * v21RootPiL ≤ v21C * Real.pi :=
    mul_le_mul hCL hpiL hpiL0 hC0
  have hcoef : v21RootCL * v21RootPiL * x ≤ v21C * Real.pi * x :=
    mul_le_mul_of_nonneg_right hCpi hx0
  have hcoefL0 : 0 ≤ v21RootCL * v21RootPiL * x :=
    mul_nonneg (mul_nonneg hCL0 hpiL0) hx0
  have hterm1a :
      v21RootCL * v21RootPiL * x * v21RootSinLower7 l ≤
        v21RootCL * v21RootPiL * x * Real.sin t :=
    mul_le_mul_of_nonneg_left hsin hcoefL0
  have hterm1b :
      v21RootCL * v21RootPiL * x * Real.sin t ≤
        v21C * Real.pi * x * Real.sin t :=
    mul_le_mul_of_nonneg_right hcoef hsint0
  have hxe : x - (n : ℝ) = e := by rw [hx]; ring
  unfold v21RootH
  rw [hxe]
  dsimp [l, t, u] at hterm1a hterm1b hcos ⊢
  nlinarith

/-- Left endpoint certificate for the first positive kernel zero. -/
lemma v21_rootH_one_left :
    v21RootH 1 (105727 / 100000 : ℝ) ≤ -(7 / 100000 : ℝ) := by
  calc
    v21RootH 1 (105727 / 100000 : ℝ) ≤
        v21RootCU * v21RootPiU * (105727 / 100000 : ℝ) *
            v21RootSinUpper9 (v21RootPiU * (5727 / 100000 : ℝ)) -
          (1 / 2 : ℝ) *
            v21RootCosLower10 (v21RootPiU * (5727 / 100000 : ℝ)) := by
      exact v21_rootH_upper_bound
        (n := 1) (x := (105727 / 100000 : ℝ))
        (e := (5727 / 100000 : ℝ)) (by norm_num) (by norm_num)
        (by norm_num [v21RootPiU])
    _ ≤ -(7 / 100000 : ℝ) := by
      norm_num [v21RootCU, v21RootPiU, v21RootSinUpper9,
        v21RootCosLower10]

/-- Right endpoint certificate for the first positive kernel zero. -/
lemma v21_rootH_one_right :
    (1 / 100000 : ℝ) ≤ v21RootH 1 (105728 / 100000 : ℝ) := by
  calc
    (1 / 100000 : ℝ) ≤
        v21RootCL * v21RootPiL * (105728 / 100000 : ℝ) *
            v21RootSinLower7 (v21RootPiL * (5728 / 100000 : ℝ)) -
          (1 / 2 : ℝ) *
            v21RootCosUpper8 (v21RootPiL * (5728 / 100000 : ℝ)) := by
      norm_num [v21RootCL, v21RootPiL, v21RootSinLower7,
        v21RootCosUpper8]
    _ ≤ v21RootH 1 (105728 / 100000 : ℝ) := by
      exact v21_rootH_lower_bound
        (n := 1) (x := (105728 / 100000 : ℝ))
        (e := (5728 / 100000 : ℝ)) (by norm_num) (by norm_num)
        (by norm_num [v21RootPiU])

end HurtadoZeta23
