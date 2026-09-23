import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

noncomputable section

open Filter Finset Real
open scoped BigOperators Topology

namespace HurtadoZeta23

/-!
Research-only exact Lean certificate for the closed-form value of the
nine-point window kernel at x=43/50.

This proves the transcendental/rational estimate.  A separate bridge must
identify this closed form with the integral definition of the overlap kernel.
-/

private def r9v2SinTerm (x : ℝ) (n : ℕ) : ℝ :=
  x ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ)

private def r9v2CosTerm (x : ℝ) (n : ℕ) : ℝ :=
  x ^ (2 * n) / ((2 * n).factorial : ℝ)

private lemma r9v2SinTerm_antitone {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Antitone (r9v2SinTerm x) := by
  refine antitone_nat_of_succ_le ?_
  intro n
  unfold r9v2SinTerm
  have hpow : x ^ (2 * (n + 1) + 1) ≤ x ^ (2 * n + 1) :=
    pow_le_pow_of_le_one hx0 hx1 (by omega)
  have hden :
      ((2 * n + 1).factorial : ℝ) ≤ ((2 * (n + 1) + 1).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le (by omega : 2 * n + 1 ≤ 2 * (n + 1) + 1)
  calc
    x ^ (2 * (n + 1) + 1) / ((2 * (n + 1) + 1).factorial : ℝ)
        ≤ x ^ (2 * n + 1) / ((2 * (n + 1) + 1).factorial : ℝ) :=
      div_le_div_of_nonneg_right hpow (by positivity)
    _ ≤ x ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ) :=
      div_le_div_of_nonneg_left (pow_nonneg hx0 _) (by positivity) hden

private lemma r9v2CosTerm_antitone {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Antitone (r9v2CosTerm x) := by
  refine antitone_nat_of_succ_le ?_
  intro n
  unfold r9v2CosTerm
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

lemma research9v2_sin_lower7 {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    x - x^3 / 6 + x^5 / 120 - x^7 / 5040 ≤ Real.sin x := by
  have ht :
      Tendsto
        (fun n : ℕ => ∑ i ∈ range n, (-1 : ℝ)^i * r9v2SinTerm x i)
        atTop (𝓝 (Real.sin x)) := by
    simpa [r9v2SinTerm, mul_div_assoc] using (Real.hasSum_sin x).tendsto_sum_nat
  have h := (r9v2SinTerm_antitone hx0 hx1).alternating_series_le_tendsto ht 2
  norm_num [r9v2SinTerm, sum_range_succ, Nat.factorial] at h ⊢
  linarith

lemma research9v2_sin_upper9 {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.sin x ≤ x - x^3 / 6 + x^5 / 120 - x^7 / 5040 + x^9 / 362880 := by
  have ht :
      Tendsto
        (fun n : ℕ => ∑ i ∈ range n, (-1 : ℝ)^i * r9v2SinTerm x i)
        atTop (𝓝 (Real.sin x)) := by
    simpa [r9v2SinTerm, mul_div_assoc] using (Real.hasSum_sin x).tendsto_sum_nat
  have h := (r9v2SinTerm_antitone hx0 hx1).tendsto_le_alternating_series ht 2
  norm_num [r9v2SinTerm, sum_range_succ, Nat.factorial] at h ⊢
  linarith

lemma research9v2_cos_lower10 {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    1 - x^2 / 2 + x^4 / 24 - x^6 / 720 + x^8 / 40320 - x^10 / 3628800
      ≤ Real.cos x := by
  have ht :
      Tendsto
        (fun n : ℕ => ∑ i ∈ range n, (-1 : ℝ)^i * r9v2CosTerm x i)
        atTop (𝓝 (Real.cos x)) := by
    simpa [r9v2CosTerm, mul_div_assoc] using (Real.hasSum_cos x).tendsto_sum_nat
  have h := (r9v2CosTerm_antitone hx0 hx1).alternating_series_le_tendsto ht 3
  norm_num [r9v2CosTerm, sum_range_succ, Nat.factorial] at h ⊢
  linarith

private def r9v2A : ℝ := (Real.sqrt 2)⁻¹
private def r9v2Theta : ℝ := (7 / 50 : ℝ) * Real.pi
private def r9v2B : ℝ := (43 / 50 : ℝ) * Real.pi
private def r9v2X : ℝ := 43 / 50

private lemma r9v2_pi_lower : (31415926 / 10000000 : ℝ) < Real.pi := by
  nlinarith [Real.pi_gt_d20]

private lemma r9v2_pi_upper : Real.pi < (31415927 / 10000000 : ℝ) := by
  nlinarith [Real.pi_lt_d20]

private lemma r9v2_A_pos : 0 < r9v2A := by
  unfold r9v2A
  positivity

private lemma r9v2_A_sq : r9v2A ^ 2 = (1 / 2 : ℝ) := by
  unfold r9v2A
  rw [inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

private lemma r9v2_A_lower : (70710678 / 100000000 : ℝ) < r9v2A := by
  by_contra h
  have hle : r9v2A ≤ (70710678 / 100000000 : ℝ) := le_of_not_gt h
  have hprod :
      0 ≤ ((70710678 / 100000000 : ℝ) - r9v2A) *
          ((70710678 / 100000000 : ℝ) + r9v2A) := by
    apply mul_nonneg
    · linarith
    · nlinarith [r9v2_A_pos.le]
  nlinarith [r9v2_A_sq]

private lemma r9v2_A_upper : r9v2A < (70710679 / 100000000 : ℝ) := by
  by_contra h
  have hle : (70710679 / 100000000 : ℝ) ≤ r9v2A := le_of_not_gt h
  have hprod :
      0 ≤ (r9v2A - (70710679 / 100000000 : ℝ)) *
          (r9v2A + (70710679 / 100000000 : ℝ)) := by
    apply mul_nonneg
    · linarith
    · nlinarith [r9v2_A_pos.le]
  nlinarith [r9v2_A_sq]

private lemma r9v2_theta_lower : (4398229 / 10000000 : ℝ) < r9v2Theta := by
  unfold r9v2Theta
  nlinarith [r9v2_pi_lower]

private lemma r9v2_theta_upper : r9v2Theta < (4398230 / 10000000 : ℝ) := by
  unfold r9v2Theta
  nlinarith [r9v2_pi_upper]

private lemma r9v2_B_lower : (27017696 / 10000000 : ℝ) < r9v2B := by
  unfold r9v2B
  nlinarith [r9v2_pi_lower]

private lemma r9v2_B_upper : r9v2B < (27017698 / 10000000 : ℝ) := by
  unfold r9v2B
  nlinarith [r9v2_pi_upper]

private lemma r9v2_sinA_lower : (6496368 / 10000000 : ℝ) < Real.sin r9v2A := by
  let aL : ℝ := 70710678 / 100000000
  have ha0 : 0 ≤ aL := by norm_num [aL]
  have ha1 : aL ≤ 1 := by norm_num [aL]
  have ht := research9v2_sin_lower7 (x := aL) ha0 ha1
  have hrat :
      (6496368 / 10000000 : ℝ) <
        aL - aL^3 / 6 + aL^5 / 120 - aL^7 / 5040 := by
    norm_num [aL]
  have hmono : Real.sin aL ≤ Real.sin r9v2A := by
    apply Real.sin_le_sin_of_le_of_le_pi_div_two
    · nlinarith [Real.pi_pos]
    · nlinarith [r9v2_pi_lower, r9v2_A_upper]
    · exact r9v2_A_lower.le
  exact hrat.trans_le (ht.trans hmono)

private lemma r9v2_sinA_upper : Real.sin r9v2A < (6496370 / 10000000 : ℝ) := by
  let aU : ℝ := 70710679 / 100000000
  have ha0 : 0 ≤ aU := by norm_num [aU]
  have ha1 : aU ≤ 1 := by norm_num [aU]
  have ht := research9v2_sin_upper9 (x := aU) ha0 ha1
  have hrat :
      aU - aU^3 / 6 + aU^5 / 120 - aU^7 / 5040 + aU^9 / 362880
        < (6496370 / 10000000 : ℝ) := by
    norm_num [aU]
  have hmono : Real.sin r9v2A ≤ Real.sin aU := by
    apply Real.sin_le_sin_of_le_of_le_pi_div_two
    · nlinarith [r9v2_A_pos.le, Real.pi_pos]
    · nlinarith [r9v2_pi_lower]
    · exact r9v2_A_upper.le
  exact (hmono.trans ht).trans_lt hrat

private lemma r9v2_cosA_lower : (7602445 / 10000000 : ℝ) < Real.cos r9v2A := by
  let aU : ℝ := 70710679 / 100000000
  have ha0 : 0 ≤ aU := by norm_num [aU]
  have ha1 : aU ≤ 1 := by norm_num [aU]
  have ht := research9v2_cos_lower10 (x := aU) ha0 ha1
  have hrat :
      (7602445 / 10000000 : ℝ) <
        1 - aU^2 / 2 + aU^4 / 24 - aU^6 / 720 + aU^8 / 40320 - aU^10 / 3628800 := by
    norm_num [aU]
  have hmono : Real.cos aU ≤ Real.cos r9v2A := by
    apply Real.cos_le_cos_of_nonneg_of_le_pi
    · exact r9v2_A_pos.le
    · nlinarith [r9v2_pi_lower]
    · exact r9v2_A_upper.le
  exact hrat.trans_le (ht.trans hmono)

private lemma r9v2_sinTheta_lower : (4257792 / 10000000 : ℝ) < Real.sin r9v2Theta := by
  let tL : ℝ := 4398229 / 10000000
  have ht0 : 0 ≤ tL := by norm_num [tL]
  have ht1 : tL ≤ 1 := by norm_num [tL]
  have hTaylor := research9v2_sin_lower7 (x := tL) ht0 ht1
  have hrat :
      (4257792 / 10000000 : ℝ) <
        tL - tL^3 / 6 + tL^5 / 120 - tL^7 / 5040 := by
    norm_num [tL]
  have hmono : Real.sin tL ≤ Real.sin r9v2Theta := by
    apply Real.sin_le_sin_of_le_of_le_pi_div_two
    · nlinarith [Real.pi_pos]
    · unfold r9v2Theta
      nlinarith [Real.pi_pos]
    · exact r9v2_theta_lower.le
  exact hrat.trans_le (hTaylor.trans hmono)

private lemma r9v2_sinTheta_upper : Real.sin r9v2Theta < (4257794 / 10000000 : ℝ) := by
  let tU : ℝ := 4398230 / 10000000
  have ht0 : 0 ≤ tU := by norm_num [tU]
  have ht1 : tU ≤ 1 := by norm_num [tU]
  have hTaylor := research9v2_sin_upper9 (x := tU) ht0 ht1
  have hrat :
      tU - tU^3 / 6 + tU^5 / 120 - tU^7 / 5040 + tU^9 / 362880
        < (4257794 / 10000000 : ℝ) := by
    norm_num [tU]
  have hmono : Real.sin r9v2Theta ≤ Real.sin tU := by
    apply Real.sin_le_sin_of_le_of_le_pi_div_two
    · unfold r9v2Theta
      nlinarith [Real.pi_pos]
    · nlinarith [r9v2_pi_lower]
    · exact r9v2_theta_upper.le
  exact (hmono.trans hTaylor).trans_lt hrat

private lemma r9v2_cosTheta_lower : (9048270 / 10000000 : ℝ) < Real.cos r9v2Theta := by
  let tU : ℝ := 4398230 / 10000000
  have ht0 : 0 ≤ tU := by norm_num [tU]
  have ht1 : tU ≤ 1 := by norm_num [tU]
  have hTaylor := research9v2_cos_lower10 (x := tU) ht0 ht1
  have hrat :
      (9048270 / 10000000 : ℝ) <
        1 - tU^2 / 2 + tU^4 / 24 - tU^6 / 720 + tU^8 / 40320 - tU^10 / 3628800 := by
    norm_num [tU]
  have hmono : Real.cos tU ≤ Real.cos r9v2Theta := by
    apply Real.cos_le_cos_of_nonneg_of_le_pi
    · unfold r9v2Theta
      positivity
    · nlinarith [r9v2_pi_lower]
    · exact r9v2_theta_upper.le
  exact hrat.trans_le (hTaylor.trans hmono)

private def r9v2Base : ℝ :=
  (r9v2A * Real.sin r9v2A * Real.cos r9v2Theta +
      r9v2B * Real.cos r9v2A * Real.sin r9v2Theta) /
    (r9v2B ^ 2 - r9v2A ^ 2)

private def r9v2Piece (n : ℕ) : ℝ :=
  r9v2X * Real.sin r9v2Theta /
    (Real.pi * (((n : ℝ) ^ 2) - r9v2X ^ 2))

/-- Exact closed form for the unnormalized overlap at x=43/50. -/
def research9v2WindowRaw086 : ℝ :=
  r9v2Base
  + (3322500 / 1000000000 : ℝ) * r9v2Piece 1
  + (7609135 / 1000000000 : ℝ) * r9v2Piece 2
  + (1190194 / 1000000000 : ℝ) * r9v2Piece 3
  + (731476 / 1000000000 : ℝ) * r9v2Piece 4
  - (1680572 / 1000000000 : ℝ) * r9v2Piece 5
  - (1141360 / 1000000000 : ℝ) * r9v2Piece 6

/-- Normalization K_v(0) for the same profile. -/
def research9v2WindowNorm : ℝ := Real.sin r9v2A / r9v2A

/-- Closed-form normalized kernel at x=43/50. -/
def research9v2WindowKernelClosed086 : ℝ :=
  research9v2WindowRaw086 / research9v2WindowNorm

private lemma r9v2_base_lower : (1897470 / 10000000 : ℝ) < r9v2Base := by
  have hdenpos : 0 < r9v2B ^ 2 - r9v2A ^ 2 := by
    have hBA : r9v2A < r9v2B := by nlinarith [r9v2_A_upper, r9v2_B_lower]
    nlinarith [sq_nonneg (r9v2B - r9v2A), r9v2_A_pos]
  apply (lt_div_iff₀ hdenpos).2
  have hnum1 :
      (70710678 / 100000000 : ℝ) * (6496368 / 10000000 : ℝ) *
          (9048270 / 10000000 : ℝ)
        < r9v2A * Real.sin r9v2A * Real.cos r9v2Theta := by
    gcongr
    · exact r9v2_A_lower
    · exact r9v2_sinA_lower
    · exact r9v2_cosTheta_lower
  have hnum2 :
      (27017696 / 10000000 : ℝ) * (7602445 / 10000000 : ℝ) *
          (4257792 / 10000000 : ℝ)
        < r9v2B * Real.cos r9v2A * Real.sin r9v2Theta := by
    gcongr
    · exact r9v2_B_lower
    · exact r9v2_cosA_lower
    · exact r9v2_sinTheta_lower
  have hBsq : r9v2B ^ 2 < (27017698 / 10000000 : ℝ) ^ 2 := by
    nlinarith [r9v2_B_upper, r9v2_B_lower]
  have hAsq : (70710678 / 100000000 : ℝ) ^ 2 < r9v2A ^ 2 := by
    nlinarith [r9v2_A_lower, r9v2_A_pos]
  have hrat :
      (1897470 / 10000000 : ℝ) *
          ((27017698 / 10000000 : ℝ)^2 -
            (70710678 / 100000000 : ℝ)^2)
        <
          (70710678 / 100000000 : ℝ) * (6496368 / 10000000 : ℝ) *
              (9048270 / 10000000 : ℝ)
          + (27017696 / 10000000 : ℝ) * (7602445 / 10000000 : ℝ) *
              (4257792 / 10000000 : ℝ) := by
    norm_num
  nlinarith

private lemma r9v2_piece_lower (n : ℕ)
    (hd : 0 < (((n : ℝ) ^ 2) - r9v2X ^ 2)) :
    r9v2X * (4257792 / 10000000 : ℝ) /
        ((31415927 / 10000000 : ℝ) * (((n : ℝ)^2) - r9v2X^2))
      < r9v2Piece n := by
  unfold r9v2Piece
  have hx0 : 0 < r9v2X := by norm_num [r9v2X]
  have hdenL : 0 < (31415927 / 10000000 : ℝ) * (((n : ℝ)^2) - r9v2X^2) := by
    positivity
  have hdenR : 0 < Real.pi * (((n : ℝ)^2) - r9v2X^2) := by
    positivity
  rw [div_lt_div_iff₀ hdenL hdenR]
  have h1 :
      (4257792 / 10000000 : ℝ) * Real.pi
        < Real.sin r9v2Theta * (31415927 / 10000000 : ℝ) := by
    have ha :
        (4257792 / 10000000 : ℝ) * Real.pi
          < Real.sin r9v2Theta * Real.pi :=
      mul_lt_mul_of_pos_right r9v2_sinTheta_lower Real.pi_pos
    have hspos : 0 < Real.sin r9v2Theta := by linarith [r9v2_sinTheta_lower]
    have hb :
        Real.sin r9v2Theta * Real.pi
          < Real.sin r9v2Theta * (31415927 / 10000000 : ℝ) :=
      mul_lt_mul_of_pos_left r9v2_pi_upper hspos
    exact ha.trans hb
  have hxd : 0 < r9v2X * (((n : ℝ)^2) - r9v2X^2) := mul_pos hx0 hd
  have hmul := mul_lt_mul_of_pos_left h1 hxd
  ring_nf at hmul ⊢
  exact hmul

private lemma r9v2_piece_upper (n : ℕ)
    (hd : 0 < (((n : ℝ) ^ 2) - r9v2X ^ 2)) :
    r9v2Piece n <
      r9v2X * (4257794 / 10000000 : ℝ) /
        ((31415926 / 10000000 : ℝ) * (((n : ℝ)^2) - r9v2X^2)) := by
  unfold r9v2Piece
  have hx0 : 0 < r9v2X := by norm_num [r9v2X]
  have hdenL : 0 < Real.pi * (((n : ℝ)^2) - r9v2X^2) := by positivity
  have hdenR : 0 < (31415926 / 10000000 : ℝ) * (((n : ℝ)^2) - r9v2X^2) := by
    positivity
  rw [div_lt_div_iff₀ hdenL hdenR]
  have hspos : 0 < Real.sin r9v2Theta := by linarith [r9v2_sinTheta_lower]
  have h1 :
      Real.sin r9v2Theta * (31415926 / 10000000 : ℝ)
        < (4257794 / 10000000 : ℝ) * Real.pi := by
    have ha :
        Real.sin r9v2Theta * (31415926 / 10000000 : ℝ)
          < Real.sin r9v2Theta * Real.pi :=
      mul_lt_mul_of_pos_left r9v2_pi_lower hspos
    have hb :
        Real.sin r9v2Theta * Real.pi
          < (4257794 / 10000000 : ℝ) * Real.pi :=
      mul_lt_mul_of_pos_right r9v2_sinTheta_upper Real.pi_pos
    exact ha.trans hb
  have hxd : 0 < r9v2X * (((n : ℝ)^2) - r9v2X^2) := mul_pos hx0 hd
  have hmul := mul_lt_mul_of_pos_left h1 hxd
  ring_nf at hmul ⊢
  exact hmul

private lemma r9v2_raw_lower :
    (1915167 / 10000000 : ℝ) < research9v2WindowRaw086 := by
  have h1 := r9v2_piece_lower 1 (by norm_num [r9v2X])
  have h2 := r9v2_piece_lower 2 (by norm_num [r9v2X])
  have h3 := r9v2_piece_lower 3 (by norm_num [r9v2X])
  have h4 := r9v2_piece_lower 4 (by norm_num [r9v2X])
  have h5 := r9v2_piece_upper 5 (by norm_num [r9v2X])
  have h6 := r9v2_piece_upper 6 (by norm_num [r9v2X])
  have hrat :
      (1915167 / 10000000 : ℝ) <
        (1897470 / 10000000 : ℝ)
        + (3322500 / 1000000000 : ℝ) *
            (r9v2X * (4257792 / 10000000 : ℝ) /
              ((31415927 / 10000000 : ℝ) * (((1 : ℝ)^2) - r9v2X^2)))
        + (7609135 / 1000000000 : ℝ) *
            (r9v2X * (4257792 / 10000000 : ℝ) /
              ((31415927 / 10000000 : ℝ) * (((2 : ℝ)^2) - r9v2X^2)))
        + (1190194 / 1000000000 : ℝ) *
            (r9v2X * (4257792 / 10000000 : ℝ) /
              ((31415927 / 10000000 : ℝ) * (((3 : ℝ)^2) - r9v2X^2)))
        + (731476 / 1000000000 : ℝ) *
            (r9v2X * (4257792 / 10000000 : ℝ) /
              ((31415927 / 10000000 : ℝ) * (((4 : ℝ)^2) - r9v2X^2)))
        - (1680572 / 1000000000 : ℝ) *
            (r9v2X * (4257794 / 10000000 : ℝ) /
              ((31415926 / 10000000 : ℝ) * (((5 : ℝ)^2) - r9v2X^2)))
        - (1141360 / 1000000000 : ℝ) *
            (r9v2X * (4257794 / 10000000 : ℝ) /
              ((31415926 / 10000000 : ℝ) * (((6 : ℝ)^2) - r9v2X^2))) := by
    norm_num [r9v2X]
  unfold research9v2WindowRaw086
  nlinarith [r9v2_base_lower, h1, h2, h3, h4, h5, h6]

private lemma r9v2_norm_pos : 0 < research9v2WindowNorm := by
  unfold research9v2WindowNorm
  have hs : 0 < Real.sin r9v2A := by linarith [r9v2_sinA_lower]
  exact div_pos hs r9v2_A_pos

private lemma r9v2_norm_upper :
    research9v2WindowNorm < (9187255 / 10000000 : ℝ) := by
  unfold research9v2WindowNorm
  rw [div_lt_iff₀ r9v2_A_pos]
  have hrat :
      (6496370 / 10000000 : ℝ)
        < (9187255 / 10000000 : ℝ) * (70710678 / 100000000 : ℝ) := by
    norm_num
  nlinarith [r9v2_sinA_upper, r9v2_A_lower]

/-- The strict rational signed-kernel target required by the hybrid block argument. -/
theorem research9v2_window_kernel_closed_gt :
    (521 / 2500 : ℝ) < research9v2WindowKernelClosed086 := by
  unfold research9v2WindowKernelClosed086
  rw [lt_div_iff₀ r9v2_norm_pos]
  have hrat :
      (521 / 2500 : ℝ) * (9187255 / 10000000 : ℝ)
        < (1915167 / 10000000 : ℝ) := by
    norm_num
  nlinarith [r9v2_raw_lower, r9v2_norm_upper]

end HurtadoZeta23
