import HurtadoZeta23.V26PhaseConstants
import HurtadoZeta23.V26PhaseGeometry
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Tactic

noncomputable section

namespace HurtadoZeta23

lemma v26_phase_angle (c x : ℝ) :
    Real.pi * v26PhaseWith c x =
      Real.pi * x - Real.arctan (c / x) := by
  unfold v26PhaseWith
  field_simp [Real.pi_ne_zero]

/-- Exact squared phase factorization of the oscillatory numerator. -/
theorem v26_phase_numerator_sq {c x : ℝ} (hx : 0 < x) :
    (x * Real.sin (Real.pi * x) - c * Real.cos (Real.pi * x)) ^ 2 =
      (x ^ 2 + c ^ 2) *
        Real.sin (Real.pi * v26PhaseWith c x) ^ 2 := by
  let S : ℝ := Real.sqrt (1 + (c / x) ^ 2)
  have hrad : 0 < 1 + (c / x) ^ 2 := by
    nlinarith [sq_nonneg (c / x)]
  have hS : 0 < S := by
    dsimp [S]
    exact Real.sqrt_pos.2 hrad
  have hS2 : S ^ 2 = 1 + (c / x) ^ 2 := by
    dsimp [S]
    exact Real.sq_sqrt hrad.le
  have hangle := v26_phase_angle c x
  have hsin :
      Real.sin (Real.pi * v26PhaseWith c x) =
        (x * Real.sin (Real.pi * x) - c * Real.cos (Real.pi * x)) /
          (x * S) := by
    rw [hangle, Real.sin_sub, Real.cos_arctan, Real.sin_arctan]
    dsimp [S]
    field_simp [hx.ne', (Real.sqrt_pos.2 hrad).ne']
  have hden : (x * S) ^ 2 = x ^ 2 + c ^ 2 := by
    calc
      (x * S) ^ 2 = x ^ 2 * S ^ 2 := by ring
      _ = x ^ 2 * (1 + (c / x) ^ 2) := by rw [hS2]
      _ = x ^ 2 + c ^ 2 := by
        field_simp [hx.ne']
  rw [hsin, div_pow, hden]
  have hsum : 0 < x ^ 2 + c ^ 2 := by
    nlinarith [sq_pos_of_pos hx, sq_nonneg c]
  field_simp [hsum.ne']

/-- The normalized overlap weight in the article's `(C0,c,dk,phase)` form. -/
theorem v26_limitingWeight_phase_form {x : ℝ}
    (hx : v21A < v21B x) :
    limitingWeight x =
      v26C0 ^ 2 *
        ((x ^ 2 + v26c ^ 2) / (x ^ 2 - v26dk) ^ 2) *
          Real.sin (Real.pi * v26PhaseWith v26c x) ^ 2 := by
  have hBpos : 0 < v21B x := v21_A_pos.trans hx
  have hxpos : 0 < x := by
    unfold v21B at hBpos
    have hxpi : 0 < x * Real.pi := by simpa [mul_comm] using hBpos
    exact pos_of_mul_pos_left hxpi Real.pi_pos.le
  have hD : (v21B x) ^ 2 - (1 / 2 : ℝ) ≠ 0 :=
    (v21_D_pos hx).ne'
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hC : v21C ≠ 0 := v26_C_pos.ne'
  have hdenrel :
      (v21B x) ^ 2 - (1 / 2 : ℝ) =
        Real.pi ^ 2 * (x ^ 2 - v26dk) := by
    unfold v21B v26dk
    field_simp [hpi]
  have hxd : x ^ 2 - v26dk ≠ 0 := by
    intro hz
    apply hD
    rw [hdenrel, hz]
    ring
  have hk :
      limitingWeight x =
        (v26C0 *
          (x * Real.sin (Real.pi * x) - v26c * Real.cos (Real.pi * x)) /
            (x ^ 2 - v26dk)) ^ 2 := by
    rw [v21_limitingWeight_normalized hx]
    unfold v26C0 v26c v26dk v21B
    field_simp [hpi, hC, hD, hxd]
  rw [hk]
  have hnum := v26_phase_numerator_sq (c := v26c) hxpos
  rw [div_pow, mul_pow, hnum]
  ring

end HurtadoZeta23
