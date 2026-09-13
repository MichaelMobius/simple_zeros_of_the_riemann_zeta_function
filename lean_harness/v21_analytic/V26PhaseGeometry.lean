import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Tactic

noncomputable section

namespace HurtadoZeta23

/-- Phase map with an abstract positive shift coefficient. -/
def v26PhaseWith (c x : ℝ) : ℝ :=
  x - (1 / Real.pi) * Real.arctan (c / x)

/-- The phase expands distances from any positive reference point.  This avoids
calculus: it follows directly from monotonicity of `arctan` and antitonicity
of `x ↦ 1/x` on the positive half-line. -/
theorem v26_phase_distance_lower {c r x : ℝ}
    (hc : 0 ≤ c) (hr : 0 < r) (hx : 0 < x) :
    |x - r| ≤ |v26PhaseWith c x - v26PhaseWith c r| := by
  rcases le_total r x with hrx | hxr
  · have hinv : 1 / x ≤ 1 / r := one_div_le_one_div_of_le hr hrx
    have hfrac : c / x ≤ c / r := by
      simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hinv hc
    have hatan : Real.arctan (c / x) ≤ Real.arctan (c / r) :=
      Real.arctan_mono hfrac
    have hpi : 0 ≤ (1 / Real.pi : ℝ) := (one_div_pos.mpr Real.pi_pos).le
    have hscaled := mul_le_mul_of_nonneg_left hatan hpi
    have hdist : x - r ≤ v26PhaseWith c x - v26PhaseWith c r := by
      unfold v26PhaseWith
      linarith
    have hxmr : 0 ≤ x - r := sub_nonneg.mpr hrx
    have hphase : 0 ≤ v26PhaseWith c x - v26PhaseWith c r := hxmr.trans hdist
    simpa [abs_of_nonneg hxmr, abs_of_nonneg hphase] using hdist
  · have hinv : 1 / r ≤ 1 / x := one_div_le_one_div_of_le hx hxr
    have hfrac : c / r ≤ c / x := by
      simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hinv hc
    have hatan : Real.arctan (c / r) ≤ Real.arctan (c / x) :=
      Real.arctan_mono hfrac
    have hpi : 0 ≤ (1 / Real.pi : ℝ) := (one_div_pos.mpr Real.pi_pos).le
    have hscaled := mul_le_mul_of_nonneg_left hatan hpi
    have hdist : r - x ≤ v26PhaseWith c r - v26PhaseWith c x := by
      unfold v26PhaseWith
      linarith
    have hrmx : 0 ≤ r - x := sub_nonneg.mpr hxr
    have hphase : 0 ≤ v26PhaseWith c r - v26PhaseWith c x := hrmx.trans hdist
    have habsx : |x - r| = r - x := by
      rw [abs_of_nonpos (sub_nonpos.mpr hxr)]
      ring
    have habsp : |v26PhaseWith c x - v26PhaseWith c r| =
        v26PhaseWith c r - v26PhaseWith c x := by
      rw [abs_of_nonpos]
      · ring
      · linarith
    rw [habsx, habsp]
    exact hdist

end HurtadoZeta23
