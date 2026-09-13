import HurtadoZeta23.V26TaylorExtension
import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic

noncomputable section

open Set

namespace HurtadoZeta23

/-- Fold a phase radius into the increasing half of the sine arch. -/
def v26Fold (rho : ℝ) : ℝ := min rho (1 - rho)

lemma v26_fold_nonneg {rho : ℝ} (h0 : 0 ≤ rho) (h1 : rho ≤ 1) :
    0 ≤ v26Fold rho := by
  unfold v26Fold
  exact le_min h0 (sub_nonneg.mpr h1)

lemma v26_fold_le_half {rho : ℝ} : v26Fold rho ≤ (1 / 2 : ℝ) := by
  unfold v26Fold
  have hleft := min_le_left rho (1 - rho)
  have hright := min_le_right rho (1 - rho)
  linarith

/-- Folding does not change `sin (pi*rho)` for `rho` in `[0,1]`. -/
lemma v26_sin_pi_fold {rho : ℝ} (h0 : 0 ≤ rho) (h1 : rho ≤ 1) :
    Real.sin (Real.pi * v26Fold rho) = Real.sin (Real.pi * rho) := by
  rcases le_total rho (1 - rho) with h | h
  · rw [v26Fold, min_eq_left h]
  · rw [v26Fold, min_eq_right h]
    have harg : Real.pi * (1 - rho) = Real.pi - Real.pi * rho := by ring
    rw [harg, Real.sin_pi_sub]

/-- Concavity of sine gives the exact chord through `(0,0)` and
`(rho, sin(pi*rho))`. -/
theorem v26_sine_chord {t rho : ℝ}
    (hrho0 : 0 < rho) (hrho1 : rho ≤ 1)
    (ht0 : 0 ≤ t) (htr : t ≤ rho) :
    (t / rho) * Real.sin (Real.pi * rho) ≤ Real.sin (Real.pi * t) := by
  have hpi0 : 0 ≤ Real.pi * rho := mul_nonneg Real.pi_pos.le hrho0.le
  have hpirho : Real.pi * rho ≤ Real.pi := by
    simpa using mul_le_mul_of_nonneg_left hrho1 Real.pi_pos.le
  have hy : Real.pi * rho ∈ Set.Icc (0 : ℝ) Real.pi := ⟨hpi0, hpirho⟩
  have hb : 0 ≤ t / rho := div_nonneg ht0 hrho0.le
  have hratio : t / rho ≤ 1 := (div_le_one hrho0).2 htr
  have ha : 0 ≤ 1 - t / rho := sub_nonneg.mpr hratio
  have hconc := Real.strictConcaveOn_sin_Icc.concaveOn.2
    (x := (0 : ℝ)) (by simp)
    (y := Real.pi * rho) hy
    (a := 1 - t / rho) (b := t / rho)
    ha hb (by ring)
  have harg :
      (1 - t / rho) * (0 : ℝ) + (t / rho) * (Real.pi * rho) =
        Real.pi * t := by
    field_simp [hrho0.ne']
    ring
  simpa [smul_eq_mul, harg] using hconc

/-- The folded endpoint sine is bounded below by the exact rational Taylor
polynomial evaluated at `3.14*s`.  This is the directed rounding used in the
certificate. -/
theorem v26_folded_endpoint_taylor_lower {rho : ℝ}
    (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1) :
    v26P7 ((314 / 100 : ℝ) * v26Fold rho) ≤
      Real.sin (Real.pi * rho) := by
  let s := v26Fold rho
  have hs0 : 0 ≤ s := v26_fold_nonneg hrho0 hrho1
  have hsh : s ≤ (1 / 2 : ℝ) := v26_fold_le_half
  have h314pi : (314 / 100 : ℝ) < Real.pi := by
    nlinarith [Real.pi_gt_d20]
  have hx0 : 0 ≤ (314 / 100 : ℝ) * s := mul_nonneg (by norm_num) hs0
  have hx8 : (314 / 100 : ℝ) * s ≤ (8 / 5 : ℝ) := by
    nlinarith
  have htaylor := v26_sin_lower7_upto_eight_fifths hx0 hx8
  have hxy : (314 / 100 : ℝ) * s ≤ Real.pi * s :=
    mul_le_mul_of_nonneg_right h314pi.le hs0
  have hys : Real.pi * s ≤ Real.pi / 2 := by
    nlinarith [Real.pi_pos]
  have hxm : -(Real.pi / 2) ≤ (314 / 100 : ℝ) * s := by
    linarith [Real.pi_pos]
  have hym : -(Real.pi / 2) ≤ Real.pi * s := by
    linarith [Real.pi_pos]
  have hxmem : (314 / 100 : ℝ) * s ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨hxm, hxy.trans hys⟩
  have hymem : Real.pi * s ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨hym, hys⟩
  have hsinmono :
      Real.sin ((314 / 100 : ℝ) * s) ≤ Real.sin (Real.pi * s) :=
    Real.monotoneOn_sin hxmem hymem hxy
  calc
    v26P7 ((314 / 100 : ℝ) * v26Fold rho)
        = v26P7 ((314 / 100 : ℝ) * s) := by rfl
    _ ≤ Real.sin ((314 / 100 : ℝ) * s) := htaylor
    _ ≤ Real.sin (Real.pi * s) := hsinmono
    _ = Real.sin (Real.pi * rho) := by
      dsimp [s]
      exact v26_sin_pi_fold hrho0 hrho1

/-- Final rational chord form used by every quadratic phase minorant. -/
theorem v26_sine_chord_taylor {t rho : ℝ}
    (hrho0 : 0 < rho) (hrho1 : rho < 1)
    (ht0 : 0 ≤ t) (htr : t ≤ rho) :
    (v26P7 ((314 / 100 : ℝ) * v26Fold rho) / rho) * t ≤
      Real.sin (Real.pi * t) := by
  have hend := v26_folded_endpoint_taylor_lower hrho0.le hrho1.le
  have hscale : 0 ≤ t / rho := div_nonneg ht0 hrho0.le
  have hmul := mul_le_mul_of_nonneg_left hend hscale
  have hchord := v26_sine_chord hrho0 hrho1.le ht0 htr
  calc
    (v26P7 ((314 / 100 : ℝ) * v26Fold rho) / rho) * t
        = (t / rho) * v26P7 ((314 / 100 : ℝ) * v26Fold rho) := by
          field_simp [hrho0.ne']
          ring
    _ ≤ (t / rho) * Real.sin (Real.pi * rho) := hmul
    _ ≤ Real.sin (Real.pi * t) := hchord

end HurtadoZeta23
