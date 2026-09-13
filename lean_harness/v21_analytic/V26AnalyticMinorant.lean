import HurtadoZeta23.V26MinorantPrereqs
import HurtadoZeta23.V26RationalCenter
import Mathlib.Tactic

noncomputable section

namespace HurtadoZeta23

/-- Exact rational chord coefficient used by the analytic minorant. -/
def v26ChordCoeff (rho : ℝ) : ℝ :=
  v26P7 ((314 / 100 : ℝ) * v26Fold rho) / rho

/-- Exact rational amplitude floor used by the analytic minorant. -/
def v26AmplitudeFloor (U : ℝ) : ℝ :=
  (2633 / 10000 : ℝ) ^ 2 *
    (U ^ 2 / (U ^ 2 - v26d0) ^ 2)

/-- Root-centred coefficient before the `999/1000` center shift. -/
def v26Araw (U rho : ℝ) : ℝ :=
  v26AmplitudeFloor U * v26ChordCoeff rho ^ 2

/-- The root-centred analytic quadratic minorant behind every rational cell.
All transcendental content is discharged by the imported phase/chord/amplitude
lemmas. -/
theorem v26_root_centred_minorant
    {L U Lstar x r q eps rho : ℝ} {N : ℕ}
    (hLx : L ≤ x) (hxU : x ≤ U)
    (hLstar0 : 0 < Lstar) (hLstarx : Lstar ≤ x) (hLstarr : Lstar ≤ r)
    (hroot : v26PhaseWith v26c r = (N : ℝ))
    (heps : 0 ≤ eps) (hrq : |r - q| ≤ eps)
    (hrho : rho = v26Mrat Lstar * (max |L - q| |U - q| + eps))
    (hrho0 : 0 < rho) (hrho1 : rho < 1)
    (hxkernel : v21A < v21B x)
    (hxdk : v26dk < x ^ 2) :
    v26Araw U rho * (x - r) ^ 2 ≤ limitingWeight x := by
  let t : ℝ := |v26PhaseWith v26c x - (N : ℝ)|
  have hx0 : 0 < x := hLstar0.trans_le hLstarx
  have hr0 : 0 < r := hLstar0.trans_le hLstarr
  have ht0 : 0 ≤ t := abs_nonneg _
  have htroot : t = |v26PhaseWith v26c x - v26PhaseWith v26c r| := by
    dsimp [t]
    rw [hroot]
  have hphaseLower :=
    v26_phase_distance_lower (c := v26c) v26_c_pos.le hr0 hx0
  have hxr_t : |x - r| ≤ t := by
    rw [htroot]
    exact hphaseLower
  have hphaseUpper :=
    v26_phase_distance_upper (c := v26c) (L := Lstar)
      v26_c_pos.le hLstar0 hLstarx hLstarr
  have hfactor := v26_exact_phase_factor_le_rational hLstar0
  have hfactorMul :
      (1 + v26c / (Real.pi * Lstar ^ 2)) * |x - r| ≤
        v26Mrat Lstar * |x - r| :=
    mul_le_mul_of_nonneg_right hfactor (abs_nonneg _)
  have hrootdist :=
    v26_interval_root_distance_le hLx hxU heps hrq
  have hM0 : 0 ≤ v26Mrat Lstar := (v26_Mrat_pos hLstar0).le
  have hMD :
      v26Mrat Lstar * |x - r| ≤
        v26Mrat Lstar * (max |L - q| |U - q| + eps) :=
    mul_le_mul_of_nonneg_left hrootdist hM0
  have ht_rho : t ≤ rho := by
    rw [htroot]
    calc
      |v26PhaseWith v26c x - v26PhaseWith v26c r|
          ≤ (1 + v26c / (Real.pi * Lstar ^ 2)) * |x - r| := hphaseUpper
      _ ≤ v26Mrat Lstar * |x - r| := hfactorMul
      _ ≤ v26Mrat Lstar * (max |L - q| |U - q| + eps) := hMD
      _ = rho := hrho.symm
  have hchord := v26_sine_chord_taylor hrho0 hrho1 ht0 ht_rho
  have hs0 : 0 ≤ v26Fold rho := v26_fold_nonneg hrho0.le hrho1.le
  have hsh : v26Fold rho ≤ (1 / 2 : ℝ) := v26_fold_le_half
  have hz0 : 0 ≤ (314 / 100 : ℝ) * v26Fold rho :=
    mul_nonneg (by norm_num) hs0
  have hz8 : (314 / 100 : ℝ) * v26Fold rho ≤ (8 / 5 : ℝ) := by
    nlinarith
  have hz2 : ((314 / 100 : ℝ) * v26Fold rho) ^ 2 ≤ (8 / 5 : ℝ) ^ 2 :=
    pow_le_pow_left₀ hz0 hz8 2
  have hz6 : ((314 / 100 : ℝ) * v26Fold rho) ^ 6 ≤ (8 / 5 : ℝ) ^ 6 :=
    pow_le_pow_left₀ hz0 hz8 6
  have hz4 : 0 ≤ ((314 / 100 : ℝ) * v26Fold rho) ^ 4 :=
    pow_nonneg hz0 4
  have hinner :
      0 ≤ 1 - ((314 / 100 : ℝ) * v26Fold rho) ^ 2 / 6
          + ((314 / 100 : ℝ) * v26Fold rho) ^ 4 / 120
          - ((314 / 100 : ℝ) * v26Fold rho) ^ 6 / 5040 := by
    nlinarith
  have hP7 : 0 ≤ v26P7 ((314 / 100 : ℝ) * v26Fold rho) := by
    have hid :
        v26P7 ((314 / 100 : ℝ) * v26Fold rho) =
          ((314 / 100 : ℝ) * v26Fold rho) *
            (1 - ((314 / 100 : ℝ) * v26Fold rho) ^ 2 / 6
              + ((314 / 100 : ℝ) * v26Fold rho) ^ 4 / 120
              - ((314 / 100 : ℝ) * v26Fold rho) ^ 6 / 5040) := by
      unfold v26P7
      ring
    rw [hid]
    exact mul_nonneg hz0 hinner
  have hk0 : 0 ≤ v26ChordCoeff rho := by
    unfold v26ChordCoeff
    exact div_nonneg hP7 hrho0.le
  have hkt0 : 0 ≤ v26ChordCoeff rho * t := mul_nonneg hk0 ht0
  have hchord' : v26ChordCoeff rho * t ≤ Real.sin (Real.pi * t) := by
    simpa [v26ChordCoeff] using hchord
  have hsinSq :
      v26ChordCoeff rho ^ 2 * t ^ 2 ≤ Real.sin (Real.pi * t) ^ 2 := by
    have hs := pow_le_pow_left₀ hkt0 hchord' 2
    simpa [mul_pow] using hs
  have hphasePeriodic :=
    v26_sin_phase_sq_distance N (v26PhaseWith v26c x)
  have hphaseSin :
      Real.sin (Real.pi * v26PhaseWith v26c x) ^ 2 =
        Real.sin (Real.pi * t) ^ 2 := by
    simpa [t] using hphasePeriodic
  have hdistSq : (x - r) ^ 2 ≤ t ^ 2 := by
    have hs := pow_le_pow_left₀ (abs_nonneg (x - r)) hxr_t 2
    simpa [sq_abs] using hs
  have hd0 : 0 ≤ v26d0 := by
    unfold v26d0
    positivity
  have hamp :=
    v26_amplitude_lower
      (Clo := (2633 / 10000 : ℝ)) (C := v26C0) (c := v26c)
      (d0 := v26d0) (dk := v26dk) (x := x) (U := U)
      (by norm_num) (le_of_lt v26_C0_lower)
      hd0 (le_of_lt v26_d0_lt_dk)
      hx0 hxdk hxU
  have hAmpFloor0 : 0 ≤ v26AmplitudeFloor U := by
    unfold v26AmplitudeFloor
    positivity
  have hAraw0 : 0 ≤ v26Araw U rho := by
    unfold v26Araw
    exact mul_nonneg hAmpFloor0 (sq_nonneg _)
  have hdistScaled :
      v26Araw U rho * (x - r) ^ 2 ≤ v26Araw U rho * t ^ 2 :=
    mul_le_mul_of_nonneg_left hdistSq hAraw0
  have hsinScaled :
      v26AmplitudeFloor U * (v26ChordCoeff rho ^ 2 * t ^ 2) ≤
        v26AmplitudeFloor U * Real.sin (Real.pi * t) ^ 2 :=
    mul_le_mul_of_nonneg_left hsinSq hAmpFloor0
  have hampScaled :
      v26AmplitudeFloor U * Real.sin (Real.pi * t) ^ 2 ≤
        (v26C0 ^ 2 * ((x ^ 2 + v26c ^ 2) / (x ^ 2 - v26dk) ^ 2)) *
          Real.sin (Real.pi * t) ^ 2 := by
    have hamp' :
        v26AmplitudeFloor U ≤
          v26C0 ^ 2 * ((x ^ 2 + v26c ^ 2) / (x ^ 2 - v26dk) ^ 2) := by
      simpa [v26AmplitudeFloor] using hamp
    exact mul_le_mul_of_nonneg_right hamp' (sq_nonneg _)
  rw [v26_limitingWeight_phase_form hxkernel, hphaseSin]
  calc
    v26Araw U rho * (x - r) ^ 2
        ≤ v26Araw U rho * t ^ 2 := hdistScaled
    _ = v26AmplitudeFloor U * (v26ChordCoeff rho ^ 2 * t ^ 2) := by
      unfold v26Araw
      ring
    _ ≤ v26AmplitudeFloor U * Real.sin (Real.pi * t) ^ 2 := hsinScaled
    _ ≤ (v26C0 ^ 2 * ((x ^ 2 + v26c ^ 2) / (x ^ 2 - v26dk) ^ 2)) *
          Real.sin (Real.pi * t) ^ 2 := hampScaled
    _ = v26C0 ^ 2 * ((x ^ 2 + v26c ^ 2) / (x ^ 2 - v26dk) ^ 2) *
          Real.sin (Real.pi * t) ^ 2 := by ring

/-- The rounded rational form used by generated cell certificates.  The only
cell-specific obligations are exact rational comparisons for `alpha` and
`eta`. -/
theorem v26_rounded_cell_minorant
    {L U Lstar x r q eps rho alpha eta : ℝ} {N : ℕ}
    (hLx : L ≤ x) (hxU : x ≤ U)
    (hLstar0 : 0 < Lstar) (hLstarx : Lstar ≤ x) (hLstarr : Lstar ≤ r)
    (hroot : v26PhaseWith v26c r = (N : ℝ))
    (heps : 0 ≤ eps) (hrq : |r - q| ≤ eps)
    (hrqStrict : |r - q| < (1 / 100000 : ℝ))
    (hrho : rho = v26Mrat Lstar * (max |L - q| |U - q| + eps))
    (hrho0 : 0 < rho) (hrho1 : rho < 1)
    (hxkernel : v21A < v21B x)
    (hxdk : v26dk < x ^ 2)
    (halpha : alpha ≤ (999 / 1000 : ℝ) * v26Araw U rho)
    (heta : (999 / 10000000000 : ℝ) * v26Araw U rho ≤ eta) :
    alpha * (x - q) ^ 2 - eta ≤ limitingWeight x := by
  have hrootMinor := v26_root_centred_minorant
    hLx hxU hLstar0 hLstarx hLstarr hroot heps hrq hrho hrho0 hrho1
    hxkernel hxdk
  have hA : 0 ≤ v26Araw U rho := by
    unfold v26Araw v26AmplitudeFloor v26ChordCoeff
    positivity
  exact v26_rounded_minorant_of_root_minorant
    hA hrootMinor hrqStrict halpha heta

end HurtadoZeta23
