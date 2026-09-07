import HurtadoZeta23.LimitingKernel
import Zeta23.ThmD.BridgeD
import Mathlib.Tactic

noncomputable section

namespace HurtadoZeta23

open Real MeasureTheory

/-- The `a_D` normalization of Anthropic's Montgomery--Taylor window. -/
def phiDMean (ϱ : ℝ → ℝ) (lam L w : ℝ) : ℝ :=
  Zeta23.AdmWindow.av (Zeta23.ThmD.phiD ϱ lam L w) L

/-- `a_D` is uniformly within `4w/L` of the limiting variational moment `aStar`. -/
theorem phiDMean_close_aStar
    {ϱ : ℝ → ℝ} {lam L w : ℝ}
    (hϱ : Zeta23.TaperProfile ϱ)
    (h0 : 0 < lam) (h1 : lam ≤ 1)
    (hw : 1 ≤ w) (hwL : 8 * w ≤ L) :
    |phiDMean ϱ lam L w - Zeta23.ThmD.aStar lam| ≤ 4 * w / L := by
  simpa [phiDMean, Zeta23.AdmWindow.av] using
    Zeta23.ThmD.aD_close hϱ h0 h1 hw hwL

/-- At the Montgomery--Taylor optimum `lam=1`, the denominator converges to `K(0)`. -/
theorem phiDMean_close_limitingK_zero
    {ϱ : ℝ → ℝ} {L w : ℝ}
    (hϱ : Zeta23.TaperProfile ϱ)
    (hw : 1 ≤ w) (hwL : 8 * w ≤ L) :
    |phiDMean ϱ 1 L w - limitingK 0| ≤ 4 * w / L := by
  rw [limitingK_zero_eq_aStar]
  exact phiDMean_close_aStar hϱ one_pos le_rfl hw hwL

/-- The exact full-grid normalized kernel produced by the Poisson identity. -/
def phiDFullGridKernel
    (ϱ : ℝ → ℝ) (L w x : ℝ) : ℝ :=
  Zeta23.AdmWindow.VPhiR (Zeta23.ThmD.phiD ϱ 1 L w)
      (2 * Real.pi * x / L) /
    (phiDMean ϱ 1 L w * L)

/-- A denominator perturbation estimate. -/
lemma div_sub_div_bound
    {A A0 B B0 d eA eB : ℝ}
    (hd : 0 < d)
    (hB : d ≤ |B|)
    (hB0 : d ≤ |B0|)
    (hA : |A - A0| ≤ eA)
    (hden : |B - B0| ≤ eB) :
    |A / B - A0 / B0|
      ≤ eA / d + |A0| * eB / (d * d) := by

  have hBn : B ≠ 0 := by
    intro h
    rw [h, abs_zero] at hB
    linarith

  have hB0n : B0 ≠ 0 := by
    intro h
    rw [h, abs_zero] at hB0
    linarith

  have hdinvB : |B⁻¹| ≤ d⁻¹ := by
    rw [abs_inv]
    exact inv_anti₀ hd hB

  have heA : 0 ≤ eA := by
    exact (abs_nonneg (A - A0)).trans hA

  have heB : 0 ≤ eB := by
    exact (abs_nonneg (B - B0)).trans hden

  have hinv :
      |B⁻¹ - B0⁻¹| ≤ eB * (d⁻¹ * d⁻¹) := by

    rw [inv_sub_inv hBn hB0n]
    rw [abs_div, abs_mul]

    have hprod :
        d * d ≤ |B| * |B0| := by
      exact mul_le_mul hB hB0 (le_of_lt hd) (abs_nonneg B)

    have hnum :
        |B0 - B| ≤ eB := by
      simpa [abs_sub_comm] using hden

    have hinvprod :
        (|B| * |B0|)⁻¹ ≤ (d * d)⁻¹ := by
      exact inv_anti₀ (mul_pos hd hd) hprod

    rw [div_eq_mul_inv]

    calc
      |B0 - B| * (|B| * |B0|)⁻¹
          ≤ eB * (d * d)⁻¹ := by
            exact mul_le_mul hnum hinvprod
              (inv_nonneg.mpr (mul_nonneg (abs_nonneg B) (abs_nonneg B0)))
              heB
      _ = eB * (d⁻¹ * d⁻¹) := by
            field_simp [ne_of_gt hd]

  calc
    |A / B - A0 / B0|
        = |(A - A0) * B⁻¹ + A0 * (B⁻¹ - B0⁻¹)| := by
            field_simp [hBn, hB0n]
            ring_nf

    _ ≤ |A - A0| * |B⁻¹|
          + |A0| * |B⁻¹ - B0⁻¹| := by
            simpa [abs_mul, Real.norm_eq_abs] using
              norm_add_le
                ((A - A0) * B⁻¹)
                (A0 * (B⁻¹ - B0⁻¹))

    _ ≤ eA * d⁻¹
          + |A0| * (eB * (d⁻¹ * d⁻¹)) := by
            apply add_le_add
            · exact mul_le_mul hA hdinvB
                (abs_nonneg B⁻¹) heA
            · exact mul_le_mul_of_nonneg_left
                hinv (abs_nonneg A0)

    _ = eA / d + |A0| * eB / (d * d) := by
          field_simp [ne_of_gt hd]

/-- Error composition used by the compact overlap limit:
finite-grid tail plus limiting-window error. -/
lemma overlap_error_triangle
    {finite full limit tailErr windowErr : ℝ}
    (htail : |finite - full| ≤ tailErr)
    (hwindow : |full - limit| ≤ windowErr) :
    |finite - limit| ≤ tailErr + windowErr := by
  calc
    |finite - limit|
        = |(finite - full) + (full - limit)| := by
            congr 1
            ring
    _ ≤ |finite - full| + |full - limit| := by
          simpa only [Real.norm_eq_abs] using
            norm_add_le (finite - full) (full - limit)
    _ ≤ tailErr + windowErr :=
      add_le_add htail hwindow

end HurtadoZeta23
