import HurtadoZeta23.FourierL1
import Zeta23.Poisson.PaperFT
import Mathlib.Tactic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

noncomputable section

namespace HurtadoZeta23

open Complex MeasureTheory Real Set

/--
Real-part adapter for the paper Fourier convention used by Zeta23.
For a real-valued integrable function, the real part of
`paperFT f r = ∫ f(u) exp(i r u) du` is its cosine transform.
-/
theorem re_paperFT_ofReal_eq_cosine
    {f : ℝ → ℝ} (hf : Integrable f) (r : ℝ) :
    (Zeta23.paperFT (fun u => (f u : ℂ)) r).re =
      ∫ u, f u * Real.cos (r * u) := by
  rw [Zeta23.paperFT_def]
  let phase : ℝ → ℂ :=
    fun u => Complex.exp (Complex.I * (r : ℂ) * u)
  have hphase_meas : AEStronglyMeasurable phase := by
    dsimp [phase]
    exact (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable
  have hphase_bound :
      ∀ᵐ u ∂(volume : Measure ℝ), ‖phase u‖ ≤ 1 := by
    apply MeasureTheory.ae_of_all
    intro u
    dsimp [phase]
    rw [Complex.norm_exp]
    simp
  have htmp : Integrable (fun u : ℝ => phase u * (f u : ℂ)) :=
    hf.ofReal.bdd_mul (c := 1) hphase_meas hphase_bound
  have hfc :
      Integrable
        (fun u : ℝ =>
          (f u : ℂ) * Complex.exp (Complex.I * (r : ℂ) * u)) := by
    refine htmp.congr ?_
    apply MeasureTheory.ae_of_all
    intro u
    dsimp [phase]
    ring
  have hre :
      (∫ u : ℝ,
          (f u : ℂ) * Complex.exp (Complex.I * (r : ℂ) * u)).re =
        ∫ u : ℝ,
          RCLike.re
            ((f u : ℂ) *
              Complex.exp (Complex.I * (r : ℂ) * u)) := by
    simpa using (integral_re hfc).symm
  calc
    (∫ u : ℝ,
        (f u : ℂ) * Complex.exp (Complex.I * (r : ℂ) * u)).re
        =
      ∫ u : ℝ,
        RCLike.re
          ((f u : ℂ) *
            Complex.exp (Complex.I * (r : ℂ) * u)) := hre
    _ = ∫ u : ℝ, f u * Real.cos (r * u) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with u
      have hexp :
          Complex.I * (r : ℂ) * (u : ℂ) =
            ((r * u : ℝ) : ℂ) * Complex.I := by
        push_cast
        ring
      rw [hexp]
      change
        (((f u : ℂ) *
            Complex.exp (((r * u : ℝ) : ℂ) * Complex.I)).re) =
          f u * Real.cos (r * u)
      rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.exp_ofReal_mul_I_re]
      ring

/-- `VPhiR` is exactly the cosine transform of the squared real window. -/
theorem VPhiR_eq_cosine_integral
    {v : ℝ → ℝ} {L w c : ℝ}
    (hW : Zeta23.AdmWindow v L w c) (r : ℝ) :
    Zeta23.AdmWindow.VPhiR v r =
      ∫ u, v u ^ 2 * Real.cos (r * u) := by
  unfold Zeta23.AdmWindow.VPhiR Zeta23.AdmWindow.VPhi
  exact re_paperFT_ofReal_eq_cosine (hW.integrable_pow two_pos) r

/-- Concrete specialization to the Montgomery--Taylor window `phiD`. -/
theorem phiD_VPhiR_eq_cosine_integral
    {ϱ : ℝ → ℝ} {L w r : ℝ}
    (hϱ : Zeta23.TaperProfile ϱ) (hw : 1 ≤ w) (hwL : 8 * w ≤ L) :
    Zeta23.AdmWindow.VPhiR (Zeta23.ThmD.phiD ϱ 1 L w) r =
      ∫ u, Zeta23.ThmD.phiD ϱ 1 L w u ^ 2 * Real.cos (r * u) := by
  exact VPhiR_eq_cosine_integral
    (Zeta23.ThmD.admWindow_phiD hϱ (by norm_num) (by norm_num) hw hwL) r

/--
The only remaining elementary convention/scaling identity needed to turn the
L1 comparison into `ScaledFourierWindowEstimate`.
-/
def SharpScalingIdentity (L x : ℝ) : Prop :=
  (∫ u, Zeta23.ThmD.sharpW 1 L u * Real.cos ((2 * Real.pi * x / L) * u)) / L
    = limitingK x


/--
The sharp-window scaling identity is not an additional analytic input.  For
`L > 0` it follows from Haar scaling of Lebesgue measure and the definition of
`sharpW` as the indicator of `[-L/2,L/2]` times `vStar 1 (u/L)`.

This is the exact change of variables `u = L t` used in the manuscript.
-/
theorem sharpScalingIdentity_proved {L x : ℝ} (hL : 0 < L) :
    SharpScalingIdentity L x := by
  have hL0 : L ≠ 0 := ne_of_gt hL
  let F : ℝ → ℝ := fun u =>
    Zeta23.ThmD.sharpW 1 L u * Real.cos ((2 * Real.pi * x / L) * u)
  have hscale := MeasureTheory.Measure.integral_comp_mul_left F L
  have hpoint : ∀ t : ℝ,
      F (L * t) =
        (Set.Icc (-(1 : ℝ) / 2) (1 / 2)).indicator
          (fun t => Zeta23.ThmD.vStar 1 t * Real.cos (2 * Real.pi * x * t)) t := by
    intro t
    dsimp [F]
    unfold Zeta23.ThmD.sharpW
    by_cases ht : t ∈ Set.Icc (-(1 : ℝ) / 2) (1 / 2)
    · have hLt : L * t ∈ Set.Icc (-(L / 2)) (L / 2) := by
        constructor <;> nlinarith [ht.1, ht.2]
      rw [Set.indicator_of_mem hLt, Set.indicator_of_mem ht]
      have hdiv : (L * t) / L = t := by field_simp [hL0]
      have hphase : (2 * Real.pi * x / L) * (L * t) = 2 * Real.pi * x * t := by
        field_simp [hL0]
        <;> ring
      rw [hdiv, hphase]
    · have hLt : L * t ∉ Set.Icc (-(L / 2)) (L / 2) := by
        intro hmem
        apply ht
        constructor <;> nlinarith [hmem.1, hmem.2]
      rw [Set.indicator_of_notMem hLt, Set.indicator_of_notMem ht, zero_mul]
  have hscaledIntegral :
      (∫ t : ℝ, F (L * t)) = limitingK x := by
    rw [show (fun t : ℝ => F (L * t)) =
      fun t => (Set.Icc (-(1 : ℝ) / 2) (1 / 2)).indicator
        (fun t => Zeta23.ThmD.vStar 1 t * Real.cos (2 * Real.pi * x * t)) t from
      funext hpoint]
    rw [MeasureTheory.integral_indicator measurableSet_Icc]
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
    rw [← intervalIntegral.integral_of_le (by norm_num : (-(1 : ℝ) / 2) ≤ 1 / 2)]
    rfl
  unfold SharpScalingIdentity
  change (∫ u : ℝ, F u) / L = limitingK x
  rw [← hscaledIntegral]
  have hscale' :
      (∫ t : ℝ, F (L * t)) = (∫ u : ℝ, F u) / L := by
    calc
      (∫ t : ℝ, F (L * t))
          = L⁻¹ * (∫ u : ℝ, F u) := by
              simpa [abs_of_pos (inv_pos.mpr hL), smul_eq_mul] using hscale
      _ = (∫ u : ℝ, F u) / L := by
            rw [div_eq_mul_inv]
            ring
  exact hscale'.symm

/--
Once the sharp-window change of variables is supplied, the L1 estimate from
Zeta23 proves the exact uniform Fourier estimate used by the kernel bridge.
-/
theorem scaledFourierWindowEstimate_of_sharpScaling
    {ϱ : ℝ → ℝ} {L w : ℝ}
    (hϱ : Zeta23.TaperProfile ϱ) (hw : 1 ≤ w) (hwL : 8 * w ≤ L)
    (hL : 0 < L)
    (hscale : ∀ x : ℝ, SharpScalingIdentity L x) :
    ScaledFourierWindowEstimate ϱ L w := by
  intro x
  have hcos := phiDsq_cosine_error_le (hϱ := hϱ) (hw := hw) (hwL := hwL) (x := x)
  have hVP := phiD_VPhiR_eq_cosine_integral
    (hϱ := hϱ) (hw := hw) (hwL := hwL) (r := 2 * Real.pi * x / L)
  unfold scaledPhiDFourier
  rw [hVP]
  have hdiv :
      |((∫ u, Zeta23.ThmD.phiD ϱ 1 L w u ^ 2 * Real.cos ((2 * Real.pi * x / L) * u)) / L) -
        ((∫ u, Zeta23.ThmD.sharpW 1 L u * Real.cos ((2 * Real.pi * x / L) * u)) / L)|
        ≤ (2 * w) / L := by
    rw [← sub_div]
    rw [abs_div, abs_of_pos hL]
    exact (div_le_div_iff_of_pos_right hL).2 hcos
  rw [hscale x] at hdiv
  simpa [div_eq_mul_inv] using hdiv


/--
The Fourier-window estimate no longer requires a scaling interface: the change
of variables is discharged internally by `sharpScalingIdentity_proved`.
-/
theorem scaledFourierWindowEstimate_proved
    {ϱ : ℝ → ℝ} {L w : ℝ}
    (hϱ : Zeta23.TaperProfile ϱ) (hw : 1 ≤ w) (hwL : 8 * w ≤ L) :
    ScaledFourierWindowEstimate ϱ L w := by
  have hL : 0 < L := by linarith
  exact scaledFourierWindowEstimate_of_sharpScaling
    hϱ hw hwL hL (fun x => sharpScalingIdentity_proved hL)


/--
Uniform normalized window-to-kernel estimate with all Fourier/scaling inputs
proved internally.  The only remaining quantitative side condition is that the
normalization perturbation is at most half of `K(0)`.
-/
theorem normalized_window_kernel_error_uniform_proved
    {ϱ : ℝ → ℝ} {L w : ℝ}
    (hϱ : Zeta23.TaperProfile ϱ) (hw : 1 ≤ w) (hwL : 8 * w ≤ L)
    (hsmall : 4 * w / L ≤ limitingK 0 / 2) :
    ∀ x : ℝ,
      |scaledPhiDFourier ϱ L w x / phiDMean ϱ 1 L w - limitingk x|
        ≤ 20 * (w / L) / limitingK 0 := by
  exact normalized_window_kernel_error_uniform hϱ hw hwL
    (scaledFourierWindowEstimate_proved hϱ hw hwL)
    limitingKernelMajorization_proved hsmall

/--
Raw finite-grid overlap bound in which the *only* analytic error supplied by
an upstream argument is the finite-grid tail.  The window/kernel error is now
fully discharged from Zeta23's L1 estimate plus the proved scaling adapter.
-/
theorem raw_overlap_error_of_tail_proved
    {finite full : ℝ} {ϱ : ℝ → ℝ} {L w x tailErr : ℝ}
    (hϱ : Zeta23.TaperProfile ϱ) (hw : 1 ≤ w) (hwL : 8 * w ≤ L)
    (hsmall : 4 * w / L ≤ limitingK 0 / 2)
    (hfull : full = scaledPhiDFourier ϱ L w x / phiDMean ϱ 1 L w)
    (htail : |finite - full| ≤ tailErr) :
    |finite - limitingk x| ≤ tailErr + 20 * (w / L) / limitingK 0 := by
  exact raw_overlap_error_of_tail_and_window hϱ hw hwL
    (scaledFourierWindowEstimate_proved hϱ hw hwL)
    limitingKernelMajorization_proved hsmall hfull htail

end HurtadoZeta23
