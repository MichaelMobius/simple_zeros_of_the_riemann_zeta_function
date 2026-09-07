import HurtadoZeta23.WindowKernelQuantitative
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

noncomputable section

namespace HurtadoZeta23

open Real Set MeasureTheory

/-- Multiplication by a cosine phase cannot increase an L¹ error. -/
theorem abs_integral_mul_cos_le_integral_abs
    {f : ℝ → ℝ} (hf : Integrable f) (xi : ℝ) :
    |∫ u, f u * Real.cos (xi * u)| ≤ ∫ u, |f u| := by
  calc
    |∫ u, f u * Real.cos (xi * u)|
        ≤ ∫ u, |f u * Real.cos (xi * u)| :=
          MeasureTheory.abs_integral_le_integral_abs
    _ ≤ ∫ u, |f u| := by
      apply MeasureTheory.integral_mono_of_nonneg
        (MeasureTheory.ae_of_all _ fun u => abs_nonneg _)
        hf.abs
      apply MeasureTheory.ae_of_all
      intro u
      change |f u * Real.cos (xi * u)| ≤ |f u|
      rw [abs_mul]
      calc
        |f u| * |Real.cos (xi * u)|
            ≤ |f u| * 1 :=
          mul_le_mul_of_nonneg_left
            (Real.abs_cos_le_one _)
            (abs_nonneg _)
        _ = |f u| := mul_one _

/-- An integrable function remains integrable after multiplication by a
bounded cosine phase. -/
private theorem integrable_mul_cos
    {f : ℝ → ℝ} (hf : Integrable f) (xi : ℝ) :
    Integrable (fun u => f u * Real.cos (xi * u)) := by
  apply hf.mul_bdd
  · exact
      (Real.continuous_cos.comp
        (continuous_const.mul continuous_id)).aestronglyMeasurable
  · filter_upwards with u
    rw [Real.norm_eq_abs]
    exact Real.abs_cos_le_one _

/-- L¹ perturbations give a uniform bound for all cosine transforms. -/
theorem cosine_transform_sub_le_l1
    {f g : ℝ → ℝ} (hf : Integrable f) (hg : Integrable g)
    {eps : ℝ} (hL1 : ∫ u, |f u - g u| ≤ eps) (xi : ℝ) :
    |(∫ u, f u * Real.cos (xi * u)) -
      (∫ u, g u * Real.cos (xi * u))| ≤ eps := by
  have hfc : Integrable (fun u => f u * Real.cos (xi * u)) :=
    integrable_mul_cos hf xi
  have hgc : Integrable (fun u => g u * Real.cos (xi * u)) :=
    integrable_mul_cos hg xi
  rw [← MeasureTheory.integral_sub hfc hgc]
  have hi : Integrable (fun u => f u - g u) := hf.sub hg
  have h :=
    abs_integral_mul_cos_le_integral_abs hi xi
  have heq :
      (fun u =>
        f u * Real.cos (xi * u) -
          g u * Real.cos (xi * u))
        =
      (fun u =>
        (f u - g u) * Real.cos (xi * u)) := by
    funext u
    ring
  rw [heq]
  exact h.trans hL1

/-- On the support interval of the limiting profile, `vStar 1` is
nonnegative.  This is a direct specialization of Zeta23's concrete
Montgomery--Taylor window bound. -/
private theorem vStar_one_nonneg_on_half
    {t : ℝ}
    (ht : t ∈ Set.Icc (-(1 : ℝ) / 2) (1 / 2)) :
    0 ≤ Zeta23.ThmD.vStar 1 t := by
  have habs : |t| ≤ (1 : ℝ) / 2 := by
    rw [abs_le]
    constructor
    · simpa only [neg_div] using ht.1
    · exact ht.2
  have h :=
    Zeta23.ThmD.cos_factor_ge
      (lam := (1 : ℝ)) (L := (1 : ℝ)) (u := t)
      (by norm_num) (by norm_num) (by norm_num)
      (by simpa using habs)
  have hthree : (0 : ℝ) ≤ 3 / 4 := by norm_num
  have hvdiv :
      0 ≤ Zeta23.ThmD.vStar 1 (t / 1) :=
    hthree.trans h
  simpa using hvdiv

/-- The limiting Montgomery--Taylor cosine kernel is maximized in modulus at zero. -/
theorem limitingKernelMajorization_proved : LimitingKernelMajorization := by
  intro x

  have hab : (-(1 : ℝ) / 2) ≤ (1 : ℝ) / 2 := by
    norm_num

  have hvnonneg :
      ∀ t ∈ Set.Icc (-(1 : ℝ) / 2) ((1 : ℝ) / 2),
        0 ≤ Zeta23.ThmD.vStar 1 t := by
    intro t ht
    exact vStar_one_nonneg_on_half ht

  have hcos :
      ∀ t ∈ Set.Icc (-(1 : ℝ) / 2) ((1 : ℝ) / 2),
        |Zeta23.ThmD.vStar 1 t * Real.cos (2 * Real.pi * x * t)|
          ≤ Zeta23.ThmD.vStar 1 t := by
    intro t ht
    rw [abs_mul, abs_of_nonneg (hvnonneg t ht)]
    calc
      Zeta23.ThmD.vStar 1 t * |Real.cos (2 * Real.pi * x * t)|
          ≤ Zeta23.ThmD.vStar 1 t * 1 :=
        mul_le_mul_of_nonneg_left
          (Real.abs_cos_le_one _)
          (hvnonneg t ht)
      _ = Zeta23.ThmD.vStar 1 t := mul_one _

  have hvcont :
      Continuous (fun t : ℝ => Zeta23.ThmD.vStar 1 t) := by
    unfold Zeta23.ThmD.vStar
    fun_prop
  have hvg :
      IntervalIntegrable
        (fun t : ℝ => Zeta23.ThmD.vStar 1 t)
        volume (-(1 : ℝ) / 2) ((1 : ℝ) / 2) :=
    hvcont.intervalIntegrable _ _

  have hnorm :=
    intervalIntegral.norm_integral_le_of_norm_le
      (μ := volume)
      (f := fun t : ℝ =>
        Zeta23.ThmD.vStar 1 t * Real.cos (2 * Real.pi * x * t))
      (g := fun t : ℝ => Zeta23.ThmD.vStar 1 t)
      (a := (-(1 : ℝ) / 2)) (b := ((1 : ℝ) / 2))
      hab
      (MeasureTheory.ae_of_all _ fun t ht => by
        rw [Real.norm_eq_abs]
        exact hcos t ⟨le_of_lt ht.1, ht.2⟩)
      hvg

  rw [Real.norm_eq_abs] at hnorm

  have hz :
      limitingK 0 =
        ∫ t in (-(1 : ℝ) / 2)..((1 : ℝ) / 2),
          Zeta23.ThmD.vStar 1 t := by
    unfold limitingK
    simp

  rw [hz]
  unfold limitingK
  exact hnorm

/--
The exact L¹-to-Fourier estimate for the concrete Montgomery--Taylor window,
expressed at the real cosine-transform level.  The convention/scaling adapter
is handled separately in `FourierConventionAdapter`.
-/
theorem phiDsq_cosine_error_le
    {ϱ : ℝ → ℝ} {L w x : ℝ}
    (hϱ : Zeta23.TaperProfile ϱ)
    (hw : 1 ≤ w)
    (hwL : 8 * w ≤ L) :
    |(∫ u,
        Zeta23.ThmD.phiD ϱ 1 L w u ^ 2 *
          Real.cos ((2 * Real.pi * x / L) * u)) -
      (∫ u,
        Zeta23.ThmD.sharpW 1 L u *
          Real.cos ((2 * Real.pi * x / L) * u))|
      ≤ 2 * w := by

  have hw0 : 0 < w := by
    linarith

  have hwL' : 2 * w ≤ L := by
    linarith

  have hL1 :
      ∫ u,
          |Zeta23.ThmD.phiD ϱ 1 L w u ^ 2 -
            Zeta23.ThmD.sharpW 1 L u|
        ≤ 2 * w := by
    exact
      Zeta23.ThmD.integral_abs_phiDsq_sub_sharp
        (ϱ := ϱ) (lam := (1 : ℝ)) (L := L) (w := w)
        hϱ (by norm_num) (by norm_num) hw0 hwL'

  have hcont :
      Continuous
        (fun u : ℝ =>
          Zeta23.ThmD.phiD ϱ 1 L w u ^ 2) :=
    ((Zeta23.ThmD.phiD_contDiff
      (ϱ := ϱ) (lam := (1 : ℝ)) (L := L) (w := w)
      hϱ (by norm_num) (by norm_num) hw0 hwL').pow 2).continuous

  have hcs :
      HasCompactSupport
        (fun u : ℝ =>
          Zeta23.ThmD.phiD ϱ 1 L w u ^ 2) := by
    apply HasCompactSupport.of_support_subset_isCompact
      (isCompact_Icc (a := -(L / 2)) (b := L / 2))
    intro u hu
    rw [Function.mem_support] at hu
    by_contra hmem
    apply hu
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hmem
    have habs : L / 2 ≤ |u| := by
      rcases hmem with hleft | hright
      · rw [abs_of_neg (by linarith : u < 0)]
        linarith
      · rw [abs_of_pos (by linarith : 0 < u)]
        linarith
    rw [Zeta23.ThmD.phiD_eq_zero hϱ hw0 habs,
      zero_pow two_ne_zero]

  have hf :
      Integrable
        (fun u =>
          Zeta23.ThmD.phiD ϱ 1 L w u ^ 2) :=
    hcont.integrable_of_hasCompactSupport hcs

  have hg :
      Integrable (Zeta23.ThmD.sharpW 1 L) := by
    unfold Zeta23.ThmD.sharpW
    exact
      (MeasureTheory.integrable_indicator_iff measurableSet_Icc).mpr
        (((by
            unfold Zeta23.ThmD.vStar
            fun_prop :
              Continuous
                (fun u : ℝ =>
                  Zeta23.ThmD.vStar 1 (u / L))).continuousOn).integrableOn_compact
          isCompact_Icc)

  exact
    cosine_transform_sub_le_l1
      hf hg hL1 (2 * Real.pi * x / L)

end HurtadoZeta23
