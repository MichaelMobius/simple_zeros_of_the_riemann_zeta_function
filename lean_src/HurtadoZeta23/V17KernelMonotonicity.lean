import HurtadoZeta23.V17ScalarPressure
import HurtadoZeta23.V17ScalarPressureFrontier
import Zeta23.ThmD.Limit
import Mathlib.Tactic

noncomputable section

open Real intervalIntegral

namespace HurtadoZeta23

/-- A signed rational lower bound at the single certified point.  The retained
v17 interval verifier proves a substantially stronger enclosure
`k(0.89) > 0.171389482...`; this proposition deliberately records only the
small rational consequence needed by Lean. -/
def V17KernelSignedCertPointClaim : Prop :=
  (171389 / 1000000 : ℝ) < limitingk v17KernelCertPoint

/-- On the nonnegative half-window, increasing the frequency up to the v17
certificate point decreases the cosine factor. -/
lemma v17_cos_freq_antitone_nonneg
    {x y t : ℝ}
    (hx : 0 ≤ x)
    (hxy : x ≤ y)
    (hy : y ≤ v17KernelCertPoint)
    (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1 / 2) :
    Real.cos (2 * Real.pi * y * t) ≤
      Real.cos (2 * Real.pi * x * t) := by
  have hy0 : 0 ≤ y := hx.trans hxy
  have hcert0 : 0 ≤ v17KernelCertPoint := hy0.trans hy
  have hfac : 0 ≤ 2 * Real.pi * t := by positivity
  have hargxy :
      2 * Real.pi * x * t ≤ 2 * Real.pi * y * t := by
    calc
      2 * Real.pi * x * t = x * (2 * Real.pi * t) := by ring
      _ ≤ y * (2 * Real.pi * t) :=
        mul_le_mul_of_nonneg_right hxy hfac
      _ = 2 * Real.pi * y * t := by ring
  have hyt : y * t ≤ v17KernelCertPoint * (1 / 2 : ℝ) := by
    exact mul_le_mul hy ht1 ht0 hcert0
  have hpi0 : 0 ≤ 2 * Real.pi := by positivity
  have hargy :
      2 * Real.pi * y * t ≤ Real.pi := by
    have hmul := mul_le_mul_of_nonneg_left hyt hpi0
    have hcert :
        2 * Real.pi * (v17KernelCertPoint * (1 / 2 : ℝ)) ≤ Real.pi := by
      rw [v17KernelCertPoint]
      nlinarith [Real.pi_pos]
    calc
      2 * Real.pi * y * t = 2 * Real.pi * (y * t) := by ring
      _ ≤ 2 * Real.pi * (v17KernelCertPoint * (1 / 2 : ℝ)) := hmul
      _ ≤ Real.pi := hcert
  have hargx0 : 0 ≤ 2 * Real.pi * x * t := by positivity
  exact Real.cos_le_cos_of_nonneg_of_le_pi hargx0 hargy hargxy

/-- The same cosine comparison on the full symmetric unit window. -/
lemma v17_cos_freq_antitone_unit_window
    {x y t : ℝ}
    (hx : 0 ≤ x)
    (hxy : x ≤ y)
    (hy : y ≤ v17KernelCertPoint)
    (ht : t ∈ Set.Icc (-(1 : ℝ) / 2) (1 / 2)) :
    Real.cos (2 * Real.pi * y * t) ≤
      Real.cos (2 * Real.pi * x * t) := by
  by_cases ht0 : 0 ≤ t
  · exact v17_cos_freq_antitone_nonneg hx hxy hy ht0 ht.2
  · have htneg : t < 0 := lt_of_not_ge ht0
    have hneg0 : 0 ≤ -t := by linarith
    have hneg1 : -t ≤ 1 / 2 := by linarith [ht.1]
    have h :=
      v17_cos_freq_antitone_nonneg
        (x := x) (y := y) (t := -t) hx hxy hy hneg0 hneg1
    calc
      Real.cos (2 * Real.pi * y * t)
          = Real.cos (2 * Real.pi * y * (-t)) := by
              rw [show 2 * Real.pi * y * t =
                -(2 * Real.pi * y * (-t)) by ring, Real.cos_neg]
      _ ≤ Real.cos (2 * Real.pi * x * (-t)) := h
      _ = Real.cos (2 * Real.pi * x * t) := by
              rw [show 2 * Real.pi * x * t =
                -(2 * Real.pi * x * (-t)) by ring, Real.cos_neg]

/-- The unnormalized limiting overlap kernel is antitone on
`[0, v17KernelCertPoint]`.  This uses only positivity of the optimal profile
and monotonicity of cosine on `[0,π]`; no differentiation under the integral
sign is needed. -/
theorem v17_limitingK_antitone_to_cert
    {x y : ℝ}
    (hx : 0 ≤ x)
    (hxy : x ≤ y)
    (hy : y ≤ v17KernelCertPoint) :
    limitingK y ≤ limitingK x := by
  unfold limitingK
  have hvy : IntervalIntegrable
      (fun t : ℝ =>
        Zeta23.ThmD.vStar 1 t * Real.cos (2 * Real.pi * y * t))
      MeasureTheory.volume (-(1 : ℝ) / 2) (1 / 2) := by
    have hc : Continuous
        (fun t : ℝ =>
          Zeta23.ThmD.vStar 1 t * Real.cos (2 * Real.pi * y * t)) := by
      unfold Zeta23.ThmD.vStar
      fun_prop
    exact hc.intervalIntegrable _ _
  have hvx : IntervalIntegrable
      (fun t : ℝ =>
        Zeta23.ThmD.vStar 1 t * Real.cos (2 * Real.pi * x * t))
      MeasureTheory.volume (-(1 : ℝ) / 2) (1 / 2) := by
    have hc : Continuous
        (fun t : ℝ =>
          Zeta23.ThmD.vStar 1 t * Real.cos (2 * Real.pi * x * t)) := by
      unfold Zeta23.ThmD.vStar
      fun_prop
    exact hc.intervalIntegrable _ _
  refine intervalIntegral.integral_mono_on (by norm_num) hvy hvx ?_
  intro t ht
  have hv : 0 ≤ Zeta23.ThmD.vStar 1 t :=
    Zeta23.ThmD.vStar_nonneg_on zero_le_one le_rfl ht
  exact mul_le_mul_of_nonneg_left
    (v17_cos_freq_antitone_unit_window hx hxy hy ht) hv

/-- Division by the positive normalization preserves the same order. -/
theorem v17_limitingk_antitone_to_cert
    {x y : ℝ}
    (hx : 0 ≤ x)
    (hxy : x ≤ y)
    (hy : y ≤ v17KernelCertPoint) :
    limitingk y ≤ limitingk x := by
  unfold limitingk
  exact (div_le_div_iff_of_pos_right limitingK_zero_pos).2
    (v17_limitingK_antitone_to_cert hx hxy hy)

/-- The signed point certificate implies the older squared-weight numerical
frontier. -/
theorem v17_weight_cert_of_signed
    (hsigned : V17KernelSignedCertPointClaim) :
    V17KernelAtCertPointClaim := by
  unfold V17KernelSignedCertPointClaim at hsigned
  unfold V17KernelAtCertPointClaim
  have hr0 : (0 : ℝ) < 171389 / 1000000 := by norm_num
  have hk0 : 0 < limitingk v17KernelCertPoint := lt_trans hr0 hsigned
  have hprod :
      0 <
        (limitingk v17KernelCertPoint - 171389 / 1000000) *
        (limitingk v17KernelCertPoint + 171389 / 1000000) := by
    exact mul_pos (sub_pos.mpr hsigned) (add_pos hk0 hr0)
  have hsquare :
      (171389 / 1000000 : ℝ) ^ 2 <
        limitingk v17KernelCertPoint ^ 2 := by
    nlinarith
  have hrat :
      (2937 / 100000 : ℝ) < (171389 / 1000000 : ℝ) ^ 2 := by
    norm_num
  unfold limitingWeight
  exact hrat.trans hsquare

/-- Below the certified point, the signed certificate plus internal kernel
monotonicity gives the required lower bound on the squared weight. -/
theorem v17_weight_cert_le_below_of_signed
    (hsigned : V17KernelSignedCertPointClaim)
    {x : ℝ}
    (hx : 0 ≤ x)
    (hxc : x ≤ v17KernelCertPoint) :
    limitingWeight v17KernelCertPoint ≤ limitingWeight x := by
  have hk :=
    v17_limitingk_antitone_to_cert hx hxc (le_refl v17KernelCertPoint)
  unfold V17KernelSignedCertPointClaim at hsigned
  have hr0 : (0 : ℝ) < 171389 / 1000000 := by norm_num
  have hkc0 : 0 ≤ limitingk v17KernelCertPoint :=
    (lt_trans hr0 hsigned).le
  have hkx0 : 0 ≤ limitingk x := hkc0.trans hk
  unfold limitingWeight
  have hprod :
      0 ≤
        (limitingk x - limitingk v17KernelCertPoint) *
        (limitingk x + limitingk v17KernelCertPoint) := by
    exact mul_nonneg (sub_nonneg.mpr hk) (add_nonneg hkx0 hkc0)
  nlinarith

/-- Therefore the universal scalar-pressure frontier follows from one signed
kernel value at `0.89`; all monotonicity is now proved internally. -/
theorem v17_scalar_pressure_of_signed_cert
    (hsigned : V17KernelSignedCertPointClaim) :
    V17ScalarPressureClaim := by
  intro g hg
  by_cases hle : g ≤ v17KernelCertPoint
  · have hwmono := v17_weight_cert_le_below_of_signed hsigned hg hle
    have hnum := v17_weight_cert_of_signed hsigned
    unfold V17KernelAtCertPointClaim at hnum
    have htarget :
        v17t * beta * v17g0 < limitingWeight v17KernelCertPoint :=
      lt_trans v17_scalar_target_lt_certified_target hnum
    have hlin : 0 ≤ v17t * beta * g := by
      have ht : 0 ≤ v17t := by norm_num [v17t]
      have hb : 0 ≤ beta := by norm_num [beta]
      positivity
    linarith
  · have hge : v17KernelCertPoint ≤ g := le_of_lt (lt_of_not_ge hle)
    have hcoef : 0 ≤ v17t * beta := by
      norm_num [v17t, beta]
    have hlinearCert :
        (2937 / 100000 : ℝ) ≤ v17t * beta * g := by
      rw [← v17_cert_point_linear_eq]
      exact mul_le_mul_of_nonneg_left hge hcoef
    have hw0 : 0 ≤ limitingWeight g := limitingWeight_nonneg g
    linarith [v17_scalar_target_lt_certified_target]

end HurtadoZeta23
