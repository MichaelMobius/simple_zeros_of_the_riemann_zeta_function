import HurtadoZeta23.RvMAsymptotics
import Zeta23.Hypotheses
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

noncomputable section

open Filter Asymptotics

namespace HurtadoZeta23

/--
For the λ = 1 Montgomery--Taylor grid, deleting `L^2` grid cells at one
endpoint means an ordinary-ordinate strip of width

  h * L^2 = (2π/L) * L^2 = 2πL.

Here `L = l(T)`.
-/
def interiorBoundaryWidth (T : ℝ) : ℝ :=
  2 * Real.pi * Zeta23.l T

/--
Exact algebra behind the conversion from normalized width `L^2` to
ordinary ordinate width `2πL`.
-/
theorem grid_L2_width_eq_interiorBoundaryWidth
    {T : ℝ}
    (hl : Zeta23.l T ≠ 0) :
    (2 * Real.pi / Zeta23.l T) * (Zeta23.l T) ^ 2
      =
    interiorBoundaryWidth T := by
  unfold interiorBoundaryWidth
  field_simp [hl]

/--
Multiplicity-counting upper bound for the two *interior* boundary strips
removed by the compact-overlap lemma.

This is deliberately distinct from Zeta23's `NII`, which counts the exterior
set `I' \ I`.
-/
def interiorBoundaryCountNat (T : ℝ) : ℕ :=
  Zeta23.Ncount
      T
      (T + interiorBoundaryWidth T)
    +
  Zeta23.Ncount
      (2 * T - interiorBoundaryWidth T)
      (2 * T)

/-- Real-valued version used in asymptotic assembly. -/
def interiorBoundaryLoss (T : ℝ) : ℝ :=
  (interiorBoundaryCountNat T : ℝ)

/--
The problem-specific consequence required from the unit-window local count:
the two interior strips have total multiplicity `O(l(T)^2)`.

This structure contains numerical data (`C`), so it lives in `Type`, not
`Prop`.
-/
structure InteriorBoundaryLocalCount where
  C : ℝ
  C_nonneg : 0 ≤ C
  eventually_bound :
    ∀ᶠ T in atTop,
      interiorBoundaryLoss T ≤ C * (Zeta23.l T) ^ 2

/-- `l(T) = log(T/(2π))` tends to `+∞`. -/
theorem tendsto_zeta_l_atTop :
    Tendsto Zeta23.l atTop atTop := by
  unfold Zeta23.l
  exact
    Real.tendsto_log_atTop.comp
      (tendsto_id.atTop_div_const
        (by positivity : (0 : ℝ) < 2 * Real.pi))

/--
The rescaled variable `T/(2π)` is `O(T)`.
-/
lemma zeta_scale_isBigO_id :
    (fun T : ℝ => T / (2 * Real.pi))
      =O[atTop]
    (fun T : ℝ => T) := by

  have hc : (0 : ℝ) < 2 * Real.pi := by
    positivity

  refine IsBigO.of_bound (2 * Real.pi)⁻¹ ?_

  refine Filter.Eventually.of_forall ?_

  intro T

  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  rw [abs_div, abs_of_pos hc]
  rw [div_eq_mul_inv]

  exact le_of_eq (mul_comm |T| (2 * Real.pi)⁻¹)

/--
The square logarithmic scale is negligible compared with `T`.

This is obtained by applying Mathlib's standard
`isLittleO_log_rpow_rpow_atTop` theorem after the fixed rescaling
`T ↦ T/(2π)`.
-/
theorem zeta_l_sq_isLittleO_T :
    (fun T : ℝ => (Zeta23.l T) ^ 2)
      =o[atTop]
    (fun T : ℝ => T) := by

  have hlogpow :
      (fun x : ℝ => Real.log x ^ (2 : ℝ))
        =o[atTop]
      (fun x : ℝ => x ^ (1 : ℝ)) := by
    exact
      isLittleO_log_rpow_rpow_atTop
        (2 : ℝ)
        (by norm_num : (0 : ℝ) < 1)

  have hscale :
      Tendsto
        (fun T : ℝ => T / (2 * Real.pi))
        atTop
        atTop := by
    exact
      tendsto_id.atTop_div_const
        (by positivity : (0 : ℝ) < 2 * Real.pi)

  have hcomp :=
    hlogpow.comp_tendsto hscale

  have hscaled :
      (fun T : ℝ => (Zeta23.l T) ^ 2)
        =o[atTop]
      (fun T : ℝ => T / (2 * Real.pi)) := by

    convert hcomp using 1 <;>
      simp [Function.comp_def, Zeta23.l, Real.rpow_one]

  exact
    hscaled.trans_isBigO
      zeta_scale_isBigO_id

/--
Since `l(T) ≥ 1` eventually, `T = O(T*l(T))`.
-/
lemma id_isBigO_T_mul_zeta_l :
    (fun T : ℝ => T)
      =O[atTop]
    (fun T : ℝ => T * Zeta23.l T) := by

  have hl1 :
      ∀ᶠ T : ℝ in atTop,
        (1 : ℝ) ≤ Zeta23.l T :=
    tendsto_zeta_l_atTop.eventually_ge_atTop 1

  refine IsBigO.of_bound 1 ?_

  filter_upwards
    [hl1, eventually_ge_atTop (0 : ℝ)]
    with T hl hT0

  rw [
    Real.norm_eq_abs,
    Real.norm_eq_abs,
    abs_of_nonneg hT0,
    abs_of_nonneg
      (mul_nonneg hT0 (by linarith))
  ]

  nlinarith

/--
The square logarithmic scale is negligible compared with `T*l(T)`.
-/
theorem zeta_l_sq_isLittleO_TlogT :
    (fun T : ℝ => (Zeta23.l T) ^ 2)
      =o[atTop]
    (fun T : ℝ => T * Zeta23.l T) := by

  exact
    zeta_l_sq_isLittleO_T.trans_isBigO
      id_isBigO_T_mul_zeta_l

/--
The correctly defined interior boundary loss is `o(T log T)` once the
local-count summation has supplied its `O(l(T)^2)` estimate.
-/
theorem InteriorBoundaryLocalCount.loss_small_TlogT
    (h : InteriorBoundaryLocalCount) :
    interiorBoundaryLoss
      =o[atTop]
    (fun T : ℝ => T * Zeta23.l T) := by

  have hO :
      interiorBoundaryLoss
        =O[atTop]
      (fun T : ℝ => (Zeta23.l T) ^ 2) := by

    refine IsBigO.of_bound h.C ?_

    filter_upwards [h.eventually_bound]
      with T hT

    rw [Real.norm_eq_abs, Real.norm_eq_abs]

    have hloss0 :
        0 ≤ interiorBoundaryLoss T := by
      simp [interiorBoundaryLoss]

    have hl20 :
        0 ≤ (Zeta23.l T) ^ 2 := by
      positivity

    rw [
      abs_of_nonneg hloss0,
      abs_of_nonneg hl20
    ]

    simpa [mul_assoc] using hT

  exact
    hO.trans_isLittleO
      zeta_l_sq_isLittleO_TlogT

/--
Transport the correctly defined interior boundary loss to `o(N)` using
Anthropic's formalized Riemann--von Mangoldt bridge.
-/
theorem InteriorBoundaryLocalCount.loss_small_zetaDyadicN
    (h : InteriorBoundaryLocalCount) :
    interiorBoundaryLoss
      =o[atTop]
    zetaDyadicN := by

  exact
    isLittleO_zetaDyadicN_of_isLittleO_TlogT
      h.loss_small_TlogT

end HurtadoZeta23