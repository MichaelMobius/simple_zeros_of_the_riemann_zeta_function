import HurtadoZeta23.ConcreteAsymptoticInputs
import HurtadoZeta23.InteriorBoundaryBridge
import Mathlib.Tactic

noncomputable section

open Filter Asymptotics

namespace HurtadoZeta23

/-!
# Retained-core and Riemann--von Mangoldt bridge

This file packages the two concrete finite-geometric ingredients needed after
finite Gram pinching:

1. the central retained simple-zero count differs from the full simple-zero
   count only by the two *interior* boundary strips;
2. the normalized retained span is bounded by the genuine Zeta23
   Riemann--von Mangoldt main scale plus an `o(T*l(T))` geometric error.

The data-carrying packages below live in `Type`, not `Prop`.
-/

/-! ## Central retained counts -/

/-- Pure cardinal bookkeeping behind `N₀ˢ - Sᵒ ≤ boundaryLoss`. -/
theorem retained_loss_le_boundary_of_counts
    {total retained removed boundary : ℕ}
    (hdecomp : retained + removed = total)
    (hremoved : removed ≤ boundary) :
    (total : ℝ) - (retained : ℝ) ≤ (boundary : ℝ) := by
  have hcast :
      (retained : ℝ) + (removed : ℝ) = (total : ℝ) := by
    exact_mod_cast hdecomp
  have hremcast :
      (removed : ℝ) ≤ (boundary : ℝ) := by
    exact_mod_cast hremoved
  have heq :
      (total : ℝ) - (retained : ℝ) = (removed : ℝ) := by
    linarith
  rw [heq]
  exact hremcast

/-- Concrete finite-count interface for the retained central simple zeros.

The deleted zeros are charged to the *interior* `L^2`-cell boundary strips
from the compact-overlap lemma, not to Zeta23's exterior `NII`.

This package contains functions, hence it belongs to `Type`.
-/
structure CentralRetentionCounts where
  retainedCount : ℝ → ℕ
  removedCount : ℝ → ℕ
  decomposition : ∀ᶠ T in atTop,
    retainedCount T + removedCount T = Zeta23.N0simple T (2 * T)
  removed_le_boundary : ∀ᶠ T in atTop,
    removedCount T ≤ interiorBoundaryCountNat T

/-- The retained central count as a real-valued function. -/
def CentralRetentionCounts.retainedReal
    (h : CentralRetentionCounts) (T : ℝ) : ℝ :=
  (h.retainedCount T : ℝ)

/-- The geometric boundary inclusion implies the exact retained-count bound
needed by shifted pinching. -/
theorem CentralRetentionCounts.eventually_retained_bound
    (h : CentralRetentionCounts) :
    ∀ᶠ T in atTop,
      globalS T - interiorBoundaryLoss T ≤ h.retainedReal T := by
  filter_upwards [h.decomposition, h.removed_le_boundary] with T hdec hrem
  have hloss :=
    retained_loss_le_boundary_of_counts hdec hrem
  simpa [globalS, interiorBoundaryLoss,
    CentralRetentionCounts.retainedReal, add_comm] using hloss

/-! ## Canonical Riemann--von Mangoldt remainder -/

/-- Genuine leading term in Zeta23's formalized Riemann--von Mangoldt
formula. -/
def rvmMainScale (T : ℝ) : ℝ :=
  T / (2 * Real.pi) * Zeta23.ell1 T

/-- Canonical absolute RvM remainder. -/
def canonicalRvMErr (T : ℝ) : ℝ :=
  |globalN T - rvmMainScale T|

/-- The canonical absolute remainder gives the elementary one-sided
comparison needed for span control. -/
theorem eventually_rvmMainScale_le_globalN_add_err :
    ∀ᶠ T in atTop,
      rvmMainScale T ≤ globalN T + canonicalRvMErr T := by
  filter_upwards [] with T
  have h :=
    le_abs_self (rvmMainScale T - globalN T)
  have habs :
      |rvmMainScale T - globalN T|
        = canonicalRvMErr T := by
    unfold canonicalRvMErr
    rw [abs_sub_comm]
  rw [habs] at h
  linarith

/-- `log T = O(l(T))`.  The two functions differ only by the fixed constant
`log(2π)` for sufficiently large positive `T`. -/
lemma log_isBigO_zeta_l :
    Real.log =O[atTop] Zeta23.l := by
  have hl_top := tendsto_zeta_l_atTop
  have hl1 :
      ∀ᶠ T : ℝ in atTop, (1 : ℝ) ≤ Zeta23.l T :=
    hl_top.eventually_ge_atTop 1
  have hconstEvt :
      ∀ᶠ T : ℝ in atTop,
        |Real.log (2 * Real.pi)| ≤ Zeta23.l T :=
    hl_top.eventually_ge_atTop |Real.log (2 * Real.pi)|
  refine IsBigO.of_bound 2 ?_
  filter_upwards
    [hl1, hconstEvt, eventually_ge_atTop (2 * Real.pi)]
    with T hl hc hT
  have hpi : 0 < 2 * Real.pi := by positivity
  have hT0 : 0 < T := lt_of_lt_of_le hpi hT
  have hlogsplit :
      Real.log T =
        Zeta23.l T + Real.log (2 * Real.pi) := by
    unfold Zeta23.l
    rw [Real.log_div hT0.ne' hpi.ne']
    ring
  rw [Real.norm_eq_abs, Real.norm_eq_abs, hlogsplit]
  have hl0 : 0 ≤ Zeta23.l T := by linarith
  calc
    |Zeta23.l T + Real.log (2 * Real.pi)|
        ≤ |Zeta23.l T| + |Real.log (2 * Real.pi)| := abs_add_le _ _
    _ ≤ 2 * |Zeta23.l T| := by
      rw [abs_of_nonneg hl0]
      linarith
    _ = 2 * ‖Zeta23.l T‖ := by
      rw [Real.norm_eq_abs]

/-- `l(T) = o(T*l(T))`. -/
lemma zeta_l_isLittleO_TlogT :
    Zeta23.l =o[atTop] (fun T : ℝ => T * Zeta23.l T) := by
  exact Zeta23.Assembly.isLittleO_l_Tl

/-- `log T = o(T*l(T))`.  This is already part of Zeta23's RvM
asymptotic package. -/
lemma log_isLittleO_TlogT :
    Real.log =o[atTop] (fun T : ℝ => T * Zeta23.l T) := by
  exact Zeta23.Assembly.isLittleO_log_Tl

/-- Zeta23's RvM remainder is `O(log T)`, hence `o(T*l(T))`. -/
theorem canonicalRvMErr_small_TlogT :
    canonicalRvMErr
      =o[atTop] (fun T : ℝ => T * Zeta23.l T) := by
  obtain ⟨C, T0, hmain⟩ :=
    Zeta23.paperInputs_zeta.RvM.main

  have hOlog :
      canonicalRvMErr =O[atTop] Real.log := by
    refine IsBigO.of_bound |C| ?_
    filter_upwards
      [eventually_ge_atTop T0, eventually_ge_atTop (1 : ℝ)]
      with T hT hT1
    have hm := hmain T hT
    have hm' :
        canonicalRvMErr T ≤ C * Real.log T := by
      simpa [canonicalRvMErr, globalN, rvmMainScale] using hm
    have herr0 : 0 ≤ canonicalRvMErr T := by
      exact abs_nonneg _
    have hlog0 : 0 ≤ Real.log T :=
      Real.log_nonneg hT1
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg herr0, abs_of_nonneg hlog0]
    exact hm'.trans
      (mul_le_mul_of_nonneg_right (le_abs_self C) hlog0)

  exact
    hOlog.trans_isLittleO log_isLittleO_TlogT

/-! ## Span package -/

/-- Problem-specific geometric span package.

It contains the span and error functions, so it lives in `Type`.
-/
structure RvMSpanInputs where
  span : ℝ → ℝ
  geomErr : ℝ → ℝ
  geom_bound : ∀ᶠ T in atTop,
    span T ≤ rvmMainScale T + geomErr T
  geomErr_small_TlogT :
    geomErr =o[atTop] (fun T : ℝ => T * Zeta23.l T)

/-- Combined span error: geometry plus the canonical RvM remainder. -/
def RvMSpanInputs.totalErr
    (h : RvMSpanInputs) (T : ℝ) : ℝ :=
  h.geomErr T + canonicalRvMErr T

theorem RvMSpanInputs.totalErr_small_TlogT
    (h : RvMSpanInputs) :
    h.totalErr
      =o[atTop] (fun T : ℝ => T * Zeta23.l T) := by
  change
    (fun T : ℝ => h.geomErr T + canonicalRvMErr T)
      =o[atTop] (fun T : ℝ => T * Zeta23.l T)
  exact
    h.geomErr_small_TlogT.add canonicalRvMErr_small_TlogT

theorem RvMSpanInputs.eventually_span_bound
    (h : RvMSpanInputs) :
    ∀ᶠ T in atTop,
      h.span T ≤ globalN T + h.totalErr T := by
  filter_upwards
    [h.geom_bound, eventually_rvmMainScale_le_globalN_add_err]
    with T hg hr
  simp only [RvMSpanInputs.totalErr]
  linarith

/-! ## Constructor for final shifted pinching -/

/-- Corrected constructor for the final RvM pinching package.

Boundary loss is the actual interior-strip loss and its `o(N)` estimate is
obtained from `InteriorBoundaryLocalCount`.
-/
def mkRvMShiftedPinchingInputs
    (ret : CentralRetentionCounts)
    (hboundary : InteriorBoundaryLocalCount)
    (sp : RvMSpanInputs)
    (defect blockErr : ℝ → ℝ)
    (hblock : blockErr =o[atTop] globalN)
    (hpinch : ∀ᶠ T in atTop,
      alpha * ret.retainedReal T - pressureCost * sp.span T
        - endpointCorrection - blockErr T ≤ defect T) :
    RvMShiftedPinchingInputs :=
  { retained := ret.retainedReal
    defect := defect
    span := sp.span
    retainedLoss := interiorBoundaryLoss
    spanErr := sp.totalErr
    blockErr := blockErr

    retainedLoss_small := by
      have hs := hboundary.loss_small_zetaDyadicN
      change
        interiorBoundaryLoss
          =o[atTop]
        (fun T : ℝ => (Zeta23.Ncount T (2 * T) : ℝ)) at hs
      change
        interiorBoundaryLoss
          =o[atTop]
        (fun T : ℝ => (Zeta23.Ncount T (2 * T) : ℝ))
      exact hs

    spanErr_small_TlogT :=
      sp.totalErr_small_TlogT

    blockErr_small := hblock

    retained_bound :=
      ret.eventually_retained_bound

    span_bound :=
      sp.eventually_span_bound

    pinching_bound := hpinch }

end HurtadoZeta23
