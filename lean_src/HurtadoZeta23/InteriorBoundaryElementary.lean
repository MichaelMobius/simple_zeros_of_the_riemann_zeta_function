import HurtadoZeta23.InteriorBoundaryUnitCover
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

noncomputable section

open Filter Asymptotics Finset

namespace HurtadoZeta23

/-- Eventually `l(T)` is positive and at least one. -/
theorem eventually_one_le_zeta_l :
    ∀ᶠ T : ℝ in atTop, (1 : ℝ) ≤ Zeta23.l T :=
  Zeta23.Assembly.eventually_one_le_l

/-- `log T ≤ T/8` eventually.  We use Mathlib's standard
`log T = o(T)` result rather than a hard-coded finite threshold. -/
theorem eventually_log_le_eighth_id :
    ∀ᶠ T : ℝ in atTop, Real.log T ≤ T / 8 := by
  have hsmall :
      Real.log =o[atTop] (fun T : ℝ => T) := by
    simpa [Real.rpow_one] using
      (isLittleO_log_rpow_atTop
        (show (0 : ℝ) < 1 by norm_num))
  have hb :=
    hsmall.def (show (0 : ℝ) < (1 / 8 : ℝ) by norm_num)
  filter_upwards
    [hb, Zeta23.Assembly.eventually_log_nonneg,
      eventually_ge_atTop (0 : ℝ)]
    with T hbound hlog0 hT0
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg hlog0, abs_of_nonneg hT0] at hbound
  nlinarith

/-- Eventually `8*l(T) ≤ T`. -/
theorem eventually_eight_zeta_l_le_id :
    ∀ᶠ T : ℝ in atTop, 8 * Zeta23.l T ≤ T := by
  filter_upwards
    [eventually_log_le_eighth_id, eventually_gt_atTop (0 : ℝ)]
    with T hlog hT
  have hconst :
      0 ≤ Real.log (2 * Real.pi) := by
    apply Real.log_nonneg
    nlinarith [Real.pi_gt_three]
  have hl_le_log :
      Zeta23.l T ≤ Real.log T := by
    rw [Zeta23.Assembly.log_eq_l_add hT]
    linarith
  nlinarith

/-- A deliberately generous ceiling bound for the number of unit windows
needed to cover a strip of width `2π l(T)`.  No optimal constant is needed in
the asymptotic argument. -/
theorem eventually_interiorBoundaryUnitWindows_le_eight_l :
    ∀ᶠ T : ℝ in atTop,
      (interiorBoundaryUnitWindows T : ℝ) ≤ 8 * Zeta23.l T := by
  filter_upwards [eventually_one_le_zeta_l] with T hl
  have hl0 : 0 ≤ Zeta23.l T := by
    linarith
  have hw0 : 0 ≤ interiorBoundaryWidth T := by
    unfold interiorBoundaryWidth
    positivity
  have hceil :
      (interiorBoundaryUnitWindows T : ℝ) <
        interiorBoundaryWidth T + 1 := by
    unfold interiorBoundaryUnitWindows
    exact_mod_cast Nat.ceil_lt_add_one hw0
  have hpi : 2 * Real.pi < 7 := by
    nlinarith [Real.pi_lt_d2]
  unfold interiorBoundaryWidth at hceil
  nlinarith

/-- A common elementary bound used on both interior strips:
for large `T`, `log(3T) ≤ 4*l(T)`. -/
theorem eventually_log_three_mul_le_four_l :
    ∀ᶠ T : ℝ in atTop,
      Real.log (3 * T) ≤ 4 * Zeta23.l T := by
  filter_upwards
    [eventually_ge_atTop (3 : ℝ),
      Zeta23.Assembly.eventually_log_le_two_l,
      eventually_one_le_zeta_l]
    with T hT hlog hl
  have hTpos : 0 < T := by
    linarith
  have hlog3 :
      Real.log 3 ≤ Real.log T := by
    exact
      Real.log_le_log
        (by norm_num : (0 : ℝ) < 3)
        (by linarith)
  rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hTpos.ne']
  nlinarith

/-- On the left interior strip, every unit-window logarithm is at most
`4*l(T)` for sufficiently large `T`. -/
theorem eventually_left_interior_log_le_four_l :
    ∀ᶠ T : ℝ in atTop,
      ∀ i < interiorBoundaryUnitWindows T,
        Real.log (|T + i| + 3) ≤ 4 * Zeta23.l T := by
  filter_upwards
    [eventually_ge_atTop (3 : ℝ),
      eventually_interiorBoundaryUnitWindows_le_eight_l,
      eventually_eight_zeta_l_le_id,
      eventually_log_three_mul_le_four_l]
    with T hT hn h8T hlog3T
  intro i hi
  have hT0 : 0 ≤ T := by
    linarith
  have hi0 : 0 ≤ (i : ℝ) := by
    positivity
  have hi_lt_n :
      (i : ℝ) < (interiorBoundaryUnitWindows T : ℝ) := by
    exact_mod_cast hi
  have hi_le_T :
      (i : ℝ) ≤ T := by
    have hi_le_l :
        (i : ℝ) ≤ 8 * Zeta23.l T := by
      linarith
    exact hi_le_l.trans h8T
  have harg :
      |T + (i : ℝ)| + 3 ≤ 3 * T := by
    rw [abs_of_nonneg (add_nonneg hT0 hi0)]
    nlinarith
  have hargpos :
      0 < |T + (i : ℝ)| + 3 := by
    positivity
  have h3Tpos :
      0 < 3 * T := by
    positivity
  have hlogmono :
      Real.log (|T + (i : ℝ)| + 3) ≤ Real.log (3 * T) := by
    exact Real.log_le_log hargpos harg
  exact hlogmono.trans hlog3T

/-- The right interior strip satisfies the same coarse logarithmic envelope. -/
theorem eventually_right_interior_log_le_four_l :
    ∀ᶠ T : ℝ in atTop,
      ∀ i < interiorBoundaryUnitWindows T,
        Real.log
            (|2 * T - interiorBoundaryUnitWindows T + i| + 3)
          ≤ 4 * Zeta23.l T := by
  filter_upwards
    [eventually_ge_atTop (3 : ℝ),
      eventually_interiorBoundaryUnitWindows_le_eight_l,
      eventually_eight_zeta_l_le_id,
      eventually_log_three_mul_le_four_l]
    with T hT hn h8T hlog3T
  intro i hi
  have hT0 : 0 ≤ T := by
    linarith
  have hnT :
      (interiorBoundaryUnitWindows T : ℝ) ≤ T :=
    hn.trans h8T
  have hi_nonneg :
      0 ≤ (i : ℝ) := by
    positivity
  have hi_le_n :
      (i : ℝ) ≤ (interiorBoundaryUnitWindows T : ℝ) := by
    exact_mod_cast Nat.le_of_lt_succ (Nat.lt_succ_of_lt hi)
  have harg0 :
      0 ≤
        2 * T - (interiorBoundaryUnitWindows T : ℝ) + (i : ℝ) := by
    nlinarith
  have harg :
      |2 * T - (interiorBoundaryUnitWindows T : ℝ) + (i : ℝ)| + 3
        ≤ 3 * T := by
    rw [abs_of_nonneg harg0]
    nlinarith
  have hargpos :
      0 <
        |2 * T - (interiorBoundaryUnitWindows T : ℝ) + (i : ℝ)| + 3 := by
    positivity
  have h3Tpos :
      0 < 3 * T := by
    positivity
  have hlogmono :
      Real.log
          (|2 * T - (interiorBoundaryUnitWindows T : ℝ) + (i : ℝ)| + 3)
        ≤ Real.log (3 * T) := by
    exact Real.log_le_log hargpos harg
  exact hlogmono.trans hlog3T

/-- The elementary envelope required by `interiorBoundaryLocalCount_of_rvm`
is therefore unconditional.  Constants 8 and 4 are intentionally loose. -/
def interiorBoundaryElementaryEnvelope : InteriorBoundaryElementaryEnvelope :=
  { Cn := 8
    Clog := 4
    Cn_nonneg := by norm_num
    Clog_nonneg := by norm_num
    unitWindows_bound := eventually_interiorBoundaryUnitWindows_le_eight_l
    leftLog_bound := eventually_left_interior_log_le_four_l
    rightLog_bound := eventually_right_interior_log_le_four_l }

/-- The two interior strips have `O(l(T)^2)` zero count, derived solely from
Zeta23's Riemann--von Mangoldt local-count theorem plus elementary analysis. -/
def interiorBoundaryLocalCount_proved : InteriorBoundaryLocalCount :=
  interiorBoundaryLocalCount_of_rvm interiorBoundaryElementaryEnvelope

/-- Consequently the number of simple zeros discarded at the two interior
strips is negligible relative to `N(T,2T)`. -/
theorem interiorBoundaryLoss_isLittleO_zetaDyadicN :
    interiorBoundaryLoss =o[atTop] zetaDyadicN :=
  interiorBoundaryLocalCount_proved.loss_small_zetaDyadicN

end HurtadoZeta23
