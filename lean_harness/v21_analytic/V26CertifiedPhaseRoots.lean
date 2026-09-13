import HurtadoZeta23.V21KernelRootQuadratic
import HurtadoZeta23.V26AnalyticMinorant
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Tactic

noncomputable section

open Set

namespace HurtadoZeta23

/-- Every certified left endpoint lies strictly to the right of its integer
cell origin.  This is exact finite rational bookkeeping. -/
lemma v26_nat_lt_rootLeft {n : ℕ} (hn1 : 1 ≤ n) (hn12 : n ≤ 12) :
    (n : ℝ) < v21RootLeft n := by
  interval_cases n <;> norm_num [v21RootLeft]

/-- The short root brackets lie inside the principal tangent branch. -/
lemma v26_rootRight_lt_nat_add_half {n : ℕ} (hn1 : 1 ≤ n) (hn12 : n ≤ 12) :
    v21RootRight n < (n : ℝ) + (1 / 2 : ℝ) := by
  interval_cases n <;> norm_num [v21RootRight]

/-- The phase shift constant is exactly the reciprocal coefficient appearing
in the cleared root numerator. -/
lemma v26_c_div_eq (x : ℝ) :
    v26c / x = 1 / (2 * v21C * Real.pi * x) := by
  unfold v26c
  ring

/-- A zero of the cleared numerator inside one of the twelve certified
brackets is exactly an integer point of the v26 phase map. -/
lemma v26_phase_eq_nat_of_rootH_zero {n : ℕ}
    (hn1 : 1 ≤ n) (hn12 : n ≤ 12) {r : ℝ}
    (hrL : v21RootLeft n < r) (hrR : r < v21RootRight n)
    (hzero : v21RootH n r = 0) :
    v26PhaseWith v26c r = (n : ℝ) := by
  have hnr : (n : ℝ) < r :=
    (v26_nat_lt_rootLeft hn1 hn12).trans hrL
  have hr0 : 0 < r := by
    have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    linarith
  have hrhalf : r < (n : ℝ) + (1 / 2 : ℝ) :=
    hrR.trans (v26_rootRight_lt_nat_add_half hn1 hn12)
  let θ : ℝ := Real.pi * (r - (n : ℝ))
  have hθ0 : 0 < θ := by
    dsimp [θ]
    exact mul_pos Real.pi_pos (sub_pos.mpr hnr)
  have hθU : θ < Real.pi / 2 := by
    have he : r - (n : ℝ) < (1 / 2 : ℝ) := by linarith
    have hm := mul_lt_mul_of_pos_left he Real.pi_pos
    dsimp [θ]
    nlinarith
  have hθL : -(Real.pi / 2) < θ := by
    have hp : 0 < Real.pi / 2 := by positivity
    linarith
  have hcos : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨hθL, hθU⟩
  have hzero' :
      v21C * Real.pi * r * Real.sin θ =
        (1 / 2 : ℝ) * Real.cos θ := by
    unfold v21RootH at hzero
    dsimp [θ]
    linarith
  have htan : Real.tan θ = v26c / r := by
    rw [Real.tan_eq_sin_div_cos, v26_c_div_eq]
    apply (div_eq_iff hcos.ne').2
    have hC : v21C ≠ 0 := v26_C_pos.ne'
    have hp : Real.pi ≠ 0 := Real.pi_ne_zero
    have hr : r ≠ 0 := hr0.ne'
    field_simp [hC, hp, hr]
    nlinarith [hzero']
  have hatan : Real.arctan (v26c / r) = θ := by
    rw [← htan]
    exact Real.arctan_tan hθL hθU
  unfold v26PhaseWith
  rw [hatan]
  dsimp [θ]
  field_simp [Real.pi_ne_zero]
  ring

/-- The twelve rational sign brackets contain genuine phase roots, strictly
inside their endpoints.  No numerical root finder or floating-point oracle is
used: existence is the intermediate value theorem applied to the exact sign
certificates. -/
theorem v26_exists_certified_phase_root {n : ℕ}
    (hn1 : 1 ≤ n) (hn12 : n ≤ 12) :
    ∃ r : ℝ,
      v21RootLeft n < r ∧
      r < v21RootRight n ∧
      v26PhaseWith v26c r = (n : ℝ) ∧
      |r - v21RootRight n| < (1 / 100000 : ℝ) := by
  have hLR : v21RootLeft n ≤ v21RootRight n :=
    v21_root_left_le_right hn1 hn12
  have hcont : ContinuousOn (v21RootH n)
      (Set.Icc (v21RootLeft n) (v21RootRight n)) := by
    intro z hz
    exact (v21_rootH_hasDerivAt n z).continuousAt.continuousWithinAt
  have hleft := v21_root_left_sign hn1 hn12
  have hright := v21_root_right_sign hn1 hn12
  have hzeroIcc :
      (0 : ℝ) ∈ Set.Icc
        (v21RootH n (v21RootLeft n))
        (v21RootH n (v21RootRight n)) := by
    constructor <;> linarith
  have hzimg := intermediate_value_Icc hLR hcont hzeroIcc
  rcases hzimg with ⟨r, hrIcc, hzero⟩
  have hLne : v21RootLeft n ≠ r := by
    intro h
    subst r
    linarith
  have hRne : r ≠ v21RootRight n := by
    intro h
    subst r
    linarith
  have hrL : v21RootLeft n < r := lt_of_le_of_ne hrIcc.1 hLne
  have hrR : r < v21RootRight n := lt_of_le_of_ne hrIcc.2 hRne
  have hphase := v26_phase_eq_nat_of_rootH_zero hn1 hn12 hrL hrR hzero
  have hwidth := v21_root_width hn1 hn12
  have hdist : |r - v21RootRight n| < (1 / 100000 : ℝ) := by
    rw [abs_of_nonpos (sub_nonpos.mpr hrIcc.2)]
    linarith
  exact ⟨r, hrL, hrR, hphase, hdist⟩

/-- Certified version of `v26_rounded_cell_minorant`.  The root and its phase
identity are now internal consequences of the twelve rational sign brackets;
cell-specific callers provide only rational interval and rounding checks. -/
theorem v26_rounded_cell_minorant_certified
    {L U Lstar x q eps rho alpha eta : ℝ} {N : ℕ}
    (hN1 : 1 ≤ N) (hN12 : N ≤ 12)
    (hq : q = v21RootRight N)
    (heps : eps = (1 / 100000 : ℝ))
    (hLstar : Lstar = min L (q - eps))
    (hLx : L ≤ x) (hxU : x ≤ U)
    (hLstar0 : 0 < Lstar) (hLstarx : Lstar ≤ x)
    (hrho : rho = v26Mrat Lstar * (max |L - q| |U - q| + eps))
    (hrho0 : 0 < rho) (hrho1 : rho < 1)
    (hxkernel : v21A < v21B x)
    (hxdk : v26dk < x ^ 2)
    (halpha : alpha ≤ (999 / 1000 : ℝ) * v26Araw U rho)
    (heta : (999 / 10000000000 : ℝ) * v26Araw U rho ≤ eta) :
    alpha * (x - q) ^ 2 - eta ≤ limitingWeight x := by
  obtain ⟨r, hrL, hrR, hphase, hdistR⟩ :=
    v26_exists_certified_phase_root hN1 hN12
  have hwidth := v21_root_width hN1 hN12
  have hqminus : q - eps = v21RootLeft N := by
    rw [hq, heps]
    linarith
  have hLstarr : Lstar ≤ r := by
    rw [hLstar, hqminus]
    exact (min_le_right L (v21RootLeft N)).trans hrL.le
  have hdist : |r - q| < (1 / 100000 : ℝ) := by
    simpa [hq] using hdistR
  have hrq : |r - q| ≤ eps := by
    rw [heps]
    exact hdist.le
  have heps0 : 0 ≤ eps := by rw [heps]; norm_num
  exact v26_rounded_cell_minorant
    hLx hxU hLstar0 hLstarx hLstarr hphase heps0 hrq hdist
    hrho hrho0 hrho1 hxkernel hxdk halpha heta

end HurtadoZeta23
