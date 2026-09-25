import HurtadoZeta23.ResearchWindowPositivity
import HurtadoZeta23.ResearchNinePointHybrid
import Mathlib.Tactic

noncomputable section

namespace HurtadoZeta23

/-!
# Research-only one-gap weighted pressure for the actual window

For `w(g) = k_v(g)^2`, the single certified signed-kernel value at
`g₀ = 43/50`, together with positivity/monotonicity of the actual seven-term
window kernel, gives the scalar inequality required by the hybrid adjacent-pair
argument for every local capacity `0 ≤ q ≤ beta`.
-/

/-- Squared actual-window overlap weight. -/
def research9WindowWeightAt (g : ℝ) : ℝ :=
  research9WindowKernelAt g ^ 2

/-- The squared actual-window weight is nonnegative everywhere. -/
theorem research9_window_weight_nonneg (g : ℝ) :
    0 ≤ research9WindowWeightAt g := by
  unfold research9WindowWeightAt
  positivity

/-- The rational kernel threshold itself is positive. -/
theorem research9_kernelLower_pos : 0 < research9KernelLower := by
  norm_num [research9KernelLower]

/-- Below `g₀`, the actual-window squared weight strictly dominates the full
worst-case linear target `t * beta * g₀`. -/
theorem research9_window_weight_gt_full_target_below_g0
    {g : ℝ} (hg : 0 ≤ g) (hle : g ≤ research9g0) :
    research9t * research9Beta * research9g0 < research9WindowWeightAt g := by
  have hg0eq : research9g0 = (43 / 50 : ℝ) := by
    rfl
  have hgIcc : g ∈ Set.Icc (0 : ℝ) (43 / 50 : ℝ) := by
    constructor
    · exact hg
    · simpa [research9g0] using hle
  have hk := research9_window_kernel_gt_of_mem_Icc_086 hgIcc
  have hklower : (0 : ℝ) < 521 / 2500 := by norm_num
  have hkpos : 0 < research9WindowKernelAt g := lt_trans hklower hk
  have hsquare :
      (521 / 2500 : ℝ) ^ 2 < research9WindowKernelAt g ^ 2 := by
    nlinarith
  have hmargin := research9_kernel_square_margin
  unfold research9WindowWeightAt
  exact lt_trans hmargin hsquare

/-- One-gap scalar pressure inequality for the actual research window.

This is the precise local inequality used when summing the adjacent-pair
mechanism: `q` may be any local certificate capacity in `[0,beta]`, and `g`
may be any nonnegative gap. -/
theorem research9_window_one_gap_pressure
    {q g : ℝ}
    (hq0 : 0 ≤ q)
    (hqβ : q ≤ research9Beta)
    (hg : 0 ≤ g) :
    research9t * q * research9g0 ≤
      research9WindowWeightAt g + research9t * q * g := by
  have ht : 0 < research9t := by norm_num [research9t]
  have hg0 : 0 < research9g0 := by norm_num [research9g0]
  by_cases hle : g ≤ research9g0
  · have hwfull := research9_window_weight_gt_full_target_below_g0 hg hle
    have hqtarget :
        research9t * q * research9g0 ≤
          research9t * research9Beta * research9g0 := by
      have hfac : 0 ≤ research9t * research9g0 := by positivity
      nlinarith
    have hlin : 0 ≤ research9t * q * g := by positivity
    linarith
  · have hge : research9g0 ≤ g := le_of_lt (lt_of_not_ge hle)
    have hlinear :
        research9t * q * research9g0 ≤ research9t * q * g := by
      have hfac : 0 ≤ research9t * q := by positivity
      exact mul_le_mul_of_nonneg_left hge hfac
    have hw0 := research9_window_weight_nonneg g
    linarith

end HurtadoZeta23
