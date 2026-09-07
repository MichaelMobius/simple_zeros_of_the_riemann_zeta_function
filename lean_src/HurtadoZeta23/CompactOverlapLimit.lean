import HurtadoZeta23.ExactTsumDecomposition
import HurtadoZeta23.FourierConventionAdapter
import HurtadoZeta23.CriticalLatticeGeometry
import HurtadoZeta23.PoissonGaborBridge
import Mathlib.Tactic

noncomputable section

namespace HurtadoZeta23

open Real Filter Topology
open scoped BigOperators

/-- The normalized finite overlap appearing in the sampled vectors
`v_rho = F(gamma)/(sqrt(a_D) L)` of the manuscript. -/
def normalizedIntervalOverlap
    (ϱ : ℝ → ℝ) (L w T τ τ' : ℝ) (kMin kMax : ℤ) : ℝ :=
  intervalFiniteGridOverlap ϱ 1 L w T τ τ' kMin kMax /
    (phiDMean ϱ 1 L w * L ^ 2)

/-- The corresponding normalized full-lattice overlap. -/
def normalizedFullOverlap
    (ϱ : ℝ → ℝ) (L w τ τ' : ℝ) : ℝ :=
  fullGridOverlap ϱ 1 L w τ τ' /
    (phiDMean ϱ 1 L w * L ^ 2)

/-- Poisson's full-grid overlap, after the vector normalization `a_D L^2`, is
exactly the normalized window kernel used in the window-to-`k` estimate. -/
theorem normalizedFullOverlap_eq_scaledKernel
    {ϱ : ℝ → ℝ} {L w τ τ' : ℝ}
    (hL : L ≠ 0) :
    normalizedFullOverlap ϱ L w τ τ' =
      scaledPhiDFourier ϱ L w (L * (τ - τ') / (2 * Real.pi)) /
        phiDMean ϱ 1 L w := by
  unfold normalizedFullOverlap fullGridOverlap scaledPhiDFourier
  field_simp [hL, Real.pi_ne_zero]

/-- Dividing a raw finite-grid truncation estimate by the Gram-vector
normalization gives the corresponding normalized truncation estimate. -/
theorem normalizedIntervalOverlap_sub_full_bound
    {ϱ : ℝ → ℝ} {L w T τ τ' tailErr : ℝ} {kMin kMax : ℤ}
    (hL : 0 < L)
    (hmean : 0 < |phiDMean ϱ 1 L w|)
    (htail :
      |intervalFiniteGridOverlap ϱ 1 L w T τ τ' kMin kMax -
        fullGridOverlap ϱ 1 L w τ τ'| ≤ tailErr) :
    |normalizedIntervalOverlap ϱ L w T τ τ' kMin kMax -
        normalizedFullOverlap ϱ L w τ τ'|
      ≤ tailErr / (|phiDMean ϱ 1 L w| * L ^ 2) := by
  unfold normalizedIntervalOverlap normalizedFullOverlap
  rw [← sub_div]
  rw [abs_div, abs_mul, abs_pow, abs_of_pos hL]
  exact div_le_div_of_nonneg_right htail (mul_nonneg (le_of_lt hmean) (sq_nonneg L))

/-- A convenient denominator lower bound derived from `aD_close`: under the
same small-perturbation condition used in the quantitative window bridge,
`|a_D| >= K(0)/2`. -/
theorem phiDMean_abs_lower
    {ϱ : ℝ → ℝ} {L w : ℝ}
    (hϱ : Zeta23.TaperProfile ϱ)
    (hw : 1 ≤ w) (hwL : 8 * w ≤ L)
    (hsmall : 4 * w / L ≤ limitingK 0 / 2) :
    limitingK 0 / 2 ≤ |phiDMean ϱ 1 L w| := by
  have hK0 : 0 < limitingK 0 := limitingK_zero_pos
  have hden := phiDMean_close_limitingK_zero hϱ hw hwL
  have htri : limitingK 0 ≤ |phiDMean ϱ 1 L w| +
      |phiDMean ϱ 1 L w - limitingK 0| := by
    calc
      limitingK 0 = |limitingK 0| := (abs_of_pos hK0).symm
      _ = |phiDMean ϱ 1 L w +
            (limitingK 0 - phiDMean ϱ 1 L w)| := by
            congr 1
            ring
      _ ≤ |phiDMean ϱ 1 L w| +
            |limitingK 0 - phiDMean ϱ 1 L w| := by
            exact abs_add_le _ _
      _ = |phiDMean ϱ 1 L w| +
            |phiDMean ϱ 1 L w - limitingK 0| := by
            rw [abs_sub_comm]
  linarith

/-- Quantitative compact-overlap estimate with all full-grid/window analysis
already discharged.  The only supplied error is the literal finite-lattice
raw tail. -/
theorem compactOverlap_quantitative
    {ϱ : ℝ → ℝ} {L w T τ τ' tailErr : ℝ} {kMin kMax : ℤ}
    (hϱ : Zeta23.TaperProfile ϱ)
    (hw : 1 ≤ w) (hwL : 8 * w ≤ L)
    (hsmall : 4 * w / L ≤ limitingK 0 / 2)
    (htail :
      |intervalFiniteGridOverlap ϱ 1 L w T τ τ' kMin kMax -
        fullGridOverlap ϱ 1 L w τ τ'| ≤ tailErr) :
    |normalizedIntervalOverlap ϱ L w T τ τ' kMin kMax -
        limitingk (L * (τ - τ') / (2 * Real.pi))|
      ≤ tailErr / (|phiDMean ϱ 1 L w| * L ^ 2) +
        20 * (w / L) / limitingK 0 := by
  have hL : 0 < L := by linarith
  have hmeanLower := phiDMean_abs_lower hϱ hw hwL hsmall
  have hK0 : 0 < limitingK 0 := limitingK_zero_pos
  have hmean : 0 < |phiDMean ϱ 1 L w| := lt_of_lt_of_le (by positivity) hmeanLower
  have htrunc := normalizedIntervalOverlap_sub_full_bound
    (ϱ := ϱ) (L := L) (w := w) (T := T) (τ := τ) (τ' := τ')
    (tailErr := tailErr) (kMin := kMin) (kMax := kMax) hL hmean htail
  have hfull := normalized_window_kernel_error_uniform_proved
    hϱ hw hwL hsmall (L * (τ - τ') / (2 * Real.pi))
  rw [normalizedFullOverlap_eq_scaledKernel (ϱ := ϱ) (w := w)
      (τ := τ) (τ' := τ') (ne_of_gt hL)] at htrunc
  exact overlap_error_triangle htrunc hfull

/-- Pointwise wrapper in exactly the form consumed by the 262-point kernel
bridge.  It separates the analytic compact-overlap estimate from the elementary
unit-norm facts about the sampled vectors. -/
theorem rawPointwiseOverlapApproximation262_of_error
    (y : ℕ → ℝ) (overlap : ℕ → ℕ → ℝ) (eps : ℝ)
    (heps : 0 ≤ eps)
    (hover : ∀ a b, |overlap a b| ≤ 1)
    (hk : ∀ a b, |limitingk (y b - y a)| ≤ 1)
    (happrox : ∀ a b,
      |overlap a b - limitingk (y b - y a)| ≤ eps) :
    RawPointwiseOverlapApproximation262 y overlap eps := by
  exact ⟨heps, hover, hk, happrox⟩

end HurtadoZeta23
