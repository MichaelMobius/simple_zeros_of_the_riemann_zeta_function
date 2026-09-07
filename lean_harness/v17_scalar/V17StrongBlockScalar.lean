import Mathlib.Tactic

noncomputable section

namespace HurtadoZeta23

/-!
# v17 strong-block scalar contradiction core

This file isolates the exact rational algebra in the `m = 450` block argument.
It deliberately assumes the analytic/spectral inputs separately.
-/

def v17A : ℝ := 4329 / 2500

def v17Q : ℝ := 111 / 125

def v17g0 : ℝ := 4449 / 5000

def v17t : ℝ := 33 / 2

def v17Threshold : ℝ := 450 / 449

/-- Slightly weakened threshold used directly on the finite Gram matrix.  It
leaves enough rational margin to absorb the small trace error of the finite
Poisson overlap. -/
def v17FiniteThreshold : ℝ := 5011 / 5000

/-- Exact positive contradiction margin for the ideal `450/449` threshold. -/
theorem v17_contradiction_margin :
    0 < v17g0 * v17Q + (1 - 1 / v17t) * v17Threshold - v17A := by
  norm_num [v17g0, v17Q, v17t, v17Threshold, v17A]

/-- The exact rational value of the ideal contradiction margin. -/
theorem v17_contradiction_margin_exact :
    v17g0 * v17Q + (1 - 1 / v17t) * v17Threshold - v17A
      = 88071 / 3086875000 := by
  norm_num [v17g0, v17Q, v17t, v17Threshold, v17A]

/-- The finite-Gram threshold still leaves a strictly positive exact margin. -/
theorem v17_finite_contradiction_margin :
    0 < v17g0 * v17Q + (1 - 1 / v17t) * v17FiniteThreshold - v17A := by
  norm_num [v17g0, v17Q, v17t, v17FiniteThreshold, v17A]

/-- Exact value of the finite-Gram contradiction margin. -/
theorem v17_finite_contradiction_margin_exact :
    v17g0 * v17Q + (1 - 1 / v17t) * v17FiniteThreshold - v17A
      = 31 / 10312500 := by
  norm_num [v17g0, v17Q, v17t, v17FiniteThreshold, v17A]

/-- Once the spectral argument supplies the standard lower bound
`2*a - 1 + a^2/449` with `a>1`, the ideal `450/449` threshold is automatic. -/
theorem v17_threshold_from_quadratic
    {D a : ℝ}
    (ha : 1 < a)
    (hD : 2 * a - 1 + a ^ 2 / 449 ≤ D) :
    v17Threshold < D := by
  have hs : 0 ≤ (a - 1) ^ 2 := sq_nonneg (a - 1)
  norm_num [v17Threshold] at hD ⊢
  nlinarith

/-- Generic error-aware scalar finisher.  The threshold is a parameter; the
only requirement is the explicit positive contradiction margin. -/
theorem v17_strong_block_scalar_with_errors_of_threshold
    {theta D E O P eK eW : ℝ}
    (hmargin :
      0 < v17g0 * v17Q + (1 - 1 / v17t) * theta - v17A)
    (hEP : v17A ≤ E + P)
    (hweighted : v17t * v17g0 * v17Q ≤ D + v17t * P + eW)
    (henergy : E - eK ≤ O)
    (hthreshold : D < O → theta < D)
    (herr : eW ≤ v17t * eK) :
    v17A - eK ≤ D + P := by
  by_contra hnot
  have hDP : D + P < v17A - eK := lt_of_not_ge hnot
  have hDO : D < O := by
    have hDE : D < E - eK := by linarith
    exact lt_of_lt_of_le hDE henergy
  have hD : theta < D := hthreshold hDO
  have hupper :
      D + v17t * P + eW <
        v17t * v17A - (v17t - 1) * theta := by
    have hid :
        D + v17t * P + eW =
          v17t * (D + P) - (v17t - 1) * D + eW := by
      ring
    rw [hid]
    have htpos : 0 < v17t := by norm_num [v17t]
    have htm1pos : 0 < v17t - 1 := by norm_num [v17t]
    nlinarith
  have hmargin' :
      v17t * v17A - (v17t - 1) * theta
        < v17t * v17g0 * v17Q := by
    have htpos : 0 < v17t := by norm_num [v17t]
    field_simp [ne_of_gt htpos] at hmargin ⊢
    nlinarith
  linarith

/-- Scalar finishing lemma for the ideal strong `m=450` block estimate. -/
theorem v17_strong_block_scalar
    {D E P : ℝ}
    (hEP : v17A ≤ E + P)
    (hweighted : v17t * v17g0 * v17Q ≤ D + v17t * P)
    (hthreshold : D < E → v17Threshold < D) :
    v17A ≤ D + P := by
  have h := v17_strong_block_scalar_with_errors_of_threshold
    (theta := v17Threshold) (D := D) (E := E) (O := E)
    (P := P) (eK := 0) (eW := 0)
    v17_contradiction_margin hEP (by simpa using hweighted)
    (by linarith) hthreshold (by norm_num)
  simpa using h

/-- Error-aware scalar finisher with the ideal threshold. -/
theorem v17_strong_block_scalar_with_errors
    {D E O P eK eW : ℝ}
    (hEP : v17A ≤ E + P)
    (hweighted : v17t * v17g0 * v17Q ≤ D + v17t * P + eW)
    (henergy : E - eK ≤ O)
    (hthreshold : D < O → v17Threshold < D)
    (herr : eW ≤ v17t * eK) :
    v17A - eK ≤ D + P := by
  exact v17_strong_block_scalar_with_errors_of_threshold
    v17_contradiction_margin hEP hweighted henergy hthreshold herr

/-- Error-aware finisher for the finite Gram matrix, using the robust
`5011/5000` threshold. -/
theorem v17_strong_block_scalar_finite
    {D E O P eK eW : ℝ}
    (hEP : v17A ≤ E + P)
    (hweighted : v17t * v17g0 * v17Q ≤ D + v17t * P + eW)
    (henergy : E - eK ≤ O)
    (hthreshold : D < O → v17FiniteThreshold < D)
    (herr : eW ≤ v17t * eK) :
    v17A - eK ≤ D + P := by
  exact v17_strong_block_scalar_with_errors_of_threshold
    v17_finite_contradiction_margin hEP hweighted henergy hthreshold herr

/-- For the raw overlap errors used at `m=450`, the adjacent loss is dominated
by `t` times the full-energy loss. -/
theorem v17_raw_error_absorption (eps : ℝ) (heps : 0 ≤ eps) :
    898 * eps ≤ v17t * (404100 * eps) := by
  norm_num [v17t]
  nlinarith

end HurtadoZeta23
