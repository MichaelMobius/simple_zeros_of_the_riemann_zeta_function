import Mathlib.Tactic

noncomputable section

namespace HurtadoZeta23

/-!
# Research-only nine-point / adjacent-pair hybrid scalar core

This file verifies only the exact rational assembly algebra for the research
branch `research/master-certificate-v1`.  It does **not** prove the imported
nine-point local certificate, the new window kernel estimate, or the analytic
arbitrary-window interface.
-/

def research9A : ℝ := 4274291 / 2500000

def research9Q : ℝ := 562 / 625

def research9g0 : ℝ := 43 / 50

def research9t : ℝ := 31 / 2

def research9Threshold : ℝ := 289 / 288

def research9Beta : ℝ := 2 / 625

def research9KernelLower : ℝ := 521 / 2500

def research9Hcert : ℝ := 3362285207 / 5000000000

def research9ProjectedBound : ℝ :=
  967204424823 / 1436451418000

/-- Exact positive contradiction margin for the ideal `m = 289` block. -/
theorem research9_contradiction_margin_exact :
    research9g0 * research9Q
      + (1 - 1 / research9t) * research9Threshold
      - research9A
      = 405889 / 174375000 := by
  norm_num [research9g0, research9Q, research9t,
    research9Threshold, research9A]

/-- The ideal block contradiction margin is strictly positive. -/
theorem research9_contradiction_margin :
    0 < research9g0 * research9Q
      + (1 - 1 / research9t) * research9Threshold
      - research9A := by
  rw [research9_contradiction_margin_exact]
  norm_num

/-- The rational signed-kernel target is already strong enough for the scalar
pressure inequality once the analytic theorem
`research9KernelLower < k_v(43/50)` is supplied. -/
theorem research9_kernel_square_margin :
    research9t * research9Beta * research9g0
      < research9KernelLower ^ 2 := by
  norm_num [research9t, research9Beta, research9g0, research9KernelLower]

/-- Pure scalar finisher for the ideal limiting Gram block.  The three
hypotheses are exactly the pieces supplied respectively by the nine-point
certificate, adjacent-pair scalar estimate, and spectral-threshold lemma. -/
theorem research9_strong_block_scalar
    {D E P : ℝ}
    (hEP : research9A ≤ E + P)
    (hweighted :
      research9t * research9g0 * research9Q ≤ D + research9t * P)
    (hthreshold : D < E → research9Threshold < D) :
    research9A ≤ D + P := by
  by_contra hnot
  have hDP : D + P < research9A := lt_of_not_ge hnot
  have hDE : D < E := by
    linarith
  have hD : research9Threshold < D := hthreshold hDE
  have hupper :
      D + research9t * P
        < research9t * research9A
          - (research9t - 1) * research9Threshold := by
    have hid :
        D + research9t * P =
          research9t * (D + P) - (research9t - 1) * D := by
      ring
    rw [hid]
    have htpos : 0 < research9t := by norm_num [research9t]
    have htm1pos : 0 < research9t - 1 := by norm_num [research9t]
    nlinarith
  have hmargin' :
      research9t * research9A
          - (research9t - 1) * research9Threshold
        < research9t * research9g0 * research9Q := by
    have hm := research9_contradiction_margin
    have htpos : 0 < research9t := by norm_num [research9t]
    field_simp [ne_of_gt htpos] at hm ⊢
    nlinarith
  linarith

/-- Exact final rational arithmetic for the projected global constant. -/
theorem research9_projected_bound_exact :
    (289 * research9Hcert - research9Q) /
        (289 - research9A)
      = research9ProjectedBound := by
  norm_num [research9Hcert, research9Q, research9A,
    research9ProjectedBound]

/-- The projected hybrid constant is strictly larger than the decimal
`0.673329`, expressed as an exact rational comparison. -/
theorem research9_projected_bound_gt_673329 :
    (673329 / 1000000 : ℝ) < research9ProjectedBound := by
  norm_num [research9ProjectedBound]

end HurtadoZeta23
