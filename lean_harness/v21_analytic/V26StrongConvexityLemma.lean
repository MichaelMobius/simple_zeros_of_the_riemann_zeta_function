import HurtadoZeta23.V26FinalConvexityCore
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic

noncomputable section

open Set

namespace HurtadoZeta23

/-- A generic one-dimensional strong-convexity lower Taylor bound.  The
statement is independent of the kernel and isolates all calculus plumbing
needed by the final ten certified cells. -/
theorem v26_strong_convex_taylor_lower
    {f fp fpp : ℝ → ℝ} {L U a x m : ℝ}
    (ha : a ∈ Icc L U) (hx : x ∈ Icc L U)
    (hf : ∀ y ∈ Icc L U, HasDerivAt f (fp y) y)
    (hfp : ∀ y ∈ Icc L U, HasDerivAt fp (fpp y) y)
    (hm : ∀ y ∈ Icc L U, m ≤ fpp y) :
    f a + fp a * (x - a) + (m / 2) * (x - a) ^ 2 ≤ f x := by
  let g : ℝ → ℝ := fun y => f y - (m / 2) * (y - a) ^ 2
  let gp : ℝ → ℝ := fun y => fp y - m * (y - a)
  let gpp : ℝ → ℝ := fun y => fpp y - m

  have hg : ∀ y ∈ Icc L U, HasDerivAt g (gp y) y := by
    intro y hy
    have hbase := ((hasDerivAt_id y).sub_const a).pow 2
    have hquad := (hbase.const_mul (m / 2)).congr_deriv
      (g' := m * (y - a)) (by
        norm_num
        ring)
    have hraw := (hf y hy).sub hquad
    convert hraw using 1
    · funext z
      simp [g]
    · simp [gp]

  have hgp : ∀ y ∈ Icc L U, HasDerivAt gp (gpp y) y := by
    intro y hy
    have hlin := (((hasDerivAt_id y).sub_const a).const_mul m).congr_deriv
      (g' := m) (by simp)
    have hraw := (hfp y hy).sub hlin
    convert hraw using 1
    · funext z
      simp [gp]
    · simp [gpp]

  have hcont : ContinuousOn g (Icc L U) := by
    intro y hy
    exact (hg y hy).continuousAt.continuousWithinAt

  have hconv : ConvexOn ℝ (Icc L U) g := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc L U) hcont
        (f' := gp) (f'' := gpp)
    · intro y hy
      exact (hg y (interior_subset hy)).hasDerivWithinAt
    · intro y hy
      exact (hgp y (interior_subset hy)).hasDerivWithinAt
    · intro y hy
      dsimp [gpp]
      exact sub_nonneg.mpr (hm y (interior_subset hy))

  have hga : HasDerivAt g (fp a) a := by
    have h := hg a ha
    apply h.congr_deriv
    dsimp [gp]
    ring

  rcases lt_trichotomy a x with hax | hax | hxa
  · have hs := hconv.le_slope_of_hasDerivAt ha hx hax hga
    rw [slope_def_field] at hs
    have hmul := (le_div_iff₀ (sub_pos.mpr hax)).mp hs
    dsimp [g] at hmul
    nlinarith
  · subst x
    simp
  · have hs := hconv.slope_le_of_hasDerivAt hx ha hxa hga
    rw [slope_def_field] at hs
    have hmul := (div_le_iff₀ (sub_pos.mpr hxa)).mp hs
    dsimp [g] at hmul
    nlinarith

end HurtadoZeta23
