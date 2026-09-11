import HurtadoZeta23.V21SevenPointAnalytic
import Mathlib.Tactic

noncomputable section

namespace HurtadoZeta23

/-- The seven-point functional written directly in the six consecutive gaps.
This removes the irrelevant translation parameter and the ambient sequence
from the remaining compact optimization problem. -/
def v21GapF (g0 g1 g2 g3 g4 g5 : ℝ) : ℝ :=
  pressure 0 * g0 +
  pressure 1 * g1 +
  pressure 2 * g2 +
  pressure 3 * g3 +
  pressure 4 * g4 +
  pressure 5 * g5 +
  (1/3 : ℝ) * (
    limitingWeight g0 +
    limitingWeight g1 +
    limitingWeight g2 +
    limitingWeight g3 +
    limitingWeight g4 +
    limitingWeight g5) +
  (2/5 : ℝ) * (
    limitingWeight (g0 + g1) +
    limitingWeight (g1 + g2) +
    limitingWeight (g2 + g3) +
    limitingWeight (g3 + g4) +
    limitingWeight (g4 + g5)) +
  (1/2 : ℝ) * (
    limitingWeight (g0 + g1 + g2) +
    limitingWeight (g1 + g2 + g3) +
    limitingWeight (g2 + g3 + g4) +
    limitingWeight (g3 + g4 + g5)) +
  (2/3 : ℝ) * (
    limitingWeight (g0 + g1 + g2 + g3) +
    limitingWeight (g1 + g2 + g3 + g4) +
    limitingWeight (g2 + g3 + g4 + g5)) +
  limitingWeight (g0 + g1 + g2 + g3 + g4) +
  limitingWeight (g1 + g2 + g3 + g4 + g5) +
  2 * limitingWeight (g0 + g1 + g2 + g3 + g4 + g5)

/-- Substituting the six consecutive gaps into `v21GapF` reproduces the exact
historical local functional.  The proof records each telescope explicitly so
Lean never has to normalize the entire 21-weight expression at once. -/
theorem v21_localFp_eq_gapF (y : ℕ → ℝ) (s : ℕ) :
    localFp (limitingWeightOnPoints y) y s =
      v21GapF
        (y (s+1) - y s)
        (y (s+2) - y (s+1))
        (y (s+3) - y (s+2))
        (y (s+4) - y (s+3))
        (y (s+5) - y (s+4))
        (y (s+6) - y (s+5)) := by
  have h02 :
      y (s+2) - y s =
        (y (s+1) - y s) + (y (s+2) - y (s+1)) := by ring
  have h13 :
      y (s+3) - y (s+1) =
        (y (s+2) - y (s+1)) + (y (s+3) - y (s+2)) := by ring
  have h24 :
      y (s+4) - y (s+2) =
        (y (s+3) - y (s+2)) + (y (s+4) - y (s+3)) := by ring
  have h35 :
      y (s+5) - y (s+3) =
        (y (s+4) - y (s+3)) + (y (s+5) - y (s+4)) := by ring
  have h46 :
      y (s+6) - y (s+4) =
        (y (s+5) - y (s+4)) + (y (s+6) - y (s+5)) := by ring
  have h03 :
      y (s+3) - y s =
        (y (s+1) - y s) + (y (s+2) - y (s+1)) +
          (y (s+3) - y (s+2)) := by ring
  have h14 :
      y (s+4) - y (s+1) =
        (y (s+2) - y (s+1)) + (y (s+3) - y (s+2)) +
          (y (s+4) - y (s+3)) := by ring
  have h25 :
      y (s+5) - y (s+2) =
        (y (s+3) - y (s+2)) + (y (s+4) - y (s+3)) +
          (y (s+5) - y (s+4)) := by ring
  have h36 :
      y (s+6) - y (s+3) =
        (y (s+4) - y (s+3)) + (y (s+5) - y (s+4)) +
          (y (s+6) - y (s+5)) := by ring
  have h04 :
      y (s+4) - y s =
        (y (s+1) - y s) + (y (s+2) - y (s+1)) +
          (y (s+3) - y (s+2)) + (y (s+4) - y (s+3)) := by ring
  have h15 :
      y (s+5) - y (s+1) =
        (y (s+2) - y (s+1)) + (y (s+3) - y (s+2)) +
          (y (s+4) - y (s+3)) + (y (s+5) - y (s+4)) := by ring
  have h26 :
      y (s+6) - y (s+2) =
        (y (s+3) - y (s+2)) + (y (s+4) - y (s+3)) +
          (y (s+5) - y (s+4)) + (y (s+6) - y (s+5)) := by ring
  have h05 :
      y (s+5) - y s =
        (y (s+1) - y s) + (y (s+2) - y (s+1)) +
          (y (s+3) - y (s+2)) + (y (s+4) - y (s+3)) +
          (y (s+5) - y (s+4)) := by ring
  have h16 :
      y (s+6) - y (s+1) =
        (y (s+2) - y (s+1)) + (y (s+3) - y (s+2)) +
          (y (s+4) - y (s+3)) + (y (s+5) - y (s+4)) +
          (y (s+6) - y (s+5)) := by ring
  have h06 :
      y (s+6) - y s =
        (y (s+1) - y s) + (y (s+2) - y (s+1)) +
          (y (s+3) - y (s+2)) + (y (s+4) - y (s+3)) +
          (y (s+5) - y (s+4)) + (y (s+6) - y (s+5)) := by ring
  rw [v21_localFp_eq_explicit]
  unfold v21ExplicitF v21GapF
  rw [h02, h13, h24, h35, h46,
      h03, h14, h25, h36,
      h04, h15, h26,
      h05, h16, h06]

/-- The compact numerical core in its minimal six-variable form.  The lower
bounds `0.89 < gj` already imply nonnegativity, so no separate sign hypotheses
are required here. -/
def V21GapHardCoreClaim : Prop :=
  ∀ g0 g1 g2 g3 g4 g5 : ℝ,
    v17KernelCertPoint < g0 →
    v17KernelCertPoint < g1 →
    v17KernelCertPoint < g2 →
    v17KernelCertPoint < g3 →
    v17KernelCertPoint < g4 →
    v17KernelCertPoint < g5 →
    g0 + g1 + g2 + g3 + g4 + g5 < (1437 / 100 : ℝ) →
      delta ≤ v21GapF g0 g1 g2 g3 g4 g5

/-- The six-variable compact claim is exactly strong enough for the sequence
form used by the article. -/
theorem v21_hard_core_of_gap_hard_core
    (hgapcore : V21GapHardCoreClaim) :
    V21HardCoreClaim := by
  intro y s hnonneg hlarge hspan
  have h0 : v17KernelCertPoint < y (s+1) - y s := by
    simpa [windowGap] using hlarge (0 : Fin 6)
  have h1 : v17KernelCertPoint < y (s+2) - y (s+1) := by
    simpa [windowGap] using hlarge (1 : Fin 6)
  have h2 : v17KernelCertPoint < y (s+3) - y (s+2) := by
    simpa [windowGap] using hlarge (2 : Fin 6)
  have h3 : v17KernelCertPoint < y (s+4) - y (s+3) := by
    simpa [windowGap] using hlarge (3 : Fin 6)
  have h4 : v17KernelCertPoint < y (s+5) - y (s+4) := by
    simpa [windowGap] using hlarge (4 : Fin 6)
  have h5 : v17KernelCertPoint < y (s+6) - y (s+5) := by
    simpa [windowGap] using hlarge (5 : Fin 6)
  have hsum :
      (y (s+1) - y s) +
      (y (s+2) - y (s+1)) +
      (y (s+3) - y (s+2)) +
      (y (s+4) - y (s+3)) +
      (y (s+5) - y (s+4)) +
      (y (s+6) - y (s+5)) < (1437 / 100 : ℝ) := by
    linarith
  have h := hgapcore
    (y (s+1) - y s)
    (y (s+2) - y (s+1))
    (y (s+3) - y (s+2))
    (y (s+4) - y (s+3))
    (y (s+5) - y (s+4))
    (y (s+6) - y (s+5))
    h0 h1 h2 h3 h4 h5 hsum
  rw [v21_localFp_eq_gapF]
  exact h

/-- Final reduction of the external seven-point frontier to one internally
stated compact six-variable inequality plus the already internal v20 kernel
point theorem. -/
theorem v21_article_of_gap_hard_core
    (hsigned : V17KernelSignedCertPointClaim)
    (hgapcore : V21GapHardCoreClaim) :
    ArticleSevenPointInequality := by
  exact v21_article_of_hard_core hsigned
    (v21_hard_core_of_gap_hard_core hgapcore)

end HurtadoZeta23