import HurtadoZeta23.V26Word511Certificate
import Mathlib.Tactic

noncomputable section

namespace HurtadoZeta23

/-- Exact positional pressure vector used by the v26 local functional.  It is
kept in the lightweight finite layer so the rational certificates do not
import the global zeta development. -/
def v26Pressure : Fin 6 → ℝ := ![
  2714 / 10000000,
  3733 / 10000000,
  3553 / 10000000,
  3553 / 10000000,
  3733 / 10000000,
  2714 / 10000000]

/-- Exact local target. -/
def v26Delta : ℝ := 39 / 10000

/-- Six-gap functional, parameterized by an arbitrary nonnegative kernel
weight.  Specialization to the article's `limitingWeight` is postponed to a
single integration module. -/
def v26GapF (weight : ℝ → ℝ)
    (g0 g1 g2 g3 g4 g5 : ℝ) : ℝ :=
  v26Pressure 0 * g0 +
  v26Pressure 1 * g1 +
  v26Pressure 2 * g2 +
  v26Pressure 3 * g3 +
  v26Pressure 4 * g4 +
  v26Pressure 5 * g5 +
  (1/3 : ℝ) * (
    weight g0 + weight g1 + weight g2 +
    weight g3 + weight g4 + weight g5) +
  (2/5 : ℝ) * (
    weight (g0 + g1) + weight (g1 + g2) + weight (g2 + g3) +
    weight (g3 + g4) + weight (g4 + g5)) +
  (1/2 : ℝ) * (
    weight (g0 + g1 + g2) + weight (g1 + g2 + g3) +
    weight (g2 + g3 + g4) + weight (g3 + g4 + g5)) +
  (2/3 : ℝ) * (
    weight (g0 + g1 + g2 + g3) +
    weight (g1 + g2 + g3 + g4) +
    weight (g2 + g3 + g4 + g5)) +
  weight (g0 + g1 + g2 + g3 + g4) +
  weight (g1 + g2 + g3 + g4 + g5) +
  2 * weight (g0 + g1 + g2 + g3 + g4 + g5)

/-- The six position-dependent one-body terms retained from the full local
functional. -/
def v26OneBodySum (weight : ℝ → ℝ)
    (g0 g1 g2 g3 g4 g5 : ℝ) : ℝ :=
  v26Pressure 0 * g0 + (1 / 3 : ℝ) * weight g0 +
  v26Pressure 1 * g1 + (1 / 3 : ℝ) * weight g1 +
  v26Pressure 2 * g2 + (1 / 3 : ℝ) * weight g2 +
  v26Pressure 3 * g3 + (1 / 3 : ℝ) * weight g3 +
  v26Pressure 4 * g4 + (1 / 3 : ℝ) * weight g4 +
  v26Pressure 5 * g5 + (1 / 3 : ℝ) * weight g5

/-- Dropping every block term of length at least two can only decrease the
functional when the kernel weight is nonnegative. -/
theorem v26_oneBodySum_le_gapF
    (weight : ℝ → ℝ) (hweight : ∀ x, 0 ≤ weight x)
    (g0 g1 g2 g3 g4 g5 : ℝ) :
    v26OneBodySum weight g0 g1 g2 g3 g4 g5 ≤
      v26GapF weight g0 g1 g2 g3 g4 g5 := by
  have h01 := hweight (g0 + g1)
  have h12 := hweight (g1 + g2)
  have h23 := hweight (g2 + g3)
  have h34 := hweight (g3 + g4)
  have h45 := hweight (g4 + g5)
  have h012 := hweight (g0 + g1 + g2)
  have h123 := hweight (g1 + g2 + g3)
  have h234 := hweight (g2 + g3 + g4)
  have h345 := hweight (g3 + g4 + g5)
  have h0123 := hweight (g0 + g1 + g2 + g3)
  have h1234 := hweight (g1 + g2 + g3 + g4)
  have h2345 := hweight (g2 + g3 + g4 + g5)
  have h01234 := hweight (g0 + g1 + g2 + g3 + g4)
  have h12345 := hweight (g1 + g2 + g3 + g4 + g5)
  have h012345 := hweight (g0 + g1 + g2 + g3 + g4 + g5)
  unfold v26OneBodySum v26GapF
  linarith

/-- The integer word weight, interpreted in units of `10^-6`, is exactly the
sum of the six published micro-floors. -/
theorem v26_wordWeight_cast (w : V26BasinWord) :
    (v26WordWeight w : ℝ) / 1000000 =
      (v26MuA w.1 : ℝ) / 1000000 +
      (v26MuB w.2.1 : ℝ) / 1000000 +
      (v26MuC w.2.2.1 : ℝ) / 1000000 +
      (v26MuC w.2.2.2.1 : ℝ) / 1000000 +
      (v26MuB w.2.2.2.2.1 : ℝ) / 1000000 +
      (v26MuA w.2.2.2.2.2 : ℝ) / 1000000 := by
  simp [v26WordWeight]
  ring

/-- Abstract bridge from six certified basin floors to the exact finite
511-word set.  The analytic layer only has to provide nonnegativity of the
weight and the six floor hypotheses. -/
theorem v26_word_survives_of_floors
    (weight : ℝ → ℝ) (hweight : ∀ x, 0 ≤ weight x)
    (w : V26BasinWord)
    (g0 g1 g2 g3 g4 g5 : ℝ)
    (h0 : (v26MuA w.1 : ℝ) / 1000000 ≤
      v26Pressure 0 * g0 + (1 / 3 : ℝ) * weight g0)
    (h1 : (v26MuB w.2.1 : ℝ) / 1000000 ≤
      v26Pressure 1 * g1 + (1 / 3 : ℝ) * weight g1)
    (h2 : (v26MuC w.2.2.1 : ℝ) / 1000000 ≤
      v26Pressure 2 * g2 + (1 / 3 : ℝ) * weight g2)
    (h3 : (v26MuC w.2.2.2.1 : ℝ) / 1000000 ≤
      v26Pressure 3 * g3 + (1 / 3 : ℝ) * weight g3)
    (h4 : (v26MuB w.2.2.2.2.1 : ℝ) / 1000000 ≤
      v26Pressure 4 * g4 + (1 / 3 : ℝ) * weight g4)
    (h5 : (v26MuA w.2.2.2.2.2 : ℝ) / 1000000 ≤
      v26Pressure 5 * g5 + (1 / 3 : ℝ) * weight g5)
    (hbad : v26GapF weight g0 g1 g2 g3 g4 g5 < v26Delta) :
    v26WordSurvives w := by
  unfold v26WordSurvives
  by_contra hnot
  have hn : 3900 ≤ v26WordWeight w := Nat.le_of_not_gt hnot
  have hnR : (3900 : ℝ) ≤ (v26WordWeight w : ℝ) := by
    exact_mod_cast hn
  have hfloor :
      (v26WordWeight w : ℝ) / 1000000 ≤
        v26OneBodySum weight g0 g1 g2 g3 g4 g5 := by
    rw [v26_wordWeight_cast]
    unfold v26OneBodySum
    linarith
  have hfull := v26_oneBodySum_le_gapF weight hweight g0 g1 g2 g3 g4 g5
  have hdelta : v26Delta ≤ (v26WordWeight w : ℝ) / 1000000 := by
    unfold v26Delta
    norm_num at ⊢
    linarith
  linarith

/-- Equivalent finite-set form of the bridge. -/
theorem v26_word_mem_511_of_floors
    (weight : ℝ → ℝ) (hweight : ∀ x, 0 ≤ weight x)
    (w : V26BasinWord)
    (g0 g1 g2 g3 g4 g5 : ℝ)
    (h0 : (v26MuA w.1 : ℝ) / 1000000 ≤
      v26Pressure 0 * g0 + (1 / 3 : ℝ) * weight g0)
    (h1 : (v26MuB w.2.1 : ℝ) / 1000000 ≤
      v26Pressure 1 * g1 + (1 / 3 : ℝ) * weight g1)
    (h2 : (v26MuC w.2.2.1 : ℝ) / 1000000 ≤
      v26Pressure 2 * g2 + (1 / 3 : ℝ) * weight g2)
    (h3 : (v26MuC w.2.2.2.1 : ℝ) / 1000000 ≤
      v26Pressure 3 * g3 + (1 / 3 : ℝ) * weight g3)
    (h4 : (v26MuB w.2.2.2.2.1 : ℝ) / 1000000 ≤
      v26Pressure 4 * g4 + (1 / 3 : ℝ) * weight g4)
    (h5 : (v26MuA w.2.2.2.2.2 : ℝ) / 1000000 ≤
      v26Pressure 5 * g5 + (1 / 3 : ℝ) * weight g5)
    (hbad : v26GapF weight g0 g1 g2 g3 g4 g5 < v26Delta) :
    w ∈ v26SurvivorWords := by
  rw [v26_mem_survivorWords_iff]
  exact v26_word_survives_of_floors weight hweight w g0 g1 g2 g3 g4 g5
    h0 h1 h2 h3 h4 h5 hbad

end HurtadoZeta23
