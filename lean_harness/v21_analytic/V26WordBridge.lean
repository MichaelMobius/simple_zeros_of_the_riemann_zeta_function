import HurtadoZeta23.V21GapFunctional
import HurtadoZeta23.V26Word511Certificate
import Mathlib.Tactic

noncomputable section

namespace HurtadoZeta23

/-- The six position-dependent one-body terms retained from the full v26
six-gap functional. -/
def v26OneBodySum (g0 g1 g2 g3 g4 g5 : ℝ) : ℝ :=
  pressure 0 * g0 + (1 / 3 : ℝ) * limitingWeight g0 +
  pressure 1 * g1 + (1 / 3 : ℝ) * limitingWeight g1 +
  pressure 2 * g2 + (1 / 3 : ℝ) * limitingWeight g2 +
  pressure 3 * g3 + (1 / 3 : ℝ) * limitingWeight g3 +
  pressure 4 * g4 + (1 / 3 : ℝ) * limitingWeight g4 +
  pressure 5 * g5 + (1 / 3 : ℝ) * limitingWeight g5

/-- Dropping every block term of length at least two can only decrease the
full six-gap functional. -/
theorem v26_oneBodySum_le_gapF (g0 g1 g2 g3 g4 g5 : ℝ) :
    v26OneBodySum g0 g1 g2 g3 g4 g5 ≤
      v21GapF g0 g1 g2 g3 g4 g5 := by
  have h01 := limitingWeight_nonneg (g0 + g1)
  have h12 := limitingWeight_nonneg (g1 + g2)
  have h23 := limitingWeight_nonneg (g2 + g3)
  have h34 := limitingWeight_nonneg (g3 + g4)
  have h45 := limitingWeight_nonneg (g4 + g5)
  have h012 := limitingWeight_nonneg (g0 + g1 + g2)
  have h123 := limitingWeight_nonneg (g1 + g2 + g3)
  have h234 := limitingWeight_nonneg (g2 + g3 + g4)
  have h345 := limitingWeight_nonneg (g3 + g4 + g5)
  have h0123 := limitingWeight_nonneg (g0 + g1 + g2 + g3)
  have h1234 := limitingWeight_nonneg (g1 + g2 + g3 + g4)
  have h2345 := limitingWeight_nonneg (g2 + g3 + g4 + g5)
  have h01234 := limitingWeight_nonneg (g0 + g1 + g2 + g3 + g4)
  have h12345 := limitingWeight_nonneg (g1 + g2 + g3 + g4 + g5)
  have h012345 := limitingWeight_nonneg (g0 + g1 + g2 + g3 + g4 + g5)
  unfold v26OneBodySum v21GapF
  nlinarith

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

/-- Abstract bridge from the six certified basin floors to the exact finite
511-word set.  The analytic localization layer only has to provide the six
floor hypotheses below; all subsequent arithmetic is kernel-checked here. -/
theorem v26_word_survives_of_floors
    (w : V26BasinWord)
    (g0 g1 g2 g3 g4 g5 : ℝ)
    (h0 : (v26MuA w.1 : ℝ) / 1000000 ≤
      pressure 0 * g0 + (1 / 3 : ℝ) * limitingWeight g0)
    (h1 : (v26MuB w.2.1 : ℝ) / 1000000 ≤
      pressure 1 * g1 + (1 / 3 : ℝ) * limitingWeight g1)
    (h2 : (v26MuC w.2.2.1 : ℝ) / 1000000 ≤
      pressure 2 * g2 + (1 / 3 : ℝ) * limitingWeight g2)
    (h3 : (v26MuC w.2.2.2.1 : ℝ) / 1000000 ≤
      pressure 3 * g3 + (1 / 3 : ℝ) * limitingWeight g3)
    (h4 : (v26MuB w.2.2.2.2.1 : ℝ) / 1000000 ≤
      pressure 4 * g4 + (1 / 3 : ℝ) * limitingWeight g4)
    (h5 : (v26MuA w.2.2.2.2.2 : ℝ) / 1000000 ≤
      pressure 5 * g5 + (1 / 3 : ℝ) * limitingWeight g5)
    (hbad : v21GapF g0 g1 g2 g3 g4 g5 < delta) :
    v26WordSurvives w := by
  unfold v26WordSurvives
  by_contra hnot
  have hn : 3900 ≤ v26WordWeight w := Nat.le_of_not_gt hnot
  have hnR : (3900 : ℝ) ≤ (v26WordWeight w : ℝ) := by
    exact_mod_cast hn
  have hfloor :
      (v26WordWeight w : ℝ) / 1000000 ≤
        v26OneBodySum g0 g1 g2 g3 g4 g5 := by
    rw [v26_wordWeight_cast]
    unfold v26OneBodySum
    nlinarith
  have hfull := v26_oneBodySum_le_gapF g0 g1 g2 g3 g4 g5
  have hdelta : delta ≤ (v26WordWeight w : ℝ) / 1000000 := by
    norm_num [delta] at ⊢
    nlinarith
  linarith

/-- Equivalent finite-set form of the bridge. -/
theorem v26_word_mem_511_of_floors
    (w : V26BasinWord)
    (g0 g1 g2 g3 g4 g5 : ℝ)
    (h0 : (v26MuA w.1 : ℝ) / 1000000 ≤
      pressure 0 * g0 + (1 / 3 : ℝ) * limitingWeight g0)
    (h1 : (v26MuB w.2.1 : ℝ) / 1000000 ≤
      pressure 1 * g1 + (1 / 3 : ℝ) * limitingWeight g1)
    (h2 : (v26MuC w.2.2.1 : ℝ) / 1000000 ≤
      pressure 2 * g2 + (1 / 3 : ℝ) * limitingWeight g2)
    (h3 : (v26MuC w.2.2.2.1 : ℝ) / 1000000 ≤
      pressure 3 * g3 + (1 / 3 : ℝ) * limitingWeight g3)
    (h4 : (v26MuB w.2.2.2.2.1 : ℝ) / 1000000 ≤
      pressure 4 * g4 + (1 / 3 : ℝ) * limitingWeight g4)
    (h5 : (v26MuA w.2.2.2.2.2 : ℝ) / 1000000 ≤
      pressure 5 * g5 + (1 / 3 : ℝ) * limitingWeight g5)
    (hbad : v21GapF g0 g1 g2 g3 g4 g5 < delta) :
    w ∈ v26SurvivorWords := by
  rw [v26_mem_survivorWords_iff]
  exact v26_word_survives_of_floors w g0 g1 g2 g3 g4 g5
    h0 h1 h2 h3 h4 h5 hbad

end HurtadoZeta23
