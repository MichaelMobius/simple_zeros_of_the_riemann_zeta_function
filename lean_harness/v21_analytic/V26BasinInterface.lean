import HurtadoZeta23.V26WordBridge
import Mathlib.Tactic

noncomputable section

namespace HurtadoZeta23

/-- Rational endpoints of the seven A basins, used at positions 0 and 5. -/
def v26ALo : Fin 7 → ℝ := ![
  955/1000, 1792/1000, 2612/1000, 3502/1000,
  4500/1000, 5500/1000, 6576/1000]

def v26AHi : Fin 7 → ℝ := ![
  1158/1000, 2258/1000, 3396/1000, 4465/1000,
  5466/1000, 6413/1000, 7270/1000]

/-- Rational endpoints of the five B basins, used at positions 1 and 4. -/
def v26BLo : Fin 5 → ℝ := ![
  955/1000, 1798/1000, 2637/1000, 3568/1000, 4611/1000]

def v26BHi : Fin 5 → ℝ := ![
  1158/1000, 2249/1000, 3358/1000, 4375/1000, 5285/1000]

/-- Rational endpoints of the six C basins, used at positions 2 and 3. -/
def v26CLo : Fin 6 → ℝ := ![
  955/1000, 1797/1000, 2633/1000, 3556/1000, 4580/1000, 5793/1000]

def v26CHi : Fin 6 → ℝ := ![
  1158/1000, 2251/1000, 3365/1000, 4392/1000, 5322/1000, 6078/1000]

def v26InA (i : Fin 7) (x : ℝ) : Prop := v26ALo i ≤ x ∧ x ≤ v26AHi i
def v26InB (i : Fin 5) (x : ℝ) : Prop := v26BLo i ≤ x ∧ x ≤ v26BHi i
def v26InC (i : Fin 6) (x : ℝ) : Prop := v26CLo i ≤ x ∧ x ≤ v26CHi i

/-- Exact A-B-C-C-B-A basin box associated with one finite word. -/
def v26InWordBox (w : V26BasinWord)
    (g0 g1 g2 g3 g4 g5 : ℝ) : Prop :=
  v26InA w.1 g0 ∧
  v26InB w.2.1 g1 ∧
  v26InC w.2.2.1 g2 ∧
  v26InC w.2.2.2.1 g3 ∧
  v26InB w.2.2.2.2.1 g4 ∧
  v26InA w.2.2.2.2.2 g5

/-- Hard-core point written locally to keep the finite layer independent of
historical wrapper modules. -/
def v26HardCorePoint : ℝ := 89 / 100

/-- Analytic localization obligation remaining for a nonnegative kernel
weight: every strict hard-core counterexample belongs to one of the exact
A-B-C-C-B-A boxes.  This is a target proposition, not a trusted statement. -/
def V26BasinLocalizationClaim (weight : ℝ → ℝ) : Prop :=
  ∀ g0 g1 g2 g3 g4 g5 : ℝ,
    v26HardCorePoint < g0 →
    v26HardCorePoint < g1 →
    v26HardCorePoint < g2 →
    v26HardCorePoint < g3 →
    v26HardCorePoint < g4 →
    v26HardCorePoint < g5 →
    g0 + g1 + g2 + g3 + g4 + g5 < (1437 / 100 : ℝ) →
    v26GapF weight g0 g1 g2 g3 g4 g5 < v26Delta →
    ∃ w : V26BasinWord, v26InWordBox w g0 g1 g2 g3 g4 g5

/-- Analytic micro-floor obligation for the exact basin table. -/
def V26BasinMicroFloorClaim (weight : ℝ → ℝ) : Prop :=
  (∀ (i : Fin 7) (x : ℝ), v26InA i x →
    (v26MuA i : ℝ) / 1000000 ≤
      v26Pressure 0 * x + (1 / 3 : ℝ) * weight x) ∧
  (∀ (i : Fin 5) (x : ℝ), v26InB i x →
    (v26MuB i : ℝ) / 1000000 ≤
      v26Pressure 1 * x + (1 / 3 : ℝ) * weight x) ∧
  (∀ (i : Fin 6) (x : ℝ), v26InC i x →
    (v26MuC i : ℝ) / 1000000 ≤
      v26Pressure 2 * x + (1 / 3 : ℝ) * weight x)

/-- Symmetry of the exact pressure vector. -/
theorem v26_pressure_symmetry :
    v26Pressure (5 : Fin 6) = v26Pressure (0 : Fin 6) ∧
    v26Pressure (4 : Fin 6) = v26Pressure (1 : Fin 6) ∧
    v26Pressure (3 : Fin 6) = v26Pressure (2 : Fin 6) := by
  norm_num [v26Pressure]

/-- Once localization and the basin micro-floors are established analytically,
a strict counterexample must belong to the exact 511-word survivor set. -/
theorem v26_counterexample_mem_511
    (weight : ℝ → ℝ) (hweight : ∀ x, 0 ≤ weight x)
    (hloc : V26BasinLocalizationClaim weight)
    (hfloor : V26BasinMicroFloorClaim weight)
    (g0 g1 g2 g3 g4 g5 : ℝ)
    (h0 : v26HardCorePoint < g0)
    (h1 : v26HardCorePoint < g1)
    (h2 : v26HardCorePoint < g2)
    (h3 : v26HardCorePoint < g3)
    (h4 : v26HardCorePoint < g4)
    (h5 : v26HardCorePoint < g5)
    (hsum : g0 + g1 + g2 + g3 + g4 + g5 < (1437 / 100 : ℝ))
    (hbad : v26GapF weight g0 g1 g2 g3 g4 g5 < v26Delta) :
    ∃ w : V26BasinWord, w ∈ v26SurvivorWords ∧
      v26InWordBox w g0 g1 g2 g3 g4 g5 := by
  rcases hloc g0 g1 g2 g3 g4 g5 h0 h1 h2 h3 h4 h5 hsum hbad with ⟨w, hw⟩
  rcases hfloor with ⟨hA, hB, hC⟩
  rcases hw with ⟨hw0, hw1, hw2, hw3, hw4, hw5⟩
  have hp := v26_pressure_symmetry
  have hf0 := hA w.1 g0 hw0
  have hf1 := hB w.2.1 g1 hw1
  have hf2 := hC w.2.2.1 g2 hw2
  have hf3base := hC w.2.2.2.1 g3 hw3
  have hf4base := hB w.2.2.2.2.1 g4 hw4
  have hf5base := hA w.2.2.2.2.2 g5 hw5
  have hf3 : (v26MuC w.2.2.2.1 : ℝ) / 1000000 ≤
      v26Pressure 3 * g3 + (1 / 3 : ℝ) * weight g3 := by
    rw [hp.2.2]
    exact hf3base
  have hf4 : (v26MuB w.2.2.2.2.1 : ℝ) / 1000000 ≤
      v26Pressure 4 * g4 + (1 / 3 : ℝ) * weight g4 := by
    rw [hp.2.1]
    exact hf4base
  have hf5 : (v26MuA w.2.2.2.2.2 : ℝ) / 1000000 ≤
      v26Pressure 5 * g5 + (1 / 3 : ℝ) * weight g5 := by
    rw [hp.1]
    exact hf5base
  have hmem := v26_word_mem_511_of_floors weight hweight w g0 g1 g2 g3 g4 g5
    hf0 hf1 hf2 hf3 hf4 hf5 hbad
  exact ⟨w, hmem, hw0, hw1, hw2, hw3, hw4, hw5⟩

end HurtadoZeta23
