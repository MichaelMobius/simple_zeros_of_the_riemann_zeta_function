import Mathlib.Tactic

namespace HurtadoZeta23

/-- The six basin indices in the positional A-B-C-C-B-A pattern. -/
abbrev V26BasinWord :=
  Fin 7 × Fin 5 × Fin 6 × Fin 6 × Fin 5 × Fin 7

/-- Exact one-body micro-floors for the seven A basins. -/
def v26MuA : Fin 7 → Nat := ![286, 550, 817, 1085, 1353, 1622, 1890]

/-- Exact one-body micro-floors for the five B basins. -/
def v26MuB : Fin 5 → Nat := ![394, 756, 1123, 1490, 1859]

/-- Exact one-body micro-floors for the six C basins. -/
def v26MuC : Fin 6 → Nat := ![375, 720, 1069, 1419, 1770, 2122]

/-- Integer micro-energy attached to a basin word. -/
def v26WordWeight (w : V26BasinWord) : Nat :=
  v26MuA w.1 +
  v26MuB w.2.1 +
  v26MuC w.2.2.1 +
  v26MuC w.2.2.2.1 +
  v26MuB w.2.2.2.2.1 +
  v26MuA w.2.2.2.2.2

/-- A word survives the one-body test precisely when its micro-energy is
strictly below `3900`, i.e. below `delta = 39/10000` in units of `10^-6`. -/
def v26WordSurvives (w : V26BasinWord) : Prop :=
  v26WordWeight w < 3900

/-- The finite set of exact survivors of the one-body test.  The predicate is
written inline so its ordinary decidability is synthesized directly from
natural-number comparison. -/
def v26SurvivorWords : Finset V26BasinWord :=
  Finset.univ.filter (fun w => v26WordWeight w < 3900)

/-- The raw A-B-C-C-B-A word space contains exactly 44,100 words. -/
theorem v26_basin_word_count : Fintype.card V26BasinWord = 44100 := by
  norm_num [V26BasinWord, Fintype.card_prod]

/-- Exact kernel-checked combinatorial certificate for the first reduction:
`44,100 -> 511`.  This theorem is intentionally stated only in terms of the
published integer micro-floors, so it has no transcendental or interval
arithmetic trust boundary. -/
theorem v26_survivor_word_count : v26SurvivorWords.card = 511 := by
  set_option maxHeartbeats 0 in
  set_option maxRecDepth 100000 in
  decide

/-- Membership in the certified finite survivor set is definitionally the
strict micro-energy inequality. -/
theorem v26_mem_survivorWords_iff (w : V26BasinWord) :
    w ∈ v26SurvivorWords ↔ v26WordWeight w < 3900 := by
  simp [v26SurvivorWords]

end HurtadoZeta23
