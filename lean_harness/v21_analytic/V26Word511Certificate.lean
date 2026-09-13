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

/-! The exact enumeration is built from right to left and pruned after every
coordinate.  All micro-floors are nonnegative, so a suffix whose weight is
already at least `3900` can never extend to a surviving full word.  This is
the same elementary dynamic-programming reduction used by the independent
rational verifier, but here every stage is an ordinary kernel-reducible
`Finset`. -/

def v26SuffixA : Finset (Fin 7) :=
  Finset.univ.filter (fun f => v26MuA f < 3900)

def v26SuffixBA : Finset (Fin 5 × Fin 7) :=
  (Finset.univ.product v26SuffixA).filter
    (fun ef => v26MuB ef.1 + v26MuA ef.2 < 3900)

def v26SuffixCBA : Finset (Fin 6 × (Fin 5 × Fin 7)) :=
  (Finset.univ.product v26SuffixBA).filter
    (fun def => v26MuC def.1 + v26MuB def.2.1 + v26MuA def.2.2 < 3900)

def v26SuffixCCBA : Finset (Fin 6 × (Fin 6 × (Fin 5 × Fin 7))) :=
  (Finset.univ.product v26SuffixCBA).filter
    (fun cdef =>
      v26MuC cdef.1 + v26MuC cdef.2.1 +
      v26MuB cdef.2.2.1 + v26MuA cdef.2.2.2 < 3900)

def v26SuffixBCCBA : Finset (Fin 5 × (Fin 6 × (Fin 6 × (Fin 5 × Fin 7)))) :=
  (Finset.univ.product v26SuffixCCBA).filter
    (fun bcdef =>
      v26MuB bcdef.1 + v26MuC bcdef.2.1 + v26MuC bcdef.2.2.1 +
      v26MuB bcdef.2.2.2.1 + v26MuA bcdef.2.2.2.2 < 3900)

/-- Exact finite set of one-body survivors.  Its type is definitionally the
A-B-C-C-B-A word type. -/
def v26SurvivorWords : Finset V26BasinWord :=
  (Finset.univ.product v26SuffixBCCBA).filter
    (fun abcdef => v26WordWeight abcdef < 3900)

/-- The raw A-B-C-C-B-A word space contains exactly 44,100 words. -/
theorem v26_basin_word_count : Fintype.card V26BasinWord = 44100 := by
  norm_num [V26BasinWord, Fintype.card_prod]

/-- Exact kernel-checked combinatorial certificate for the first reduction:
`44,100 -> 511`.  The staged pruning keeps the definitional computation small
and does not change the survivor predicate. -/
theorem v26_survivor_word_count : v26SurvivorWords.card = 511 := by
  set_option maxHeartbeats 0 in
  set_option maxRecDepth 100000 in
  decide

/-- Membership in the pruned enumeration is exactly the published strict
micro-energy inequality. -/
theorem v26_mem_survivorWords_iff (w : V26BasinWord) :
    w ∈ v26SurvivorWords ↔ v26WordWeight w < 3900 := by
  constructor
  · intro hw
    simpa [v26SurvivorWords] using hw
  · intro hw
    rcases w with ⟨a, b, c, d, e, f⟩
    simp only [v26SurvivorWords, Finset.mem_filter, Finset.mem_product,
      Finset.mem_univ, true_and]
    constructor
    · simp only [v26SuffixBCCBA, Finset.mem_filter, Finset.mem_product,
        Finset.mem_univ, true_and]
      constructor
      · simp only [v26SuffixCCBA, Finset.mem_filter, Finset.mem_product,
          Finset.mem_univ, true_and]
        constructor
        · simp only [v26SuffixCBA, Finset.mem_filter, Finset.mem_product,
            Finset.mem_univ, true_and]
          constructor
          · simp only [v26SuffixBA, Finset.mem_filter, Finset.mem_product,
              Finset.mem_univ, true_and]
            constructor
            · simp only [v26SuffixA, Finset.mem_filter, Finset.mem_univ, true_and]
              unfold v26WordWeight at hw
              omega
            · unfold v26WordWeight at hw
              omega
          · unfold v26WordWeight at hw
            omega
        · unfold v26WordWeight at hw
          omega
      · unfold v26WordWeight at hw
        omega
    · exact hw

end HurtadoZeta23
