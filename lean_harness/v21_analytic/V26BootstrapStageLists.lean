import HurtadoZeta23.V26Word511Certificate
import Mathlib.Tactic

namespace HurtadoZeta23

/-- Decimal code of a basin word, using the published 1-based basin labels. -/
def v26WordCode (w : V26BasinWord) : Nat :=
  100000 * (w.1.1 + 1) +
  10000 * (w.2.1.1 + 1) +
  1000 * (w.2.2.1.1 + 1) +
  100 * (w.2.2.2.1.1 + 1) +
  10 * (w.2.2.2.2.1.1 + 1) +
  (w.2.2.2.2.2.1 + 1)

/-- Published survivor codes after the first exact rational bootstrap pass. -/
def v26Round1Codes : Finset Nat := [111111, 111112, 111113, 111121, 111122, 111123, 111131, 111132, 111211, 111212, 111213, 111214, 111221, 111222, 111223, 111231, 111311, 111312, 111313, 111321, 111411, 112111, 112112, 112113, 112114, 112121, 112122, 112123, 112131, 112132, 112141, 112211, 112212, 112213, 112214, 112221, 112222, 112231, 112311, 112312, 112321, 113111, 113112, 113113, 113121, 113122, 113131, 113211, 113212, 113221, 113311, 114111, 114112, 114121, 121111, 121112, 121113, 121114, 121121, 121122, 121123, 121131, 121132, 121141, 121211, 121212, 121213, 121214, 121221, 121222, 121223, 121231, 121311, 121312, 121313, 121321, 121411, 122111, 122112, 122113, 122121, 122122, 122123, 122131, 122211, 122212, 122213, 122221, 122222, 122311, 122312, 123111, 123112, 123121, 123122, 123211, 123212, 131111, 131112, 131113, 131121, 131122, 131131, 131211, 131212, 131213, 131221, 131222, 131311, 131312, 132111, 132112, 132121, 132211, 132212, 141121, 141211, 211111, 211112, 211113, 211121, 211122, 211123, 211131, 211132, 211211, 211212, 211213, 211214, 211221, 211222, 211231, 211311, 211312, 211313, 211321, 211411, 212111, 212112, 212113, 212114, 212121, 212122, 212123, 212131, 212132, 212211, 212212, 212213, 212221, 212222, 212231, 212311, 212312, 212321, 213111, 213112, 213113, 213121, 213122, 213131, 213211, 213212, 213221, 221111, 221112, 221113, 221121, 221122, 221131, 221211, 221212, 221213, 221221, 221222, 221311, 221312, 221321, 222111, 222112, 222113, 222121, 222122, 222131, 222211, 222212, 222221, 231111, 231112, 231121, 231211, 231212, 311111, 311112, 311121, 311122, 311131, 311211, 311212, 311213, 311221, 311222, 311311, 311312, 312111, 312112, 312113, 312121, 312122, 312131, 312211, 312212, 312221, 313111, 313112, 313121, 321111, 321112, 321121, 321211, 321212, 321221, 322111, 322121, 411121, 411211, 411212, 412111, 412112, 412121, 412211].toFinset

/-- Published survivor codes after the second pass. -/
def v26Round2Codes : Finset Nat := [112121, 112211, 112212, 112221, 121121, 121211, 121212, 121221, 122112, 122121, 122122, 122211, 122212, 211212, 211221, 212112, 212121, 212122, 212211, 212212, 212221, 221212, 221221].toFinset

/-- The five published final words. -/
def v26Round3Codes : Finset Nat := [121212, 121221, 122121, 212121, 212212].toFinset

/-- The stage sets are deliberately defined as filters of the previously
certified set.  At this layer they are bookkeeping objects only; the rational
quadratic certificates must separately prove that every discarded word is
indeed impossible. -/
def v26Round1Words : Finset V26BasinWord :=
  v26SurvivorWords.filter (fun w => v26WordCode w ∈ v26Round1Codes)

def v26Round2Words : Finset V26BasinWord :=
  v26Round1Words.filter (fun w => v26WordCode w ∈ v26Round2Codes)

def v26Round3Words : Finset V26BasinWord :=
  v26Round2Words.filter (fun w => v26WordCode w ∈ v26Round3Codes)

/-- Closed bookkeeping check: the first published stage contains 231 words. -/
theorem v26_round1_count : v26Round1Words.card = 231 := by
  set_option maxHeartbeats 0 in
  decide

/-- Closed bookkeeping check: the second published stage contains 23 words. -/
theorem v26_round2_count : v26Round2Words.card = 23 := by
  set_option maxHeartbeats 0 in
  decide

/-- Closed bookkeeping check: the final stage contains five words. -/
theorem v26_round3_count : v26Round3Words.card = 5 := by
  set_option maxHeartbeats 0 in
  decide

/-- Closed check of the exact five final decimal codes. -/
theorem v26_round3_codes_exact :
    v26Round3Words.image v26WordCode =
      {121212, 121221, 122121, 212121, 212212} := by
  set_option maxHeartbeats 0 in
  decide

end HurtadoZeta23
