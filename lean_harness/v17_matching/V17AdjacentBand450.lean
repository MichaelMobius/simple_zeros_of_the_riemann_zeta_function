import HurtadoZeta23.V17ConcreteMatching450
import HurtadoZeta23.V17MatchingIndices
import HurtadoZeta23.V17AdjacentBandScalar
import HurtadoZeta23.V17ParitySplit
import Mathlib.Tactic

noncomputable section

open Matrix Finset
open scoped BigOperators ComplexOrder

namespace HurtadoZeta23

/-- Totalized squared matrix entry used only by the finite matching argument. -/
def v17MatchingNormSqNat450
    (G : Matrix (Fin 450) (Fin 450) ℂ)
    (a b : ℕ) : ℝ :=
  if ha : a < 450 then
    if hb : b < 450 then
      ‖G ⟨a, ha⟩ ⟨b, hb⟩‖ ^ 2
    else 0
  else 0

/-- The complete 449-edge adjacent band of a PSD 450-by-450 matrix costs at
most one copy of its spectral defect, assuming only the robust diagonal bound
`Re G_ii ≤ 1`.

The proof joins the even matching with the once-rotated matching.  The latter
contains the 224 odd adjacent edges plus the nonnegative wrap edge `(449,0)`. -/
theorem v17_adjacent_matrix_band_le_defect_450
    (G : Matrix (Fin 450) (Fin 450) ℂ)
    (hG : G.PosSemidef)
    (hdiag : ∀ i, (G i i).re ≤ 1) :
    pairBandEnergy 450 0 (v17MatchingNormSqNat450 G)
      ≤ gramSpectralDefect G hG := by
  let D : ℝ := gramSpectralDefect G hG
  let evenE : ℝ :=
    ∑ b : Fin 225,
      ‖G (v17PairEquiv450 (b, 0)) (v17PairEquiv450 (b, 1))‖ ^ 2
  let oddE : ℝ :=
    ∑ b : Fin 224,
      ‖G (finRotate 450 (v17PairEquiv450 (b.castSucc, 0)))
          (finRotate 450 (v17PairEquiv450 (b.castSucc, 1)))‖ ^ 2
  let wrapE : ℝ :=
    ‖G (finRotate 450 (v17PairEquiv450 (Fin.last 224, 0)))
        (finRotate 450 (v17PairEquiv450 (Fin.last 224, 1)))‖ ^ 2

  have heven0 := v17_even_matching_fin450 G hG hdiag
  have heven : 2 * evenE ≤ D := by
    dsimp [evenE, D]
    calc
      2 * (∑ b : Fin 225,
          ‖G (v17PairEquiv450 (b, 0)) (v17PairEquiv450 (b, 1))‖ ^ 2)
          = ∑ b : Fin 225,
              2 * ‖G (v17PairEquiv450 (b, 0))
                    (v17PairEquiv450 (b, 1))‖ ^ 2 := by
              rw [Finset.mul_sum]
      _ ≤ gramSpectralDefect G hG := heven0

  have hrot0 := v17_rotated_matching_fin450 G hG hdiag
  have hrot : 2 * (oddE + wrapE) ≤ D := by
    rw [Fin.sum_univ_castSucc] at hrot0
    dsimp [oddE, wrapE, D]
    calc
      2 *
          ((∑ b : Fin 224,
              ‖G (finRotate 450 (v17PairEquiv450 (b.castSucc, 0)))
                  (finRotate 450 (v17PairEquiv450 (b.castSucc, 1)))‖ ^ 2) +
            ‖G (finRotate 450 (v17PairEquiv450 (Fin.last 224, 0)))
                (finRotate 450 (v17PairEquiv450 (Fin.last 224, 1)))‖ ^ 2)
          =
          (∑ b : Fin 224,
              2 * ‖G (finRotate 450 (v17PairEquiv450 (b.castSucc, 0)))
                    (finRotate 450 (v17PairEquiv450 (b.castSucc, 1)))‖ ^ 2) +
            2 * ‖G (finRotate 450 (v17PairEquiv450 (Fin.last 224, 0)))
                  (finRotate 450 (v17PairEquiv450 (Fin.last 224, 1)))‖ ^ 2 := by
              rw [mul_add, Finset.mul_sum]
      _ ≤ gramSpectralDefect G hG := hrot0

  have hwrap : 0 ≤ wrapE := by
    dsimp [wrapE]
    exact sq_nonneg _

  have hevenEq :
      (∑ b ∈ Finset.range 225,
          v17MatchingNormSqNat450 G (2 * b) (2 * b + 1)) = evenE := by
    dsimp [evenE]
    apply Finset.sum_bij
      (fun b hb => (⟨b, Finset.mem_range.mp hb⟩ : Fin 225))
    · intro b hb
      simp
    · intro b₁ hb₁ b₂ hb₂ h
      exact congrArg Fin.val h
    · intro q hq
      refine ⟨q.1, Finset.mem_range.mpr q.2, ?_⟩
      apply Fin.ext
      rfl
    · intro b hb
      have hb225 : b < 225 := Finset.mem_range.mp hb
      have h0 : 2 * b < 450 := by omega
      have h1 : 2 * b + 1 < 450 := by omega
      simp only [v17MatchingNormSqNat450, h0, h1, dite_true]
      have hidx0 :
          (⟨2 * b, h0⟩ : Fin 450) =
            v17PairEquiv450 (⟨b, hb225⟩, 0) := by
        apply Fin.ext
        simpa using (v17PairEquiv450_zero_val ⟨b, hb225⟩).symm
      have hidx1 :
          (⟨2 * b + 1, h1⟩ : Fin 450) =
            v17PairEquiv450 (⟨b, hb225⟩, 1) := by
        apply Fin.ext
        simpa using (v17PairEquiv450_one_val ⟨b, hb225⟩).symm
      rw [hidx0, hidx1]

  have hoddEq :
      (∑ b ∈ Finset.range 224,
          v17MatchingNormSqNat450 G (2 * b + 1) (2 * b + 2)) = oddE := by
    dsimp [oddE]
    apply Finset.sum_bij
      (fun b hb => (⟨b, Finset.mem_range.mp hb⟩ : Fin 224))
    · intro b hb
      simp
    · intro b₁ hb₁ b₂ hb₂ h
      exact congrArg Fin.val h
    · intro q hq
      refine ⟨q.1, Finset.mem_range.mpr q.2, ?_⟩
      apply Fin.ext
      rfl
    · intro b hb
      have hb224 : b < 224 := Finset.mem_range.mp hb
      have h1 : 2 * b + 1 < 450 := by omega
      have h2 : 2 * b + 2 < 450 := by omega
      simp only [v17MatchingNormSqNat450, h1, h2, dite_true]
      have hidx1 :
          (⟨2 * b + 1, h1⟩ : Fin 450) =
            finRotate 450 (v17PairEquiv450 ((⟨b, hb224⟩ : Fin 224).castSucc, 0)) := by
        apply Fin.ext
        simpa using (v17_rotated_pair_zero_val ⟨b, hb224⟩).symm
      have hidx2 :
          (⟨2 * b + 2, h2⟩ : Fin 450) =
            finRotate 450 (v17PairEquiv450 ((⟨b, hb224⟩ : Fin 224).castSucc, 1)) := by
        apply Fin.ext
        simpa using (v17_rotated_pair_one_val ⟨b, hb224⟩).symm
      rw [hidx1, hidx2]

  have hband :
      pairBandEnergy 450 0 (v17MatchingNormSqNat450 G) = evenE + oddE := by
    rw [v17_pairBandEnergy_450_even_odd]
    rw [hevenEq, hoddEq]

  exact v17_two_matchings_close_adjacent_band
    heven hrot hwrap hband

end HurtadoZeta23