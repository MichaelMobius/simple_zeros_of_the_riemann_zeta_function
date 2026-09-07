import HurtadoZeta23.ShiftedRetainedPinching
import HurtadoZeta23.V17AnalyticBridge450
import Mathlib.Tactic

noncomputable section

open Matrix Finset
open scoped ComplexOrder BigOperators

namespace HurtadoZeta23

set_option maxRecDepth 10000

/-- The length-450 consecutive principal block of the retained Gram indexed by
retained rank. -/
noncomputable def v17RetainedGramFinBlock450
    (T : ℝ) (s : ℕ)
    (hs : s + 450 ≤ articleRetainedCard T) :
    Matrix (Fin 450) (Fin 450) ℂ :=
  (articleRetainedGramFin T).submatrix
    (v17RetainedRank450 T s hs)
    (v17RetainedRank450 T s hs)

/-- Every retained-rank length-450 block is PSD. -/
theorem v17RetainedGramFinBlock450_posSemidef
    (T : ℝ) (s : ℕ)
    (hs : s + 450 ≤ articleRetainedCard T) :
    (v17RetainedGramFinBlock450 T s hs).PosSemidef := by
  exact principal_submatrix_posSemidef
    (articleRetainedGramFin T)
    (articleRetainedGramFin_posSemidef T)
    (v17RetainedRank450 T s hs)

/-- The retained-rank principal block is literally the v17 Gram block already
used by the analytic bridge. -/
theorem v17RetainedGramFinBlock450_eq_Gram450
    (T : ℝ) (s : ℕ)
    (hs : s + 450 ≤ articleRetainedCard T) :
    v17RetainedGramFinBlock450 T s hs = v17Gram450 T s hs := by
  ext i j
  rfl

/-- Spectral defect of an actual consecutive v17 length-450 retained block. -/
noncomputable def v17BlockDefect450
    (T : ℝ) (s : ℕ)
    (hs : s + 450 ≤ articleRetainedCard T) : ℝ :=
  gramSpectralDefect
    (v17RetainedGramFinBlock450 T s hs)
    (v17RetainedGramFinBlock450_posSemidef T s hs)

/-- The local defect agrees with the defect of the analytic `v17Gram450`. -/
theorem v17BlockDefect450_eq_Gram450
    (T : ℝ) (s : ℕ)
    (hs : s + 450 ≤ articleRetainedCard T) :
    v17BlockDefect450 T s hs =
      gramSpectralDefect
        (v17Gram450 T s hs)
        (by
          rw [← v17RetainedGramFinBlock450_eq_Gram450 T s hs]
          exact v17RetainedGramFinBlock450_posSemidef T s hs) := by
  unfold v17BlockDefect450
  exact gramSpectralDefect_eq_of_matrix_eq
    (v17RetainedGramFinBlock450_posSemidef T s hs)
    (by
      rw [← v17RetainedGramFinBlock450_eq_Gram450 T s hs]
      exact v17RetainedGramFinBlock450_posSemidef T s hs)
    (v17RetainedGramFinBlock450_eq_Gram450 T s hs)

/-- A complete 450-block in the tail beginning at residue `r` is the ordinary
v17 consecutive block beginning at `r + 450*q`. -/
theorem v17_shifted_fullBlock_eq_retained450
    (T : ℝ)
    (hS : 450 ≤ articleRetainedCard T)
    (r : Fin 450)
    (q : Fin ((articleRetainedCard T - r.1) / 450)) :
    fullBlockMatrix
        450 (by norm_num)
        (tailMatrix
          (articleRetainedGramFin T)
          r.1
          (residue_le_card hS r))
        q
      =
    v17RetainedGramFinBlock450
      T
      (shiftedBlockStart r q)
      (shiftedBlockStart_add_le
        (N := articleRetainedCard T)
        (m := 450)
        (by norm_num)
        r q) := by
  rw [fullBlockMatrix_tail_eq_sliding
    (m := 450)
    (by norm_num)
    (articleRetainedGramFin T)
    r.1
    (residue_le_card hS r)
    q]
  ext i j
  congr 2 <;> apply Fin.ext <;> rfl

/-- Equality of the corresponding spectral defects. -/
theorem v17_shifted_fullBlockDefect_eq
    (T : ℝ)
    (hS : 450 ≤ articleRetainedCard T)
    (r : Fin 450)
    (q : Fin ((articleRetainedCard T - r.1) / 450)) :
    fullBlockDefect
        450 (by norm_num)
        (tailMatrix
          (articleRetainedGramFin T)
          r.1
          (residue_le_card hS r))
        (tailMatrix_posSemidef
          (articleRetainedGramFin T)
          (articleRetainedGramFin_posSemidef T)
          r.1
          (residue_le_card hS r))
        q
      =
    v17BlockDefect450
      T
      (shiftedBlockStart r q)
      (shiftedBlockStart_add_le
        (N := articleRetainedCard T)
        (m := 450)
        (by norm_num)
        r q) := by
  unfold fullBlockDefect v17BlockDefect450
  exact gramSpectralDefect_eq_of_matrix_eq
    _ _ (v17_shifted_fullBlock_eq_retained450 T hS r q)

/-- For one residue class modulo 450, the disjoint family of full blocks costs
at most the defect of the retained Gram. -/
theorem v17_one_shift_defect_le_retained
    (T : ℝ)
    (hS : 450 ≤ articleRetainedCard T)
    (r : Fin 450) :
    (∑ q : Fin ((articleRetainedCard T - r.1) / 450),
      v17BlockDefect450
        T
        (shiftedBlockStart r q)
        (shiftedBlockStart_add_le
          (N := articleRetainedCard T)
          (m := 450)
          (by norm_num)
          r q))
      ≤ articleRetainedDefect T := by
  let hr := residue_le_card hS r
  let Tail := tailMatrix (articleRetainedGramFin T) r.1 hr
  let hTail : Tail.PosSemidef :=
    tailMatrix_posSemidef
      (articleRetainedGramFin T)
      (articleRetainedGramFin_posSemidef T)
      r.1 hr
  have hblocks :=
    sum_fullBlockDefect_le
      (N := articleRetainedCard T - r.1)
      (m := 450)
      (by norm_num)
      Tail hTail
  have htail :
      gramSpectralDefect Tail hTail ≤
        gramSpectralDefect
          (articleRetainedGramFin T)
          (articleRetainedGramFin_posSemidef T) := by
    exact tailDefect_le
      (articleRetainedGramFin T)
      (articleRetainedGramFin_posSemidef T)
      r.1 hr
  have hfin :
      gramSpectralDefect
          (articleRetainedGramFin T)
          (articleRetainedGramFin_posSemidef T)
        = articleRetainedDefect T :=
    articleRetainedGramFin_defect_eq T
  calc
    (∑ q : Fin ((articleRetainedCard T - r.1) / 450),
      v17BlockDefect450
        T
        (shiftedBlockStart r q)
        (shiftedBlockStart_add_le
          (N := articleRetainedCard T)
          (m := 450)
          (by norm_num)
          r q))
      =
    ∑ q : Fin ((articleRetainedCard T - r.1) / 450),
      fullBlockDefect 450 (by norm_num) Tail hTail q := by
        apply Finset.sum_congr rfl
        intro q hq
        symm
        simpa [Tail, hTail, hr] using
          v17_shifted_fullBlockDefect_eq T hS r q
    _ ≤ gramSpectralDefect Tail hTail := hblocks
    _ ≤ gramSpectralDefect
          (articleRetainedGramFin T)
          (articleRetainedGramFin_posSemidef T) := htail
    _ = articleRetainedDefect T := hfin

/-- Sum of defects of all consecutive length-450 retained blocks is at most
450 copies of the retained global defect. -/
theorem v17_sum_all_blockDefect450_le_retained
    (T : ℝ)
    (hS : 450 ≤ articleRetainedCard T) :
    (∑ s : Fin (articleRetainedCard T - 450 + 1),
      v17BlockDefect450
        T s.1
        (by
          have hs := s.2
          omega))
      ≤ (450 : ℝ) * articleRetainedDefect T := by
  have hreindex :=
    sum_sliding_starts_eq_nested_shifted
      (N := articleRetainedCard T)
      (m := 450)
      (by norm_num)
      hS
      (fun s : ℕ =>
        if hs : s + 450 ≤ articleRetainedCard T then
          v17BlockDefect450 T s hs
        else 0)

  have hleft :
      (∑ s : Fin (articleRetainedCard T - 450 + 1),
        (if hs : s.1 + 450 ≤ articleRetainedCard T then
          v17BlockDefect450 T s.1 hs
        else 0))
      =
      (∑ s : Fin (articleRetainedCard T - 450 + 1),
        v17BlockDefect450
          T s.1
          (by
            have hs := s.2
            omega)) := by
    apply Finset.sum_congr rfl
    intro s hs
    split
    · rename_i hfit
      unfold v17BlockDefect450
      exact gramSpectralDefect_eq_of_matrix_eq
        (v17RetainedGramFinBlock450_posSemidef T s.1 hfit)
        (v17RetainedGramFinBlock450_posSemidef T s.1 (by
          have hs' := s.2
          omega))
        rfl
    · rename_i hbad
      exfalso
      apply hbad
      have hs' := s.2
      omega

  have hright :
      (∑ r : Fin 450,
        ∑ q : Fin ((articleRetainedCard T - r.1) / 450),
          (if hs : r.1 + q.1 * 450 + 450 ≤ articleRetainedCard T then
            v17BlockDefect450 T (r.1 + q.1 * 450) hs
          else 0))
      =
      ∑ r : Fin 450,
        ∑ q : Fin ((articleRetainedCard T - r.1) / 450),
          v17BlockDefect450
            T
            (shiftedBlockStart r q)
            (shiftedBlockStart_add_le
              (N := articleRetainedCard T)
              (m := 450)
              (by norm_num)
              r q) := by
    apply Finset.sum_congr rfl
    intro r hr
    apply Finset.sum_congr rfl
    intro q hq
    have hfit := shiftedBlockStart_add_le
      (N := articleRetainedCard T)
      (m := 450)
      (by norm_num)
      r q
    simp only [shiftedBlockStart] at hfit ⊢
    split
    · rename_i hfit'
      unfold v17BlockDefect450
      exact gramSpectralDefect_eq_of_matrix_eq
        (v17RetainedGramFinBlock450_posSemidef
          T (r.1 + q.1 * 450) hfit')
        (v17RetainedGramFinBlock450_posSemidef
          T (r.1 + q.1 * 450) hfit)
        rfl
    · rename_i hbad
      exact False.elim (hbad hfit)

  rw [hleft] at hreindex
  rw [hright] at hreindex
  rw [hreindex]
  calc
    (∑ r : Fin 450,
      ∑ q : Fin ((articleRetainedCard T - r.1) / 450),
        v17BlockDefect450
          T
          (shiftedBlockStart r q)
          (shiftedBlockStart_add_le
            (N := articleRetainedCard T)
            (m := 450)
            (by norm_num)
            r q))
      ≤ ∑ r : Fin 450, articleRetainedDefect T := by
        apply Finset.sum_le_sum
        intro r hr
        exact v17_one_shift_defect_le_retained T hS r
    _ = (450 : ℝ) * articleRetainedDefect T := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      norm_num

/-- Published/global form: the total defect of all consecutive v17 blocks is
bounded by 450 copies of the global stable defect. -/
theorem v17_sum_all_blockDefect450_le_stable
    (T : ℝ)
    (hS : 450 ≤ articleRetainedCard T) :
    (∑ s : Fin (articleRetainedCard T - 450 + 1),
      v17BlockDefect450
        T s.1
        (by
          have hs := s.2
          omega))
      ≤ (450 : ℝ) * articleStableDefect T := by
  calc
    _ ≤ (450 : ℝ) * articleRetainedDefect T :=
      v17_sum_all_blockDefect450_le_retained T hS
    _ ≤ (450 : ℝ) * articleStableDefect T := by
      exact mul_le_mul_of_nonneg_left
        (articleRetainedDefect_le_articleStableDefect T)
        (by positivity)

end HurtadoZeta23