import HurtadoZeta23.ShiftedBlockIndexing
import HurtadoZeta23.RetainedGramFin
import Mathlib.Tactic

noncomputable section

open Matrix Finset
open scoped ComplexOrder BigOperators

namespace HurtadoZeta23

/-!
# Shifted retained Gram pinching

This file combines:

* the disjoint-block pinching theorem on `Fin N`;
* the exact residue/quotient decomposition of all sliding starts;
* principal-submatrix monotonicity obtained from one Boolean pinching.

The result is the finite-dimensional heart of the article:

  ∑_{s=0}^{S-m} D(M_s) ≤ m * D(M_retained),

specialized downstream to `m = blockLength = 262`.
-/

/-! ## Tail principal submatrices -/

/-- Embed the tail `r, r+1, ..., N-1` into `Fin N`. -/
def tailEmbed
    (N r : ℕ) (hr : r ≤ N) :
    Fin (N - r) → Fin N :=
  fun i =>
    ⟨r + i.1, by omega⟩

/-- Principal tail of a matrix indexed by `Fin N`. -/
def tailMatrix
    {N : ℕ}
    (M : Matrix (Fin N) (Fin N) ℂ)
    (r : ℕ) (hr : r ≤ N) :
    Matrix (Fin (N - r)) (Fin (N - r)) ℂ :=
  M.submatrix
    (tailEmbed N r hr)
    (tailEmbed N r hr)

/-- A principal tail of a PSD matrix is PSD. -/
theorem tailMatrix_posSemidef
    {N : ℕ}
    (M : Matrix (Fin N) (Fin N) ℂ)
    (hM : M.PosSemidef)
    (r : ℕ) (hr : r ≤ N) :
    (tailMatrix M r hr).PosSemidef := by
  exact
    principal_submatrix_posSemidef
      M hM (tailEmbed N r hr)

/-- Boolean label selecting the tail `i ≥ r`. -/
noncomputable def tailLabel
    (N r : ℕ) :
    Fin N → Bool := by
  classical
  exact fun i => decide (r ≤ i.1)

/-- The `true` tail fiber is canonically `Fin (N-r)`. -/
noncomputable def tailTrueFiberEquiv
    (N r : ℕ) (hr : r ≤ N) :
    BlockFiber (tailLabel N r) true
      ≃ Fin (N - r) where

  toFun z := by
    classical
    have hz : r ≤ z.1.1 := by
      simpa [tailLabel] using z.2
    exact ⟨z.1.1 - r, by omega⟩

  invFun i := by
    classical
    refine
      ⟨tailEmbed N r hr i, ?_⟩
    simp [tailLabel, tailEmbed]

  left_inv z := by
    apply Subtype.ext
    apply Fin.ext
    classical
    have hz : r ≤ z.1.1 := by
      simpa [tailLabel] using z.2
    dsimp [tailEmbed]
    omega

  right_inv i := by
    apply Fin.ext
    dsimp [tailEmbed]
    omega

/-- Reindexing the `true` Boolean fiber gives the literal tail matrix. -/
theorem tailTrueBlock_reindex
    {N : ℕ}
    (M : Matrix (Fin N) (Fin N) ℂ)
    (r : ℕ) (hr : r ≤ N) :
    Matrix.reindex
        (tailTrueFiberEquiv N r hr)
        (tailTrueFiberEquiv N r hr)
        (partitionBlock
          (tailLabel N r) M true)
      =
    tailMatrix M r hr := by
  ext i j
  rfl

/-- Spectral defect of a principal tail. -/
noncomputable def tailDefect
    {N : ℕ}
    (M : Matrix (Fin N) (Fin N) ℂ)
    (hM : M.PosSemidef)
    (r : ℕ) (hr : r ≤ N) :
    ℝ :=
  gramSpectralDefect
    (tailMatrix M r hr)
    (tailMatrix_posSemidef M hM r hr)

/-- The tail defect is the defect of the `true` Boolean partition block. -/
theorem tailDefect_eq_trueBlockDefect
    {N : ℕ}
    (M : Matrix (Fin N) (Fin N) ℂ)
    (hM : M.PosSemidef)
    (r : ℕ) (hr : r ≤ N) :
    tailDefect M hM r hr
      =
    gramSpectralDefect
      (partitionBlock (tailLabel N r) M true)
      (principal_submatrix_posSemidef
        M hM
        (fun i : BlockFiber (tailLabel N r) true =>
          i.1)) := by

  let B :=
    partitionBlock (tailLabel N r) M true

  let hB : B.PosSemidef :=
    principal_submatrix_posSemidef
      M hM
      (fun i : BlockFiber (tailLabel N r) true =>
        i.1)

  let e := tailTrueFiberEquiv N r hr

  have hre :
      gramSpectralDefect
          (Matrix.reindex e e B)
          (posSemidef_reindex e B hB)
        =
      gramSpectralDefect B hB :=
    gramSpectralDefect_reindex e B hB

  have hmat :
      Matrix.reindex e e B =
        tailMatrix M r hr := by
    simpa [B, e] using
      tailTrueBlock_reindex M r hr

  unfold tailDefect

  calc
    gramSpectralDefect
        (tailMatrix M r hr)
        (tailMatrix_posSemidef M hM r hr)
      =
    gramSpectralDefect
        (Matrix.reindex e e B)
        (posSemidef_reindex e B hB) := by
          exact
            (gramSpectralDefect_eq_of_matrix_eq
              (posSemidef_reindex e B hB)
              (tailMatrix_posSemidef M hM r hr)
              hmat).symm
    _ = gramSpectralDefect B hB := hre

/-- Principal-tail defect is bounded by ambient defect. -/
theorem tailDefect_le
    {N : ℕ}
    (M : Matrix (Fin N) (Fin N) ℂ)
    (hM : M.PosSemidef)
    (r : ℕ) (hr : r ≤ N) :
    tailDefect M hM r hr
      ≤ gramSpectralDefect M hM := by

  have hp :=
    gramDefectPinching_bool_proved
      (tailLabel N r) M hM

  unfold GramDefectPinchingPartition at hp
  rw [Fintype.sum_bool] at hp

  let hfalse :
      (partitionBlock
        (tailLabel N r) M false).PosSemidef :=
    principal_submatrix_posSemidef
      M hM
      (fun i :
        BlockFiber (tailLabel N r) false =>
          i.1)

  have hfalse0 :
      0 ≤
      gramSpectralDefect
        (partitionBlock
          (tailLabel N r) M false)
        hfalse :=
    gramSpectralDefect_nonneg _ hfalse

  have htrue :=
    tailDefect_eq_trueBlockDefect
      M hM r hr

  rw [htrue]

  linarith

/-! ## Identify shifted tail blocks with ordinary consecutive blocks -/

/-- The ambient `Fin N` index of local point `i` in block `q` of the
tail beginning at `r`. -/
def shiftedTailBlockEmbed
    {N m : ℕ}
    (hm : 1 ≤ m)
    (r : ℕ) (hr : r ≤ N)
    (q : Fin ((N - r) / m))
    (i : Fin m) :
    Fin N := by

  have hq1 :
      q.1 + 1 ≤ (N - r) / m :=
    Nat.succ_le_of_lt q.2

  have hmul1 :
      (q.1 + 1) * m
        ≤ ((N - r) / m) * m :=
    Nat.mul_le_mul_right m hq1

  have hmul2 :
      ((N - r) / m) * m
        ≤ N - r :=
    Nat.div_mul_le_self (N - r) m

  have hblock :
      (q.1 + 1) * m ≤ N - r :=
    hmul1.trans hmul2

  have hlocal :
      q.1 * m + i.1 < N - r := by
    calc
      q.1 * m + i.1
          < q.1 * m + m :=
        Nat.add_lt_add_left i.2 (q.1 * m)
      _ = (q.1 + 1) * m := by
        rw [Nat.succ_mul]
      _ ≤ N - r := hblock

  have hadd :
      r + (q.1 * m + i.1)
        < r + (N - r) :=
    Nat.add_lt_add_left hlocal r

  have hcancel :
      r + (N - r) = N :=
    Nat.add_sub_of_le hr

  refine ⟨r + q.1 * m + i.1, ?_⟩

  calc
    r + q.1 * m + i.1
        = r + (q.1 * m + i.1) := by
          omega
    _ < r + (N - r) := hadd
    _ = N := hcancel

/-- Composing the tail embedding with the complete-block embedding gives
the direct ambient shifted-block embedding. -/
theorem tailEmbed_fullBlockEmbed_eq_shifted
    {N m : ℕ}
    (hm : 1 ≤ m)
    (r : ℕ) (hr : r ≤ N)
    (q : Fin ((N - r) / m))
    (i : Fin m) :
    tailEmbed N r hr
        (fullBlockEmbed (N - r) m hm q i)
      =
    shiftedTailBlockEmbed hm r hr q i := by

  apply Fin.ext
  change
    r + (q.1 * m + i.1) =
      r + q.1 * m + i.1
  omega

/-- Full block `q` in the tail beginning at `r` is the ordinary consecutive
block beginning at `r + q*m`. -/
theorem fullBlockMatrix_tail_eq_sliding
    {N m : ℕ}
    (hm : 1 ≤ m)
    (M : Matrix (Fin N) (Fin N) ℂ)
    (r : ℕ) (hr : r ≤ N)
    (q : Fin ((N - r) / m)) :
    fullBlockMatrix
        m hm
        (tailMatrix M r hr)
        q
      =
    M.submatrix
      (shiftedTailBlockEmbed hm r hr q)
      (shiftedTailBlockEmbed hm r hr q) := by

  ext i j

  change
    M
      (tailEmbed N r hr
        (fullBlockEmbed (N - r) m hm q i))
      (tailEmbed N r hr
        (fullBlockEmbed (N - r) m hm q j))
      =
    M
      (shiftedTailBlockEmbed hm r hr q i)
      (shiftedTailBlockEmbed hm r hr q j)

  rw [
    tailEmbed_fullBlockEmbed_eq_shifted,
    tailEmbed_fullBlockEmbed_eq_shifted
  ]

/-!
For the article we only need residues `r < m` and `m ≤ S`, so `r ≤ S`.
-/
lemma residue_le_card
    {N m : ℕ}
    (hNm : m ≤ N)
    (r : Fin m) :
    r.1 ≤ N := by
  omega

/-- The complete block in residue family `r` is exactly the already defined
consecutive retained block. -/
theorem article_shifted_fullBlock_eq_consecutive
    (T : ℝ)
    (hS : blockLength ≤ articleRetainedCard T)
    (r : Fin blockLength)
    (q :
      Fin ((articleRetainedCard T - r.1) / blockLength)) :
    fullBlockMatrix
        blockLength
        (by norm_num [blockLength])
        (tailMatrix
          (articleRetainedGramFin T)
          r.1
          (residue_le_card hS r))
        q
      =
    consecutiveRetainedGramFinBlock
      T
      (shiftedBlockStart r q)
      (shiftedBlockStart_add_le
        (N := articleRetainedCard T)
        (m := blockLength)
        (by norm_num [blockLength])
        r q) := by

  rw [
    fullBlockMatrix_tail_eq_sliding
      (m := blockLength)
      (by norm_num [blockLength])
      (articleRetainedGramFin T)
      r.1
      (residue_le_card hS r)
      q
  ]

  ext i j

  change
    articleRetainedGramFin T
      (shiftedTailBlockEmbed
        (N := articleRetainedCard T)
        (by norm_num [blockLength])
        r.1
        (residue_le_card hS r)
        q i)
      (shiftedTailBlockEmbed
        (N := articleRetainedCard T)
        (by norm_num [blockLength])
        r.1
        (residue_le_card hS r)
        q j)
      =
    articleRetainedGramFin T
      (consecutiveRetainedRank
        T
        (shiftedBlockStart r q)
        (shiftedBlockStart_add_le
          (N := articleRetainedCard T)
          (m := blockLength)
          (by norm_num [blockLength])
          r q)
        i)
      (consecutiveRetainedRank
        T
        (shiftedBlockStart r q)
        (shiftedBlockStart_add_le
          (N := articleRetainedCard T)
          (m := blockLength)
          (by norm_num [blockLength])
          r q)
        j)

  congr 2 <;> apply Fin.ext <;> rfl

/-- Hence the corresponding defects agree. -/
theorem article_shifted_fullBlockDefect_eq
    (T : ℝ)
    (hS : blockLength ≤ articleRetainedCard T)
    (r : Fin blockLength)
    (q :
      Fin ((articleRetainedCard T - r.1) / blockLength)) :
    fullBlockDefect
        blockLength
        (by norm_num [blockLength])
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
    consecutiveBlockDefect
      T
      (shiftedBlockStart r q)
      (shiftedBlockStart_add_le
        (N := articleRetainedCard T)
        (m := blockLength)
        (by norm_num [blockLength])
        r q) := by

  unfold fullBlockDefect

  calc
    gramSpectralDefect
      (fullBlockMatrix
        blockLength
        (by norm_num [blockLength])
        (tailMatrix
          (articleRetainedGramFin T)
          r.1
          (residue_le_card hS r))
        q)
      (fullBlockMatrix_posSemidef
        blockLength
        (by norm_num [blockLength])
        (tailMatrix
          (articleRetainedGramFin T)
          r.1
          (residue_le_card hS r))
        (tailMatrix_posSemidef
          (articleRetainedGramFin T)
          (articleRetainedGramFin_posSemidef T)
          r.1
          (residue_le_card hS r))
        q)
      =
    gramSpectralDefect
      (consecutiveRetainedGramFinBlock
        T
        (shiftedBlockStart r q)
        (shiftedBlockStart_add_le
          (N := articleRetainedCard T)
          (m := blockLength)
          (by norm_num [blockLength])
          r q))
      (consecutiveRetainedGramFinBlock_posSemidef
        T
        (shiftedBlockStart r q)
        (shiftedBlockStart_add_le
          (N := articleRetainedCard T)
          (m := blockLength)
          (by norm_num [blockLength])
          r q)) := by

        exact
          gramSpectralDefect_eq_of_matrix_eq
            _
            _
            (article_shifted_fullBlock_eq_consecutive
              T hS r q)

    _ =
      consecutiveBlockDefect
        T
        (shiftedBlockStart r q)
        (shiftedBlockStart_add_le
          (N := articleRetainedCard T)
          (m := blockLength)
          (by norm_num [blockLength])
          r q) :=
      consecutiveRetainedGramFinBlock_defect_eq
        T
        (shiftedBlockStart r q)
        (shiftedBlockStart_add_le
          (N := articleRetainedCard T)
          (m := blockLength)
          (by norm_num [blockLength])
          r q)

/-! ## One residue family and all sliding blocks -/

/-- For one residue `r`, the disjoint shifted family costs at most the retained
Gram defect. -/
theorem article_one_shift_defect_le
    (T : ℝ)
    (hS : blockLength ≤ articleRetainedCard T)
    (r : Fin blockLength) :
    (∑ q :
        Fin ((articleRetainedCard T - r.1) / blockLength),
      consecutiveBlockDefect
        T
        (shiftedBlockStart r q)
        (shiftedBlockStart_add_le
          (N := articleRetainedCard T)
          (m := blockLength)
          (by norm_num [blockLength])
          r q))
      ≤ articleRetainedDefect T := by

  let hr :=
    residue_le_card hS r

  let Tail :=
    tailMatrix
      (articleRetainedGramFin T)
      r.1 hr

  let hTail :
      Tail.PosSemidef :=
    tailMatrix_posSemidef
      (articleRetainedGramFin T)
      (articleRetainedGramFin_posSemidef T)
      r.1 hr

  have hblocks :=
    sum_fullBlockDefect_le
      (N := articleRetainedCard T - r.1)
      (m := blockLength)
      (by norm_num [blockLength])
      Tail hTail

  have htail :
      gramSpectralDefect Tail hTail
        ≤
      gramSpectralDefect
        (articleRetainedGramFin T)
        (articleRetainedGramFin_posSemidef T) := by
    exact
      tailDefect_le
        (articleRetainedGramFin T)
        (articleRetainedGramFin_posSemidef T)
        r.1 hr

  have hfin :
      gramSpectralDefect
        (articleRetainedGramFin T)
        (articleRetainedGramFin_posSemidef T)
        =
      articleRetainedDefect T :=
    articleRetainedGramFin_defect_eq T

  calc
    (∑ q :
        Fin ((articleRetainedCard T - r.1) / blockLength),
      consecutiveBlockDefect
        T
        (shiftedBlockStart r q)
        (shiftedBlockStart_add_le
          (N := articleRetainedCard T)
          (m := blockLength)
          (by norm_num [blockLength])
          r q))
      =
    (∑ q :
        Fin ((articleRetainedCard T - r.1) / blockLength),
      fullBlockDefect
        blockLength
        (by norm_num [blockLength])
        Tail hTail q) := by
          apply Finset.sum_congr rfl
          intro q hq
          symm
          simpa [Tail, hTail, hr] using
            article_shifted_fullBlockDefect_eq
              T hS r q

    _ ≤ gramSpectralDefect Tail hTail := hblocks
    _ ≤
      gramSpectralDefect
        (articleRetainedGramFin T)
        (articleRetainedGramFin_posSemidef T) := htail
    _ = articleRetainedDefect T := hfin

/-- Sum of defects of *all* consecutive length-262 retained blocks is at most
`262 * D(M_retained)`. -/
theorem sum_all_consecutiveBlockDefect_le_retained
    (T : ℝ)
    (hS : blockLength ≤ articleRetainedCard T) :
    (∑ s : Fin
        (articleRetainedCard T - blockLength + 1),
      consecutiveBlockDefect
        T s.1
        (by
          have hs := s.2
          omega))
      ≤
    (blockLength : ℝ) * articleRetainedDefect T := by

  have hreindex :=
    sum_sliding_starts_eq_nested_shifted
      (N := articleRetainedCard T)
      (m := blockLength)
      (by norm_num [blockLength])
      hS
      (fun s : ℕ =>
        if hs : s + blockLength ≤ articleRetainedCard T then
          consecutiveBlockDefect T s hs
        else
          0)

  have hleft :
      (∑ s : Fin
          (articleRetainedCard T - blockLength + 1),
        (if hs : s.1 + blockLength ≤ articleRetainedCard T then
          consecutiveBlockDefect T s.1 hs
        else
          0))
      =
      (∑ s : Fin
          (articleRetainedCard T - blockLength + 1),
        consecutiveBlockDefect
          T s.1
          (by
            have hs := s.2
            omega)) := by
    apply Finset.sum_congr rfl
    intro s hs
    split
    · rename_i hfit
      exact
        gramSpectralDefect_eq_of_matrix_eq
          (consecutiveGramBlock_posSemidef T s.1 hfit)
          (consecutiveGramBlock_posSemidef T s.1 (by
            have hs' := s.2
            omega))
          rfl
    · rename_i hbad
      exfalso
      apply hbad
      have hs' := s.2
      omega

  have hright :
      (∑ r : Fin blockLength,
        ∑ q :
          Fin ((articleRetainedCard T - r.1) / blockLength),
          (if hs :
              r.1 + q.1 * blockLength + blockLength
                ≤ articleRetainedCard T
            then
              consecutiveBlockDefect
                T
                (r.1 + q.1 * blockLength)
                hs
            else
              0))
      =
      ∑ r : Fin blockLength,
        ∑ q :
          Fin ((articleRetainedCard T - r.1) / blockLength),
          consecutiveBlockDefect
            T
            (shiftedBlockStart r q)
            (shiftedBlockStart_add_le
              (N := articleRetainedCard T)
              (m := blockLength)
              (by norm_num [blockLength])
              r q) := by

    apply Finset.sum_congr rfl
    intro r hr

    apply Finset.sum_congr rfl
    intro q hq

    have hfit :=
      shiftedBlockStart_add_le
        (N := articleRetainedCard T)
        (m := blockLength)
        (by norm_num [blockLength])
        r q

    simp only [shiftedBlockStart] at hfit ⊢

    split
    · rename_i hfit'
      exact
        gramSpectralDefect_eq_of_matrix_eq
          (consecutiveGramBlock_posSemidef
            T
            (r.1 + q.1 * blockLength)
            hfit')
          (consecutiveGramBlock_posSemidef
            T
            (r.1 + q.1 * blockLength)
            hfit)
          rfl
    · rename_i hbad
      exact False.elim (hbad hfit)

  rw [hleft] at hreindex
  rw [hright] at hreindex

  rw [hreindex]

  calc
    (∑ r : Fin blockLength,
      ∑ q :
        Fin ((articleRetainedCard T - r.1) / blockLength),
        consecutiveBlockDefect
          T
          (shiftedBlockStart r q)
          (shiftedBlockStart_add_le
            (N := articleRetainedCard T)
            (m := blockLength)
            (by norm_num [blockLength])
            r q))
      ≤
    ∑ r : Fin blockLength,
      articleRetainedDefect T := by
        apply Finset.sum_le_sum
        intro r hr
        exact article_one_shift_defect_le T hS r

    _ = (blockLength : ℝ) * articleRetainedDefect T := by
      simp

/-- Published-form finite pinching inequality against the *global* stable
defect. -/
theorem sum_all_consecutiveBlockDefect_le_stable
    (T : ℝ)
    (hS : blockLength ≤ articleRetainedCard T) :
    (∑ s : Fin
        (articleRetainedCard T - blockLength + 1),
      consecutiveBlockDefect
        T s.1
        (by
          have hs := s.2
          omega))
      ≤
    (blockLength : ℝ) * articleStableDefect T := by

  calc
    _ ≤
      (blockLength : ℝ) * articleRetainedDefect T :=
        sum_all_consecutiveBlockDefect_le_retained T hS
    _ ≤
      (blockLength : ℝ) * articleStableDefect T := by
        exact
          mul_le_mul_of_nonneg_left
            (articleRetainedDefect_le_articleStableDefect T)
            (by positivity)

end HurtadoZeta23
