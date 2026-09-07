import HurtadoZeta23.RetainedGramFin
import HurtadoZeta23.GramPinchingFinitePartition
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

noncomputable section

open Matrix Finset
open scoped ComplexOrder BigOperators

namespace HurtadoZeta23

/-!
# Unshifted disjoint-block pinching on `Fin N`

For a PSD matrix indexed by `Fin N`, partition the first `⌊N/m⌋ * m`
indices into consecutive disjoint blocks of length `m`, leaving the final
remainder in a separate fiber.  Finite-partition Gram pinching then gives

  sum_q D(M[q*m : (q+1)*m]) ≤ D(M).

This is the reusable finite-dimensional core of shifted pinching.
-/

/-- Label an index by its full block quotient when that quotient corresponds
to a complete length-`m` block; otherwise send it to `none` (the final
remainder). -/
noncomputable def fullBlockPart
    (N m : ℕ) (hm : 1 ≤ m) :
    Fin N → Option (Fin (N / m)) := by
  classical
  exact fun i =>
    if h : i.1 / m < N / m then
      some ⟨i.1 / m, h⟩
    else
      none

lemma fullBlockPart_eq_some_iff
    (N m : ℕ) (hm : 1 ≤ m)
    (i : Fin N) (q : Fin (N / m)) :
    fullBlockPart N m hm i = some q
      ↔ i.1 / m = q.1 := by
  classical
  unfold fullBlockPart
  split
  · rename_i h
    constructor
    · intro heq
      have hfin :
          (⟨i.1 / m, h⟩ : Fin (N / m)) = q :=
        Option.some.inj heq
      exact congrArg Fin.val hfin
    · intro heq
      apply congrArg some
      apply Fin.ext
      exact heq
  · rename_i h
    constructor
    · intro hbad
      simp at hbad
    · intro hq
      exfalso
      apply h
      rw [hq]
      exact q.2

/-- The index `q*m+i` of local position `i` in complete block `q`. -/
def fullBlockEmbed
    (N m : ℕ) (hm : 1 ≤ m)
    (q : Fin (N / m)) (i : Fin m) :
    Fin N := by

  have hq1 :
      q.1 + 1 ≤ N / m :=
    Nat.succ_le_iff.mpr q.2

  have hmul :
      (q.1 + 1) * m ≤ (N / m) * m :=
    Nat.mul_le_mul_right m hq1

  have hdiv :
      (N / m) * m ≤ N :=
    Nat.div_mul_le_self N m

  refine ⟨q.1 * m + i.1, ?_⟩

  calc
    q.1 * m + i.1
        < q.1 * m + m :=
      Nat.add_lt_add_left i.2 (q.1 * m)
    _ = (q.1 + 1) * m := by
      rw [Nat.succ_mul]
    _ ≤ (N / m) * m := hmul
    _ ≤ N := hdiv

/-- The complete quotient fiber is canonically a `Fin m`. -/
noncomputable def fullBlockFiberEquiv
    (N m : ℕ) (hm : 1 ≤ m)
    (q : Fin (N / m)) :
    BlockFiber (fullBlockPart N m hm) (some q)
      ≃ Fin m where

  toFun z :=
    ⟨z.1.1 % m, by
      exact Nat.mod_lt _ (by omega)⟩

  invFun i :=
    ⟨fullBlockEmbed N m hm q i, by
      apply (fullBlockPart_eq_some_iff N m hm _ q).2
      change (q.1 * m + i.1) / m = q.1
      exact
        Nat.div_eq_of_lt_le
          (by
            exact Nat.le_add_right
              (q.1 * m) i.1)
          (by
            calc
              q.1 * m + i.1
                  < q.1 * m + m :=
                Nat.add_lt_add_left i.2 (q.1 * m)
              _ = (q.1 + 1) * m := by
                rw [Nat.succ_mul])⟩

  left_inv z := by
    apply Subtype.ext
    change
      fullBlockEmbed N m hm q
          ⟨z.1.1 % m, Nat.mod_lt _ (by omega)⟩
        =
      z.1
    apply Fin.ext
    change
      q.1 * m + z.1.1 % m = z.1.1
    have hq :
        z.1.1 / m = q.1 :=
      (fullBlockPart_eq_some_iff
        N m hm z.1 q).1 z.2
    rw [← hq]
    simpa [Nat.add_comm, Nat.mul_comm] using
      (Nat.mod_add_div z.1.1 m)

  right_inv i := by
    apply Fin.ext
    change
      (q.1 * m + i.1) % m = i.1
    rw [Nat.add_comm]
    simp [Nat.mod_eq_of_lt i.2]

/-- Complete block `q` as a principal submatrix. -/
def fullBlockMatrix
    {N : ℕ} (m : ℕ) (hm : 1 ≤ m)
    (M : Matrix (Fin N) (Fin N) ℂ)
    (q : Fin (N / m)) :
    Matrix (Fin m) (Fin m) ℂ :=
  M.submatrix
    (fullBlockEmbed N m hm q)
    (fullBlockEmbed N m hm q)

/-- Complete blocks of a PSD matrix remain PSD. -/
theorem fullBlockMatrix_posSemidef
    {N : ℕ} (m : ℕ) (hm : 1 ≤ m)
    (M : Matrix (Fin N) (Fin N) ℂ)
    (hM : M.PosSemidef)
    (q : Fin (N / m)) :
    (fullBlockMatrix m hm M q).PosSemidef := by
  exact
    principal_submatrix_posSemidef
      M hM (fullBlockEmbed N m hm q)

/-- Reindexing the quotient fiber gives the literal complete block. -/
theorem fullBlockFiber_reindex
    {N : ℕ} (m : ℕ) (hm : 1 ≤ m)
    (M : Matrix (Fin N) (Fin N) ℂ)
    (q : Fin (N / m)) :
    Matrix.reindex
        (fullBlockFiberEquiv N m hm q)
        (fullBlockFiberEquiv N m hm q)
        (finitePartitionBlock
          (fullBlockPart N m hm) M (some q))
      =
    fullBlockMatrix m hm M q := by
  ext i j
  rfl

/-- Spectral defect of complete block `q`. -/
noncomputable def fullBlockDefect
    {N : ℕ} (m : ℕ) (hm : 1 ≤ m)
    (M : Matrix (Fin N) (Fin N) ℂ)
    (hM : M.PosSemidef)
    (q : Fin (N / m)) :
    ℝ :=
  gramSpectralDefect
    (fullBlockMatrix m hm M q)
    (fullBlockMatrix_posSemidef m hm M hM q)

/-- The quotient-fiber defect equals the literal complete-block defect. -/
theorem fullBlockDefect_eq_partition
    {N : ℕ} (m : ℕ) (hm : 1 ≤ m)
    (M : Matrix (Fin N) (Fin N) ℂ)
    (hM : M.PosSemidef)
    (q : Fin (N / m)) :
    fullBlockDefect m hm M hM q
      =
    gramSpectralDefect
      (finitePartitionBlock
        (fullBlockPart N m hm) M (some q))
      (finitePartitionBlock_posSemidef
        (fullBlockPart N m hm) M hM (some q)) := by

  let B :=
    finitePartitionBlock
      (fullBlockPart N m hm) M (some q)

  let hB : B.PosSemidef :=
    finitePartitionBlock_posSemidef
      (fullBlockPart N m hm) M hM (some q)

  let e := fullBlockFiberEquiv N m hm q

  have hre :=
    gramSpectralDefect_reindex e B hB

  have hmat :
      Matrix.reindex e e B =
        fullBlockMatrix m hm M q := by
    simpa [B, e] using
      fullBlockFiber_reindex m hm M q

  unfold fullBlockDefect

  calc
    gramSpectralDefect
        (fullBlockMatrix m hm M q)
        (fullBlockMatrix_posSemidef m hm M hM q)
      =
    gramSpectralDefect
        (Matrix.reindex e e B)
        (posSemidef_reindex e B hB) := by
          exact
            (gramSpectralDefect_eq_of_matrix_eq
              (posSemidef_reindex e B hB)
              (fullBlockMatrix_posSemidef m hm M hM q)
              hmat).symm
    _ = gramSpectralDefect B hB := hre

/-- Sum of all disjoint complete length-`m` block defects is bounded by the
defect of the ambient PSD matrix. -/
theorem sum_fullBlockDefect_le
    {N m : ℕ} (hm : 1 ≤ m)
    (M : Matrix (Fin N) (Fin N) ℂ)
    (hM : M.PosSemidef) :
    (∑ q : Fin (N / m),
        fullBlockDefect m hm M hM q)
      ≤
    gramSpectralDefect M hM := by

  let part := fullBlockPart N m hm

  let labels :
      Finset (Option (Fin (N / m))) :=
    Finset.univ.image some

  have hp :=
    finitePartitionSubsetPinching_proved
      (S := labels) part M hM

  have hrewrite :
      (∑ b ∈ labels,
        gramSpectralDefect
          (finitePartitionBlock part M b)
          (finitePartitionBlock_posSemidef
            part M hM b))
        =
      ∑ q : Fin (N / m),
        gramSpectralDefect
          (finitePartitionBlock part M (some q))
          (finitePartitionBlock_posSemidef
            part M hM (some q)) := by

    dsimp [labels]

    rw [Finset.sum_image]
    intro a ha b hb hab
    exact Option.some.inj hab

  rw [hrewrite] at hp

  calc
    (∑ q : Fin (N / m),
        fullBlockDefect m hm M hM q)
      =
    ∑ q : Fin (N / m),
        gramSpectralDefect
          (finitePartitionBlock part M (some q))
          (finitePartitionBlock_posSemidef
            part M hM (some q)) := by
      apply Finset.sum_congr rfl
      intro q hq
      simpa [part] using
        fullBlockDefect_eq_partition
          m hm M hM q
    _ ≤ gramSpectralDefect M hM := hp

end HurtadoZeta23
