import HurtadoZeta23.GramPinchingBlockDiagonal
import Mathlib.Data.Finset.Card
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic

noncomputable section

open Matrix Finset
open scoped ComplexOrder BigOperators

universe u v w

namespace HurtadoZeta23

/-!
# Finite-partition iteration

The matrix-analytic input has already been closed in
`gramDefectPinching_bool_proved`.  This file performs only finite bookkeeping.

The proof below is intentionally shorter than the earlier experimental version:
we prove the inequality for an arbitrary finite subset `S` of labels and
induct on `S`.  In the induction step one label `b` is split off by the Boolean
pinching theorem, and the induction hypothesis is applied to the complementary
principal submatrix.

No asymptotic or zeta-function input occurs here.
-/

/-! ## Principal blocks -/

section Blocks

variable {ι : Type u} {β : Type v}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype β] [DecidableEq β]

/-- Principal block indexed by one fiber of a finite labeling. -/
def finitePartitionBlock (part : ι → β) (M : Matrix ι ι ℂ) (b : β) :
    Matrix {i : ι // part i = b} {i : ι // part i = b} ℂ :=
  M.submatrix Subtype.val Subtype.val

theorem finitePartitionBlock_posSemidef
    (part : ι → β) (M : Matrix ι ι ℂ) (hM : M.PosSemidef) (b : β) :
    (finitePartitionBlock part M b).PosSemidef := by
  exact principal_submatrix_posSemidef M hM
    (fun i : {i : ι // part i = b} => i.1)

/-- Every Gram spectral defect of a PSD matrix is nonnegative. -/
theorem gramSpectralDefect_nonneg
    (M : Matrix ι ι ℂ) (hM : M.PosSemidef) :
    0 ≤ gramSpectralDefect M hM := by
  unfold gramSpectralDefect
  rw [← RHLinalg.sum_eigenvalues_reindex hM.isHermitian psi]
  apply Finset.sum_nonneg
  intro i hi
  exact psi_nonneg_of_nonneg (hM.eigenvalues_nonneg i)

end Blocks

/-! ## Reindex invariance -/

section Reindex

variable {ι : Type u} {κ : Type w}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype κ] [DecidableEq κ]

/-- PSD is preserved by simultaneous reindexing. -/
theorem posSemidef_reindex
    (e : ι ≃ κ) (M : Matrix ι ι ℂ) (hM : M.PosSemidef) :
    (Matrix.reindex e e M).PosSemidef := by
  rw [Matrix.reindex_apply]
  exact hM.submatrix e.symm

/-- The Gram spectral defect is invariant under a finite change of index type. -/
theorem gramSpectralDefect_reindex
    (e : ι ≃ κ) (M : Matrix ι ι ℂ) (hM : M.PosSemidef) :
    gramSpectralDefect
        (Matrix.reindex e e M)
        (posSemidef_reindex e M hM)
      =
    gramSpectralDefect M hM := by
  have hr1 :=
    rootsPsiGramBridge_proved
      (Matrix.reindex e e M) (posSemidef_reindex e M hM)
  have hr2 := rootsPsiGramBridge_proved M hM
  rw [← hr1, ← hr2]
  unfold rootsPsiSum
  rw [Matrix.charpoly_reindex e M]

end Reindex

/-! ## One label versus its complement -/

section OneBlock

variable {ι : Type u} {β : Type v}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype β] [DecidableEq β]

/-- Boolean label that isolates one fiber. -/
def isolateLabel (part : ι → β) (b : β) : ι → Bool :=
  fun i => decide (part i = b)

/-- The true Boolean fiber is the original `b`-fiber. -/
def trueFiberEquivPartition (part : ι → β) (b : β) :
    BlockFiber (isolateLabel part b) true ≃ {i : ι // part i = b} where
  toFun i := ⟨i.1, by
    have hi : decide (part i.1 = b) = true := by
      simpa [isolateLabel] using i.2
    simpa using hi⟩
  invFun i := ⟨i.1, by
    simp [isolateLabel, i.2]⟩
  left_inv i := by
    apply Subtype.ext
    rfl
  right_inv i := by
    apply Subtype.ext
    rfl

/-- The false Boolean fiber is the complement subtype. -/
def falseFiberEquivPartition (part : ι → β) (b : β) :
    BlockFiber (isolateLabel part b) false ≃ {i : ι // part i ≠ b} where
  toFun i := ⟨i.1, by
    have hi : decide (part i.1 = b) = false := by
      simpa [isolateLabel] using i.2
    simpa using hi⟩
  invFun i := ⟨i.1, by
    simp [isolateLabel, i.2]⟩
  left_inv i := by
    apply Subtype.ext
    rfl
  right_inv i := by
    apply Subtype.ext
    rfl

/-- Reindexing the true Boolean block gives the original `b` block. -/
theorem trueFiberBlock_reindex
    (part : ι → β) (b : β) (M : Matrix ι ι ℂ) :
    Matrix.reindex (trueFiberEquivPartition part b)
        (trueFiberEquivPartition part b)
        (partitionBlock (isolateLabel part b) M true)
      =
    finitePartitionBlock part M b := by
  ext i j
  rfl

/-- Reindexing the false Boolean block gives the complementary principal
submatrix. -/
theorem falseFiberBlock_reindex
    (part : ι → β) (b : β) (M : Matrix ι ι ℂ) :
    Matrix.reindex (falseFiberEquivPartition part b)
        (falseFiberEquivPartition part b)
        (partitionBlock (isolateLabel part b) M false)
      =
    M.submatrix
      (fun i : {i : ι // part i ≠ b} => i.1)
      (fun i : {i : ι // part i ≠ b} => i.1) := by
  ext i j
  rfl

/-- Exact one-block/complement inequality used by the finite induction. -/
def OneBlockComplementDefectSplit : Prop :=
  ∀ {ι : Type u} {β : Type v}
      [Fintype ι] [DecidableEq ι]
      [Fintype β] [DecidableEq β]
      (part : ι → β) (b : β)
      (M : Matrix ι ι ℂ) (hM : M.PosSemidef),
    let Mc :=
      M.submatrix
        (fun i : {i : ι // part i ≠ b} => i.1)
        (fun i : {i : ι // part i ≠ b} => i.1)
    let hMc : Mc.PosSemidef :=
      principal_submatrix_posSemidef M hM
        (fun i : {i : ι // part i ≠ b} => i.1)
    gramSpectralDefect
        (finitePartitionBlock part M b)
        (finitePartitionBlock_posSemidef part M hM b)
      + gramSpectralDefect Mc hMc
      ≤ gramSpectralDefect M hM

/-- The one-block/complement split is the already-proved Boolean theorem,
transported along the two fiber equivalences. -/
theorem oneBlockComplementDefectSplit_proved :
    OneBlockComplementDefectSplit.{u, v} := by
  intro ι β _ _ _ _ part b M hM

  let label : ι → Bool := isolateLabel part b

  let Mt : Matrix (BlockFiber label true) (BlockFiber label true) ℂ :=
    partitionBlock label M true
  let Mf : Matrix (BlockFiber label false) (BlockFiber label false) ℂ :=
    partitionBlock label M false

  let hMt : Mt.PosSemidef :=
    principal_submatrix_posSemidef M hM
      (fun i : BlockFiber label true => i.1)
  let hMf : Mf.PosSemidef :=
    principal_submatrix_posSemidef M hM
      (fun i : BlockFiber label false => i.1)

  let Mc :=
    M.submatrix
      (fun i : {i : ι // part i ≠ b} => i.1)
      (fun i : {i : ι // part i ≠ b} => i.1)
  let hMc : Mc.PosSemidef :=
    principal_submatrix_posSemidef M hM
      (fun i : {i : ι // part i ≠ b} => i.1)

  have hpinch :=
    gramDefectPinching_bool_proved label M hM
  unfold GramDefectPinchingPartition at hpinch
  rw [Fintype.sum_bool] at hpinch

  have htrue :
      gramSpectralDefect Mt hMt =
        gramSpectralDefect
          (finitePartitionBlock part M b)
          (finitePartitionBlock_posSemidef part M hM b) := by
    let e := trueFiberEquivPartition part b
    have hre := gramSpectralDefect_reindex e Mt hMt
    have hmat :
        Matrix.reindex e e Mt = finitePartitionBlock part M b := by
      simpa [e, Mt, label] using trueFiberBlock_reindex part b M
    calc
      gramSpectralDefect Mt hMt
          =
        gramSpectralDefect
          (Matrix.reindex e e Mt)
          (posSemidef_reindex e Mt hMt) := hre.symm
      _ =
        gramSpectralDefect
          (finitePartitionBlock part M b)
          (finitePartitionBlock_posSemidef part M hM b) := by
            exact gramSpectralDefect_eq_of_matrix_eq
              (posSemidef_reindex e Mt hMt)
              (finitePartitionBlock_posSemidef part M hM b)
              hmat

  have hfalse :
      gramSpectralDefect Mf hMf =
        gramSpectralDefect Mc hMc := by
    let e := falseFiberEquivPartition part b
    have hre := gramSpectralDefect_reindex e Mf hMf
    have hmat : Matrix.reindex e e Mf = Mc := by
      simpa [e, Mf, Mc, label] using falseFiberBlock_reindex part b M
    calc
      gramSpectralDefect Mf hMf
          =
        gramSpectralDefect
          (Matrix.reindex e e Mf)
          (posSemidef_reindex e Mf hMf) := hre.symm
      _ = gramSpectralDefect Mc hMc := by
            exact gramSpectralDefect_eq_of_matrix_eq
              (posSemidef_reindex e Mf hMf)
              hMc
              hmat

  have htrue' :
      gramSpectralDefect
          (partitionBlock (isolateLabel part b) M true)
          (principal_submatrix_posSemidef M hM
            (fun i : BlockFiber (isolateLabel part b) true => i.1))
        =
      gramSpectralDefect
          (finitePartitionBlock part M b)
          (finitePartitionBlock_posSemidef part M hM b) := by
    simpa [Mt, hMt, label] using htrue

  have hfalse' :
      gramSpectralDefect
          (partitionBlock (isolateLabel part b) M false)
          (principal_submatrix_posSemidef M hM
            (fun i : BlockFiber (isolateLabel part b) false => i.1))
        =
      gramSpectralDefect
          (M.submatrix
            (fun i : {i : ι // part i ≠ b} => i.1)
            (fun i : {i : ι // part i ≠ b} => i.1))
          (principal_submatrix_posSemidef M hM
            (fun i : {i : ι // part i ≠ b} => i.1)) := by
    simpa [Mf, hMf, Mc, hMc, label] using hfalse

  dsimp [label] at hpinch
  dsimp [Mc, hMc]

  calc
    gramSpectralDefect
          (finitePartitionBlock part M b)
          (finitePartitionBlock_posSemidef part M hM b)
        +
      gramSpectralDefect
          (M.submatrix
            (fun i : {i : ι // part i ≠ b} => i.1)
            (fun i : {i : ι // part i ≠ b} => i.1))
          (principal_submatrix_posSemidef M hM
            (fun i : {i : ι // part i ≠ b} => i.1))
      =
    gramSpectralDefect
          (partitionBlock (isolateLabel part b) M true)
          (principal_submatrix_posSemidef M hM
            (fun i : BlockFiber (isolateLabel part b) true => i.1))
        +
      gramSpectralDefect
          (partitionBlock (isolateLabel part b) M false)
          (principal_submatrix_posSemidef M hM
            (fun i : BlockFiber (isolateLabel part b) false => i.1)) := by
              rw [htrue', hfalse']
    _ ≤ gramSpectralDefect M hM := hpinch

end OneBlock

/-! ## Complement fibers for the recursive call -/

section Complement

variable {ι : Type u} {β : Type v}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype β] [DecidableEq β]

/-- Keep the ambient label type `β`, but restrict the index set away from `b`. -/
def complementPartSame (part : ι → β) (b : β) :
    {i : ι // part i ≠ b} → β :=
  fun i => part i.1

/-- For `c ≠ b`, a `c`-fiber inside the complement is equivalent to the
original `c`-fiber. -/
def complementFiberEquivSame
    (part : ι → β) (b c : β) (hcb : c ≠ b) :
    {i : {j : ι // part j ≠ b} // complementPartSame part b i = c}
      ≃ {i : ι // part i = c} where
  toFun i := ⟨i.1.1, i.2⟩
  invFun i :=
    ⟨⟨i.1, by
        intro hib
        exact hcb (i.2.symm.trans hib)⟩,
      i.2⟩
  left_inv i := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv i := by
    apply Subtype.ext
    rfl

/-- The recursive `c` block is the original `c` block after reindexing. -/
theorem complementFiberBlock_reindex_same
    (part : ι → β) (b c : β) (hcb : c ≠ b)
    (M : Matrix ι ι ℂ) :
    let Mc :=
      M.submatrix
        (fun i : {i : ι // part i ≠ b} => i.1)
        (fun i : {i : ι // part i ≠ b} => i.1)
    Matrix.reindex (complementFiberEquivSame part b c hcb)
        (complementFiberEquivSame part b c hcb)
        (finitePartitionBlock (complementPartSame part b) Mc c)
      =
    finitePartitionBlock part M c := by
  dsimp [finitePartitionBlock, complementPartSame]
  ext i j
  rfl

end Complement

/-! ## Finite-set induction -/

/-- The stronger subset statement.  Proving this makes the full partition
theorem an immediate specialization to `Finset.univ`. -/
def FinitePartitionSubsetPinching : Prop :=
  ∀ {β : Type v} [Fintype β] [DecidableEq β] (S : Finset β),
    ∀ {ι : Type u} [Fintype ι] [DecidableEq ι]
        (part : ι → β) (M : Matrix ι ι ℂ) (hM : M.PosSemidef),
      (∑ b ∈ S,
        gramSpectralDefect
          (finitePartitionBlock part M b)
          (finitePartitionBlock_posSemidef part M hM b))
        ≤ gramSpectralDefect M hM

/-- The finite subset inequality follows by repeatedly isolating one label. -/
theorem finitePartitionSubsetPinching_proved :
    FinitePartitionSubsetPinching.{u, v} := by
  intro β _ _ S
  induction S using Finset.induction_on with
  | empty =>
      intro ι _ _ part M hM
      simp only [Finset.sum_empty]
      exact gramSpectralDefect_nonneg M hM
  | @insert b S hb ih =>
      intro ι _ _ part M hM

      let Ic := {i : ι // part i ≠ b}
      let Mc : Matrix Ic Ic ℂ :=
        M.submatrix
          (fun i : Ic => i.1)
          (fun i : Ic => i.1)
      let hMc : Mc.PosSemidef :=
        principal_submatrix_posSemidef M hM
          (fun i : Ic => i.1)
      let partC : Ic → β :=
        complementPartSame part b

      have hrec0 :
          (∑ c ∈ S,
            gramSpectralDefect
              (finitePartitionBlock partC Mc c)
              (finitePartitionBlock_posSemidef partC Mc hMc c))
            ≤ gramSpectralDefect Mc hMc := by
        exact ih partC Mc hMc

      have hsum :
          (∑ c ∈ S,
            gramSpectralDefect
              (finitePartitionBlock partC Mc c)
              (finitePartitionBlock_posSemidef partC Mc hMc c))
          =
          (∑ c ∈ S,
            gramSpectralDefect
              (finitePartitionBlock part M c)
              (finitePartitionBlock_posSemidef part M hM c)) := by
        apply Finset.sum_congr rfl
        intro c hcS
        have hcb : c ≠ b := by
          intro h
          subst c
          exact hb hcS
        let e := complementFiberEquivSame part b c hcb
        have hre :=
          gramSpectralDefect_reindex e
            (finitePartitionBlock partC Mc c)
            (finitePartitionBlock_posSemidef partC Mc hMc c)
        have hmat :
            Matrix.reindex e e (finitePartitionBlock partC Mc c) =
              finitePartitionBlock part M c := by
          simpa [e, partC, Mc, Ic] using
            complementFiberBlock_reindex_same part b c hcb M
        calc
          gramSpectralDefect
              (finitePartitionBlock partC Mc c)
              (finitePartitionBlock_posSemidef partC Mc hMc c)
            =
          gramSpectralDefect
              (Matrix.reindex e e (finitePartitionBlock partC Mc c))
              (posSemidef_reindex e
                (finitePartitionBlock partC Mc c)
                (finitePartitionBlock_posSemidef partC Mc hMc c)) := hre.symm
          _ =
          gramSpectralDefect
              (finitePartitionBlock part M c)
              (finitePartitionBlock_posSemidef part M hM c) := by
                exact gramSpectralDefect_eq_of_matrix_eq
                  (posSemidef_reindex e
                    (finitePartitionBlock partC Mc c)
                    (finitePartitionBlock_posSemidef partC Mc hMc c))
                  (finitePartitionBlock_posSemidef part M hM c)
                  hmat

      have hrec :
          (∑ c ∈ S,
            gramSpectralDefect
              (finitePartitionBlock part M c)
              (finitePartitionBlock_posSemidef part M hM c))
            ≤ gramSpectralDefect Mc hMc := by
        rw [← hsum]
        exact hrec0

      have hsplit0 :=
        oneBlockComplementDefectSplit_proved
          (part := part) (b := b) M hM

      have hsplit :
          gramSpectralDefect
              (finitePartitionBlock part M b)
              (finitePartitionBlock_posSemidef part M hM b)
            + gramSpectralDefect Mc hMc
            ≤ gramSpectralDefect M hM := by
        simpa [Mc, hMc, Ic] using hsplit0

      rw [Finset.sum_insert hb]
      exact
        (add_le_add_right hrec
          (gramSpectralDefect
            (finitePartitionBlock part M b)
            (finitePartitionBlock_posSemidef part M hM b))).trans hsplit

/-- Target finite-partition theorem. -/
def FinitePartitionGramPinching : Prop :=
  ∀ {ι : Type u} {β : Type v}
      [Fintype ι] [DecidableEq ι]
      [Fintype β] [DecidableEq β]
      (part : ι → β) (M : Matrix ι ι ℂ) (hM : M.PosSemidef),
    (∑ b : β,
      gramSpectralDefect
        (finitePartitionBlock part M b)
        (finitePartitionBlock_posSemidef part M hM b))
      ≤ gramSpectralDefect M hM

/-- Full finite-partition pinching, obtained by taking `S = univ`. -/
theorem finitePartitionGramPinching_proved :
    FinitePartitionGramPinching.{u, v} := by
  intro ι β _ _ _ _ part M hM
  simpa using
    (finitePartitionSubsetPinching_proved
      (S := (Finset.univ : Finset β)) part M hM)

/-- Compatibility wrapper matching the older interface. -/
def FinitePartitionInductionStep : Prop :=
  ∀ {ι : Type u} {β : Type v}
      [Fintype ι] [DecidableEq ι]
      [Fintype β] [DecidableEq β]
      (part : ι → β) (M : Matrix ι ι ℂ) (hM : M.PosSemidef)
      (S : Finset β),
    (∑ b ∈ S,
      gramSpectralDefect
        (finitePartitionBlock part M b)
        (finitePartitionBlock_posSemidef part M hM b))
      ≤ gramSpectralDefect M hM

theorem finitePartitionInductionStep_proved :
    FinitePartitionInductionStep.{u, v} := by
  intro ι β _ _ _ _ part M hM S
  exact finitePartitionSubsetPinching_proved S part M hM

theorem finitePartitionGramPinching_of_induction
    (hind : FinitePartitionInductionStep.{u, v}) :
    FinitePartitionGramPinching.{u, v} := by
  intro ι β _ _ _ _ part M hM
  simpa using hind part M hM (Finset.univ : Finset β)

end HurtadoZeta23
