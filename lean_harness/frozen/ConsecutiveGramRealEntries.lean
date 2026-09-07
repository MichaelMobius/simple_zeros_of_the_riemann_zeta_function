import HurtadoZeta23.ConcreteBlockDefect
import Mathlib.Analysis.Complex.Norm
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Tactic

noncomputable section

open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators

namespace HurtadoZeta23

/-!
# Real entries of the consecutive simple Gram blocks

The sampled on-line vectors used by the article are real on the critical line.
Consequently every entry of the simple Gram matrix, and hence of every
consecutive retained principal block, is fixed by complex conjugation.

This file isolates that algebraic fact before the later pair-energy
reindexing.  In particular, for an actual consecutive Gram entry,

`‖G i j‖² = (G i j).re²`.

That is the exact scalar identity needed to identify the analytic real overlap
with the matrix off-diagonal energy.
-/

section AbstractRealSynthesis

variable {ι d : Type*}
variable [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d]

/-- Every entry of the simple on-line synthesis matrix is real. -/
lemma star_simpleOnLineSynthesis_apply
    (D : Zeta23.ZeroSide.ZeroBlockData ι d)
    (c : ℝ)
    (k : d)
    (z : SimpleOnLineColumn D) :
    star (simpleOnLineSynthesis D c k z)
      =
    simpleOnLineSynthesis D c k z := by

  have hv :
      star (D.v z.1 k) = D.v z.1 k :=
    conj_v_of_simpleOnLine D z k

  unfold simpleOnLineSynthesis

  rw [star_mul']
  rw [hv]

  simp only [
    Complex.star_def,
    Complex.conj_ofReal
  ]

end AbstractRealSynthesis

section ArticleRealSynthesis

/-- The article's concrete simple synthesis matrix has real entries. -/
lemma star_zeroSideSimpleSynthesis_apply
    (T : ℝ)
    (k : Fin ((articleParams.atD T).d T))
    (z : ArticleSimpleColumn T) :
    star
        (zeroSideSimpleSynthesis
          Zeta23.zetaZeroConfig
          (articleParams.atD T)
          T
          (articlePhiHatConj T)
          k z)
      =
        zeroSideSimpleSynthesis
          Zeta23.zetaZeroConfig
          (articleParams.atD T)
          T
          (articlePhiHatConj T)
          k z := by

  unfold zeroSideSimpleSynthesis

  exact
    star_simpleOnLineSynthesis_apply
      (ArticleBlockData T)
      ((articleParams.atD T).a T * (articleParams.atD T).L T ^ 2)
      k z

/-- Every entry of the global simple Gram matrix is real. -/
theorem star_articleGlobalSimpleGram_apply
    (T : ℝ)
    (i j : ArticleSimpleColumn T) :
    star (articleGlobalSimpleGram T i j)
      =
    articleGlobalSimpleGram T i j := by

  change
    star
      (zeroSideSimpleGram
        Zeta23.zetaZeroConfig
        (articleParams.atD T)
        T
        (articlePhiHatConj T)
        i j)
      =
    zeroSideSimpleGram
      Zeta23.zetaZeroConfig
      (articleParams.atD T)
      T
      (articlePhiHatConj T)
      i j

  unfold zeroSideSimpleGram

  simp only [
    Matrix.mul_apply,
    Matrix.conjTranspose_apply
  ]

  /-
  The displayed sum is already a `Fintype.sum`, definitionally a
  `Finset.univ.sum`.  `star_sum` rewrites it directly, so no explicit
  `change` is needed here.
  -/
  rw [star_sum]

  apply Finset.sum_congr rfl
  intro k hk

  have hi :=
    star_zeroSideSimpleSynthesis_apply T k i

  have hj :=
    star_zeroSideSimpleSynthesis_apply T k j

  rw [star_mul']
  simp only [star_star]
  rw [hi, hj]

/-- Every entry of an actual consecutive retained Gram block is real. -/
theorem star_consecutiveGramBlock_apply
    (T : ℝ)
    (s : ℕ)
    (hs : s + blockLength ≤ articleRetainedCard T)
    (i j : Fin blockLength) :
    star (consecutiveGramBlock T s hs i j)
      =
    consecutiveGramBlock T s hs i j := by

  rw [consecutiveGramBlock_apply]

  exact
    star_articleGlobalSimpleGram_apply
      T
      (consecutiveSimpleColumn T s hs i)
      (consecutiveSimpleColumn T s hs j)

/-- The imaginary part of every consecutive Gram entry vanishes. -/
theorem consecutiveGramBlock_im_eq_zero
    (T : ℝ)
    (s : ℕ)
    (hs : s + blockLength ≤ articleRetainedCard T)
    (i j : Fin blockLength) :
    (consecutiveGramBlock T s hs i j).im = 0 := by

  apply
    (Complex.im_eq_zero_iff_isSelfAdjoint
      (consecutiveGramBlock T s hs i j)).2

  exact
    (isSelfAdjoint_iff).2
      (star_consecutiveGramBlock_apply T s hs i j)

/-- For an actual consecutive Gram entry, norm-square is real-part-square. -/
theorem consecutiveGramBlock_norm_sq_eq_re_sq
    (T : ℝ)
    (s : ℕ)
    (hs : s + blockLength ≤ articleRetainedCard T)
    (i j : Fin blockLength) :
    ‖consecutiveGramBlock T s hs i j‖ ^ 2
      =
    (consecutiveGramBlock T s hs i j).re ^ 2 := by

  rw [Complex.sq_norm]
  rw [Complex.normSq_apply]
  rw [consecutiveGramBlock_im_eq_zero T s hs i j]

  ring

end ArticleRealSynthesis

/--
Natural-number interface for the real overlap carried by one consecutive
262-point Gram block.  Values outside the block are set to zero; only
`a,b < blockLength` are consumed by `globalPairEnergyNat`.
-/
noncomputable def consecutiveGramOverlapNat
    (T : ℝ)
    (s : ℕ)
    (hs : s + blockLength ≤ articleRetainedCard T)
    (a b : ℕ) :
    ℝ :=
  if ha : a < blockLength then
    if hb : b < blockLength then
      (consecutiveGramBlock T s hs ⟨a, ha⟩ ⟨b, hb⟩).re
    else
      0
  else
    0

@[simp] theorem consecutiveGramOverlapNat_eq
    (T : ℝ)
    (s : ℕ)
    (hs : s + blockLength ≤ articleRetainedCard T)
    {a b : ℕ}
    (ha : a < blockLength)
    (hb : b < blockLength) :
    consecutiveGramOverlapNat T s hs a b
      =
    (consecutiveGramBlock T s hs ⟨a, ha⟩ ⟨b, hb⟩).re := by

  simp [consecutiveGramOverlapNat, ha, hb]

/--
On every in-range pair, the square of the real overlap is exactly the squared
norm of the corresponding Gram entry.
-/
theorem consecutiveGramOverlapNat_sq_eq_norm_sq
    (T : ℝ)
    (s : ℕ)
    (hs : s + blockLength ≤ articleRetainedCard T)
    {a b : ℕ}
    (ha : a < blockLength)
    (hb : b < blockLength) :
    consecutiveGramOverlapNat T s hs a b ^ 2
      =
    ‖consecutiveGramBlock T s hs ⟨a, ha⟩ ⟨b, hb⟩‖ ^ 2 := by

  rw [consecutiveGramOverlapNat_eq T s hs ha hb]

  symm

  exact
    consecutiveGramBlock_norm_sq_eq_re_sq
      T s hs ⟨a, ha⟩ ⟨b, hb⟩

end HurtadoZeta23
