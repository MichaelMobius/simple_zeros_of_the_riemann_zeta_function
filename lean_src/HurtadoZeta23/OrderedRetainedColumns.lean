import HurtadoZeta23.ConcreteRetainedCore
import HurtadoZeta23.PrincipalGramBlocks
import Mathlib.Data.Fintype.Sort
import Mathlib.Tactic

noncomputable section

open Matrix Finset
open scoped BigOperators

namespace HurtadoZeta23

/-!
# Ordered retained simple columns

The article's shifted-block argument needs the simple critical-line columns to
be placed in increasing ordinate order.  This file supplies that order
canonically.

The key point is elementary but important: two simple critical-line zeros with
the same ordinate are the same complex number, because both have real part
`1/2`.  Hence the imaginary-part map is injective on the simple-column type,
so we can pull back the linear order of `ℝ`.
-/

/-- The concrete zero-side block data at the article endpoint `λ = 1`. -/
abbrev ArticleBlockData (T : ℝ) :=
  Zeta23.ZeroSide.blockData
    Zeta23.zetaZeroConfig
    T
    (articleParams.atD T)
    (articlePhiHatConj T)

/-- Global simple critical-line columns of the article Gram matrix. -/
abbrev ArticleSimpleColumn (T : ℝ) :=
  SimpleOnLineColumn (ArticleBlockData T)

/-- The complex zero represented by a simple Gram column. -/
def articleColumnZero {T : ℝ} (z : ArticleSimpleColumn T) : ℂ :=
  z.1.1

/-- Every article simple column lies on the critical line. -/
theorem articleSimpleColumn_re_half
    {T : ℝ} (z : ArticleSimpleColumn T) :
    (articleColumnZero z).re = 1 / 2 := by

  have hz := z.2
  simp only [
    Zeta23.ZeroSide.ZeroBlockData.S₁,
    Finset.mem_filter,
    Finset.mem_univ,
    true_and
  ] at hz

  have hsigma :
      (ArticleBlockData T).σ z.1 = z.1 :=
    hz.1

  change
    (Zeta23.ZeroSide.mkData
      Zeta23.zetaZeroConfig T
      (Zeta23.ZeroSide.evalVec
        Zeta23.zetaZeroConfig T (articleParams.atD T))
      (Zeta23.ZeroSide.evalVec_reflect
        (Z := Zeta23.zetaZeroConfig)
        (T := T)
        (P := articleParams.atD T)
        (articlePhiHatConj T))).σ z.1 = z.1
    at hsigma

  rw [Zeta23.ZeroSide.mkData_σ_eq_iff] at hsigma

  simpa [articleColumnZero] using hsigma

/-- Every article simple column has multiplicity exactly one in the zeta zero
configuration. -/
theorem articleSimpleColumn_mult_one
    {T : ℝ} (z : ArticleSimpleColumn T) :
    Zeta23.zetaZeroConfig.mult (articleColumnZero z) = 1 := by

  have hm :=
    mult_eq_one_of_mem_S₁
      (ArticleBlockData T)
      z.2

  change
    (Zeta23.ZeroSide.mkData
      Zeta23.zetaZeroConfig T
      (Zeta23.ZeroSide.evalVec
        Zeta23.zetaZeroConfig T (articleParams.atD T))
      (Zeta23.ZeroSide.evalVec_reflect
        (Z := Zeta23.zetaZeroConfig)
        (T := T)
        (P := articleParams.atD T)
        (articlePhiHatConj T))).m z.1 = 1
    at hm

  rw [Zeta23.ZeroSide.mkData_m] at hm

  simpa [articleColumnZero] using hm

/-- On simple critical-line columns the ordinate map is injective. -/
theorem articleSimpleColumn_im_injective
    (T : ℝ) :
    Function.Injective
      (fun z : ArticleSimpleColumn T =>
        (articleColumnZero z).im) := by

  intro a b hab

  apply Subtype.ext
  apply Subtype.ext
  apply Complex.ext

  ·
    change
      (articleColumnZero a).re =
        (articleColumnZero b).re
    rw [
      articleSimpleColumn_re_half a,
      articleSimpleColumn_re_half b
    ]

  ·
    change
      (articleColumnZero a).im =
        (articleColumnZero b).im
    exact hab

/-- Canonical linear order on simple columns: increasing imaginary part. -/
noncomputable instance articleSimpleColumnLinearOrder
    (T : ℝ) :
    LinearOrder (ArticleSimpleColumn T) :=
  LinearOrder.lift'
    (fun z : ArticleSimpleColumn T =>
      (articleColumnZero z).im)
    (articleSimpleColumn_im_injective T)

/-- The retained simple columns are literally the columns whose underlying zero
belongs to the concrete central retained set. -/
noncomputable def articleRetainedColumnsFinset
    (T : ℝ) :
    Finset (ArticleSimpleColumn T) := by
  classical
  exact
    Finset.univ.filter
      (fun z =>
        articleColumnZero z ∈
          retainedSimpleCriticalSet T)

/-- Type of retained simple Gram columns. -/
abbrev ArticleRetainedColumn (T : ℝ) :=
  {z : ArticleSimpleColumn T //
    z ∈ articleRetainedColumnsFinset T}

/-- Membership in the retained-column type exposes the literal retained-zero
predicate. -/
theorem articleRetainedColumn_mem
    {T : ℝ} (z : ArticleRetainedColumn T) :
    articleColumnZero z.1 ∈
      retainedSimpleCriticalSet T := by
  classical
  have hz := z.2
  simp only [
    articleRetainedColumnsFinset,
    Finset.mem_filter,
    Finset.mem_univ,
    true_and
  ] at hz
  exact hz

/-- Increasing enumeration of all retained simple columns. -/
noncomputable def articleRetainedOrderIso
    (T : ℝ) :
    Fin (Fintype.card (ArticleRetainedColumn T))
      ≃o
    ArticleRetainedColumn T :=
  Fintype.orderIsoFinOfCardEq
    (ArticleRetainedColumn T)
    rfl

/-- The retained simple column of rank `i` in increasing ordinate order. -/
noncomputable def orderedRetainedColumn
    (T : ℝ)
    (i : Fin (Fintype.card (ArticleRetainedColumn T))) :
    ArticleSimpleColumn T :=
  (articleRetainedOrderIso T i).1

/-- The actual zeta zero at retained rank `i`. -/
noncomputable def orderedRetainedZero
    (T : ℝ)
    (i : Fin (Fintype.card (ArticleRetainedColumn T))) :
    ℂ :=
  articleColumnZero (orderedRetainedColumn T i)

/-- The order isomorphism really enumerates by nondecreasing ordinate. -/
theorem orderedRetainedZero_im_mono
    {T : ℝ}
    {i j : Fin (Fintype.card (ArticleRetainedColumn T))}
    (hij : i ≤ j) :
    (orderedRetainedZero T i).im
      ≤
    (orderedRetainedZero T j).im := by

  have hcol :
      articleRetainedOrderIso T i
        ≤
      articleRetainedOrderIso T j :=
    (articleRetainedOrderIso T).monotone hij

  change
    (articleColumnZero
      (articleRetainedOrderIso T i).1).im
      ≤
    (articleColumnZero
      (articleRetainedOrderIso T j).1).im
    at hcol

  simpa [
    orderedRetainedZero,
    orderedRetainedColumn
  ] using hcol

/-- Normalized ordinate used by the limiting kernel:
`y = L(γ-T)/(2π)`. -/
noncomputable def orderedRetainedY
    (T : ℝ)
    (i : Fin (Fintype.card (ArticleRetainedColumn T))) :
    ℝ :=
  articleParams.L T *
    ((orderedRetainedZero T i).im - T) /
      (2 * Real.pi)

/-- For positive `L`, normalized retained ordinates are ordered as well. -/
theorem orderedRetainedY_mono
    {T : ℝ}
    (hL : 0 ≤ articleParams.L T)
    {i j : Fin (Fintype.card (ArticleRetainedColumn T))}
    (hij : i ≤ j) :
    orderedRetainedY T i ≤
      orderedRetainedY T j := by

  have him :=
    orderedRetainedZero_im_mono
      (T := T) hij

  have hpi :
      0 < 2 * Real.pi := by
    positivity

  unfold orderedRetainedY

  have hsub :
      (orderedRetainedZero T i).im - T
        ≤
      (orderedRetainedZero T j).im - T := by
    linarith

  have hmul :
      articleParams.L T *
          ((orderedRetainedZero T i).im - T)
        ≤
      articleParams.L T *
          ((orderedRetainedZero T j).im - T) :=
    mul_le_mul_of_nonneg_left hsub hL

  exact
    (div_le_div_iff_of_pos_right hpi).2 hmul

end HurtadoZeta23
