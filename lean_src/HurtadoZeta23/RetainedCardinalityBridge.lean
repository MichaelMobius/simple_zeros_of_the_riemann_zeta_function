import HurtadoZeta23.ShiftedRetainedPinching
import Zeta23.Statement.SeamClosed
import Mathlib.Tactic

noncomputable section

open Matrix Finset Set
open scoped BigOperators

namespace HurtadoZeta23

/-!
# Retained-cardinality bridge

The shifted finite argument is indexed by `ArticleRetainedColumn T`, whereas
the asymptotic retained-count package is defined by the literal set
`retainedSimpleCriticalSet T`.

This file proves that these are exactly the same finite set, not merely
asymptotically comparable.
-/

/-- The literal retained simple-zero set as a `Finset`. -/
noncomputable def retainedSimpleCriticalFinset (T : ℝ) : Finset ℂ :=
  (retainedSimpleCriticalSet_finite T).toFinset

@[simp] theorem mem_retainedSimpleCriticalFinset
    {T : ℝ} {ρ : ℂ} :
    ρ ∈ retainedSimpleCriticalFinset T
      ↔ ρ ∈ retainedSimpleCriticalSet T := by
  exact Set.Finite.mem_toFinset _

/-- A retained Gram column determines its underlying retained zeta zero. -/
noncomputable def retainedColumnToZero
    (T : ℝ) :
    ArticleRetainedColumn T →
      ↥(retainedSimpleCriticalFinset T) :=
  fun z =>
    ⟨articleColumnZero z.1,
      (mem_retainedSimpleCriticalFinset).2
        (articleRetainedColumn_mem z)⟩

/-- A literal retained simple critical-line zero belongs to the enlarged
zero-side index set `ZI`, hence gives a simple Gram column. -/
noncomputable def retainedZeroToColumn
    (T : ℝ) :
    ↥(retainedSimpleCriticalFinset T) →
      ArticleRetainedColumn T := by

  intro ρ

  have hret :
      (ρ.1 : ℂ) ∈ retainedSimpleCriticalSet T :=
    (mem_retainedSimpleCriticalFinset).1 ρ.2

  have hdy :
      (ρ.1 : ℂ) ∈ dyadicSimpleCriticalSet T :=
    hret.1

  have hzero :
      (ρ.1 : ℂ) ∈ Zeta23.zerosIn T (2 * T) :=
    hdy.1.1

  have hre :
      (ρ.1 : ℂ).re = 1 / 2 :=
    hdy.1.2

  have hmult :
      Zeta23.zeroMult (ρ.1 : ℂ) = 1 :=
    hdy.2

  have hD0 :
      0 ≤ Zeta23.D0 T := by
    unfold Zeta23.D0
    positivity

  have hZIprime :
      (ρ.1 : ℂ) ∈
        Zeta23.zetaZeroConfig.ZIprime T := by

    rw [
      Zeta23.ZeroSide.mem_ZIprime_iff
        Zeta23.zetaZeroConfig T
    ]

    constructor

    ·
      simpa using hzero.1

    ·
      constructor

      ·
        have hlo := hzero.2.1
        linarith

      ·
        have hhi := hzero.2.2
        linarith

  have hZI :
      (ρ.1 : ℂ) ∈
        Zeta23.ZeroSide.ZI
          Zeta23.zetaZeroConfig T := by
    exact
      (Zeta23.ZeroSide.mem_ZI
        Zeta23.zetaZeroConfig T).2 hZIprime

  let z0 :
      Zeta23.ZeroSide.ZI
        Zeta23.zetaZeroConfig T :=
    ⟨ρ.1, hZI⟩

  have hs1 :
      z0 ∈ (ArticleBlockData T).S₁ := by

    simp only [
      Zeta23.ZeroSide.ZeroBlockData.S₁,
      Finset.mem_filter,
      Finset.mem_univ,
      true_and
    ]

    constructor

    ·
      change
        (Zeta23.ZeroSide.mkData
          Zeta23.zetaZeroConfig T
          (Zeta23.ZeroSide.evalVec
            Zeta23.zetaZeroConfig T
            (articleParams.atD T))
          (Zeta23.ZeroSide.evalVec_reflect
            (Z := Zeta23.zetaZeroConfig)
            (T := T)
            (P := articleParams.atD T)
            (articlePhiHatConj T))).σ z0
          =
        z0

      rw [Zeta23.ZeroSide.mkData_σ_eq_iff]

      exact hre

    ·
      change
        (Zeta23.ZeroSide.mkData
          Zeta23.zetaZeroConfig T
          (Zeta23.ZeroSide.evalVec
            Zeta23.zetaZeroConfig T
            (articleParams.atD T))
          (Zeta23.ZeroSide.evalVec_reflect
            (Z := Zeta23.zetaZeroConfig)
            (T := T)
            (P := articleParams.atD T)
            (articlePhiHatConj T))).m z0
          =
        1

      rw [Zeta23.ZeroSide.mkData_m]

      simpa [
        Zeta23.zetaZeroConfig_mult
      ] using hmult

  let z :
      ArticleSimpleColumn T :=
    ⟨z0, hs1⟩

  have hzret :
      z ∈ articleRetainedColumnsFinset T := by

    simp only [
      articleRetainedColumnsFinset,
      Finset.mem_filter,
      Finset.mem_univ,
      true_and
    ]

    change
      (ρ.1 : ℂ) ∈ retainedSimpleCriticalSet T

    exact hret

  exact ⟨z, hzret⟩

/-- The two constructions are inverse. -/
noncomputable def retainedColumnZeroEquiv
    (T : ℝ) :
    ArticleRetainedColumn T
      ≃
    ↥(retainedSimpleCriticalFinset T) where

  toFun := retainedColumnToZero T
  invFun := retainedZeroToColumn T

  left_inv := by
    intro z

    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext

    rfl

  right_inv := by
    intro ρ

    apply Subtype.ext

    rfl

/-- The finite Gram index count is exactly the literal retained simple-zero
cardinality. -/
theorem articleRetainedCard_eq_ncard
    (T : ℝ) :
    articleRetainedCard T
      =
    (retainedSimpleCriticalSet T).ncard := by

  have hcard :
      Fintype.card (ArticleRetainedColumn T)
        =
      Fintype.card ↥(retainedSimpleCriticalFinset T) :=
    Fintype.card_congr (retainedColumnZeroEquiv T)

  calc
    articleRetainedCard T
        =
      Fintype.card (ArticleRetainedColumn T) := by
        rfl

    _ =
      Fintype.card ↥(retainedSimpleCriticalFinset T) :=
        hcard

    _ =
      (retainedSimpleCriticalFinset T).card := by
        exact Fintype.card_coe
          (retainedSimpleCriticalFinset T)

    _ =
      (retainedSimpleCriticalSet T).ncard := by
        rw [
          Set.ncard_eq_toFinset_card
            (retainedSimpleCriticalSet T)
            (retainedSimpleCriticalSet_finite T)
        ]
        rfl

/-- Consequently the cardinal used by shifted pinching is exactly the
`retainedCount` field of the concrete asymptotic package. -/
theorem articleRetainedCard_eq_retainedCount
    (T : ℝ) :
    articleRetainedCard T
      =
    articleCentralRetentionCounts.retainedCount T := by
  simpa [articleCentralRetentionCounts] using
    articleRetainedCard_eq_ncard T

/-- Real-valued version used directly in the scalar shifted-pinching theorem. -/
theorem articleRetainedCard_cast_eq_retainedReal
    (T : ℝ) :
    (articleRetainedCard T : ℝ)
      =
    articleCentralRetentionCounts.retainedReal T := by
  rw [
    articleCentralRetentionCounts_retainedReal,
    ← articleRetainedCard_eq_ncard
  ]

end HurtadoZeta23
