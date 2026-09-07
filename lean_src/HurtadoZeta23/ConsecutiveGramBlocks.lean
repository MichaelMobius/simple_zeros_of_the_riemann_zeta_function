import HurtadoZeta23.OrderedRetainedColumns
import HurtadoZeta23.PoissonGaborBridge
import HurtadoZeta23.GramPinchingFinitePartition
import Mathlib.Tactic

noncomputable section

open Matrix Finset
open scoped BigOperators ComplexOrder

namespace HurtadoZeta23

/-!
# Consecutive retained Gram blocks

This file turns the ordered retained simple-zero columns into literal
length-`blockLength = 262` principal Gram blocks.

No pinching or asymptotics occur here.  The only hypothesis on a starting
position `s` is that the full block fits inside the retained enumeration.
-/

/-- Number of retained simple columns at height `T`. -/
abbrev articleRetainedCard (T : ℝ) : ℕ :=
  Fintype.card (ArticleRetainedColumn T)

/-- Rank `s+i` of the `i`-th point in a full consecutive block. -/
noncomputable def consecutiveRetainedRank
    (T : ℝ) (s : ℕ)
    (hs : s + blockLength ≤ articleRetainedCard T)
    (i : Fin blockLength) :
    Fin (articleRetainedCard T) :=
  ⟨s + i.1, by
    have hi : i.1 < blockLength := i.2
    omega⟩

/-- The retained column of local block index `i`. -/
noncomputable def consecutiveRetainedColumn
    (T : ℝ) (s : ℕ)
    (hs : s + blockLength ≤ articleRetainedCard T)
    (i : Fin blockLength) :
    ArticleRetainedColumn T :=
  articleRetainedOrderIso T
    (consecutiveRetainedRank T s hs i)

/-- The same column viewed in the global simple-column type. -/
noncomputable def consecutiveSimpleColumn
    (T : ℝ) (s : ℕ)
    (hs : s + blockLength ≤ articleRetainedCard T)
    (i : Fin blockLength) :
    ArticleSimpleColumn T :=
  (consecutiveRetainedColumn T s hs i).1

/-- Consecutive length-262 principal block of the global simple Gram. -/
noncomputable abbrev consecutiveGramBlock
    (T : ℝ) (s : ℕ)
    (hs : s + blockLength ≤ articleRetainedCard T) :
    Matrix (Fin blockLength) (Fin blockLength) ℂ :=
  zeroSidePrincipalGramBlock
    Zeta23.zetaZeroConfig
    (articleParams.atD T)
    T
    (articlePhiHatConj T)
    (consecutiveSimpleColumn T s hs)

/-- Every consecutive block is positive semidefinite. -/
theorem consecutiveGramBlock_posSemidef
    (T : ℝ) (s : ℕ)
    (hs : s + blockLength ≤ articleRetainedCard T) :
    (consecutiveGramBlock T s hs).PosSemidef := by
  exact
    zeroSidePrincipalGramBlock_posSemidef
      Zeta23.zetaZeroConfig
      (articleParams.atD T)
      T
      (articlePhiHatConj T)
      (consecutiveSimpleColumn T s hs)

/-- Entries are literally entries of the global simple Gram. -/
theorem consecutiveGramBlock_apply
    (T : ℝ) (s : ℕ)
    (hs : s + blockLength ≤ articleRetainedCard T)
    (i j : Fin blockLength) :
    consecutiveGramBlock T s hs i j =
      zeroSideSimpleGram
        Zeta23.zetaZeroConfig
        (articleParams.atD T)
        T
        (articlePhiHatConj T)
        (consecutiveSimpleColumn T s hs i)
        (consecutiveSimpleColumn T s hs j) := by
  rfl

/-- Actual zero occupying local block position `i`. -/
noncomputable def consecutiveZero
    (T : ℝ) (s : ℕ)
    (hs : s + blockLength ≤ articleRetainedCard T)
    (i : Fin blockLength) :
    ℂ :=
  articleColumnZero
    (consecutiveSimpleColumn T s hs i)

/-- The block zero agrees with the globally ordered zero at rank `s+i`. -/
theorem consecutiveZero_eq_ordered
    (T : ℝ) (s : ℕ)
    (hs : s + blockLength ≤ articleRetainedCard T)
    (i : Fin blockLength) :
    consecutiveZero T s hs i =
      orderedRetainedZero T
        (consecutiveRetainedRank T s hs i) := by
  rfl

/-- Normalized ordinate of a local block point.  Values outside the first
`blockLength` naturals are irrelevant and are set to zero so that the existing
seven-point API, which is phrased on `ℕ → ℝ`, can be used directly. -/
noncomputable def consecutiveY
    (T : ℝ) (s : ℕ)
    (hs : s + blockLength ≤ articleRetainedCard T)
    (q : ℕ) :
    ℝ :=
  if hq : q < blockLength then
    orderedRetainedY T
      (consecutiveRetainedRank T s hs ⟨q, hq⟩)
  else
    0

@[simp] theorem consecutiveY_eq
    (T : ℝ) (s : ℕ)
    (hs : s + blockLength ≤ articleRetainedCard T)
    {q : ℕ} (hq : q < blockLength) :
    consecutiveY T s hs q =
      orderedRetainedY T
        (consecutiveRetainedRank T s hs ⟨q, hq⟩) := by
  simp [consecutiveY, hq]

/-- The local normalized coordinates are nondecreasing whenever the global
normalizing scale is nonnegative. -/
theorem consecutiveY_mono
    (T : ℝ) (s : ℕ)
    (hs : s + blockLength ≤ articleRetainedCard T)
    (hL : 0 ≤ articleParams.L T) :
    ∀ q < blockLength - 1,
      consecutiveY T s hs q ≤
        consecutiveY T s hs (q + 1) := by

  intro q hq

  have hq0 : q < blockLength := by
    omega

  have hq1 : q + 1 < blockLength := by
    omega

  rw [
    consecutiveY_eq T s hs hq0,
    consecutiveY_eq T s hs hq1
  ]

  apply orderedRetainedY_mono hL
  change s + q ≤ s + (q + 1)
  omega

/-- The full normalized span of a consecutive block. -/
def consecutiveBlockSpan
    (T : ℝ) (s : ℕ)
    (hs : s + blockLength ≤ articleRetainedCard T) :
    ℝ :=
  consecutiveY T s hs (blockLength - 1)
    - consecutiveY T s hs 0

/-- Ordered blocks have nonnegative span. -/
theorem consecutiveBlockSpan_nonneg
    (T : ℝ) (s : ℕ)
    (hs : s + blockLength ≤ articleRetainedCard T)
    (hL : 0 ≤ articleParams.L T) :
    0 ≤ consecutiveBlockSpan T s hs := by

  have hm :
      consecutiveY T s hs 0 ≤
        consecutiveY T s hs (blockLength - 1) := by

    have h0 : 0 < blockLength := by
      norm_num [blockLength]

    have hlast :
        blockLength - 1 < blockLength := by
      omega

    rw [
      consecutiveY_eq T s hs h0,
      consecutiveY_eq T s hs hlast
    ]

    apply orderedRetainedY_mono hL
    change s + 0 ≤ s + (blockLength - 1)
    omega

  unfold consecutiveBlockSpan
  linarith

/-- Exact endpoint form of the block span. -/
theorem consecutiveBlockSpan_eq
    (T : ℝ) (s : ℕ)
    (hs : s + blockLength ≤ articleRetainedCard T) :
    consecutiveBlockSpan T s hs =
      consecutiveY T s hs (blockLength - 1)
        - consecutiveY T s hs 0 := by
  rfl

/-- Defect of one actual consecutive principal Gram block. -/
noncomputable def consecutiveBlockDefect
    (T : ℝ) (s : ℕ)
    (hs : s + blockLength ≤ articleRetainedCard T) :
    ℝ :=
  gramSpectralDefect
    (consecutiveGramBlock T s hs)
    (consecutiveGramBlock_posSemidef T s hs)

/-- Every consecutive block defect is nonnegative. -/
theorem consecutiveBlockDefect_nonneg
    (T : ℝ) (s : ℕ)
    (hs : s + blockLength ≤ articleRetainedCard T) :
    0 ≤ consecutiveBlockDefect T s hs := by
  exact
    gramSpectralDefect_nonneg
      (consecutiveGramBlock T s hs)
      (consecutiveGramBlock_posSemidef T s hs)

end HurtadoZeta23
