import HurtadoZeta23.ConcreteStableCore
import HurtadoZeta23.BlockDefect
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

noncomputable section

open Matrix Finset
open scoped ComplexOrder

namespace HurtadoZeta23

/-!
# Principal Gram blocks

This file is the structural bridge between the article's global simple-zero
Gram matrix `M = VᴴV` and the consecutive Gram blocks used by the
position-weighted argument.

No asymptotics enter here.  A block is represented by a map from a finite
block index type into the simple-zero column type.  Its Gram matrix is the
corresponding principal submatrix of `M`, and simultaneously the Gram matrix
of the restricted synthesis matrix.
-/

section Abstract

variable {row col blk : Type*}
variable [Fintype row] [DecidableEq row]
variable [Fintype col] [DecidableEq col]
variable [Fintype blk] [DecidableEq blk]

/-- Restrict a synthesis matrix to a selected family of columns. -/
def restrictSynthesis (V : Matrix row col ℂ) (e : blk → col) : Matrix row blk ℂ :=
  V.submatrix id e

/-- Principal Gram block selected by `e`. -/
def principalGramBlock (M : Matrix col col ℂ) (e : blk → col) : Matrix blk blk ℂ :=
  M.submatrix e e

/-- **Exact Gram restriction identity.**  A principal submatrix of `VᴴV` is
exactly the Gram matrix of the correspondingly restricted synthesis matrix. -/
theorem principalGramBlock_eq_restrictedGram
    (V : Matrix row col ℂ) (e : blk → col) :
    principalGramBlock (V.conjTranspose * V) e =
      (restrictSynthesis V e).conjTranspose * restrictSynthesis V e := by
  classical
  ext i j
  simp [principalGramBlock, restrictSynthesis, Matrix.mul_apply]

/-- Every principal Gram block is positive semidefinite. -/
theorem principalGramBlock_posSemidef
    (V : Matrix row col ℂ) (e : blk → col) :
    (principalGramBlock (V.conjTranspose * V) e).PosSemidef := by
  rw [principalGramBlock_eq_restrictedGram]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- The same PSD conclusion obtained directly from the global Gram PSD
property. -/
theorem principal_submatrix_posSemidef
    (M : Matrix col col ℂ) (hM : M.PosSemidef) (e : blk → col) :
    (principalGramBlock M e).PosSemidef := by
  simpa [principalGramBlock] using hM.submatrix e

/-- Off-diagonal entries of a principal block are literally entries of the
global Gram matrix. -/
theorem principalGramBlock_apply
    (M : Matrix col col ℂ) (e : blk → col) (i j : blk) :
    principalGramBlock M e i j = M (e i) (e j) := by
  rfl

end Abstract

section ZetaConcrete

variable (Z : Zeta23.ZeroConfig) (P : Zeta23.Params) (T : ℝ)

/-- A selected principal block inside the article's simple-zero column type. -/
def zeroSidePrincipalGramBlock
    (hconj : Zeta23.ZeroSide.PhiHatConj T P)
    {blk : Type*} [Fintype blk] [DecidableEq blk]
    (e : blk → SimpleOnLineColumn (Zeta23.ZeroSide.blockData Z T P hconj)) :
    Matrix blk blk ℂ :=
  principalGramBlock (zeroSideSimpleGram Z P T hconj) e

/-- The selected simple-zero block is exactly the Gram matrix of the
correspondingly restricted simple synthesis matrix. -/
theorem zeroSidePrincipalGramBlock_eq_restrictedGram
    (hconj : Zeta23.ZeroSide.PhiHatConj T P)
    {blk : Type*} [Fintype blk] [DecidableEq blk]
    (e : blk → SimpleOnLineColumn (Zeta23.ZeroSide.blockData Z T P hconj)) :
    zeroSidePrincipalGramBlock Z P T hconj e =
      (restrictSynthesis (zeroSideSimpleSynthesis Z P T hconj) e).conjTranspose *
        restrictSynthesis (zeroSideSimpleSynthesis Z P T hconj) e := by
  exact principalGramBlock_eq_restrictedGram _ _

/-- Every concrete selected simple-zero Gram block is PSD. -/
theorem zeroSidePrincipalGramBlock_posSemidef
    (hconj : Zeta23.ZeroSide.PhiHatConj T P)
    {blk : Type*} [Fintype blk] [DecidableEq blk]
    (e : blk → SimpleOnLineColumn (Zeta23.ZeroSide.blockData Z T P hconj)) :
    (zeroSidePrincipalGramBlock Z P T hconj e).PosSemidef := by
  exact principalGramBlock_posSemidef _ _

end ZetaConcrete

/-!
## Pinching interface

The partition-based pinching statements downstream should now be instantiated
with `zeroSideSimpleGram`, so every retained principal block contains only
simple critical-line zeros, exactly as in `M°` of the article.
-/

end HurtadoZeta23
