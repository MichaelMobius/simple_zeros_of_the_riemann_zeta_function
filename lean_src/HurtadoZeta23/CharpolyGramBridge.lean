import HurtadoZeta23.SylvesterGramBridge
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic

noncomputable section

open Matrix Finset Polynomial
open scoped ComplexOrder

namespace HurtadoZeta23

universe uK uI uJ

variable {𝕜 : Type uK} [RCLike 𝕜]
variable {n : Type uI}
variable {r : Type uJ}

variable [Fintype n] [DecidableEq n]
variable [Fintype r] [DecidableEq r]

/--
Rectangular characteristic-polynomial identity for a matrix and its adjoint.

Mathlib proves `Matrix.charpoly_mul_comm'` for rectangular matrices:

  X^(card r) * charpoly(V Vᴴ)
    =
  X^(card n) * charpoly(Vᴴ V).

Thus the two characteristic polynomials differ only by a power of `X`;
only the zero eigenvalue can acquire a different multiplicity.
-/
theorem gram_charpoly_identity
    (V : Matrix n r 𝕜) :
    Polynomial.X ^ Fintype.card r *
        (V * V.conjTranspose).charpoly
      =
    Polynomial.X ^ Fintype.card n *
        (V.conjTranspose * V).charpoly := by

  simpa using
    Matrix.charpoly_mul_comm'
      V
      V.conjTranspose

/--
Nonzero characteristic-root multiplicities agree on the two Gram sides.
-/
def NonzeroCharpolyMultiplicityMatch
    (V : Matrix n r 𝕜) : Prop :=
  ∀ lam : 𝕜,
    lam ≠ 0 →
      Polynomial.rootMultiplicity
          lam
          (V * V.conjTranspose).charpoly
        =
      Polynomial.rootMultiplicity
          lam
          (V.conjTranspose * V).charpoly

/--
Pure polynomial cancellation interface.

The universe parameter is explicit: this is important because the field
must be instantiated at the same universe as the scalar field of `V`.
-/
def CharpolyMultiplicityCancellation.{u} : Prop :=
  ∀ {K : Type u}
      [Field K]
      (p q : Polynomial K)
      (a : K)
      (m n : ℕ),
    a ≠ 0 →
    Polynomial.X ^ m * p =
      Polynomial.X ^ n * q →
    Polynomial.rootMultiplicity a p =
      Polynomial.rootMultiplicity a q

/--
The characteristic-polynomial identity gives equality of every nonzero root
multiplicity once the standard polynomial cancellation interface is supplied.
-/
theorem nonzero_charpoly_multiplicity_match_of_cancellation
    (hcancel : CharpolyMultiplicityCancellation.{uK})
    (V : Matrix n r 𝕜) :
    NonzeroCharpolyMultiplicityMatch V := by

  intro lam hlam

  exact
    hcancel
      (V * V.conjTranspose).charpoly
      (V.conjTranspose * V).charpoly
      lam
      (Fintype.card r)
      (Fintype.card n)
      hlam
      (gram_charpoly_identity V)

/--
Library-level adapter from characteristic roots with algebraic multiplicity
to the Hermitian eigenvalue arrays used in the Gram defect.

All three universe parameters are explicit so that this interface can be
instantiated at the scalar and index universes of a concrete rectangular
matrix.
-/
def HermitianRootsToEigenvaluesAdapter.{u, v, w} : Prop :=
  ∀ {K : Type u}
      [RCLike K]
      {ι : Type v}
      {κ : Type w}
      [Fintype ι]
      [DecidableEq ι]
      [Fintype κ]
      [DecidableEq κ]
      (P : Matrix ι ι K)
      (hP : P.PosSemidef)
      (M : Matrix κ κ K)
      (hM : M.PosSemidef),
    (∀ lam : K,
      lam ≠ 0 →
        Polynomial.rootMultiplicity
            lam
            P.charpoly
          =
        Polynomial.rootMultiplicity
            lam
            M.charpoly) →
    Nonempty
      (GramNonzeroSpectrumBridge
        P hP M hM)

/--
With the polynomial cancellation and spectral representation adapters, the
nonzero-spectrum Gram bridge follows for `V Vᴴ` and `Vᴴ V`.
-/
theorem gramNonzeroSpectrumBridge_of_charpoly
    (hcancel : CharpolyMultiplicityCancellation.{uK})
    (hadapt : HermitianRootsToEigenvaluesAdapter.{uK, uI, uJ})
    (V : Matrix n r 𝕜) :
    Nonempty
      (GramNonzeroSpectrumBridge
        (V * V.conjTranspose)
        (posSemidef_mul_conjTranspose_self V)
        (V.conjTranspose * V)
        (Matrix.posSemidef_conjTranspose_mul_self V)) := by

  exact
    hadapt
      (V * V.conjTranspose)
      (posSemidef_mul_conjTranspose_self V)
      (V.conjTranspose * V)
      (Matrix.posSemidef_conjTranspose_mul_self V)
      (nonzero_charpoly_multiplicity_match_of_cancellation
        hcancel
        V)

/--
Stable rank--trace inequality with the paper's Gram defect, reduced to the
polynomial cancellation and spectral representation adapters.
-/
theorem stable_rank_trace_ineq_two_of_charpoly
    (hcancel : CharpolyMultiplicityCancellation.{uK})
    (hadapt : HermitianRootsToEigenvaluesAdapter.{uK, uI, uJ})
    (V : Matrix n r 𝕜)
    {Q : Matrix n n 𝕜}
    (hQ : Q.IsHermitian)
    {b : ℕ}
    (hr :
      (V * V.conjTranspose).rank
        ≤ Fintype.card r)
    (hb :
      RHLinalg.posIndex hQ
        ≤ b)
    (htr :
      RHLinalg.rtrace
          (V * V.conjTranspose)
        ≤ Fintype.card r) :
    4 *
        RHLinalg.rtrace
          (V * V.conjTranspose + Q)
      - 3 * (Fintype.card r : ℝ)
      - 4 * (b : ℝ)
      +
        gramSpectralDefect
          (V.conjTranspose * V)
          (Matrix.posSemidef_conjTranspose_mul_self V)
      ≤
    RHLinalg.frobSq
      (V * V.conjTranspose + Q) := by

  have hP :
      (V * V.conjTranspose).PosSemidef :=
    posSemidef_mul_conjTranspose_self V

  have hM :
      (V.conjTranspose * V).PosSemidef :=
    Matrix.posSemidef_conjTranspose_mul_self V

  obtain ⟨hPM⟩ :=
    gramNonzeroSpectrumBridge_of_charpoly
      hcancel
      hadapt
      V

  exact
    stable_rank_trace_ineq_two_gram
      hP
      hQ
      (V.conjTranspose * V)
      hM
      hPM
      hr
      hb
      htr

end HurtadoZeta23