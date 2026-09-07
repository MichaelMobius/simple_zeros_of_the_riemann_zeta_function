import HurtadoZeta23.GramSpectrumBridge
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic

noncomputable section

open Matrix Finset
open scoped ComplexOrder

namespace HurtadoZeta23

variable {𝕜 : Type*} [RCLike 𝕜]
variable {n r : Type*}
variable [Fintype n] [DecidableEq n]
variable [Fintype r] [DecidableEq r]

/--
Rectangular Sylvester bridge for a matrix and its adjoint.

This is the determinant identity underlying the standard fact that `V Vᴴ`
and `Vᴴ V` have the same nonzero spectrum. It is an immediate specialization
of Mathlib's Weinstein--Aronszajn identity `Matrix.det_one_sub_mul_comm`.
-/
theorem det_one_sub_vvStar_eq_det_one_sub_vStarv
    (V : Matrix n r 𝕜) (z : 𝕜) :
    (1 - (z • V) * V.conjTranspose).det =
      (1 - V.conjTranspose * (z • V)).det := by

  simpa using
    Matrix.det_one_sub_mul_comm
      (z • V)
      V.conjTranspose

/--
The same identity with the scalar moved from `V` onto the square product.

This is the form used to test a nonzero spectral value `lam`.
-/
theorem det_one_sub_smul_vvStar_eq_det_one_sub_smul_vStarv
    (V : Matrix n r 𝕜) (z : 𝕜) :
    (1 - z • (V * V.conjTranspose)).det =
      (1 - z • (V.conjTranspose * V)).det := by

  simpa [smul_mul, mul_smul] using
    (det_one_sub_vvStar_eq_det_one_sub_vStarv
      (V := V) z)

/--
Resolvent-form Sylvester identity.

For `lam ≠ 0`, this compares the two matrices at the reciprocal spectral
parameter `lam⁻¹`.

Consequently, a nonzero `lam` is detected by the same vanishing determinant
on both Gram sides. The multiplicity statement is obtained by applying the
same identity over the polynomial ring in the reciprocal parameter.
-/
theorem gram_resolvent_det_eq
    (V : Matrix n r 𝕜)
    {lam : 𝕜}
    (_hlam : lam ≠ 0) :
    (1 - lam⁻¹ • (V * V.conjTranspose)).det =
      (1 - lam⁻¹ • (V.conjTranspose * V)).det := by

  exact
    det_one_sub_smul_vvStar_eq_det_one_sub_smul_vStarv
      V
      lam⁻¹

/--
The exact standard theorem still needed to discharge
`GramNonzeroSpectrumBridge` automatically.

The determinant identity above supplies the algebraic engine. To turn it into
this multiplicity-preserving equivalence, one transports the identity to
`Polynomial 𝕜` (replace the scalar `z` by the indeterminate `X`) and compares
root multiplicities.

Keeping this proposition separate makes the remaining trust boundary precise
rather than hiding it inside the zeta argument.
-/
def SylvesterMultiplicityBridge
    (V : Matrix n r 𝕜) : Prop :=
  let P := V * V.conjTranspose
  let M := V.conjTranspose * V
  ∀ (hP : P.PosSemidef) (hM : M.PosSemidef),
    Nonempty (GramNonzeroSpectrumBridge P hP M hM)

/--
`V Vᴴ` is positive semidefinite.

Mathlib directly supplies positivity of `Aᴴ A`. Applying that theorem to
`A = Vᴴ` gives `(Vᴴ)ᴴ Vᴴ = V Vᴴ`.
-/
theorem posSemidef_mul_conjTranspose_self
    (V : Matrix n r 𝕜) :
    (V * V.conjTranspose).PosSemidef := by

  simpa using
    (Matrix.posSemidef_conjTranspose_mul_self
      V.conjTranspose)

/--
Once the polynomial multiplicity bridge is supplied, the Gram defect in the
stable rank--trace inequality is automatically the paper's `tr Ψ(VᴴV)`.

This theorem is the final bookkeeping step between Sylvester and v4.3.
-/
theorem stable_rank_trace_ineq_two_of_sylvester_bridge
    (V : Matrix n r 𝕜)
    {Q : Matrix n n 𝕜}
    (hQ : Q.IsHermitian)
    (hSylv : SylvesterMultiplicityBridge V)
    {b : ℕ}
    (hr :
      (V * V.conjTranspose).rank
        ≤ Fintype.card r)
    (hb :
      RHLinalg.posIndex hQ
        ≤ b)
    (htr :
      RHLinalg.rtrace (V * V.conjTranspose)
        ≤ Fintype.card r) :
    4 * RHLinalg.rtrace
          (V * V.conjTranspose + Q)
        - 3 * (Fintype.card r : ℝ)
        - 4 * (b : ℝ)
        + gramSpectralDefect
            (V.conjTranspose * V)
            (Matrix.posSemidef_conjTranspose_mul_self V)
      ≤
    RHLinalg.frobSq
      (V * V.conjTranspose + Q) := by

  let P : Matrix n n 𝕜 :=
    V * V.conjTranspose

  let M : Matrix r r 𝕜 :=
    V.conjTranspose * V

  have hP : P.PosSemidef := by
    dsimp [P]
    exact
      posSemidef_mul_conjTranspose_self V

  have hM : M.PosSemidef := by
    dsimp [M]
    exact
      Matrix.posSemidef_conjTranspose_mul_self V

  obtain ⟨hPM⟩ :=
    hSylv hP hM

  exact
    stable_rank_trace_ineq_two_gram
      hP
      hQ
      M
      hM
      hPM
      hr
      hb
      htr

end HurtadoZeta23
