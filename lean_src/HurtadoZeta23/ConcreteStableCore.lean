import HurtadoZeta23.StableAssemblySeam
import HurtadoZeta23.OnLineSynthesis
import HurtadoZeta23.StableRankTraceMatrix
import Zeta23.ZeroSide
import Mathlib.Tactic

noncomputable section

open Matrix Finset RHLinalg
open scoped ComplexOrder

namespace HurtadoZeta23

/--
Concrete stability-enhanced zero-side core aligned exactly with the article.

Here

* `P = P₁` is built only from the simple critical-line zeros `S₁`;
* `Q = Q'` contains the multiple critical-line block and all off-line pairs;
* `r = s₁`;
* `b = s₂+p`.

Thus the conclusion is a bound for `s₁`, not `s₁+s₂`.
-/
theorem stableCoreAt_of_zeroSide
    (Z : Zeta23.ZeroConfig)
    (P : Zeta23.Params)
    (T : ℝ)
    (hconj : Zeta23.ZeroSide.PhiHatConj T P)
    (hreal : Zeta23.ZeroSide.PhiHatReal T P)
    (hPois : Zeta23.ZeroSide.PoissonSq T P)
    (hc : 0 < P.a T * P.L T ^ 2) :
    StableCoreAt
      Z P T
      (concreteSimplePDefect Z P T hconj hc) := by

  let Pm := zeroSideSimpleP Z P T hconj
  let Qm := zeroSideSimpleQ Z P T hconj
  let r : ℕ := Z.s1 T
  let b : ℕ := Z.s2 T + Z.p T

  have hPsd : Pm.PosSemidef := by
    dsimp [Pm]
    exact zeroSideSimpleP_posSemidef Z P T hconj hc

  have hQh : Qm.IsHermitian := by
    dsimp [Qm]
    exact zeroSideSimpleQ_isHermitian Z P T hconj hc

  have hrank : Pm.rank ≤ r := by
    simpa [Pm, r] using zeroSideSimpleP_rank_le Z P T hconj hc

  have hpos : posIndex hQh ≤ b := by
    simpa [Qm, b] using zeroSideSimpleQ_posIndex_le Z P T hconj hc

  have htrace : rtrace Pm ≤ (r : ℝ) := by
    simpa [Pm, r] using
      zeroSideSimpleP_rtrace_le Z P T hconj hreal hPois hc

  have henh :=
    stable_rank_trace_ineq_two
      hPsd hQh hrank hpos htrace

  have hA :
      P.hat T (Z.Az P T) = Pm + Qm := by
    simpa [Pm, Qm] using
      hat_Az_eq_zeroSideSimpleP_add_zeroSideSimpleQ Z P T hconj

  have hcountNat :
      Z.s1 T + 2 * Z.s2 T + 2 * Z.p T ≤ Z.NIprime T :=
    Zeta23.ZeroSide.s1_add_two_s2_add_two_p_le_NIprime Z T

  have hcountNat' :
      Z.s1 T + 2 * (Z.s2 T + Z.p T) ≤ Z.NIprime T := by
    omega

  have hcount :
      (r : ℝ) + 2 * (b : ℝ) ≤ (Z.NIprime T : ℝ) := by
    dsimp [r, b]
    exact_mod_cast hcountNat'

  unfold StableCoreAt
  change
    4 * rtrace (P.hat T (Z.Az P T))
        - 2 * (Z.NIprime T : ℝ)
        - frobSq (P.hat T (Z.Az P T))
        + concreteSimplePDefect Z P T hconj hc
      ≤ (r : ℝ)

  rw [hA]

  change
    4 * rtrace (Pm + Qm)
        - 2 * (Z.NIprime T : ℝ)
        - frobSq (Pm + Qm)
        + matrixSpectralDefect Pm hPsd r
      ≤ (r : ℝ)

  exact stable_zeroside_core_finish henh hcount

/-- The same concrete core written with the article's Gram defect
`D(M) = tr Ψ(VᴴV)`. -/
theorem stableCoreAt_of_zeroSideSimpleGram
    (Z : Zeta23.ZeroConfig)
    (P : Zeta23.Params)
    (T : ℝ)
    (hconj : Zeta23.ZeroSide.PhiHatConj T P)
    (hreal : Zeta23.ZeroSide.PhiHatReal T P)
    (hPois : Zeta23.ZeroSide.PoissonSq T P)
    (hc : 0 < P.a T * P.L T ^ 2) :
    StableCoreAt Z P T
      (gramSpectralDefect
        (zeroSideSimpleGram Z P T hconj)
        (zeroSideSimpleGram_posSemidef Z P T hconj)) := by
  have hcore := stableCoreAt_of_zeroSide Z P T hconj hreal hPois hc
  rw [concreteSimplePDefect_eq_zeroSideSimpleGramDefect Z P T hconj hc] at hcore
  exact hcore

end HurtadoZeta23
