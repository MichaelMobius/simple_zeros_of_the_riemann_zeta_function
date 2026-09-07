import HurtadoZeta23.PoissonColumnNorm
import HurtadoZeta23.ConsecutiveGramRealEntries
import Mathlib.Tactic

noncomputable section

open Matrix Finset
open scoped BigOperators ComplexOrder

namespace HurtadoZeta23

/-!
# Poisson Gram unit bound

The column estimate from `PoissonColumnNorm` is converted into the entrywise
Gram bound required by the raw-overlap bridge.

We deliberately use the elementary inequality

  `2ab ≤ a² + b²`

term by term, rather than a generic square-root Cauchy--Schwarz theorem.
This keeps elaboration small.
-/

/--
For the concrete zero-side simple Gram, unit column norms imply
`|Re G_ij| ≤ 1`.
-/
theorem zeroSideSimpleGram_re_abs_le_one_of_column_norms
    (Z : Zeta23.ZeroConfig)
    (P : Zeta23.Params)
    (T : ℝ)
    (hconj : Zeta23.ZeroSide.PhiHatConj T P)
    (hcol :
      ∀ z : SimpleOnLineColumn
          (Zeta23.ZeroSide.blockData Z T P hconj),
        (∑ k : Fin (P.d T),
          ‖zeroSideSimpleSynthesis Z P T hconj k z‖ ^ 2) ≤ 1)
    (i j : SimpleOnLineColumn
      (Zeta23.ZeroSide.blockData Z T P hconj)) :
    |(zeroSideSimpleGram Z P T hconj i j).re| ≤ 1 := by

  let V := zeroSideSimpleSynthesis Z P T hconj

  have hi :
      (∑ k : Fin (P.d T), ‖V k i‖ ^ 2) ≤ 1 := by
    simpa [V] using hcol i

  have hj :
      (∑ k : Fin (P.d T), ‖V k j‖ ^ 2) ≤ 1 := by
    simpa [V] using hcol j

  have htri :
      ‖zeroSideSimpleGram Z P T hconj i j‖
        ≤
      ∑ k : Fin (P.d T), ‖V k i‖ * ‖V k j‖ := by

    unfold zeroSideSimpleGram

    simp only [
      Matrix.mul_apply,
      Matrix.conjTranspose_apply
    ]

    calc
      ‖∑ k : Fin (P.d T), star (V k i) * V k j‖
          ≤
        ∑ k : Fin (P.d T), ‖star (V k i) * V k j‖ := by
          exact
            norm_sum_le Finset.univ
              (fun k : Fin (P.d T) =>
                star (V k i) * V k j)

      _ =
        ∑ k : Fin (P.d T), ‖V k i‖ * ‖V k j‖ := by
          apply Finset.sum_congr rfl
          intro k hk
          simp

  have hquad :
      2 * (∑ k : Fin (P.d T), ‖V k i‖ * ‖V k j‖)
        ≤
      (∑ k : Fin (P.d T), ‖V k i‖ ^ 2)
        +
      (∑ k : Fin (P.d T), ‖V k j‖ ^ 2) := by

    rw [Finset.mul_sum]

    calc
      (∑ k : Fin (P.d T),
        2 * (‖V k i‖ * ‖V k j‖))
          ≤
        ∑ k : Fin (P.d T),
          (‖V k i‖ ^ 2 + ‖V k j‖ ^ 2) := by

            apply Finset.sum_le_sum

            intro k hk

            nlinarith [
              sq_nonneg (‖V k i‖ - ‖V k j‖)
            ]

      _ =
        (∑ k : Fin (P.d T), ‖V k i‖ ^ 2)
          +
        (∑ k : Fin (P.d T), ‖V k j‖ ^ 2) := by
            exact Finset.sum_add_distrib

  have hnorm :
      ‖zeroSideSimpleGram Z P T hconj i j‖ ≤ 1 := by
    nlinarith

  exact
    (Complex.abs_re_le_norm
      (zeroSideSimpleGram Z P T hconj i j)).trans hnorm

/--
Poisson specialization for the article's global simple Gram.
-/
theorem articleGlobalSimpleGram_re_abs_le_one
    (T : ℝ)
    (hPois :
      Zeta23.ZeroSide.PoissonSq T (articleParams.atD T))
    (hc :
      0 <
        (articleParams.atD T).a T *
          (articleParams.atD T).L T ^ 2)
    (i j : ArticleSimpleColumn T) :
    |(articleGlobalSimpleGram T i j).re| ≤ 1 := by

  exact
    zeroSideSimpleGram_re_abs_le_one_of_column_norms
      Zeta23.zetaZeroConfig
      (articleParams.atD T)
      T
      (articlePhiHatConj T)
      (articleSimpleSynthesis_column_normSq_le_one T hPois hc)
      i j

/--
The bound required by `hraw` for every actual consecutive retained block.
-/
theorem consecutiveGramBlock_re_abs_le_one
    (T : ℝ)
    (hPois :
      Zeta23.ZeroSide.PoissonSq T (articleParams.atD T))
    (hc :
      0 <
        (articleParams.atD T).a T *
          (articleParams.atD T).L T ^ 2)
    (s : ℕ)
    (hs : s + blockLength ≤ articleRetainedCard T)
    (i j : Fin blockLength) :
    |(consecutiveGramBlock T s hs i j).re| ≤ 1 := by

  rw [consecutiveGramBlock_apply]

  exact
    articleGlobalSimpleGram_re_abs_le_one
      T hPois hc
      (consecutiveSimpleColumn T s hs i)
      (consecutiveSimpleColumn T s hs j)

end HurtadoZeta23
