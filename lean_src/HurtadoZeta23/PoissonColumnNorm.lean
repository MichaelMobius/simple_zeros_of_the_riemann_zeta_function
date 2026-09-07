import HurtadoZeta23.ConcreteRawOverlapReduction
import HurtadoZeta23.OnLineSynthesis
import Mathlib.Tactic

noncomputable section

open Matrix Finset
open scoped BigOperators ComplexOrder

namespace HurtadoZeta23

/-!
# Poisson column normalization

This file connects the existing zero-side Poisson estimate to the actual
simple-zero synthesis columns used by the article.

It proves only the column bound

  `∑ k, ‖V k z‖^2 ≤ 1`

for the normalized synthesis `V`.  The Gram-entry bound is intentionally left
for the next small module.
-/

/--
The raw zero-side Poisson estimate implies that every normalized simple
critical-line synthesis column has squared norm at most one.
-/
theorem zeroSideSimpleSynthesis_column_normSq_le_one
    (Z : Zeta23.ZeroConfig)
    (P : Zeta23.Params)
    (T : ℝ)
    (hconj : Zeta23.ZeroSide.PhiHatConj T P)
    (hreal : Zeta23.ZeroSide.PhiHatReal T P)
    (hPois : Zeta23.ZeroSide.PoissonSq T P)
    (hc : 0 < P.a T * P.L T ^ 2)
    (z : SimpleOnLineColumn
      (Zeta23.ZeroSide.blockData Z T P hconj)) :
    (∑ k : Fin (P.d T),
      ‖zeroSideSimpleSynthesis Z P T hconj k z‖ ^ 2) ≤ 1 := by

  let D :=
    Zeta23.ZeroSide.blockData Z T P hconj

  let c : ℝ :=
    P.a T * P.L T ^ 2

  have hc' : 0 < c := by
    simpa [c] using hc

  have hm :
      D.m z.1 = 1 := by
    exact mult_eq_one_of_mem_S₁ D z.2

  have hzOn :
      z.1 ∈ D.onLine := by
    exact mem_onLine_of_mem_S₁ D z.2

  have hv :
      (∑ k : Fin (P.d T), ‖D.v z.1 k‖ ^ 2) ≤ c := by
    simpa [D, c] using
      Zeta23.ZeroSide.sum_normSq_v_le
        Z T P hconj hreal hPois z.1 hzOn

  have hsqrt :
      (Real.sqrt ((D.m z.1 : ℝ) / c)) ^ 2
        =
      (D.m z.1 : ℝ) / c := by
    exact sq_sqrt_mult_div hc'

  change
    (∑ k : Fin (P.d T),
      ‖(((Real.sqrt ((D.m z.1 : ℝ) / c) : ℝ) : ℂ) *
          D.v z.1 k)‖ ^ 2) ≤ 1

  calc
    (∑ k : Fin (P.d T),
      ‖(((Real.sqrt ((D.m z.1 : ℝ) / c) : ℝ) : ℂ) *
          D.v z.1 k)‖ ^ 2)
        =
      ∑ k : Fin (P.d T),
        ((D.m z.1 : ℝ) / c) * ‖D.v z.1 k‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          rw [abs_of_nonneg (Real.sqrt_nonneg _)]
          rw [mul_pow]
          rw [hsqrt]

    _ =
      ((D.m z.1 : ℝ) / c) *
        (∑ k : Fin (P.d T), ‖D.v z.1 k‖ ^ 2) := by
          rw [Finset.mul_sum]

    _ =
      (1 / c) *
        (∑ k : Fin (P.d T), ‖D.v z.1 k‖ ^ 2) := by
          rw [hm]
          norm_num

    _ ≤
      (1 / c) * c := by
          exact
            mul_le_mul_of_nonneg_left
              hv
              (by positivity)

    _ = 1 := by
          field_simp

/--
Article-endpoint specialization.  This is the exact column estimate needed by
the concrete consecutive Gram blocks.
-/
theorem articleSimpleSynthesis_column_normSq_le_one
    (T : ℝ)
    (hPois :
      Zeta23.ZeroSide.PoissonSq T (articleParams.atD T))
    (hc :
      0 <
        (articleParams.atD T).a T *
          (articleParams.atD T).L T ^ 2)
    (z : ArticleSimpleColumn T) :
    (∑ k : Fin ((articleParams.atD T).d T),
      ‖zeroSideSimpleSynthesis
          Zeta23.zetaZeroConfig
          (articleParams.atD T)
          T
          (articlePhiHatConj T)
          k z‖ ^ 2) ≤ 1 := by

  exact
    zeroSideSimpleSynthesis_column_normSq_le_one
      Zeta23.zetaZeroConfig
      (articleParams.atD T)
      T
      (articlePhiHatConj T)
      (articlePhiHatReal T)
      hPois
      hc
      z

end HurtadoZeta23
