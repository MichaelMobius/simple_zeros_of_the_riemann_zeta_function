import HurtadoZeta23.ConcreteStableSeam
import HurtadoZeta23.OrderedRetainedColumns
import HurtadoZeta23.RetainedGramPinching
import HurtadoZeta23.OnLineSynthesis
import Mathlib.Tactic

noncomputable section

open Matrix Finset
open scoped BigOperators ComplexOrder

namespace HurtadoZeta23

/-!
# Lightweight Poisson unit bound for the v17 global Gram

The historical `PoissonColumnNorm` / `PoissonGramUnitBound` chain also imported
consecutive 262-point wrappers.  The v17 450-point argument only needs the
global simple-Gram bound, so this module keeps precisely that part.
-/

/-- The raw zero-side Poisson estimate gives unit squared norm for every
normalized simple critical-line synthesis column. -/
theorem v17_zeroSideSimpleSynthesis_column_normSq_le_one
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
  let D := Zeta23.ZeroSide.blockData Z T P hconj
  let c : ℝ := P.a T * P.L T ^ 2
  have hc' : 0 < c := by simpa [c] using hc
  have hm : D.m z.1 = 1 := mult_eq_one_of_mem_S₁ D z.2
  have hzOn : z.1 ∈ D.onLine := mem_onLine_of_mem_S₁ D z.2
  have hv : (∑ k : Fin (P.d T), ‖D.v z.1 k‖ ^ 2) ≤ c := by
    simpa [D, c] using
      Zeta23.ZeroSide.sum_normSq_v_le Z T P hconj hreal hPois z.1 hzOn
  have hsqrt :
      (Real.sqrt ((D.m z.1 : ℝ) / c)) ^ 2 = (D.m z.1 : ℝ) / c := by
    exact sq_sqrt_mult_div hc'
  change
    (∑ k : Fin (P.d T),
      ‖(((Real.sqrt ((D.m z.1 : ℝ) / c) : ℝ) : ℂ) * D.v z.1 k)‖ ^ 2) ≤ 1
  calc
    (∑ k : Fin (P.d T),
      ‖(((Real.sqrt ((D.m z.1 : ℝ) / c) : ℝ) : ℂ) * D.v z.1 k)‖ ^ 2)
        = ∑ k : Fin (P.d T),
            ((D.m z.1 : ℝ) / c) * ‖D.v z.1 k‖ ^ 2 := by
              apply Finset.sum_congr rfl
              intro k hk
              rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
              rw [abs_of_nonneg (Real.sqrt_nonneg _)]
              rw [mul_pow]
              rw [hsqrt]
    _ = ((D.m z.1 : ℝ) / c) * (∑ k : Fin (P.d T), ‖D.v z.1 k‖ ^ 2) := by
          rw [Finset.mul_sum]
    _ = (1 / c) * (∑ k : Fin (P.d T), ‖D.v z.1 k‖ ^ 2) := by
          rw [hm]
          norm_num
    _ ≤ (1 / c) * c := by
          exact mul_le_mul_of_nonneg_left hv (by positivity)
    _ = 1 := by field_simp

/-- Article specialization of the unit column estimate. -/
theorem v17_articleSimpleSynthesis_column_normSq_le_one
    (T : ℝ)
    (hPois : Zeta23.ZeroSide.PoissonSq T (articleParams.atD T))
    (hc : 0 < (articleParams.atD T).a T * (articleParams.atD T).L T ^ 2)
    (z : ArticleSimpleColumn T) :
    (∑ k : Fin ((articleParams.atD T).d T),
      ‖zeroSideSimpleSynthesis
          Zeta23.zetaZeroConfig (articleParams.atD T) T
          (articlePhiHatConj T) k z‖ ^ 2) ≤ 1 := by
  exact
    v17_zeroSideSimpleSynthesis_column_normSq_le_one
      Zeta23.zetaZeroConfig (articleParams.atD T) T
      (articlePhiHatConj T) (articlePhiHatReal T) hPois hc z

/-- Unit column norms imply `|Re G_ij| ≤ 1` for the concrete simple Gram. -/
theorem v17_zeroSideSimpleGram_re_abs_le_one_of_column_norms
    (Z : Zeta23.ZeroConfig)
    (P : Zeta23.Params)
    (T : ℝ)
    (hconj : Zeta23.ZeroSide.PhiHatConj T P)
    (hcol :
      ∀ z : SimpleOnLineColumn (Zeta23.ZeroSide.blockData Z T P hconj),
        (∑ k : Fin (P.d T),
          ‖zeroSideSimpleSynthesis Z P T hconj k z‖ ^ 2) ≤ 1)
    (i j : SimpleOnLineColumn (Zeta23.ZeroSide.blockData Z T P hconj)) :
    |(zeroSideSimpleGram Z P T hconj i j).re| ≤ 1 := by
  let V := zeroSideSimpleSynthesis Z P T hconj
  have hi : (∑ k : Fin (P.d T), ‖V k i‖ ^ 2) ≤ 1 := by simpa [V] using hcol i
  have hj : (∑ k : Fin (P.d T), ‖V k j‖ ^ 2) ≤ 1 := by simpa [V] using hcol j
  have htri :
      ‖zeroSideSimpleGram Z P T hconj i j‖ ≤
        ∑ k : Fin (P.d T), ‖V k i‖ * ‖V k j‖ := by
    unfold zeroSideSimpleGram
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
    calc
      ‖∑ k : Fin (P.d T), star (V k i) * V k j‖
          ≤ ∑ k : Fin (P.d T), ‖star (V k i) * V k j‖ := by
              exact norm_sum_le Finset.univ
                (fun k : Fin (P.d T) => star (V k i) * V k j)
      _ = ∑ k : Fin (P.d T), ‖V k i‖ * ‖V k j‖ := by
            apply Finset.sum_congr rfl
            intro k hk
            simp
  have hquad :
      2 * (∑ k : Fin (P.d T), ‖V k i‖ * ‖V k j‖) ≤
        (∑ k : Fin (P.d T), ‖V k i‖ ^ 2) +
          (∑ k : Fin (P.d T), ‖V k j‖ ^ 2) := by
    rw [Finset.mul_sum]
    calc
      (∑ k : Fin (P.d T), 2 * (‖V k i‖ * ‖V k j‖)) ≤
          ∑ k : Fin (P.d T), (‖V k i‖ ^ 2 + ‖V k j‖ ^ 2) := by
            apply Finset.sum_le_sum
            intro k hk
            nlinarith [sq_nonneg (‖V k i‖ - ‖V k j‖)]
      _ = (∑ k : Fin (P.d T), ‖V k i‖ ^ 2) +
            (∑ k : Fin (P.d T), ‖V k j‖ ^ 2) := by
            exact Finset.sum_add_distrib
  have hnorm : ‖zeroSideSimpleGram Z P T hconj i j‖ ≤ 1 := by
    nlinarith
  exact (Complex.abs_re_le_norm (zeroSideSimpleGram Z P T hconj i j)).trans hnorm

/-- Poisson specialization for the article's global simple Gram. -/
theorem v17_articleGlobalSimpleGram_re_abs_le_one
    (T : ℝ)
    (hPois : Zeta23.ZeroSide.PoissonSq T (articleParams.atD T))
    (hc : 0 < (articleParams.atD T).a T * (articleParams.atD T).L T ^ 2)
    (i j : ArticleSimpleColumn T) :
    |(articleGlobalSimpleGram T i j).re| ≤ 1 := by
  exact
    v17_zeroSideSimpleGram_re_abs_le_one_of_column_norms
      Zeta23.zetaZeroConfig (articleParams.atD T) T (articlePhiHatConj T)
      (v17_articleSimpleSynthesis_column_normSq_le_one T hPois hc) i j

end HurtadoZeta23
