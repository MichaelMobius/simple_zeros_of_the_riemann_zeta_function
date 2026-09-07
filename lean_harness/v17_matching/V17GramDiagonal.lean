import HurtadoZeta23.OnLineSynthesis
import HurtadoZeta23.PrincipalGramBlocks
import Mathlib.Tactic

noncomputable section

open Matrix Finset
open scoped BigOperators ComplexOrder

namespace HurtadoZeta23

section AbstractGram

variable {row col : Type*}
variable [Fintype row] [DecidableEq row] [Fintype col] [DecidableEq col]

/-- A diagonal entry of `VᴴV` is the squared norm of the corresponding
column. -/
theorem v17_gram_diag_re_eq_column_norm_sq
    (V : Matrix row col ℂ) (z : col) :
    ((V.conjTranspose * V) z z).re = ∑ k, ‖V k z‖ ^ 2 := by
  classical
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [RCLike.star_def, RCLike.conj_mul]
  exact RCLike.re_ofReal_pow (K := ℂ) (‖V k z‖) 2

/-- Column norm at most one implies the real Gram diagonal is at most one. -/
theorem v17_gram_diag_re_le_one_of_column_norm_sq_le_one
    (V : Matrix row col ℂ)
    (hcol : ∀ z, (∑ k, ‖V k z‖ ^ 2) ≤ 1) :
    ∀ z, ((V.conjTranspose * V) z z).re ≤ 1 := by
  intro z
  rw [v17_gram_diag_re_eq_column_norm_sq]
  exact hcol z

end AbstractGram

section SimpleColumns

variable {ι d : Type*}
variable [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d]

/-- The pointwise Poisson bound already used in the trace argument gives norm
at most one for every normalized simple-zero synthesis column. -/
theorem v17_simpleOnLineSynthesis_column_norm_sq_le_one
    (D : Zeta23.ZeroSide.ZeroBlockData ι d)
    {c : ℝ} (hc : 0 < c)
    (hPois : ∀ z ∈ D.S₁, ∑ k, ‖D.v z k‖ ^ 2 ≤ c) :
    ∀ z : SimpleOnLineColumn D,
      (∑ k, ‖simpleOnLineSynthesis D c k z‖ ^ 2) ≤ 1 := by
  intro z
  have hm : D.m z.1 = 1 := mult_eq_one_of_mem_S₁ D z.2
  have hz : (∑ k, ‖D.v z.1 k‖ ^ 2) ≤ c := hPois z.1 z.2
  have hsqrt :
      (Real.sqrt ((D.m z.1 : ℝ) / c)) ^ 2 =
        (D.m z.1 : ℝ) / c := by
    exact sq_sqrt_mult_div hc
  change
    (∑ k,
      ‖(((Real.sqrt ((D.m z.1 : ℝ) / c) : ℝ) : ℂ) *
          D.v z.1 k)‖ ^ 2) ≤ 1
  calc
    (∑ k,
      ‖(((Real.sqrt ((D.m z.1 : ℝ) / c) : ℝ) : ℂ) *
          D.v z.1 k)‖ ^ 2)
        = ∑ k,
            ((D.m z.1 : ℝ) / c) * ‖D.v z.1 k‖ ^ 2 := by
              apply Finset.sum_congr rfl
              intro k hk
              rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
              rw [abs_of_nonneg (Real.sqrt_nonneg _)]
              rw [mul_pow]
              rw [hsqrt]
    _ = ((D.m z.1 : ℝ) / c) *
          (∑ k, ‖D.v z.1 k‖ ^ 2) := by
            rw [Finset.mul_sum]
    _ = (1 / c) * (∑ k, ‖D.v z.1 k‖ ^ 2) := by
          rw [hm]
          norm_num
    _ ≤ (1 / c) * c := by
          exact mul_le_mul_of_nonneg_left hz (by positivity)
    _ = 1 := by
          field_simp

/-- Pointwise diagonal bound for the normalized simple-zero Gram matrix. -/
theorem v17_simpleOnLineGram_diag_re_le_one
    (D : Zeta23.ZeroSide.ZeroBlockData ι d)
    {c : ℝ} (hc : 0 < c)
    (hPois : ∀ z ∈ D.S₁, ∑ k, ‖D.v z k‖ ^ 2 ≤ c) :
    ∀ z : SimpleOnLineColumn D,
      (((simpleOnLineSynthesis D c).conjTranspose *
          simpleOnLineSynthesis D c) z z).re ≤ 1 := by
  exact v17_gram_diag_re_le_one_of_column_norm_sq_le_one
    (simpleOnLineSynthesis D c)
    (v17_simpleOnLineSynthesis_column_norm_sq_le_one D hc hPois)

/-- Any principal block selected from that Gram inherits the same diagonal
bound. -/
theorem v17_principal_simpleOnLineGram_diag_re_le_one
    (D : Zeta23.ZeroSide.ZeroBlockData ι d)
    {c : ℝ} (hc : 0 < c)
    (hPois : ∀ z ∈ D.S₁, ∑ k, ‖D.v z k‖ ^ 2 ≤ c)
    {blk : Type*} [Fintype blk] [DecidableEq blk]
    (e : blk → SimpleOnLineColumn D) :
    ∀ i : blk,
      (principalGramBlock
        ((simpleOnLineSynthesis D c).conjTranspose * simpleOnLineSynthesis D c)
        e i i).re ≤ 1 := by
  intro i
  rw [principalGramBlock_apply]
  exact v17_simpleOnLineGram_diag_re_le_one D hc hPois (e i)

end SimpleColumns

end HurtadoZeta23
