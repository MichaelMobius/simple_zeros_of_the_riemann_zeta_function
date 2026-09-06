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
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, RCLike.conj_mul]

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
  have hz := hPois z.1 z.2
  have hsqrt := sq_sqrt_mult_div (m := D.m z.1) hc
  have hcoeff : (Real.sqrt ((D.m z.1 : ℝ) / c)) ^ 2 = c⁻¹ := by
    rw [hsqrt, hm]
    norm_num
    rw [div_eq_mul_inv]
  calc
    (∑ k, ‖simpleOnLineSynthesis D c k z‖ ^ 2)
        = c⁻¹ * ∑ k, ‖D.v z.1 k‖ ^ 2 := by
            simp_rw [simpleOnLineSynthesis, norm_mul, RCLike.norm_ofReal,
              Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow]
            rw [← Finset.mul_sum]
            congr 1
            exact hcoeff
    _ ≤ c⁻¹ * c :=
      mul_le_mul_of_nonneg_left hz (inv_nonneg.mpr hc.le)
    _ = 1 := inv_mul_cancel₀ hc.ne'

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
