import Zeta23.Tail.Grid
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic

noncomputable section

open Finset Real
open scoped BigOperators

namespace HurtadoZeta23

/-- Promote the finite telescoping estimate already proved in `Zeta23.Tail.Grid`
to the corresponding infinite arithmetic-grid tail.  This is the numerical
core of the finite-vs-infinite Gabor overlap truncation. -/
theorem v17_tsum_inv_pow_four_grid_tail
    {D h : ℝ} (hD : 0 < D) (hh : 0 < h) :
    (∑' n : ℕ, ((D + n * h) ^ 4)⁻¹)
      ≤ (D ^ 4)⁻¹ + (D ^ 3)⁻¹ / (3 * h) := by
  apply Real.tsum_le_of_sum_range_le
  · intro n
    positivity
  · intro n
    exact Zeta23.Tail.sum_inv_pow_four_le hD hh n

/-- Specialize the infinite tail to the sampling mesh `h = 2π/L`, in the
same coarse form used by the finite-grid estimate of `Zeta23.Tail.Grid`. -/
theorem v17_tsum_inv_pow_four_sampling_grid_le
    {D L : ℝ} (hD : 1 ≤ D) (hL : 2 ≤ L) :
    (∑' n : ℕ, ((D + n * (2 * Real.pi / L)) ^ 4)⁻¹)
      ≤ L * (D ^ 3)⁻¹ := by
  have hD0 : 0 < D := by linarith
  have hmesh : 0 < 2 * Real.pi / L := by
    have hL0 : 0 < L := by linarith
    positivity
  exact (v17_tsum_inv_pow_four_grid_tail hD0 hmesh).trans
    (Zeta23.Tail.grid_const_bound hD hL)

/-- If the omitted grid begins at physical distance at least `2π L`, as it
does after deleting `L²` normalized grid steps, the fourth-power tail is
`O(L⁻²)` with an explicit coarse constant. -/
theorem v17_tsum_inv_pow_four_after_L_sq_steps
    {L : ℝ} (hL : 2 ≤ L) :
    (∑' n : ℕ,
      (((2 * Real.pi * L) + n * (2 * Real.pi / L)) ^ 4)⁻¹)
      ≤ (1 / 64 : ℝ) * (L ^ 2)⁻¹ := by
  have hD : 1 ≤ 2 * Real.pi * L := by
    have hpi : 2 ≤ Real.pi := Real.two_le_pi
    nlinarith
  have h0 := v17_tsum_inv_pow_four_sampling_grid_le hD hL
  have hL0 : 0 < L := by linarith
  have hpi : 2 ≤ Real.pi := Real.two_le_pi
  calc
    (∑' n : ℕ,
      (((2 * Real.pi * L) + n * (2 * Real.pi / L)) ^ 4)⁻¹)
        ≤ L * (((2 * Real.pi * L) ^ 3)⁻¹) := h0
    _ ≤ L * (((4 * L) ^ 3)⁻¹) := by
          gcongr
          apply inv_anti₀ <;> positivity
          exact pow_le_pow_left₀ (by positivity) (by nlinarith) 3
    _ = (1 / 64 : ℝ) * (L ^ 2)⁻¹ := by
          field_simp [hL0.ne']
          ring

end HurtadoZeta23
