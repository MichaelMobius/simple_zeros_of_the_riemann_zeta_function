import Zeta23.Tail.Grid
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic

noncomputable section

open Finset Real
open scoped BigOperators

namespace HurtadoZeta23

/-- Two quadratic-decay bounds multiply to a summable fourth-power tail.
This is the abstract analytic estimate needed to truncate the cross-Poisson
identity from the full integer grid to the finite sampling grid. -/
theorem v17_cross_tail_of_quadratic_decay
    {D h C : ℝ}
    (hD : 0 < D) (hh : 0 < h) (hC : 0 ≤ C)
    (f g : ℕ → ℝ)
    (hf : ∀ n, |f n| ≤ C * ((D + n * h) ^ 2)⁻¹)
    (hg : ∀ n, |g n| ≤ C * ((D + n * h) ^ 2)⁻¹) :
    (∑' n : ℕ, |f n * g n|)
      ≤ C ^ 2 * ((D ^ 4)⁻¹ + (D ^ 3)⁻¹ / (3 * h)) := by
  apply Real.tsum_le_of_sum_range_le
  · intro n
    exact abs_nonneg _
  · intro N
    calc
      (∑ n ∈ range N, |f n * g n|)
          ≤ ∑ n ∈ range N, C ^ 2 * ((D + n * h) ^ 4)⁻¹ := by
              apply Finset.sum_le_sum
              intro n hn
              rw [abs_mul]
              have hx : 0 < D + n * h := by positivity
              calc
                |f n| * |g n|
                    ≤ (C * ((D + n * h) ^ 2)⁻¹) *
                      (C * ((D + n * h) ^ 2)⁻¹) := by
                        exact mul_le_mul (hf n) (hg n) (abs_nonneg _) (by positivity)
                _ = C ^ 2 * ((D + n * h) ^ 4)⁻¹ := by
                      field_simp [hx.ne']
      _ = C ^ 2 * (∑ n ∈ range N, ((D + n * h) ^ 4)⁻¹) := by
            rw [Finset.mul_sum]
      _ ≤ C ^ 2 * ((D ^ 4)⁻¹ + (D ^ 3)⁻¹ / (3 * h)) := by
            exact mul_le_mul_of_nonneg_left
              (Zeta23.Tail.sum_inv_pow_four_le hD hh N) (sq_nonneg C)

end HurtadoZeta23
