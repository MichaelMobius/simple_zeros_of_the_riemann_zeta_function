import HurtadoZeta23.DirectRedistribution
import HurtadoZeta23.V17StrongBlockScalar
import Mathlib.Tactic

noncomputable section

namespace HurtadoZeta23

open scoped BigOperators

/-- Literal v17 block pressure: the sum of the position-weighted pressure over
all consecutive seven-point windows. Keeping it in this form avoids an
unnecessary explicit `q_r` array in the strong-block argument. -/
def v17LiteralBlockPressure (m : ℕ) (y : ℕ → ℝ) : ℝ :=
  ∑ s ∈ Finset.range (m - 6), localPressure y s

/-- The total pressure mass of the literal window sum is exactly
`beta * (m-6)`. This is just the number of windows times `sum_j p_j`. -/
theorem v17_literal_pressure_mass
    {m : ℕ} :
    (∑ _s ∈ Finset.range (m - 6), ∑ j : Fin 6, pressure j)
      = beta * ((m - 6 : ℕ) : ℝ) := by
  rw [pressure_sum]
  simp [mul_comm]

/-- Weighted adjacent-energy inequality.

Assume the one-gap scalar estimate
`w(q,q+1) + t*beta*g_q ≥ t*beta*g0` for every global gap. Multiply the
estimate at relative position `j` by `p_j`, sum over all local windows, and
use the shifted-band injection. Because `sum_j p_j = beta`, the allocated
adjacent energy costs at most one full adjacent band. After cancelling the
positive factor `beta`, one obtains exactly the v17 lower bound

`W_adj + t P_B ≥ t g0 beta (m-6)`.
-/
theorem v17_weighted_adjacent_pressure
    {m : ℕ} (hm : 7 ≤ m)
    (y : ℕ → ℝ)
    (w : ℕ → ℕ → ℝ)
    (hw : ∀ a b, 0 ≤ w a b)
    (hscalar : ∀ q < m - 1,
      v17t * beta * v17g0 ≤
        w q (q + 1) + v17t * beta * (y (q + 1) - y q)) :
    v17t * v17g0 * (beta * ((m - 6 : ℕ) : ℝ)) ≤
      pairBandEnergy m 0 w + v17t * v17LiteralBlockPressure m y := by
  have hbeta : 0 < beta := by norm_num [beta]

  have hshift (j : Fin 6) :
      (∑ s ∈ Finset.range (m - 6), w (s + j.1) (s + j.1 + 1))
        ≤ pairBandEnergy m 0 w := by
    exact shifted_pair_sum_le_band
      hm (r0 := 0) (i := j.1) (by norm_num) j.2 w hw

  have halloc :
      (∑ j : Fin 6,
          pressure j *
            (∑ s ∈ Finset.range (m - 6), w (s + j.1) (s + j.1 + 1)))
        ≤ beta * pairBandEnergy m 0 w := by
    calc
      (∑ j : Fin 6,
          pressure j *
            (∑ s ∈ Finset.range (m - 6), w (s + j.1) (s + j.1 + 1)))
          ≤ ∑ j : Fin 6, pressure j * pairBandEnergy m 0 w := by
              apply Finset.sum_le_sum
              intro j hj
              exact mul_le_mul_of_nonneg_left (hshift j) (pressure_nonneg j)
      _ = (∑ j : Fin 6, pressure j) * pairBandEnergy m 0 w := by
            rw [Finset.sum_mul]
      _ = beta * pairBandEnergy m 0 w := by rw [pressure_sum]

  have hlocal :
      (∑ j : Fin 6, ∑ s ∈ Finset.range (m - 6),
          pressure j * (v17t * beta * v17g0))
        ≤
      (∑ j : Fin 6, ∑ s ∈ Finset.range (m - 6),
          pressure j *
            (w (s + j.1) (s + j.1 + 1) +
              v17t * beta * (y (s + j.1 + 1) - y (s + j.1)))) := by
    apply Finset.sum_le_sum
    intro j hj
    apply Finset.sum_le_sum
    intro s hs
    have hq : s + j.1 < m - 1 := by
      have hslt : s < m - 6 := Finset.mem_range.mp hs
      have hj : j.1 < 6 := j.2
      omega
    exact mul_le_mul_of_nonneg_left (hscalar (s + j.1) hq) (pressure_nonneg j)

  have hleft :
      (∑ j : Fin 6, ∑ s ∈ Finset.range (m - 6),
          pressure j * (v17t * beta * v17g0))
        = beta * (v17t * beta * v17g0) * ((m - 6 : ℕ) : ℝ) := by
    calc
      (∑ j : Fin 6, ∑ s ∈ Finset.range (m - 6),
          pressure j * (v17t * beta * v17g0))
          = ∑ j : Fin 6,
              ((m - 6 : ℕ) : ℝ) * (pressure j * (v17t * beta * v17g0)) := by
                apply Finset.sum_congr rfl
                intro j hj
                simp
      _ = ((m - 6 : ℕ) : ℝ) *
            ((∑ j : Fin 6, pressure j) * (v17t * beta * v17g0)) := by
              rw [← Finset.mul_sum]
              congr 1
              rw [Finset.sum_mul]
      _ = beta * (v17t * beta * v17g0) * ((m - 6 : ℕ) : ℝ) := by
            rw [pressure_sum]
            ring

  have hright :
      (∑ j : Fin 6, ∑ s ∈ Finset.range (m - 6),
          pressure j *
            (w (s + j.1) (s + j.1 + 1) +
              v17t * beta * (y (s + j.1 + 1) - y (s + j.1))))
        =
      (∑ j : Fin 6,
          pressure j *
            (∑ s ∈ Finset.range (m - 6), w (s + j.1) (s + j.1 + 1)))
        + v17t * beta * v17LiteralBlockPressure m y := by
    unfold v17LiteralBlockPressure localPressure windowGap
    simp_rw [mul_add, Finset.sum_add_distrib]
    rw [Finset.sum_add_distrib]
    congr 1
    · apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mul_sum]
    · calc
        (∑ j : Fin 6, ∑ s ∈ Finset.range (m - 6),
            pressure j *
              (v17t * beta * (y (s + j.1 + 1) - y (s + j.1))))
            = v17t * beta *
                (∑ j : Fin 6, ∑ s ∈ Finset.range (m - 6),
                  pressure j * (y (s + j.1 + 1) - y (s + j.1))) := by
                simp_rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro j hj
                apply Finset.sum_congr rfl
                intro s hs
                ring
        _ = v17t * beta *
              (∑ s ∈ Finset.range (m - 6), ∑ j : Fin 6,
                pressure j * (y (s + j.1 + 1) - y (s + j.1))) := by
                apply congrArg (fun z : ℝ => v17t * beta * z)
                rw [Finset.sum_comm]

  rw [hleft, hright] at hlocal
  have hcombined :
      beta * (v17t * beta * v17g0) * ((m - 6 : ℕ) : ℝ)
        ≤ beta * pairBandEnergy m 0 w +
            v17t * beta * v17LiteralBlockPressure m y := by
    linarith
  have hfactor :
      beta *
          (v17t * v17g0 * (beta * ((m - 6 : ℕ) : ℝ)))
        ≤ beta *
          (pairBandEnergy m 0 w + v17t * v17LiteralBlockPressure m y) := by
    nlinarith
  have hfactor' := hfactor
  norm_num [beta] at hfactor' ⊢
  linarith

end HurtadoZeta23
