import HurtadoZeta23.V26QuadraticCore
import Mathlib.Tactic

noncomputable section

open scoped BigOperators

namespace HurtadoZeta23

/-- Six-coordinate wrapper around `v26_weighted_cauchy_of_energy`.

The bootstrap certificates are six-dimensional.  Keeping this normalization
lemma separate prevents every generated contraction theorem from repeatedly
expanding `Fin 6` sums and reassociating the same six terms. -/
theorem v26_weighted_cauchy6_of_energy
    (a0 a1 a2 a3 a4 a5 : ℝ)
    (y0 y1 y2 y3 y4 y5 : ℝ)
    (d0 d1 d2 d3 d4 d5 gap : ℝ)
    (hd0 : 0 < d0) (hd1 : 0 < d1) (hd2 : 0 < d2)
    (hd3 : 0 < d3) (hd4 : 0 < d4) (hd5 : 0 < d5)
    (henergy :
      d0 * y0 ^ 2 + d1 * y1 ^ 2 + d2 * y2 ^ 2 +
      d3 * y3 ^ 2 + d4 * y4 ^ 2 + d5 * y5 ^ 2 ≤ gap) :
    (a0 * y0 + a1 * y1 + a2 * y2 + a3 * y3 + a4 * y4 + a5 * y5) ^ 2 ≤
      gap *
        (a0 ^ 2 / d0 + a1 ^ 2 / d1 + a2 ^ 2 / d2 +
         a3 ^ 2 / d3 + a4 ^ 2 / d4 + a5 ^ 2 / d5) := by
  let a : Fin 6 → ℝ := ![a0, a1, a2, a3, a4, a5]
  let y : Fin 6 → ℝ := ![y0, y1, y2, y3, y4, y5]
  let d : Fin 6 → ℝ := ![d0, d1, d2, d3, d4, d5]
  have hd : ∀ i, 0 < d i := by
    intro i
    fin_cases i <;> simp [d, hd0, hd1, hd2, hd3, hd4, hd5]
  have he : (∑ i, d i * (y i) ^ 2) ≤ gap := by
    simp [d, y, Fin.sum_univ_succ]
    ring_nf at henergy ⊢
    exact henergy
  have h := v26_weighted_cauchy_of_energy a y d hd gap he
  simp [a, y, d, Fin.sum_univ_succ] at h
  convert h using 1 <;> ring

end HurtadoZeta23
