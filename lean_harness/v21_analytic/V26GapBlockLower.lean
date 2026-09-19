import HurtadoZeta23.V26WordBridge
import Mathlib.Tactic

noncomputable section
namespace HurtadoZeta23

/-- Generic linear assembly of the 21 contiguous-block lower bounds entering
`v26GapF`.  The `b00,...,b50` variables are arbitrary real lower bounds for
the six blocks of length 1, five of length 2, ..., one of length 6.

Keeping this theorem symbolic separates the trivial positive weighted sum from
the nonlinear formulas used to obtain each block lower bound. -/
theorem v26_gapF_lower_of_block_lowers
    (weight : ℝ → ℝ)
    (g0 g1 g2 g3 g4 g5 : ℝ)
    (b00 b01 b02 b03 b04 b05 : ℝ)
    (b10 b11 b12 b13 b14 : ℝ)
    (b20 b21 b22 b23 : ℝ)
    (b30 b31 b32 : ℝ)
    (b40 b41 : ℝ)
    (b50 : ℝ)
    (h00 : b00 ≤ weight g0)
    (h01 : b01 ≤ weight g1)
    (h02 : b02 ≤ weight g2)
    (h03 : b03 ≤ weight g3)
    (h04 : b04 ≤ weight g4)
    (h05 : b05 ≤ weight g5)
    (h10 : b10 ≤ weight (g0 + g1))
    (h11 : b11 ≤ weight (g1 + g2))
    (h12 : b12 ≤ weight (g2 + g3))
    (h13 : b13 ≤ weight (g3 + g4))
    (h14 : b14 ≤ weight (g4 + g5))
    (h20 : b20 ≤ weight (g0 + g1 + g2))
    (h21 : b21 ≤ weight (g1 + g2 + g3))
    (h22 : b22 ≤ weight (g2 + g3 + g4))
    (h23 : b23 ≤ weight (g3 + g4 + g5))
    (h30 : b30 ≤ weight (g0 + g1 + g2 + g3))
    (h31 : b31 ≤ weight (g1 + g2 + g3 + g4))
    (h32 : b32 ≤ weight (g2 + g3 + g4 + g5))
    (h40 : b40 ≤ weight (g0 + g1 + g2 + g3 + g4))
    (h41 : b41 ≤ weight (g1 + g2 + g3 + g4 + g5))
    (h50 : b50 ≤ weight (g0 + g1 + g2 + g3 + g4 + g5)) :
    v26Pressure 0 * g0 +
      v26Pressure 1 * g1 +
      v26Pressure 2 * g2 +
      v26Pressure 3 * g3 +
      v26Pressure 4 * g4 +
      v26Pressure 5 * g5 +
      (1 / 3 : ℝ) * (b00 + b01 + b02 + b03 + b04 + b05) +
      (2 / 5 : ℝ) * (b10 + b11 + b12 + b13 + b14) +
      (1 / 2 : ℝ) * (b20 + b21 + b22 + b23) +
      (2 / 3 : ℝ) * (b30 + b31 + b32) +
      b40 + b41 + 2 * b50 ≤
        v26GapF weight g0 g1 g2 g3 g4 g5 := by
  unfold v26GapF
  linarith

end HurtadoZeta23
