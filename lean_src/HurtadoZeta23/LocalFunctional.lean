import HurtadoZeta23.WindowCombinatorics
import Mathlib.Tactic

noncomputable section

namespace HurtadoZeta23

open scoped BigOperators

/-- The six consecutive normalized gaps in the seven-point window starting at `s`. -/
def windowGap (y : ℕ → ℝ) (s : ℕ) (j : Fin 6) : ℝ :=
  y (s + j.1 + 1) - y (s + j.1)

/-- The paper's pressure term `∑ p_j g_j` on the window beginning at `s`. -/
def localPressure (y : ℕ → ℝ) (s : ℕ) : ℝ :=
  ∑ j : Fin 6, pressure j * windowGap y s j

/--
The pair-energy part of the paper's `E₇`, written directly in global point
indices. `r0 = 0,...,5` represents paper separation `r = r0+1`; for that
separation, `i = 0,...,5-r0` enumerates the `7-r` pairs in the window.
-/
def localPairEnergy (w : ℕ → ℕ → ℝ) (s : ℕ) : ℝ :=
  ∑ r0 ∈ Finset.range 6,
    (2 / ((6 - r0 : ℕ) : ℝ)) *
      ∑ i ∈ Finset.range (6 - r0), w (s + i) (s + i + r0 + 1)

/-- The position-weighted seven-point functional `F_p` of equations (E7),(Fp). -/
def localFp (w : ℕ → ℕ → ℝ) (y : ℕ → ℝ) (s : ℕ) : ℝ :=
  localPressure y s + localPairEnergy w s

lemma localFp_eq (w : ℕ → ℕ → ℝ) (y : ℕ → ℝ) (s : ℕ) :
    localFp w y s = localPressure y s + localPairEnergy w s := rfl

/-- Ordered points give nonnegative gaps in every admissible seven-point window. -/
lemma windowGap_nonneg
    {m : ℕ} (y : ℕ → ℝ)
    (hmono : ∀ q < m - 1, y q ≤ y (q + 1))
    {s : ℕ} (hs : s < m - 6) (j : Fin 6) :
    0 ≤ windowGap y s j := by
  unfold windowGap
  have hj : j.1 ≤ 5 := Nat.le_pred_of_lt j.2
  have hq : s + j.1 < m - 1 := by omega
  exact sub_nonneg.mpr (hmono (s + j.1) hq)

/-- A semantic form of the computer-assisted seven-point certificate. -/
def SevenPointCertificate (w : ℕ → ℕ → ℝ) (y : ℕ → ℝ) (m : ℕ) : Prop :=
  ∀ s < m - 6, delta ≤ localFp w y s

/-- Summing the literal `F_p` certificate over all consecutive windows. -/
lemma summed_explicit_local_certificate
    {m : ℕ} (hm : 7 ≤ m)
    (w : ℕ → ℕ → ℝ) (y : ℕ → ℝ)
    (hcert : SevenPointCertificate w y m) :
    delta * ((m - 6 : ℕ) : ℝ)
      ≤ ∑ s ∈ Finset.range (m - 6), localFp w y s := by
  have hsum :
      (∑ s ∈ Finset.range (m - 6), delta)
        ≤ ∑ s ∈ Finset.range (m - 6), localFp w y s := by
    apply Finset.sum_le_sum
    intro s hs
    exact hcert s (Finset.mem_range.mp hs)
  calc
    delta * ((m - 6 : ℕ) : ℝ)
        = ∑ s ∈ Finset.range (m - 6), delta := by simp [mul_comm]
    _ ≤ ∑ s ∈ Finset.range (m - 6), localFp w y s := hsum

end HurtadoZeta23
