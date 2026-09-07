import HurtadoZeta23.LocalFunctional
import Mathlib.Tactic

namespace HurtadoZeta23

open scoped BigOperators

/-- The contribution of pairs at the fixed separation `r0+1`. -/
def pairBandEnergy (m r0 : ℕ) (w : ℕ → ℕ → ℝ) : ℝ :=
  ∑ a ∈ Finset.range (m - (r0 + 1)), w a (a + r0 + 1)

/-- The same global pair energy as `2 * ∑_{a<b} w(a,b)`, written by diagonals. -/
def globalPairEnergyNat (m : ℕ) (w : ℕ → ℕ → ℝ) : ℝ :=
  2 * ∑ r0 ∈ Finset.range (m - 1), pairBandEnergy m r0 w

/-- A shifted nonnegative sum is bounded by any larger initial range containing it. -/
lemma sum_shifted_range_le_range
    {n k N : ℕ} (f : ℕ → ℝ) (hf : ∀ a < N, 0 ≤ f a)
    (hbound : n + k ≤ N) :
    (∑ s ∈ Finset.range n, f (s + k)) ≤ ∑ a ∈ Finset.range N, f a := by
  let S : Finset ℕ := (Finset.range n).image (fun s => s + k)
  have hinj : Set.InjOn (fun s : ℕ => s + k) (↑(Finset.range n) : Set ℕ) := by
    intro a ha b hb hab
    exact Nat.add_right_cancel hab
  have hsum :
      (∑ a ∈ S, f a) = ∑ s ∈ Finset.range n, f (s + k) := by
    dsimp [S]
    exact Finset.sum_image hinj
  have hsub : S ⊆ Finset.range N := by
    intro a ha
    rcases Finset.mem_image.mp ha with ⟨s, hs, rfl⟩
    apply Finset.mem_range.mpr
    have hslt : s < n := Finset.mem_range.mp hs
    omega
  have hle : (∑ a ∈ S, f a) ≤ ∑ a ∈ Finset.range N, f a := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (by
      intro a ha haS
      exact hf a (Finset.mem_range.mp ha))
  rw [hsum] at hle
  exact hle

/-- Every shifted copy of a fixed-separation pair band is dominated by that band. -/
lemma shifted_pair_sum_le_band
    {m r0 i : ℕ} (hm : 7 ≤ m)
    (hr : r0 < 6) (hi : i < 6 - r0)
    (w : ℕ → ℕ → ℝ) (hw : ∀ a b, 0 ≤ w a b) :
    (∑ s ∈ Finset.range (m - 6),
        w (s + i) (s + i + r0 + 1))
      ≤ pairBandEnergy m r0 w := by
  unfold pairBandEnergy
  apply sum_shifted_range_le_range
    (f := fun a => w a (a + r0 + 1))
    (hf := fun a ha => hw a (a + r0 + 1))
  omega

/--
For one separation `r=r0+1`, summing all local positions and all windows costs
at most twice the corresponding global pair band.  This is where the factor
`7-r` cancels against `2/(7-r)`.
-/
lemma one_separation_local_pair_le
    {m r0 : ℕ} (hm : 7 ≤ m) (hr : r0 < 6)
    (w : ℕ → ℕ → ℝ) (hw : ∀ a b, 0 ≤ w a b) :
    (∑ s ∈ Finset.range (m - 6),
        (2 / ((6 - r0 : ℕ) : ℝ)) *
          ∑ i ∈ Finset.range (6 - r0),
            w (s + i) (s + i + r0 + 1))
      ≤ 2 * pairBandEnergy m r0 w := by
  have hdenNat : 0 < 6 - r0 := by omega
  have hden : (0 : ℝ) < ((6 - r0 : ℕ) : ℝ) := by exact_mod_cast hdenNat
  calc
    (∑ s ∈ Finset.range (m - 6),
        (2 / ((6 - r0 : ℕ) : ℝ)) *
          ∑ i ∈ Finset.range (6 - r0),
            w (s + i) (s + i + r0 + 1))
        = (2 / ((6 - r0 : ℕ) : ℝ)) *
            ∑ i ∈ Finset.range (6 - r0),
              ∑ s ∈ Finset.range (m - 6),
                w (s + i) (s + i + r0 + 1) := by
            rw [← Finset.mul_sum]
            congr 1
            rw [Finset.sum_comm]
    _ ≤ (2 / ((6 - r0 : ℕ) : ℝ)) *
          ∑ i ∈ Finset.range (6 - r0), pairBandEnergy m r0 w := by
            apply mul_le_mul_of_nonneg_left
            · apply Finset.sum_le_sum
              intro i hi
              exact shifted_pair_sum_le_band
                hm hr (Finset.mem_range.mp hi) w hw
            · positivity

    _ = (2 / ((6 - r0 : ℕ) : ℝ)) *
          (((6 - r0 : ℕ) : ℝ) * pairBandEnergy m r0 w) := by
            congr 1
            simp

    _ = 2 * pairBandEnergy m r0 w := by
          have hden0 : ((6 - r0 : ℕ) : ℝ) ≠ 0 := by
            exact ne_of_gt hden
          field_simp [hden0]

/-- The complete local pair part is bounded by the global pair energy. -/
lemma summed_localPairEnergy_le_global
    {m : ℕ} (hm : 7 ≤ m)
    (w : ℕ → ℕ → ℝ) (hw : ∀ a b, 0 ≤ w a b) :
    (∑ s ∈ Finset.range (m - 6), localPairEnergy w s)
      ≤ globalPairEnergyNat m w := by
  unfold localPairEnergy globalPairEnergyNat
  have hfirst :
      (∑ s ∈ Finset.range (m - 6),
        ∑ r0 ∈ Finset.range 6,
          (2 / ((6 - r0 : ℕ) : ℝ)) *
            ∑ i ∈ Finset.range (6 - r0), w (s + i) (s + i + r0 + 1))
      ≤ ∑ r0 ∈ Finset.range 6, 2 * pairBandEnergy m r0 w := by
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro r0 hr
    exact one_separation_local_pair_le hm (Finset.mem_range.mp hr) w hw
  have hbands_nonneg : ∀ r0, 0 ≤ pairBandEnergy m r0 w := by
    intro r0
    unfold pairBandEnergy
    exact Finset.sum_nonneg (fun a ha => hw a (a + r0 + 1))
  have hsubset : Finset.range 6 ⊆ Finset.range (m - 1) := by
    intro r0 hr
    apply Finset.mem_range.mpr
    have : r0 < 6 := Finset.mem_range.mp hr
    omega
  have hsecond :
      (∑ r0 ∈ Finset.range 6, pairBandEnergy m r0 w)
        ≤ ∑ r0 ∈ Finset.range (m - 1), pairBandEnergy m r0 w := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
      intro r0 hr hr6
      exact hbands_nonneg r0)
  calc
    (∑ s ∈ Finset.range (m - 6),
        ∑ r0 ∈ Finset.range 6,
          (2 / ((6 - r0 : ℕ) : ℝ)) *
            ∑ i ∈ Finset.range (6 - r0), w (s + i) (s + i + r0 + 1))
        ≤ ∑ r0 ∈ Finset.range 6, 2 * pairBandEnergy m r0 w := hfirst
    _ = 2 * ∑ r0 ∈ Finset.range 6, pairBandEnergy m r0 w := by rw [Finset.mul_sum]
    _ ≤ 2 * ∑ r0 ∈ Finset.range (m - 1), pairBandEnergy m r0 w := by
          exact mul_le_mul_of_nonneg_left hsecond (by norm_num)

/-- Every shifted copy of the global gap sequence is bounded by the total span. -/
lemma shifted_gap_sum_le_span
    {m : ℕ} (hm : 7 ≤ m) (y : ℕ → ℝ)
    (hmono : ∀ q < m - 1, y q ≤ y (q + 1))
    (j : Fin 6) :
    (∑ s ∈ Finset.range (m - 6), windowGap y s j)
      ≤ y (m - 1) - y 0 := by
  have hshift := sum_shifted_range_le_range
    (f := fun q => y (q + 1) - y q)
    (hf := fun q hq => sub_nonneg.mpr (hmono q hq))
    (n := m - 6) (k := j.1) (N := m - 1)
    (by
      have hj : j.1 < 6 := j.2
      omega)
  -- On the target range all gaps are nonnegative, and the full range telescopes.
  have htel := telescoping_gap_sum y (m - 1)
  unfold windowGap
  rw [htel] at hshift
  exact hshift

/-- The complete position-weighted pressure sum costs at most `beta * span`. -/
lemma summed_localPressure_le_span
    {m : ℕ} (hm : 7 ≤ m) (y : ℕ → ℝ)
    (hmono : ∀ q < m - 1, y q ≤ y (q + 1)) :
    (∑ s ∈ Finset.range (m - 6), localPressure y s)
      ≤ beta * (y (m - 1) - y 0) := by
  unfold localPressure
  rw [Finset.sum_comm]
  calc
    (∑ j : Fin 6, ∑ s ∈ Finset.range (m - 6), pressure j * windowGap y s j)
        = ∑ j : Fin 6, pressure j *
            (∑ s ∈ Finset.range (m - 6), windowGap y s j) := by
              apply Finset.sum_congr rfl
              intro j hj
              rw [Finset.mul_sum]
    _ ≤ ∑ j : Fin 6, pressure j * (y (m - 1) - y 0) := by
          apply Finset.sum_le_sum
          intro j hj
          exact mul_le_mul_of_nonneg_left
            (shifted_gap_sum_le_span hm y hmono j)
            (pressure_nonneg j)
    _ = beta * (y (m - 1) - y 0) := by
          rw [← Finset.sum_mul, pressure_sum]

/--
Pressure redistribution directly from the literal seven-point functional.
There is no reindexing hypothesis: both global estimates are proved by shifted
range injections and nonnegativity.
-/
theorem pressure_redistribution
    {m : ℕ} (hm : 7 ≤ m)
    (y : ℕ → ℝ)
    (hmono : ∀ q < m - 1, y q ≤ y (q + 1))
    (w : ℕ → ℕ → ℝ)
    (hw : ∀ a b, 0 ≤ w a b)
    (hcert : SevenPointCertificate w y m) :
    delta * ((m - 6 : ℕ) : ℝ)
      ≤ globalPairEnergyNat m w + beta * (y (m - 1) - y 0) := by
  have hlocal := summed_explicit_local_certificate hm w y hcert
  have hsplit :
      (∑ s ∈ Finset.range (m - 6), localFp w y s) =
        (∑ s ∈ Finset.range (m - 6), localPairEnergy w s) +
        (∑ s ∈ Finset.range (m - 6), localPressure y s) := by
    simp only [localFp, Finset.sum_add_distrib]
    ac_rfl
  rw [hsplit] at hlocal
  have hpairs := summed_localPairEnergy_le_global hm w hw
  have hpressure := summed_localPressure_le_span hm y hmono
  linarith

/-- The exact `m=262`, `A₀=624/625` specialization used in block stability. -/
theorem pressure_redistribution_262
    (y : ℕ → ℝ)
    (hmono : ∀ q < blockLength - 1, y q ≤ y (q + 1))
    (w : ℕ → ℕ → ℝ)
    (hw : ∀ a b, 0 ≤ w a b)
    (hcert : SevenPointCertificate w y blockLength) :
    A0 ≤ globalPairEnergyNat blockLength w +
      beta * (y (blockLength - 1) - y 0) := by
  have h := pressure_redistribution
    (m := blockLength) (by norm_num [blockLength]) y hmono w hw hcert
  have hA : delta * (((blockLength - 6 : ℕ) : ℝ)) = A0 := by
    norm_num [delta, blockLength, A0]
  rw [hA] at h
  exact h

end HurtadoZeta23
