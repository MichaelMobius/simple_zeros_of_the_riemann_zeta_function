import HurtadoZeta23.V17ShiftedPressure450
import HurtadoZeta23.V17AnalyticBridge450
import HurtadoZeta23.RetainedSpanBridge
import Mathlib.Tactic

noncomputable section

open Finset
open scoped BigOperators

namespace HurtadoZeta23

/-- Totalized normalized ordinate sequence of all retained columns.  Only
indices below `articleRetainedCard T` are used in the concrete shifted
argument. -/
noncomputable def v17RetainedYNat (T : ℝ) (q : ℕ) : ℝ :=
  if hq : q < articleRetainedCard T then
    orderedRetainedY T ⟨q, hq⟩
  else 0

lemma v17RetainedYNat_eq
    (T : ℝ) {q : ℕ}
    (hq : q < articleRetainedCard T) :
    v17RetainedYNat T q = orderedRetainedY T ⟨q, hq⟩ := by
  simp [v17RetainedYNat, hq]

/-- On its genuine retained range the totalized sequence is nondecreasing. -/
theorem v17RetainedYNat_mono
    {T : ℝ}
    (hL : 0 ≤ articleParams.L T) :
    ∀ q < articleRetainedCard T - 1,
      v17RetainedYNat T q ≤ v17RetainedYNat T (q + 1) := by
  intro q hq
  have hq0 : q < articleRetainedCard T := by omega
  have hq1 : q + 1 < articleRetainedCard T := by omega
  rw [v17RetainedYNat_eq T hq0, v17RetainedYNat_eq T hq1]
  apply orderedRetainedY_mono hL
  change q ≤ q + 1
  omega

/-- The local totalization used in the analytic 450-block is the restriction
of the global retained ordinate sequence to the shifted interval. -/
lemma v17Y450_eq_v17RetainedYNat_shift
    (T : ℝ) (s : ℕ)
    (hs : s + 450 ≤ articleRetainedCard T)
    {a : ℕ} (ha : a < 450) :
    v17Y450 T s hs a = v17RetainedYNat T (s + a) := by
  have hsa : s + a < articleRetainedCard T := by omega
  rw [v17Y450_of_lt T s hs ha]
  rw [v17RetainedYNat_eq T hsa]
  rfl

/-- Literal local pressure of an actual 450-block agrees exactly with the
corresponding shifted pressure of the global retained ordinate sequence. -/
theorem v17_block_pressure_eq_shiftedRetained
    (T : ℝ) (s : ℕ)
    (hs : s + 450 ≤ articleRetainedCard T) :
    v17LiteralBlockPressure 450 (v17Y450 T s hs) =
      v17ShiftedLiteralPressure450 (v17RetainedYNat T) s := by
  unfold v17ShiftedLiteralPressure450 v17LiteralBlockPressure
  apply Finset.sum_congr rfl
  intro u hu
  unfold localPressure
  apply Finset.sum_congr rfl
  intro j hj
  unfold windowGap
  have hu0 : u < 444 := Finset.mem_range.mp hu
  have hj0 : j.1 < 6 := j.2
  have ha : u + j.1 < 450 := by omega
  have hb : u + j.1 + 1 < 450 := by omega
  rw [v17Y450_eq_v17RetainedYNat_shift T s hs ha]
  rw [v17Y450_eq_v17RetainedYNat_shift T s hs hb]
  simp only [Nat.add_assoc]

/-- Totalized actual local pressure; outside the full-block range it is zero. -/
noncomputable def v17ActualBlockPressure450
    (T : ℝ) (s : ℕ) : ℝ :=
  if hs : s + 450 ≤ articleRetainedCard T then
    v17LiteralBlockPressure 450 (v17Y450 T s hs)
  else 0

lemma v17ActualBlockPressure450_of_fit
    (T : ℝ) (s : ℕ)
    (hs : s + 450 ≤ articleRetainedCard T) :
    v17ActualBlockPressure450 T s =
      v17LiteralBlockPressure 450 (v17Y450 T s hs) := by
  simp [v17ActualBlockPressure450, hs]

/-- Endpoint span of the concrete global retained ordinate sequence is bounded
by the universal sampling span. -/
theorem v17RetainedYNat_span_le_sampling
    (T : ℝ)
    (hS : 450 ≤ articleRetainedCard T)
    (hT : 0 ≤ T)
    (hl : 0 ≤ Zeta23.l T) :
    v17RetainedYNat T (articleRetainedCard T - 1) -
        v17RetainedYNat T 0
      ≤ samplingSpanScale T := by
  have hSold : blockLength ≤ articleRetainedCard T := by
    norm_num [blockLength]
    omega
  have hspan :=
    articleRetainedTotalSpan_le_samplingSpanScale T hSold hT hl
  rw [articleRetainedTotalSpan_eq_endpoints T hSold] at hspan
  have hpos : 0 < articleRetainedCard T := by omega
  have hlast : articleRetainedCard T - 1 < articleRetainedCard T := by omega
  rw [v17RetainedYNat_eq T hlast]
  rw [v17RetainedYNat_eq T hpos]
  exact hspan

/-- Exact-pressure averaging for the actual retained 450-blocks, already in
the sampling-span form needed by the global v17 assembly. -/
theorem v17_sum_actual_block_pressure450_le_sampling
    (T : ℝ)
    (hS : 450 ≤ articleRetainedCard T)
    (hT : 0 ≤ T)
    (hl : 0 ≤ Zeta23.l T) :
    (∑ b ∈ Finset.range (articleRetainedCard T - 450 + 1),
      v17ActualBlockPressure450 T b)
      ≤ v17Q * samplingSpanScale T := by
  have hL : 0 ≤ articleParams.L T := by
    simpa [articleParams_L_eq_zeta_l] using hl
  have hmono := v17RetainedYNat_mono hL
  have hshift :=
    v17_sum_shifted_literal_pressure450_le
      hS (v17RetainedYNat T) hmono
  have hspan := v17RetainedYNat_span_le_sampling T hS hT hl
  have hQ : 0 ≤ v17Q := by norm_num [v17Q]
  calc
    (∑ b ∈ Finset.range (articleRetainedCard T - 450 + 1),
      v17ActualBlockPressure450 T b)
        =
      ∑ b ∈ Finset.range (articleRetainedCard T - 450 + 1),
        v17ShiftedLiteralPressure450 (v17RetainedYNat T) b := by
          apply Finset.sum_congr rfl
          intro b hb
          have hfit : b + 450 ≤ articleRetainedCard T := by
            have hb' := Finset.mem_range.mp hb
            omega
          rw [v17ActualBlockPressure450_of_fit T b hfit]
          exact v17_block_pressure_eq_shiftedRetained T b hfit
    _ ≤ v17Q *
          (v17RetainedYNat T (articleRetainedCard T - 1) -
            v17RetainedYNat T 0) := hshift
    _ ≤ v17Q * samplingSpanScale T :=
      mul_le_mul_of_nonneg_left hspan hQ

end HurtadoZeta23