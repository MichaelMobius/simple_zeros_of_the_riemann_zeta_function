import HurtadoZeta23.V17ConcretePressure450
import HurtadoZeta23.V17ShiftedGramPinching450
import HurtadoZeta23.V17ShiftedAssembly450
import HurtadoZeta23.V17ConcreteStrongBlock450
import Mathlib.Tactic

noncomputable section

open Matrix Finset
open scoped BigOperators ComplexOrder

namespace HurtadoZeta23

/-- Totalized spectral defect of the actual consecutive retained 450-block. -/
noncomputable def v17ActualBlockDefect450
    (T : ℝ) (s : ℕ) : ℝ :=
  if hs : s + 450 ≤ articleRetainedCard T then
    v17BlockDefect450 T s hs
  else 0

lemma v17ActualBlockDefect450_of_fit
    (T : ℝ) (s : ℕ)
    (hs : s + 450 ≤ articleRetainedCard T) :
    v17ActualBlockDefect450 T s = v17BlockDefect450 T s hs := by
  simp [v17ActualBlockDefect450, hs]

/-- The concrete strong-block theorem rewritten in the global shifted-block
coordinates used by the finite assembly. -/
theorem v17_actual_local_strong_block_450
    (hcertExt : ArchivedSevenPointClaim)
    (hscalarExt : V17ScalarPressureClaim)
    {T : ℝ}
    (hPois : Zeta23.ZeroSide.PoissonSq T (articleParams.atD T))
    (hnorm : 0 < (articleParams.atD T).a T * (articleParams.atD T).L T ^ 2)
    (hl : 0 < Zeta23.l T)
    (hwL : 8 * articleParams.w ≤ articleParams.L T)
    (hsmall : 4 * articleParams.w / articleParams.L T ≤ limitingK 0 / 2)
    {M : ℕ}
    (hM1 : 1 ≤ M)
    (hM2 : (M : ℝ) + 2 ≤ (Zeta23.l T) ^ 2)
    (hkk : (0 : ℤ) ≤ articleLastGridIndex T)
    (s : ℕ)
    (hs : s + 450 ≤ articleRetainedCard T) :
    v17A - 404100 * v17ArticleCompactError T M ≤
      v17ActualBlockDefect450 T s + v17ActualBlockPressure450 T s := by
  have h :=
    v17_concrete_strong_block_450
      hcertExt hscalarExt hPois hnorm hl hwL hsmall
      hM1 hM2 hkk s hs
  rw [v17ActualBlockDefect450_of_fit T s hs]
  rw [v17ActualBlockPressure450_of_fit T s hs]
  have hdef := v17BlockDefect450_eq_Gram450 T s hs
  rw [hdef]
  simpa using h

/-- Range-indexed form of the 450-fold shifted Gram pinching estimate. -/
theorem v17_sum_actual_blockDefect450_le_stable
    (T : ℝ)
    (hS : 450 ≤ articleRetainedCard T) :
    (∑ s ∈ Finset.range (articleRetainedCard T - 450 + 1),
      v17ActualBlockDefect450 T s)
      ≤ (450 : ℝ) * articleStableDefect T := by
  have hfin := v17_sum_all_blockDefect450_le_stable T hS
  have heq :
      (∑ s ∈ Finset.range (articleRetainedCard T - 450 + 1),
        v17ActualBlockDefect450 T s)
        =
      (∑ s : Fin (articleRetainedCard T - 450 + 1),
        v17BlockDefect450
          T s.1
          (by
            have hs := s.2
            omega)) := by
    rw [Finset.sum_range]
    apply Finset.sum_congr rfl
    intro s hs_mem
    have hfit : s.1 + 450 ≤ articleRetainedCard T := by
      have hs := s.2
      omega
    rw [v17ActualBlockDefect450_of_fit T s.1 hfit]
    unfold v17BlockDefect450
    exact gramSpectralDefect_eq_of_matrix_eq
      (v17RetainedGramFinBlock450_posSemidef T s.1 hfit)
      (v17RetainedGramFinBlock450_posSemidef T s.1 (by
        have hs := s.2
        omega))
      rfl
  rw [heq]
  exact hfin

/-- Fully concrete finite-T shifted v17 inequality for retained cardinality at
least 450.  The local analytic loss is accumulated exactly over all complete
blocks and divided by the 450 shifted decompositions. -/
theorem v17_concrete_shifted_assembly_450
    (hcertExt : ArchivedSevenPointClaim)
    (hscalarExt : V17ScalarPressureClaim)
    {T : ℝ}
    (hS : 450 ≤ articleRetainedCard T)
    (hT : 0 ≤ T)
    (hPois : Zeta23.ZeroSide.PoissonSq T (articleParams.atD T))
    (hnorm : 0 < (articleParams.atD T).a T * (articleParams.atD T).L T ^ 2)
    (hl : 0 < Zeta23.l T)
    (hwL : 8 * articleParams.w ≤ articleParams.L T)
    (hsmall : 4 * articleParams.w / articleParams.L T ≤ limitingK 0 / 2)
    {M : ℕ}
    (hM1 : 1 ≤ M)
    (hM2 : (M : ℝ) + 2 ≤ (Zeta23.l T) ^ 2)
    (hkk : (0 : ℤ) ≤ articleLastGridIndex T) :
    v17Alpha * (articleRetainedCard T : ℝ)
      - v17PressureCost * samplingSpanScale T
      - v17EndpointCorrection
      - ((((articleRetainedCard T - 450 + 1 : ℕ) : ℝ) *
          (404100 * v17ArticleCompactError T M)) / 450)
      ≤ articleStableDefect T := by
  apply v17_shifted_assembly_from_uniform_blocks
    (S := articleRetainedCard T)
    hS
    (D := articleStableDefect T)
    (totalSpan := samplingSpanScale T)
    (e := 404100 * v17ArticleCompactError T M)
    (blockDef := v17ActualBlockDefect450 T)
    (pressure := v17ActualBlockPressure450 T)
  · intro b hb
    have hfit : b + 450 ≤ articleRetainedCard T := by omega
    exact v17_actual_local_strong_block_450
      hcertExt hscalarExt hPois hnorm hl hwL hsmall
      hM1 hM2 hkk b hfit
  · exact v17_sum_actual_block_pressure450_le_sampling
      T hS hT (le_of_lt hl)
  · exact v17_sum_actual_blockDefect450_le_stable T hS

end HurtadoZeta23