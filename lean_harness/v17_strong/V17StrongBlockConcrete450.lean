import HurtadoZeta23.V17StrongBlockMatrix450
import HurtadoZeta23.V17Y450Order
import HurtadoZeta23.V17AnalyticBridge450
import Mathlib.Tactic

noncomputable section

open Matrix Finset
open scoped BigOperators ComplexOrder

namespace HurtadoZeta23

/-!
# Concrete v17 strong block for the actual retained Gram

This wrapper instantiates every finite/matrix interface of the abstract strong
block with the actual 450 retained columns.  It deliberately leaves the two
independent certificate frontiers explicit:

* the seven-point local certificate;
* the one-gap scalar pressure inequality.

The compact-overlap/Poisson hypotheses discharge PSD, the diagonal bound, and
the pointwise `kernel - 2 eps <= |Gram|^2` comparison internally.
-/

/-- The actual 450-point principal Gram is positive semidefinite. -/
theorem v17Gram450_posSemidef
    (T : ℝ) (s : ℕ)
    (hs : s + 450 ≤ articleRetainedCard T) :
    (v17Gram450 T s hs).PosSemidef := by
  unfold v17Gram450
  exact
    principal_submatrix_posSemidef
      (articleGlobalSimpleGram T)
      (articleGlobalSimpleGram_posSemidef T)
      (v17SimpleColumn450 T s hs)

/-- The pointwise Poisson normalization gives the one-sided diagonal bound
needed by the finite spectral threshold. -/
theorem v17Gram450_diag_re_le_one
    {T : ℝ}
    (hPois : Zeta23.ZeroSide.PoissonSq T (articleParams.atD T))
    (hnorm :
      0 <
        (articleParams.atD T).a T *
          (articleParams.atD T).L T ^ 2)
    (s : ℕ)
    (hs : s + 450 ≤ articleRetainedCard T) :
    ∀ i : Fin 450, (v17Gram450 T s hs i i).re ≤ 1 := by
  intro i
  unfold v17Gram450
  rw [principalGramBlock_apply]
  have habs :=
    articleGlobalSimpleGram_re_abs_le_one
      T hPois hnorm
      (v17SimpleColumn450 T s hs i)
      (v17SimpleColumn450 T s hs i)
  exact le_trans (le_abs_self _) habs

/-- Actual v17 strong-block inequality, conditional only on the two archived
certificate frontiers plus the explicit analytic hypotheses used by the
compact-overlap theorem. -/
theorem v17_actual_strong_block_450_of_interfaces
    {T : ℝ}
    (hPois : Zeta23.ZeroSide.PoissonSq T (articleParams.atD T))
    (hnorm :
      0 <
        (articleParams.atD T).a T *
          (articleParams.atD T).L T ^ 2)
    (hl : 0 < Zeta23.l T)
    (hwL : 8 * articleParams.w ≤ articleParams.L T)
    (hsmall :
      4 * articleParams.w / articleParams.L T
        ≤ limitingK 0 / 2)
    {M : ℕ}
    (hM1 : 1 ≤ M)
    (hM2 : (M : ℝ) + 2 ≤ (Zeta23.l T) ^ 2)
    (hkk : (0 : ℤ) ≤ articleLastGridIndex T)
    (s : ℕ)
    (hs : s + 450 ≤ articleRetainedCard T)
    (hcert :
      SevenPointCertificate
        (limitingWeightOnPoints (v17Y450 T s hs))
        (v17Y450 T s hs)
        450)
    (hscalar : ∀ q < 449,
      v17t * beta * v17g0 ≤
        limitingWeightOnPoints (v17Y450 T s hs) q (q + 1) +
          v17t * beta *
            (v17Y450 T s hs (q + 1) - v17Y450 T s hs q)) :
    v17A - 404100 * articleCompactError T M ≤
      gramSpectralDefect
          (v17Gram450 T s hs)
          (v17Gram450_posSemidef T s hs) +
        v17LiteralBlockPressure 450 (v17Y450 T s hs) := by
  let y : ℕ → ℝ := v17Y450 T s hs
  let w : ℕ → ℕ → ℝ := limitingWeightOnPoints y
  let G : Matrix (Fin 450) (Fin 450) ℂ := v17Gram450 T s hs
  let eps : ℝ := articleCompactError T M

  have hG : G.PosSemidef := by
    dsimp [G]
    exact v17Gram450_posSemidef T s hs

  have hdiag : ∀ i, (G i i).re ≤ 1 := by
    dsimp [G]
    exact v17Gram450_diag_re_le_one hPois hnorm s hs

  have heps : 0 ≤ eps := by
    dsimp [eps]
    exact articleCompactError_nonneg hl M

  have hw : ∀ a b, 0 ≤ w a b := by
    intro a b
    dsimp [w]
    unfold limitingWeightOnPoints
    exact limitingWeight_nonneg _

  have hpoint : ∀ a b, a < 450 → b < 450 →
      w a b - 2 * eps ≤ v17MatrixNormSqNat450 G a b := by
    intro a b ha hb
    have h :=
      v17_Gram450_pointwise_squared_lower
        hPois hnorm hl hwL hsmall hM1 hM2 hkk s hs a b ha hb
    dsimp [w, y, eps, G]
    simpa [v17MatrixNormSqNat450, ha, hb] using h

  have hcert' : SevenPointCertificate w y 450 := by
    simpa [w, y] using hcert

  have hscalar' : ∀ q < 449,
      v17t * beta * v17g0 ≤
        w q (q + 1) + v17t * beta * (y (q + 1) - y q) := by
    simpa [w, y] using hscalar

  have hstrong :=
    v17_strong_block_450_of_matrix_interfaces
      y w G hG hdiag eps heps hw hcert' hscalar' hpoint

  dsimp [y, w, G, eps] at hstrong
  simpa only [Subsingleton.elim hG (v17Gram450_posSemidef T s hs)] using hstrong

end HurtadoZeta23
