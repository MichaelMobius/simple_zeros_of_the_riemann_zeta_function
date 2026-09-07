import HurtadoZeta23.ExternalCertificateFrontier
import HurtadoZeta23.V17AnalyticBridge450
import HurtadoZeta23.V17StrongBlockMatrix450
import HurtadoZeta23.V17ScalarPressureFrontier
import Mathlib.Tactic

noncomputable section

open Matrix Finset Real Filter Topology
open scoped BigOperators ComplexOrder

namespace HurtadoZeta23

/-- The normalized ordinates of every actual v17 450-point retained block are
nondecreasing. -/
theorem v17Y450_mono
    {T : ℝ}
    (hL : 0 ≤ articleParams.L T)
    (s : ℕ)
    (hs : s + 450 ≤ articleRetainedCard T) :
    ∀ q < 449,
      v17Y450 T s hs q ≤ v17Y450 T s hs (q + 1) := by
  intro q hq
  have hq0 : q < 450 := by omega
  have hq1 : q + 1 < 450 := by omega
  rw [v17Y450_of_lt T s hs hq0]
  rw [v17Y450_of_lt T s hs hq1]
  apply orderedRetainedY_mono hL
  change s + q ≤ s + (q + 1)
  omega

/-- Every actual v17 principal Gram block is PSD. -/
theorem v17Gram450_posSemidef
    (T : ℝ)
    (s : ℕ)
    (hs : s + 450 ≤ articleRetainedCard T) :
    (v17Gram450 T s hs).PosSemidef := by
  unfold v17Gram450
  exact principal_submatrix_posSemidef
    (articleGlobalSimpleGram T)
    (articleGlobalSimpleGram_posSemidef T)
    (v17SimpleColumn450 T s hs)

/-- The Poisson unit-column bound gives the diagonal hypothesis required by
the finite spectral threshold on the actual 450-point Gram block. -/
theorem v17Gram450_diag_re_le_one
    {T : ℝ}
    (hPois : Zeta23.ZeroSide.PoissonSq T (articleParams.atD T))
    (hnorm : 0 < (articleParams.atD T).a T * (articleParams.atD T).L T ^ 2)
    (s : ℕ)
    (hs : s + 450 ≤ articleRetainedCard T) :
    ∀ i : Fin 450, (v17Gram450 T s hs i i).re ≤ 1 := by
  intro i
  change
    (articleGlobalSimpleGram T
      (v17SimpleColumn450 T s hs i)
      (v17SimpleColumn450 T s hs i)).re ≤ 1
  have habs :=
    v17_articleGlobalSimpleGram_re_abs_le_one
      T hPois hnorm
      (v17SimpleColumn450 T s hs i)
      (v17SimpleColumn450 T s hs i)
  exact (le_abs_self _).trans habs

/-- Fully concrete finite-T v17 strong block.

The only logical trust frontiers are the already archived universal seven-point
certificate and the new scalar-pressure claim.  All Gram, PSD, diagonal,
compact-overlap, adjacent-band, global-energy, and spectral-threshold inputs
are built internally from the actual retained 450-point block. -/
theorem v17_concrete_strong_block_450
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
      gramSpectralDefect
          (v17Gram450 T s hs)
          (v17Gram450_posSemidef T s hs)
        + v17LiteralBlockPressure 450 (v17Y450 T s hs) := by
  let y : ℕ → ℝ := v17Y450 T s hs
  let w : ℕ → ℕ → ℝ := limitingWeightOnPoints y
  let G : Matrix (Fin 450) (Fin 450) ℂ := v17Gram450 T s hs
  let eps : ℝ := v17ArticleCompactError T M

  have hL : 0 ≤ articleParams.L T := by
    rw [articleParams_L_eq_zeta_l]
    exact le_of_lt hl

  have hyMono : ∀ q < 449, y q ≤ y (q + 1) := by
    dsimp [y]
    exact v17Y450_mono hL s hs

  have hw : ∀ a b, 0 ≤ w a b := by
    intro a b
    exact limitingWeightOnPoints_nonneg y a b

  have hcert : SevenPointCertificate w y 450 := by
    dsimp [w]
    exact
      sevenPointCertificate_of_articleSevenPointInequality
        hcertExt y hyMono

  have hscalar : ∀ q < 449,
      v17t * beta * v17g0 ≤
        w q (q + 1) + v17t * beta * (y (q + 1) - y q) := by
    dsimp [w]
    exact v17_scalar_pressure_450_of_claim hscalarExt y hyMono

  have heps : 0 ≤ eps := by
    dsimp [eps]
    exact v17ArticleCompactError_nonneg hl M

  have hG : G.PosSemidef := by
    dsimp [G]
    exact v17Gram450_posSemidef T s hs

  have hdiag : ∀ i, (G i i).re ≤ 1 := by
    dsimp [G]
    exact v17Gram450_diag_re_le_one hPois hnorm s hs

  have hpoint : ∀ a b, a < 450 → b < 450 →
      w a b - 2 * eps ≤ v17MatrixNormSqNat450 G a b := by
    intro a b ha hb
    have hp :=
      v17_Gram450_pointwise_squared_lower
        hPois hnorm hl hwL hsmall hM1 hM2 hkk s hs a b ha hb
    dsimp [w, y, eps, G]
    simpa [v17MatrixNormSqNat450, ha, hb] using hp

  have h :=
    v17_strong_block_450_of_matrix_interfaces
      y w G hG hdiag eps heps hw hcert hscalar hpoint

  dsimp [y, w, G, eps] at h ⊢
  simpa using h

end HurtadoZeta23