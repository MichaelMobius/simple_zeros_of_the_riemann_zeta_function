import HurtadoZeta23.ConcreteBlockDefect
import HurtadoZeta23.V17TraceLeSpectralThreshold
import Mathlib.Tactic

noncomputable section

open Matrix Finset
open scoped BigOperators ComplexOrder

namespace HurtadoZeta23

/-- A PSD `450 × 450` finite Gram matrix satisfies the exact v17 spectral
threshold as soon as its real trace is at most 450.

No exact unit diagonal is assumed. If the defect lies below the actual
off-diagonal energy, then it also lies below the full centered Frobenius
energy. The Frobenius/spectral identity and the trace-monotone scalar theorem
then force `D > 450/449`.
-/
theorem v17_matrix_spectral_threshold_fin450
    (G : Matrix (Fin 450) (Fin 450) ℂ)
    (hG : G.PosSemidef)
    (htrace : RHLinalg.rtrace G ≤ 450)
    (hsmall : gramSpectralDefect G hG < offDiagonalEnergy G) :
    v17Threshold < gramSpectralDefect G hG := by
  let lam : Fin 450 → ℝ := hG.isHermitian.eigenvalues

  have hlam0 : ∀ i, 0 ≤ lam i := by
    intro i
    dsimp [lam]
    exact hG.eigenvalues_nonneg i

  have hsum : (∑ i : Fin 450, lam i) ≤ 450 := by
    dsimp [lam]
    rw [← RHLinalg.rtrace_eq_sum_eigenvalues hG.isHermitian]
    exact htrace

  have hD :
      gramSpectralDefect G hG = ∑ i : Fin 450, psi (lam i) := by
    unfold gramSpectralDefect
    dsimp [lam]
    exact (RHLinalg.sum_eigenvalues_reindex hG.isHermitian psi).symm

  have hFS := frobeniusSpectralIdentity_proved G hG.isHermitian
  unfold FrobeniusSpectralIdentity at hFS

  have hoffSpec : offDiagonalEnergy G ≤ spectralDeviationSq hG.isHermitian := by
    calc
      offDiagonalEnergy G ≤ frobeniusDeviationSq G :=
        offDiagonalEnergy_le_frobeniusDeviationSq G
      _ = spectralDeviationSq hG.isHermitian := hFS

  have hDE :
      gramSpectralDefect G hG < spectralDeviationSq hG.isHermitian :=
    lt_of_lt_of_le hsmall hoffSpec

  have hE :
      spectralDeviationSq hG.isHermitian =
        ∑ i : Fin 450, (lam i - 1) ^ 2 := by
    rfl

  exact v17_spectral_threshold_fin450_sum_le
    lam hlam0 hsum hD hE hDE

end HurtadoZeta23
