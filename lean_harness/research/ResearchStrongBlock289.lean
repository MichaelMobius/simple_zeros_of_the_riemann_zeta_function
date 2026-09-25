import HurtadoZeta23.ResearchGramThreshold289
import HurtadoZeta23.ResearchNinePointHybrid
import HurtadoZeta23.MatrixEnergy
import Mathlib.Tactic

noncomputable section

open Matrix Finset
open scoped BigOperators ComplexOrder

namespace HurtadoZeta23

/-!
# Research-only strong-block wrapper at `m = 289`

This layer is purely finite linear algebra plus the exact scalar contradiction
already proved in `ResearchNinePointHybrid`.  It deliberately leaves the two
analytic/certificate inputs explicit:

* `research9A ≤ offDiagonalEnergy G + P`;
* the weighted adjacent-pressure inequality.

The spectral-threshold implication is discharged internally from PSD and the
one-sided diagonal bound.
-/

/-- Matrix-facing ideal strong-block theorem for the research `m = 289`
configuration. -/
theorem research9_strong_block_289_of_matrix_interfaces
    (G : Matrix (Fin 289) (Fin 289) ℂ)
    (hG : G.PosSemidef)
    (hdiag : ∀ i : Fin 289, (G i i).re ≤ 1)
    {P : ℝ}
    (hEP : research9A ≤ offDiagonalEnergy G + P)
    (hweighted :
      research9t * research9g0 * research9Q ≤
        gramSpectralDefect G hG + research9t * P) :
    research9A ≤ gramSpectralDefect G hG + P := by
  apply research9_strong_block_scalar
    (D := gramSpectralDefect G hG)
    (E := offDiagonalEnergy G)
    (P := P)
  · exact hEP
  · exact hweighted
  · intro hDO
    exact research9_psd_gram_threshold_289_of_diag G hG hdiag hDO

end HurtadoZeta23
