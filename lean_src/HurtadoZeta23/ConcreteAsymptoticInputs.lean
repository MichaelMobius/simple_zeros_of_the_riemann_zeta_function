import HurtadoZeta23.GlobalAssembly
import HurtadoZeta23.RvMAsymptotics
import Mathlib.Tactic

noncomputable section

open Filter Asymptotics

namespace HurtadoZeta23

/--
A more concrete final-input package.

The boundary loss is explicit because the compact-overlap argument removes
*interior* `L^2`-cell strips; it must not be identified with Zeta23's exterior
`NII`.

The constructor in `RetainedCoreBridge` supplies the correct loss and its
`o(N)` proof.

For the span error we ask only for the natural stronger statement
`o(T log T)`; Zeta23 transports it automatically to `o(N)`.
-/
structure RvMShiftedPinchingInputs where
  retained : ℝ → ℝ
  defect : ℝ → ℝ
  span : ℝ → ℝ

  retainedLoss : ℝ → ℝ
  spanErr : ℝ → ℝ
  blockErr : ℝ → ℝ

  retainedLoss_small :
    retainedLoss =o[atTop] globalN

  spanErr_small_TlogT :
    spanErr =o[atTop] (fun T : ℝ => T * Zeta23.l T)

  blockErr_small :
    blockErr =o[atTop] globalN

  retained_bound :
    ∀ᶠ T in atTop,
      globalS T - retainedLoss T ≤ retained T

  span_bound :
    ∀ᶠ T in atTop,
      span T ≤ globalN T + spanErr T

  pinching_bound :
    ∀ᶠ T in atTop,
      alpha * retained T
        - pressureCost * span T
        - endpointCorrection
        - blockErr T
        ≤ defect T

/--
Convert the RvM-aware package to the generic assembly input.

The span error is transported by Zeta23; the boundary loss has already been
proved `o(N)` by the concrete interior-boundary bridge.
-/
def RvMShiftedPinchingInputs.toShiftedPinchingAsymptotics
    (h : RvMShiftedPinchingInputs) :
    ShiftedPinchingAsymptotics :=
  {
    retained := h.retained
    defect := h.defect
    span := h.span

    retainedLoss := h.retainedLoss
    spanErr := h.spanErr
    blockErr := h.blockErr

    retainedLoss_small := h.retainedLoss_small

    spanErr_small := by
      have hs :
          h.spanErr
            =o[atTop]
          zetaDyadicN :=
        isLittleO_zetaDyadicN_of_isLittleO_TlogT
          h.spanErr_small_TlogT

      change
        h.spanErr
          =o[atTop]
        globalN

      exact hs

    blockErr_small := h.blockErr_small

    retained_bound := h.retained_bound
    span_bound := h.span_bound
    pinching_bound := h.pinching_bound
  }

/--
Published epsilon-form directly from the more concrete RvM-aware pinching
package and the defect-enhanced baseline.
-/
theorem published_eps_form_of_rvm_pinching_and_baseline
    (p : RvMShiftedPinchingInputs)
    (b : BaselineWithDefect p.defect) :
    ∀ ε > 0,
      ∃ T₀ : ℝ,
        ∀ T ≥ T₀,
          (publishedConstant - ε)
              * (Zeta23.Ncount T (2 * T) : ℝ)
            ≤
          Zeta23.N0simple T (2 * T) := by

  exact
    published_eps_form_of_pinching_and_baseline
      p.toShiftedPinchingAsymptotics
      b

end HurtadoZeta23