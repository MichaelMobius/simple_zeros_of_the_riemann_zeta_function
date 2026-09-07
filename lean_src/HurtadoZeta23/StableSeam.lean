import HurtadoZeta23.GlobalAssembly
import Zeta23.ThmD.Mult
import Mathlib.Tactic

noncomputable section

open Filter Asymptotics Topology Real

namespace HurtadoZeta23

/--
Fixed-T algebra for the stability-enhanced c=2 seam.

This is the exact analogue of `Zeta23.ThmD.N0star_lower_c`, with an additional
nonnegative Gram-defect term left visible. The hypothesis `h0` is precisely
what one gets after replacing Anthropic's ordinary rank--trace core by the
stability-enhanced rank--trace inequality and then performing the same tail
perturbation and I' -> I bookkeeping as `Assembly.seamA_mult2`.
-/
theorem stable_N0s_lower_c
    {N0s N NII trGh frGh B cinv R₁ R₂ defect : ℝ}
    (hB : 0 ≤ B)
    (h0 :
      4 * trGh - frGh - 2 * N - 3 * NII
        - B * (4 + 2 * Real.sqrt frGh + B)
        + defect
        ≤ N0s)
    (htr : |trGh - N| ≤ R₁)
    (hfr : frGh ≤ cinv * N + R₂) :
    (2 - cinv) * N + defect
        - (4 * R₁ + R₂ + 3 * NII
          + B * (4 + 2 * Real.sqrt (cinv * N + R₂) + B))
      ≤ N0s := by

  have htrLower :
      -R₁ ≤ trGh - N := by
    exact (abs_le.mp htr).1

  have h1 :
      N - R₁ ≤ trGh := by
    linarith

  have h2 :
      Real.sqrt frGh
        ≤ Real.sqrt (cinv * N + R₂) := by
    exact Real.sqrt_le_sqrt hfr

  have hBh2 :
      B * Real.sqrt frGh
        ≤ B * Real.sqrt (cinv * N + R₂) := by
    exact mul_le_mul_of_nonneg_left h2 hB

  nlinarith [h0, h1, h2, hBh2]

/--
The precise asymptotic output needed from a defect-preserving version of
Anthropic's c=2 endgame, before freezing the limiting Montgomery--Taylor
constant.

Compared with `BaselineWithDefect`, this structure is lower-level: the
coefficient is the actual finite-T `2-cinv(T)`, and the only asymptotic datum is
that `cinv(T)` tends to `2-HMT`.

This structure contains functions as data, so it lives in `Type`.
-/
structure StableSeamAsymptotics where

  defect : ℝ → ℝ

  cinv : ℝ → ℝ

  err : ℝ → ℝ

  err_small :
    err =o[atTop] globalN

  cinv_tendsto :
    Tendsto cinv atTop (𝓝 (2 - HMT))

  bound :
    ∀ᶠ T in atTop,
      (2 - cinv T) * globalN T
        + defect T
        - err T
        ≤ globalS T

/--
Drift caused by replacing the finite-T coefficient `2-cinv(T)` by HMT.
-/
def stableSeamDrift
    (h : StableSeamAsymptotics)
    (T : ℝ) : ℝ :=
  |h.cinv T - (2 - HMT)| * globalN T

/--
The coefficient drift is `o(N)` because `cinv(T) → 2-HMT`.
-/
lemma stableSeamDrift_small
    (h : StableSeamAsymptotics) :
    stableSeamDrift h =o[atTop] globalN := by

  have hz :
      Tendsto
        (fun T : ℝ =>
          |h.cinv T - (2 - HMT)|)
        atTop
        (𝓝 0) := by

    have hs :
        Tendsto
          (fun T : ℝ =>
            h.cinv T - (2 - HMT))
          atTop
          (𝓝 0) := by

      simpa using
        h.cinv_tendsto.sub_const
          (2 - HMT)

    simpa using hs.abs

  have hsmall :
      (fun T : ℝ =>
        |h.cinv T - (2 - HMT)|)
        =o[atTop]
      (fun _ : ℝ => (1 : ℝ)) := by

    exact
      (isLittleO_one_iff ℝ).2 hz

  have hN :
      globalN =O[atTop] globalN :=
    isBigO_refl globalN atTop

  have hprod :
      (fun T : ℝ =>
        |h.cinv T - (2 - HMT)| * globalN T)
        =o[atTop]
      (fun T : ℝ => (1 : ℝ) * globalN T) := by

    exact hsmall.mul_isBigO hN

  have hprod' :
      (fun T : ℝ =>
        |h.cinv T - (2 - HMT)| * globalN T)
        =o[atTop]
      globalN := by

    simpa only [one_mul] using hprod

  change
    (fun T : ℝ =>
      |h.cinv T - (2 - HMT)| * globalN T)
      =o[atTop]
    globalN

  exact hprod'

/--
A defect-preserving c=2 seam with the correct limiting coefficient gives
exactly the `BaselineWithDefect` used by the final assembly.
-/
def baselineWithDefect_of_stableSeam
    (h : StableSeamAsymptotics) :
    BaselineWithDefect h.defect := by

  refine
    {
      err :=
        fun T =>
          h.err T + stableSeamDrift h T

      err_small :=
        h.err_small.add
          (stableSeamDrift_small h)

      bound := ?_
    }

  filter_upwards [h.bound]
    with T hb

  have hN0 :
      0 ≤ globalN T := by
    unfold globalN
    positivity

  have habs :
      h.cinv T - (2 - HMT)
        ≤
      |h.cinv T - (2 - HMT)| := by
    exact le_abs_self _

  have hm :
      (h.cinv T - (2 - HMT)) * globalN T
        ≤
      |h.cinv T - (2 - HMT)| * globalN T := by

    exact
      mul_le_mul_of_nonneg_right
        habs
        hN0

  have hdrift :
      HMT * globalN T
        - stableSeamDrift h T
        ≤
      (2 - h.cinv T) * globalN T := by

    unfold stableSeamDrift

    linarith

  linarith

/--
Final published epsilon theorem from shifted pinching plus the lower-level
defect-preserving seam, eliminating `BaselineWithDefect` from the public API.
-/
theorem published_eps_form_of_pinching_and_stable_seam
    (p : ShiftedPinchingAsymptotics)
    (s : StableSeamAsymptotics)
    (hdef : s.defect = p.defect) :
    ∀ ε > 0,
      ∃ T₀ : ℝ,
        ∀ T ≥ T₀,
          (publishedConstant - ε)
              * (Zeta23.Ncount T (2 * T) : ℝ)
            ≤
          Zeta23.N0simple T (2 * T) := by

  have b :
      BaselineWithDefect p.defect := by

    rw [← hdef]

    exact
      baselineWithDefect_of_stableSeam s

  exact
    published_eps_form_of_pinching_and_baseline
      p
      b

end HurtadoZeta23