import HurtadoZeta23.StableSeam
import Zeta23.Assembly
import Zeta23.ThmD.AssemblyD
import Mathlib.Tactic

noncomputable section

open Matrix Finset RHLinalg
open Real

namespace HurtadoZeta23

/--
The fixed-`T` stability core aligned with the article.

The right-hand side is `s₁`, the number of simple critical-line zeros in the
enlarged interval.  The defect is the Gram defect of the simple-zero synthesis
matrix.
-/
def StableCoreAt (Z : Zeta23.ZeroConfig) (P : Zeta23.Params)
    (T defect : ℝ) : Prop :=
  4 * rtrace (P.hat T (Z.Az P T))
      - 2 * (Z.NIprime T : ℝ)
      - frobSq (P.hat T (Z.Az P T))
      + defect
    ≤ (Z.s1 T : ℝ)

/--
**Defect-preserving Seam A for simple zeros.**

This is the same tail perturbation and interval bookkeeping as Anthropic's
`Assembly.seamA`, but starts from the article-aligned stable core with right
side `s₁` and therefore finishes with `N₀ˢ(T,2T)` using
`Zeta23.Assembly.s1_le`.
-/
theorem stable_seamA
    (Z : Zeta23.ZeroConfig) (P : Zeta23.Params) {T θ₀ defect : ℝ}
    (hT : 0 ≤ T)
    (hB : Zeta23.Assembly.BlockInputs Z P T)
    (hTl : Zeta23.Assembly.TailInputs Z P T θ₀)
    (ha : 0 < P.a T) (hL : 0 < P.L T)
    (hstable : StableCoreAt Z P T defect) :
    4 * rtrace (P.hat T (Z.Gz P T))
      - frobSq (P.hat T (Z.Gz P T))
      - 2 * (Z.N T (2 * T) : ℝ)
      - 3 * (Zeta23.Assembly.NII Z T : ℝ)
      - θ₀ / (P.a T * P.L T) *
          (4 + 2 * Real.sqrt (frobSq (P.hat T (Z.Gz P T)))
             + θ₀ / (P.a T * P.L T))
      + defect
    ≤ (Z.N0s T (2 * T) : ℝ) := by
  obtain ⟨B, hB0, htrE, hfrE, hBle⟩ := hTl.hat
  have hGAE :
      P.hat T (Z.Gz P T) = P.hat T (Z.Az P T) + P.hat T (Z.Ez P T) := by
    rw [← Zeta23.Assembly.hat_add]
    congr 1
    simp [Zeta23.ZeroConfig.Ez]
  have hB₀ : 0 ≤ θ₀ / (P.a T * P.L T) :=
    div_nonneg hTl.theta_nonneg (mul_pos ha hL).le
  have hpert := Zeta23.Assembly.four_tr_sub_frobSq_perturb hGAE hB₀
    (htrE.trans hBle) (hfrE.trans (pow_le_pow_left₀ hB0 hBle 2))
  have hcount :
      (Z.s1 T : ℝ)
        ≤ (Z.N0s T (2 * T) : ℝ) + (Zeta23.Assembly.NII Z T : ℝ) := by
    exact_mod_cast Zeta23.Assembly.s1_le Z hT
  have hNI :
      (Z.NIprime T : ℝ)
        = (Z.N T (2 * T) : ℝ) + (Zeta23.Assembly.NII Z T : ℝ) := by
    exact_mod_cast Zeta23.Assembly.NIprime_eq Z hT
  unfold StableCoreAt at hstable
  rw [hNI] at hstable
  linarith

/-- The fixed-`T` stable seam in the scalar form consumed by
`stable_N0s_lower_c`. -/
theorem stable_seamA_lower_c
    (Z : Zeta23.ZeroConfig) (P : Zeta23.Params) {T θ₀ defect cinv R₁ R₂ : ℝ}
    (hT : 0 ≤ T)
    (hB : Zeta23.Assembly.BlockInputs Z P T)
    (hTl : Zeta23.Assembly.TailInputs Z P T θ₀)
    (ha : 0 < P.a T) (hL : 0 < P.L T)
    (hstable : StableCoreAt Z P T defect)
    (htr : |rtrace (P.hat T (Z.Gz P T)) - (Z.N T (2*T) : ℝ)| ≤ R₁)
    (hfr : frobSq (P.hat T (Z.Gz P T)) ≤ cinv * (Z.N T (2*T) : ℝ) + R₂) :
    (2 - cinv) * (Z.N T (2*T) : ℝ) + defect
      - (4 * R₁ + R₂ + 3 * (Zeta23.Assembly.NII Z T : ℝ)
        + θ₀ / (P.a T * P.L T) *
          (4 + 2 * Real.sqrt (cinv * (Z.N T (2*T) : ℝ) + R₂)
             + θ₀ / (P.a T * P.L T)))
      ≤ (Z.N0s T (2*T) : ℝ) := by
  have hs := stable_seamA Z P hT hB hTl ha hL hstable
  exact stable_N0s_lower_c
    (div_nonneg hTl.theta_nonneg (mul_pos ha hL).le)
    hs htr hfr

end HurtadoZeta23
