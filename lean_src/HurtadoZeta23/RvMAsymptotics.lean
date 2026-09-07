import HurtadoZeta23.ZetaRvMBridge
import Zeta23.ThmD.Mult
import Mathlib.Tactic

noncomputable section

open Filter Asymptotics

namespace HurtadoZeta23

/-- The standard `sqrt T * log T` scale used by Zeta23's local zero-count bounds
is negligible with respect to the dyadic zero count. -/

theorem sqrtTlogT_isLittleO_zetaDyadicN :
    (fun T : ℝ => Real.sqrt T * Zeta23.l T) =o[atTop] zetaDyadicN := by
  change
    (fun T : ℝ => Real.sqrt T * Zeta23.l T)
      =o[atTop]
    (fun T : ℝ => (Zeta23.Ncount T (2 * T) : ℝ))
  exact
    Zeta23.Assembly.isLittleO_N_of_isLittleO_Tl
      Zeta23.zetaZeroConfig
      Zeta23.paperInputs_zeta.RvM
      Zeta23.Assembly.isLittleO_sqrt_mul_l_Tl

theorem isLittleO_zetaDyadicN_of_isBigO_sqrtTlogT
    {f : ℝ → ℝ}
    (hf : f =O[atTop] (fun T : ℝ => Real.sqrt T * Zeta23.l T)) :
    f =o[atTop] zetaDyadicN :=
  hf.trans_isLittleO sqrtTlogT_isLittleO_zetaDyadicN

theorem isLittleO_zetaDyadicN_of_isLittleO_TlogT
    {f : ℝ → ℝ}
    (hf : f =o[atTop] (fun T : ℝ => T * Zeta23.l T)) :
    f =o[atTop] zetaDyadicN := by
  change
    f =o[atTop]
      (fun T : ℝ => (Zeta23.Ncount T (2 * T) : ℝ))
  exact
    Zeta23.Assembly.isLittleO_N_of_isLittleO_Tl
      Zeta23.zetaZeroConfig
      Zeta23.paperInputs_zeta.RvM
      hf

theorem zetaNII_isLittleO_zetaDyadicN :
    (fun T : ℝ =>
      (Zeta23.Assembly.NII Zeta23.zetaZeroConfig T : ℝ))
      =o[atTop] zetaDyadicN := by
  obtain ⟨A0, hA0, hloc⟩ :=
    Zeta23.paperInputs_zeta.RvM.local_count

  obtain ⟨CII, hII⟩ :=
    Zeta23.Tail.eventually_NII_le
      Zeta23.zetaZeroConfig hA0 hloc

  have hO :
      (fun T : ℝ =>
        (Zeta23.Assembly.NII Zeta23.zetaZeroConfig T : ℝ))
        =O[atTop]
          (fun T : ℝ => Real.sqrt T * Zeta23.l T) := by
    refine IsBigO.of_bound CII ?_
    filter_upwards
      [hII, Zeta23.Assembly.eventually_l_pos]
      with T h hl
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Nat.cast_nonneg _),
      abs_of_nonneg (by positivity)]
    simpa [mul_assoc] using h

  exact
    isLittleO_zetaDyadicN_of_isBigO_sqrtTlogT hO

def zetaBoundaryLoss (T : ℝ) : ℝ :=
  (Zeta23.Assembly.NII Zeta23.zetaZeroConfig T : ℝ)

theorem zetaBoundaryLoss_small :
    zetaBoundaryLoss =o[atTop] zetaDyadicN := by
  change
    (fun T : ℝ =>
      (Zeta23.Assembly.NII Zeta23.zetaZeroConfig T : ℝ))
      =o[atTop] zetaDyadicN
  exact zetaNII_isLittleO_zetaDyadicN

end HurtadoZeta23
