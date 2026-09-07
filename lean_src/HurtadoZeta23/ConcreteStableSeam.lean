import HurtadoZeta23.ConcreteStableCore
import Zeta23.ThmD.Mult
import Mathlib.Tactic

noncomputable section

open Filter Asymptotics Topology Real RHLinalg

namespace HurtadoZeta23

open Zeta23
open Zeta23.Assembly
open Zeta23.ThmD

/--
The theorem-D parameter family at the Montgomery--Taylor endpoint `λ = 1`.

Unlike Anthropic's public fixed-λ epsilon wrapper, the lower-level analytic
ingredients used below are valid under `λ ≤ 1`; this lets the defect-preserving
seam use the same endpoint window as the seven-point Gram certificate.
-/
def articleParams : Zeta23.Params :=
  Zeta23.paramsOf Zeta23.stdProfile 1

lemma articleParams_valid :
    articleParams.Valid := by
  unfold articleParams
  exact
    Zeta23.paramsOf_valid
      Zeta23.taperProfile_stdProfile
      one_pos
      le_rfl

/-- Canonical conjugation witness used in the endpoint simple-zero Gram. -/
theorem articlePhiHatConj (T : ℝ) :
    Zeta23.ZeroSide.PhiHatConj T (articleParams.atD T) :=
  fun z =>
    Zeta23.GzGp.phiHat_conj
      (articleParams.atD T) T z

/-- Canonical real-axis witness used in the endpoint simple-zero Gram. -/
theorem articlePhiHatReal (T : ℝ) :
    Zeta23.ZeroSide.PhiHatReal T (articleParams.atD T) :=
  fun r =>
    Zeta23.GzGp.phiHat_ofReal
      (articleParams.atD T) T r

/--
The exact global simple-zero Gram defect used by both sides of the article:
the stability-enhanced Montgomery--Taylor baseline and, downstream, shifted
principal-block pinching.
-/
def articleStableDefect (T : ℝ) : ℝ :=
  gramSpectralDefect
    (zeroSideSimpleGram
      Zeta23.zetaZeroConfig
      (articleParams.atD T)
      T
      (articlePhiHatConj T))
    (zeroSideSimpleGram_posSemidef
      Zeta23.zetaZeroConfig
      (articleParams.atD T)
      T
      (articlePhiHatConj T))

/--
Concrete defect-preserving Montgomery--Taylor seam at `λ = 1`.

This is the article-aligned analogue of the c=2 portion of
`Zeta23.ThmD.thmD_mult2_abstract`, but it keeps the simple-zero Gram spectral
defect visible and does not freeze the finite-T coefficient prematurely.
-/
theorem articleStableSeamAsymptotics_exists :
    ∃ s : StableSeamAsymptotics,
      s.defect = articleStableDefect := by

  let Z := Zeta23.zetaZeroConfig
  let H := Zeta23.paperInputs_zeta
  let P := articleParams
  let hP : P.Valid := articleParams_valid

  have hLoc : Zeta23.ThmD.LocalHypsCoreDEventually P :=
    Zeta23.ThmD.localHypsCoreD_eventually hP

  have hTr :=
    Zeta23.ThmD.tracesBoundsD_concrete
      (Z := Z) hP H hLoc

  have hc :=
    Zeta23.ThmD.tendsto_cRatio_concrete hP Z

  have hc0 :
      0 < Zeta23.ThmD.cStar P.lam :=
    Zeta23.ThmD.cStar_pos
      hP.lam_pos hP.lam_le_one

  have ha :
      ∀ᶠ T in atTop,
        1 / 2 ≤ (Zeta23.ThmD.concreteDataD P Z).aT T ∧
        (Zeta23.ThmD.concreteDataD P Z).aT T ≤ 1 :=
    (Zeta23.ThmD.concreteFactsD hP H hLoc).ab_range.mono
      (fun T h => ⟨h.1.trans h.2.1, h.2.2.1⟩)

  have hBlock :=
    Zeta23.ThmD.eventually_blockInputsD Z hP

  obtain ⟨θ₀, hTail, hθ₀⟩ :=
    Zeta23.ThmD.eventually_tailPackageD Z H hP

  obtain ⟨A₀, hA₀, hloc⟩ :=
    H.RvM.local_count

  have hNII :=
    Zeta23.Tail.eventually_NII_le Z hA₀ hloc

  have hGzGp :=
    Zeta23.ThmD.eventually_GzGpD Z H hP

  have hId :
      ∀ᶠ T in atTop,
        (P.atD T).trGtilde T =
            (Zeta23.ThmD.concreteDataD P Z).trG T ∧
        (P.atD T).trGtildeSq T =
            (Zeta23.ThmD.concreteDataD P Z).trG2 T ∧
        (P.atD T).a T =
            (Zeta23.ThmD.concreteDataD P Z).aT T :=
    Eventually.of_forall fun T =>
      ⟨Zeta23.Params.atD_trGtilde T hP,
       Zeta23.Params.atD_trGtildeSq T hP,
       Zeta23.Params.atD_a T hP⟩

  have hcalE :=
    Zeta23.Assembly.calE_tendsto_zero
      P hP.lam_pos hP.lam_le_one
      (zero_le_one.trans hP.one_le_w)

  let aT : ℝ → ℝ :=
    (Zeta23.ThmD.concreteDataD P Z).aT

  let bT : ℝ → ℝ :=
    (Zeta23.ThmD.concreteDataD P Z).bT

  let JT : ℝ → ℝ :=
    (Zeta23.ThmD.concreteDataD P Z).JT

  let trG : ℝ → ℝ :=
    (Zeta23.ThmD.concreteDataD P Z).trG

  let trG2 : ℝ → ℝ :=
    (Zeta23.ThmD.concreteDataD P Z).trG2

  let N : ℝ → ℝ :=
    fun T => (Z.N T (2 * T) : ℝ)

  obtain ⟨C₁, hC₁, T₁, htr1⟩ := hTr.tr1
  obtain ⟨C₂, hC₂, T₂, hfr2⟩ := hTr.frhat
  obtain ⟨Cθ, hθ⟩ := hθ₀
  obtain ⟨CII, hII⟩ := hNII

  let cinv : ℝ → ℝ :=
    fun T =>
      (Zeta23.ThmD.cRatio
        (P.lam1 T) (aT T) (bT T) (JT T))⁻¹

  let R₁ : ℝ → ℝ :=
    fun T => C₁ * Real.sqrt (P.X T) / aT T

  let R₂ : ℝ → ℝ :=
    fun T => C₂ * P.calE T * (cinv T * N T)

  let B : ℝ → ℝ :=
    fun T => θ₀ T / (aT T * P.L T)

  let err : ℝ → ℝ :=
    fun T =>
      4 * R₁ T + R₂ T
        + 3 * (Zeta23.Assembly.NII Z T : ℝ)
        + B T *
          (4 + 2 * Real.sqrt (cinv T * N T + R₂ T) + B T)

  have hcinv_to :
      Tendsto cinv atTop
        (𝓝 (Zeta23.ThmD.cStar P.lam)⁻¹) := by
    exact hc.inv₀ hc0.ne'

  have hmain :
      ∀ᶠ T in atTop,
        (2 - cinv T) * N T
          + articleStableDefect T
          - err T
        ≤ (Z.N0s T (2 * T) : ℝ) := by

    filter_upwards
      [hBlock, hTail, hGzGp, hId, ha,
       eventually_ge_atTop T₁,
       eventually_ge_atTop T₂,
       eventually_ge_atTop (0 : ℝ),
       Zeta23.Assembly.eventually_l_pos,
       Zeta23.Assembly.eventually_calE_nonneg
          P hP.lam_pos
          (zero_le_one.trans hP.one_le_w),
       Zeta23.ThmD.eventually_w8 hP]
      with T hBl hTl hGG hid ha2 hT₁ hT₂ hT0 hl hE0 h8

    obtain ⟨hidtr, hidfr, hida⟩ := hid

    have hapos' : 0 < aT T := by
      dsimp [aT]
      linarith [ha2.1]

    have haposD :
        0 < (P.atD T).a T := by
      rw [hida]
      exact hapos'

    have hLpos :
        0 < P.L T := by
      simpa [Zeta23.Params.L] using
        mul_pos hP.lam_pos hl

    have hLposD :
        0 < (P.atD T).L T := by
      simpa using hLpos

    have hnorm :
        0 < (P.atD T).a T * (P.atD T).L T ^ 2 := by
      exact mul_pos haposD (pow_pos hLposD 2)

    have hPois :
        Zeta23.ZeroSide.PoissonSq T (P.atD T) :=
      Zeta23.ThmD.poissonSqD hP h8

    have hstable :
        StableCoreAt Z (P.atD T) T
          (articleStableDefect T) := by
      have hs :=
        stableCoreAt_of_zeroSideSimpleGram
          Z (P.atD T) T
          (articlePhiHatConj T)
          (articlePhiHatReal T)
          hPois hnorm
      simpa [Z, P, articleStableDefect, articleParams] using hs

    have hrt :
        rtrace ((P.atD T).hat T (Z.Gz (P.atD T) T))
          = (aT T * P.L T)⁻¹ * trG T := by
      rw [Zeta23.Assembly.rtrace_hat, hGG,
        Zeta23.Assembly.rtrace_tilde_Gp, hidtr, hida]
      rfl

    have hfr :
        frobSq ((P.atD T).hat T (Z.Gz (P.atD T) T))
          = ((aT T * P.L T)⁻¹) ^ 2 * trG2 T := by
      rw [Zeta23.Assembly.frobSq_hat, hGG,
        Zeta23.Assembly.frobSq_tilde_Gp, hidfr, hida]
      rfl

    have htr :
        |(aT T * P.L T)⁻¹ * trG T - N T|
          ≤ R₁ T := by
      exact
        Zeta23.Assembly.trGhat_sub_N_le
          hapos' hLpos
          (by
            dsimp [aT, trG, N]
            simpa [Zeta23.ThmD.concreteDataD] using
              htr1 T hT₁)

    have hfrb :
        ((aT T * P.L T)⁻¹) ^ 2 * trG2 T
          ≤ cinv T * N T + R₂ T := by

      have h := hfr2 T hT₂
      simp only at h

      have h1 :
          trG2 T / (aT T * P.L T) ^ 2
              - cinv T * N T
            ≤ C₂ * P.calE T * (cinv T * N T) := by
        rw [← mul_assoc] at h
        exact
          le_trans
            (le_trans (le_max_left _ 0) (le_abs_self _))
            h

      have heq :
          ((aT T * P.L T)⁻¹) ^ 2 * trG2 T
            =
          trG2 T / (aT T * P.L T) ^ 2 := by
        rw [inv_pow, div_eq_inv_mul]

      rw [heq]
      dsimp [R₂]
      linarith

    have htrM :
        |rtrace ((P.atD T).hat T (Z.Gz (P.atD T) T))
            - (Z.N T (2 * T) : ℝ)|
          ≤ R₁ T := by
      rw [hrt]
      simpa [N] using htr

    have hfrM :
        frobSq ((P.atD T).hat T (Z.Gz (P.atD T) T))
          ≤ cinv T * (Z.N T (2 * T) : ℝ) + R₂ T := by
      rw [hfr]
      simpa [N] using hfrb

    have hs :=
      stable_seamA_lower_c
        Z (P.atD T)
        (T := T)
        (θ₀ := θ₀ T)
        (defect := articleStableDefect T)
        (cinv := cinv T)
        (R₁ := R₁ T)
        (R₂ := R₂ T)
        hT0 hBl hTl haposD hLposD
        hstable htrM hfrM

    dsimp [err, B, R₁, R₂, N] at hs ⊢
    rw [hida] at hs
    simpa using hs

  have hNtop :
      Tendsto N atTop atTop :=
    Zeta23.Assembly.tendsto_N_atTop Z H.RvM

  have o1 : R₁ =o[atTop] N := by
    have hbd :
        (fun T => C₁ / aT T)
          =O[atTop] (fun _ => (1 : ℝ)) := by
      refine Zeta23.Assembly.isBigO_one_of_abs_le
        (C := 2 * C₁) ?_
      filter_upwards [ha] with T ha2
      rw [abs_of_nonneg
        (div_nonneg hC₁.le (by linarith [ha2.1]))]
      rw [div_le_iff₀ (by linarith [ha2.1])]
      nlinarith [ha2.1]

    have hsqrt :=
      Zeta23.Assembly.isLittleO_N_of_isLittleO_Tl
        Z H.RvM
        (Zeta23.Assembly.isLittleO_sqrtX_Tl
          P hP.lam_pos hP.lam_le_one)

    have ho :=
      Zeta23.Assembly.isLittleO_of_bdd_mul
        hbd hsqrt

    exact ho.congr_left
      (fun T => by
        dsimp [R₁]
        ring)

  have hcinv_bd :
      ∀ᶠ T in atTop,
        0 ≤ cinv T ∧
        cinv T ≤ 2 * (Zeta23.ThmD.cStar P.lam)⁻¹ := by

    have hcpos :
        (0 : ℝ) < (Zeta23.ThmD.cStar P.lam)⁻¹ :=
      inv_pos.mpr hc0

    filter_upwards
      [hcinv_to.eventually (eventually_ge_nhds hcpos),
       hcinv_to.eventually
         (eventually_le_nhds
           (show
             (Zeta23.ThmD.cStar P.lam)⁻¹
               < 2 * (Zeta23.ThmD.cStar P.lam)⁻¹
            by linarith))]
      with T h1 h2

    exact ⟨h1, h2⟩

  have hcinvO :
      cinv =O[atTop] (fun _ => (1 : ℝ)) := by
    refine
      Zeta23.Assembly.isBigO_one_of_abs_le
        (C := 2 * (Zeta23.ThmD.cStar P.lam)⁻¹) ?_
    filter_upwards [hcinv_bd] with T h
    rw [abs_of_nonneg h.1]
    exact h.2

  have o2 : R₂ =o[atTop] N := by

    have hcE0 :
        Tendsto
          (fun T => C₂ * P.calE T)
          atTop (𝓝 0) := by
      simpa using hcalE.const_mul C₂

    have i1 :
        (fun T => cinv T * N T)
          =O[atTop] N := by
      have hh :=
        hcinvO.mul (isBigO_refl N atTop)
      simpa using hh

    have hh :=
      ((isLittleO_one_iff ℝ).2 hcE0).mul_isBigO i1

    refine
      (hh.congr_left
        (fun T => by
          dsimp [R₂])).congr_right
        (fun T => by simp)

  have o3 :
      (fun T => (Zeta23.Assembly.NII Z T : ℝ))
        =o[atTop] N := by

    have hO :
        (fun T => (Zeta23.Assembly.NII Z T : ℝ))
          =O[atTop]
        (fun T => Real.sqrt T * Zeta23.l T) := by

      refine IsBigO.of_bound CII ?_

      filter_upwards
        [hII, Zeta23.Assembly.eventually_l_pos]
        with T h hl

      rw [Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (Nat.cast_nonneg _),
        abs_of_nonneg (by positivity)]

      simpa [mul_assoc] using h

    exact
      hO.trans_isLittleO
        (Zeta23.Assembly.isLittleO_N_of_isLittleO_Tl
          Z H.RvM
          Zeta23.Assembly.isLittleO_sqrt_mul_l_Tl)

  have o4 :
      Tendsto B atTop (𝓝 0) := by

    have hup :
        Tendsto
          (fun T =>
            2 * |Cθ| *
              (Zeta23.l T * T ^ (P.lam / 2 - 1) / P.L T))
          atTop
          (𝓝 0) := by

      simpa using
        (Zeta23.Assembly.tendsto_theta_over_L
          P hP.lam_pos hP.lam_le_one).const_mul
            (2 * |Cθ|)

    refine
      tendsto_of_tendsto_of_tendsto_of_le_of_le'
        tendsto_const_nhds hup ?_ ?_

    ·
      filter_upwards
        [hTail, ha, Zeta23.Assembly.eventually_l_pos]
        with T hTl ha2 hl

      have hLpos : 0 < P.L T := by
        simpa [Zeta23.Params.L] using
          mul_pos hP.lam_pos hl

      dsimp [B]
      exact
        div_nonneg hTl.theta_nonneg
          (by nlinarith [ha2.1])

    ·
      filter_upwards
        [hTail, ha, Zeta23.Assembly.eventually_l_pos,
         hθ, eventually_gt_atTop (0 : ℝ)]
        with T hTl ha2 hl hθT hT0

      have hLpos : 0 < P.L T := by
        simpa [Zeta23.Params.L] using
          mul_pos hP.lam_pos hl

      have hapos' : 0 < aT T := by
        linarith [ha2.1]

      have hq :
          0 ≤
            Zeta23.l T * T ^ (P.lam / 2 - 1) / P.L T := by
        positivity

      dsimp [B]

      rw [div_le_iff₀ (mul_pos hapos' hLpos)]

      calc
        θ₀ T
            ≤ Cθ * Zeta23.l T *
                T ^ (P.lam / 2 - 1) := hθT
        _ ≤ |Cθ| * Zeta23.l T *
                T ^ (P.lam / 2 - 1) := by
              gcongr
              exact le_abs_self _
        _ =
            |Cθ| *
              (Zeta23.l T * T ^ (P.lam / 2 - 1) / P.L T) *
              P.L T := by
              field_simp
        _ ≤
            (2 * |Cθ| *
              (Zeta23.l T * T ^ (P.lam / 2 - 1) / P.L T)) *
              (aT T * P.L T) := by
              have he :
                  |Cθ| *
                      (Zeta23.l T *
                        T ^ (P.lam / 2 - 1) / P.L T) *
                      P.L T
                    =
                  (2 * |Cθ| *
                      (Zeta23.l T *
                        T ^ (P.lam / 2 - 1) / P.L T)) *
                      (1 / 2 * P.L T) := by
                ring
              rw [he]
              gcongr
              exact ha2.1

  have oerr :
      err =o[atTop] N := by

    have hh :=
      Zeta23.Assembly.err_isLittleO
        (R₁ := R₁)
        (R₂ := R₂)
        (NII := fun T =>
          (Zeta23.Assembly.NII Z T : ℝ))
        (B := B)
        (cl := cinv)
        hNtop o1 o2 o3 o4 hcinv_bd

    simpa [err] using hh

  have hP_lam :
      P.lam = 1 := by
    rfl

  have htarget :
      (Zeta23.ThmD.cStar P.lam)⁻¹
        = 2 - HMT := by
    rw [hP_lam]
    unfold HMT
    have hh :=
      Zeta23.ThmD.two_sub_inv_cStar (1 : ℝ)
    rw [← hh]
    ring

  refine
    ⟨{
      defect := articleStableDefect
      cinv := cinv
      err := err
      err_small := ?_
      cinv_tendsto := ?_
      bound := ?_
    }, rfl⟩

  ·
    change err =o[atTop]
      (fun T : ℝ => (Zeta23.Ncount T (2 * T) : ℝ))
    exact oerr

  ·
    simpa [htarget] using hcinv_to

  ·
    filter_upwards [hmain] with T hT
    change
      (2 - cinv T) *
          (Zeta23.Ncount T (2 * T) : ℝ)
        + articleStableDefect T
        - err T
      ≤ (Zeta23.N0simple T (2 * T) : ℝ)
    exact hT

/--
The concrete stable seam.  The analytic existence proof lives in `Prop`;
`Classical.choose` merely selects the witnessed structure, which is standard
noncomputable extraction from a proved existential.
-/
noncomputable def articleStableSeamAsymptotics :
    StableSeamAsymptotics :=
  Classical.choose articleStableSeamAsymptotics_exists

@[simp] theorem articleStableSeamAsymptotics_defect :
    articleStableSeamAsymptotics.defect = articleStableDefect :=
  Classical.choose_spec articleStableSeamAsymptotics_exists

/--
The stable baseline required by `GlobalAssembly` is now concrete: it is not an
external input anymore.
-/
noncomputable def articleBaselineWithDefect :
    BaselineWithDefect articleStableDefect := by
  rw [← articleStableSeamAsymptotics_defect]
  exact
    baselineWithDefect_of_stableSeam
      articleStableSeamAsymptotics

end HurtadoZeta23
