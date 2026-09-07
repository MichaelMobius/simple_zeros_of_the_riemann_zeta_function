import HurtadoZeta23.WindowKernelLimit
import HurtadoZeta23.FiniteGridTruncation
import Mathlib.Tactic

noncomputable section

namespace HurtadoZeta23

open Real

/-- The Fourier-side numerator after dividing out the lattice scale `L`. -/
def scaledPhiDFourier
    (ϱ : ℝ → ℝ) (L w x : ℝ) : ℝ :=
  Zeta23.AdmWindow.VPhiR (Zeta23.ThmD.phiD ϱ 1 L w)
      (2 * Real.pi * x / L) / L

/--
This is the exact analytic estimate supplied by the `L¹` comparison
`integral_abs_phiDsq_sub_sharp`: after scaling `u = Lt`, the Fourier transform
of `phiD²` is within `2w/L` of the sharp limiting cosine transform.

It is isolated as a proposition so the remaining proof obligation is visibly
just the Fourier `L¹ → L∞` estimate, not any zeta-function input.
-/
def ScaledFourierWindowEstimate
    (ϱ : ℝ → ℝ) (L w : ℝ) : Prop :=
  ∀ x : ℝ,
    |scaledPhiDFourier ϱ L w x - limitingK x| ≤ 2 * w / L

/-- The limiting cosine transform has modulus at most its value at zero. -/
def LimitingKernelMajorization : Prop :=
  ∀ x : ℝ, |limitingK x| ≤ limitingK 0

/--
Quantitative normalization lemma.

Once the unnormalized Fourier transform is within `2w/L` of `K(x)` and
`a_D` is within `4w/L` of `K(0)`, the normalized kernel is within

`20 (w/L) / K(0)`,

provided the denominator perturbation is at most half of `K(0)`.
-/
theorem normalized_window_kernel_error
    {ϱ : ℝ → ℝ} {L w x : ℝ}
    (hϱ : Zeta23.TaperProfile ϱ)
    (hw : 1 ≤ w)
    (hwL : 8 * w ≤ L)
    (hnum :
      |scaledPhiDFourier ϱ L w x - limitingK x| ≤ 2 * w / L)
    (hK :
      |limitingK x| ≤ limitingK 0)
    (hsmall :
      4 * w / L ≤ limitingK 0 / 2) :
    |scaledPhiDFourier ϱ L w x / phiDMean ϱ 1 L w - limitingk x|
      ≤ 20 * (w / L) / limitingK 0 := by

  have hK0 : 0 < limitingK 0 :=
    limitingK_zero_pos

  have hw0 : 0 ≤ w := by
    linarith

  have hL : 0 < L := by
    nlinarith [hw, hwL]

  have hfour_nonneg :
      0 ≤ 4 * w / L := by
    positivity

  have hdpos :
      0 < limitingK 0 / 2 := by
    positivity

  have hden :
      |phiDMean ϱ 1 L w - limitingK 0|
        ≤ 4 * w / L :=
    phiDMean_close_limitingK_zero hϱ hw hwL

  /-
  From
      |a_D - K(0)| ≤ 4w/L
  we obtain
      a_D - K(0) ≥ -4w/L.
  Together with
      4w/L ≤ K(0)/2
  this gives
      a_D ≥ K(0)/2.
  -/
  have hdiffLower :
      -(4 * w / L)
        ≤ phiDMean ϱ 1 L w - limitingK 0 := by
    exact (abs_le.mp hden).1

  have hmeanRaw :
      limitingK 0 / 2
        ≤ phiDMean ϱ 1 L w := by
    linarith [hdiffLower, hsmall]

  have hmeanLower :
      limitingK 0 / 2
        ≤ |phiDMean ϱ 1 L w| := by
    exact hmeanRaw.trans (le_abs_self _)

  have hK0Lower :
      limitingK 0 / 2
        ≤ |limitingK 0| := by
    rw [abs_of_pos hK0]
    linarith

  have hdiv :=
    div_sub_div_bound
      (A := scaledPhiDFourier ϱ L w x)
      (A0 := limitingK x)
      (B := phiDMean ϱ 1 L w)
      (B0 := limitingK 0)
      (d := limitingK 0 / 2)
      (eA := 2 * w / L)
      (eB := 4 * w / L)
      hdpos
      hmeanLower
      hK0Lower
      hnum
      hden

  unfold limitingk

  calc
    |scaledPhiDFourier ϱ L w x / phiDMean ϱ 1 L w
        - limitingK x / limitingK 0|
        ≤
      (2 * w / L) / (limitingK 0 / 2)
        +
      |limitingK x| * (4 * w / L) /
        ((limitingK 0 / 2) * (limitingK 0 / 2)) := hdiv

    _ ≤
      (2 * w / L) / (limitingK 0 / 2)
        +
      limitingK 0 * (4 * w / L) /
        ((limitingK 0 / 2) * (limitingK 0 / 2)) := by

          have hnumTerm :
              |limitingK x| * (4 * w / L)
                ≤ limitingK 0 * (4 * w / L) := by
            exact
              mul_le_mul_of_nonneg_right
                hK
                hfour_nonneg

          have hdenTerm :
              0 ≤
                (limitingK 0 / 2) *
                  (limitingK 0 / 2) := by
            positivity

          have hterm :
              |limitingK x| * (4 * w / L) /
                  ((limitingK 0 / 2) * (limitingK 0 / 2))
                ≤
              limitingK 0 * (4 * w / L) /
                  ((limitingK 0 / 2) * (limitingK 0 / 2)) := by
            exact
              div_le_div_of_nonneg_right
                hnumTerm
                hdenTerm

          linarith

    _ = 20 * (w / L) / limitingK 0 := by
          field_simp [ne_of_gt hK0]
          ring

/--
Uniform version on every compact
(indeed, the bound is independent of `x`).
-/
theorem normalized_window_kernel_error_uniform
    {ϱ : ℝ → ℝ} {L w : ℝ}
    (hϱ : Zeta23.TaperProfile ϱ)
    (hw : 1 ≤ w)
    (hwL : 8 * w ≤ L)
    (hFourier : ScaledFourierWindowEstimate ϱ L w)
    (hK : LimitingKernelMajorization)
    (hsmall : 4 * w / L ≤ limitingK 0 / 2) :
    ∀ x : ℝ,
      |scaledPhiDFourier ϱ L w x / phiDMean ϱ 1 L w - limitingk x|
        ≤ 20 * (w / L) / limitingK 0 := by

  intro x

  exact
    normalized_window_kernel_error
      hϱ
      hw
      hwL
      (hFourier x)
      (hK x)
      hsmall

/--
Once a finite-grid tail is bounded by `tailErr`, the full raw overlap error is
explicit: tail error plus `20 (w/L)/K(0)`.
-/
theorem raw_overlap_error_of_tail_and_window
    {finite full : ℝ}
    {ϱ : ℝ → ℝ}
    {L w x tailErr : ℝ}
    (hϱ : Zeta23.TaperProfile ϱ)
    (hw : 1 ≤ w)
    (hwL : 8 * w ≤ L)
    (hFourier : ScaledFourierWindowEstimate ϱ L w)
    (hK : LimitingKernelMajorization)
    (hsmall : 4 * w / L ≤ limitingK 0 / 2)
    (hfull :
      full =
        scaledPhiDFourier ϱ L w x /
          phiDMean ϱ 1 L w)
    (htail :
      |finite - full| ≤ tailErr) :
    |finite - limitingk x|
      ≤ tailErr + 20 * (w / L) / limitingK 0 := by

  have hwnd :=
    normalized_window_kernel_error_uniform
      hϱ
      hw
      hwL
      hFourier
      hK
      hsmall
      x

  subst full

  exact
    overlap_error_triangle
      htail
      hwnd

end HurtadoZeta23