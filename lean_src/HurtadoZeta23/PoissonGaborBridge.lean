import HurtadoZeta23.KernelBridge
import Zeta23.ThmD.BridgeD
import Mathlib.Tactic

noncomputable section

namespace HurtadoZeta23

open Real Set MeasureTheory Filter Topology
open scoped BigOperators

/--
The exact infinite critical-lattice Poisson identity used by Appendix IV of the
position-weighted paper, specialized to Anthropic/Zeta23's Montgomery--Taylor
window `phiD`.

This is not a new analytic assumption: it is a direct wrapper around
`Zeta23.AdmWindow.hasSum_vHatR_mul` plus `Zeta23.ThmD.admWindow_phiD`.
-/
theorem hasSum_phiD_full_grid
    {ϱ : ℝ → ℝ} {lam L w : ℝ}
    (hϱ : Zeta23.TaperProfile ϱ)
    (h0 : 0 < lam) (h1 : lam ≤ 1)
    (hw : 1 ≤ w) (hwL : 8 * w ≤ L)
    (T τ τ' : ℝ) :
    HasSum
      (fun k : ℤ =>
        Zeta23.AdmWindow.vHatR (Zeta23.ThmD.phiD ϱ lam L w)
            (τ - (T + k * (2 * Real.pi / L))) *
        Zeta23.AdmWindow.vHatR (Zeta23.ThmD.phiD ϱ lam L w)
            (τ' - (T + k * (2 * Real.pi / L))))
      (L * Zeta23.AdmWindow.VPhiR
        (Zeta23.ThmD.phiD ϱ lam L w) (τ - τ')) := by
  exact
    (Zeta23.ThmD.admWindow_phiD hϱ h0 h1 hw hwL).hasSum_vHatR_mul
      T τ τ'

/--
Raw real overlap control implies control of squared overlaps. The factor `2`
is the sharp elementary estimate on the unit interval:

`|a²-b²| = |a-b||a+b| ≤ 2 eps`

when `|a|,|b| ≤ 1`.
-/
lemma sq_lower_of_abs_sub_le
    {a b eps : ℝ}
    (heps : 0 ≤ eps)
    (ha : |a| ≤ 1)
    (hb : |b| ≤ 1)
    (hab : |a - b| ≤ eps) :
    b ^ 2 - 2 * eps ≤ a ^ 2 := by

  have habsum : |a + b| ≤ 2 := by
    calc
      |a + b|
          ≤ |a| + |b| := by
            simpa only [Real.norm_eq_abs] using
              norm_add_le a b
      _ ≤ 1 + 1 := add_le_add ha hb
      _ = 2 := by
            norm_num

  have hprod :
      |a ^ 2 - b ^ 2| ≤ 2 * eps := by

    rw [
      show a ^ 2 - b ^ 2 = (a - b) * (a + b) by ring,
      abs_mul
    ]

    calc
      |a - b| * |a + b|
          ≤ eps * 2 := by
            exact mul_le_mul
              hab
              habsum
              (abs_nonneg _)
              heps

      _ = 2 * eps := by
            ring

  have hlower :
      b ^ 2 - a ^ 2 ≤ |a ^ 2 - b ^ 2| := by
    have h := neg_abs_le (a ^ 2 - b ^ 2)
    nlinarith

  nlinarith

/--
The analytic statement in the manuscript controls the raw overlap, not its
square. This structure mirrors that statement on a 262-point retained block.
-/
def RawPointwiseOverlapApproximation262
    (y : ℕ → ℝ)
    (overlap : ℕ → ℕ → ℝ)
    (eps : ℝ) : Prop :=
  0 ≤ eps ∧
  (∀ a b, |overlap a b| ≤ 1) ∧
  (∀ a b, |limitingk (y b - y a)| ≤ 1) ∧
  (∀ a b,
    |overlap a b - limitingk (y b - y a)| ≤ eps)

/--
A raw overlap approximation gives precisely the squared-overlap approximation
consumed by `KernelBridge`, with per-pair error `2 * eps`.
-/
theorem pointwiseKernelApproximation262_of_raw
    (y : ℕ → ℝ)
    (overlap : ℕ → ℕ → ℝ)
    (eps : ℝ)
    (h : RawPointwiseOverlapApproximation262 y overlap eps) :
    PointwiseKernelApproximation262
      y
      (fun a b => (overlap a b) ^ 2)
      (2 * eps) := by

  rcases h with ⟨heps, hover, hk, happ⟩

  constructor

  · positivity

  · intro a b
    change
      limitingk (y b - y a) ^ 2 - 2 * eps
        ≤ overlap a b ^ 2

    exact
      sq_lower_of_abs_sub_le
        heps
        (hover a b)
        (hk a b)
        (happ a b)

/--
Consequently a raw overlap error `eps` costs at most `136764 * eps` in the
262-point global pair energy:

`68382 * (2 * eps) = 136764 * eps`.
-/
theorem aggregate_kernel_lower_262_of_raw
    (y : ℕ → ℝ)
    (overlap : ℕ → ℕ → ℝ)
    (eps : ℝ)
    (h : RawPointwiseOverlapApproximation262 y overlap eps) :
    globalPairEnergyNat blockLength (limitingWeightOnPoints y)
        - 136764 * eps
      ≤
    globalPairEnergyNat blockLength
      (fun a b => overlap a b ^ 2) := by

  have hp :=
    pointwiseKernelApproximation262_of_raw
      y
      overlap
      eps
      h

  have hs :=
    kernel_bridge_262_of_pointwise
      y
      (fun a b => overlap a b ^ 2)
      (2 * eps)
      hp

  have hcoeff :
      (68382 : ℝ) * (2 * eps)
        =
      136764 * eps := by
    ring

  rw [hcoeff] at hs

  exact hs

/--
A form matching the actual compact overlap limit of the paper: once the real
Gram entries are uniformly within `eps` of `k`, unit boundedness converts that
statement directly into uniform block stability.
-/
theorem block_stability_262_of_raw_overlap
    (y : ℕ → ℝ)
    (overlap : ℕ → ℕ → ℝ)
    (hcert :
      SevenPointCertificate
        (limitingWeightOnPoints y)
        y
        blockLength)
    (hmono :
      ∀ q < blockLength - 1,
        y q ≤ y (q + 1))
    (hspan0 :
      0 ≤ y (blockLength - 1) - y 0)
    {D gramOffDiag eps : ℝ}
    (hD0 : 0 ≤ D)
    (hblock :
      min 1 gramOffDiag ≤ D)
    (hraw :
      RawPointwiseOverlapApproximation262
        y
        overlap
        eps)
    (hGram :
      globalPairEnergyNat blockLength
        (fun a b => overlap a b ^ 2)
        =
      gramOffDiag) :
    A0 - 136764 * eps
      ≤
    D + beta * (y (blockLength - 1) - y 0) := by

  rcases hraw with ⟨heps, hover, hk, happ⟩

  have hpoint :
      ∀ a b,
        limitingWeightOnPoints y a b - 2 * eps
          ≤ overlap a b ^ 2 := by
    intro a b

    change
      limitingk (y b - y a) ^ 2 - 2 * eps
        ≤ overlap a b ^ 2

    exact
      sq_lower_of_abs_sub_le
        heps
        (hover a b)
        (hk a b)
        (happ a b)

  have hbase :=
    block_stability_262_of_pointwise_kernel
      y
      (fun a b => overlap a b ^ 2)
      hcert
      hmono
      hspan0
      hD0
      hblock
      (eta := 2 * eps)
      (by positivity)
      hpoint
      hGram

  have hcoeff :
      (68382 : ℝ) * (2 * eps)
        =
      136764 * eps := by
    ring

  rw [hcoeff] at hbase

  exact hbase

end HurtadoZeta23