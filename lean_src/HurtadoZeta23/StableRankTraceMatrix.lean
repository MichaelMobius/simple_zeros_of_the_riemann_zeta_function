import HurtadoZeta23.StableRankTraceScalar
import Zeta23.LinAlg.RankTrace
import Mathlib.Tactic

noncomputable section

open Matrix Finset
open scoped ComplexOrder BigOperators
open RHLinalg

namespace HurtadoZeta23

variable {𝕜 : Type*} [RCLike 𝕜]
variable {n : Type*} [Fintype n] [DecidableEq n]

/--
Support of a nonnegative spectral sequence.

In the matrix application this is the set of nonzero eigenvalues of `P`.
-/
def spectralSupport
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℝ) : Finset ι :=
  Finset.univ.filter fun i => p i ≠ 0

/--
The stability defect attached to a spectral sequence with an ambient rank
budget `r`.

The padding term `(r - #support)` is exactly the contribution of zero
eigenvalues because `psi 0 = 1`.

When `p` is the nonzero spectrum of `P = V Vᴴ` and `M = Vᴴ V` is `r × r`,
this is the spectral quantity `tr Ψ(M)` from the paper.
-/
def spectralDefect
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℝ) (r : ℕ) : ℝ :=
  (∑ i ∈ spectralSupport p, psi (p i))
    + ((r - (spectralSupport p).card : ℕ) : ℝ)

lemma psi_zero :
    psi 0 = 1 := by
  simp [psi]

lemma stable_scalar_zero :
    2 * (0 : ℝ) - 1 + psi 0 = 0 := by
  rw [psi_zero]
  norm_num

/--
Rewrite the summed scalar stability contribution in the rank-budget form

`2 Σp - r + defect`.

Structural zero eigenvalues outside the support do not contribute because

`2·0 - 1 + ψ(0) = 0`;

missing eigenvalues inside the `r`-dimensional Gram side are represented by
the padding term in `spectralDefect`.
-/
theorem sum_stable_scalar_eq_rank_defect
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℝ) {r : ℕ}
    (hr : (spectralSupport p).card ≤ r) :
    (∑ i, (2 * p i - 1 + psi (p i)))
      =
    2 * (∑ i, p i) - r + spectralDefect p r := by

  classical

  let s : Finset ι := spectralSupport p

  have hs_mem (i : ι) :
      i ∈ s ↔ p i ≠ 0 := by
    simp [s, spectralSupport]

  have hsum_p :
      (∑ i, p i) =
        ∑ i ∈ s, p i := by
    symm
    apply Finset.sum_subset (Finset.subset_univ s)
    intro i hi hnot

    have hz : p i = 0 := by
      by_contra hne
      apply hnot
      exact (hs_mem i).2 hne

    exact hz

  have hsum_stable :
      (∑ i, (2 * p i - 1 + psi (p i)))
        =
      ∑ i ∈ s, (2 * p i - 1 + psi (p i)) := by

    symm
    apply Finset.sum_subset (Finset.subset_univ s)
    intro i hi hnot

    have hz : p i = 0 := by
      by_contra hne
      apply hnot
      exact (hs_mem i).2 hne

    rw [hz]
    exact stable_scalar_zero

  rw [hsum_p, hsum_stable]

  unfold spectralDefect

  change
    (∑ i ∈ s, (2 * p i - 1 + psi (p i)))
      =
    2 * (∑ i ∈ s, p i) - (r : ℝ)
      +
    ((∑ i ∈ s, psi (p i))
      + ((r - s.card : ℕ) : ℝ))

  have hcard : s.card ≤ r := by
    simpa [s] using hr

  have hcast :
      ((r - s.card : ℕ) : ℝ)
        =
      (r : ℝ) - (s.card : ℝ) := by
    rw [Nat.cast_sub hcard]

  rw [hcast]

  calc
    (∑ i ∈ s, (2 * p i - 1 + psi (p i)))
        =
      2 * (∑ i ∈ s, p i)
        - (s.card : ℝ)
        + (∑ i ∈ s, psi (p i)) := by

          simp_rw [
            Finset.sum_add_distrib,
            Finset.sum_sub_distrib
          ]

          simp only [
            Finset.sum_const,
            nsmul_eq_mul
          ]

          rw [← Finset.mul_sum]

          ring

    _ =
      2 * (∑ i ∈ s, p i) - (r : ℝ)
        +
      ((∑ i ∈ s, psi (p i))
        + ((r : ℝ) - (s.card : ℝ))) := by
          ring

/--
Matrix-level defect obtained from the sorted spectrum of a PSD matrix `P`
and a rank budget `r`.

This is intentionally defined in the same `Fin d` coordinates used by
Anthropic's proof of `rank_trace_ineq`.
-/
def matrixSpectralDefect
    (P : Matrix n n 𝕜)
    (hP : P.PosSemidef)
    (r : ℕ) : ℝ :=
  let d := Fintype.card n
  let p : Fin d → ℝ :=
    hP.isHermitian.eigenvalues₀
  spectralDefect p r

/--
Stability-enhanced rank--trace inequality before using `tr P ≤ r`.

This is a minimal modification of `RHLinalg.rank_trace_ineq` at `c = 2`.

Anthropic already supplies:

* Hermitian positive/negative parts `Q₊,Q₋`;
* PSD and orthogonality of those parts;
* von Neumann's trace inequality;
* trace/Frobenius spectral identities;
* the positive-part rank bound.

The changed step is the scalar estimate for the `P - Q₋` block, where
`stable_scalar_sum` retains `matrixSpectralDefect` instead of discarding it.
-/
theorem stable_rank_trace_pre
    {P Q : Matrix n n 𝕜}
    (hP : P.PosSemidef)
    (hQ : Q.IsHermitian)
    {r b : ℕ}
    (hr : P.rank ≤ r)
    (hb : posIndex hQ ≤ b) :
    2 * rtrace P - (r : ℝ)
        + 4 * rtrace Q - 4 * (b : ℝ)
        + matrixSpectralDefect P hP r
      ≤
    frobSq (P + Q) := by

  classical

  set Qp := hermPosPart hQ with hQp_def
  set Qm := hermNegPart hQ with hQm_def

  have hQdec :
      Q = Qp - Qm :=
    (hermPosPart_sub_hermNegPart hQ).symm

  have hQp_psd :
      Qp.PosSemidef :=
    hermPosPart_posSemidef hQ

  have hQm_psd :
      Qm.PosSemidef :=
    hermNegPart_posSemidef hQ

  have hQpQm :
      Qp * Qm = 0 :=
    hermPosPart_mul_hermNegPart hQ

  set d := Fintype.card n

  set p : Fin d → ℝ :=
    hP.isHermitian.eigenvalues₀

  set m : Fin d → ℝ :=
    hQm_psd.isHermitian.eigenvalues₀

  have hp_nn :
      ∀ k, 0 ≤ p k := by
    intro k

    rw [
      show
        p k =
          hP.isHermitian.eigenvalues (eigEquiv k)
        from
          (eigenvalues_eigEquiv hP.isHermitian k).symm
    ]

    exact hP.eigenvalues_nonneg _

  have hm_nn :
      ∀ k, 0 ≤ m k := by
    intro k

    rw [
      show
        m k =
          hQm_psd.isHermitian.eigenvalues (eigEquiv k)
        from
          (eigenvalues_eigEquiv
            hQm_psd.isHermitian k).symm
    ]

    exact hQm_psd.eigenvalues_nonneg _

  have hp_card :
      (spectralSupport p).card ≤ r := by

    change #{k | p k ≠ 0} ≤ r

    calc
      #{k | p k ≠ 0}
          =
        #{i | hP.isHermitian.eigenvalues i ≠ 0} :=
            (card_eigenvalues_reindex
              hP.isHermitian
              (· ≠ 0)).symm

      _ = P.rank := by
            rw [
              hP.isHermitian.rank_eq_card_non_zero_eigs,
              Fintype.card_subtype
            ]

      _ ≤ r := hr

  have htraceP :
      rtrace P = ∑ k, p k := by
    rw [rtrace_eq_sum_eigenvalues hP.isHermitian]

    exact
      sum_eigenvalues_reindex
        hP.isHermitian
        id

  have htraceQm :
      rtrace Qm = ∑ k, m k := by
    rw [
      rtrace_eq_sum_eigenvalues
        hQm_psd.isHermitian
    ]

    exact
      sum_eigenvalues_reindex
        hQm_psd.isHermitian
        id

  have hfrobP :
      frobSq P = ∑ k, (p k) ^ 2 := by
    rw [
      frobSq_hermitian_eq_sum_sq_eigenvalues
        hP.isHermitian
    ]

    exact
      sum_eigenvalues_reindex
        hP.isHermitian
        (· ^ 2)

  have hfrobQm :
      frobSq Qm = ∑ k, (m k) ^ 2 := by
    rw [
      frobSq_hermitian_eq_sum_sq_eigenvalues
        hQm_psd.isHermitian
    ]

    exact
      sum_eigenvalues_reindex
        hQm_psd.isHermitian
        (· ^ 2)

  have hexpand :
      frobSq (P + Q)
        =
      frobSq P
        + 2 * RCLike.re (P * Qp).trace
        - 2 * RCLike.re (P * Qm).trace
        + frobSq Qp
        + frobSq Qm := by

    have h1 :
        frobSq (-Qm) = frobSq Qm := by
      unfold frobSq
      rw [conjTranspose_neg, neg_mul_neg]

    have h2 :
        RCLike.re (Qp * -Qm).trace = 0 := by
      rw [mul_neg, hQpQm]
      simp

    rw [
      hQdec,
      frobSq_add_hermitian
        hP.isHermitian
        (hQp_psd.isHermitian.sub
          hQm_psd.isHermitian),
      sub_eq_add_neg Qp Qm,
      frobSq_add_hermitian
        hQp_psd.isHermitian
        hQm_psd.isHermitian.neg,
      h1,
      h2,
      mul_add,
      mul_neg,
      trace_add,
      trace_neg,
      map_add,
      map_neg
    ]

    ring

  have hPQp :
      0 ≤ RCLike.re (P * Qp).trace :=
    trace_mul_nonneg_of_posSemidef
      hP
      hQp_psd

  have hvN :
      RCLike.re (P * Qm).trace
        ≤
      ∑ k, p k * m k :=
    vonNeumann_trace_ineq
      hP.isHermitian
      hQm_psd.isHermitian

  have hminus :
      ∑ k, (p k - m k) ^ 2
        ≤
      frobSq P
        - 2 * RCLike.re (P * Qm).trace
        + frobSq Qm := by

    have hsplit :
        ∑ k, (p k - m k) ^ 2
          =
        ∑ k, (p k) ^ 2
          - 2 * ∑ k, p k * m k
          + ∑ k, (m k) ^ 2 := by

      simp only [
        sub_sq,
        Finset.sum_add_distrib,
        Finset.sum_sub_distrib,
        Finset.mul_sum,
        mul_assoc
      ]

    rw [
      hsplit,
      hfrobP,
      hfrobQm
    ]

    linarith

  have hstableSum :=
    stable_scalar_sum
      p
      m
      hp_nn
      hm_nn

  have hstableId :=
    sum_stable_scalar_eq_rank_defect
      p
      hp_card

  have hstableSumNorm :
      (∑ k, (2 * p k - 1 + psi (p k)))
        ≤
      (∑ k, (p k - m k) ^ 2)
        + 4 * (∑ k, m k) := by

    calc
      (∑ k, (2 * p k - 1 + psi (p k)))
          ≤
        ∑ k, ((p k - m k) ^ 2 + 4 * m k) :=
          hstableSum

      _ =
        (∑ k, (p k - m k) ^ 2)
          + ∑ k, 4 * m k := by
            rw [Finset.sum_add_distrib]

      _ =
        (∑ k, (p k - m k) ^ 2)
          + 4 * (∑ k, m k) := by
            rw [Finset.mul_sum]

  have hstableSum' :
      (∑ k, (2 * p k - 1 + psi (p k)))
          - 4 * (∑ k, m k)
        ≤
      ∑ k, (p k - m k) ^ 2 := by
    linarith [hstableSumNorm]

  have hminusStable :
      2 * rtrace P - (r : ℝ)
          + matrixSpectralDefect P hP r
          - 4 * rtrace Qm
        ≤
      frobSq P
        - 2 * RCLike.re (P * Qm).trace
        + frobSq Qm := by

    rw [htraceP, htraceQm]

    change
      2 * (∑ k, p k) - (r : ℝ)
          + spectralDefect p r
          - 4 * (∑ k, m k)
        ≤
      frobSq P
        - 2 * RCLike.re (P * Qm).trace
        + frobSq Qm

    rw [← hstableId]

    exact le_trans hstableSum' hminus

  have hplus :
      4 * rtrace Qp - 4 * (b : ℝ)
        ≤
      frobSq Qp := by

    rw [
      hQp_def,
      rtrace_hermPosPart,
      frobSq_hermPosPart
    ]

    have hcard :
        #{i | (hQ.eigenvalues i)⁺ ≠ 0}
          ≤ b := by

      calc
        #{i | (hQ.eigenvalues i)⁺ ≠ 0}
            =
          #{i | 0 < hQ.eigenvalues i} := by
              congr 1
              ext i
              simp [posPart_eq_zero, not_le]

        _ ≤ b := hb

    have hsq :=
      sum_sq_lower_of_card_pos_le
        hcard
        (2 : ℝ)

    norm_num at hsq

    linarith

  have htraceQ :
      4 * rtrace Q
        =
      4 * rtrace Qp - 4 * rtrace Qm := by

    rw [hQdec, rtrace_sub]

    ring

  linarith [
    hminusStable,
    hplus,
    hPQp,
    hexpand,
    htraceQ
  ]

/--
The exact stability-enhanced `c = 2` rank--trace inequality.

Compared with `RHLinalg.rank_trace_ineq_two`, the additional term is
`matrixSpectralDefect P hP r`.

The only extra hypothesis is the trace bound `tr P ≤ r`, which is precisely
the hat-unit bound already available in Anthropic's zero-side assembly.
-/
theorem stable_rank_trace_ineq_two
    {P Q : Matrix n n 𝕜}
    (hP : P.PosSemidef)
    (hQ : Q.IsHermitian)
    {r b : ℕ}
    (hr : P.rank ≤ r)
    (hb : posIndex hQ ≤ b)
    (htrP : rtrace P ≤ r) :
    4 * rtrace (P + Q)
        - 3 * (r : ℝ)
        - 4 * (b : ℝ)
        + matrixSpectralDefect P hP r
      ≤
    frobSq (P + Q) := by

  have hpre :=
    stable_rank_trace_pre
      hP
      hQ
      hr
      hb

  rw [rtrace_add]

  unfold matrixSpectralDefect at hpre ⊢

  linarith

end HurtadoZeta23