import HurtadoZeta23.StableRankTraceMatrix
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic

noncomputable section

open Matrix Finset
open scoped ComplexOrder BigOperators
open RHLinalg

namespace HurtadoZeta23

variable {𝕜 : Type*} [RCLike 𝕜]

/--
A multiplicity-preserving equality of the nonzero parts of two finite
real spectra.

Instead of storing an explicit equivalence between the subtype-indexed
supports, we record exactly its two invariant consequences:

* equal support cardinality;
* equal sums of every test function over the nonzero spectra.

This avoids irrelevant universe/subtype bookkeeping while retaining the
full multiplicity information needed below.
-/
structure NonzeroSpectrumMatch
    {ι κ : Type*}
    [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (p : ι → ℝ) (m : κ → ℝ) : Prop where

  support_card_eq :
    (spectralSupport p).card =
      (spectralSupport m).card

  sum_eq :
    ∀ F : ℝ → ℝ,
      (∑ i ∈ spectralSupport p, F (p i))
        =
      ∑ j ∈ spectralSupport m, F (m j)

/--
Reindexing a function of the nonzero spectrum across a
`NonzeroSpectrumMatch`.
-/
theorem sum_over_support_eq_of_match
    {ι κ : Type*}
    [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    {p : ι → ℝ} {m : κ → ℝ}
    (h : NonzeroSpectrumMatch p m)
    (F : ℝ → ℝ) :
    (∑ i ∈ spectralSupport p, F (p i))
      =
    ∑ j ∈ spectralSupport m, F (m j) := by

  exact h.sum_eq F

/--
Matching nonzero spectra have the same number of nonzero eigenvalues.
-/
theorem support_card_eq_of_match
    {ι κ : Type*}
    [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    {p : ι → ℝ} {m : κ → ℝ}
    (h : NonzeroSpectrumMatch p m) :
    (spectralSupport p).card =
      (spectralSupport m).card := by

  exact h.support_card_eq

/--
For a finite spectrum, the sum of `psi` over all eigenvalues equals its
nonzero-spectrum contribution plus one for every zero eigenvalue.

The complement of `spectralSupport m` is precisely the set where `m = 0`,
and `psi 0 = 1`.
-/
theorem sum_psi_eq_support_plus_zeros
    {κ : Type*}
    [Fintype κ] [DecidableEq κ]
    (m : κ → ℝ) :
    (∑ j, psi (m j))
      =
    (∑ j ∈ spectralSupport m, psi (m j))
      +
    ((Fintype.card κ - (spectralSupport m).card : ℕ) : ℝ) := by

  classical

  let s : Finset κ := spectralSupport m

  have hsplit :
      (∑ j : κ, psi (m j))
        =
      (∑ j ∈ s, psi (m j))
        +
      (∑ j ∈ Finset.univ.filter (fun j => ¬ j ∈ s),
        psi (m j)) := by

    rw [
      ← Finset.sum_filter_add_sum_filter_not
        Finset.univ
        (fun j => j ∈ s)
        (fun j => psi (m j))
    ]

    simp

  have hzero :
      ∀ j ∈ Finset.univ.filter (fun j => ¬ j ∈ s),
        m j = 0 := by

    intro j hj

    have hjnot : j ∉ s := by
      simpa using hj

    simp only [
      s,
      spectralSupport,
      Finset.mem_filter,
      Finset.mem_univ,
      true_and,
      not_ne_iff
    ] at hjnot

    exact hjnot

  have hzset :
      Finset.univ.filter (fun j => ¬ j ∈ s)
        =
      sᶜ := by
    ext j
    simp

  have hzerosum :
      (∑ j ∈ Finset.univ.filter (fun j => ¬ j ∈ s),
          psi (m j))
        =
      ((Fintype.card κ - s.card : ℕ) : ℝ) := by

    calc
      (∑ j ∈ Finset.univ.filter (fun j => ¬ j ∈ s),
          psi (m j))
          =
        ∑ _j ∈ Finset.univ.filter (fun j => ¬ j ∈ s),
          (1 : ℝ) := by

            apply Finset.sum_congr rfl
            intro j hj

            have hz : m j = 0 :=
              hzero j hj

            rw [hz]

            exact psi_zero

      _ =
        ((Finset.univ.filter
          (fun j => ¬ j ∈ s)).card : ℝ) := by
            simp

      _ =
        ((sᶜ.card : ℕ) : ℝ) := by
            rw [hzset]

      _ =
        ((Fintype.card κ - s.card : ℕ) : ℝ) := by
            rw [Finset.card_compl]

  rw [hsplit, hzerosum]

/--
Abstract Gram-spectrum bridge.

If `p` is the spectrum of `P = V Vᴴ`, `m` is the spectrum of `M = Vᴴ V`,
`M` has exactly `r` spectral slots, and their nonzero spectra coincide with
multiplicity, then the padded defect used by the stable rank--trace
inequality is exactly

`Σ ψ(λᵢ(M))`.
-/
theorem spectralDefect_eq_sum_psi_of_nonzero_match
    {ι κ : Type*}
    [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (p : ι → ℝ)
    (m : κ → ℝ)
    {r : ℕ}
    (hr : Fintype.card κ = r)
    (hmatch : NonzeroSpectrumMatch p m) :
    spectralDefect p r =
      ∑ j, psi (m j) := by

  classical

  unfold spectralDefect

  have hsum :
      (∑ i ∈ spectralSupport p, psi (p i))
        =
      ∑ j ∈ spectralSupport m, psi (m j) := by
    exact
      sum_over_support_eq_of_match
        hmatch
        psi

  have hcard :
      (spectralSupport p).card =
        (spectralSupport m).card := by
    exact
      support_card_eq_of_match hmatch

  rw [← hr]
  rw [hsum, hcard]

  symm

  exact
    sum_psi_eq_support_plus_zeros m


variable {n rι : Type*}
variable [Fintype n] [DecidableEq n]
variable [Fintype rι] [DecidableEq rι]

/--
Matrix-level packaging of the standard linear-algebra fact that
`P = V Vᴴ` and `M = Vᴴ V` have the same nonzero eigenvalues with
multiplicity.

The actual construction of this bridge may later be obtained from the
rectangular Gram relation between `V Vᴴ` and `Vᴴ V`.
-/
structure GramNonzeroSpectrumBridge
    (P : Matrix n n 𝕜)
    (hP : P.PosSemidef)
    (M : Matrix rι rι 𝕜)
    (hM : M.PosSemidef) : Prop where

  spectrumMatch :
    NonzeroSpectrumMatch
      hP.isHermitian.eigenvalues₀
      hM.isHermitian.eigenvalues₀

/--
Once the nonzero-spectrum bridge is supplied, the matrix defect in
`stable_rank_trace_ineq_two` becomes exactly the Gram defect

`tr Ψ(M) = Σ ψ(λᵢ(M))`.
-/
theorem matrixSpectralDefect_eq_gramDefect
    (P : Matrix n n 𝕜)
    (hP : P.PosSemidef)
    (M : Matrix rι rι 𝕜)
    (hM : M.PosSemidef)
    (hPM : GramNonzeroSpectrumBridge P hP M hM) :
    matrixSpectralDefect P hP (Fintype.card rι)
      =
    ∑ j, psi (hM.isHermitian.eigenvalues₀ j) := by

  unfold matrixSpectralDefect

  apply
    spectralDefect_eq_sum_psi_of_nonzero_match
      hP.isHermitian.eigenvalues₀
      hM.isHermitian.eigenvalues₀

  · simp

  · exact hPM.spectrumMatch

/--
Convenient name for the Gram-side stability defect.
-/
def gramSpectralDefect
    (M : Matrix rι rι 𝕜)
    (hM : M.PosSemidef) : ℝ :=
  ∑ j, psi (hM.isHermitian.eigenvalues₀ j)

/--
The enhanced rank--trace inequality rewritten directly with the Gram-side
defect, conditional only on the nonzero-spectrum equivalence.
-/
theorem stable_rank_trace_ineq_two_gram
    {P Q : Matrix n n 𝕜}
    (hP : P.PosSemidef)
    (hQ : Q.IsHermitian)
    (M : Matrix rι rι 𝕜)
    (hM : M.PosSemidef)
    (hPM : GramNonzeroSpectrumBridge P hP M hM)
    {b : ℕ}
    (hr : P.rank ≤ Fintype.card rι)
    (hb : posIndex hQ ≤ b)
    (htrP : rtrace P ≤ Fintype.card rι) :
    4 * rtrace (P + Q)
        - 3 * (Fintype.card rι : ℝ)
        - 4 * (b : ℝ)
        + gramSpectralDefect M hM
      ≤
    frobSq (P + Q) := by

  have h :=
    stable_rank_trace_ineq_two
      hP
      hQ
      hr
      hb
      htrP

  rw [
    matrixSpectralDefect_eq_gramDefect
      P
      hP
      M
      hM
      hPM
  ] at h

  exact h

end HurtadoZeta23