import HurtadoZeta23.CharpolyGramBridge
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic

noncomputable section

open Matrix Finset Polynomial
open scoped ComplexOrder

namespace HurtadoZeta23

universe uK uN uR

variable {𝕜 : Type uK} [RCLike 𝕜]

variable {n : Type uN}
variable {r : Type uR}

variable [Fintype n] [DecidableEq n]
variable [Fintype r] [DecidableEq r]

/--
The multiset of nonzero characteristic roots, with algebraic multiplicity.
-/
def nonzeroCharpolyRoots
    {ι : Type*}
    [Fintype ι]
    [DecidableEq ι]
    (A : Matrix ι ι 𝕜) :
    Multiset 𝕜 := by

  classical

  exact
    A.charpoly.roots.filter
      (fun z => z ≠ 0)

/--
The nonzero Hermitian eigenvalue multiset, represented in the same form
used by Mathlib's `roots_charpoly_eq_eigenvalues₀`.
-/
def nonzeroHermitianEigenRoots
    {ι : Type*}
    [Fintype ι]
    [DecidableEq ι]
    {A : Matrix ι ι 𝕜}
    (hA : A.IsHermitian) :
    Multiset 𝕜 := by

  classical

  exact
    (Multiset.map
      (RCLike.ofReal ∘ hA.eigenvalues₀)
      Finset.univ.val).filter
        (fun z => z ≠ 0)

/--
Characteristic roots and Hermitian eigenvalues agree with multiplicity;
filtering zero preserves that equality.
-/
theorem nonzeroCharpolyRoots_eq_eigenvalues₀
    {ι : Type*}
    [Fintype ι]
    [DecidableEq ι]
    {A : Matrix ι ι 𝕜}
    (hA : A.IsHermitian) :
    nonzeroCharpolyRoots A =
      nonzeroHermitianEigenRoots hA := by

  classical

  unfold
    nonzeroCharpolyRoots
    nonzeroHermitianEigenRoots

  rw [hA.roots_charpoly_eq_eigenvalues₀]

/--
Multiplication by a power of `X` inserts only zero roots.
-/
theorem filter_ne_zero_roots_X_pow_mul
    {K : Type*}
    [Field K]
    [DecidableEq K]
    (p : Polynomial K)
    (m : ℕ) :
    (Polynomial.X ^ m * p).roots.filter
        (fun z => z ≠ 0)
      =
    p.roots.filter
        (fun z => z ≠ 0) := by

  by_cases hp : p = 0

  · subst p
    simp

  ·
    have hx :
        (Polynomial.X ^ m : Polynomial K) ≠ 0 := by
      exact
        pow_ne_zero
          _
          Polynomial.X_ne_zero

    have hprod :
        Polynomial.X ^ m * p ≠ 0 := by
      exact mul_ne_zero hx hp

    rw [
      Polynomial.roots_mul hprod,
      Polynomial.roots_X_pow
    ]

    simp

/--
If `X^m p = X^n q`, then `p` and `q` have the same nonzero roots,
including algebraic multiplicity.
-/
theorem nonzeroRootsCancellation_proved
    {K : Type*}
    [Field K]
    [DecidableEq K]
    (p q : Polynomial K)
    (m n : ℕ)
    (h :
      Polynomial.X ^ m * p =
        Polynomial.X ^ n * q) :
    p.roots.filter (fun z => z ≠ 0)
      =
    q.roots.filter (fun z => z ≠ 0) := by

  calc
    p.roots.filter (fun z => z ≠ 0)
        =
      (Polynomial.X ^ m * p).roots.filter
        (fun z => z ≠ 0) := by

          symm

          exact
            filter_ne_zero_roots_X_pow_mul
              p
              m

    _ =
      (Polynomial.X ^ n * q).roots.filter
        (fun z => z ≠ 0) := by

          rw [h]

    _ =
      q.roots.filter (fun z => z ≠ 0) := by

          exact
            filter_ne_zero_roots_X_pow_mul
              q
              n

/--
The rectangular characteristic-polynomial identity therefore gives equality
of the two nonzero characteristic-root multisets.
-/
theorem gram_nonzero_charpoly_roots_eq
    (V : Matrix n r 𝕜) :
    nonzeroCharpolyRoots
        (V * V.conjTranspose)
      =
    nonzeroCharpolyRoots
        (V.conjTranspose * V) := by

  classical

  exact
    nonzeroRootsCancellation_proved
      (V * V.conjTranspose).charpoly
      (V.conjTranspose * V).charpoly
      (Fintype.card r)
      (Fintype.card n)
      (gram_charpoly_identity V)

/--
Consequently the nonzero Hermitian eigenvalue multisets agree.
-/
theorem gram_nonzero_eigenvalue_multisets_eq
    (V : Matrix n r 𝕜) :
    nonzeroHermitianEigenRoots
        (posSemidef_mul_conjTranspose_self V).isHermitian
      =
    nonzeroHermitianEigenRoots
        (Matrix.posSemidef_conjTranspose_mul_self V).isHermitian := by

  rw [
    ← nonzeroCharpolyRoots_eq_eigenvalues₀,
    ← nonzeroCharpolyRoots_eq_eigenvalues₀
  ]

  exact
    gram_nonzero_charpoly_roots_eq V

/--
Multiset-level nonzero-spectrum bridge.
-/
structure GramNonzeroRootMultisetBridge
    (V : Matrix n r 𝕜) : Prop where

  roots_eq :
    nonzeroHermitianEigenRoots
        (posSemidef_mul_conjTranspose_self V).isHermitian
      =
    nonzeroHermitianEigenRoots
        (Matrix.posSemidef_conjTranspose_mul_self V).isHermitian

/--
The multiset bridge is unconditional.
-/
theorem gramNonzeroRootMultisetBridge
    (V : Matrix n r 𝕜) :
    GramNonzeroRootMultisetBridge V := by

  exact
    ⟨gram_nonzero_eigenvalue_multisets_eq V⟩

/--
Sum of `psi` over the nonzero Hermitian spectrum.
-/
def nonzeroEigenRootPsiSum
    {ι : Type*}
    [Fintype ι]
    [DecidableEq ι]
    {A : Matrix ι ι 𝕜}
    (hA : A.IsHermitian) :
    ℝ :=

  ((nonzeroHermitianEigenRoots hA).map
      (fun z =>
        psi (RCLike.re z))).sum

/--
Filtering the scalar eigenvalue multiset at zero has exactly the cardinality
of `spectralSupport`.
-/
theorem card_nonzeroHermitianEigenRoots_eq_support
    {ι : Type*}
    [Fintype ι]
    [DecidableEq ι]
    {A : Matrix ι ι 𝕜}
    (hA : A.IsHermitian) :
    (nonzeroHermitianEigenRoots hA).card
      =
    (spectralSupport
      hA.eigenvalues₀).card := by

  classical

  unfold
    nonzeroHermitianEigenRoots
    spectralSupport

  rw [Multiset.filter_map]

  simp only [
    Function.comp_apply,
    Multiset.card_map
  ]

  have hpred :
      (fun i : Fin (Fintype.card ι) =>
        ((hA.eigenvalues₀ i : 𝕜) ≠ 0))
        =
      (fun i : Fin (Fintype.card ι) =>
        hA.eigenvalues₀ i ≠ 0) := by

    funext i

    apply propext

    constructor

    · intro h hzero

      apply h

      simp [hzero]

    · intro h hzero

      apply h

      have hre :=
        congrArg RCLike.re hzero

      simpa using hre

  simp only [hpred]

  have hval :
      (Finset.filter
        (fun i : Fin (Fintype.card ι) =>
          hA.eigenvalues₀ i ≠ 0)
        Finset.univ).val
        =
      Multiset.filter
        (fun i : Fin (Fintype.card ι) =>
          hA.eigenvalues₀ i ≠ 0)
        Finset.univ.val := by
    exact Finset.filter_val _ _

  have hcard :=
    congrArg Multiset.card hval

  simpa only [Finset.card_val] using hcard.symm

/--
The corresponding `psi` sum agrees with the support-restricted finite sum.
-/
theorem nonzeroEigenRootPsiSum_eq_support_sum
    {ι : Type*}
    [Fintype ι]
    [DecidableEq ι]
    {A : Matrix ι ι 𝕜}
    (hA : A.IsHermitian) :
    nonzeroEigenRootPsiSum hA
      =
    ∑ i ∈ spectralSupport hA.eigenvalues₀,
      psi (hA.eigenvalues₀ i) := by

  classical

  unfold
    nonzeroEigenRootPsiSum
    nonzeroHermitianEigenRoots
    spectralSupport

  rw [Multiset.filter_map]

  simp only [
    Function.comp_apply,
    Multiset.map_map
  ]

  have hpred :
      (fun i : Fin (Fintype.card ι) =>
        ((hA.eigenvalues₀ i : 𝕜) ≠ 0))
        =
      (fun i : Fin (Fintype.card ι) =>
        hA.eigenvalues₀ i ≠ 0) := by

    funext i

    apply propext

    constructor

    · intro h hzero

      apply h

      simp [hzero]

    · intro h hzero

      apply h

      have hre :=
        congrArg RCLike.re hzero

      simpa using hre

  have hpsi :
      (fun i : Fin (Fintype.card ι) =>
        psi
          (RCLike.re
            (hA.eigenvalues₀ i : 𝕜)))
        =
      (fun i : Fin (Fintype.card ι) =>
        psi (hA.eigenvalues₀ i)) := by

    funext i

    congr 1

    simp

  simp only [hpred, hpsi]

  have hval :
      (Finset.filter
        (fun i : Fin (Fintype.card ι) =>
          hA.eigenvalues₀ i ≠ 0)
        Finset.univ).val
        =
      Multiset.filter
        (fun i : Fin (Fintype.card ι) =>
          hA.eigenvalues₀ i ≠ 0)
        Finset.univ.val := by
    exact Finset.filter_val _ _

  have hsum :=
    congrArg
      (fun s : Multiset (Fin (Fintype.card ι)) =>
        (Multiset.map
          (fun i => psi (hA.eigenvalues₀ i))
          s).sum)
      hval

  exact hsum.symm

/--
Finite-multiset bookkeeping from equality of the nonzero spectra to equality
of the two stability defects.
-/
def RootMultisetToDefectBridge.{u, v, w} : Prop :=
  ∀ {K : Type u}
      [RCLike K]
      {ι : Type v}
      {κ : Type w}
      [Fintype ι]
      [DecidableEq ι]
      [Fintype κ]
      [DecidableEq κ]
      (P : Matrix ι ι K)
      (hP : P.PosSemidef)
      (M : Matrix κ κ K)
      (hM : M.PosSemidef),

    nonzeroHermitianEigenRoots
        hP.isHermitian
      =
    nonzeroHermitianEigenRoots
        hM.isHermitian
      →

    matrixSpectralDefect
        P hP (Fintype.card κ)
      =
    gramSpectralDefect
        M hM

/--
The finite-multiset bookkeeping bridge is unconditional.

Equality of the nonzero eigenvalue multisets gives equality both of their
cardinalities and of their `psi` sums. Missing Gram eigenvalues are zeros,
and each zero contributes `psi 0 = 1`.
-/
theorem rootMultisetToDefectBridge_proved :
    RootMultisetToDefectBridge.{uK, uN, uR} := by

  intro K _ ι κ _ _ _ _
    P hP M hM hroots

  let hp :=
    hP.isHermitian

  let hm :=
    hM.isHermitian

  have hcardRoots :=
    congrArg
      Multiset.card
      hroots

  have hsumRoots :=
    congrArg
      (fun s : Multiset K =>
        (s.map
          (fun z =>
            psi (RCLike.re z))).sum)
      hroots

  have hcard :
      (spectralSupport
          hp.eigenvalues₀).card
        =
      (spectralSupport
          hm.eigenvalues₀).card := by

    rw [
      ← card_nonzeroHermitianEigenRoots_eq_support hp,
      ← card_nonzeroHermitianEigenRoots_eq_support hm
    ]

    exact hcardRoots

  have hsum :
      (∑ i ∈ spectralSupport hp.eigenvalues₀,
        psi (hp.eigenvalues₀ i))
        =
      ∑ j ∈ spectralSupport hm.eigenvalues₀,
        psi (hm.eigenvalues₀ j) := by

    rw [
      ← nonzeroEigenRootPsiSum_eq_support_sum hp,
      ← nonzeroEigenRootPsiSum_eq_support_sum hm
    ]

    exact hsumRoots

  unfold
    matrixSpectralDefect
    gramSpectralDefect
    spectralDefect

  dsimp

  rw [hsum, hcard]

  symm

  simpa using
    (sum_psi_eq_support_plus_zeros
      hm.eigenvalues₀)

/--
Stable rank--trace inequality with the Gram defect, obtained from the
unconditional multiset bridge.
-/
theorem stable_rank_trace_ineq_two_of_root_multisets
    (V : Matrix n r 𝕜)
    {Q : Matrix n n 𝕜}
    (hQ : Q.IsHermitian)
    {b : ℕ}
    (hr :
      (V * V.conjTranspose).rank
        ≤ Fintype.card r)
    (hb :
      RHLinalg.posIndex hQ
        ≤ b)
    (htr :
      RHLinalg.rtrace
          (V * V.conjTranspose)
        ≤ Fintype.card r) :
    4 *
        RHLinalg.rtrace
          (V * V.conjTranspose + Q)
      - 3 * (Fintype.card r : ℝ)
      - 4 * (b : ℝ)
      +
        gramSpectralDefect
          (V.conjTranspose * V)
          (Matrix.posSemidef_conjTranspose_mul_self V)
      ≤
    RHLinalg.frobSq
      (V * V.conjTranspose + Q) := by

  have hP :
      (V * V.conjTranspose).PosSemidef :=
    posSemidef_mul_conjTranspose_self V

  have hM :
      (V.conjTranspose * V).PosSemidef :=
    Matrix.posSemidef_conjTranspose_mul_self V

  have hroots :
      nonzeroHermitianEigenRoots
          hP.isHermitian
        =
      nonzeroHermitianEigenRoots
          hM.isHermitian :=
    (gramNonzeroRootMultisetBridge V).roots_eq

  have hdefeq :
      matrixSpectralDefect
          (V * V.conjTranspose)
          hP
          (Fintype.card r)
        =
      gramSpectralDefect
          (V.conjTranspose * V)
          hM := by

    exact
      rootMultisetToDefectBridge_proved
        (V * V.conjTranspose)
        hP
        (V.conjTranspose * V)
        hM
        hroots

  have h :=
    stable_rank_trace_ineq_two
      hP
      hQ
      hr
      hb
      htr

  rw [hdefeq] at h

  exact h

end HurtadoZeta23