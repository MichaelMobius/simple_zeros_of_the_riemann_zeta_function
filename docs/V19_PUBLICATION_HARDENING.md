# v19 publication hardening

Date: 7 September 2026

## Purpose

This revision implements the mandatory changes found by a hostile-referee
publication audit of the v18 manuscript.  It does not change the theorem, the
published numerical constant, the position-weighted seven-point certificate,
or the Lean theorem statement.

## Changes

1. **Alpöge--Furman theorem labels.**  The manuscript now distinguishes the
   Montgomery--Taylor clause of Theorem A in the current Alpöge--Furman paper
   from the historical/formal `Theorem D` label retained in Anthropic's Lean
   artifact.  The previous wording `Theorem D of Alpöge--Furman` was
   bibliographically inaccurate for the current paper version.
2. **Logical derivation versus independent discovery.**  Appendix headings now
   say `Self-contained derivation` rather than `Independent proof`.  Appendix
   III explicitly records that its prime-side architecture parallels Section 5
   of Alpöge--Furman while deriving the needed estimates from the cited
   classical inputs rather than importing their theorem as a premise.
3. **Unbounded-domain certificate closure.**  The seven-point verifier now
   fail-closes on the exact pressure cutoff.  It checks
   `2714/10^7 * 57480/4000 - 39/10000 = 9/500000000 > 0` before constructing
   the finite search.  A `--check-cutoff-only` mode exposes this audit cheaply.
4. **Uniform error accumulation.**  The block approximation error is quantified
   by a compact-uniform `eta_T(R)`.  The manuscript proves
   `|D(G_B)-D(K_B)| <= 2 m^2 eta_T(R)` and then explicitly derives the total
   `O(N eta_T(R)) = o(N)` error over all shifted blocks.
5. **Normalized span.**  The pressure averaging step now proves directly from
   Riemann--von Mangoldt that `x_last-x_first <= N(T,2T)` for all sufficiently
   large `T`, instead of referring vaguely to a previously used consequence.
6. **Attribution and notation.**  The stability-enhanced rank--trace lemma is
   attributed to Jo at its point of use, and `G_B` is explicitly defined as the
   principal Gram block associated with a retained block.

## Mathematical status

The final bound remains

\[
\frac{1125000H_{\rm MT}-2220}{1120671}
=0.6731175265883904388095857434106058666\ldots .
\]

No new numerical optimization is introduced.  The new verifier assertion only
makes explicit, machine-checked, and fail-closed a cutoff inequality already
used implicitly to reduce the nonnegative orthant to a finite search.

## Publication classification

These changes address the three mandatory issues from the hostile-referee pass:
correct theorem provenance, explicit unbounded-domain certificate closure, and
quantitative passage from uniform block error to the global `o(N)` term.
## Frozen versus hardened verifier

The historical 256-bit certificate remains tied to the exact verifier object
in release `v1.0.0-paper` and to its published SHA-256.  The file at the same
repository path on the v19/default branch intentionally differs by the new
fail-closed cutoff assertion and `--check-cutoff-only` audit mode.  v19 does
not relabel the modified file as the historical frozen verifier and does not
change the archived certificate hash.

