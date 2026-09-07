# v18 adversarial manuscript audit

Date: 7 September 2026

## Scope

This audit reviews the manuscript `paper/main.tex` adversarially with four separate questions in view:

1. Does the mathematical chain leading to the v17 constant contain an identified gap or contradiction?
2. Does the manuscript distinguish inherited mathematics from the contributions of the present project?
3. Does the article state the relationship to the Claude / Alpöge--Furman result accurately, including the origin of Theorem D?
4. Does the description of the Lean verification match the actual software and certificate trust boundaries?

The audit is intentionally stricter than a normal copy-edit. It treats ambiguous provenance, over-broad independence language, and inaccurate reproducibility terminology as defects even when they do not affect the theorem.

## Mathematical verdict

No defect was found in this audit that invalidates the v17 mathematical deduction or changes the published constant

\[
\frac{1125000H_{\rm MT}-2220}{1120671}
=0.6731175265883904388095857434\ldots.
\]

In particular, the audit rechecked the logical roles of:

- the position-weighted seven-point certificate;
- exact pressure redistribution and the identity `sum q_r = beta (m-6)`;
- adjacent-pair pinching;
- the scalar kernel inequality at `g0 = 0.89`;
- the spectral threshold argument;
- strong block stability for `m = 450`;
- shifted-block averaging; and
- the final algebraic assembly.

This conclusion should not be read as a substitute for independent peer review. It records that the present adversarial pass found no mathematical failure requiring withdrawal or alteration of the theorem.

## Provenance corrections introduced in v18

### Claude / Alpöge--Furman

The previous manuscript cited a `Claude26` preprint too loosely and referred to “Theorem D” without first giving its canonical provenance. The revised manuscript now cites Alpöge--Furman, records that the proof was discovered by Claude at Anthropic and verified/communicated by Alpöge and Furman, and identifies Theorem D as the Montgomery--Taylor optimized specialization relevant to the constant denoted `H_MT` in this paper.

The manuscript also cites Anthropic's research note as provenance for the discovery and formalization workflow.

### Logical independence versus software independence

The revised manuscript makes the following distinction explicit:

- **Written mathematical derivation.** The proof in the manuscript reconstructs the analytic/Gabor package from stated classical inputs and does not invoke Theorem D of Alpöge--Furman as a premise of the main theorem.
- **Lean software provenance.** The v17 `HurtadoZeta23` modules are compiled as an overlay on the pinned Anthropic `formal-math/zeta23` source tree at commit `fbdc36bbf17d20af3fd0447c6d1a8a02773c9844`.

Therefore the article does not claim a clean-room re-formalization of the entire underlying analytic library.

### Exact meaning of “two external propositions”

The final Lean theorem has exactly two **explicit external certificate propositions** as mathematical arguments:

1. `ArchivedSevenPointClaim`;
2. `V17KernelSignedCertPointClaim`.

The phrase “exactly two” does not mean that the complete software/foundational dependency stack consists of only two objects. Lean, Mathlib, the pinned Zeta23 library, and the usual trusted kernel/foundational stack remain part of the formal verification environment.

### Hurtado contribution layers

The revised manuscript separates the stages of the present project:

- the earlier frozen Hurtado artifact introduced the position-weighted pressure vector and the certified seven-point value `39/10000`;
- the present refinement introduces exact pressure preservation through shifted-block averaging, adjacent-pair pinching, the new signed scalar enclosure, and the `m = 450` assembly.

This avoids presenting the earlier Hurtado certificate as an unattributed external artifact.

## Additional literature and priority corrections

The revised manuscript adds:

- Lamzouri's independent, conceptually different proof of the 67.25% baseline;
- Bhatia as a standard source for von Neumann's trace inequality and pinching/majorization;
- the pinned Anthropic `formal-math` repository as software provenance;
- contemporaneous larger public computational claims by Ojha and Devine, with an explicit statement that they are not inputs to this proof and that this paper does **not** claim the largest publicly reported numerical value.

This is a priority/provenance clarification, not a concession that those contemporaneous claims have the same review or formal-verification status as the present theorem.

## Reproducibility terminology

The previous wording called a GitHub release “immutable”. GitHub does not enforce immutability for that release. The revised text instead calls it a **frozen release snapshot identified by its tag, commit SHA, and cryptographic hashes**. This is the property actually used by the reproducibility argument.

## Matrix-analysis dependencies

The revised manuscript now cites standard matrix analysis for:

- von Neumann's trace inequality;
- the pinching/majorization principle used to show that the convex unitarily invariant spectral trace functional does not increase under pinching.

The proof still does not require operator convexity of `Psi`.

## Formal verification status

No Lean theorem or certificate was changed by this editorial/provenance revision. The v17 formal result remains the implication from the two explicit certificate propositions to the published epsilon-form theorem, with kernel monotonicity and the universal scalar-pressure step proved internally in Lean.

The frozen release `v1.2.0-paper` remains untouched as the historical snapshot of the already published v17 state. v18 is a post-release manuscript clarification and provenance hardening pass.

## Final classification

**Mathematics:** no invalidating defect found.

**Formal proof:** no change to theorem or trust frontier; provenance description strengthened.

**Certificates:** no change.

**Main numerical constant:** no change.

**Required revision class:** substantive editorial/provenance revision, not a mathematical correction.
