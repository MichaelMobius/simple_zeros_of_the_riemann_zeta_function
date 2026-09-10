# v20 manuscript alignment

Date: 9 September 2026

This revision aligns the paper with the already-audited v20 Lean formalization. It does not change the main theorem, the numerical constant, the seven-point certificate, or the historical `v1.2.0-paper` release.

Changes made:

- update manuscript version/date metadata to v20;
- state in the abstract that the signed kernel inequality at `89/100` is proved analytically in Lean;
- retain `verify_improved_bound.py` as an independent non-Lean reproducibility check rather than an external v20 theorem input;
- update the provenance table to include the v20 signed-kernel wrapper;
- add a direct positive-semidefiniteness justification for the limiting kernel Gram matrix;
- make the domain used in the spectral-threshold Jensen step explicit;
- summarize the exact analytic Lean route for `k(89/100)`;
- replace the obsolete two-certificate v17 trust-boundary description by the v20 one-certificate interface;
- record the audited standard axiom closure `[propext, Classical.choice, Quot.sound]` and the symbolic repair of the inherited finite pair-count lemma;
- correct the `v1.3.0-lean-analytic` release notes so they distinguish an unchanged theorem/bound from the later v18/v19 manuscript hardening.

The sole explicit external mathematical certificate argument of the v20 published wrapper remains `ArchivedSevenPointClaim`. Software provenance remains an overlay on the pinned Anthropic `formal-math/zeta23` commit `fbdc36bbf17d20af3fd0447c6d1a8a02773c9844`; no clean-room claim is made.
