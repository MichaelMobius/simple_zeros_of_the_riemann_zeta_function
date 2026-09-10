# Pressure-Preserving Refinements for Simple Zeros of the Riemann Zeta Function

This repository contains the manuscript, formalization, and reproducibility artifacts for

> **Pressure-Preserving Refinements for Simple Zeros of the Riemann Zeta Function**

by **Michael Hurtado**.

The manuscript establishes the unconditional lower bound

$$
\liminf_{T\to\infty}
\frac{N_0^s(T,2T)}{N(T,2T)}
\ge
0.6731175265883904388096\ldots
$$

for the proportion of simple zeros of the Riemann zeta function on the critical line.

The mathematical bound is the v17 result. The current v20 formalization hardens its proof provenance by replacing the signed limiting-kernel certificate at `g = 0.89` with an analytic Lean proof, without changing the numerical constant or the manuscript.

---

## Main result

Let

$$
H_{\rm MT}=\frac32-\frac1{\sqrt2}\cot\left(\frac1{\sqrt2}\right).
$$

The bound is

$$
\boxed{
\liminf_{T\to\infty}
\frac{N_0^s(T,2T)}{N(T,2T)}
\ge
\frac{1125000H_{\rm MT}-2220}{1120671}
}
$$

with numerical value

$$
0.6731175265883904388095857434\ldots.
$$

The computer-assisted seven-point component uses the position-dependent pressure vector

$$
p=\frac1{10^7}(2714,3733,3553,3553,3733,2714),
\qquad \sum_j p_j=\frac1{500},
$$

and the archived Arb/FLINT computation certifies

$$
F_{6,\mathrm{nonuniform}}\ge\frac{39}{10000}=0.0039.
$$

The refined global argument preserves this positional pressure and uses adjacent-pair pinching with block length

$$
m=450.
$$

---

## Repository structure

```text
.
├── README.md
├── CITATION.cff
├── LICENSE-CODE
├── LICENSE-CONTENT
│
├── paper/
│   ├── main.tex
│   └── main.pdf
│
├── certification/
│   ├── arb_256/
│   └── v17/
│
├── lean_harness/
│   ├── frozen/
│   ├── v17_weighted/
│   ├── v17_energy/
│   ├── v17_strong/
│   ├── v17_global/
│   ├── v20_analytic/
│   └── ...
│
└── docs/
    ├── RELEASE_v1.2.0-paper.md
    ├── RELEASE_v1.3.0-lean-analytic.md
    ├── V20_ADVERSARIAL_AUDIT.md
    └── V20_ANALYTIC_KERNEL_PLAN.md
```

### `paper/`

Contains the submission-ready LaTeX source and compiled manuscript. The manuscript remains the v17 mathematical revision; v20 changes formal provenance, not the paper's quantitative theorem.

### `certification/arb_256/`

Contains the archived 256-bit Arb/FLINT proof artifact for the nonuniform seven-point certificate, including the execution log, environment record, reproduction scripts, and SHA-256 manifest.

### `certification/v17/`

Contains the historical exact-arithmetic verifier for the v17 signed scalar kernel enclosure, pressure accounting, contradiction margin, and final constant. These files remain reproducibility artifacts. In v20 the signed kernel inequality is no longer an explicit mathematical input to the published Lean wrapper.

### `lean_harness/v20_analytic/`

Contains the v20 analytic Lean proof of the signed limiting-kernel point and the final wrapper that feeds it into the existing v17 global assembly.

---

## Reproducibility releases

### Current formal-provenance publication target

**`v1.3.0-lean-analytic`** is the publication target for the v20 formalization in which the signed limiting-kernel certificate is proved analytically in Lean. Its canonical release notes are prepared in

```text
docs/RELEASE_v1.3.0-lean-analytic.md
```

The numerical lower bound and v17 manuscript are unchanged.

### Frozen v17 manuscript release

**`v1.2.0-paper`** freezes the v17 manuscript, v17 formalization state, and v17 exact-arithmetic certificate. Its canonical release notes are in

```text
docs/RELEASE_v1.2.0-paper.md
```

### Previous releases

- **`v1.1.0-paper`** — preceding submission-ready manuscript.
- **`v1.0.0-paper @ c57f53e`** — frozen historical Arb/FLINT computational artifact reused unchanged by later revisions.

The separation is intentional:

```text
v1.3.0-lean-analytic  (publication target)
    │
    └── v20 Lean provenance hardening
             │
             ├── same v17 mathematical bound
             ├── same v17 manuscript
             ├── signed kernel point proved inside Lean
             └── one explicit external mathematical certificate frontier
                      │
                      ▼
v1.2.0-paper
    │
    └── v17 manuscript + two-frontier Lean wrapper
             │
             ▼
v1.0.0-paper @ c57f53e
    │
    └── frozen 256-bit Arb/FLINT seven-point certificate
```

---

## Historical 256-bit seven-point certificate

The archived certification run records:

| Parameter | Value |
| --- | ---: |
| Grid denominator | `4000` |
| Working precision | `256 bits` |
| Initial boxes | `1296` |
| Visited nodes | `1,119,372` |
| Splits | `559,038` |
| Pruned nodes | `560,334` |
| Maximum depth | `39` |
| Status | `verified=true` |

The certified pressure vector is

```text
(2714, 3733, 3553, 3553, 3733, 2714) / 10^7
```

and the certified target is

```text
F6_nonuniform >= 39/10000
```

The frozen verifier SHA-256 is

```text
8eb7b4a17da8e114881264d3c2fc8daf262a0558d4248692b386c0fca2cc4301
```

and the archived 256-bit log SHA-256 is

```text
4b0e62dcb5c4014504981f16e431144e3a01184b2aa2aa6b0bf650705d59db83
```

The complete manifest is `certification/arb_256/SHA256SUMS.txt`.

### Reproduction

The recorded reference environment uses

```text
Python 3.14.7
python-flint 0.9.0
```

Linux/macOS:

```bash
cd certification/arb_256
bash run_certificate_256.sh
```

Windows PowerShell:

```powershell
cd certification/arb_256
.\run_certificate_256.ps1
```

A successful execution must terminate with `verified=true`.

---

## Historical v17 exact-arithmetic signed-kernel verifier

The v17 verifier is

```text
certification/v17/verify_improved_bound.py
```

and can be replayed with

```bash
python certification/v17/verify_improved_bound.py \
  --output certification/v17/verification.generated.json
```

Among other checks, it certifies the signed enclosure

$$
\frac{171389}{1000000}<k\!\left(\frac{89}{100}\right).
$$

In the historical v17 wrapper this enclosure was represented by the explicit external proposition

```text
V17KernelSignedCertPointClaim
```

In v20 the same inequality is instead proved analytically inside Lean. The verifier and frozen JSON remain in the repository for provenance, reproducibility, and independent cross-checking; they are not an explicit mathematical argument of the v20 published wrapper.

---

## v20 Lean formalization status

The v20 analytic theorem is

```text
HurtadoZeta23.v20_kernel_signed_89_100
```

in

```text
HurtadoZeta23.V20KernelSignedAnalytic
```

and proves

```text
(171389 / 1000000 : ℝ) < limitingk (89 / 100 : ℝ)
```

from exact integral identities, rational Taylor bounds for sine and cosine, Mathlib's proved bounds for `π`, and exact rational arithmetic.

The final CI root is

```text
HurtadoZeta23.V20FinalAssembly
```

and the public epsilon-form theorem is

```text
HurtadoZeta23.v20_published_eps_form
```

Its only explicit external mathematical certificate argument is

```text
ArchivedSevenPointClaim
```

The v20 CI builds against the pinned upstream source base

```text
formal-math commit: fbdc36bbf17d20af3fd0447c6d1a8a02773c9844
```

The final audited pre-merge run was

```text
GitHub Actions run: 34428159178
Audited branch HEAD: ebf11ae228638e32d4e77a99e78f405ee1600dea
```

and the audited implementation was merged into `main` as

```text
fe2eef5516c9eb3443c0d2a7f22b73a5f2afb986
```

The workflow directly builds the repaired v17 bridge, the v20 analytic theorem, and the final v20 assembly; it also enforces the exact audited axiom closure and dependency/trust guards.

---

## Axiom and native-evaluator audit

A transitive adversarial audit found that the inherited finite pair-count lemma

```text
HurtadoZeta23.v17_pairMultiplicitySumNat_450
```

had previously used `native_decide`, which exposed a native-evaluator primitive in the final theorem's axiom report.

That lemma is now proved symbolically. The v20 CI audits the following four targets:

```text
HurtadoZeta23.v17_pairMultiplicitySumNat_450
HurtadoZeta23.v20_kernel_signed_89_100
HurtadoZeta23.v20_kernel_signed_claim
HurtadoZeta23.v20_published_eps_form
```

and requires the exact standard Mathlib axiom set

```text
[propext, Classical.choice, Quot.sound]
```

for all four. The workflow rejects `sorryAx`, `_native.native_decide.ax_`, placeholders in the v20 sources, new trusted/unsafe declarations there, and circular dependencies back to the historical signed-certificate frontier.

Thus “kernel-checked” here means that Lean checks the proof terms under this explicit standard Mathlib axiom boundary; it does not mean constructively axiom-free.

---

## Trust model

The v20 published wrapper has **one explicit external mathematical certificate frontier**.

1. **Historical seven-point Arb/FLINT certificate.** `ArchivedSevenPointClaim` names the proposition supported by the frozen 256-bit branch-and-bound run. Its computational trust base includes the frozen verifier, `python-flint`, FLINT/Arb, the recorded environment, and the correctness of directed interval arithmetic in those libraries.

The signed limiting-kernel point at `g = 0.89` is no longer an external mathematical certificate in v20: it is proved inside Lean and converted internally to the historical `V17KernelSignedCertPointClaim` interface required by the v17 assembly.

This reduction in the mathematical certificate frontier does **not** imply clean-room software independence. The implementation still builds on the pinned Anthropic `formal-math/zeta23` source base above; that dependency is software provenance rather than an extra theorem parameter.

The archived 128-bit and 256-bit Arb executions are replications of the same verification algorithm at different working precisions and should not be interpreted as algorithmically independent proof implementations.

---

## Relation to previous work

The upstream work of **Sunghyeon Jo** introduced the relevant reproducible seven-point stability framework with uniform pressure and certified

$$
\frac{19}{5000}=0.0038,
$$

leading to the bound

$$
0.6730085279277797\ldots.
$$

A subsequent reproducible refinement by **Lea Rademacher** strengthened the uniform seven-point certificate to

$$
\frac{191}{50000}=0.00382,
$$

leading to the bound

$$
0.6730213619501665\ldots.
$$

The present mathematical refinement keeps the same total pressure

$$
\sum_jp_j=\frac1{500},
$$

but allows its distribution among the six gap positions to vary. The certified nonuniform vector raises the local value to

$$
\frac{39}{10000}=0.0039.
$$

The v17 shifted-block and adjacent-pair argument then raises the resulting global lower bound to

$$
0.6731175265883904388095857434\ldots.
$$

v20 leaves this quantitative result unchanged and hardens the formal provenance of the signed-kernel step.

---

## AI provenance

Recent upstream computational artifacts relevant to this project report the use of AI systems during their development.

The present repository treats AI use as **research provenance rather than mathematical authorship**.

Mathematical claims are intended to be supported by explicit arguments, cited external results, reproducible computational certificates, or kernel-checked formal proofs. Computer-assisted components are accompanied by source code, execution records, cryptographic hashes, machine-readable parameters, and reproduction instructions for independent inspection.

---

## Citation

If you use the mathematical result, please cite the accompanying manuscript. If you use or reproduce the computational or formal artifacts, please also cite the relevant repository release.

Citation metadata is provided in `CITATION.cff`.

- `v1.3.0-lean-analytic` is the v20 formal-provenance publication target.
- `v1.2.0-paper` freezes the v17 manuscript state.
- `v1.1.0-paper` freezes the preceding submission-ready manuscript.
- `v1.0.0-paper @ c57f53e` freezes the historical Arb/FLINT computational artifact.

---

## License

Source code, including certificate verifiers and reproduction scripts, is released under the **MIT License** unless otherwise stated. See `LICENSE-CODE`.

The manuscript, documentation, certificate metadata, execution logs, and other non-software material are released under **CC BY 4.0**. See `LICENSE-CONTENT`.

Third-party software and dependencies retain their respective licenses.

---

## Author

**Michael Hurtado**

Repository: `https://github.com/MichaelMobius/simple_zeros_of_the_riemann_zeta_function`

---

## Status

- **Current manuscript:** v17
- **Current formalization:** v20 analytic signed-kernel hardening
- **Current formal-provenance publication target:** `v1.3.0-lean-analytic`
- **Historical frozen manuscript release:** `v1.2.0-paper`
- **Historical Arb/FLINT certificate:** `verified=true`, 256 bits
- **Certified seven-point local bound:** `39/10000`
- **Signed kernel inequality:** `171389/1000000 < k(89/100)`, proved analytically in Lean in v20
- **Lean final assembly:** `HurtadoZeta23.V20FinalAssembly`
- **Lean explicit external mathematical frontiers:** one (`ArchivedSevenPointClaim`)
- **Audited axiom closure:** `[propext, Classical.choice, Quot.sound]`
- **Resulting unconditional bound:**

$$
\boxed{0.6731175265883904388095857434\ldots}
$$
