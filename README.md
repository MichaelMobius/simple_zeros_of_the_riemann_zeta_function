# Pressure-Preserving Refinements for Simple Zeros of the Riemann Zeta Function

This repository contains the manuscript, formalization, and reproducibility
artifacts for

> **Pressure-Preserving Refinements for Simple Zeros of the Riemann Zeta
> Function**

by **Michael Hurtado**.

> **Current default-branch manuscript:** publication-hardened v19  
> **Repository auditability cleanup:** v20  
> **Mathematical theorem:** v17  
> **Current bound:** `0.6731175265883904388095857434...`  
> **Latest frozen theorem release:** `v1.2.0-paper`

The manuscript establishes the unconditional lower bound

$$
\liminf_{T\to\infty}
\frac{N_0^s(T,2T)}{N(T,2T)}
\ge
0.6731175265883904388096\ldots
$$

for the proportion of simple zeros of the Riemann zeta function on the
critical line.

The new ingredients are **exact pressure-preserving shifted-block accounting**
and an **adjacent-pair pinching refinement**, built on the existing nonuniform
seven-point certificate.

---

## Main result

Let

$$
H_{\rm MT}=\frac32-\frac1{\sqrt2}\cot\left(\frac1{\sqrt2}\right).
$$

The v17 bound is

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

The computer-assisted seven-point component uses the position-dependent
pressure vector

$$
p=\frac1{10^7}(2714,3733,3553,3553,3733,2714),
\qquad \sum_j p_j=\frac1{500},
$$

and the archived Arb/FLINT computation certifies

$$
F_{6,\mathrm{nonuniform}}\ge\frac{39}{10000}=0.0039.
$$

The refined global argument preserves this positional pressure and uses
adjacent-pair pinching with block length

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
│   │   ├── README.md
│   │   ├── certify_nonuniform_3900_v1_1.py
│   │   ├── run_certificate_256.ps1
│   │   ├── run_certificate_256.sh
│   │   ├── arb-certificate-256.log
│   │   ├── certificate-summary.json
│   │   ├── environment-256.txt
│   │   ├── requirements-lock-256.txt
│   │   ├── verifier-sha256-256.txt
│   │   ├── certificate-log-sha256-256.txt
│   │   └── SHA256SUMS.txt
│   │
│   └── v17/
│       ├── verify_improved_bound.py
│       ├── verification.json
│       └── verification.generated.json
│
├── lean_src/
│   ├── HurtadoZeta23/        # canonical browseable .lean sources
│   └── V17_FINAL_CLOSURE.txt
├── lean_harness/             # historical/stage-specific harness files
├── scripts/
│   └── install_hurtado_overlay.sh
│
└── docs/
    ├── RELEASE_v1.2.0-paper.md
    ├── V18_ADVERSARIAL_AUDIT.md
    ├── V19_PUBLICATION_HARDENING.md
    └── V20_PUBLIC_AUDITABILITY.md
```

### `paper/`

Contains the submission-ready LaTeX source and compiled manuscript.

### `certification/arb_256/`

Contains the archived 256-bit Arb/FLINT proof artifact for the nonuniform
seven-point certificate, including the execution log, environment record,
reproduction scripts, and SHA-256 manifest.

### `certification/v17/`

Contains a Python-standard-library exact-arithmetic verifier for the new v17
scalar kernel enclosure, pressure accounting, contradiction margin, and final
constant. It does **not** rerun the historical seven-point branch-and-bound
certificate.

### `lean_src/` and `lean_harness/`

`lean_src/HurtadoZeta23/` is the canonical human-browseable Lean source tree:
every Hurtado module in the published v17 final closure is stored as an ordinary
`.lean` file and can be inspected directly in GitHub.
`lean_src/V17_FINAL_CLOSURE.txt` records the exact transitive closure of
`HurtadoZeta23.V17FinalAssembly`. CI installs these sources on top of the pinned
upstream `formal-math/zeta23` tree using `scripts/install_hurtado_overlay.sh`.
The stage-specific `lean_harness/` directories remain for provenance and source
organization; encoded base64/tar source fragments are no longer used.

---

## Reproducibility releases

The current frozen manuscript release is:

### Current frozen v17 manuscript

**`v1.2.0-paper`** freezes the current v17 manuscript, formalization, and v17
exact-arithmetic certificate. Its canonical release notes are in
`docs/RELEASE_v1.2.0-paper.md`.

### Previous frozen manuscript

**`v1.1.0-paper`** freezes the preceding submission-ready manuscript.

### Frozen computational artifact

**`v1.0.0-paper @ c57f53e`** freezes the earlier Arb/FLINT computational
artifact reused by v17.

The separation is intentional:

```text
v1.2.0-paper
    │
    └── v17 manuscript + Lean formalization + v17 scalar certificate
             │
             ├── reuses v1.0.0-paper historical Arb/FLINT certificate
             │
             ▼
v1.1.0-paper
    │
    └── preceding frozen manuscript
             │
             ▼
v1.0.0-paper @ c57f53e
    │
    └── frozen Arb/FLINT certificate
             │
             ▼
      256-bit verification
             │
             ▼
 F6_nonuniform >= 39/10000
```

The v17 refinement reuses that seven-point certificate unchanged and adds a
separate exact-arithmetic scalar certificate plus a Lean-checked global
assembly.

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

A successful execution must terminate with `verified=true`. The verifier
should not be modified between hash verification and execution.

---

## v17 exact-arithmetic certificate

The v17 verifier is

```text
certification/v17/verify_improved_bound.py
```

and can be replayed with

```bash
python certification/v17/verify_improved_bound.py \
  --output certification/v17/verification.generated.json
```

The key additional signed enclosure consumed by the formal v17 route is

$$
\frac{171389}{1000000}<k\!\left(\frac{89}{100}\right).
$$

The verifier also checks, using exact rational arithmetic and rigorous
transcendental enclosures, that

$$
\left(\frac{171389}{1000000}\right)^2
>\frac{2937}{100000},
$$

together with the v17 pressure mass, contradiction margin, and the exact final
constant

$$
\frac{1125000H_{\rm MT}-2220}{1120671}.
$$

CI replays this verifier and compares its machine-readable output
semantically with the frozen `verification.json`.

---

## Lean formalization status

The v17 implication from the two explicit external certificate propositions to
the published epsilon-form theorem is kernel-checked in Lean.

The exact CI root is

```text
HurtadoZeta23.V17FinalAssembly
```

and the final public theorem is

```text
HurtadoZeta23.v17_published_eps_form_of_certificates
```

Its explicit external arguments are exactly

```text
ArchivedSevenPointClaim
V17KernelSignedCertPointClaim
```

The universal scalar-pressure inequality is **not** an additional external
assumption: it is derived inside Lean from the signed kernel certificate using
the proved monotonicity of the limiting kernel on the relevant interval.

More explicitly, the formal stack is **Mathlib + the pinned Anthropic
`formal-math/zeta23` formalization + the browseable `HurtadoZeta23` v17 source
tree**, with exactly two external numerical certificate propositions at the
final theorem boundary.

The exact final CI closure currently contains **127 Hurtado modules** and
builds successfully against

```text
formal-math commit: fbdc36bbf17d20af3fd0447c6d1a8a02773c9844
Lean:               4.33.0-rc2
mathlib commit:     51e6992efd06126df61a496bebf8f49482a4e129
```

The successful full build reaches

```text
Built HurtadoZeta23.V17ConcreteShiftedAssembly450
Built HurtadoZeta23.V17FinalAssembly
Build completed successfully (8964 jobs).
```

CI recomputes the exact transitive `HurtadoZeta23` closure from the browseable
source tree, checks it against `lean_src/V17_FINAL_CLOSURE.txt`, rejects
`sorry`, `admit`, explicit `axiom` declarations and `unsafe` declarations in
that closure, verifies the final theorem signature, replays the v17 exact
arithmetic certificate, and checks the historical certificate manifest hashes.

---

## Trust model

There are **two explicit external certificate frontiers** in v17.

1. **Historical seven-point Arb/FLINT certificate.**
   `ArchivedSevenPointClaim` names the exact mathematical proposition supported
   by the frozen 256-bit branch-and-bound run. Its trust base includes the
   frozen verifier, `python-flint`, FLINT/Arb, the recorded environment, and the
   correctness of directed interval arithmetic in those libraries.

2. **Signed limiting-kernel certificate at `g = 0.89`.**
   `V17KernelSignedCertPointClaim` names the rigorous numerical enclosure
   produced by `certification/v17/verify_improved_bound.py`. This verifier uses
   Python standard-library integer/rational arithmetic; transcendental values
   are bounded by explicit rational series/enclosures.

Neither external execution is silently promoted to a Lean theorem or declared
as an axiom. Instead, the final Lean theorem takes the two propositions above as
explicit arguments and kernel-checks the complete mathematical implication
from them to the published v17 bound.

Accordingly, the statement

> **the v17 Lean closure is end-to-end kernel-checked**

means that the implication from the two named external certificate propositions
to the final epsilon theorem is formally checked on top of pinned Mathlib and
Anthropic `formal-math/zeta23`. It does **not** mean that the Arb/FLINT
execution or the Python transcendental enclosure has itself been reimplemented
inside the Lean kernel, nor that the full analytic library was re-formalized
from scratch in this repository.

The archived 128-bit and 256-bit Arb executions are replications of the same
verification algorithm at different working precisions; they should not be
interpreted as algorithmically independent proof implementations.

---

## Relation to previous work

The manuscript distinguishes the present contribution from the immediately
preceding reproducible artifacts.

The upstream work of **[Sunghyeon Jo (`ainta`)](https://github.com/ainta/zeta-simple-zeros)** introduced the relevant reproducible
seven-point stability framework with uniform pressure and certified

$$
\frac{19}{5000}=0.0038,
$$

leading to the bound

$$
0.6730085279277797\ldots.
$$

A subsequent reproducible refinement by **[Lea Rademacher](https://github.com/learademacher/ai-refines-ai-zeta-bound)** strengthened
the uniform seven-point certificate to

$$
\frac{191}{50000}=0.00382,
$$

leading to the bound

$$
0.6730213619501665\ldots.
$$

The present work keeps the same total pressure

$$
\sum_jp_j=\frac1{500},
$$

but allows its distribution among the six gap positions to vary. The certified
nonuniform vector raises the local value to

$$
\frac{39}{10000}=0.0039.
$$

The v17 shifted-block and adjacent-pair argument then raises the resulting
global lower bound to

$$
0.6731175265883904388095857434\ldots.
$$

The precise mathematical and bibliographic comparison is given in the
manuscript.

---

## AI provenance

Recent upstream computational artifacts relevant to this project report the use
of AI systems during their development.

The present repository treats AI use as **research provenance rather than
mathematical authorship**.

All mathematical claims in the manuscript are intended to be supported by
explicit arguments, cited external results, reproducible computational
certificates, or kernel-checked formal proofs. The computer-assisted components
are accompanied by source code, execution records, cryptographic hashes,
machine-readable parameters, and reproduction instructions so that they can be
independently inspected.

---

## Citation

If you use the mathematical result, please cite the accompanying manuscript.
If you use or reproduce the computational artifact, please also cite the
repository/release.

Citation metadata is provided in `CITATION.cff`.

The v17 revision is frozen in `v1.2.0-paper`. The preceding submission-ready
manuscript is frozen in `v1.1.0-paper`, and the historical computational
artifact is frozen in `v1.0.0-paper @ c57f53e`.

---

## License

Source code, including the certificate verifiers and reproduction scripts, is
released under the **MIT License** unless otherwise stated. See `LICENSE-CODE`.

The manuscript, documentation, certificate metadata, execution logs, and other
non-software material are released under **CC BY 4.0**. See
`LICENSE-CONTENT`.

Third-party software and dependencies retain their respective licenses.

---

## Author

**Michael Hurtado**

Repository: `https://github.com/MichaelMobius/simple_zeros_of_the_riemann_zeta_function`

---

## Status

- **Current manuscript:** v19 publication-hardened text; mathematical theorem v17
- **Repository auditability cleanup:** v20
- **Current frozen theorem release:** `v1.2.0-paper`
- **Historical Arb/FLINT certificate:** `verified=true`, 256 bits
- **Certified seven-point local bound:** `39/10000`
- **v17 signed kernel claim:** `171389/1000000 < k(89/100)`
- **Canonical browseable Lean closure:** 127 modules
- **Lean final assembly:** green against the exact pinned upstream closure
- **Lean explicit external numerical frontiers:** two
- **Resulting unconditional bound:**

$$
\boxed{0.6731175265883904388095857434\ldots}
$$
