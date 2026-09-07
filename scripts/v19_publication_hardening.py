from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TEX = ROOT / "paper" / "main.tex"
CERT = ROOT / "certification" / "arb_256" / "certify_nonuniform_3900_v1_1.py"
CERT_README = ROOT / "certification" / "arb_256" / "README.md"
AUDIT = ROOT / "docs" / "V19_PUBLICATION_HARDENING.md"


def replace_once(text: str, old: str, new: str, label: str) -> str:
    count = text.count(old)
    if count != 1:
        raise RuntimeError(f"{label}: expected exactly one occurrence, found {count}")
    return text.replace(old, new, 1)


def replace_count(text: str, old: str, new: str, expected: int, label: str) -> str:
    count = text.count(old)
    if count != expected:
        raise RuntimeError(f"{label}: expected {expected} occurrences, found {count}")
    return text.replace(old, new)


tex = TEX.read_text(encoding="utf-8")

tex = replace_once(
    tex,
    "Their Theorem~D is the\nMontgomery--Taylor optimized specialization of that framework; in the present\nnormalization its simple-zero constant is the number denoted below by\n\\(H_{\\rm MT}\\).",
    "The Montgomery--Taylor clause of their Theorem~A gives the optimized\nsimple-zero constant denoted below by \\(H_{\\rm MT}\\).  The companion\nAnthropic Lean artifact retains the historical label \"Theorem D\" for the\ncorresponding Montgomery--Taylor constant and formal theorem family\n\\cite{AnthropicFormal26}.",
    "correct Theorem A / formal Theorem D provenance",
)

tex = replace_count(
    tex,
    "Theorem~D of Alpöge--Furman~\\cite{AlpogeFurman26}",
    "the Montgomery--Taylor clause of Theorem~A of Alpöge--Furman~\\cite{AlpogeFurman26}",
    2,
    "replace paper-Theorem-D references",
)

tex = replace_once(
    tex,
    "That theorem\nis the Montgomery--Taylor optimized specialization of the unconditional\nfinite-compression/rank--trace framework discovered by Claude and verified and\ncommunicated by Alpöge and Furman~\\cite{AlpogeFurman26,Anthropic26}.  Its role\nhere is comparison, provenance, and normalization cross-checking only; no\nproposition from that paper is a premise of Theorem~\\ref{thm:main}.",
    "That clause belongs to the unconditional finite-compression/rank--trace\nframework discovered by Claude and verified and communicated by Alpöge and\nFurman~\\cite{AlpogeFurman26,Anthropic26}.  In Anthropic's companion Lean\nartifact, the corresponding optimized result is organized under the historical\nlabel Theorem~D~\\cite{AnthropicFormal26}.  Its role here is comparison,\nprovenance, and normalization cross-checking only; no theorem from the\nAlpöge--Furman paper is a premise of Theorem~\\ref{thm:main}.",
    "clarify trust-section theorem labels",
)

tex = replace_once(
    tex,
    "The following stability refinement is",
    "The following stability refinement is",
    "stability anchor sanity",
) if "The following stability refinement is" in tex else tex

stable_anchor = "Define the convex function\n\\begin{equation}\\label{eq:Psi}"
stable_insert = (
    "The stability-enhanced rank--trace inequality used next is due to\n"
    "Jo~\\cite{Jo26}; we include the proof to fix the normalization and the\n"
    "precise defect functional used in the present argument.\n\n"
    "Define the convex function\n\\begin{equation}\\label{eq:Psi}"
)
tex = replace_once(tex, stable_anchor, stable_insert, "attribute stability lemma to Jo")

for roman in ("I", "II", "III", "IV"):
    tex = replace_count(
        tex,
        f"Independent proof of Input {roman}",
        f"Self-contained derivation of Input {roman}",
        1,
        f"rename appendix Input {roman}",
    )
    tex = replace_count(
        tex,
        f"[Independent Input {roman}]",
        f"[Self-contained Input {roman}]",
        1,
        f"rename theorem Input {roman}",
    )

input3_anchor = (
    "This appendix fixes the Fourier normalization of Weil's explicit formula~\\cite{Weil52,Titchmarsh86},\n"
    "derives the spectral density, controls integrated finite-grid end effects,\n"
    "and evaluates the prime diagonal and both off-diagonal frequency types.\n"
    "The weighted Montgomery--Vaughan inequality~\\cite{MV74} is used only with an unspecified\n"
    "absolute constant."
)
input3_new = input3_anchor + (
    "\nThe route is deliberately written out from these classical ingredients.  Its\n"
    "prime-side architecture parallels Section~5 of Alpöge--Furman\n"
    "~\\cite{AlpogeFurman26}---continuous second moment, diagonal prime term,\n"
    "quotient-frequency off-diagonal terms controlled by Montgomery--Vaughan,\n"
    "and secondary terms---but no theorem from that paper is invoked as a\n"
    "premise here.  Thus \"self-contained\" in this appendix is a statement\n"
    "about logical derivation from the cited classical inputs, not a claim of\n"
    "independent discovery of the base analytic architecture."
)
tex = replace_once(tex, input3_anchor, input3_new, "clarify Input III provenance")

cert_anchor = (
    "The frozen 256-bit run reports \\texttt{verified=true}, with $1{,}119{,}372$\n"
    "visited nodes, $559{,}038$ splits, and maximum depth $39$."
)
cert_insert = (
    "The search over the unbounded orthant has an explicit fail-closed pressure\n"
    "cutoff.  The implementation uses cell index $57{,}480$ on the mesh\n"
    "$1/4000$.  Since the smallest pressure coefficient is $2714/10^7$,\n"
    "\\[\n"
    " \\frac{2714}{10^7}\\frac{57480}{4000}\n"
    " =\\frac{1950009}{500000000}\n"
    " =\\frac{39}{10000}+\\frac{9}{500000000}\n"
    " >\\frac{39}{10000},\n"
    "\\]\n"
    "any box with at least one coordinate beyond that cutoff is certified by\n"
    "the pressure term alone.  The verifier now checks this exact rational\n"
    "identity before constructing the finite branch-and-bound search and aborts\n"
    "if it fails.\n\n"
) + cert_anchor
tex = replace_once(tex, cert_anchor, cert_insert, "document unbounded-domain cutoff")

block_decl_old = (
    "Let \\(B\\) be a block of\n"
    "\\[\n m=450\n\\]\n"
    "consecutive retained simple zeros, with exact pressure \\(P_B\\) from\n"
    "\\eqref{eq:qr}.  Put"
)
block_decl_new = (
    "Let \\(B\\) be a block of\n"
    "\\[\n m=450\n\\]\n"
    "consecutive retained simple zeros, with exact pressure \\(P_B\\) from\n"
    "\\eqref{eq:qr}.  Let \\(G_B\\) denote the corresponding principal Gram\n"
    "block of \\(M^\\circ\\).  Put"
)
tex = replace_once(tex, block_decl_old, block_decl_new, "define G_B explicitly")

uniform_old = (
    "Thus all pair separations remain in a fixed compact interval.  Since \\(m\\) is\n"
    "fixed, Lemma~\\ref{lem:kernel} gives, uniformly in this branch,\n"
    "\\[\n G_B=K_B+o(1)\n\\]\n"
    "in matrix norm, where\n"
    "\\[\n K_B=(k(y_i-y_j))_{i,j=1}^m.\n\\]\n"
    "By continuity of the spectral trace functional,\n"
    "\\[\n \\mathcal D(G_B)=\\mathcal D(K_B)+o(1).\n\\]\n"
    "It remains to prove"
)
uniform_new = (
    "Thus all pair separations remain in the fixed compact interval\n"
    "\\[\n"
    " 0\\le |y_i-y_j|\\le R:=\\frac{A}{\\min_jp_j}.\n"
    "\\]\n"
    "Make the uniform error explicit by setting\n"
    "\\[\n"
    " \\eta_T(R):=\n"
    " \\sup_{\\substack{\\rho,\\rho'\\in\\mathcal S^\\circ\\\\\n"
    " |x_\\rho-x_{\\rho'}|\\le R}}\n"
    " \\left|\\langle v_\\rho,v_{\\rho'}\\rangle\n"
    "       -k(x_\\rho-x_{\\rho'})\\right|.\n"
    "\\]\n"
    "Lemma~\\ref{lem:kernel} gives \\(\\eta_T(R)\\to0\\).  Since \\(m\\) is\n"
    "fixed and\n"
    "\\[\n K_B=(k(y_i-y_j))_{i,j=1}^m,\n\\]\n"
    "the entrywise bound implies\n"
    "\\[\n"
    " \\|G_B-K_B\\|_{\\rm op}\\le m\\eta_T(R).\n"
    "\\]\n"
    "The function \\(\\Psi\\) is globally $2$-Lipschitz on $[0,\\infty)$;\n"
    "therefore Weyl's eigenvalue perturbation inequality gives the quantitative\n"
    "uniform estimate\n"
    "\\begin{equation}\\label{eq:block-defect-uniform-error}\n"
    " \\left|\\mathcal D(G_B)-\\mathcal D(K_B)\\right|\n"
    " \\le 2m\\|G_B-K_B\\|_{\\rm op}\n"
    " \\le 2m^2\\eta_T(R)=o(1).\n"
    "\\end{equation}\n"
    "In particular, the $o(1)$ is uniform over every block in the branch\n"
    "\\(P_B<A\\).  It remains to prove"
)
tex = replace_once(tex, uniform_old, uniform_new, "quantify block approximation error")

shift_old = (
    "Summing over all offsets and applying Proposition~\\ref{prop:blockstab450},\n"
    "\\begin{equation}\\label{eq:shifted-exact}\n"
    " m\\mathcal D(M^\\circ)\n"
    " \\ge\n"
    " (S^\\circ-m+1)A\n"
    " -\\sum_BP_B\n"
    " -o(N).\n"
    "\\end{equation}"
)
shift_new = (
    "Summing over all offsets and applying Proposition~\\ref{prop:blockstab450},\n"
    "\\begin{equation}\\label{eq:shifted-exact}\n"
    " m\\mathcal D(M^\\circ)\n"
    " \\ge\n"
    " (S^\\circ-m+1)A\n"
    " -\\sum_BP_B\n"
    " -o(N).\n"
    "\\end{equation}\n"
    "Here the accumulated error is genuinely $o(N)$ rather than merely a\n"
    "blockwise notation: across all $m$ offsets there are $O(N)$ full blocks,\n"
    "and \\eqref{eq:block-defect-uniform-error} bounds the error of each relevant\n"
    "block by $2m^2\\eta_T(R)$ with the same \\(\\eta_T(R)\\to0\\).  Hence the\n"
    "total contribution is $O(N\\eta_T(R))=o(N)$; endpoint blocks contribute\n"
    "only $O(1)$ because $m$ is fixed."
)
tex = replace_once(tex, shift_old, shift_new, "justify blockwise o(1) to global o(N)")

span_old = (
    "Hence\n"
    "\\begin{equation}\\label{eq:pressure-global}\n"
    " \\sum_BP_B\n"
    " \\le\n"
    " Q(x_{S^\\circ}-x_1)\n"
    " \\le\n"
    " QN(T,2T)+o(N(T,2T)),\n"
    "\\end{equation}\n"
    "where the last inequality is the same normalized-span consequence of the\n"
    "Riemann--von Mangoldt formula used previously."
)
span_new = (
    "The span estimate can be made explicit.  Because the retained coordinates\n"
    "lie in the sampling interval,\n"
    "\\[\n"
    " x_{S^\\circ}-x_1\\le\\frac{LT}{2\\pi}.\n"
    "\\]\n"
    "On the other hand Riemann--von Mangoldt gives\n"
    "\\[\n"
    " N(T,2T)=\\frac{T}{2\\pi}\n"
    " \\bigl(L+2\\log2-1\\bigr)+O(\\log T),\n"
    "\\]\n"
    "and $2\\log2-1>0$.  Thus, for all sufficiently large $T$,\n"
    "\\(x_{S^\\circ}-x_1\\le N(T,2T)\\), and therefore\n"
    "\\begin{equation}\\label{eq:pressure-global}\n"
    " \\sum_BP_B\n"
    " \\le Q(x_{S^\\circ}-x_1)\n"
    " \\le QN(T,2T).\n"
    "\\end{equation}"
)
tex = replace_once(tex, span_old, span_new, "make normalized span bound explicit")

TEX.write_text(tex, encoding="utf-8")

cert = CERT.read_text(encoding="utf-8")
const_anchor = (
    "PRESSURE_CUTOFF_CELLS = 57_480\n\n"
    "# c_s = 2/(7-s), where s is the number of gaps crossed by a pair."
)
const_new = (
    "PRESSURE_CUTOFF_CELLS = 57_480\n\n"
    "TARGET_RATIONAL = fmpq(TARGET_NUMERATOR, TARGET_DENOMINATOR)\n"
    "PRESSURE_CUTOFF_LOWER = fmpq(\n"
    "    min(PRESSURE_NUMERATORS) * PRESSURE_CUTOFF_CELLS,\n"
    "    GRID * PRESSURE_DENOMINATOR,\n"
    ")\n"
    "PRESSURE_CUTOFF_MARGIN = PRESSURE_CUTOFF_LOWER - TARGET_RATIONAL\n\n"
    "def certify_pressure_cutoff() -> fmpq:\n"
    "    \"\"\"Fail closed unless the pressure alone covers the unbounded tail.\"\"\"\n"
    "    expected_margin = fmpq(9, 500_000_000)\n"
    "    assert PRESSURE_CUTOFF_MARGIN == expected_margin\n"
    "    assert PRESSURE_CUTOFF_LOWER > TARGET_RATIONAL\n"
    "    return PRESSURE_CUTOFF_MARGIN\n\n"
    "# c_s = 2/(7-s), where s is the number of gaps crossed by a pair."
)
cert = replace_once(cert, const_anchor, const_new, "add exact pressure cutoff check")

verify_anchor = (
    "    started = time.perf_counter()\n"
    "    cell_count = PRESSURE_CUTOFF_CELLS + 8"
)
verify_new = (
    "    started = time.perf_counter()\n"
    "    cutoff_margin = certify_pressure_cutoff()\n"
    "    cell_count = PRESSURE_CUTOFF_CELLS + 8"
)
cert = replace_once(cert, verify_anchor, verify_new, "invoke cutoff check")

report_anchor = (
    '            "pressure_numerators": str(PRESSURE_NUMERATORS),\n'
    '            "pressure_denominator": PRESSURE_DENOMINATOR,\n'
)
report_new = (
    '            "pressure_numerators": str(PRESSURE_NUMERATORS),\n'
    '            "pressure_denominator": PRESSURE_DENOMINATOR,\n'
    '            "pressure_cutoff_cells": PRESSURE_CUTOFF_CELLS,\n'
    '            "pressure_cutoff_lower": str(PRESSURE_CUTOFF_LOWER),\n'
    '            "pressure_cutoff_margin": str(cutoff_margin),\n'
)
cert = replace_once(cert, report_anchor, report_new, "report cutoff metadata")

cli_old = (
    '    parser.add_argument("--precision", type=int, default=PRECISION_BITS,\n'
    '                        help="Arb working precision in bits (default: 256)")\n'
    '    args=parser.parse_args()\n'
    '    report=verify_seven(progress_every=args.progress_every, precision_bits=args.precision)\n'
    '    print(report.to_text())'
)
cli_new = (
    '    parser.add_argument("--precision", type=int, default=PRECISION_BITS,\n'
    '                        help="Arb working precision in bits (default: 256)")\n'
    '    parser.add_argument("--check-cutoff-only", action="store_true",\n'
    '                        help="verify only the exact unbounded-domain pressure cutoff")\n'
    '    args=parser.parse_args()\n'
    '    if args.check_cutoff_only:\n'
    '        margin = certify_pressure_cutoff()\n'
    '        print(f"pressure_cutoff_verified=true\\npressure_cutoff_margin={margin}")\n'
    '    else:\n'
    '        report=verify_seven(progress_every=args.progress_every, precision_bits=args.precision)\n'
    '        print(report.to_text())'
)
cert = replace_once(cert, cli_old, cli_new, "add cutoff-only CLI")
CERT.write_text(cert, encoding="utf-8")

readme = CERT_README.read_text(encoding="utf-8")
cutoff_section = r'''

## Unbounded-domain cutoff

The branch-and-bound search itself is finite, but the certified statement is
for all nonnegative gaps.  This reduction is fail-closed in the verifier.  The
smallest pressure coefficient is `2714/10^7`, the mesh is `1/4000`, and the
cutoff index is `57480`, so exactly

\[
\frac{2714}{10^7}\frac{57480}{4000}
=\frac{39}{10000}+\frac{9}{500000000}
>\frac{39}{10000}.
\]

Therefore, if any coordinate lies beyond the cutoff, its pressure contribution
alone proves the target.  `certify_pressure_cutoff()` checks the exact rational
margin before the search tree is created.  A cheap standalone audit is

```bash
python certify_nonuniform_3900_v1_1.py --check-cutoff-only
```

and must print `pressure_cutoff_verified=true`.
'''
if "## Unbounded-domain cutoff" not in readme:
    readme = readme.rstrip() + cutoff_section + "\n"
else:
    raise RuntimeError("cutoff README section already exists")
CERT_README.write_text(readme, encoding="utf-8")

AUDIT.write_text(r'''# v19 publication hardening

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
''', encoding="utf-8")

print("v19 publication hardening patch applied")
