from pathlib import Path
import re

PATH = Path("paper/main.tex")
text = PATH.read_text(encoding="utf-8")


def sub_once(pattern: str, repl: str, label: str, flags: int = 0) -> None:
    global text
    text2, n = re.subn(pattern, lambda _m: repl, text, count=1, flags=flags)
    if n != 1:
        raise SystemExit(f"{label}: expected exactly one match, found {n}")
    text = text2


def replace_once(old: str, new: str, label: str) -> None:
    global text
    n = text.count(old)
    if n != 1:
        raise SystemExit(f"{label}: expected exactly one match, found {n}")
    text = text.replace(old, new, 1)


replace_once(
    "% Manuscript version v17: pressure-preserving averaging and adjacent-pair refinement.",
    "% Manuscript version v18: v17 mathematics with adversarial provenance and trust-boundary revisions.",
    "version header",
)

replace_once(
    "The complete implication from\n"
    "the archived seven-point certificate and this signed scalar claim to the final\n"
    "epsilon theorem is kernel-checked in Lean.",
    "The complete implication from\n"
    "the archived seven-point certificate and this signed scalar claim to the final\n"
    "epsilon theorem is kernel-checked in Lean.  The written mathematical derivation\n"
    "below does not invoke the recent Alpöge--Furman theorem as a premise; the\n"
    "software provenance of the Lean verification is stated separately in\n"
    "Section~\\ref{sec:trust}.",
    "abstract provenance",
)

sub_once(
    r"Recent work has made the relevant finite-compression and zero-side inertia.*?"
    r"\\begin\{equation\}\\label\{eq:HMT\}.*?\\end\{equation\}",
    r"""Recent work has made the relevant finite-compression and zero-side inertia
mechanism unconditional.  Alpöge and Furman~\cite{AlpogeFurman26}, communicating
a proof discovered autonomously by Claude at Anthropic as recorded both by the
authors and by Anthropic~\cite{Anthropic26}, establish the finite-compression,
rank--trace, and inertia route unconditionally.  Their Theorem~D is the
Montgomery--Taylor optimized specialization of that framework; in the present
normalization its simple-zero constant is the number denoted below by
\(H_{\rm MT}\).  Lamzouri~\cite{Lamzouri26} subsequently gave a conceptually
different unconditional proof of the same \(67.25\%\)-level conclusion.
For surrounding pair-correlation work see
Baluyot--Goldston--Suriajaya--Turnage-Butterbaugh~\cite{BGSTB24,BGSTB25} and
Goldston--Suriajaya~\cite{GS25,GS26}.
For the optimized Montgomery--Taylor test family we write
\begin{equation}\label{eq:HMT}
 H_{\rm MT}:=\frac32-\frac1{\sqrt2}\cot\frac1{\sqrt2}
 =0.6725007036794116457\ldots .
\end{equation}""",
    "canonical recent-work attribution",
    re.S,
)

sub_once(
    r"The contribution of the present paper is explicit and layered\..*?"
    r"for which the seven-point functional satisfies",
    r"""The contribution of the present paper is explicit and layered.  We do not
claim the finite-compression/rank--trace mechanism, the stability-enhanced
rank--trace inequality, or the seven-point architecture as new.  The
position-weighted seven-point certificate itself is an earlier contribution of
the present project, frozen in the reproducibility artifact
\cite{Hurtado26Artifact}; that version already introduced the nonuniform
pressure vector
\begin{equation}\label{eq:p}
 p=\frac1{10^7}(2714,3733,3553,3553,3733,2714),
 \qquad
 \beta:=\sum_{j=1}^6p_j=\frac1{500},
\end{equation}
for which the seven-point functional satisfies""",
    "earlier Hurtado certificate provenance",
    re.S,
)

sub_once(
    r"A second contribution is expository and logical rather than a separate.*?"
    r"recent Theorem D as an imported black box\.",
    r"""A second contribution is expository and logical rather than a separate
priority claim: we reconstruct the analytic/Gabor package needed by the proof
from classical theorems and explicitly identify the common finite compression
on its zero and prime sides.  Consequently, Theorem~\ref{thm:main} does not
invoke Theorem~D of Alpöge--Furman~\cite{AlpogeFurman26}, or any other theorem
of that paper, as a mathematical premise.  This is a statement about the
logical derivation presented in the manuscript, not a claim of clean-room
software independence: the Lean verification has the distinct provenance
recorded in Section~\ref{sec:trust}.""",
    "Theorem D independence clarification",
    re.S,
)

sub_once(
    r"\\paragraph\{Priority convention\.\}.*?"
    r"itself is inherited unchanged from the frozen artifact\.",
    r"""\paragraph{Priority and provenance convention.}
The priority statements above concern the public artifacts inspected while
preparing this version.  The proof discovered by Claude and verified and
communicated by Alpöge--Furman supplies the immediate unconditional
finite-compression/rank--trace comparison point~\cite{AlpogeFurman26,Anthropic26}.
Jo's repository is the public upstream artifact for the stability-enhanced
seven-point draft used here; Rademacher's repository records that provenance
and strengthens its uniform finite certificate.  The position-weighted
seven-point certificate \eqref{eq:p}--\eqref{eq:local-cert-intro} is frozen in
our earlier artifact~\cite{Hurtado26Artifact}.  The new claims of the present
version are restricted to the exact pressure-preserving global accounting, the
adjacent-pair defect lemma, the scalar kernel enclosure used with that lemma,
and the resulting constant.  The seven-point branch-and-bound certificate is
reused unchanged.

\begin{center}
\small
\begin{tabular}{@{}p{0.43\linewidth}p{0.50\linewidth}@{}}
\toprule
Component & Provenance used in this paper\\
\midrule
Classical analytic inputs & Weil explicit formula, Montgomery--Taylor optimization,
Riemann--von Mangoldt, PNT, Poisson summation, Montgomery--Vaughan and standard
matrix analysis\\
Finite compression, zero-side inertia and rank--trace route & Proof discovered by
Claude (Anthropic), verified and communicated by Alpöge--Furman
\cite{AlpogeFurman26,Anthropic26}; not imported as a premise of
Theorem~\ref{thm:main}\\
Stability-enhanced rank--trace and seven-point architecture & Jo~\cite{Jo26}\\
Uniform seven-point strengthening & Rademacher~\cite{Rademacher26}\\
Position-weighted seven-point certificate \(39/10000\) & Hurtado, earlier frozen
artifact~\cite{Hurtado26Artifact}\\
Exact pressure preservation, adjacent-pair pinching, scalar enclosure and
\(m=450\) assembly & Present paper\\
Lean base library & Anthropic \texttt{formal-math/zeta23}, pinned commit recorded
in Section~\ref{sec:trust}~\cite{AnthropicFormal26}\\
Lean v17 refinement layer & \texttt{HurtadoZeta23} modules in the present
repository\\
\bottomrule
\end{tabular}
\end{center}""",
    "priority/provenance table",
    re.S,
)

replace_once(
    "Von Neumann's trace inequality then implies",
    "Von Neumann's trace inequality~\\cite{Bhatia97} then implies",
    "von Neumann citation",
)

sub_once(
    r"Pinching \$M\$ to the\s+retained central principal block and its complement does not increase\s+"
    r"\$\\tr\\Psi\$: pinching is a random-unitary average, and the spectral trace\s+"
    r"functional \$X\\mapsto\\tr\\Psi\(X\)\$ is convex and unitarily invariant\.\s+No\s+"
    r"operator convexity of \$\\Psi\$ is required\.",
    r"""Pinching $M$ to the
retained central principal block and its complement does not increase
$\tr\Psi$: by the standard pinching/majorization principle for Hermitian
matrices~\cite{Bhatia97}, pinching is a random-unitary average and the spectral
trace functional $X\mapsto\tr\Psi(X)$ is convex and unitarily invariant.
No operator convexity of $\Psi$ is required.""",
    "global pinching citation",
    re.S,
)

sub_once(
    r"The spectral trace functional \$X\\mapsto\\operatorname\{tr\}\\Psi\(X\)\$ cannot\s+"
    r"increase under either pinching, since pinching is a random-unitary average\s+"
    r"and this trace functional is convex and unitarily invariant\.",
    r"""The spectral trace functional $X\mapsto\operatorname{tr}\Psi(X)$ cannot
increase under either pinching by the standard pinching/majorization
principle~\cite{Bhatia97}: pinching is a random-unitary average and this trace
functional is convex and unitarily invariant.""",
    "adjacent pinching citation",
    re.S,
)

replace_once(
    "The complete 256-bit\nartifact is publicly archived in the immutable release\n\\cite{Hurtado26Artifact}.  Appendix~\\ref{app:cert} records the hashes and\nenvironment.",
    "The complete 256-bit\nartifact is publicly archived in the frozen release snapshot\n\\cite{Hurtado26Artifact}, identified by its release tag, commit SHA, and\ncryptographic hashes.  Appendix~\\ref{app:cert} records the hashes and\nenvironment.",
    "immutable release wording in certificate proof",
)

sub_once(
    r"\\noindent\\textbf\{Logical status of the theorem\.\}.*?"
    r"Appendix~\\ref\{app:inputIII\}\.",
    r"""\noindent\textbf{Logical status of the theorem and relation to the
Alpöge--Furman/Claude result.}
The common compression is fixed in Section~\ref{sec:common-compression}, and
the analytic/Gabor package used in the main argument is proved in
Appendices~\ref{app:inputI}--\ref{app:inputIV}.  In particular it is not
imported from Theorem~D of Alpöge--Furman~\cite{AlpogeFurman26}.  That theorem
is the Montgomery--Taylor optimized specialization of the unconditional
finite-compression/rank--trace framework discovered by Claude and verified and
communicated by Alpöge and Furman~\cite{AlpogeFurman26,Anthropic26}.  Its role
here is comparison, provenance, and normalization cross-checking only; no
proposition from that paper is a premise of Theorem~\ref{thm:main}.

The analytic external trust base consists of standard classical results: the
Weil explicit formula for $\zeta$ in the Fourier normalization stated in
Appendix~\ref{app:inputIII}, Stirling's formula, the Prime Number Theorem, the
Riemann--von Mangoldt formula and its standard local zero-count consequence,
standard Chebyshev and prime-power estimates, the weighted
Montgomery--Vaughan Hilbert inequality, Poisson summation, and standard
finite-dimensional matrix facts such as von Neumann's trace inequality and the
pinching/majorization principle~\cite{Bhatia97}.  The Montgomery--Vaughan paper
is correctly cited as \emph{Hilbert's inequality}, J. London Math. Soc. (2)
\textbf{8} (1974), 73--82.  The recent pair-correlation papers cited in the
introduction provide context; the particular first/second-moment route used
here is reconstructed directly in Appendix~\ref{app:inputIII}.""",
    "scope logical status",
    re.S,
)

replace_once(
    "Proposition~\\ref{prop:cert} is computer-assisted.  Its trust base includes the\nimmutable artifact release~\\cite{Hurtado26Artifact}, the frozen verifier,",
    "Proposition~\\ref{prop:cert} is computer-assisted.  Its trust base includes the\nfrozen artifact release snapshot~\\cite{Hurtado26Artifact}, the frozen verifier,",
    "immutable trust wording",
)

sub_once(
    r"The v17 formalization has a separate, explicit trust boundary\..*?"
    r"arguments of the final theorem\.",
    r"""The v17 formalization has a separate, explicit trust boundary and a distinct
software provenance.  The Lean root
\texttt{HurtadoZeta23.V17FinalAssembly} kernel-checks the implication from
exactly two \emph{explicit external certificate propositions}---the archived
seven-point claim and the signed kernel claim above---to the published
epsilon-form theorem
\texttt{v17\_published\_eps\_form\_of\_certificates}.  The universal scalar
pressure inequality, including the required kernel monotonicity, is proved
inside Lean.  The external computations are not promoted silently to Lean
proof terms or declared as axioms; their propositions remain explicit
arguments of the final theorem.

The phrase ``exactly two'' refers to the explicit mathematical certificate
arguments of that final theorem, not to the entire software or foundational
stack.  The v17 \texttt{HurtadoZeta23} modules are compiled as an overlay on
the pinned Anthropic \texttt{formal-math/zeta23} source tree at commit
\texttt{fbdc36bbf17d20af3fd0447c6d1a8a02773c9844}~\cite{AnthropicFormal26},
together with the pinned Lean/Mathlib toolchain recorded in the repository.
Thus the manuscript's independence from Theorem~D as a mathematical premise
must not be conflated with clean-room software independence of the Lean
formalization.""",
    "Lean software provenance",
    re.S,
)

replace_once(
    "Thus the paper is self-contained relative to the\nclassical analytic results just listed and to the stated Arb/FLINT\ncertificate; it does not claim to reprove those classical theorems from first\nprinciples.",
    "Thus the written mathematical proof is self-contained relative to the\nclassical analytic and matrix results just listed and to the stated Arb/FLINT\ncertificate; it does not claim to reprove those classical theorems from first\nprinciples.  The separate Lean verification should be read with the software\nprovenance in the preceding paragraph.",
    "self-contained qualifier",
)

replace_once(
    "The immutable snapshot used for the present certificate is GitHub release\n\\texttt{v1.0.0-paper}, attached to commit \\texttt{c57f53e}.",
    "The frozen snapshot used for the present certificate is GitHub release\n\\texttt{v1.0.0-paper}, attached to commit \\texttt{c57f53e} and identified\nadditionally by the verifier and log SHA-256 values below.",
    "appendix immutable wording",
)

replace_once(
    "\\section{Comparison and structural interpretation}\n\nJo's upstream reproducible draft~\\cite{Jo26} uses",
    "\\section{Comparison and structural interpretation}\n\n"
    "At the baseline level, Alpöge--Furman~\\cite{AlpogeFurman26} and\n"
    "Lamzouri~\\cite{Lamzouri26} now provide different unconditional routes to the\n"
    "\\(67.25\\%\\)-level Montgomery--Taylor conclusion.  The present argument is not\n"
    "obtained by invoking either result: it reconstructs the analytic package used\n"
    "below and then adds the separate stability and local-pressure machinery whose\n"
    "provenance is summarized in the table in Section~\\ref{sec:introduction}.\n\n"
    "Jo's upstream reproducible draft~\\cite{Jo26} uses",
    "comparison baseline provenance",
)

sub_once(
    r"\\bibitem\{Claude26\}.*?preprint, August 10, 2026, Anthropic\.\n",
    r"""\bibitem{AlpogeFurman26}
L.~Alpöge and R.~Furman,
\emph{More than two thirds of the zeta zeros are simple and on the critical
line},
arXiv:2608.13637v2 (2026).
The arXiv record states that the proof was discovered autonomously by Claude
(Anthropic), and verified and communicated by the listed authors.

\bibitem{Anthropic26}
Anthropic,
\emph{Learning more about Claude's mathematical capabilities},
research note, 10 August 2026,
\url{https://www.anthropic.com/research/riemann-zeta}.

\bibitem{Lamzouri26}
Y.~Lamzouri,
\emph{A new proof that more than $2/3$ of the zeros of the Riemann zeta
function are simple and on the critical line},
arXiv:2609.02882 (2026).

\bibitem{Bhatia97}
R.~Bhatia,
\emph{Matrix Analysis},
Graduate Texts in Mathematics, Vol.~169, Springer, 1997.

\bibitem{AnthropicFormal26}
Anthropic,
\emph{formal-math: zeta23 Lean 4 formalisation},
GitHub repository \texttt{anthropics/formal-math},
pinned by the present verification at commit
\texttt{fbdc36bbf17d20af3fd0447c6d1a8a02773c9844} (2026).
""",
    "canonical bibliography",
    re.S,
)

for forbidden in [
    "\\cite{Claude26}",
    "immutable release",
    "immutable artifact release",
    "Theorem D as an imported black box",
]:
    if forbidden in text:
        raise SystemExit(f"forbidden stale wording remains: {forbidden}")

for required in [
    "\\cite{AlpogeFurman26}",
    "\\cite{Lamzouri26}",
    "\\cite{AnthropicFormal26}",
    "fbdc36bbf17d20af3fd0447c6d1a8a02773c9844",
    "clean-room software independence",
    "frozen release snapshot",
]:
    if required not in text:
        raise SystemExit(f"required revised wording missing: {required}")

PATH.write_text(text, encoding="utf-8")
print("v18 editorial/provenance patch applied successfully")
