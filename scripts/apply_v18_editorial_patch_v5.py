from pathlib import Path

path = Path("paper/main.tex")
text = path.read_text(encoding="utf-8")

old_adj = r'''\begin{proof}
Pinch \(K\) first into the principal \(2\times2\) blocks
\[
 (1,2),(3,4),\ldots
\]
and then into
\[
 (2,3),(4,5),\ldots .
\]
The spectral trace functional \(X\mapsto\operatorname{tr}\Psi(X)\) cannot
increase under either pinching by the standard pinching/majorization
principle~\cite{Bhatia97}: pinching is a random-unitary average and this trace
functional is convex and unitarily invariant.

The block associated with a consecutive gap \(g\) is
\[
 \begin{pmatrix}1&k(g)\\ \overline{k(g)}&1\end{pmatrix},
\]
whose eigenvalues are \(1\pm|k(g)|\in[0,2]\).  Its defect is therefore
exactly \(2|k(g)|^2=2w(g)\).  The first pinching gives
\[
 \mathcal D(K)\ge2\sum_{j\ {\rm odd}}w(g_j),
\]
and the second gives the corresponding inequality over even \(j\).  Averaging
the two inequalities proves \eqref{eq:adjacent-pair-defect}.
\end{proof}'''

new_adj = r'''\begin{proof}
Apply two separate pinchings to the original matrix \(K\).  The first uses the
principal \(2\times2\) blocks
\[
 (1,2),(3,4),\ldots,
\]
while the second, independently applied to the same original \(K\), uses
\[
 (2,3),(4,5),\ldots .
\]
For each of these two pinchings, the spectral trace functional
\(X\mapsto\operatorname{tr}\Psi(X)\) cannot increase by the standard
pinching/majorization principle~\cite{Bhatia97}: pinching is a random-unitary
average and this trace functional is convex and unitarily invariant.

The block associated with a consecutive gap \(g\) is
\[
 \begin{pmatrix}1&k(g)\\ \overline{k(g)}&1\end{pmatrix},
\]
whose eigenvalues are \(1\pm|k(g)|\in[0,2]\).  Its defect is therefore
exactly \(2|k(g)|^2=2w(g)\).  The first pinching gives
\[
 \mathcal D(K)\ge2\sum_{j\ {\rm odd}}w(g_j),
\]
while the second, as a separate inequality for the same \(K\), gives the
corresponding bound over even \(j\).  Averaging these two independently
obtained inequalities proves \eqref{eq:adjacent-pair-defect}.
\end{proof}'''

if old_adj not in text:
    raise SystemExit("Adjacent-pair proof block not found exactly")
text = text.replace(old_adj, new_adj, 1)

old_ojha = r'''\bibitem{Ojha26}
V.~Ojha,
\emph{Certified lower-bound candidate for simple zeros of the Riemann zeta
function},
research repository \texttt{trmdy/zeta-simple-zeros-673137}, 2026,
\url{https://github.com/trmdy/zeta-simple-zeros-673137}.'''

new_ojha = r'''\bibitem{Ojha26}
V.~Ojha,
\emph{A 67.3312742272\% lower-bound candidate for simple zeros of zeta},
research repository \texttt{trmdy/zeta-simple-zeros-673137}, 2026,
\url{https://github.com/trmdy/zeta-simple-zeros-673137}.'''

if old_ojha not in text:
    raise SystemExit("Ojha bibliography block not found exactly")
text = text.replace(old_ojha, new_ojha, 1)

path.write_text(text, encoding="utf-8")
print("Applied final v18 editorial corrections")
