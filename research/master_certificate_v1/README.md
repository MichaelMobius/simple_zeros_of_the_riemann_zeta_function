# Master-certificate experiment v1

This directory records a **research experiment**, not a theorem of the paper.
It combines the pinned nine-point local certificate of
`trmdy/zeta-simple-zeros-673137` with the adjacent-pair defect and
spectral-threshold mechanism of the current Hurtado manuscript.

Pinned upstream commit:

`trmdy/zeta-simple-zeros-673137@1610b97b7895ff34982260f8dcaf04a0f7b82cf7`.

## Pinned local data

For the upstream window, with `w=k_v^2`, the nine-point certificate has

```text
q       = 8
p       = 1/2500
epsilon = 15211/2500000
beta    = q p = 2/625
H_cert  = 3362285207/5000000000
```

and all eight exact span capacities are `2`.  Summing it through an
`m`-point block gives

\[
E+P\ge A:=\epsilon(m-8),\qquad
\sum_rq_r=Q:=\beta(m-8),\qquad0\le q_r\le\beta.
\]

The Hurtado adjacent-pair argument supplies

\[
D\ge\sum_r w(g_r),
\]

and, if

\[
w(g)+tqg\ge tqg_0,
\]

then

\[
D+tP\ge tg_0Q.
\]

Together with the spectral threshold

\[
D<E\Longrightarrow D>\frac{m}{m-1},
\]

one obtains `D+P>=A` whenever

\[
g_0Q+\left(1-\frac1t\right)\frac{m}{m-1}-A>0.
\]

## Robust rational operating point

We use

\[
g_0=\frac{43}{50},\qquad t=\frac{31}{2},\qquad m=289.
\]

Then

\[
A=\frac{4274291}{2500000},\qquad Q=\frac{562}{625},
\]

and the exact block contradiction margin is

\[
g_0Q+\left(1-\frac1t\right)\frac{289}{288}-A
=\frac{405889}{174375000}>0.
\]

The scalar kernel condition reduces to

\[
k_v\!\left(\frac{43}{50}\right)>\frac{521}{2500},
\]

because

\[
\left(\frac{521}{2500}\right)^2-
\frac{1333}{31250}=\frac{4841}{6250000}>0.
\]

## Signed-kernel and integral-bridge status

The exact-rational reproduction `verify_window_kernel_086.py` proves

\[
k_v(43/50)\in
[0.208459268877159404,0.208459354615668058],
\]

hence in particular `k_v(43/50)>521/2500`.

`lean_harness/research/ResearchWindowKernel086v2.lean` proves in Lean the
corresponding strict inequality for the exact closed form.  Its axiom report
is the standard Lean/Mathlib set

```text
propext, Classical.choice, Quot.sound
```

The integral bridge has also advanced beyond a purely numerical identity.
`ResearchWindowKernelBridge.lean` now kernel-checks the exact cosine-overlap
formula

\[
\int_{-1/2}^{1/2}\cos(as)\cos(bs)\,ds
=
\frac{\sin((a-b)/2)}{a-b}
+
\frac{\sin((a+b)/2)}{a+b},
\]

as well as the one-frequency normalization and the vanishing of every
nonzero integer Fourier mode.  The next substep is to finish the Lean theorem
identifying the normalization integral of the actual pinned seven-term window
with the closed normalization used above, then do the analogous numerator
identity at `x=43/50`.

## Nine-point certificate replay

The upstream certificate consists of 96 disjoint rigorous shards and reports
116,272,426 search nodes in total.  Before attempting the entire replay we ran
an independent pinned pilot on shard `0/96`.  It completed successfully in CI
run `35943514827` with

```text
verified        = True
nodes           = 658969
pruned          = 329486
splits          = 329483
maximum_depth   = 45
elapsed_seconds = 723.233
```

and independently rebuilt the exact upstream interval tables with matching
SHA-256 hashes

```text
w   = 2be38c2f2a5a4659200341fae9b2a926760e64ad04fa44ae214a77dd958c56e3
w'' = 580e9682f1171ead19595438ee83c9f4c5af837179060ec49d9faee88032f6d5
```

To avoid rebuilding those expensive tables 96 times, the full replay is now
split into six jobs.  Each job builds the rigorous tables once and reuses them
for sixteen of the original 96 shards.  Workflow
`research-nine-point-replay-full.yml` therefore covers the complete certificate
without changing the upstream verifier or the original shard partition.
A full replay is not recorded as complete until all six jobs return `PASS`.

## Projected global constant

Once the pinned nine-point inequality and the analytic window interface are
independently discharged, the hybrid block theorem gives

\[
\frac SN\ge
\frac{289H_{\rm cert}-562/625}
     {289-4274291/2500000}
=
\boxed{\frac{967204424823}{1436451418000}}
\]

and hence

\[
\boxed{0.6733290194872431112041966740\ldots}.
\]

This is larger than the current Hurtado theorem
`0.6731175265883904...`, the upstream nine-point assembly
`0.6733127422722459...`, and the Shi two-certificate candidate
`0.6733169771424713...`.  It is **not yet a certified new zeta-zero bound**.

## Current proof ledger

- **Green in Lean:** exact block contradiction algebra.
- **Green in Lean:** exact final rational constant arithmetic.
- **Green exact-rational + Lean closed form:** signed kernel at `43/50`.
- **Green in Lean:** generic cosine-overlap integral bridge and integer-mode
  normalization identities.
- **Green replay pilot:** shard `0/96` of the pinned nine-point certificate.
- **In progress:** full grouped replay of all 96 certificate shards.
- **In progress:** actual-window normalization identity in Lean.
- **Open:** actual-window numerator identity at `x=43/50` and composition with
  the closed signed-kernel theorem.
- **Open:** package positivity/monotonicity of the upstream window needed by
  the scalar argument.
- **Open:** prove the upstream window satisfies the analytic hypotheses of
  Appendices III--IV without importing the upstream arbitrary-window
  interface as a black box.
- **Open:** compose the generalized block theorem through the literal
  `liminf` endpoint.

No result from this directory should be moved into `paper/main.tex` until the
open items above are closed.
