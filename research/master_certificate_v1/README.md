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

## Signed-kernel status

Two independent proof layers are now present.

1. `verify_window_kernel_086.py` uses exact Python `Fraction` arithmetic,
   directed rational bounds for `pi` and `1/sqrt(2)`, and alternating Taylor
   estimates.  It proves

   \[
   k_v(43/50)>0.2084592688771594\ldots>0.2084.
   \]

2. `lean_harness/research/ResearchWindowKernel086v2.lean` proves in Lean the
   strict inequality

   ```text
   521/2500 < research9v2WindowKernelClosed086
   ```

   for the exact closed-form evaluation of the same trigonometric profile.
   CI run `35808157599` completed successfully.  The axiom report for this
   theorem is exactly the standard Lean/Mathlib set

   ```text
   propext, Classical.choice, Quot.sound
   ```

The remaining kernel task is therefore no longer numerical.  It is the
formal **identity bridge** equating `research9v2WindowKernelClosed086` with
the integral definition of the normalized overlap kernel of the window.

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
- **Open:** prove the closed-form/integral kernel identity.
- **Open:** package positivity/monotonicity of the upstream window needed by
  the scalar argument.
- **Open:** reproduce or independently recertify the full nine-point local
  inequality.
- **Open:** prove the upstream window satisfies the analytic hypotheses of
  Appendices III--IV without importing the upstream arbitrary-window
  interface as a black box.
- **Open:** compose the generalized block theorem through the literal
  `liminf` endpoint.

No result from this directory should be moved into `paper/main.tex` until the
open items above are closed.
