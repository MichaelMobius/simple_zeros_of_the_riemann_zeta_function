# Master-certificate experiment v1

This directory records a **research experiment**, not a theorem of the paper.
It tests whether the exact nine-point certificate of `trmdy/zeta-simple-zeros-673137`
can be combined with the adjacent-pair defect mechanism already proved in the
current Hurtado manuscript.

Upstream nine-point data are pinned to

`trmdy/zeta-simple-zeros-673137@1610b97b7895ff34982260f8dcaf04a0f7b82cf7`.

The purpose of this experiment is deliberately narrow: keep the certified
nine-point local inequality and its admissible window, but replace its generic
finite-dimensional block assembly by the stronger adjacent-pair/spectral-threshold
argument of the present project.

## Imported local data

For the upstream admissible window, write `w=k_v^2`.  The pinned nine-point
certificate has

```text
q       = 8
p       = 1/2500
epsilon = 15211/2500000
beta    = q p = 2/625
H_cert  = 3362285207/5000000000
```

and exact span capacities equal to `2`.  Thus, after summing the local
nine-point inequality through an `m`-point block,

\[
E+P\ge A:=\epsilon(m-8),
\qquad
\sum_r q_r=Q:=\beta(m-8),
\qquad
0\le q_r\le\beta.
\]

Here `E` is the full pair energy and `P=\sum_r q_r g_r` is the exact block
pressure.

## Additional information from the Hurtado argument

For a positive-semidefinite unit-diagonal Gram block `K`, let

\[
D=\operatorname{tr}\Psi(K).
\]

The adjacent-pair pinching lemma gives

\[
D\ge\sum_r w(g_r).
\]

If numbers `g0,t` satisfy

\[
w(g)+tqg\ge tqg_0
\qquad(g\ge0,\ 0\le q\le\beta),
\]

then

\[
D+tP\ge t g_0 Q.
\]

The spectral-threshold lemma gives, whenever `D<E`,

\[
D>\frac{m}{m-1}.
\]

Therefore a contradiction to `D+P<A` follows as soon as

\[
 g_0Q+\left(1-\frac1t\right)\frac{m}{m-1}-A>0.
\]

This is exactly the same mechanism used in the current manuscript for the
seven-point Montgomery--Taylor certificate; only the local data are changed.

## A robust rational operating point

The first useful point found by the experiment is

\[
 g_0=\frac{43}{50}=0.86,
 \qquad
 t=\frac{31}{2}=15.5,
 \qquad
 m=289.
\]

For these values,

\[
 A=\frac{4274291}{2500000}=1.7097164,
 \qquad
 Q=\frac{562}{625}=0.8992,
\]

and the block contradiction margin is the exact positive rational

\[
 g_0Q+\left(1-\frac1t\right)\frac{289}{288}-A
 =\frac{405889}{174375000}
 =0.002327678853\ldots>0.
\]

The scalar kernel condition reduces to

\[
 w\!\left(\frac{43}{50}\right)
 > t\beta g_0
 =\frac{1333}{31250}
 =0.042656.
\]

It suffices to prove the signed estimate

\[
 k_v\!\left(\frac{43}{50}\right)>\frac{521}{2500}=0.2084,
\]

because

\[
 \left(\frac{521}{2500}\right)^2
 -\frac{1333}{31250}
 =0.00077456>0.
\]

The companion script `verify_window_kernel_086.py` now proves an
**exact-rational enclosure** of this signed kernel value.  It uses only
`fractions.Fraction`, the standard alternating Taylor bounds for sine and
cosine on `[0,1]`, the same decimal bounds for `pi` used in the existing Lean
proof, and an exact rational bracket for `1/sqrt(2)`.  Its resulting interval
has lower endpoint approximately

\[
 0.2084592688771594>0.2084.
\]

Thus the scalar inequality is no longer merely a floating-point discovery
observation.  What remains is to port this exact-rational derivation to Lean,
where the required alternating-series and `pi` machinery already exists in
`V20KernelSignedAnalytic.lean`.

Positivity of the upstream profile on `[-1/2,1/2]` also makes the monotonicity
argument on `0<=g<=g0<1` identical to the one already used in the present
paper: for fixed `|u|<=1/2`, `cos(2 pi g |u|)` decreases with `g` while its
argument stays in `[0,pi)`.

## Projected global constant

If the pinned nine-point certificate is independently accepted/replayed and
the analytic window interface is discharged, then the block argument gives

\[
D+P\ge A.
\]

Shifted-block averaging then gives

\[
\mathcal D(M)
\ge \frac{A}{289}S-\frac{Q}{289}N-o(N),
\]

so the arbitrary-window rank--trace interface yields

\[
\frac SN\ge
\frac{289H_{\rm cert}-562/625}
     {289-4274291/2500000}.
\]

The right-hand side is the exact rational

\[
\boxed{
\frac{967204424823}{1436451418000}
=0.6733290194872431112041966740\ldots
}.
\]

This is larger than both

```text
current Hurtado theorem      0.6731175265883904...
upstream 9-point assembly    0.6733127422722459...
```

but it is **not yet a certified new bound**.  The point of the experiment is
that the gain comes from a mathematically transparent hybrid:

```text
upstream 9-point local certificate
        +
Hurtado adjacent-pair pinching
        +
Hurtado spectral-threshold contradiction
        =
stronger block assembly
```

No claim of priority or validity beyond the stated proof boundary is made.

## Immediate proof obligations

1. **Open:** reproduce or independently recertify the pinned nine-point
   inequality.
2. **Open:** prove the upstream window satisfies the analytic hypotheses used
   by our Appendices III--IV, rather than importing that interface as a black
   box.
3. **Exact-rational check complete / Lean port open:**
   `k_v(43/50) > 521/2500`; positivity/monotonicity must also be packaged in
   the Lean interface.
4. **Open:** generalize the existing Lean adjacent-pair/spectral-threshold
   modules from the Montgomery--Taylor kernel to an abstract positive window
   plus the one signed kernel point.
5. **Open:** compose the resulting block theorem with the literal `liminf`
   endpoint.

Only after these five items are green should the projected decimal be moved
into the publication manuscript.
