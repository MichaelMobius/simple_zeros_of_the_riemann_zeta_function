#!/usr/bin/env python3
"""Exact rational verifier for the v21 six-gap analytic certificate.

Trust boundary of this script:
  * Python integer arithmetic and fractions.Fraction only.
  * No floating point, Arb/FLINT, interval arithmetic, grid search,
    branch-and-bound, SDP, or external numerical solver.

Analytic inputs assumed already proved in the manuscript/Lean development:
  1. root brackets |r_N-q_N| < 1e-5 for N=1,...,12;
  2. C0 > 2633/10000, c < 193/1000, 3.14 < pi < 3.142;
  3. the phase/quadratic minorant derived from these bounds;
  4. one-body basin localization and micro-unit floors mu_A,mu_B,mu_C;
  5. the final strong-convexity tables J,m,W,D,R.

The verifier checks, exactly in Q:
  44100 -> 511 -> 231 -> 23 -> 5,
then verifies that the five words lie in the final J-cells and that the
five final quadratic minima exceed 39/10000 + 1/2000000.
"""

from fractions import Fraction as Q
from itertools import product
from collections import defaultdict
from math import isqrt
import json
import hashlib
import os
import sys

# ---------------------------------------------------------------------------
# Basic exact helpers
# ---------------------------------------------------------------------------

def qstr(x: Q) -> str:
    return f"{x.numerator}/{x.denominator}"

def floor_frac(x: Q, den: int) -> Q:
    return Q(x.numerator * den // x.denominator, den)

def ceil_frac(x: Q, den: int) -> Q:
    return Q((x.numerator * den + x.denominator - 1) // x.denominator, den)

def sqrt_upper_rational(x: Q, den: int = 10_000) -> Q:
    """Smallest k/den with (k/den)^2 > x, using integer arithmetic only."""
    assert x >= 0
    target_num = x.numerator * den * den
    target_den = x.denominator
    k = isqrt(target_num // target_den)
    if k * k * target_den <= target_num:
        k += 1
    assert Q(k * k, den * den) > x
    if k > 0:
        assert Q((k - 1) * (k - 1), den * den) <= x
    return Q(k, den)

def det_frac(A):
    A = [row[:] for row in A]
    n = len(A)
    d = Q(1)
    for col in range(n):
        piv = next((i for i in range(col, n) if A[i][col] != 0), None)
        if piv is None:
            return Q(0)
        if piv != col:
            A[col], A[piv] = A[piv], A[col]
            d = -d
        pv = A[col][col]
        d *= pv
        for i in range(col + 1, n):
            if A[i][col] == 0:
                continue
            fac = A[i][col] / pv
            for j in range(col + 1, n):
                A[i][j] -= fac * A[col][j]
            A[i][col] = Q(0)
    return d

def assert_pos_def(A):
    for k in range(1, len(A) + 1):
        d = det_frac([row[:k] for row in A[:k]])
        assert d > 0, (k, d)

def inv_frac(A):
    n = len(A)
    aug = [A[i][:] + [Q(int(i == j)) for j in range(n)] for i in range(n)]
    for col in range(n):
        piv = next(i for i in range(col, n) if aug[i][col] != 0)
        aug[col], aug[piv] = aug[piv], aug[col]
        pv = aug[col][col]
        aug[col] = [x / pv for x in aug[col]]
        for i in range(n):
            if i == col:
                continue
            fac = aug[i][col]
            if fac != 0:
                aug[i] = [aug[i][j] - fac * aug[col][j] for j in range(2 * n)]
    return [row[n:] for row in aug]

def matvec(A, v):
    return [sum((A[i][j] * v[j] for j in range(len(v))), Q(0)) for i in range(len(A))]

def dot(u, v):
    return sum((u[i] * v[i] for i in range(len(u))), Q(0))

# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------

delta = Q(39, 10_000)
p = [Q(2714, 10_000_000), Q(3733, 10_000_000), Q(3553, 10_000_000),
     Q(3553, 10_000_000), Q(3733, 10_000_000), Q(2714, 10_000_000)]

muA = [286, 550, 817, 1085, 1353, 1622, 1890]
muB = [394, 756, 1123, 1490, 1859]
muC = [375, 720, 1069, 1419, 1770, 2122]

IA = [(Q(955,1000),Q(1158,1000)), (Q(1792,1000),Q(2258,1000)),
      (Q(2612,1000),Q(3396,1000)), (Q(3502,1000),Q(4465,1000)),
      (Q(4500,1000),Q(5466,1000)), (Q(5500,1000),Q(6413,1000)),
      (Q(6576,1000),Q(7270,1000))]
IB = [(Q(955,1000),Q(1158,1000)), (Q(1798,1000),Q(2249,1000)),
      (Q(2637,1000),Q(3358,1000)), (Q(3568,1000),Q(4375,1000)),
      (Q(4611,1000),Q(5285,1000))]
IC = [(Q(955,1000),Q(1158,1000)), (Q(1797,1000),Q(2251,1000)),
      (Q(2633,1000),Q(3365,1000)), (Q(3556,1000),Q(4392,1000)),
      (Q(4580,1000),Q(5322,1000)), (Q(5793,1000),Q(6078,1000))]
basins = [IA, IB, IC, IC, IB, IA]

q = [None] + [Q(x,100_000) for x in
    [105728,203007,302025,401524,501221,601019,
     700874,800765,900680,1000612,1100557,1200510]]

weights = {1:Q(1,3), 2:Q(2,5), 3:Q(1,2), 4:Q(2,3), 5:Q(1), 6:Q(2)}

pi_lo = Q(314,100)
pi_hi = Q(3142,1000)
C0_lo = Q(2633,10_000)
d0 = Q(1) / (2*pi_hi*pi_hi)

# ---------------------------------------------------------------------------
# 44100 -> 511
# ---------------------------------------------------------------------------

def word_weight(w):
    a,b,c,d,e,f = w
    return muA[a-1]+muB[b-1]+muC[c-1]+muC[d-1]+muB[e-1]+muA[f-1]

def enumerate_511():
    survivors = []
    for w in product(range(1,8), range(1,6), range(1,7),
                     range(1,7), range(1,6), range(1,8)):
        wt = word_weight(w)
        if wt < 3900:
            survivors.append((w, wt))
    assert len(survivors) == 511

    D = {0:1}
    stats = []
    for S in (muA,muB,muC,muC,muB,muA):
        N = defaultdict(int)
        for n,cnt in D.items():
            for u in S:
                if n+u < 3900:
                    N[n+u] += cnt
        D = dict(N)
        stats.append((len(D), sum(D.values()), min(D), max(D)))
    expected = [
        (7,7,286,1890),
        (35,35,680,3749),
        (142,142,1055,3898),
        (189,316,1430,3899),
        (152,384,1824,3898),
        (145,511,2110,3897),
    ]
    assert stats == expected
    return survivors, stats

# ---------------------------------------------------------------------------
# Rational phase minorant
# ---------------------------------------------------------------------------

def P7(t):
    return t - t**3/Q(6) + t**5/Q(120) - t**7/Q(5040)

def phase_minorant_exact(L, U, N):
    assert 1 <= N <= 12 and 0 < L <= U
    rlo = q[N] - Q(1,100_000)
    xmin = min(L, rlo)
    assert xmin > 0
    M = Q(1) + Q(193) / (Q(3140)*xmin*xmin)
    D = max(abs(L-q[N]), abs(U-q[N])) + Q(1,100_000)
    rho = M*D
    if not (rho < 1):
        return None
    s = min(rho, Q(1)-rho)
    t = pi_lo*s
    if t > Q(8,5):
        return None
    p7 = P7(t)
    if p7 <= 0:
        return None
    Araw = C0_lo*C0_lo * (U*U)/((U*U-d0)**2) * (p7/rho)**2
    alpha = Araw * Q(999,1000)
    eta = Araw * Q(999,10_000_000_000)
    return alpha, eta, rho

def phase_minorant_rounded(L, U, N):
    exact = phase_minorant_exact(L,U,N)
    if exact is None:
        return None
    alpha, eta, rho = exact
    af = floor_frac(alpha, 10**9)
    eu = ceil_frac(eta, 10**15)
    if af <= 0:
        return None
    assert af <= alpha and eu >= eta
    return af, eu, rho

# ---------------------------------------------------------------------------
# Quadratic forms and contractions
# ---------------------------------------------------------------------------

def initial_intervals(word):
    box = [basins[i][word[i]-1] for i in range(6)]
    out = {}
    for r in range(1,7):
        for i in range(7-r):
            L = sum((box[j][0] for j in range(i,i+r)), Q(0))
            U = sum((box[j][1] for j in range(i,i+r)), Q(0))
            out[(i,r)] = (L,U)
    return out

def add_quad(M, b, c, idxs, alpha, center, eta, coeff):
    aa = coeff*alpha
    linear = -2*aa*center
    for u in idxs:
        M[u][u] += aa
        b[u] += linear/2
        for vv in idxs:
            if vv > u:
                M[u][vv] += aa
                M[vv][u] += aa
    c += coeff*(alpha*center*center - eta)
    return c

def build_Q(word, intervals):
    M = [[Q(0) for _ in range(6)] for _ in range(6)]
    b = [p[i]/2 for i in range(6)]
    c = Q(0)
    used = []
    for r in range(1,7):
        coeff = weights[r]
        for i in range(7-r):
            L,U = intervals[(i,r)]
            N = sum(word[i:i+r])
            minor = phase_minorant_rounded(L,U,N) if N <= 12 else None
            if minor is None:
                continue
            alpha,eta,rho = minor
            c = add_quad(M,b,c,list(range(i,i+r)),alpha,q[N],eta,coeff)
            used.append((i,r,N,alpha,eta,rho))
    assert_pos_def(M)
    return M,b,c,used

def qmin_and_inverse(M,b,c):
    inv = inv_frac(M)
    invb = matvec(inv,b)
    qmin = c - dot(b,invb)
    xstar = [-z for z in invb]
    return qmin, inv, xstar

def contract(word, intervals):
    M,b,c,used = build_Q(word,intervals)
    qmin,inv,xstar = qmin_and_inverse(M,b,c)
    if qmin >= delta:
        return False, qmin, None, len(used)
    gap = delta-qmin
    new = {}
    for r in range(1,7):
        for i in range(7-r):
            ell = [Q(1) if i <= j < i+r else Q(0) for j in range(6)]
            invell = matvec(inv,ell)
            rad2 = gap*dot(ell,invell)
            radius = sqrt_upper_rational(rad2,10_000)
            center = dot(ell,xstar)
            lo0 = floor_frac(center-radius,10_000)
            hi0 = ceil_frac(center+radius,10_000)
            L,U = intervals[(i,r)]
            lo,hi = max(L,lo0), min(U,hi0)
            assert lo < hi
            new[(i,r)] = (lo,hi)
    return True, qmin, new, len(used)

def run_round(items, initial=False):
    survivors = []
    discards = []
    for item in items:
        if initial:
            word,wt = item
            intervals = initial_intervals(word)
        else:
            word,intervals,*_ = item
        ok,qmin,new,nused = contract(word,intervals)
        if ok:
            survivors.append((word,new,qmin,nused))
        else:
            discards.append((word,qmin-delta,qmin,nused))
    return survivors,discards

# ---------------------------------------------------------------------------
# Final J-cells and strong-convexity quadratics
# ---------------------------------------------------------------------------

J = [None,
     (Q(1023,1000),Q(1061,1000)), (Q(1950,1000),Q(2018,1000)),
     (Q(2991,1000),Q(3061,1000)), (Q(3950,1000),Q(4084,1000)),
     (Q(4962,1000),Q(5050,1000)), (Q(5975,1000),Q(6086,1000)),
     (Q(6967,1000),Q(7101,1000)), (Q(7993,1000),Q(8080,1000)),
     (Q(9013,1000),Q(9108,1000)), (Q(10025,1000),Q(10078,1000))]

m2 = [Q(37,25),Q(723,2000),Q(17,125),Q(173,2500),Q(507,10000),
      Q(31,1000),Q(213,10000),Q(181,10000),Q(1,80),Q(117,10000)]
a2 = [Q(1043,1000),Q(1984,1000),Q(3026,1000),Q(4018,1000),Q(5004,1000),
      Q(6045,1000),Q(7034,1000),Q(8036,1000),Q(9074,1000),Q(10052,1000)]
W2 = [Q(16195,100_000_000),Q(39121,100_000_000),Q(254,100_000_000),
      Q(32,100_000_000),Q(186,100_000_000),Q(2278,100_000_000),
      Q(886,100_000_000),Q(853,100_000_000),Q(3712,100_000_000),
      Q(1420,100_000_000)]
D2 = [Q(-230346,10_000_000),Q(-172761,10_000_000),Q(8840,10_000_000),
      Q(2381,10_000_000),Q(-4542,10_000_000),Q(12962,10_000_000),
      Q(6976,10_000_000),Q(5985,10_000_000),Q(10801,10_000_000),
      Q(6120,10_000_000)]
R2 = [Q(20,1000),Q(34,1000),Q(35,1000),Q(68,1000),Q(46,1000),
      Q(70,1000),Q(67,1000),Q(44,1000),Q(61,1000),Q(27,1000)]

def add_final_L(M,b,c,idxs,N,coeff):
    j=N-1
    alpha=m2[j]/2
    beta=D2[j]-m2[j]*a2[j]
    gamma=W2[j]-R2[j]/20_000_000-D2[j]*a2[j]+m2[j]*a2[j]*a2[j]/2
    for u in idxs:
        M[u][u] += coeff*alpha
        b[u] += coeff*beta/2
        for vv in idxs:
            if vv>u:
                M[u][vv] += coeff*alpha
                M[vv][u] += coeff*alpha
    c += coeff*gamma
    return c

def final_margin(word):
    M=[[Q(0) for _ in range(6)] for _ in range(6)]
    b=[p[i]/2 for i in range(6)]
    c=Q(0)
    for r in range(1,7):
        for i in range(7-r):
            N=sum(word[i:i+r])
            c=add_final_L(M,b,c,list(range(i,i+r)),N,weights[r])
    assert_pos_def(M)
    qmin,_,_=qmin_and_inverse(M,b,c)
    return qmin-delta

# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main():
    words511, dpstats = enumerate_511()
    r0,d0s = run_round(words511, initial=True)
    r1,d1s = run_round(r0)
    r2,d2s = run_round(r1)

    assert (len(words511),len(r0),len(r1),len(r2)) == (511,231,23,5)
    final_words = [x[0] for x in r2]
    expected_final = [
        (1,2,1,2,1,2),
        (1,2,1,2,2,1),
        (1,2,2,1,2,1),
        (2,1,2,1,2,1),
        (2,1,2,2,1,2),
    ]
    assert final_words == expected_final

    for word,intervals,_,_ in r2:
        for r in range(1,7):
            for i in range(7-r):
                N=sum(word[i:i+r])
                L,U=intervals[(i,r)]
                JL,JU=J[N]
                assert JL <= L <= U <= JU, (word,i,r,N,L,U,J[N])

    final_margins = {''.join(map(str,w)): final_margin(w) for w in expected_final}
    for margin in final_margins.values():
        assert margin > Q(1,2_000_000)

    round_mins=[]
    for name,ds in [('R0',d0s),('R1',d1s),('R2',d2s)]:
        w,margin,qmin,nused=min(ds,key=lambda t:t[1])
        round_mins.append((name,w,margin,nused))

    def enc_intervals(intervals):
        return {f'{i+1}:{r}':[qstr(L),qstr(U)] for (i,r),(L,U) in sorted(intervals.items())}
    def enc_survivor(x):
        word,intervals,qmin,nused=x
        return {'word':''.join(map(str,word)),'qmin':qstr(qmin),'used_terms':nused,
                'intervals':enc_intervals(intervals)}
    def enc_discard(x):
        word,margin,qmin,nused=x
        return {'word':''.join(map(str,word)),'margin':qstr(margin),'qmin':qstr(qmin),
                'used_terms':nused}

    certificate = {
        'chain':[44100,511,231,23,5],
        'dp_stats':[list(x) for x in dpstats],
        'words_511':[{'word':''.join(map(str,w)),'weight':wt} for w,wt in words511],
        'rounds':{
            'R0':{'survivors':[enc_survivor(x) for x in r0],
                  'discards':[enc_discard(x) for x in d0s]},
            'R1':{'survivors':[enc_survivor(x) for x in r1],
                  'discards':[enc_discard(x) for x in d1s]},
            'R2':{'survivors':[enc_survivor(x) for x in r2],
                  'discards':[enc_discard(x) for x in d2s]},
        },
        'round_min_discard_margins':[
            {'round':name,'word':list(w),'margin':qstr(margin),'used_terms':nused}
            for name,w,margin,nused in round_mins
        ],
        'survivors_231':[''.join(map(str,x[0])) for x in r0],
        'survivors_23':[''.join(map(str,x[0])) for x in r1],
        'survivors_5':[''.join(map(str,x[0])) for x in r2],
        'final_margins':{k:qstr(vv) for k,vv in final_margins.items()},
        'final_margin_gt':'1/2000000',
        'rounding':{
            'minorant_alpha':'down to denominator 1e9',
            'minorant_eta':'up to denominator 1e15',
            'ellipsoid_radius':'strict upper bound on denominator 1e4',
            'contracted_endpoints':'outward to denominator 1e4',
        },
    }
    payload=json.dumps(certificate,sort_keys=True,separators=(',',':')).encode()
    certificate['sha256_without_sha_field']=hashlib.sha256(payload).hexdigest()

    out=os.environ.get('V26_CERT_OUT', '/mnt/data/v21_rational_bootstrap_certificate.json')
    with open(out,'w',encoding='utf-8') as f:
        json.dump(certificate,f,indent=2,sort_keys=True)
        f.write('\n')

    print('EXACT RATIONAL CERTIFICATE: VERIFIED')
    print('chain: 44100 -> 511 -> 231 -> 23 -> 5')
    print('final words:', ', '.join(certificate['survivors_5']))
    for name,w,margin,nused in round_mins:
        print(f'{name} smallest discard margin: {qstr(margin)} at {"".join(map(str,w))}; terms={nused}')
    print('final exact margins above 39/10000:')
    for k,vv in final_margins.items():
        print(' ',k,qstr(vv))
    print('all final margins > 1/2000000')
    print('certificate json:',out)
    print('certificate payload sha256:',certificate['sha256_without_sha_field'])

if __name__ == '__main__':
    main()
