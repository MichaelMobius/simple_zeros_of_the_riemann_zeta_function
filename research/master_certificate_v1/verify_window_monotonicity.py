#!/usr/bin/env python3
"""Exact-rational certificate for monotonicity of the pinned local profile.

For

  v(s) = cos(sqrt(2)s) + sum_{n=1}^6 d_n cos(2*pi*n*s),

put x = 2*pi*s and c = cos x.  Using sin(nx)=U_{n-1}(c) sin x,

  sum n*d_n*sin(nx) = sin(x) P(c)

for a rational quintic P.  This verifier proves P(c) >= -q on [-1,1]
with q=161/5000 by an exact Bernstein certificate on 14 equal rational
subintervals.  Together with sin y >= 2y/pi on [0,pi/2], sin x <= x for
x>=0, and q*pi^3 < 1, this yields v'(s) <= 0 on [0,1/2].

Only Fraction arithmetic is used here.  The analytic sine/Chebyshev identities
are to be mirrored in Lean.
"""

from fractions import Fraction as Q
from math import comb

D = {
    1: Q(3322500, 10**9),
    2: Q(-7609135, 10**9),
    3: Q(1190194, 10**9),
    4: Q(-731476, 10**9),
    5: Q(-1680572, 10**9),
    6: Q(1141360, 10**9),
}
QBAD = Q(161, 5000)  # 0.0322
PI_HI = Q(314159265358979323847, 10**20)


def add(a, b):
    n = max(len(a), len(b))
    return [(a[i] if i < len(a) else Q(0)) + (b[i] if i < len(b) else Q(0)) for i in range(n)]


def scale(a, q):
    return [q*x for x in a]


def mul_x(a):
    return [Q(0)] + a


# Chebyshev U_0=1, U_1=2c, U_{k+1}=2c U_k-U_{k-1}.
U = [[Q(1)], [Q(0), Q(2)]]
for k in range(1, 5):
    U.append(add(scale(mul_x(U[k]), Q(2)), scale(U[k-1], Q(-1))))

P = [Q(0)]
for n, dn in D.items():
    P = add(P, scale(U[n-1], Q(n) * dn))
P += [Q(0)] * (6-len(P))

# Independent exact expected polynomial audit.
EXPECTED = [
    Q(-4325471, 500000000),
    Q(11178018, 500000000),
    Q(57558324, 500000000),
    Q(-121274176, 500000000),
    Q(-67222880, 500000000),
    Q(109570560, 500000000),
]
assert P == EXPECTED

# Qpoly = P + QBAD.
QP = P[:]
QP[0] += QBAD


def compose_affine_power_coeffs(poly, a, h):
    """Power coefficients in t of poly(a+h*t)."""
    out = [Q(0)] * len(poly)
    for i, ai in enumerate(poly):
        for k in range(i + 1):
            out[k] += ai * Q(comb(i, k)) * (a ** (i-k)) * (h ** k)
    return out


def power_to_bernstein(power, degree):
    """Degree-N Bernstein coefficients from power coefficients."""
    out = []
    for k in range(degree + 1):
        val = Q(0)
        for i in range(min(k, len(power)-1) + 1):
            val += power[i] * Q(comb(k, i), comb(degree, i))
        out.append(val)
    return out


all_coeffs = []
parts = 14
for j in range(parts):
    a = Q(-1) + Q(2*j, parts)
    b = Q(-1) + Q(2*(j+1), parts)
    power = compose_affine_power_coeffs(QP, a, b-a)
    bern = power_to_bernstein(power, 5)
    assert all(x >= 0 for x in bern), (j, a, b, bern)
    all_coeffs.append((a, b, bern))

# The analytic comparison after the Bernstein bound is
#   sqrt(2) sin(sqrt(2)s) + 2*pi*sin(x)P(c)
#     >= 4s/pi - 4*pi^2*q*s
#     = (4s/pi)(1-q*pi^3).
# pi < PI_HI makes the final positivity a rational check.
assert QBAD * PI_HI**3 < 1

print("P(c) coefficients low-to-high:")
for i, x in enumerate(P):
    print(f"  c^{i}: {x}")
print("Bernstein subdivision parts:", parts)
print("minimum Bernstein coefficient:", min(x for _, _, bb in all_coeffs for x in bb))
print("q =", QBAD, float(QBAD))
print("1 - q*pi_upper^3 =", 1 - QBAD*PI_HI**3, float(1 - QBAD*PI_HI**3))
print("WINDOW_MONOTONICITY_RATIONAL_AUDIT_OK")
