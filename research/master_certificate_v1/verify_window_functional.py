#!/usr/bin/env python3
"""Exact-rational audit for the nine-point window functional baseline.

Research-only certificate.  This script verifies the rational arithmetic behind

    H(v) = H_MT - delta / (2 sin(1/sqrt(2))^2),

where, for the six integer Fourier perturbations d_n cos(2*pi*n*s),

    delta = 1/2 * sum d_n^2 - 1/(4*pi^2) * sum d_n^2/n^2.

The analytic identities (orthogonality, cross-term cancellation, Taylor
alternation and monotonicity on [0,1]) are intended to be proved separately in
Lean.  Everything below those identities is checked using Fraction only.
"""

from fractions import Fraction as Q
from math import factorial

D = {
    1: Q(3322500, 10**9),
    2: Q(-7609135, 10**9),
    3: Q(1190194, 10**9),
    4: Q(-731476, 10**9),
    5: Q(-1680572, 10**9),
    6: Q(1141360, 10**9),
}

H_CERT = Q(3362285207, 5000000000)
HMT_LOWER_TARGET = Q(6725007036794, 10**13)
CORR_UPPER_TARGET = Q(43662264868, 10**15)

# Rational brackets for a = 1/sqrt(2).  The square checks below certify them.
A_LO = Q(7071067811865475, 10**16)
A_HI = Q(7071067811865476, 10**16)
assert A_LO > 0
assert A_LO * A_LO < Q(1, 2) < A_HI * A_HI

# Mathlib's Real.pi_lt_d20 supplies pi < 3.14159265358979323847.
PI_HI = Q(314159265358979323847, 10**20)
assert PI_HI > 3


def sin_lower_15(x: Q) -> Q:
    """x - x^3/3! + ... - x^15/15!, a lower bound for sin x on [0,1]."""
    return sum(
        (Q(1) if n % 2 == 0 else Q(-1)) * x ** (2 * n + 1) / factorial(2 * n + 1)
        for n in range(8)
    )


def cos_upper_16(x: Q) -> Q:
    """1 - x^2/2! + ... + x^16/16!, an upper bound for cos x on [0,1]."""
    return sum(
        (Q(1) if n % 2 == 0 else Q(-1)) * x ** (2 * n) / factorial(2 * n)
        for n in range(9)
    )


S0 = sum(c * c for c in D.values())
S2 = sum(c * c / (n * n) for n, c in D.items())

assert S0 == Q(75016585491221, 10**18)
assert S2 == Q(23268362407797749, 9 * 10**20)

SIN_LO = sin_lower_15(A_LO)
COS_HI = cos_upper_16(A_LO)
assert SIN_LO > 0

# Since A_LO < a < A_HI, sin is increasing and cos is decreasing on [0,1].
# Thus sin(a) >= SIN_LO and cos(a) <= COS_HI.  Check the target MT bound
# without forming any floating-point quotient:
#
#   3/2 - a cos(a)/sin(a) > HMT_LOWER_TARGET.
R = Q(3, 2) - HMT_LOWER_TARGET
assert A_HI * COS_HI < R * SIN_LO

# pi < PI_HI implies
#   delta < S0/2 - S2/(4*PI_HI^2) = DELTA_HI.
DELTA_HI = S0 / 2 - S2 / (4 * PI_HI * PI_HI)
assert DELTA_HI > 0

# sin(a)^2 >= SIN_LO^2, hence the correction is bounded above by
# DELTA_HI/(2*SIN_LO^2).  Again check the target without decimals.
assert DELTA_HI < CORR_UPPER_TARGET * 2 * SIN_LO * SIN_LO

FINAL_LOWER = HMT_LOWER_TARGET - CORR_UPPER_TARGET
assert FINAL_LOWER > H_CERT
assert FINAL_LOWER - H_CERT == Q(3633, 250000000000000)

print("S0 =", S0)
print("S2 =", S2)
print("H_MT lower target =", HMT_LOWER_TARGET, float(HMT_LOWER_TARGET))
print("correction upper target =", CORR_UPPER_TARGET, float(CORR_UPPER_TARGET))
print("final rational lower =", FINAL_LOWER, float(FINAL_LOWER))
print("H_cert =", H_CERT, float(H_CERT))
print("exact margin =", FINAL_LOWER - H_CERT, float(FINAL_LOWER - H_CERT))
print("WINDOW_FUNCTIONAL_RATIONAL_AUDIT_OK")
