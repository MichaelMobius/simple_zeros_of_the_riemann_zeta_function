#!/usr/bin/env python3
"""Exact-rational enclosure for the imported window kernel at g=43/50.

This script performs only rational arithmetic (fractions.Fraction).  It uses:

  * 31415926/10^7 < pi < 31415927/10^7,
  * 70710678/10^8 < 1/sqrt(2) < 70710679/10^8,
  * standard alternating Taylor bounds for sin/cos on [0,1].

The first pi bounds are the same decimal bounds available in Mathlib and used
by the project's existing Lean signed-kernel proof.  The sqrt(2) interval is
verified here by exact squaring.  The Taylor polynomials are evaluated exactly.

The conclusion is

    k_v(43/50) > 521/2500,

for the seven-term trigonometric profile pinned in
trmdy/zeta-simple-zeros-673137@1610b97b7895ff34982260f8dcaf04a0f7b82cf7.

This is intended as an exact-arithmetic bridge to a Lean proof; the script is
not itself a substitute for kernel checking of the alternating-series lemmas.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Q


@dataclass(frozen=True)
class IV:
    lo: Q
    hi: Q

    def __post_init__(self) -> None:
        if self.lo > self.hi:
            raise ValueError("invalid interval")

    @staticmethod
    def point(x: Q | int) -> "IV":
        q = Q(x)
        return IV(q, q)

    def __add__(self, other: "IV | Q | int") -> "IV":
        o = other if isinstance(other, IV) else IV.point(other)
        return IV(self.lo + o.lo, self.hi + o.hi)

    __radd__ = __add__

    def __neg__(self) -> "IV":
        return IV(-self.hi, -self.lo)

    def __sub__(self, other: "IV | Q | int") -> "IV":
        o = other if isinstance(other, IV) else IV.point(other)
        return self + (-o)

    def __rsub__(self, other: "IV | Q | int") -> "IV":
        return IV.point(other) - self

    def __mul__(self, other: "IV | Q | int") -> "IV":
        o = other if isinstance(other, IV) else IV.point(other)
        vals = (
            self.lo * o.lo,
            self.lo * o.hi,
            self.hi * o.lo,
            self.hi * o.hi,
        )
        return IV(min(vals), max(vals))

    __rmul__ = __mul__

    def __truediv__(self, other: "IV | Q | int") -> "IV":
        o = other if isinstance(other, IV) else IV.point(other)
        if o.lo <= 0 <= o.hi:
            raise ZeroDivisionError("interval denominator contains zero")
        vals = (
            self.lo / o.lo,
            self.lo / o.hi,
            self.hi / o.lo,
            self.hi / o.hi,
        )
        return IV(min(vals), max(vals))

    def sq(self) -> "IV":
        return self * self


def sin_lower7(x: Q) -> Q:
    return x - x**3 / 6 + x**5 / 120 - x**7 / 5040


def sin_upper9(x: Q) -> Q:
    return x - x**3 / 6 + x**5 / 120 - x**7 / 5040 + x**9 / 362880


def cos_lower10(x: Q) -> Q:
    return (
        Q(1)
        - x**2 / 2
        + x**4 / 24
        - x**6 / 720
        + x**8 / 40320
        - x**10 / 3628800
    )


def cos_upper8(x: Q) -> Q:
    return Q(1) - x**2 / 2 + x**4 / 24 - x**6 / 720 + x**8 / 40320


def sin_interval(x: IV) -> IV:
    # On [0,1], sin is increasing and the alternating bounds above apply.
    assert 0 <= x.lo <= x.hi <= 1
    return IV(sin_lower7(x.lo), sin_upper9(x.hi))


def cos_interval(x: IV) -> IV:
    # On [0,1], cos is decreasing.
    assert 0 <= x.lo <= x.hi <= 1
    return IV(cos_lower10(x.hi), cos_upper8(x.lo))


def dec(q: Q, digits: int = 18) -> str:
    return f"{float(q):.{digits}f}"


def main() -> None:
    pi = IV(Q(31_415_926, 10_000_000), Q(31_415_927, 10_000_000))
    A = IV(Q(70_710_678, 100_000_000), Q(70_710_679, 100_000_000))

    # Exact verification that A brackets 1/sqrt(2).
    half = Q(1, 2)
    assert A.lo * A.lo < half < A.hi * A.hi

    x = Q(43, 50)
    theta = pi * Q(7, 50)   # theta = pi - x*pi
    B = pi * x

    sinA = sin_interval(A)
    cosA = cos_interval(A)
    sin_theta = sin_interval(theta)
    cos_theta = cos_interval(theta)

    # The sqrt(2)-frequency contribution.  With A=1/sqrt(2), B=x*pi and
    # theta=pi-B,
    #
    # int cos(sqrt(2)s) cos(2*pi*x*s) ds
    #   = (A sin(A) cos(theta) + B cos(A) sin(theta)) / (B^2-A^2).
    base = (
        A * sinA * cos_theta + B * cosA * sin_theta
    ) / (B.sq() - A.sq())

    # Remaining frequencies are 2*pi*n.  Since x=43/50,
    #
    # I_n = (-1)^(n+1) * x sin(pi*x) / (pi (n^2-x^2))
    #     = (-1)^(n+1) * x sin(theta) / (pi (n^2-x^2)).
    coeff = [
        Q(3_322_500, 1_000_000_000),
        Q(-7_609_135, 1_000_000_000),
        Q(1_190_194, 1_000_000_000),
        Q(-731_476, 1_000_000_000),
        Q(-1_680_572, 1_000_000_000),
        Q(1_141_360, 1_000_000_000),
    ]

    raw = base
    for n, c in enumerate(coeff, start=1):
        positive_piece = (
            IV.point(x) * sin_theta
        ) / (pi * Q(n * n - x * x))
        sign = 1 if n % 2 == 1 else -1
        raw = raw + positive_piece * (c * sign)

    # Integral of the window itself: all integer-frequency cosine terms have
    # zero integral, so only the sqrt(2) term remains: sin(A)/A.
    norm = sinA / A
    k = raw / norm

    target = Q(521, 2500)
    beta = Q(2, 625)
    t = Q(31, 2)
    g0 = x
    scalar_rhs = t * beta * g0

    print("exact rational enclosure")
    print("  k_v(43/50) in [")
    print("   ", dec(k.lo, 18), ",")
    print("   ", dec(k.hi, 18), "]")
    print("  target 521/2500 =", dec(target, 18))
    print("  lower-target      =", dec(k.lo - target, 18))

    assert k.lo > target
    assert target * target > scalar_rhs

    print()
    print("scalar consequence")
    print("  (521/2500)^2      =", dec(target * target, 18))
    print("  t*beta*g0         =", dec(scalar_rhs, 18))
    print("  exact square gap  =", target * target - scalar_rhs)
    print("STATUS: EXACT-RATIONAL SIGNED-KERNEL ENCLOSURE PASSED")


if __name__ == "__main__":
    main()
