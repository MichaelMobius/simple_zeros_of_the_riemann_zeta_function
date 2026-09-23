#!/usr/bin/env python3
"""Exact-arithmetic assembly prototype for the nine-point/adjacent-pair hybrid.

This is a research diagnostic, not a proof of the local nine-point certificate
or of the signed transcendental kernel inequality.  Everything *after* those
inputs is checked with fractions.Fraction.

Pinned local data:
  trmdy/zeta-simple-zeros-673137
  commit 1610b97b7895ff34982260f8dcaf04a0f7b82cf7
"""

from __future__ import annotations

from fractions import Fraction as Q
import math


# Pinned upstream nine-point data.
EPS = Q(15211, 2_500_000)
P = Q(1, 2500)
Q_GAPS = 8
BETA = Q_GAPS * P
H_CERT = Q(3_362_285_207, 5_000_000_000)

# Hybrid adjacent-pair operating point.
G0 = Q(43, 50)
T = Q(31, 2)
K_LOWER = Q(521, 2500)

# Upstream admissible window v(s)=sum c_j cos(omega_j s).
WINDOW_DEN = 1_000_000_000
WINDOW_NUM = [
    1_000_000_000,
    3_322_500,
    -7_609_135,
    1_190_194,
    -731_476,
    -1_680_572,
    1_141_360,
]


def integral_cos(a: float) -> float:
    """Integral of cos(a*s) from -1/2 to 1/2."""
    if abs(a) < 1e-15:
        return 1.0
    return 2.0 * math.sin(a / 2.0) / a


def window_kernel_float(x: float) -> float:
    """NONRIGOROUS discovery evaluation of the normalized overlap kernel."""
    coeff = [n / WINDOW_DEN for n in WINDOW_NUM]
    omega = [
        math.sqrt(2.0),
        2.0 * math.pi,
        4.0 * math.pi,
        6.0 * math.pi,
        8.0 * math.pi,
        10.0 * math.pi,
        12.0 * math.pi,
    ]

    norm = sum(c * integral_cos(w) for c, w in zip(coeff, omega))
    b = 2.0 * math.pi * x

    def product_integral(a: float, b: float) -> float:
        # int cos(a s) cos(b s) ds on [-1/2,1/2]
        ap = a + b
        am = a - b
        tp = 0.5 if abs(ap) < 1e-14 else math.sin(ap / 2.0) / ap
        tm = 0.5 if abs(am) < 1e-14 else math.sin(am / 2.0) / am
        return tp + tm

    value = sum(c * product_integral(w, b) for c, w in zip(coeff, omega))
    return value / norm


def block_data(m: int) -> tuple[Q, Q, Q]:
    if m <= Q_GAPS:
        raise ValueError("m must exceed the number of gaps")
    a = EPS * (m - Q_GAPS)
    q = BETA * (m - Q_GAPS)
    margin = G0 * q + (Q(1) - Q(1) / T) * Q(m, m - 1) - a
    return a, q, margin


def projected_bound(m: int) -> Q:
    a, q, _ = block_data(m)
    return (m * H_CERT - q) / (m - a)


def main() -> None:
    scalar_rhs = T * BETA * G0
    scalar_margin_from_target = K_LOWER * K_LOWER - scalar_rhs

    print("=== exact hybrid assembly prototype ===")
    print("epsilon =", EPS, "=", float(EPS))
    print("beta    =", BETA, "=", float(BETA))
    print("g0      =", G0, "=", float(G0))
    print("t       =", T, "=", float(T))
    print()

    print("scalar target:")
    print("  t*beta*g0 =", scalar_rhs, "=", float(scalar_rhs))
    print("  k_lower   =", K_LOWER, "=", float(K_LOWER))
    print(
        "  k_lower^2 - t*beta*g0 =",
        scalar_margin_from_target,
        "=",
        float(scalar_margin_from_target),
    )
    assert scalar_margin_from_target > 0

    kdiag = window_kernel_float(float(G0))
    print()
    print("NONRIGOROUS window-kernel diagnostic:")
    print("  k_v(g0) ~=", format(kdiag, ".16f"))
    print("  k_v(g0) - k_lower ~=", format(kdiag - float(K_LOWER), ".16e"))
    print("  (this diagnostic is not a proof obligation discharge)")

    feasible: list[tuple[Q, int, Q]] = []
    for m in range(Q_GAPS + 1, 1001):
        a, q, margin = block_data(m)
        if margin > 0:
            feasible.append((projected_bound(m), m, margin))

    if not feasible:
        raise SystemExit("no block length satisfies the exact contradiction margin")

    best_bound, best_m, best_margin = max(feasible, key=lambda item: item[0])
    a, q, _ = block_data(best_m)

    print()
    print("best exact block length in scan 9..1000:")
    print("  m       =", best_m)
    print("  A       =", a, "=", float(a))
    print("  Q       =", q, "=", float(q))
    print("  margin  =", best_margin, "=", float(best_margin))
    print("  bound   =", best_bound)
    print("          =", format(float(best_bound), ".16f"))

    # Locked values recorded in README.md.
    assert best_m == 289
    assert a == Q(4_274_291, 2_500_000)
    assert q == Q(562, 625)
    assert best_margin == Q(405_889, 174_375_000)
    assert best_bound == Q(967_204_424_823, 1_436_451_418_000)

    current = 0.6731175265883904
    upstream = 0.6733127422722459
    print()
    print("diagnostic comparisons:")
    print("  gain over current Hurtado theorem ~=", float(best_bound) - current)
    print("  gain over upstream 9-point assembly ~=", float(best_bound) - upstream)

    print()
    print("PROOF BOUNDARY:")
    print("  exact assembly arithmetic: checked")
    print("  upstream 9-point local certificate: imported/pinned, must be replayed")
    print("  signed k_v(43/50)>521/2500: NOT proved here")
    print("  arbitrary-window analytic interface: must be reconstructed/formalized")


if __name__ == "__main__":
    main()
