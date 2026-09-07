#!/usr/bin/env python3
"""Exact rational arithmetic for the seven-point analytic refinement.

Python standard library only. This verifies the NEW numerical constant,
pressure accounting, and integer block optimum. It does NOT rerun the
seven-point local certificate, the analytic zeta input, or Lean.

Run: python verify_improved_bound.py --output verification.json
All assertions about bounds use Fraction and integer arithmetic; Decimal
is used only to display outward-rounded endpoints.
"""
from fractions import Fraction as F
from math import factorial, isqrt
from decimal import Decimal, localcontext, ROUND_FLOOR, ROUND_CEILING
from pathlib import Path
import argparse
import json

DELTA = F(39, 10000)
BETA = F(1, 500)
Q = 6
P = tuple(F(v, 10**7) for v in (2714, 3733, 3553, 3553, 3733, 2714))
RATIO = BETA / DELTA
SIGNED_KERNEL_LOWER = F(171389, 10**6)


def sqrt_bounds(value, digits=80):
    """Enclose sqrt(value) by adjacent rationals with denominator 10^digits."""
    assert value >= 0
    scale = 10**digits
    integer = isqrt((value.numerator * scale * scale) // value.denominator)
    lo, hi = F(integer, scale), F(integer + 1, scale)
    assert lo * lo <= value <= hi * hi
    return lo, hi


def h_bounds():
    def partial(last, shift):
        return sum((F((-1)**k, 2**k * factorial(2*k + shift))
                    for k in range(last + 1)), F(0))
    cos_lo, cos_hi = partial(41, 0), partial(40, 0)
    sinc_lo, sinc_hi = partial(41, 1), partial(40, 1)
    assert 0 < cos_lo < cos_hi and 0 < sinc_lo < sinc_hi
    return F(3, 2) - cos_hi / sinc_lo, F(3, 2) - cos_lo / sinc_hi


def add_iv(a, b):
    return a[0]+b[0], a[1]+b[1]


def neg_iv(a):
    return -a[1], -a[0]


def mul_iv(a, b):
    products = [x*y for x in a for y in b]
    return min(products), max(products)


def div_iv(a, b):
    assert b[0] > 0 or b[1] < 0
    return mul_iv(a, (1/b[1], 1/b[0]))


def pi_bounds():
    def atan_interval(x, n):
        partial = sum(((-1)**k*x**(2*k+1)/(2*k+1)
                       for k in range(n+1)), F(0))
        following = partial + (-1)**(n+1)*x**(2*n+3)/(2*n+3)
        return min(partial, following), max(partial, following)
    return add_iv(mul_iv((F(16),F(16)), atan_interval(F(1,5), 60)),
                  mul_iv((F(-4),F(-4)), atan_interval(F(1,239), 20)))


def trig_at_rational(x, shift):
    n = 42
    assert 0 <= x <= 4
    partial = sum((F((-1)**k, factorial(2*k+shift))*x**(2*k+shift)
                   for k in range(n+1)), F(0))
    following = partial + F((-1)**(n+1), factorial(2*n+2+shift))*x**(2*n+2+shift)
    return min(partial, following), max(partial, following)


def kernel_at_089(h):
    gap = F(89,100)
    pi = pi_bounds()
    z = mul_iv(pi, (gap,gap))
    midpoint, radius = (z[0]+z[1])/2, (z[1]-z[0])/2
    sinz = add_iv(trig_at_rational(midpoint,1), (-radius,radius))
    cosz = add_iv(trig_at_rational(midpoint,0), (-radius,radius))
    c = F(3,2)-h[1], F(3,2)-h[0]
    numerator = add_iv(cosz, neg_iv(mul_iv(mul_iv((F(2),F(2)), z), mul_iv(c,sinz))))
    denominator = add_iv((F(1),F(1)), neg_iv(mul_iv((F(2),F(2)),mul_iv(z,z))))
    k = div_iv(numerator, denominator)
    assert k[0] > SIGNED_KERNEL_LOWER
    w = k[0]**2, k[1]**2
    assert SIGNED_KERNEL_LOWER**2 > F(2937,100000)
    assert w[0] > F(2937,100000)
    return k, w


def adjacent_pair_refinement(h):
    m, g0, t = 450, F(89,100), F(33,2)
    energy = DELTA*(m-Q)
    pressure_mass = BETA*(m-Q)
    threshold = F(m,m-1)
    k, w = kernel_at_089(h)
    assert t*BETA*g0 == F(2937,100000)
    margin = g0*pressure_mass+(1-1/t)*threshold-energy
    assert margin == F(6363,30868750) and margin > 0
    b = tuple((m*v-pressure_mass)/(m-energy) for v in h)
    assert b[0] > F(673117526588390,10**15)
    return {
        "block_size": m, "g0": str(g0), "t": str(t),
        "A": str(energy), "pressure_mass": str(pressure_mass),
        "kernel_at_g0": show_interval(k), "w_at_g0": show_interval(w),
        "signed_kernel_lower_bound": str(SIGNED_KERNEL_LOWER),
        "signed_kernel_claim": "171389/1000000 < k(89/100)",
        "required_w_lower_bound": "2937/100000",
        "signed_square_margin_over_required_w": str(
            SIGNED_KERNEL_LOWER**2 - F(2937,100000)),
        "contradiction_margin": str(margin),
        "bound_exact_expression": "(1125000*H_MT-2220)/1120671",
        "bound": show_interval(b),
        "strict_rational_target": "0.673117526588390",
        "scope": "New analytic adjacent-pair lemma plus one exact rational transcendental enclosure; no new seven-point certificate.",
    }


def phi_bounds(m):
    energy = DELTA * (m - Q)
    assert 0 < energy < m * (m - 1)
    if energy <= F(m, m - 1):
        return energy, energy
    lo, hi = sqrt_bounds(F(m - 1, m) * energy)
    return 2*lo - 1 + energy/m, 2*hi - 1 + energy/m


def bound_interval(m, h):
    plo, phi = phi_bounds(m)
    zlo, zhi = plo/m, phi/m
    assert 0 <= zlo <= zhi < 1 and h[0] > RATIO
    return ((h[0] - RATIO*zlo)/(1-zlo),
            (h[1] - RATIO*zhi)/(1-zhi))


def directed_decimal(value, rounding, digits=65):
    with localcontext() as ctx:
        ctx.prec = digits
        ctx.rounding = rounding
        return str(Decimal(value.numerator)/Decimal(value.denominator))


def show_interval(pair):
    return {"lower": directed_decimal(pair[0], ROUND_FLOOR),
            "upper": directed_decimal(pair[1], ROUND_CEILING)}


def derivative_sign_polynomial(m):
    a, b = DELTA.numerator, DELTA.denominator
    hp_numerator = m*m - 2*(Q+1)*m + 3*Q
    positive_rhs = (b-a)*m + 2*a*Q
    assert hp_numerator > 0 and positive_rhs > 0
    return (a*b*m*hp_numerator**2
            - positive_rhs**2*(m-1)*(m-Q))


def check_pressure(m):
    weights = [F(0) for _ in range(m-1)]
    for start in range(m-Q):
        for j, pressure in enumerate(P):
            weights[start+j] += pressure
    assert sum(P) == BETA
    assert sum(weights) == BETA*(m-Q)
    assert min(weights) >= min(P)
    assert max(weights) <= BETA
    return {"block_size": m, "mass": str(sum(weights)),
            "minimum_weight": str(min(weights))}


def verify():
    h = h_bounds()
    candidates = {m: bound_interval(m, h) for m in range(7, 277)}
    best = candidates[275]
    for m, other in candidates.items():
        if m != 275:
            assert best[0] > other[1], (m, "interval comparison failed")
    assert derivative_sign_polynomial(275) < 0
    assert derivative_sign_polynomial(276) > 0
    assert DELTA*(276-Q) > F(276, 275)
    target = F(673111908530165, 10**15)
    assert best[0] > target
    baseline = tuple((655000*v-1305)/652504 for v in h)
    assert best[0] > baseline[1]
    gain = (best[0]-baseline[1], best[1]-baseline[0])
    p266 = phi_bounds(266)
    b266 = ((266*h[0]-BETA*(266-Q))/(266-p266[0]),
            (266*h[1]-BETA*(266-Q))/(266-p266[1]))
    return {
        "status": "EXACT_ARITHMETIC_PASSED",
        "scope": "Arithmetic and pressure mass only; existing local and analytic theorems are inputs.",
        "local_delta": str(DELTA), "local_beta": str(BETA),
        "q": Q, "optimal_integer_m": 275,
        "A": str(DELTA*(275-Q)),
        "Phi_A": show_interval(phi_bounds(275)),
        "H_MT": show_interval(h),
        "baseline": show_interval(baseline),
        "improved_bound": show_interval(best),
        "strict_rational_target": str(target),
        "gain_in_proportion": show_interval(gain),
        "gain_in_percentage_points": show_interval(tuple(100*v for v in gain)),
        "stronger_adjacent_pair_refinement": adjacent_pair_refinement(h),
        "prior_266_candidate_recovered": show_interval(b266),
        "integer_optimality": {
            "finite_comparisons": "all integers 7 <= m <= 276",
            "infinite_tail": "strict concavity in x=1/m and positive derivative at x=1/276",
            "derivative_sign_polynomial_275": derivative_sign_polynomial(275),
            "derivative_sign_polynomial_276": derivative_sign_polynomial(276),
        },
        "nearby_bounds": {str(m): show_interval(candidates[m])
                          for m in (262,263,264,266,274,275,276)},
        "pressure_checks": [check_pressure(m) for m in (7,262,266,275,1000)],
        "not_verified_here": ["seven-point local branch-and-bound replay",
                              "analytic zeta inputs", "Lean formalization"],
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = verify()
    rendered = json.dumps(result, indent=2, ensure_ascii=False)
    if args.output:
        args.output.write_text(rendered + "\n", encoding="utf-8")
    print(rendered)
