# Standalone rigorous verifier for the nonuniform seven-point certificate.
# Requires: python-flint >= 0.9.0
from __future__ import annotations
import hashlib, itertools, math, struct, time, sys
from importlib.metadata import version as package_version
from pathlib import Path
from dataclasses import dataclass
from typing import Any, Dict, Iterable, List, Optional, Sequence, Tuple
from flint import arb, ctx, fmpq





def down_ratio(numerator: int, denominator: int) -> float:
    """A binary64 lower bound for a nonnegative rational number."""

    if numerator < 0 or denominator <= 0:
        raise ValueError("down_ratio expects numerator >= 0 and denominator > 0")
    if numerator == 0:
        return 0.0
    return math.nextafter(numerator / denominator, -math.inf)


def up_ratio(numerator: int, denominator: int) -> float:
    """A binary64 upper bound for a nonnegative rational number."""

    if numerator < 0 or denominator <= 0:
        raise ValueError("up_ratio expects numerator >= 0 and denominator > 0")
    if numerator == 0:
        return 0.0
    return math.nextafter(numerator / denominator, math.inf)


def down_mul(left: float, right: float) -> float:
    """A lower bound for the product of two nonnegative lower bounds."""

    if left < 0.0 or right < 0.0:
        raise ValueError("down_mul expects nonnegative inputs")
    if left == 0.0 or right == 0.0:
        return 0.0
    return max(0.0, math.nextafter(left * right, -math.inf))


def down_add(left: float, right: float) -> float:
    """A lower bound for the sum of two nonnegative lower bounds."""

    if left < 0.0 or right < 0.0:
        raise ValueError("down_add expects nonnegative inputs")
    if left == 0.0 and right == 0.0:
        return 0.0
    return max(0.0, math.nextafter(left + right, -math.inf))







def configure_arb(precision: int = 128) -> None:
    """Set the working precision used to produce cell enclosures."""

    if precision < 80:
        raise ValueError("at least 80 bits are required")
    ctx.prec = precision


@dataclass(frozen=True)
class KernelConstants:
    sqrt_two: arb
    inv_sqrt_two: arb
    pi: arb
    k_zero: arb


def kernel_constants() -> KernelConstants:
    sqrt_two = arb(2).sqrt()
    inv_sqrt_two = 1 / sqrt_two
    return KernelConstants(
        sqrt_two=sqrt_two,
        inv_sqrt_two=inv_sqrt_two,
        pi=arb.pi(),
        k_zero=sqrt_two * inv_sqrt_two.sin(),
    )


def normalized_kernel(x: arb, constants: KernelConstants | None = None) -> arb:
    r"""Enclose k(x) = K(x)/K(0) using the entire sinc representation.

    Here K(x) = integral_{-1/2}^{1/2} cos(sqrt(2)t) cos(2 pi x t) dt.
    The sinc form has no removable-singularity special cases.
    """

    c = constants or kernel_constants()
    frequency = 2 * c.pi * x
    left = ((c.sqrt_two - frequency) / 2).sinc()
    right = ((c.sqrt_two + frequency) / 2).sinc()
    return ((left + right) / 2) / c.k_zero


def squared_kernel_derivatives(
    x: arb, constants: KernelConstants | None = None
) -> tuple[arb, arb, arb]:
    r"""Return enclosures for w(x)=k(x)^2 and its first two derivatives.

    This formula divides by z^3 and is therefore used only for x >= 0.95 in
    the 7-point verifier; the entire sinc formula remains the general kernel
    evaluator.
    """

    c = constants or kernel_constants()
    z_left = c.pi * x - c.inv_sqrt_two
    z_right = c.pi * x + c.inv_sqrt_two

    def sinc_derivatives(z: arb) -> tuple[arb, arb, arb]:
        sine = z.sin()
        cosine = z.cos()
        z_squared = z * z
        value = sine / z
        first = (z * cosine - sine) / z_squared
        second = ((2 - z_squared) * sine - 2 * z * cosine) / (z_squared * z)
        return value, first, second

    left, left_prime, left_second = sinc_derivatives(z_left)
    right, right_prime, right_second = sinc_derivatives(z_right)
    raw = (left + right) / 2
    raw_prime = c.pi * (left_prime + right_prime) / 2
    raw_second = c.pi * c.pi * (left_second + right_second) / 2
    normalization_squared = c.k_zero * c.k_zero

    value = raw * raw / normalization_squared
    first = 2 * raw * raw_prime / normalization_squared
    second = 2 * (raw_prime * raw_prime + raw * raw_second) / normalization_squared
    return value, first, second


def closed_cell(index: int, grid: int) -> arb:
    """Return the exact ball [index/grid, (index+1)/grid]."""

    if index < 0 or grid <= 0:
        raise ValueError("index must be nonnegative and grid must be positive")
    return arb(fmpq(2 * index + 1, 2 * grid), fmpq(1, 2 * grid))


def _arb_nonnegative_lower_to_float(value: arb) -> float:
    """Convert an Arb nonnegative lower endpoint to a widened binary64 bound."""

    candidate = float(value.lower())
    if candidate <= 0.0:
        return 0.0
    return math.nextafter(candidate, -math.inf)


def arb_lower_to_float(value: arb) -> float:
    """A widened binary64 lower bound for a signed Arb enclosure."""

    return math.nextafter(float(value.lower()), -math.inf)


def squared_kernel_cell_lower(
    index: int, grid: int, constants: KernelConstants | None = None
) -> float:
    """Rigorous binary64 lower bound for min k(x)^2 on one closed cell."""

    enclosure = normalized_kernel(closed_cell(index, grid), constants)
    absolute_lower = _arb_nonnegative_lower_to_float(enclosure.abs_lower())
    return down_mul(absolute_lower, absolute_lower)


def build_kernel_table(grid: int, cell_count: int, precision: int = 128) -> List[float]:
    """Build rigorous lower bounds for k^2 on consecutive grid cells."""

    configure_arb(precision)
    constants = kernel_constants()
    return [squared_kernel_cell_lower(i, grid, constants) for i in range(cell_count)]


def build_second_derivative_lower_table(
    grid: int, cell_count: int, start_index: int, precision: int = 128
) -> List[float]:
    """Build lower bounds for w'' on cells safely away from the removable pole."""

    configure_arb(precision)
    constants = kernel_constants()
    values = [-math.inf] * cell_count
    for index in range(start_index, cell_count):
        _, _, second = squared_kernel_derivatives(closed_cell(index, grid), constants)
        values[index] = arb_lower_to_float(second.lower())
    return values


def table_sha256(values: Sequence[float]) -> str:
    """Hash the exact binary64 table representation."""

    digest = hashlib.sha256()
    for value in values:
        digest.update(struct.pack(">d", value))
    return digest.hexdigest()


class RangeMinimum:
    """O(1) idempotent sparse-table range-minimum queries."""

    def __init__(self, values: Sequence[float]):
        if not values:
            raise ValueError("values must be nonempty")
        self._length = len(values)
        levels: List[List[float]] = [list(values)]
        width = 1
        while 2 * width <= self._length:
            previous = levels[-1]
            half = width
            width *= 2
            levels.append(
                [
                    min(previous[i], previous[i + half])
                    for i in range(self._length - width + 1)
                ]
            )
        self._levels = levels

    @property
    def length(self) -> int:
        return self._length

    def query(self, left: int, right: int) -> float:
        """Return min(values[left:right+1])."""

        if left < 0 or right < left or right >= self._length:
            raise IndexError((left, right, self._length))
        level = (right - left + 1).bit_length() - 1
        width = 1 << level
        row = self._levels[level]
        return min(row[left], row[right - width + 1])

from dataclasses import dataclass
from typing import Any, Dict
@dataclass(frozen=True)
class VerificationReport:
    certificate: str
    verified: bool
    target: str
    grid: int
    precision_bits: int
    kernel_table_sha256: str
    nodes: int
    pruned: int
    splits: int
    maximum_depth: int
    initial_boxes: int
    elapsed_seconds: float
    details: Dict[str, Any]
    def to_text(self):
        parts=[f"certificate={self.certificate}",f"verified={str(self.verified).lower()}",f"target={self.target}",f"grid={self.grid}",f"precision_bits={self.precision_bits}",f"kernel_table_sha256={self.kernel_table_sha256}",f"nodes={self.nodes}",f"pruned={self.pruned}",f"splits={self.splits}",f"maximum_depth={self.maximum_depth}",f"initial_boxes={self.initial_boxes}",f"elapsed_seconds={self.elapsed_seconds:.6f}"]
        parts += [f"{k}={self.details[k]}" for k in sorted(self.details)]
        return "\n".join(parts)




import itertools
import math
import time
from typing import Iterable, List, Optional, Sequence, Tuple

from flint import arb, fmpq



GRID = 4_000
PRECISION_BITS = 256
TARGET_NUMERATOR = 39
TARGET_DENOMINATOR = 10_000
# Symmetric nonuniform pressure (2714,3733,3553,3553,3733,2714)/1e7.
# The six coefficients sum to 1/500, exactly matching the original global span cost.
PRESSURE_NUMERATORS = (2714, 3733, 3553, 3553, 3733, 2714)
PRESSURE_DENOMINATOR = 10_000_000
PRESSURE_CUTOFF_CELLS = 57_480

# c_s = 2/(7-s), where s is the number of gaps crossed by a pair.
COEFFICIENTS = {
    1: down_ratio(1, 3),
    2: down_ratio(2, 5),
    3: down_ratio(1, 2),
    4: down_ratio(2, 3),
    5: 1.0,
    6: 2.0,
}
COEFFICIENTS_UP = {
    1: up_ratio(1, 3),
    2: up_ratio(2, 5),
    3: up_ratio(1, 2),
    4: up_ratio(2, 3),
    5: 1.0,
    6: 2.0,
}
COEFFICIENT_RATIONALS = {
    1: fmpq(1, 3),
    2: fmpq(2, 5),
    3: fmpq(1, 2),
    4: fmpq(2, 3),
    5: fmpq(1),
    6: fmpq(2),
}

CellRange = Tuple[int, int]
SevenBox = Tuple[CellRange, CellRange, CellRange, CellRange, CellRange, CellRange]


def _components(indices: Iterable[int]) -> List[CellRange]:
    result: List[List[int]] = []
    for index in indices:
        if not result or index > result[-1][1] + 1:
            result.append([index, index])
        else:
            result[-1][1] = index
    return [(left, right) for left, right in result]


def verify_seven(progress_every: int = 0, precision_bits: int = PRECISION_BITS) -> VerificationReport:
    r"""Prove F6_nonuniform(g1,...,g6) >= 39/10000 for all nonnegative gaps.

    Arb first encloses k(x)^2 on a fixed 1/4000 grid. The second phase uses
    only lower bounds, outward-rounded binary64 arithmetic, range minima, and
    exhaustive subdivision of the remaining six-dimensional cell boxes.
    """

    started = time.perf_counter()
    cell_count = PRESSURE_CUTOFF_CELLS + 8
    table = build_kernel_table(GRID, cell_count, precision_bits)
    ranges = RangeMinimum(table)
    second_table = build_second_derivative_lower_table(
        GRID, cell_count, start_index=3_800, precision=precision_bits
    )
    second_ranges = RangeMinimum(second_table)
    constants = kernel_constants()
    target_upper = up_ratio(TARGET_NUMERATOR, TARGET_DENOMINATOR)

    def kernel_min(left: int, right: int) -> float:
        # If the interval extends past the pressure cutoff, zero is still a
        # rigorous lower bound for the nonnegative function w=k^2.
        if right >= ranges.length:
            return 0.0
        return ranges.query(left, right)

    def second_derivative_min(left: int, right: int) -> float:
        if right >= second_ranges.length:
            return float("-inf")
        return second_ranges.query(left, right)

    # Coordinate-dependent one-body filters U_i(g)=p_i g+w(g)/3.
    components_by_coordinate: List[List[CellRange]] = []
    for pressure_numerator in PRESSURE_NUMERATORS:
        surviving_cells: List[int] = []
        for index in range(PRESSURE_CUTOFF_CELLS):
            one_body = down_ratio(
                pressure_numerator * index, GRID * PRESSURE_DENOMINATOR
            )
            one_body = down_add(one_body, down_mul(COEFFICIENTS[1], table[index]))
            if one_body < target_upper:
                surviving_cells.append(index)
        components_by_coordinate.append(_components(surviving_cells))

    stack: List[Tuple[SevenBox, int]] = [
        (tuple(parts), 0)  # type: ignore[arg-type]
        for parts in itertools.product(*components_by_coordinate)
    ]
    initial_boxes = len(stack)
    nodes = pruned = splits = maximum_depth = 0
    pressure_pruned = interval_pruned = 0
    tangent_pruned = 0

    def box_lower(box: SevenBox) -> float:
        lows = [part[0] for part in box]
        highs = [part[1] for part in box]
        low_prefix = [0]
        high_prefix = [0]
        for low, high in zip(lows, highs):
            low_prefix.append(low_prefix[-1] + low)
            high_prefix.append(high_prefix[-1] + high)

        result = 0.0
        for coordinate, low in enumerate(lows):
            result = down_add(
                result,
                down_ratio(
                    PRESSURE_NUMERATORS[coordinate] * low,
                    GRID * PRESSURE_DENOMINATOR,
                ),
            )
        for span in range(1, 7):
            coefficient = COEFFICIENTS[span]
            for start in range(7 - span):
                left = low_prefix[start + span] - low_prefix[start]
                # A sum of `span` closed cells has this inclusive cell range.
                right = (
                    high_prefix[start + span] - high_prefix[start] + span - 1
                )
                result = down_add(
                    result,
                    down_mul(coefficient, kernel_min(left, right)),
                )
        return result

    def coefficient_times_signed_lower(span: int, lower: float) -> float:
        if lower == float("-inf"):
            return lower
        coefficient = COEFFICIENTS[span] if lower >= 0.0 else COEFFICIENTS_UP[span]
        # Multiplication is rounded to nearest first, then widened down.
        return math.nextafter(coefficient * lower, -math.inf)

    def float_ldl_is_positive(matrix: List[List[float]]) -> bool:
        """Cheap heuristic; success is rechecked with Arb below."""

        lower = [[0.0] * 6 for _ in range(6)]
        diagonal = [0.0] * 6
        for column in range(6):
            pivot = matrix[column][column]
            for previous in range(column):
                pivot -= (
                    lower[column][previous]
                    * lower[column][previous]
                    * diagonal[previous]
                )
            if pivot <= 1e-12:
                return False
            diagonal[column] = pivot
            lower[column][column] = 1.0
            for row in range(column + 1, 6):
                value = matrix[row][column]
                for previous in range(column):
                    value -= (
                        lower[row][previous]
                        * lower[column][previous]
                        * diagonal[previous]
                    )
                lower[row][column] = value / pivot
        return True

    def exact_float(value: float) -> arb:
        numerator, denominator = value.as_integer_ratio()
        return arb(fmpq(numerator, denominator))

    def arb_ldl_is_positive(terms: Sequence[Tuple[int, int, float]]) -> bool:
        """Prove the rational lower-Hessian matrix positive definite."""

        matrix = [[arb(0) for _ in range(6)] for _ in range(6)]
        for start, span, coefficient in terms:
            exact = exact_float(coefficient)
            for row in range(start, start + span):
                for column in range(start, start + span):
                    matrix[row][column] += exact

        lower = [[arb(0) for _ in range(6)] for _ in range(6)]
        diagonal = [arb(0) for _ in range(6)]
        for column in range(6):
            lower[column][column] = arb(1)
            pivot = matrix[column][column]
            for previous in range(column):
                pivot -= (
                    lower[column][previous]
                    * lower[column][previous]
                    * diagonal[previous]
                )
            if not (pivot > 0):
                return False
            diagonal[column] = pivot
            for row in range(column + 1, 6):
                value = matrix[row][column]
                for previous in range(column):
                    value -= (
                        lower[row][previous]
                        * lower[column][previous]
                        * diagonal[previous]
                    )
                lower[row][column] = value / pivot
        return True

    def convex_tangent_lower(box: SevenBox) -> Optional[arb]:
        """Return a rigorous tangent lower bound when convexity is certified."""

        low_prefix = [0]
        high_prefix = [0]
        for low, high in box:
            low_prefix.append(low_prefix[-1] + low)
            high_prefix.append(high_prefix[-1] + high)

        terms: List[Tuple[int, int, float]] = []
        heuristic = [[0.0] * 6 for _ in range(6)]
        for span in range(1, 7):
            for start in range(7 - span):
                left = low_prefix[start + span] - low_prefix[start]
                right = (
                    high_prefix[start + span] - high_prefix[start] + span - 1
                )
                second_lower = second_derivative_min(left, right)
                scalar = coefficient_times_signed_lower(span, second_lower)
                if scalar == float("-inf"):
                    return None
                terms.append((start, span, scalar))
                for row in range(start, start + span):
                    for column in range(start, start + span):
                        heuristic[row][column] += scalar

        if not float_ldl_is_positive(heuristic):
            return None
        if not arb_ldl_is_positive(terms):
            return None

        midpoints = [fmpq(low + high + 1, 2 * GRID) for low, high in box]
        radii = [fmpq(high - low + 1, 2 * GRID) for low, high in box]
        value = sum(
            (
                arb(fmpq(PRESSURE_NUMERATORS[i], PRESSURE_DENOMINATOR))
                * arb(midpoints[i])
                for i in range(6)
            ),
            arb(0),
        )
        gradient = [
            arb(fmpq(PRESSURE_NUMERATORS[i], PRESSURE_DENOMINATOR))
            for i in range(6)
        ]

        for span in range(1, 7):
            coefficient = arb(COEFFICIENT_RATIONALS[span])
            for start in range(7 - span):
                point = sum(midpoints[start : start + span], fmpq(0))
                potential, derivative, _ = squared_kernel_derivatives(
                    arb(point), constants
                )
                value += coefficient * potential
                for coordinate in range(start, start + span):
                    gradient[coordinate] += coefficient * derivative

        lower = value
        for derivative, radius in zip(gradient, radii):
            lower -= derivative.abs_upper() * arb(radius)
        return lower

    while stack:
        box, depth = stack.pop()
        nodes += 1
        maximum_depth = max(maximum_depth, depth)

        pressure_lower = sum(
            (
                arb(
                    fmpq(
                        PRESSURE_NUMERATORS[i] * box[i][0],
                        GRID * PRESSURE_DENOMINATOR,
                    )
                )
                for i in range(6)
            ),
            arb(0),
        )
        if pressure_lower >= arb(fmpq(TARGET_NUMERATOR, TARGET_DENOMINATOR)):
            pruned += 1
            pressure_pruned += 1
            continue

        lower = box_lower(box)
        if lower >= target_upper:
            pruned += 1
            interval_pruned += 1
            continue

        tangent_lower = convex_tangent_lower(box)
        if tangent_lower is not None and tangent_lower >= arb(
            fmpq(TARGET_NUMERATOR, TARGET_DENOMINATOR)
        ):
            pruned += 1
            tangent_pruned += 1
            continue

        widths = [right - left for left, right in box]
        if max(widths) == 0:
            raise RuntimeError(
                "7-point certificate failed at a terminal cell: "
                f"box={box}, lower={lower.hex()}"
            )

        splits += 1
        coordinate = max(range(6), key=widths.__getitem__)
        left, right = box[coordinate]
        midpoint = (left + right) // 2
        lower_half = list(box)
        upper_half = list(box)
        lower_half[coordinate] = (left, midpoint)
        upper_half[coordinate] = (midpoint + 1, right)
        stack.append((tuple(lower_half), depth + 1))  # type: ignore[arg-type]
        stack.append((tuple(upper_half), depth + 1))  # type: ignore[arg-type]

        if progress_every and nodes % progress_every == 0:
            print(f"seven: nodes={nodes} pending={len(stack)} depth={maximum_depth}")

    elapsed = time.perf_counter() - started
    component_text = " | ".join(
        ";".join(f"[{a},{b}]" for a, b in components)
        for components in components_by_coordinate
    )
    return VerificationReport(
        certificate="seven-point",
        verified=True,
        target="F6_nonuniform >= 39/10000",
        grid=GRID,
        precision_bits=precision_bits,
        kernel_table_sha256=table_sha256(table),
        nodes=nodes,
        pruned=pruned,
        splits=splits,
        maximum_depth=maximum_depth,
        initial_boxes=initial_boxes,
        elapsed_seconds=elapsed,
        details={
            "pressure_pruned": pressure_pruned,
            "interval_pruned": interval_pruned,
            "tangent_pruned": tangent_pruned,
            "second_derivative_table_sha256": table_sha256(second_table),
            "surviving_gap_components_cells": component_text,
            "surviving_gap_components_count": sum(
                len(parts) for parts in components_by_coordinate
            ),
            "pressure_numerators": str(PRESSURE_NUMERATORS),
            "pressure_denominator": PRESSURE_DENOMINATOR,
            "python_version": sys.version.split()[0],
            "python_flint_version": package_version("python-flint"),
            "verifier_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        },
    )

if __name__ == "__main__":
    import argparse
    parser=argparse.ArgumentParser()
    parser.add_argument("--progress-every", type=int, default=100000)
    parser.add_argument("--precision", type=int, default=PRECISION_BITS,
                        help="Arb working precision in bits (default: 256)")
    args=parser.parse_args()
    report=verify_seven(progress_every=args.progress_every, precision_bits=args.precision)
    print(report.to_text())
