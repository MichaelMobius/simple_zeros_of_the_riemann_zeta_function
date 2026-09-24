#!/usr/bin/env python3
"""Replay one 16-shard group of the pinned 96-shard nine-point certificate.

The rigorous tables are built once per process and reused for sixteen disjoint
shards. Six concurrent group jobs therefore cover all 96 shards while avoiding
96 repetitions of the expensive table construction.
"""

from __future__ import annotations

import argparse
import time

from zeta_ext.kernel import table_sha256
from zeta_ext.nine_point import certificate_spec
from zeta_ext.verify_general import build_tables, verify_general

EXPECTED_W = "2be38c2f2a5a4659200341fae9b2a926760e64ad04fa44ae214a77dd958c56e3"
EXPECTED_W2 = "580e9682f1171ead19595438ee83c9f4c5af837179060ec49d9faee88032f6d5"
SHARD_COUNT = 96
GROUP_SIZE = 16
GROUP_COUNT = SHARD_COUNT // GROUP_SIZE


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--group", type=int, required=True, choices=range(GROUP_COUNT))
    args = ap.parse_args()

    spec = certificate_spec(grid=4000, use_tangent=True)
    assert str(spec.pressure) == "1/2500"
    assert str(spec.target) == "15211/2500000"
    assert spec.q == 8
    assert spec.capacity_ok()

    t0 = time.monotonic()
    tables = build_tables(spec)
    h0 = table_sha256(tables[0])
    h2 = table_sha256(tables[1])
    print("w_table_sha256=", h0, flush=True)
    print("w_second_table_sha256=", h2, flush=True)
    assert h0 == EXPECTED_W
    assert h2 == EXPECTED_W2

    start = args.group * GROUP_SIZE
    stop = start + GROUP_SIZE
    total_nodes = total_pruned = total_splits = 0
    max_depth = 0

    for shard in range(start, stop):
        ts = time.monotonic()
        report = verify_general(
            spec,
            progress_every=0,
            shard=shard,
            shard_count=SHARD_COUNT,
            tables=tables,
        )
        assert report.verified, f"shard {shard} failed"
        assert report.details["w_table_sha256"] == EXPECTED_W
        assert report.details["w_second_table_sha256"] == EXPECTED_W2
        total_nodes += report.nodes
        total_pruned += report.pruned
        total_splits += report.splits
        max_depth = max(max_depth, report.maximum_depth)
        print(
            f"SHARD {shard:02d}/95 PASS nodes={report.nodes} "
            f"depth={report.maximum_depth} seconds={time.monotonic()-ts:.3f}",
            flush=True,
        )

    print(
        f"GROUP {args.group}/5 PASS shards={start}..{stop-1} "
        f"nodes={total_nodes} pruned={total_pruned} splits={total_splits} "
        f"max_depth={max_depth} elapsed={time.monotonic()-t0:.3f}",
        flush=True,
    )
    print("STATUS: FULL-CERTIFICATE GROUP REPLAY PASSED", flush=True)


if __name__ == "__main__":
    main()
