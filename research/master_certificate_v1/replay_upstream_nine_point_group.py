#!/usr/bin/env python3
"""Replay pinned shards of the 96-shard nine-point certificate.

Two modes are supported:

  --shard j   replay exactly one original shard j/95;
  --group g   replay the historical 16-shard group g/5.

The one-shard mode is used by CI because some shards take long enough that
packing sixteen into a 60-minute job can be cancelled before completion.
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
    mode = ap.add_mutually_exclusive_group(required=True)
    mode.add_argument("--shard", type=int, choices=range(SHARD_COUNT))
    mode.add_argument("--group", type=int, choices=range(GROUP_COUNT))
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

    if args.shard is not None:
        shards = [args.shard]
        label = f"SHARD {args.shard:02d}/95"
    else:
        start = args.group * GROUP_SIZE
        stop = start + GROUP_SIZE
        shards = list(range(start, stop))
        label = f"GROUP {args.group}/5 shards={start}..{stop-1}"

    total_nodes = total_pruned = total_splits = 0
    max_depth = 0

    for shard in shards:
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
            f"pruned={report.pruned} splits={report.splits} "
            f"depth={report.maximum_depth} seconds={time.monotonic()-ts:.3f}",
            flush=True,
        )

    print(
        f"{label} PASS nodes={total_nodes} pruned={total_pruned} "
        f"splits={total_splits} max_depth={max_depth} "
        f"elapsed={time.monotonic()-t0:.3f}",
        flush=True,
    )
    print("STATUS: CERTIFICATE REPLAY PASSED", flush=True)


if __name__ == "__main__":
    main()
