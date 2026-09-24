#!/usr/bin/env python3
"""Independent replay pilot for one shard of the pinned nine-point certificate.

The workflow installs trmdy/zeta-simple-zeros-673137 at the exact public
commit 1610b97b7895ff34982260f8dcaf04a0f7b82cf7, then runs this script.
It deliberately re-builds the rigorous w and w'' tables and checks their
SHA-256 hashes before replaying shard 0 of 96 of the final p=1/2500,
target=15211/2500000 certificate.

This is only a pilot: a full independent replay requires all 96 disjoint
shards (or a different exhaustive certificate proved independently).
"""

from zeta_ext.kernel import table_sha256
from zeta_ext.nine_point import certificate_spec
from zeta_ext.verify_general import build_tables, verify_general

EXPECTED_W = "2be38c2f2a5a4659200341fae9b2a926760e64ad04fa44ae214a77dd958c56e3"
EXPECTED_W2 = "580e9682f1171ead19595438ee83c9f4c5af837179060ec49d9faee88032f6d5"


def main() -> None:
    spec = certificate_spec(grid=4000, use_tangent=True)
    assert str(spec.pressure) == "1/2500"
    assert str(spec.target) == "15211/2500000"
    assert spec.q == 8
    assert spec.capacity_ok()

    tables = build_tables(spec)
    h0 = table_sha256(tables[0])
    h2 = table_sha256(tables[1])
    print("w_table_sha256=", h0)
    print("w_second_table_sha256=", h2)
    assert h0 == EXPECTED_W
    assert h2 == EXPECTED_W2

    report = verify_general(
        spec,
        progress_every=200_000,
        shard=0,
        shard_count=96,
        tables=tables,
    )
    print("\n".join(report.lines()))
    assert report.verified
    assert report.details["w_table_sha256"] == EXPECTED_W
    assert report.details["w_second_table_sha256"] == EXPECTED_W2
    print("STATUS: PINNED NINE-POINT SHARD 0/96 REPLAY PASSED")


if __name__ == "__main__":
    main()
