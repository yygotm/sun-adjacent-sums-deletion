"""Check all 525 finite cyclic three-deletion certificates independently.

Run with Python 3; no search, compiled program, or third-party package is used.
"""
import argparse
import json
import math
from pathlib import Path


def one_hole_cycle(n):
    k = n // 4
    top = 2 * k - 1 if n % 4 == 1 else 2 * k + 1
    return (list(range(2 * k + 2, n, 2)) + list(range(2, 2 * k + 1, 2))
            + list(range(top, 0, -2)) + list(range(n - 2, top + 1, -2)))


def verify(path):
    expected = {(n, t) for n in range(7, 48, 2) for t in range(2, n)}
    seen = set()
    edge_count = 0
    with path.open(encoding="utf-8-sig") as stream:
        for line in stream:
            row = json.loads(line)
            n, t = row["n"], row["t"]
            key = (n, t)
            assert key in expected and key not in seen, "invalid or duplicate case"
            seen.add(key)
            holes = {0, 1, t}
            cycle = row["cycle"]
            assert len(cycle) == n - 3 > 2
            assert all(type(x) is int and 0 <= x < n for x in cycle)
            assert len(set(cycle)) == len(cycle)
            assert set(cycle) == set(range(n)) - holes
            colors = [(cycle[i] + cycle[(i + 1) % len(cycle)]) % n
                      for i in range(len(cycle))]
            assert len(set(colors)) == len(cycle), "repeated cyclic sum"
            anchor, step = row["anchor"], row["multiplier"]
            assert anchor in holes
            assert math.gcd(step, n) == 1
            template = [(anchor + step * x) % n for x in one_hole_cycle(n)]
            assert [x for x in template if x not in holes] == cycle
            edge_count += len(colors)
    assert seen == expected and len(seen) == 525, "incomplete finite base"
    return {"pass": True, "cases": len(seen), "cyclicEdges": edge_count}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificate", nargs="?", type=Path,
                        default=Path(__file__).with_name("cyclic-finite-certificate.jsonl"))
    args = parser.parse_args()
    print(json.dumps(verify(args.certificate), sort_keys=True))
