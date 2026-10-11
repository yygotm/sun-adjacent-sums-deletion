"""Audit saved all-subset block counts using binomial coefficients and Burnside.

This checks coverage and recorded outcomes, not individual cycle witnesses.
Usage: python audit_all_subsets.py RUN_DIRECTORY [GROUP ...]
"""
import argparse
import itertools
import json
import math
from pathlib import Path


def check_group(root, name):
    directory = root / name
    summary = json.loads((directory / "summary.json").read_text(encoding="utf-8-sig"))
    dims = summary["radices"]
    n = math.prod(dims)
    assert n == summary["order"]
    blocks = [json.loads(line) for line in
              (directory / "blocks.jsonl").read_text(encoding="utf-8-sig").splitlines()]
    blocks.sort(key=lambda b: b["Id"])
    end = 0
    by_size, normalized, all_sets = [0] * (n + 1), [0] * (n + 1), [0] * (n + 1)
    for index, block in enumerate(blocks):
        assert block["Id"] == index and block["Start"] == end
        end = block["End"]
        assert block["Start"] < end <= 2 ** (n - 1)
        excluded = sum(block["Start"] <= x < end for x in
                       [0] + [2 ** j for j in range(n - 1)])
        assert block["Candidates"] == end - block["Start"] - excluded
        assert block["Counterexamples"] == block["Unresolved"] == []
        assert block["Representatives"] == sum(block["BySize"])
        assert block["NormalizedCovered"] == sum(block["NormalizedBySize"])
        assert block["AllCovered"] == sum(block["AllBySize"])
        for size in range(3, n + 1):
            by_size[size] += block["BySize"][size]
            normalized[size] += block["NormalizedBySize"][size]
            all_sets[size] += block["AllBySize"][size]
    assert end == 2 ** (n - 1)
    orders = [math.lcm(*(m // math.gcd(x, m) for x, m in zip(point, dims)))
              for point in itertools.product(*(range(m) for m in dims))]
    recorded = {row["size"]: row for row in summary["bySize"]}
    assert set(recorded) == set(range(3, n + 1))
    for size in range(3, n + 1):
        fixed = sum(math.comb(n // d, size // d) for d in orders if size % d == 0)
        assert fixed % n == 0
        assert by_size[size] == fixed // n == recorded[size]["representatives"]
        assert normalized[size] == math.comb(n - 1, size - 1) == recorded[size]["normalized"]
        assert all_sets[size] == math.comb(n, size) == recorded[size]["all"]
    assert summary["counterexampleRepresentatives"] == summary["unresolvedRepresentatives"] == []
    assert summary["coverageVerified"] and summary["independentWitnessVerification"]
    assert summary["representatives"] == sum(by_size)
    assert summary["normalizedSubsets"] == sum(normalized) == 2 ** (n - 1) - n
    assert summary["allSubsets"] == sum(all_sets) == 2 ** n - 1 - n - math.comb(n, 2)
    return {"group": name, "blocks": len(blocks), "representatives": sum(by_size),
            "normalized": sum(normalized), "allSubsets": sum(all_sets), "pass": True}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("root", type=Path)
    parser.add_argument("groups", nargs="*")
    args = parser.parse_args()
    names = args.groups or sorted(p.name for p in args.root.iterdir()
                                  if p.is_dir() and (p / "summary.json").is_file())
    assert names, "no saved groups found"
    result = [check_group(args.root, name) for name in names]
    print(json.dumps({"pass": True, "groups": result,
                      "representatives": sum(r["representatives"] for r in result),
                      "normalized": sum(r["normalized"] for r in result),
                      "allSubsets": sum(r["allSubsets"] for r in result)}, indent=2))
