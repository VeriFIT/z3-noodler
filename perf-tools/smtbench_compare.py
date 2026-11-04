#!/usr/bin/env python3
"""Compares two solvers of a smtbench_run.py CSV per set.

A run is solved if it answers sat/unsat; it is wrong if an answer contradicts the :status of the formula or the
sat/unsat answer of the other solver.
Usage: smtbench_compare.py RESULTS.csv OLD NEW
"""
import collections
import csv
import sys


def answers(result):
    return [a for a in result.split() if a in ("sat", "unsat")]


def outcome(row, other):
    result = row["result"]
    if result == "timeout" or result.startswith("crash") or result in ("error", "other"):
        return result.split("(")[0]
    got = result.split()
    if not answers(result):
        return "unknown"
    expected = row["expected"].split()
    for i, a in enumerate(got):
        if a not in ("sat", "unsat"):
            continue
        if i < len(expected) and expected[i] in ("sat", "unsat") and expected[i] != a:
            return "WRONG"
    if other is not None:
        other_got = other["result"].split()
        if len(other_got) == len(got) and any(a in ("sat", "unsat") and b in ("sat", "unsat") and a != b
                                              for a, b in zip(got, other_got)):
            return "DISAGREE"
    return "solved" if all(a in ("sat", "unsat") for a in got) else "unknown"


def main():
    path, old, new = sys.argv[1:4]
    runs = collections.defaultdict(dict)
    with open(path) as f:
        for row in csv.DictReader(f, delimiter=";"):
            runs[row["file"]][row["solver"]] = row
    pairs = {f: r for f, r in runs.items() if old in r and new in r}
    sets = sorted({r[old]["set"] for r in pairs.values()})
    kinds = ["solved", "WRONG", "DISAGREE", "timeout", "unknown", "error", "crash", "other"]
    print(f"{len(pairs)} formulas with both runs\n")
    print(f"{'set':20} {'run':5} " + " ".join(f"{k:>8}" for k in kinds) + f" {'time [s]':>9} {'both [s]':>9} {'ratio':>6}")
    changes = collections.Counter()
    examples = collections.defaultdict(list)
    slow = []
    totals = {s: collections.Counter() for s in (old, new)}
    for name in sets + ["total"]:
        files = [f for f, r in pairs.items() if name == "total" or r[old]["set"] == name]
        counts = {s: collections.Counter() for s in (old, new)}
        time = {s: 0.0 for s in (old, new)}
        both = {s: 0.0 for s in (old, new)}
        for f in files:
            o = {s: outcome(pairs[f][s], pairs[f][t]) for s, t in ((old, new), (new, old))}
            for s in (old, new):
                counts[s][o[s]] += 1
                time[s] += float(pairs[f][s]["seconds"])
            if o[old] == o[new] == "solved":
                for s in (old, new):
                    both[s] += float(pairs[f][s]["seconds"])
                a, b = float(pairs[f][old]["seconds"]), float(pairs[f][new]["seconds"])
                if name == "total":
                    slow.append((b - a, f, a, b))
            if name == "total" and o[old] != o[new]:
                changes[(pairs[f][old]["set"], o[old], o[new])] += 1
                examples[(pairs[f][old]["set"], o[old], o[new])].append(f.split("/")[-1])
        for s in (old, new):
            ratio = f"{both[new] / both[old]:.2f}" if s == new and both[old] > 0 else ""
            print(f"{name:20} {s:5} " + " ".join(f"{counts[s][k]:>8}" for k in kinds)
                  + f" {time[s]:>9.1f} {both[s]:>9.1f} {ratio:>6}")
    print("\nChanged outcomes (set: old -> new):")
    for (name, a, b), n in sorted(changes.items(), key=lambda x: (x[0][0], -x[1])):
        print(f"  {name:20} {a:>8} -> {b:<8} {n:>5}  {' '.join(examples[(name, a, b)][:4])}")
    slow.sort(reverse=True)
    print("\nBiggest slowdowns (solved by both):")
    for d, f, a, b in slow[:15]:
        print(f"  {f:90} {a:7.3f} -> {b:7.3f}")
    print("\nBiggest speedups (solved by both):")
    for d, f, a, b in sorted(slow)[:8]:
        print(f"  {f:90} {a:7.3f} -> {b:7.3f}")


if __name__ == "__main__":
    main()
