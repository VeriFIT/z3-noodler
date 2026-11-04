#!/usr/bin/env python3
"""Appends a per-set summary of benchmark results to perf-tools/results/SUMMARY.md.

Reads smtbench_run.py CSVs (file;set;solver;expected;result;seconds) and the CSVs of ecma2020-smt-bench's run.py
(file;family;expected;result;seconds;message, one solver per file, named by --solver).
Usage: summarize.py TITLE [--note TEXT] [--solver NAME=CSV...] CSV...
"""
import argparse
import collections
import csv
import datetime
import os

SUMMARY = os.path.join(os.path.dirname(os.path.abspath(__file__)), "results", "SUMMARY.md")


def read(path, solver_name=None):
    with open(path) as f:
        for row in csv.DictReader(f, delimiter=";"):
            name = row.get("set") or row.get("family")
            solver = row.get("solver") or solver_name
            yield name, solver, row["expected"], row["result"], float(row["seconds"])


def outcome(expected, result):
    if result == "timeout":
        return "timeout"
    answers = result.split()
    if not answers or any(a not in ("sat", "unsat") for a in answers):
        return "unknown" if answers and answers[0] == "unknown" else "other"
    exp = expected.split()
    if any(e in ("sat", "unsat") and e != a for e, a in zip(exp, answers)):
        return "wrong"
    return "solved"


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("title")
    parser.add_argument("--note", default="")
    parser.add_argument("--solver", nargs="*", default=[], help="NAME=CSV of run.py with one solver")
    parser.add_argument("csvs", nargs="*")
    args = parser.parse_args()

    stats = collections.defaultdict(lambda: collections.defaultdict(list))
    for spec in args.solver:
        name, path = spec.split("=", 1)
        for s, solver, expected, result, seconds in read(path, name):
            stats[s][solver].append((outcome(expected, result), seconds))
    for path in args.csvs:
        for s, solver, expected, result, seconds in read(path):
            stats[s][solver].append((outcome(expected, result), seconds))

    lines = [f"\n## {args.title} ({datetime.date.today()})\n"]
    if args.note:
        lines.append(args.note + "\n")
    lines.append("| set | solver | formulas | solved | wrong | timeout | other | mean time [s] | mean time of solved [s] |")
    lines.append("|---|---|---|---|---|---|---|---|---|")
    totals = collections.defaultdict(list)
    for s in sorted(stats):
        for solver in sorted(stats[s]):
            runs = stats[s][solver]
            totals[solver] += runs
            lines.append(row(s, solver, runs))
    for solver in sorted(totals):
        lines.append(row("**total**", solver, totals[solver]))
    os.makedirs(os.path.dirname(SUMMARY), exist_ok=True)
    with open(SUMMARY, "a") as f:
        f.write("\n".join(lines) + "\n")
    print("\n".join(lines))


def row(s, solver, runs):
    count = collections.Counter(o for o, _ in runs)
    solved = [t for o, t in runs if o == "solved"]
    mean = sum(t for _, t in runs) / len(runs)
    mean_solved = sum(solved) / len(solved) if solved else 0
    other = len(runs) - count["solved"] - count["wrong"] - count["timeout"]
    return (f"| {s} | {solver} | {len(runs)} | {count['solved']} | {count['wrong']} | {count['timeout']} | {other} "
            f"| {mean:.3f} | {mean_solved:.3f} |")


if __name__ == "__main__":
    main()
