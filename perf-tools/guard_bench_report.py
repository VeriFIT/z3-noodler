#!/usr/bin/env python3
"""Markdown report of a smtbench_run.py benchmark of several solvers against a baseline solver.

Only formulas with a run of every solver are counted; timeouts count as the timeout.
Optional groups come from a selection CSV (file, set, affected) of the formulas, e.g., formulas affected by a change and a control sample.
Usage: guard_bench_report.py BENCH.csv BASELINE [--selection SELECTION.csv] [--solvers a,b] [--timeout 30] [--out REPORT.md]
"""
import argparse

import numpy as np
import pandas as pd

ANSWERS = ("sat", "unsat")
QUANTILES = [0.5, 0.9, 0.95, 0.97, 0.98, 0.99]
EXTRA_QUANTILES = [0.9, 0.95, 0.97, 0.98, 0.99, 0.995, 0.999]


def outcome(row):
    result = row.result
    if result == "timeout":
        return "timeout"
    got = result.split()
    if not got or any(a not in ANSWERS for a in got):
        return "other"
    expected = row.expected.split()
    if any(e in ANSWERS and e != a for e, a in zip(expected, got)):
        return "wrong"
    return "solved"


def solver_order(name):
    """Solvers named NAME-NUMBER (e.g., qt-1e6) in the order of the numbers, after the other ones."""
    try:
        return 1, float(name.rsplit("-", 1)[-1])
    except ValueError:
        return 0, name


def load(bench, selection=None, solvers=None):
    # a formula of two sets is run twice
    runs = pd.read_csv(bench, sep=";").drop_duplicates(["file", "solver"])
    if solvers:
        runs = runs[runs.solver.isin(solvers)]
    runs["outcome"] = [outcome(r) for r in runs.itertuples()]
    solvers = sorted(runs.solver.unique(), key=solver_order)
    complete = runs.groupby("file").solver.nunique() == len(solvers)
    runs = runs[runs.file.isin(complete[complete].index)].copy()
    # a sat/unsat answer different from another solver's
    answers = runs[runs.outcome == "solved"].groupby("file").result.nunique()
    runs.loc[runs.file.isin(answers[answers > 1].index) & runs.outcome.eq("solved"), "outcome"] = "disagree"
    if selection:
        groups = pd.read_csv(selection).drop_duplicates("file").set_index("file").affected.map({True: "affected", False: "control"})
        runs["group"] = runs.file.map(groups).fillna("other")
    else:
        runs["group"] = "all"
    return runs, solvers


def distribution(runs, solvers, baseline):
    """Time quantiles per solver over all formulas and over the formulas solved by every solver, and the quantiles of the
    per-formula ratio of the time to the baseline's time on the latter."""
    solved_by_all = runs.groupby("file").outcome.agg(lambda o: (o == "solved").all())
    common = runs[runs.file.isin(solved_by_all[solved_by_all].index)]
    rows = {}
    for name, r in [("all", runs), ("common", common)]:
        for s in solvers:
            t = r[r.solver == s].seconds
            rows[(name, s)] = {"formulas": len(t), "total": t.sum(), "mean": t.mean(), **{f"p{q * 100:g}": t.quantile(q) for q in QUANTILES},
                               "max": t.max()}
    times = pd.DataFrame(rows).T
    times.index = [f"{name}: {s}" for name, s in times.index]
    wide = common.pivot(index="file", columns="solver", values="seconds").clip(lower=0.01)
    ratios = {}
    for s in solvers:
        if s == baseline:
            continue
        ratio = wide[s] / wide[baseline]
        ratios[s] = {"geometric_mean": np.exp(np.log(ratio).mean()), **{f"p{q * 100:g}": ratio.quantile(q) for q in [0.01, 0.05, 0.5, 0.95, 0.99]},
                     "faster_2x": int((ratio < 0.5).sum()), "slower_2x": int((ratio > 2).sum())}
    return times, pd.DataFrame(ratios).T


def totals(runs, solvers, baseline):
    """One row per solver: outcomes, the total time, and the time of the formulas solved by every solver relative to the baseline."""
    solved_by_all = runs.groupby("file").outcome.agg(lambda o: (o == "solved").all())
    common = runs[runs.file.isin(solved_by_all[solved_by_all].index)]
    common_time = common.groupby("solver").seconds.sum()
    rows = {}
    for s in solvers:
        r = runs[runs.solver == s]
        counts = r.outcome.value_counts()
        rows[s] = {"formulas": len(r), **{k: int(counts.get(k, 0)) for k in ["solved", "wrong", "disagree", "timeout", "other"]},
                   "time_s": r.seconds.sum(), "time_ratio": r.seconds.sum() / runs[runs.solver == baseline].seconds.sum(),
                   "common_s": common_time.get(s, 0.0), "common_ratio": common_time.get(s, 0.0) / common_time.get(baseline, 1.0)}
    return pd.DataFrame(rows).T


def comparison(runs, baseline, new):
    """One row per statistic, the baseline and the new solver side by side with their ratio."""
    wide = runs.pivot(index="file", columns="solver", values="seconds")
    outcome = runs.pivot(index="file", columns="solver", values="outcome")
    both = (outcome[baseline] == "solved") & (outcome[new] == "solved")
    rows = {}
    for s in [baseline, new]:
        t, o = wide[s], outcome[s]
        rows[s] = {"solved": (o == "solved").sum(), "timeout": (o == "timeout").sum(), "other (unknown, error, memory)": (o == "other").sum(),
                   "wrong": (o == "wrong").sum(), "disagree": (o == "disagree").sum(), "solved only by this one":((o == "solved") & ~both).sum(),
                   "total time [s]": t.sum(), "mean [s]": t.mean(),
                   **{f"{q * 100:g}th percentile [s]": t.quantile(q) for q in [0.5] + EXTRA_QUANTILES},
                   "max [s]": t.max(), "total time of the formulas solved by both [s]": t[both].sum(),
                   "mean of the formulas solved by both [s]": t[both].mean(),
                   **{f"{q * 100:g}th percentile of the formulas solved by both [s]": t[both].quantile(q) for q in [0.5] + EXTRA_QUANTILES},
                   "formulas over 1 s": (t > 1).sum(), "formulas over 10 s (timeouts included)": (t > 10).sum()}
    table = pd.DataFrame(rows)
    table["ratio"] = table[new] / table[baseline]
    ratio = wide[new].clip(lower=0.01) / wide[baseline].clip(lower=0.01)
    diff = wide[new] - wide[baseline]
    extra = pd.DataFrame({"value": {
        "geometric mean of the per-formula time ratio (solved by both, times below 0.01 s count as 0.01 s)": np.exp(np.log(ratio[both]).mean()),
        "formulas more than 2× and 0.5 s faster": ((ratio < 0.5) & (diff < -0.5)).sum(),
        "formulas more than 2× and 0.5 s slower": ((ratio > 2) & (diff > 0.5)).sum(),
        "formulas more than 1 s faster": (diff < -1).sum(), "formulas more than 1 s slower": (diff > 1).sum()}})
    return table, extra


def per_set(runs, solvers):
    """Solved formulas, the total time, the mean time and the 99th percentile of the time per set and solver."""
    g = runs.groupby(["set", "solver"]).agg(solved=("outcome", lambda o: int((o == "solved").sum())), total=("seconds", "sum"),
                                            mean=("seconds", "mean"), p99=("seconds", lambda t: t.quantile(0.99)),
                                            formulas=("file", "size")).reset_index()
    out = pd.DataFrame({"formulas": g.groupby("set").formulas.first()})
    for s in solvers:
        r = g[g.solver == s].set_index("set")
        out[s] = [f"{r.solved[x]} / {r.total[x]:.0f} / {r["mean"][x]:.3f} / {r.p99[x]:.2f}" for x in out.index]
    return out


def changes(runs, solvers, baseline, timeout, limit=12):
    """Per solver, the formulas whose outcome or time changed against the baseline the most."""
    wide = runs.pivot(index="file", columns="solver", values="seconds")
    outcome = runs.pivot(index="file", columns="solver", values="outcome")
    sets = runs.groupby("file").set.first()
    lines = []
    for s in solvers:
        if s == baseline:
            continue
        gained = ((outcome[s] == "solved") & (outcome[baseline] != "solved")).sum()
        lost = ((outcome[s] != "solved") & (outcome[baseline] == "solved")).sum()
        diff = wide[s] - wide[baseline]
        ratio = wide[s].clip(lower=0.05) / wide[baseline].clip(lower=0.05)
        faster = ((ratio < 0.5) & (diff < -0.5)).sum()
        slower = ((ratio > 2) & (diff > 0.5)).sum()
        lines.append(f"### {s} vs {baseline}")
        lines.append("")
        lines.append(f"Solved only by {s}: {gained}, only by {baseline}: {lost}; "
                     f"more than 2× and 0.5 s faster: {faster}, slower: {slower}; time difference {diff.sum():+.0f} s.")
        lines.append("")
        for title, order in [("Biggest slowdowns", diff.sort_values(ascending=False)), ("Biggest speedups", diff.sort_values())]:
            top = order.head(limit)
            top = top[top.abs() > 0.5]
            if top.empty:
                continue
            lines.append(f"{title}:")
            lines.append("")
            lines.append(f"| formula | set | {baseline} [s] | {s} [s] |")
            lines.append("|---|---|---|---|")
            for f in top.index:
                show = lambda x: "timeout" if outcome.at[f, x] == "timeout" else f"{wide.at[f, x]:.2f} ({outcome.at[f, x]})"
                lines.append(f"| {f.split('/')[-1]} | {sets[f]} | {show(baseline)} | {show(s)} |")
            lines.append("")
    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("bench")
    parser.add_argument("baseline")
    parser.add_argument("--selection")
    parser.add_argument("--solvers", help="comma-separated solvers to compare (default: all)")
    parser.add_argument("--timeout", type=float, default=30)
    parser.add_argument("--out")
    args = parser.parse_args()

    runs, solvers = load(args.bench, args.selection, args.solvers.split(",") if args.solvers else None)
    out = [f"Formulas with a run of every solver: {runs.file.nunique()}; timeouts count as {args.timeout:g} s; "
           f"common = the formulas solved by every solver.", ""]
    if len(solvers) == 2:
        new = next(s for s in solvers if s != args.baseline)
        table, extra = comparison(runs, args.baseline, new)
        out += [f"## {args.baseline} vs {new}", "", table.to_markdown(floatfmt=".4g"), "", extra.to_markdown(floatfmt=".4g"), ""]
    for group in ["all", "affected", "control"]:
        r = runs[runs.group == group]
        if r.empty:
            continue
        out += [f"## Totals: {group} formulas ({r.file.nunique()})", "", totals(r, solvers, args.baseline).to_markdown(floatfmt=".3g"), ""]
    times, ratios = distribution(runs, solvers, args.baseline)
    out += ["## Time distribution [s] (all formulas, and the formulas solved by every solver)", "", times.to_markdown(floatfmt=".3g"), ""]
    out += [f"## Per-formula time ratio to {args.baseline} (formulas solved by every solver, times below 0.01 s count as 0.01 s)", "",
            ratios.to_markdown(floatfmt=".3g"), ""]
    out += ["## Per set: solved / total time [s] / mean time [s] / 99th percentile of the time [s]", "", per_set(runs, solvers).to_markdown(), ""]
    out += ["## Changes against the baseline", "", changes(runs, solvers, args.baseline, args.timeout)]
    text = "\n".join(out)
    if args.out:
        with open(args.out, "w") as f:
            f.write(text + "\n")
    print(text)


if __name__ == "__main__":
    main()
