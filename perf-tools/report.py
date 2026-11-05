#!/usr/bin/env python3
"""Markdown report of a benchmark of run_bench.py: the solvers against a baseline solver.

Only the formulas with a run of every solver are counted, and timeouts count as the timeout.
Sections: outcomes and total time per solver; solved formulas and total time per set; for each other solver against the baseline,
the changed outcomes, time statistics side by side and the biggest slowdowns and speedups.

Example: report.py out/runs.csv --baseline old --out out/REPORT.md
"""
import argparse

import pandas as pd

import bench_data
from bench_data import notably_faster, notably_slower

OUTCOMES = ["solved", "wrong", "disagree", "timeout", "unknown", "failed"]
QUANTILES = [0.5, 0.9, 0.95, 0.99]


def parse_arguments():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("runs", nargs="+", help="runs.csv of run_bench.py (several are concatenated)")
    parser.add_argument("--baseline", required=True, help="the solver the others are compared to")
    parser.add_argument("--solvers", help="comma-separated solvers to include (default: all)")
    parser.add_argument("--top", type=int, default=12, help="how many of the biggest slowdowns and speedups to list")
    parser.add_argument("--out", help="write the report to this file (it is printed in any case)")
    return parser.parse_args()


def totals(runs, solvers, baseline):
    """Per solver: the outcomes, the total time, and the total time of the formulas solved by every solver, both also relative to the baseline."""
    common = runs[runs.file.isin(bench_data.solved_by_all(runs))]
    rows = {}
    for solver in solvers:
        own = runs[runs.solver == solver]
        counts = own.outcome.value_counts()
        rows[solver] = {"formulas": len(own), **{name: int(counts.get(name, 0)) for name in OUTCOMES},
                        "total time [s]": own.seconds.sum(), "common time [s]": common[common.solver == solver].seconds.sum()}
    table = pd.DataFrame(rows).T
    table["total / baseline"] = table["total time [s]"] / table.at[baseline, "total time [s]"]
    table["common / baseline"] = table["common time [s]"] / table.at[baseline, "common time [s]"]
    return table


def per_set(runs, solvers):
    """Per set and solver: the solved formulas and the total time."""
    solved = runs[runs.outcome == "solved"].groupby(["set", "solver"]).size().unstack(fill_value=0)
    seconds = runs.groupby(["set", "solver"]).seconds.sum().unstack()
    table = pd.DataFrame({"formulas": runs.groupby("set").file.nunique()})
    for solver in solvers:
        table[f"{solver} solved"] = solved.get(solver, 0)
        table[f"{solver} time [s]"] = seconds[solver]
    return table.fillna(0)


def changed_outcomes(runs, baseline, new):
    """How many formulas went from each outcome of the baseline to each other outcome of the new solver."""
    outcomes = bench_data.outcome_table(runs)
    changed = outcomes[outcomes[baseline] != outcomes[new]]
    return changed.groupby([baseline, new]).size().rename("formulas").reset_index()


def time_statistics(runs, baseline, new):
    """Statistics of the times of all formulas and of the formulas solved by both, the baseline and the new solver side by side."""
    seconds = bench_data.seconds_table(runs)
    outcomes = bench_data.outcome_table(runs)
    solved_by_both = (outcomes[baseline] == "solved") & (outcomes[new] == "solved")
    rows = {}
    for label, formulas in [("all", seconds.index), ("solved by both", seconds.index[solved_by_both])]:
        for solver in [baseline, new]:
            times = seconds.loc[formulas, solver]
            column = rows.setdefault(solver, {})
            column[f"{label}: total [s]"] = times.sum()
            column[f"{label}: mean [s]"] = times.mean()
            for quantile in QUANTILES:
                column[f"{label}: {quantile * 100:g}th percentile [s]"] = times.quantile(quantile)
    table = pd.DataFrame(rows)
    table["ratio"] = table[new] / table[baseline]
    both = seconds[solved_by_both]
    summary = {"geometric mean of the per-formula time ratio (solved by both)": bench_data.geometric_mean(bench_data.time_ratio(both[new], both[baseline])),
               f"formulas more than {bench_data.NOTABLE_RATIO}× and {bench_data.NOTABLE_SECONDS} s faster": int(notably_faster(seconds[new], seconds[baseline]).sum()),
               f"formulas more than {bench_data.NOTABLE_RATIO}× and {bench_data.NOTABLE_SECONDS} s slower": int(notably_slower(seconds[new], seconds[baseline]).sum())}
    return table, summary


def biggest_changes(runs, baseline, new, top):
    """The formulas whose time grew and dropped the most (at least by NOTABLE_SECONDS)."""
    seconds = bench_data.seconds_table(runs)
    outcomes = bench_data.outcome_table(runs)
    sets = runs.groupby("file")["set"].first()
    difference = seconds[new] - seconds[baseline]
    tables = {}
    for title, files in [("Biggest slowdowns", difference.nlargest(top).index), ("Biggest speedups", difference.nsmallest(top).index)]:
        files = [file for file in files if abs(difference[file]) > bench_data.NOTABLE_SECONDS]
        tables[title] = pd.DataFrame({"formula": [file.split("/")[-1] for file in files], "set": sets[files].to_list(),
                                      f"{baseline} [s]": seconds.loc[files, baseline].to_list(),
                                      f"{baseline} outcome": outcomes.loc[files, baseline].to_list(),
                                      f"{new} [s]": seconds.loc[files, new].to_list(), f"{new} outcome": outcomes.loc[files, new].to_list()})
    return tables


def markdown(table, floatfmt=".4g", index=True):
    return table.to_markdown(floatfmt=floatfmt, index=index)


def report(runs, solvers, baseline, top):
    sections = [f"{runs.file.nunique()} formulas with a run of every solver; timeouts count as the timeout; "
                f"common = the formulas solved by every solver.",
                "## Totals", markdown(totals(runs, solvers, baseline)),
                "## Per set", markdown(per_set(runs, solvers))]
    for new in solvers:
        if new == baseline:
            continue
        statistics, summary = time_statistics(runs, baseline, new)
        changed = changed_outcomes(runs, baseline, new)
        sections += [f"## {new} against {baseline}",
                     "Changed outcomes:", markdown(changed, index=False) if not changed.empty else "none",
                     markdown(statistics), "\n".join(f"- {name}: {value:.4g}" for name, value in summary.items())]
        for title, table in biggest_changes(runs, baseline, new, top).items():
            if not table.empty:
                sections += [f"{title}:", markdown(table, floatfmt=".2f", index=False)]
    return "\n\n".join(sections) + "\n"


def main():
    args = parse_arguments()
    runs, solvers = bench_data.load_runs(args.runs, args.solvers.split(",") if args.solvers else None)
    solvers = [args.baseline] + [solver for solver in solvers if solver != args.baseline]
    text = report(runs, solvers, args.baseline, args.top)
    if args.out:
        with open(args.out, "w") as f:
            f.write(text)
    print(text)


if __name__ == "__main__":
    main()
