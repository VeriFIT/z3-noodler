#!/usr/bin/env python3
"""Markdown reports and plots of a benchmark of run.py.

Writes into RUN_DIR:
  REPORT.md      the outcomes and times of the formulas, overall and per set, and with two solvers the differences between them;
  REDUCTIONS.md  if the run has reductions.csv (run.py --reduce-log), the mata::nfa::reduce calls of the solvers;
  plots/         with two solvers, the plots of plots.py.
The reports compare two solvers, old and new (by default the first two of solvers.csv), or describe one solver.
A cell with the values of both solvers is written as old/new.
Only the formulas with a run of each solver are counted, and timeouts count as the timeout.

Example: report.py runs/guard --old old --new new
"""
import argparse
import csv
from pathlib import Path

import pandas as pd

import plots

# Times below this count as this in ratios of times, so that very fast runs do not give huge ratios.
MIN_TIME = 0.01
# A notable change of the time of a formula: more than this many times and this many seconds faster or slower.
NOTABLE_RATIO = 2
NOTABLE_SECONDS = 0.5
PERCENTILES = [50, 90, 95, 99]
# How many formulas the tables of the biggest changes and of the fails list.
TOP_CHANGES = 10
TOP_FAILS = 30
# Outcomes of runs.csv merged into "other" in the overall and per-set tables.
OTHER_OUTCOMES = ["unknown", "failed"]
# Outcomes of a run that finished, so that the solver did all the work of the formula.
FINISHED_OUTCOMES = ["solved", "wrong", "disagree", "unknown"]


def parse_arguments():
    """The command-line arguments."""
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("run_dir", type=Path, help="output directory of run.py")
    parser.add_argument("--old", help="the solver compared to (default: the first one of solvers.csv)")
    parser.add_argument("--new", help="the solver compared (default: the second one of solvers.csv, if any)")
    return parser.parse_args()


# ---------------------------------------------------------------------------------------------------------------------------------
# loading and formatting


def load_runs(run_dir, solvers):
    """The runs of the solvers, only of the formulas with a run of each of them.

    A solved run whose answer differs from the answer of the other solver gets the outcome disagree.
    The column short_outcome merges OTHER_OUTCOMES into other.
    """
    runs = pd.read_csv(run_dir / "runs.csv", dtype={"expected": str, "result": str})
    runs = runs[runs.solver.isin(solvers)]
    runs_per_file = runs.groupby("file").solver.nunique()
    runs = runs[runs.file.isin(runs_per_file[runs_per_file == len(solvers)].index)].copy()

    answers_per_file = runs[runs.outcome == "solved"].groupby("file").result.nunique()
    disagreeing = runs.file.isin(answers_per_file[answers_per_file > 1].index) & (runs.outcome == "solved")
    runs.loc[disagreeing, "outcome"] = "disagree"

    runs["short_outcome"] = runs.outcome.where(~runs.outcome.isin(OTHER_OUTCOMES), "other")
    return runs


def number(value):
    """A whole number with thousands separators, e.g. 15,710,000."""
    return f"{value:,.0f}"


def time_text(seconds):
    """A time in seconds with thousands separators, with three decimals below a second and two otherwise, e.g. 0.026 or 4,531.20."""
    return f"{seconds:,.3f}" if seconds < 1 else f"{seconds:,.2f}"


def cell(values, text=number):
    """The values of the solvers in one cell, old/new, each written by the function text."""
    return "/".join(text(value) for value in values)


def ratio(new_value, old_value):
    """new / old with three decimals, or - if old is zero."""
    return f"{new_value / old_value:.3f}" if old_value else "-"


def markdown(rows):
    """A list of dicts (one per row, all with the same keys) as a Markdown table, the columns of numbers aligned right and the others left."""
    table = pd.DataFrame(rows).astype(str)
    alignment = ["right" if table[column].str.fullmatch(r"[-\d,./]+").all() else "left" for column in table.columns]
    return table.to_markdown(index=False, colalign=alignment, disable_numparse=True)


def header(title, hashcodes, solvers, first_line):
    """The title, one line per solver with the hashcode it was built from, and a line about the formulas."""
    return "\n".join([f"# {title}", "", *[f"- {name} = {hashcodes.get(name, 'unknown')}" for name in solvers], "", first_line])


# ---------------------------------------------------------------------------------------------------------------------------------
# REPORT.md


def overall(runs, solvers):
    """One row: the formulas, the short outcomes and the total time of each solver."""
    by_solver = [runs[runs.solver == solver] for solver in solvers]
    row = {"formulas": number(runs.file.nunique())}
    for name in ["solved", "wrong", "disagree", "timeout", "other"]:
        row[name] = cell([(runs_of.short_outcome == name).sum() for runs_of in by_solver])
    row["time [s]"] = cell([runs_of.seconds.sum() for runs_of in by_solver], time_text)
    return [row]


def per_set(runs, solvers):
    """One row per set: the formulas, the solved, timed out and other runs, the total time and its ratio new/old."""
    rows = []
    for name, set_runs in runs.groupby("set"):
        by_solver = [set_runs[set_runs.solver == solver] for solver in solvers]
        row = {"set": name, "formulas": number(set_runs.file.nunique())}
        for outcome in ["solved", "timeout", "other"]:
            row[outcome] = cell([(runs_of.short_outcome == outcome).sum() for runs_of in by_solver])
        times = [runs_of.seconds.sum() for runs_of in by_solver]
        row["time [s]"] = cell(times, time_text)
        if len(solvers) == 2:
            row["new/old"] = ratio(times[1], times[0])
        rows.append(row)
    return rows


def time_statistics(seconds, solvers):
    """One row per statistic of the times (total, mean, percentiles), one column per solver, and the ratio new/old."""
    statistics = {"total": seconds.sum(), "mean": seconds.mean()}
    for percentile in PERCENTILES:
        statistics[f"{percentile}th percentile"] = seconds.quantile(percentile / 100)

    rows = []
    for name, values in statistics.items():
        row = {"": name, **{f"{solver} [s]": time_text(values[solver]) for solver in solvers}}
        if len(solvers) == 2:
            row["new/old"] = ratio(values[solvers[1]], values[solvers[0]])
        rows.append(row)
    return rows


def notable_changes(seconds, old, new):
    """The line with the numbers of formulas notably faster and slower in new."""
    ratios = seconds[new].clip(lower=MIN_TIME) / seconds[old].clip(lower=MIN_TIME)
    difference = seconds[new] - seconds[old]
    faster = ((ratios < 1 / NOTABLE_RATIO) & (-difference > NOTABLE_SECONDS)).sum()
    slower = ((ratios > NOTABLE_RATIO) & (difference > NOTABLE_SECONDS)).sum()
    return f"More than {NOTABLE_RATIO}× and {NOTABLE_SECONDS} s faster in {new}: {number(faster)} formulas; slower: {number(slower)}."


def changed_outcomes(outcomes, old, new):
    """How many formulas went from each outcome in old to each other outcome in new."""
    changed = outcomes[outcomes[old] != outcomes[new]]
    counts = changed.groupby([old, new]).size().sort_values(ascending=False)
    return [{old: old_outcome, new: new_outcome, "formulas": number(count)} for (old_outcome, new_outcome), count in counts.items()]


def fails_in_one(runs, outcomes, old, new):
    """The formulas that failed (crash, error, other output) in exactly one solver, with the results of both.

    Returns at most TOP_FAILS rows and the number of the formulas not listed.
    """
    failed = outcomes.eq("failed")
    files = failed.index[failed[old] != failed[new]]
    results = runs.pivot(index="file", columns="solver", values="result")
    sets = runs.groupby("file")["set"].first()
    rows = [{"formula": Path(file).name, "set": sets[file], old: results.at[file, old], new: results.at[file, new]}
            for file in files[:TOP_FAILS]]
    return rows, max(0, len(files) - TOP_FAILS)


def biggest_changes(runs, seconds, outcomes, old, new):
    """The formulas whose time grew and dropped the most (by more than NOTABLE_SECONDS)."""
    sets = runs.groupby("file")["set"].first()
    difference = seconds[new] - seconds[old]
    slowdowns = difference.nlargest(TOP_CHANGES).index
    speedups = difference.nsmallest(TOP_CHANGES).index

    tables = {}
    for title, files in [("Biggest slowdowns", slowdowns), ("Biggest speedups", speedups)]:
        tables[title] = [{"formula": Path(file).name, "set": sets[file],
                          f"{old} [s]": time_text(seconds.at[file, old]), f"{new} [s]": time_text(seconds.at[file, new]),
                          "outcome": f"{outcomes.at[file, old]}/{outcomes.at[file, new]}"}
                         for file in files if abs(difference[file]) > NOTABLE_SECONDS]
    return tables


def benchmark_report(runs, solvers, hashcodes):
    """The text of REPORT.md."""
    timeouts = runs.seconds[runs.outcome == "timeout"]
    timeout = f"timeout {timeouts.max():g} s (counted as {timeouts.max():g} s)" if len(timeouts) else "no timeouts"
    sections = [header("Benchmark results", hashcodes, solvers, f"{number(runs.file.nunique())} formulas, {timeout}."),
                "## Overall", markdown(overall(runs, solvers))]

    seconds = runs.pivot(index="file", columns="solver", values="seconds")
    outcomes = runs.pivot(index="file", columns="solver", values="outcome")
    solved_by_all = outcomes.eq("solved").all(axis=1)

    if len(solvers) == 2:
        old, new = solvers
        changed = changed_outcomes(outcomes, old, new)
        sections += ["## Changed outcomes", markdown(changed) if changed else "None."]
        fails, not_listed = fails_in_one(runs, outcomes, old, new)
        if fails:
            sections += ["## Fails in one solver only", markdown(fails)]
            if not_listed:
                sections.append(f"+{number(not_listed)} more.")

    solved_title = "Time: solved by both" if len(solvers) == 2 else "Time: solved"
    for title, formulas in [("Time: all formulas", seconds.index), (solved_title, seconds.index[solved_by_all])]:
        sections += [f"## {title}", f"{number(len(formulas))} formulas.", markdown(time_statistics(seconds.loc[formulas], solvers))]
        if len(solvers) == 2:
            sections.append(notable_changes(seconds.loc[formulas], *solvers))

    sections += ["## Per set", markdown(per_set(runs, solvers))]

    if len(solvers) == 2:
        for title, rows in biggest_changes(runs, seconds, outcomes, *solvers).items():
            if rows:
                sections += [f"## {title}", markdown(rows)]
        sections += ["## Plots", "![Time per formula](plots/scatter.png)", "![Total time per set](plots/sets.png)"]

    return "\n\n".join(sections) + "\n"


# ---------------------------------------------------------------------------------------------------------------------------------
# REDUCTIONS.md


def load_reductions(run_dir, runs, solvers):
    """The reductions and the runs of the formulas that every solver finished, so that the solvers did the same work.

    The column site_label marks the guarded reductions of a site, and the columns of the removed states and transitions are added.
    """
    finished = runs[runs.outcome.isin(FINISHED_OUTCOMES)]
    finished_per_file = finished.groupby("file").solver.nunique()
    files = finished_per_file[finished_per_file == len(solvers)].index

    reductions = pd.read_csv(run_dir / "reductions.csv")
    reductions = reductions[reductions.solver.isin(solvers) & reductions.file.isin(files)].copy()
    reductions["site_label"] = reductions.site.where(reductions.guarded == 0, reductions.site + " (guarded)")
    reductions["seconds"] = reductions.ns / 1e9
    reductions["states_removed"] = reductions.states_before - reductions.states_after
    reductions["transitions_removed"] = reductions.transitions_before - reductions.transitions_after
    return reductions, runs[runs.file.isin(files)]


def summed(reductions, group, solvers):
    """The columns of the reductions summed per group: one row per group, one column per (column, solver).

    The rows are sorted by the reductions of the first solver.
    """
    sums = reductions.groupby([group, "solver"]).sum(numeric_only=True).unstack("solver", fill_value=0)
    # a solver without reductions has no columns yet
    columns = [(column, solver) for column in sums.columns.levels[0] for solver in solvers]
    sums = sums.reindex(columns=columns, fill_value=0)
    return sums.sort_values(("reductions", solvers[0]), ascending=False)


def reductions_overall(reductions, finished_runs, solvers):
    """One row per quantity, the values of the solvers in one cell."""
    by_solver = [reductions[reductions.solver == solver] for solver in solvers]
    guarded = [runs_of[runs_of.guarded == 1] for runs_of in by_solver]
    quantities = [
        ("reductions", [runs_of.reductions.sum() for runs_of in by_solver], number),
        ("time of reductions [s]", [runs_of.seconds.sum() for runs_of in by_solver], time_text),
        ("states before", [runs_of.states_before.sum() for runs_of in by_solver], number),
        ("states after", [runs_of.states_after.sum() for runs_of in by_solver], number),
        ("states removed", [runs_of.states_removed.sum() for runs_of in by_solver], number),
        ("transitions before", [runs_of.transitions_before.sum() for runs_of in by_solver], number),
        ("transitions after", [runs_of.transitions_after.sum() for runs_of in by_solver], number),
        ("transitions removed", [runs_of.transitions_removed.sum() for runs_of in by_solver], number),
        ("guarded reductions", [runs_of.reductions.sum() for runs_of in guarded], number),
        ("time of guarded reductions [s]", [runs_of.seconds.sum() for runs_of in guarded], time_text),
        ("states removed by guarded reductions", [runs_of.states_removed.sum() for runs_of in guarded], number),
        ("transitions removed by guarded reductions", [runs_of.transitions_removed.sum() for runs_of in guarded], number),
        ("solving time [s]", [finished_runs[finished_runs.solver == solver].seconds.sum() for solver in solvers], time_text),
    ]
    return [{"": name, "/".join(solvers): cell(values, text)} for name, values, text in quantities]


def reductions_per_group(reductions, group, title, columns, solvers):
    """One row per group, one cell per (column title, column, text function) with the values of the solvers."""
    sums = summed(reductions, group, solvers)
    return [{title: name, **{column_title: cell([sums.at[name, (column, solver)] for solver in solvers], text)
                             for column_title, column, text in columns}}
            for name in sums.index]


def reductions_report(reductions, finished_runs, solvers, hashcodes):
    """The text of REDUCTIONS.md."""
    site_columns = [("reductions", "reductions", number), ("time [s]", "seconds", time_text), ("states before", "states_before", number),
                    ("states after", "states_after", number), ("transitions before", "transitions_before", number),
                    ("transitions after", "transitions_after", number)]
    set_columns = [("reductions", "reductions", number), ("time [s]", "seconds", time_text), ("states removed", "states_removed", number),
                   ("transitions removed", "transitions_removed", number)]
    formulas = f"{number(finished_runs.file.nunique())} formulas finished by every solver."
    sections = [header("Reductions of automata", hashcodes, solvers, formulas),
                "## Overall", markdown(reductions_overall(reductions, finished_runs, solvers)),
                "## Per call site", markdown(reductions_per_group(reductions, "site_label", "site", site_columns, solvers)),
                "## Per set", markdown(reductions_per_group(reductions, "set", "set", set_columns, solvers))]
    return "\n\n".join(sections) + "\n"


# ---------------------------------------------------------------------------------------------------------------------------------


def main():
    """Writes the reports and the plots into the run directory."""
    args = parse_arguments()
    with open(args.run_dir / "solvers.csv", newline="") as f:
        hashcodes = {row["name"]: row["hashcode"] for row in csv.DictReader(f)}
    names = list(hashcodes)
    solvers = [args.old or names[0]]
    if args.new or len(names) > 1:
        solvers.append(args.new or next(name for name in names if name != solvers[0]))

    runs = load_runs(args.run_dir, solvers)
    (args.run_dir / "REPORT.md").write_text(benchmark_report(runs, solvers, hashcodes))
    if len(solvers) == 2:
        old, new = solvers
        plots.write_plots(runs, old, new, args.run_dir / "plots")

    if (args.run_dir / "reductions.csv").exists():
        reductions, finished_runs = load_reductions(args.run_dir, runs, solvers)
        (args.run_dir / "REDUCTIONS.md").write_text(reductions_report(reductions, finished_runs, solvers, hashcodes))


if __name__ == "__main__":
    main()
