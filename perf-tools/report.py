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

from __future__ import annotations

import argparse
import csv
from collections.abc import Callable, Iterable
from dataclasses import dataclass
from pathlib import Path
from typing import NamedTuple

import pandas as pd
import plots

# Times below this count as this in ratios of times, so that very fast runs do not give huge ratios.
# The plots show times below this as this.
MIN_TIME = plots.MIN_TIME

# A notable change of the time of a formula: more than this many times and this many seconds faster or slower.
NOTABLE_RATIO = 2
NOTABLE_SECONDS = 0.5

# The percentiles in the tables of the statistics of times.
PERCENTILES = [50, 90, 95, 99]

# How many formulas the tables of the biggest changes and of the fails list.
TOP_CHANGES = 10
TOP_FAILS = 30

# The outcomes of the runs.
# run.py writes solved, wrong, timeout, unknown and failed into runs.csv.
# load_runs changes solved to disagree for the formulas to which the solvers gave different answers.
# load_runs also adds the column short_outcome, which merges OTHER_OUTCOMES into other.
OTHER_OUTCOMES = ["unknown", "failed"]

# The short outcomes that are the columns of the overall table and of the table per set.
OVERALL_OUTCOMES = ["solved", "wrong", "disagree", "timeout", "other"]
SET_OUTCOMES = ["solved", "timeout", "other"]

# Outcomes of a run that finished, so that the solver did all the work of the formula.
FINISHED_OUTCOMES = ["solved", "wrong", "disagree", "unknown"]

# The text of a cell with numbers: digits, thousands separators, decimal points, the - of a missing ratio and the / between two solvers.
NUMERIC_CELL = r"[-\d,./]+"

# A table of a report: one dict per row, from the title of each column to the text of the cell.
Table = list[dict[str, str]]

# A function that writes a number as the text of a cell, such as number and time_text.
Formatter = Callable[[float], str]

# The functions below take the solvers in two ways.
# A parameter solvers is the list of the one or two solvers of the report, and with two solvers it is [old, new].
# The parameters old and new are the names of the two solvers, for the parts of the reports that need two solvers.


def parse_arguments() -> argparse.Namespace:
    """The command-line arguments."""
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)

    parser.add_argument("run_dir", type=Path, help="output directory of run.py")
    parser.add_argument("--old", help="the solver compared to (default: the first one of solvers.csv)")
    parser.add_argument("--new", help="the solver compared (default: the second one of solvers.csv, if any)")

    return parser.parse_args()


# ---------------------------------------------------------------------------------------------------------------------------------
# loading the run


def read_hashcodes(run_dir: Path) -> dict[str, str]:
    """The build hashcode of each solver of the run, by the name of the solver, in the order of solvers.csv."""
    with open(run_dir / "solvers.csv", newline="") as f:
        return {row["name"]: row["hashcode"] for row in csv.DictReader(f)}


def choose_solvers(names: list[str], old: str | None, new: str | None) -> list[str]:
    """The solvers of the reports: [old, new], or only [old] if the run has one solver and no new solver is given.

    names are the solvers of the run in the order of solvers.csv.
    By default, old is the first of them and new is the first one that is not old.
    """
    old = old or names[0]

    if new:
        return [old, new]

    if len(names) > 1:
        first_other = next(name for name in names if name != old)
        return [old, first_other]

    return [old]


def files_with_every_solver(runs: pd.DataFrame, solvers: list[str]) -> pd.Index:
    """The formulas that have a run of each of the solvers in runs, which has only runs of these solvers."""
    solvers_per_file = runs.groupby("file").solver.nunique()
    return solvers_per_file[solvers_per_file == len(solvers)].index


def load_runs(run_dir: Path, solvers: list[str]) -> pd.DataFrame:
    """The runs of the solvers, only of the formulas with a run of each of them.

    A solved run whose answer differs from the answer of the other solver gets the outcome disagree.
    The column short_outcome merges OTHER_OUTCOMES into other.
    """
    runs = pd.read_csv(run_dir / "runs.csv", dtype={"expected": str, "result": str})

    # Only the runs of the given solvers, on the formulas that each of them ran.
    runs = runs[runs.solver.isin(solvers)]
    runs = runs[runs.file.isin(files_with_every_solver(runs, solvers))].copy()

    # If the solved runs of a formula have different answers, their outcome changes from solved to disagree.
    solved = runs.outcome == "solved"
    answers_per_file = runs[solved].groupby("file").result.nunique()
    disagreeing_files = answers_per_file[answers_per_file > 1].index
    runs.loc[solved & runs.file.isin(disagreeing_files), "outcome"] = "disagree"

    # The short outcome is other for OTHER_OUTCOMES, and the outcome itself for the rest.
    is_other = runs.outcome.isin(OTHER_OUTCOMES)
    runs["short_outcome"] = runs.outcome.where(~is_other, "other")

    return runs


@dataclass
class FormulaTables:
    """The runs as tables with one row per formula, indexed by the file of the formula."""

    sets: pd.Series  # the set of each formula
    seconds: pd.DataFrame  # the time of each solver, one column per solver
    outcomes: pd.DataFrame  # the outcome of each solver, one column per solver
    results: pd.DataFrame  # the result of each solver, one column per solver


def formula_tables(runs: pd.DataFrame) -> FormulaTables:
    """The tables per formula of the runs of load_runs."""
    return FormulaTables(
        sets=runs.groupby("file")["set"].first(),
        seconds=runs.pivot(index="file", columns="solver", values="seconds"),
        outcomes=runs.pivot(index="file", columns="solver", values="outcome"),
        results=runs.pivot(index="file", columns="solver", values="result"),
    )


def split_by_solver(table: pd.DataFrame, solvers: list[str]) -> list[pd.DataFrame]:
    """The rows of each solver in a table with the column solver, in the order of solvers."""
    return [table[table.solver == solver] for solver in solvers]


# ---------------------------------------------------------------------------------------------------------------------------------
# formatting


def number(value: float) -> str:
    """A whole number with thousands separators, e.g. 15,710,000."""
    return f"{value:,.0f}"


def time_text(seconds: float) -> str:
    """A time in seconds with thousands separators, with three decimals below a second and two otherwise, e.g. 0.026 or 4,531.20."""
    return f"{seconds:,.3f}" if seconds < 1 else f"{seconds:,.2f}"


def cell(values: Iterable[float], format_value: Formatter = number) -> str:
    """The values of the solvers in one cell, old/new, each written by the function format_value."""
    return "/".join(format_value(value) for value in values)


def ratio(new_value: float, old_value: float) -> str:
    """new / old with three decimals, or - if old is zero."""
    return f"{new_value / old_value:.3f}" if old_value else "-"


def markdown(rows: Table) -> str:
    """A list of dicts (one per row, all with the same keys) as a Markdown table.

    A column is aligned right if all its cells are numbers (see NUMERIC_CELL), and left otherwise.
    """
    table = pd.DataFrame(rows).astype(str)

    alignment = []
    for column in table.columns:
        is_numeric = table[column].str.fullmatch(NUMERIC_CELL).all()
        alignment.append("right" if is_numeric else "left")

    return table.to_markdown(index=False, colalign=alignment, disable_numparse=True)


def header(title: str, hashcodes: dict[str, str], solvers: list[str], formulas_line: str) -> str:
    """The title, one line per solver with the hashcode it was built from, and a line about the formulas."""
    lines = [f"# {title}", ""]

    for name in solvers:
        lines.append(f"- {name} = {hashcodes.get(name, 'unknown')}")

    lines += ["", formulas_line]
    return "\n".join(lines)


def join_blocks(blocks: list[str]) -> str:
    """The text of a report from its blocks: headings, paragraphs and tables."""
    return "\n\n".join(blocks) + "\n"


# ---------------------------------------------------------------------------------------------------------------------------------
# REPORT.md
#
# The functions are in the order of the sections of the report.
# A function named ..._section returns the Markdown blocks of the section: its heading and its paragraphs and tables.
# It returns an empty list if the report has nothing to show in the section.


def header_section(runs: pd.DataFrame, solvers: list[str], hashcodes: dict[str, str]) -> list[str]:
    """The title, the solvers, and the number of the formulas with the timeout of the runs."""
    timeouts = runs.seconds[runs.outcome == "timeout"]

    # A run that timed out has the timeout as its time.
    if len(timeouts):
        timeout = f"timeout {timeouts.max():g} s (counted as {timeouts.max():g} s)"
    else:
        timeout = "no timeouts"

    formulas_line = f"{number(runs.file.nunique())} formulas, {timeout}."
    return [header("Benchmark results", hashcodes, solvers, formulas_line)]


def outcome_cell(by_solver: list[pd.DataFrame], short_outcome: str) -> str:
    """How many runs of each solver have a short outcome, in one cell."""
    counts = [(runs_of_solver.short_outcome == short_outcome).sum() for runs_of_solver in by_solver]
    return cell(counts)


def total_times(by_solver: list[pd.DataFrame]) -> list[float]:
    """The total time of the runs of each solver."""
    return [runs_of_solver.seconds.sum() for runs_of_solver in by_solver]


def overall(runs: pd.DataFrame, solvers: list[str]) -> Table:
    """One row: the formulas, the short outcomes and the total time of each solver."""
    by_solver = split_by_solver(runs, solvers)

    row = {"formulas": number(runs.file.nunique())}
    for short_outcome in OVERALL_OUTCOMES:
        row[short_outcome] = outcome_cell(by_solver, short_outcome)
    row["time [s]"] = cell(total_times(by_solver), time_text)

    return [row]


def overall_section(runs: pd.DataFrame, solvers: list[str]) -> list[str]:
    """The table of overall."""
    return ["## Overall", markdown(overall(runs, solvers))]


def changed_outcomes(outcomes: pd.DataFrame, old: str, new: str) -> Table:
    """How many formulas went from each outcome in old to each other outcome in new, the most frequent change first."""
    changed = outcomes[outcomes[old] != outcomes[new]]
    counts = changed.groupby([old, new]).size().sort_values(ascending=False)

    rows = []
    for (old_outcome, new_outcome), count in counts.items():
        rows.append({old: old_outcome, new: new_outcome, "formulas": number(count)})

    return rows


def changed_outcomes_section(tables: FormulaTables, old: str, new: str) -> list[str]:
    """The table of changed_outcomes, or a note that no outcome changed."""
    rows = changed_outcomes(tables.outcomes, old, new)
    return ["## Changed outcomes", markdown(rows) if rows else "None."]


def fails_in_one_section(tables: FormulaTables, old: str, new: str) -> list[str]:
    """The formulas that failed (crash, error, other output) in exactly one solver, with the results of both.

    The table lists at most TOP_FAILS formulas, and a line below it tells how many formulas are not listed.
    """
    failed = tables.outcomes.eq("failed")
    files = failed.index[failed[old] != failed[new]]

    if len(files) == 0:
        return []

    rows = []
    for file in files[:TOP_FAILS]:
        row = {
            "formula": Path(file).name,
            "set": tables.sets[file],
            old: tables.results.at[file, old],
            new: tables.results.at[file, new],
        }
        rows.append(row)

    blocks = ["## Fails in one solver only", markdown(rows)]

    not_listed = len(files) - TOP_FAILS
    if not_listed > 0:
        blocks.append(f"+{number(not_listed)} more.")

    return blocks


def time_statistics(seconds: pd.DataFrame, solvers: list[str]) -> Table:
    """One row per statistic of the times (total, mean, percentiles), one column per solver, and the ratio new/old.

    seconds has one row per formula and one column per solver.
    """
    # Each statistic has one value per solver.
    statistics = {"total": seconds.sum(), "mean": seconds.mean()}
    for percentile in PERCENTILES:
        statistics[f"{percentile}th percentile"] = seconds.quantile(percentile / 100)

    rows = []
    for name, values in statistics.items():
        row = {"": name}
        for solver in solvers:
            row[f"{solver} [s]"] = time_text(values[solver])

        if len(solvers) == 2:
            old, new = solvers
            row["new/old"] = ratio(values[new], values[old])

        rows.append(row)

    return rows


def time_ratios(seconds: pd.DataFrame, old: str, new: str) -> pd.Series:
    """The ratio new / old of the time of each formula, with times below MIN_TIME counted as MIN_TIME.

    seconds has one row per formula and one column per solver.
    """
    return seconds[new].clip(lower=MIN_TIME) / seconds[old].clip(lower=MIN_TIME)


def notable_changes(seconds: pd.DataFrame, old: str, new: str) -> str:
    """The line with the numbers of formulas notably faster and slower in new.

    seconds has one row per formula and one column per solver.
    """
    ratios = time_ratios(seconds, old, new)
    difference = seconds[new] - seconds[old]

    # A notable change is big both as a ratio and in seconds.
    faster = ((ratios < 1 / NOTABLE_RATIO) & (-difference > NOTABLE_SECONDS)).sum()
    slower = ((ratios > NOTABLE_RATIO) & (difference > NOTABLE_SECONDS)).sum()

    return (
        f"More than {NOTABLE_RATIO}× and {NOTABLE_SECONDS} s faster in {new}: {number(faster)} formulas; "
        f"slower: {number(slower)}."
    )


def time_section(title: str, seconds: pd.DataFrame, solvers: list[str]) -> list[str]:
    """The statistics of the times of some formulas, and with two solvers the line of notable_changes.

    seconds has one row per formula of the section and one column per solver.
    """
    blocks = [
        f"## {title}",
        f"{number(len(seconds))} formulas.",
        markdown(time_statistics(seconds, solvers)),
    ]

    if len(solvers) == 2:
        old, new = solvers
        blocks.append(notable_changes(seconds, old, new))

    return blocks


def per_set(runs: pd.DataFrame, solvers: list[str]) -> Table:
    """One row per set: the formulas, the solved, timed out and other runs, the total time and its ratio new/old."""
    rows = []

    for set_name, set_runs in runs.groupby("set"):
        by_solver = split_by_solver(set_runs, solvers)
        times = total_times(by_solver)

        row = {"set": set_name, "formulas": number(set_runs.file.nunique())}
        for short_outcome in SET_OUTCOMES:
            row[short_outcome] = outcome_cell(by_solver, short_outcome)
        row["time [s]"] = cell(times, time_text)

        if len(solvers) == 2:
            old_time, new_time = times
            row["new/old"] = ratio(new_time, old_time)

        rows.append(row)

    return rows


def per_set_section(runs: pd.DataFrame, solvers: list[str]) -> list[str]:
    """The table of per_set."""
    return ["## Per set", markdown(per_set(runs, solvers))]


def biggest_changes_sections(tables: FormulaTables, old: str, new: str) -> list[str]:
    """Two sections: the formulas whose time grew the most and those whose time dropped the most.

    Each section lists at most TOP_CHANGES formulas, and only those whose time changed by more than NOTABLE_SECONDS.
    """
    difference = tables.seconds[new] - tables.seconds[old]
    slowdowns = difference.nlargest(TOP_CHANGES).index
    speedups = difference.nsmallest(TOP_CHANGES).index

    blocks = []
    for title, files in [("Biggest slowdowns", slowdowns), ("Biggest speedups", speedups)]:
        rows = []
        for file in files:
            if abs(difference[file]) > NOTABLE_SECONDS:
                row = {
                    "formula": Path(file).name,
                    "set": tables.sets[file],
                    f"{old} [s]": time_text(tables.seconds.at[file, old]),
                    f"{new} [s]": time_text(tables.seconds.at[file, new]),
                    "outcome": f"{tables.outcomes.at[file, old]}/{tables.outcomes.at[file, new]}",
                }
                rows.append(row)

        if rows:
            blocks += [f"## {title}", markdown(rows)]

    return blocks


def plots_section() -> list[str]:
    """The plots that plots.write_plots writes."""
    return ["## Plots", "![Time per formula](plots/scatter.png)", "![Total time per set](plots/sets.png)"]


def benchmark_report(runs: pd.DataFrame, solvers: list[str], hashcodes: dict[str, str]) -> str:
    """The text of REPORT.md."""
    tables = formula_tables(runs)
    solved_by_all = tables.outcomes.eq("solved").all(axis=1)
    comparing = len(solvers) == 2

    blocks = header_section(runs, solvers, hashcodes)
    blocks += overall_section(runs, solvers)

    if comparing:
        old, new = solvers
        blocks += changed_outcomes_section(tables, old, new)
        blocks += fails_in_one_section(tables, old, new)

    blocks += time_section("Time: all formulas", tables.seconds, solvers)
    solved_title = "Time: solved by both" if comparing else "Time: solved"
    blocks += time_section(solved_title, tables.seconds[solved_by_all], solvers)

    blocks += per_set_section(runs, solvers)

    if comparing:
        blocks += biggest_changes_sections(tables, old, new)
        blocks += plots_section()

    return join_blocks(blocks)


# ---------------------------------------------------------------------------------------------------------------------------------
# REDUCTIONS.md


class ReductionSum(NamedTuple):
    """A number in a table of REDUCTIONS.md: the sum of a column of the reductions."""

    title: str  # the title of the number in the table
    column: str  # the column of the reductions that is summed
    format_value: Formatter = number  # how the sum is written


# The rows of the overall table: sums over all reductions, and sums over the guarded reductions.
OVERALL_SUMS = [
    ReductionSum("reductions", "reductions"),
    ReductionSum("time of reductions [s]", "seconds", time_text),
    ReductionSum("states before", "states_before"),
    ReductionSum("states after", "states_after"),
    ReductionSum("states removed", "states_removed"),
    ReductionSum("transitions before", "transitions_before"),
    ReductionSum("transitions after", "transitions_after"),
    ReductionSum("transitions removed", "transitions_removed"),
]
GUARDED_SUMS = [
    ReductionSum("guarded reductions", "reductions"),
    ReductionSum("time of guarded reductions [s]", "seconds", time_text),
    ReductionSum("states removed by guarded reductions", "states_removed"),
    ReductionSum("transitions removed by guarded reductions", "transitions_removed"),
]

# The columns of the table per call site and of the table per set.
SITE_SUMS = [
    ReductionSum("reductions", "reductions"),
    ReductionSum("time [s]", "seconds", time_text),
    ReductionSum("states before", "states_before"),
    ReductionSum("states after", "states_after"),
    ReductionSum("transitions before", "transitions_before"),
    ReductionSum("transitions after", "transitions_after"),
]
SET_SUMS = [
    ReductionSum("reductions", "reductions"),
    ReductionSum("time [s]", "seconds", time_text),
    ReductionSum("states removed", "states_removed"),
    ReductionSum("transitions removed", "transitions_removed"),
]


def files_finished_by_all(runs: pd.DataFrame, solvers: list[str]) -> pd.Index:
    """The formulas that every solver finished, so that the solvers did the same work on them."""
    finished = runs[runs.outcome.isin(FINISHED_OUTCOMES)]
    return files_with_every_solver(finished, solvers)


def load_reductions(run_dir: Path, files: pd.Index, solvers: list[str]) -> pd.DataFrame:
    """The reductions of the solvers on the formulas in files.

    The column site_label marks the guarded reductions of a site, and the columns of the removed states and transitions are added.
    """
    reductions = pd.read_csv(run_dir / "reductions.csv")
    reductions = reductions[reductions.solver.isin(solvers) & reductions.file.isin(files)].copy()

    not_guarded = reductions.guarded == 0
    reductions["site_label"] = reductions.site.where(not_guarded, reductions.site + " (guarded)")

    reductions["seconds"] = reductions.ns / 1e9
    reductions["states_removed"] = reductions.states_before - reductions.states_after
    reductions["transitions_removed"] = reductions.transitions_before - reductions.transitions_after

    return reductions


def sum_cell(by_solver: list[pd.DataFrame], reduction_sum: ReductionSum) -> str:
    """The sum of a column of the reductions of each solver, in one cell."""
    values = [reductions_of_solver[reduction_sum.column].sum() for reductions_of_solver in by_solver]
    return cell(values, reduction_sum.format_value)


def reductions_overall(reductions: pd.DataFrame, finished_runs: pd.DataFrame, solvers: list[str]) -> Table:
    """One row per sum over the reductions, the values of the solvers in one cell, and a row with the solving time."""
    solvers_title = "/".join(solvers)

    by_solver = split_by_solver(reductions, solvers)
    guarded_by_solver = [reductions_of_solver[reductions_of_solver.guarded == 1] for reductions_of_solver in by_solver]

    rows = []
    for reduction_sum in OVERALL_SUMS:
        rows.append({"": reduction_sum.title, solvers_title: sum_cell(by_solver, reduction_sum)})
    for reduction_sum in GUARDED_SUMS:
        rows.append({"": reduction_sum.title, solvers_title: sum_cell(guarded_by_solver, reduction_sum)})

    # The time of the whole runs, to compare the time of the reductions with.
    solving_times = total_times(split_by_solver(finished_runs, solvers))
    rows.append({"": "solving time [s]", solvers_title: cell(solving_times, time_text)})

    return rows


def summed(reductions: pd.DataFrame, group: str, solvers: list[str]) -> pd.DataFrame:
    """The columns of the reductions summed per group: one row per group, one column per (column, solver).

    group is the column whose values are the groups, such as set.
    The rows are sorted by the reductions of the first solver.
    """
    sums = reductions.groupby([group, "solver"]).sum(numeric_only=True).unstack("solver", fill_value=0)

    # A solver without reductions has no columns yet.
    columns = [(column, solver) for column in sums.columns.levels[0] for solver in solvers]
    sums = sums.reindex(columns=columns, fill_value=0)

    return sums.sort_values(("reductions", solvers[0]), ascending=False)


def reductions_per_group(
    reductions: pd.DataFrame,
    group: str,
    title: str,
    reduction_sums: list[ReductionSum],
    solvers: list[str],
) -> Table:
    """One row per group, under the given title, and one cell per sum with the values of the solvers.

    group is the column of the reductions whose values are the groups.
    """
    sums = summed(reductions, group, solvers)

    rows = []
    for name in sums.index:
        row = {title: name}

        for reduction_sum in reduction_sums:
            values = [sums.at[name, (reduction_sum.column, solver)] for solver in solvers]
            row[reduction_sum.title] = cell(values, reduction_sum.format_value)

        rows.append(row)

    return rows


def reductions_report(
    reductions: pd.DataFrame,
    finished_runs: pd.DataFrame,
    solvers: list[str],
    hashcodes: dict[str, str],
) -> str:
    """The text of REDUCTIONS.md.

    finished_runs are the runs of the formulas that every solver finished, and reductions are the reductions of these runs.
    """
    formulas_line = f"{number(finished_runs.file.nunique())} formulas finished by every solver."

    blocks = [
        header("Reductions of automata", hashcodes, solvers, formulas_line),
        "## Overall",
        markdown(reductions_overall(reductions, finished_runs, solvers)),
        "## Per call site",
        markdown(reductions_per_group(reductions, "site_label", "site", SITE_SUMS, solvers)),
        "## Per set",
        markdown(reductions_per_group(reductions, "set", "set", SET_SUMS, solvers)),
    ]

    return join_blocks(blocks)


# ---------------------------------------------------------------------------------------------------------------------------------


def main() -> None:
    """Writes the reports and the plots into the run directory."""
    args = parse_arguments()
    run_dir = args.run_dir

    hashcodes = read_hashcodes(run_dir)
    solvers = choose_solvers(list(hashcodes), args.old, args.new)
    runs = load_runs(run_dir, solvers)

    # REPORT.md, and its plots if it compares two solvers.
    (run_dir / "REPORT.md").write_text(benchmark_report(runs, solvers, hashcodes))
    if len(solvers) == 2:
        old, new = solvers
        plots.write_plots(runs, old, new, run_dir / "plots")

    # REDUCTIONS.md, if the run recorded the reductions.
    if (run_dir / "reductions.csv").exists():
        files = files_finished_by_all(runs, solvers)
        reductions = load_reductions(run_dir, files, solvers)
        finished_runs = runs[runs.file.isin(files)]

        (run_dir / "REDUCTIONS.md").write_text(reductions_report(reductions, finished_runs, solvers, hashcodes))


if __name__ == "__main__":
    main()
