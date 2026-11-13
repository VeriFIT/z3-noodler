#!/usr/bin/env python3
"""Tables, statistical tests and plots that compare two solvers of a run of run.py with reductions.csv (run.py --reduce-log).

Writes into RUN_DIR/analysis:
  tables.md  the outcomes, the paired comparisons of the solving and reduction times overall and per set, the reductions per call
             site, the reduced automata at the guard sites, the formulas with changed outcomes, and all formulas of FULL_SET;
  plots/     scatter.png and sets.png of plots.py, ratios.png with the distribution of the ratios of times per formula, and sites.png
             with the reduction time per call site.
The guard sites are the call sites with guarded reductions.
The formulas on which both solvers time out are left out, except in the tables of FULL_SET, and the other timeouts count as the timeout.

Example: analysis.py runs/reduce-counts-2026-11-07 --new-label new-guard
"""

from __future__ import annotations

import argparse
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import NamedTuple

import matplotlib.pyplot as plt
import numpy as np
import pandas as pd
import seaborn as sns
from scipy import stats

import plots
import report
from report import markdown, number, time_text

# The set whose tables include the formulas on which both solvers time out.
# Its tables are left out if the run does not have it.
FULL_SET = "ecma2020_mixed_bmp"

# A change of a total time counts only if the ratio new / old of the totals is below FASTER_RATIO or above SLOWER_RATIO.
# Binaries differ by about ±2 % by code layout, and separate runs by up to 5 %.
FASTER_RATIO = 0.95
SLOWER_RATIO = 1.05

# A change of a total time counts only if it is at least this many seconds, as starting z3 alone takes 20-25 ms per run.
MIN_CHANGE = 1.0

# The bootstrap intervals of the ratios of total times: the number of samples, and the seed of the random numbers.
BOOTSTRAP_SAMPLES = 2000
SEED = 1

# The slow formulas take at least this many seconds in one solver.
# The ratios of their times are shown separately from those of all formulas.
SLOW_FORMULA = 1.0

# The numbers of the formulas with the largest savings in the table of the concentration of the saving,
# and how many sets the table names for each of them.
TOP_SAVINGS = [10, 100, 1000]
TOP_SAVING_SETS = 3

# How many call sites the table of the reduction time of FULL_SET lists.
TOP_FULL_SET_SITES = 5

# The plot of the reduction time per call site shows the sites with at least this many seconds in one solver.
MIN_SITE_SECONDS = 1.0

# The outcomes counted in the table of the outcomes.
OUTCOMES = ["solved", "wrong", "unknown", "failed", "timeout"]

# The names of the merged groups of call sites in the tables.
OTHER_SITES = "all other sites"
ALL_GUARD_SITES = "all guard sites"

# The note below the plot of the reduction times on how it treats the timeouts.
# The note of the other plots tells the timeout of the run, so timeout_note writes it.
REDUCTION_TIMEOUT_NOTE = (
    "Formulas that time out in both solvers are excluded; timed-out runs of the other formulas are included."
)

# The columns of the reductions summed per (formula, guard site) for the tables of the reduced automata.
AUTOMATON_COLUMNS = ["reductions", "states_before", "transitions_before"]

# The functions below take the two solvers as the parameters old and new, which are their labels in the tables and plots.


def parse_arguments() -> argparse.Namespace:
    """The command-line arguments."""
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)

    parser.add_argument("run_dir", type=Path, help="output directory of run.py, with reductions.csv")
    parser.add_argument("--old", help="the solver compared to (default: the first one of solvers.csv)")
    parser.add_argument("--new", help="the solver compared (default: the second one of solvers.csv)")
    parser.add_argument("--old-label", help="the name of old in the tables and plots (default: its name in the run)")
    parser.add_argument("--new-label", help="the name of new in the tables and plots (default: its name in the run)")

    return parser.parse_args()


# ---------------------------------------------------------------------------------------------------------------------------------
# loading the run


@dataclass
class RunData:
    """The runs and the reductions of the two solvers, with the solvers named by their labels."""

    runs: pd.DataFrame  # all runs
    kept_runs: pd.DataFrame  # the runs of the kept formulas, on which at least one solver does not time out
    kept_reductions: pd.DataFrame  # the reductions of the kept formulas
    full_set_reductions: pd.DataFrame  # the reductions of all formulas of FULL_SET


def solver_labels(
    run_dir: Path,
    old: str | None,
    new: str | None,
    old_label: str | None,
    new_label: str | None,
) -> dict[str, str]:
    """The labels of the two solvers, by their names in the run, old first.

    old and new default to the first two solvers of solvers.csv, and each label defaults to the name of its solver.
    """
    names = list(report.read_hashcodes(run_dir))
    solvers = report.choose_solvers(names, old, new)

    if len(solvers) != 2:
        sys.exit(f"{run_dir} has one solver, but the analysis compares two.")

    old_name, new_name = solvers
    return {old_name: old_label or old_name, new_name: new_label or new_name}


def load_run_data(run_dir: Path, labels: dict[str, str]) -> RunData:
    """The runs and the reductions of the solvers in labels, with each solver renamed to its label."""
    names = list(labels)

    # The runs and the reductions of the formulas with a run of each solver (see report.load_runs).
    runs = report.load_runs(run_dir, names)
    reductions = report.load_reductions(run_dir, pd.Index(runs.file.unique()), names)

    runs["solver"] = runs.solver.map(labels)
    reductions["solver"] = reductions.solver.map(labels)

    # A formula is kept if at least one solver does not time out on it.
    kept_files = runs.file[runs.outcome != "timeout"].unique()

    return RunData(
        runs=runs,
        kept_runs=runs[runs.file.isin(kept_files)],
        kept_reductions=reductions[reductions.file.isin(kept_files)],
        full_set_reductions=reductions[reductions.set == FULL_SET],
    )


def summed_seconds(reductions: pd.DataFrame, group: str, old: str, new: str) -> pd.DataFrame:
    """The total reduction time per value of the column group (such as file or site), one column per solver."""
    sums = reductions.groupby([group, "solver"]).seconds.sum().unstack("solver", fill_value=0)
    return sums.reindex(columns=[old, new], fill_value=0)


def reduction_seconds(reductions: pd.DataFrame, files: pd.Index, old: str, new: str) -> pd.DataFrame:
    """The total reduction time of each formula in files, one column per solver, zero for a formula without reductions."""
    return summed_seconds(reductions, "file", old, new).reindex(index=files, fill_value=0)


def is_slow(seconds: pd.DataFrame) -> pd.Series:
    """Whether each formula is slow, which is at least SLOW_FORMULA seconds in one solver."""
    return seconds.max(axis=1) >= SLOW_FORMULA


def timeout_note(runs: pd.DataFrame) -> str:
    """The note below the plots of the solving times on how they treat the timeouts."""
    timeout = runs.seconds[runs.outcome == "timeout"].max()
    return f"Formulas that time out in both solvers are excluded; other timeouts count as {timeout:g} s."


# ---------------------------------------------------------------------------------------------------------------------------------
# statistics


class Interval(NamedTuple):
    """A 95 % confidence interval."""

    low: float
    high: float


class PairedTest(NamedTuple):
    """The Wilcoxon signed-rank test of pairs of values (old, new)."""

    pairs: int  # the pairs with both values defined
    differing: int  # the pairs whose two values differ
    r: float  # the rank-biserial correlation, from -1 (new smaller in all differing pairs) to 1 (new larger), or nan
    p: float  # the p-value, or nan if no pair differs


class PairedComparison(NamedTuple):
    """The comparison of the paired values (old, new) of some formulas, such as their solving times."""

    old_total: float
    new_total: float
    test: PairedTest  # the test of the pairs
    interval: Interval  # the bootstrap interval of new_total / old_total


def paired_test(old_values: pd.Series, new_values: pd.Series) -> PairedTest:
    """The Wilcoxon signed-rank test of the pairs (old, new).

    The pairs with an undefined value (e.g. T/Q of 0 states) are left out, and the test also leaves out the pairs with equal values.
    """
    # The differences of the pairs with both values defined, and those of them that are not zero.
    differences = np.asarray(new_values, dtype=float) - np.asarray(old_values, dtype=float)
    differences = differences[np.isfinite(differences)]
    nonzero = differences[differences != 0]

    if len(nonzero) == 0:
        return PairedTest(pairs=len(differences), differing=0, r=float("nan"), p=float("nan"))

    # The rank-biserial correlation: the ranks of the positive differences minus those of the negative ones, relative to all ranks.
    ranks = stats.rankdata(np.abs(nonzero))
    positive = ranks[nonzero > 0].sum()
    negative = ranks[nonzero < 0].sum()
    r = (positive - negative) / (positive + negative)

    # A single differing pair counts as p = 1.
    if len(nonzero) > 1:
        p = stats.wilcoxon(nonzero, zero_method="wilcox", method="approx").pvalue
    else:
        p = 1.0

    return PairedTest(pairs=len(differences), differing=len(nonzero), r=r, p=p)


def bootstrap_interval(old_values: pd.Series, new_values: pd.Series, rng: np.random.Generator) -> Interval:
    """The 95 % percentile bootstrap interval of sum(new) / sum(old), resampling the pairs (old, new)."""
    old_array = np.asarray(old_values, dtype=float)
    new_array = np.asarray(new_values, dtype=float)

    # Each sample draws as many pairs as there are, with replacement.
    # The samples are drawn one by one, as all of them at once would take an array of formulas × BOOTSTRAP_SAMPLES indices.
    ratios = np.empty(BOOTSTRAP_SAMPLES)
    for sample in range(BOOTSTRAP_SAMPLES):
        index = rng.integers(0, len(old_array), len(old_array))
        ratios[sample] = new_array[index].sum() / old_array[index].sum()

    low, high = np.percentile(ratios, [2.5, 97.5])
    return Interval(low, high)


def compare(values: pd.DataFrame, old: str, new: str, rng: np.random.Generator) -> PairedComparison:
    """The comparison of paired values, which have one row per formula and one column per solver."""
    return PairedComparison(
        old_total=values[old].sum(),
        new_total=values[new].sum(),
        test=paired_test(values[old], values[new]),
        interval=bootstrap_interval(values[old], values[new], rng),
    )


def holm(p_values: list[float]) -> np.ndarray:
    """The p-values adjusted by the Holm step-down method, in the same order; a missing p-value counts as 1."""
    p = np.nan_to_num(np.asarray(p_values, dtype=float), nan=1.0)
    adjusted = np.empty(len(p))

    # From the smallest p-value up, the k-th smallest is multiplied by the number of the p-values from it up,
    # and an adjusted p-value is never smaller than the one before it.
    running = 0.0
    for rank, index in enumerate(np.argsort(p)):
        running = max(running, min(1.0, (len(p) - rank) * p[index]))
        adjusted[index] = running

    return adjusted


def verdict(comparison: PairedComparison) -> str:
    """faster or slower if the change of the total is big enough and its interval does not contain 1, no change otherwise.

    A change is big enough if it is at least MIN_CHANGE seconds and the ratio new / old is outside FASTER_RATIO to SLOWER_RATIO.
    """
    ratio = comparison.new_total / comparison.old_total

    if abs(comparison.new_total - comparison.old_total) < MIN_CHANGE:
        return "no change"
    if ratio < FASTER_RATIO and comparison.interval.high < 1:
        return "faster"
    if ratio > SLOWER_RATIO and comparison.interval.low > 1:
        return "slower"

    return "no change"


# ---------------------------------------------------------------------------------------------------------------------------------
# formatting


def p_text(p: float) -> str:
    """A p-value in scientific notation, or - if it is missing."""
    if pd.isna(p):
        return "-"
    return "< 1e-300" if p < 1e-300 else f"{p:.1e}"


def three_decimals(value: float) -> str:
    """A number with three decimals, such as a ratio or r, or - if it is missing."""
    return "-" if pd.isna(value) else f"{value:.3f}"


def interval_text(interval: Interval) -> str:
    """A confidence interval as low–high."""
    return f"{interval.low:.3f}–{interval.high:.3f}"


def total_cells(comparison: PairedComparison, old: str, new: str) -> dict[str, str]:
    """The cells of the totals of a comparison: the two totals, the saved time, and the ratio new / old with its interval."""
    return {
        f"{old} [s]": time_text(comparison.old_total),
        f"{new} [s]": time_text(comparison.new_total),
        "saved [s]": time_text(comparison.old_total - comparison.new_total),
        "ratio": report.ratio(comparison.new_total, comparison.old_total),
        "95 % CI": interval_text(comparison.interval),
    }


# ---------------------------------------------------------------------------------------------------------------------------------
# tables.md: all kept formulas
#
# A function named ..._section returns the Markdown blocks of the section: its heading and its paragraphs and tables.
# seconds has one row per kept formula and one column per solver.


def header_section(data: RunData) -> list[str]:
    """The title, and the numbers of the kept and the excluded formulas."""
    kept = data.kept_runs.file.nunique()
    excluded = data.runs.file.nunique() - kept
    return ["# Tables of RESULTS.md", f"{number(kept)} formulas; {number(excluded)} excluded (timeout in both)."]


def outcomes_section(kept_runs: pd.DataFrame, old: str, new: str) -> list[str]:
    """How many runs of each solver have each of OUTCOMES."""
    rows = []
    for solver in [old, new]:
        runs_of_solver = kept_runs[kept_runs.solver == solver]
        counts = runs_of_solver.outcome.value_counts()

        row = {"solver": solver, "formulas": number(len(runs_of_solver))}
        for outcome in OUTCOMES:
            row[outcome] = number(counts.get(outcome, 0))

        rows.append(row)

    return ["## Outcomes", markdown(rows)]


def time_statistics_section(seconds: pd.DataFrame, old: str, new: str) -> list[str]:
    """The statistics of the solving times and the line of the notable changes of report.py."""
    return [
        "## Time statistics",
        markdown(report.time_statistics(seconds, [old, new])),
        report.notable_changes(seconds, old, new),
    ]


def comparison_row(title: str, comparison: PairedComparison, old: str, new: str) -> dict[str, str]:
    """One row of the table of the paired comparisons: the totals, the test and the verdict."""
    return {
        "": title,
        **total_cells(comparison, old, new),
        "differing pairs": number(comparison.test.differing),
        "r": three_decimals(comparison.test.r),
        "p": p_text(comparison.test.p),
        "verdict": verdict(comparison),
    }


def paired_comparisons_section(
    seconds: pd.DataFrame,
    reduction_times: pd.DataFrame,
    reductions: pd.DataFrame,
    guard_sites: list[str],
    old: str,
    new: str,
    rng: np.random.Generator,
) -> list[str]:
    """Paired comparisons of the solving time, the reduction time at all sites and at the guard sites, and the rest of the time.

    reduction_times has the reduction time of each formula of seconds, and reductions are the reductions of these formulas.
    """
    guard_times = reduction_seconds(reductions[reductions.site.isin(guard_sites)], seconds.index, old, new)
    rest = seconds - reduction_times

    # The comparisons draw their bootstrap samples in this order.
    rows = [
        comparison_row("solving time", compare(seconds, old, new, rng), old, new),
        comparison_row("reduction time, all sites", compare(reduction_times, old, new, rng), old, new),
        comparison_row("reduction time, guard sites", compare(guard_times, old, new, rng), old, new),
        comparison_row("solving time without reductions", compare(rest, old, new, rng), old, new),
    ]

    return ["## Paired comparisons (per formula)", markdown(rows)]


def ratio_row(title: str, ratios: pd.Series) -> dict[str, str]:
    """One row of the table of the ratios per formula: how many formulas, and the median and geometric mean of their ratios."""
    return {
        "formulas": title,
        "count": number(len(ratios)),
        "median ratio": three_decimals(ratios.median()),
        "geometric mean ratio": three_decimals(stats.gmean(ratios)),
    }


def ratios_section(seconds: pd.DataFrame, old: str, new: str) -> list[str]:
    """The median and geometric mean of the ratios new / old per formula, of all formulas and of the slow ones."""
    ratios = report.time_ratios(seconds, old, new)

    rows = [
        ratio_row("all", ratios),
        ratio_row(f">= {SLOW_FORMULA:g} s in one solver", ratios[is_slow(seconds)]),
    ]

    return ["## Ratios per formula", markdown(rows)]


def concentration_section(seconds: pd.DataFrame, sets: pd.Series, old: str, new: str) -> list[str]:
    """How much of the net saved solving time the formulas with the largest savings give, and from which sets they are.

    sets has the set of each formula.
    """
    saved = (seconds[old] - seconds[new]).sort_values(ascending=False)
    net = saved.sum()

    rows = []
    for top in TOP_SAVINGS:
        # The formulas with the largest savings, and the sets that give the most of their saving.
        best = saved.head(top)
        top_sets = best.groupby(sets[best.index]).sum().sort_values(ascending=False).head(TOP_SAVING_SETS)

        row = {
            "formulas with the largest saving": number(top),
            "their saving [s]": time_text(best.sum()),
            "share of the net saving": f"{best.sum() / net:.0%}",
            "main sets (saving [s])": ", ".join(f"{name} ({number(value)})" for name, value in top_sets.items()),
        }
        rows.append(row)

    # The formulas slower in new, whose saving is negative.
    slower = saved[saved < 0]
    row = {
        "formulas with the largest saving": f"all {number(len(slower))} slower formulas",
        "their saving [s]": time_text(slower.sum()),
        "share of the net saving": f"{slower.sum() / net:.0%}",
        "main sets (saving [s])": "",
    }
    rows.append(row)

    return ["## Concentration of the saved solving time", markdown(rows)]


# ---------------------------------------------------------------------------------------------------------------------------------
# tables.md: per set


@dataclass
class SetComparison:
    """The solving and reduction times of the kept formulas of one set in the two solvers."""

    name: str
    formulas: int
    solving: PairedComparison  # the comparison of the solving times
    old_reduction_seconds: float  # the total reduction time of old
    new_reduction_seconds: float  # the total reduction time of new
    p_holm: float = float("nan")  # the p-value of the test of the solving times, adjusted for the number of sets

    @property
    def saved(self) -> float:
        """The saved solving time."""
        return self.solving.old_total - self.solving.new_total

    @property
    def rest_change(self) -> float:
        """The change of the solving time without the reductions."""
        old_rest = self.solving.old_total - self.old_reduction_seconds
        new_rest = self.solving.new_total - self.new_reduction_seconds
        return new_rest - old_rest


def set_comparison(
    name: str,
    seconds: pd.DataFrame,
    reduction_times: pd.DataFrame,
    old: str,
    new: str,
    rng: np.random.Generator,
) -> SetComparison:
    """The comparison of one set, whose formulas are the rows of seconds.

    reduction_times has the reduction time of each kept formula, one column per solver.
    """
    set_reduction_times = reduction_times.loc[seconds.index]

    return SetComparison(
        name=name,
        formulas=len(seconds),
        solving=compare(seconds, old, new, rng),
        old_reduction_seconds=set_reduction_times[old].sum(),
        new_reduction_seconds=set_reduction_times[new].sum(),
    )


def set_time_row(comparison: SetComparison, old: str, new: str) -> dict[str, str]:
    """One row of the table of the solving times per set."""
    return {
        "set": comparison.name,
        "formulas": number(comparison.formulas),
        **total_cells(comparison.solving, old, new),
        "r": three_decimals(comparison.solving.test.r),
        "p (Holm)": p_text(comparison.p_holm),
        "verdict": verdict(comparison.solving),
    }


def set_reduction_row(comparison: SetComparison, old: str, new: str) -> dict[str, str]:
    """One row of the table of the reduction times per set, with the change of the solving time without them."""
    old_reduction = comparison.old_reduction_seconds
    new_reduction = comparison.new_reduction_seconds

    return {
        "set": comparison.name,
        f"reduction {old} [s]": time_text(old_reduction),
        f"reduction {new} [s]": time_text(new_reduction),
        "reduction saved [s]": time_text(old_reduction - new_reduction),
        "share of reductions in solving, old": f"{old_reduction / comparison.solving.old_total:.1%}",
        "change of the rest [s]": f"{comparison.rest_change:+,.1f}",
    }


def per_set_sections(
    seconds: pd.DataFrame,
    sets: pd.Series,
    reduction_times: pd.DataFrame,
    old: str,
    new: str,
    rng: np.random.Generator,
) -> list[str]:
    """Two tables with one row per set, sorted by the saved solving time: the solving times, and the reduction times.

    sets has the set of each formula, and reduction_times has the reduction time of each formula, one column per solver.
    """
    # The comparisons draw their bootstrap samples in the order of the names of the sets.
    comparisons = []
    for set_name, set_seconds in seconds.groupby(sets):
        comparisons.append(set_comparison(set_name, set_seconds, reduction_times, old, new, rng))

    # The p-values adjusted for testing many sets.
    adjusted = holm([comparison.solving.test.p for comparison in comparisons])
    for comparison, p in zip(comparisons, adjusted):
        comparison.p_holm = p

    comparisons.sort(key=lambda comparison: comparison.saved, reverse=True)

    time_rows = [set_time_row(comparison, old, new) for comparison in comparisons]
    reduction_rows = [set_reduction_row(comparison, old, new) for comparison in comparisons]

    return [
        "## Per set (sorted by saved solving time)",
        markdown(time_rows),
        "## Reduction time per set (same order)",
        markdown(reduction_rows),
    ]


# ---------------------------------------------------------------------------------------------------------------------------------
# tables.md: reductions


def site_row(site: str, solver: str, sums: pd.Series) -> dict[str, str]:
    """One row of the table of the reductions per site: the sums of the reductions of a solver at a site, their means and shares."""
    count = sums.reductions
    row = {"site": site, "solver": solver, "reductions": number(count), "time [s]": time_text(sums.seconds)}

    # The means and the shares are undefined without reductions.
    if count == 0:
        undefined = [
            "ms per reduction",
            "mean states",
            "mean transitions",
            "mean density T/Q",
            "states removed",
            "transitions removed",
        ]
        return row | {title: "-" for title in undefined}

    row["ms per reduction"] = f"{sums.seconds * 1e3 / count:.2f}"
    row["mean states"] = f"{sums.states_before / count:.1f}"
    row["mean transitions"] = f"{sums.transitions_before / count:.1f}"
    row["mean density T/Q"] = f"{sums.transitions_before / sums.states_before:.1f}"
    row["states removed"] = f"{1 - sums.states_after / sums.states_before:.1%}"
    row["transitions removed"] = f"{1 - sums.transitions_after / sums.transitions_before:.1%}"

    return row


def sites_section(reductions: pd.DataFrame, guard_sites: list[str], old: str, new: str) -> list[str]:
    """The reductions of each guard site and of all other sites together, one row per site and solver."""
    sites = [*guard_sites, OTHER_SITES]

    # The reductions summed per site and solver, with the sites without a guard merged into OTHER_SITES.
    site = reductions.site.where(reductions.site.isin(guard_sites), OTHER_SITES)
    sums = reductions.groupby([site, "solver"]).sum(numeric_only=True)
    sums = sums.reindex(pd.MultiIndex.from_product([sites, [old, new]]), fill_value=0)

    rows = []
    for (site_name, solver), site_sums in sums.iterrows():
        rows.append(site_row(site_name, solver, site_sums))

    return ["## Reductions per site", markdown(rows)]


class Quantity(NamedTuple):
    """A quantity of the reduced automata of a (formula, guard site), computed from the sums of its reductions."""

    title: str
    numerator: str  # the summed column
    denominator: str | None = None  # the summed column that the numerator is divided by, if any

    def values(self, sums: pd.DataFrame, solver: str) -> pd.Series:
        """The quantity of each row of the sums of guard_site_sums, for one solver."""
        values = sums[self.numerator][solver]
        if self.denominator:
            values = values / sums[self.denominator][solver]
        return values


# The quantities compared in the table of the reduced automata.
REDUCTIONS_PER_FORMULA = Quantity("reductions per formula", "reductions")
MEAN_STATES = Quantity("mean states", "states_before", "reductions")
MEAN_TRANSITIONS = Quantity("mean transitions", "transitions_before", "reductions")
MEAN_DENSITY = Quantity("mean density T/Q", "transitions_before", "states_before")
QUANTITIES = [REDUCTIONS_PER_FORMULA, MEAN_STATES, MEAN_TRANSITIONS, MEAN_DENSITY]


def guard_site_sums(reductions: pd.DataFrame, guard_sites: list[str], old: str, new: str) -> pd.DataFrame:
    """The AUTOMATON_COLUMNS of the reductions at the guard sites summed per (formula, site): one column per (column, solver)."""
    at_guard_sites = reductions[reductions.site.isin(guard_sites)]
    sums = at_guard_sites.groupby(["file", "site", "solver"])[AUTOMATON_COLUMNS].sum().unstack("solver", fill_value=0)

    # A solver without reductions has no columns yet.
    return sums.reindex(columns=pd.MultiIndex.from_product([AUTOMATON_COLUMNS, [old, new]]), fill_value=0)


def rows_of_site(sums: pd.DataFrame, site: str) -> pd.DataFrame:
    """The rows of one site in the sums of guard_site_sums."""
    return sums[sums.index.get_level_values("site") == site]


def quantity_rows(site: str, sums: pd.DataFrame, old: str, new: str) -> list[dict[str, str]]:
    """The rows of the table of the reduced automata of a site: per quantity, its medians in the two solvers and their test.

    sums are the rows of the site in the sums of guard_site_sums.
    """
    rows = []
    for quantity in QUANTITIES:
        old_values = quantity.values(sums, old)
        new_values = quantity.values(sums, new)
        test = paired_test(old_values, new_values)
        differences = (new_values - old_values)[new_values != old_values]

        row = {
            "site": site,
            "quantity": quantity.title,
            "pairs": number(test.pairs),
            "differing": number(test.differing),
            f"median {old}": f"{old_values.median():.1f}",
            f"median {new}": f"{new_values.median():.1f}",
            "median difference (differing)": f"{differences.median():+.1f}" if test.differing else "-",
            "r": three_decimals(test.r),
            "p": p_text(test.p),
        }
        rows.append(row)

    return rows


def both_solvers_reduce_section(guard_sums: pd.DataFrame, guard_sites: list[str], old: str, new: str) -> list[str]:
    """The paired tests of the QUANTITIES of the (formula, guard site) pairs that both solvers reduce, per site and for all of them.

    guard_sums are the sums of guard_site_sums.
    """
    counts = guard_sums["reductions"]
    both = guard_sums[(counts[old] > 0) & (counts[new] > 0)]

    rows = []
    for site in guard_sites:
        rows += quantity_rows(site, rows_of_site(both, site), old, new)
    rows += quantity_rows(ALL_GUARD_SITES, both, old, new)

    return ["## Mean reduced automaton per (formula, guard site), both solvers reduce", markdown(rows)]


def one_solver_row(solver: str, site: str, sums: pd.DataFrame) -> dict[str, str]:
    """One row of the table of the pairs reduced by one solver only: the pairs of a site, and their mean automata.

    sums are the rows of these pairs in the sums of guard_site_sums.
    """
    states = sums["states_before"][solver]
    transitions = sums["transitions_before"][solver]

    return {
        "reduced by": f"{solver} only",
        "site": site,
        "formulas": number(len(sums)),
        "reductions": number(sums["reductions"][solver].sum()),
        "median mean states": f"{MEAN_STATES.values(sums, solver).median():.1f}",
        "median mean transitions": f"{MEAN_TRANSITIONS.values(sums, solver).median():.1f}",
        "mean density T/Q": f"{transitions.sum() / states.sum():.1f}",
    }


def one_solver_reduces_section(guard_sums: pd.DataFrame, guard_sites: list[str], old: str, new: str) -> list[str]:
    """The (formula, guard site) pairs that only one solver reduces, per solver and site, with their mean automata.

    guard_sums are the sums of guard_site_sums.
    """
    counts = guard_sums["reductions"]

    rows = []
    for solver, other in [(old, new), (new, old)]:
        only_solver = guard_sums[(counts[solver] > 0) & (counts[other] == 0)]

        for site in guard_sites:
            of_site = rows_of_site(only_solver, site)
            if len(of_site) > 0:
                rows.append(one_solver_row(solver, site, of_site))

    return ["## (formula, guard site) pairs reduced by one solver only", markdown(rows)]


# ---------------------------------------------------------------------------------------------------------------------------------
# tables.md: single formulas and FULL_SET


def changed_formulas_section(tables: report.FormulaTables, old: str, new: str) -> list[str]:
    """The formulas with a different outcome in the two solvers, sorted by set and name."""
    outcomes = tables.outcomes
    changed = outcomes.index[outcomes[old] != outcomes[new]]

    rows = []
    for file in sorted(changed, key=lambda file: (tables.sets[file], Path(file).name)):
        row = {
            "formula": Path(file).name,
            "set": tables.sets[file],
            old: outcomes.at[file, old],
            new: outcomes.at[file, new],
            f"{old} [s]": time_text(tables.seconds.at[file, old]),
            f"{new} [s]": time_text(tables.seconds.at[file, new]),
        }
        rows.append(row)

    return ["## Changed outcomes", markdown(rows) if rows else "None."]


class FullSetFormulas(NamedTuple):
    """The formulas of FULL_SET by their timeouts."""

    shared_timeouts: pd.Index  # the formulas on which both solvers time out
    finished: pd.Index  # the formulas on which neither solver times out


def total_row(title: str, times: pd.DataFrame, files: pd.Index, old: str, new: str) -> dict[str, str]:
    """One row of the table of FULL_SET: the total times of the formulas in files, times having one column per solver."""
    return {
        "": title,
        "formulas": number(len(files)),
        f"{old} [s]": time_text(times.loc[files, old].sum()),
        f"{new} [s]": time_text(times.loc[files, new].sum()),
    }


def full_set_total_rows(
    seconds: pd.DataFrame,
    reduction_times: pd.DataFrame,
    formulas: FullSetFormulas,
    old: str,
    new: str,
) -> list[dict[str, str]]:
    """The solving and reduction times of all formulas of FULL_SET, of the shared timeouts and of the finished formulas."""
    rest = seconds - reduction_times

    return [
        total_row("all formulas", seconds, seconds.index, old, new),
        total_row("shared timeouts", seconds, formulas.shared_timeouts, old, new),
        total_row("no timeout: solving", seconds, formulas.finished, old, new),
        total_row("no timeout: reductions", reduction_times, formulas.finished, old, new),
        total_row("no timeout: solving without reductions", rest, formulas.finished, old, new),
        total_row("shared timeouts: logged reductions", reduction_times, formulas.shared_timeouts, old, new),
    ]


def prefixes_line(shared_timeouts: pd.Index) -> str:
    """How many shared timeouts have each prefix of the name, which is the part of the name of a formula before its last _."""
    prefixes = pd.Series([Path(file).name.rsplit("_", 1)[0] for file in shared_timeouts]).value_counts()
    return "Shared timeouts by name prefix: " + ", ".join(f"{prefix} {count}" for prefix, count in prefixes.items())


def full_set_site_rows(reductions: pd.DataFrame, formulas: FullSetFormulas, old: str, new: str) -> list[dict[str, str]]:
    """The TOP_FULL_SET_SITES sites with the longest reduction time of old, of the finished formulas and of the shared timeouts.

    reductions are the reductions of FULL_SET.
    """
    rows = []
    for title, files in [("no timeout", formulas.finished), ("shared timeouts", formulas.shared_timeouts)]:
        sums = summed_seconds(reductions[reductions.file.isin(files)], "site", old, new)
        sums = sums.sort_values(old, ascending=False).head(TOP_FULL_SET_SITES)

        for site in sums.index:
            row = {
                "formulas": title,
                "site": site,
                f"{old} [s]": time_text(sums.at[site, old]),
                f"{new} [s]": time_text(sums.at[site, new]),
            }
            rows.append(row)

    return rows


def full_set_sections(runs: pd.DataFrame, reductions: pd.DataFrame, old: str, new: str) -> list[str]:
    """The times of all formulas of FULL_SET, the shared timeouts included, and its reduction time per site.

    runs are all runs, and reductions are the reductions of all formulas of FULL_SET.
    """
    set_runs = runs[runs.set == FULL_SET]
    if len(set_runs) == 0:
        return []

    # The formulas on which both solvers time out, and those on which neither does.
    tables = report.formula_tables(set_runs)
    timed_out = tables.outcomes[[old, new]] == "timeout"
    formulas = FullSetFormulas(
        shared_timeouts=timed_out.index[timed_out.all(axis=1)],
        finished=timed_out.index[~timed_out.any(axis=1)],
    )

    seconds = tables.seconds[[old, new]]
    reduction_times = reduction_seconds(reductions, seconds.index, old, new)

    return [
        f"## {FULL_SET}, all formulas",
        markdown(full_set_total_rows(seconds, reduction_times, formulas, old, new)),
        prefixes_line(formulas.shared_timeouts),
        f"## {FULL_SET}: reduction time per site (top {TOP_FULL_SET_SITES})",
        markdown(full_set_site_rows(reductions, formulas, old, new)),
    ]


# ---------------------------------------------------------------------------------------------------------------------------------
# plots


def plot_ratio_distribution(seconds: pd.DataFrame, old: str, new: str, path: Path, note: str) -> None:
    """The distribution (ECDF) of the ratios new / old per formula, of all formulas and of the slow ones."""
    ratios = report.time_ratios(seconds, old, new)
    slow = is_slow(seconds)
    figure, axes = plt.subplots(figsize=(7, 4.5))

    # One curve of all formulas and one of the slow formulas.
    curves = {
        f"all formulas ({len(ratios):,})": ratios,
        f"formulas of at least {SLOW_FORMULA:g} s in one solver ({slow.sum():,})": ratios[slow],
    }
    for label, values in curves.items():
        sns.ecdfplot(x=values, label=label, ax=axes)

    # The vertical line of the same time, and a log scale from 0.01 to 100 with plain numbers at the ticks.
    low, high = 0.01, 100
    axes.axvline(1, color="gray", linewidth=1, linestyle="--")
    axes.set_xscale("log")
    axes.set_xlim(low, high)
    axes.set_xticks([tick for tick in plots.RATIO_TICKS if low <= tick <= high])
    axes.xaxis.set_major_formatter(plots.PLAIN_NUMBERS)

    axes.set(
        xlabel=f"time of {new} / time of {old} (per formula)",
        ylabel="share of formulas",
        title="Distribution of the ratios per formula",
    )
    axes.legend(loc="upper left", fontsize=8)

    plots.save(figure, path, note)


def plot_site_times(reductions: pd.DataFrame, guard_sites: list[str], old: str, new: str, path: Path) -> None:
    """The total reduction time of each site with at least MIN_SITE_SECONDS in one solver, the guard sites marked with *."""
    sums = summed_seconds(reductions, "site", old, new)
    sums = sums[sums.max(axis=1) >= MIN_SITE_SECONDS].sort_values(old, ascending=False)

    # One row per site and solver, as seaborn needs it.
    long = sums.reset_index().melt(id_vars="site", var_name="solver", value_name="seconds")
    long["site"] = long.site.map(lambda site: f"* {site}" if site in guard_sites else site)

    # One pair of bars per site, the longest reduction time of old on top.
    figure, axes = plt.subplots(figsize=(8, 0.45 * len(sums) + 1.5))
    sns.barplot(data=long, y="site", x="seconds", hue="solver", hue_order=[old, new], ax=axes)
    axes.set(xlabel="reduction time [s]", ylabel="* = guard site", title="Reduction time per call site")

    plots.save(figure, path, REDUCTION_TIMEOUT_NOTE)


# ---------------------------------------------------------------------------------------------------------------------------------


def main() -> None:
    """Writes tables.md and the plots into RUN_DIR/analysis."""
    args = parse_arguments()
    out_dir = args.run_dir / "analysis"

    # The two solvers are named by their labels from here on.
    labels = solver_labels(args.run_dir, args.old, args.new, args.old_label, args.new_label)
    old, new = labels.values()
    data = load_run_data(args.run_dir, labels)

    # The tables per kept formula, the reduction time of each kept formula, and the call sites with guarded reductions.
    tables = report.formula_tables(data.kept_runs)
    seconds = tables.seconds[[old, new]]
    reduction_times = reduction_seconds(data.kept_reductions, seconds.index, old, new)
    guard_sites = sorted(data.kept_reductions.site[data.kept_reductions.guarded == 1].unique())
    guard_sums = guard_site_sums(data.kept_reductions, guard_sites, old, new)

    # The paired comparisons and the per-set sections draw their bootstrap samples from one generator, in this order.
    rng = np.random.default_rng(SEED)

    # tables.md
    blocks = header_section(data)
    blocks += outcomes_section(data.kept_runs, old, new)
    blocks += time_statistics_section(seconds, old, new)
    blocks += paired_comparisons_section(seconds, reduction_times, data.kept_reductions, guard_sites, old, new, rng)
    blocks += ratios_section(seconds, old, new)
    blocks += concentration_section(seconds, tables.sets, old, new)
    blocks += per_set_sections(seconds, tables.sets, reduction_times, old, new, rng)
    blocks += sites_section(data.kept_reductions, guard_sites, old, new)
    blocks += both_solvers_reduce_section(guard_sums, guard_sites, old, new)
    blocks += one_solver_reduces_section(guard_sums, guard_sites, old, new)
    blocks += changed_formulas_section(tables, old, new)
    blocks += full_set_sections(data.runs, data.full_set_reductions, old, new)

    out_dir.mkdir(exist_ok=True)
    (out_dir / "tables.md").write_text(report.join_blocks(blocks))

    # The plots of plots.py, then the ratios per formula and the reduction time per site.
    plot_dir = out_dir / "plots"
    note = timeout_note(data.runs)

    plots.write_plots(data.kept_runs, old, new, plot_dir, note)
    plot_ratio_distribution(seconds, old, new, plot_dir / "ratios.png", note)
    plot_site_times(data.kept_reductions, guard_sites, old, new, plot_dir / "sites.png")


if __name__ == "__main__":
    main()
