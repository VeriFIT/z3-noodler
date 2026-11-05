"""The results of run_bench.py as pandas tables, shared by report.py and plots.py."""
import numpy as np
import pandas as pd

import benchlib

# Times below this count as this in ratios of times, so that very fast runs do not produce huge ratios.
MIN_TIME = 0.01
# A notable change of the time of a formula: more than this many times and this many seconds faster or slower.
NOTABLE_RATIO = 2
NOTABLE_SECONDS = 0.5


def load_runs(paths, solvers=None):
    """The runs of the given runs.csv files, only of the formulas with a run of every solver.

    The outcome is recomputed by benchlib.outcome, and a solved run whose answer differs from another solver's answer is marked as disagree.
    """
    runs = pd.concat([pd.read_csv(path, dtype={"expected": str, "result": str}) for path in paths], ignore_index=True)
    # a formula listed in two sets is run twice
    runs = runs.drop_duplicates(["file", "solver"])
    if solvers:
        runs = runs[runs.solver.isin(solvers)]
    runs["outcome"] = [benchlib.outcome(expected, result) for expected, result in zip(runs.expected, runs.result)]
    solvers = solvers or sorted(runs.solver.unique())
    runs_per_file = runs.groupby("file").solver.nunique()
    runs = runs[runs.file.isin(runs_per_file[runs_per_file == len(solvers)].index)].copy()
    mark_disagreements(runs)
    return runs, solvers


def mark_disagreements(runs):
    answers_per_file = runs[runs.outcome == "solved"].groupby("file").result.nunique()
    disagreeing_files = answers_per_file[answers_per_file > 1].index
    runs.loc[runs.file.isin(disagreeing_files) & (runs.outcome == "solved"), "outcome"] = "disagree"


def seconds_table(runs):
    """One row per formula, one column per solver: the time."""
    return runs.pivot(index="file", columns="solver", values="seconds")


def outcome_table(runs):
    """One row per formula, one column per solver: the outcome."""
    return runs.pivot(index="file", columns="solver", values="outcome")


def solved_by_all(runs):
    """The formulas that every solver solved."""
    all_solved = outcome_table(runs).eq("solved").all(axis=1)
    return all_solved[all_solved].index


def time_ratio(new_seconds, old_seconds):
    return new_seconds.clip(lower=MIN_TIME) / old_seconds.clip(lower=MIN_TIME)


def geometric_mean(values):
    return float(np.exp(np.log(values).mean()))


def notably_faster(new_seconds, old_seconds):
    return (time_ratio(new_seconds, old_seconds) < 1 / NOTABLE_RATIO) & (old_seconds - new_seconds > NOTABLE_SECONDS)


def notably_slower(new_seconds, old_seconds):
    return (time_ratio(new_seconds, old_seconds) > NOTABLE_RATIO) & (new_seconds - old_seconds > NOTABLE_SECONDS)
