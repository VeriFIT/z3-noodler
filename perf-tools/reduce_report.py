#!/usr/bin/env python3
"""How many automata the solvers reduce by mata::nfa::reduce, from a benchmark of run_bench.py with --reduce-log.

Counts only the formulas that every solver finished (no timeout or failure), so that the solvers did the same work.
Sections: per solver, per call site and per set: the reductions, the states and transitions before and after, and their time.
A reduction is one call of mata::nfa::reduce; repeated calls on the same automaton (e.g., in repeated final checks) count each time.

Example: reduce_report.py out --baseline old --out out/REDUCE-REPORT.md
"""
import argparse
from pathlib import Path

import pandas as pd

import reduce_log


def parse_arguments():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("bench_dir", type=Path, help="output directory of run_bench.py with runs.csv and reduce-calls.csv")
    parser.add_argument("--baseline", required=True, help="the solver listed first and used for sorting")
    parser.add_argument("--out", help="write the report to this file (it is printed in any case)")
    return parser.parse_args()


def load(bench_dir):
    """The runs and the reduce calls of the formulas that every solver finished."""
    runs = pd.read_csv(bench_dir / "runs.csv")
    calls = pd.read_csv(bench_dir / "reduce-calls.csv", dtype={"caller": str, "operation": str})
    solvers = runs.solver.unique()
    finished = runs[runs.outcome.isin(["solved", "wrong", "unknown"])]
    finished_by_all = finished.groupby("file").solver.nunique() == len(solvers)
    files = finished_by_all[finished_by_all].index
    runs = runs[runs.file.isin(files)]
    calls = calls[calls.file.isin(files)].copy()
    calls["states_before"] = calls.states * calls.repeats
    calls["states_after"] = calls.res_states * calls.repeats
    calls["transitions_before"] = calls.transitions * calls.repeats
    calls["transitions_after"] = calls.res_transitions * calls.repeats
    calls["guarded"] = calls.site.map(reduce_log.is_guarded)
    return runs, calls


def totals(calls, group):
    """The reductions, their sizes before and after, and their time, summed per group."""
    table = calls.groupby(group).agg(reductions=("repeats", "sum"), states_before=("states_before", "sum"),
                                     states_after=("states_after", "sum"), transitions_before=("transitions_before", "sum"),
                                     transitions_after=("transitions_after", "sum"), reduce_seconds=("ns_sum", "sum"))
    table["reduce_seconds"] /= 1e9
    table["states_removed"] = table.states_before - table.states_after
    return table


def per_solver(runs, calls):
    table = totals(calls, "solver")
    table.insert(0, "formulas", runs.groupby("solver").file.nunique())
    table["solving_seconds"] = runs.groupby("solver").seconds.sum()
    guarded = totals(calls[calls.guarded], "solver")
    table["guarded_reductions"] = guarded.reductions
    table["guarded_reduce_seconds"] = guarded.reduce_seconds
    return table


def side_by_side(table, solvers, columns):
    """One row per group, the given columns of each solver next to each other (the table is indexed by group and solver)."""
    wide = table[columns].unstack("solver").fillna(0)
    wide = wide.reindex(columns=[(column, solver) for solver in solvers for column in columns])
    wide.columns = [f"{solver} {column}" for column, solver in wide.columns]
    return wide


def report(runs, calls, solvers):
    files = runs.file.nunique()
    sites = totals(calls, ["site", "solver"])
    sets = totals(calls, ["set", "solver"])
    site_table = side_by_side(sites, solvers, ["reductions", "reduce_seconds", "states_removed"])
    site_table.insert(0, "guarded", [reduce_log.is_guarded(site) for site in site_table.index])
    site_table = site_table.sort_values(f"{solvers[0]} reductions", ascending=False)
    set_table = side_by_side(sets, solvers, ["reductions", "reduce_seconds"]).sort_values(f"{solvers[0]} reductions", ascending=False)
    sections = [f"{files} formulas finished by every solver ({', '.join(solvers)}).",
                "Guarded sites: the regex construction (except loop bodies), the final-check intersection and the membership heuristics.",
                "## Per solver", per_solver(runs, calls).loc[solvers].T.to_markdown(floatfmt=".4g"),
                "## Per call site", site_table.to_markdown(floatfmt=".4g"),
                "## Per set", set_table.to_markdown(floatfmt=".4g")]
    return "\n\n".join(sections) + "\n"


def main():
    args = parse_arguments()
    runs, calls = load(args.bench_dir)
    solvers = [args.baseline] + sorted(set(runs.solver) - {args.baseline})
    text = report(runs, calls, solvers)
    if args.out:
        with open(args.out, "w") as f:
            f.write(text)
    print(text)


if __name__ == "__main__":
    main()
