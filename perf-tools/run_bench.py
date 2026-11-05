#!/usr/bin/env python3
"""Runs solvers on benchmark formulas and records the results.

All runs go into one pool in random order of the formulas; the runs of one formula are next to each other, so that the solvers run
under similar load and a stopped benchmark leaves few formulas with only some of their runs.
Writes into OUT_DIR:
  runs.csv          one row per run (file, set, solver, expected, result, outcome, seconds; with --reduce-log also the number and the
                    total time of the mata::nfa::reduce calls);
  reduce-calls.csv  with --reduce-log, one row per distinct reduce call of a run (see reduce_log.py);
  provenance.json   the command, the machine, the repository state and the solver binaries.
A rerun with the same OUT_DIR skips the runs already in runs.csv.

Examples:
  run_bench.py out --solver old=build/release/variants/old/z3 --solver new=build/release/z3 --sets all --sample-per-set 100 --minutes 40
  run_bench.py out --solver stats=build/release/variants/stats/z3 --list formulas.txt --reduce-log
"""
import argparse
import itertools
import random
import time
from pathlib import Path

import benchlib
import reduce_log

RUN_FIELDS = ["file", "set", "solver", "expected", "result", "outcome", "seconds", "reduce_calls", "reduce_ns"]
CALL_FIELDS = ["file", "set", "solver"] + reduce_log.CALL_FIELDS


def parse_arguments():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("out_dir", type=Path)
    parser.add_argument("--solver", action="append", required=True, type=benchlib.parse_name_value, metavar="NAME=Z3",
                        help="a solver binary under a name (repeat the option for more solvers)")
    formulas = parser.add_mutually_exclusive_group(required=True)
    formulas.add_argument("--sets", help='comma-separated sets of smt-bench, or "all" for all available ones')
    formulas.add_argument("--list", help="a list file with lines SET;PATH;OPTIONS")
    parser.add_argument("--sample-per-set", type=int, help="only a random sample of this many formulas of each set")
    parser.add_argument("--seed", type=int, default=0, help="seed of the sample and of the order of the runs")
    parser.add_argument("--jobs", type=int, default=4, help="runs in parallel")
    parser.add_argument("--timeout", type=float, default=30, help="seconds per run")
    parser.add_argument("--memory-gb", type=float, default=6, help="address-space limit of one run")
    parser.add_argument("--minutes", type=float, help="no run starts after this many minutes")
    parser.add_argument("--reduce-log", action="store_true",
                        help="record the mata::nfa::reduce calls (the solvers must be built with the reduce wrapper)")
    return parser.parse_args()


def planned_runs(formulas, solvers, done, seed):
    """The (formula, solver name) pairs still to run: formulas in random order, the solvers of a formula next to each other."""
    rng = random.Random(seed)
    formulas = list(formulas)
    rng.shuffle(formulas)
    runs = []
    for formula in formulas:
        names = list(solvers)
        rng.shuffle(names)
        runs += [(formula, name) for name in names if (formula.path, name) not in done]
    return runs


def main():
    args = parse_arguments()
    args.out_dir.mkdir(parents=True, exist_ok=True)
    solvers = dict(args.solver)
    benchlib.write_provenance(args.out_dir / "provenance.json", args.solver)

    formulas = benchlib.select_formulas(args.sets, args.list, args.sample_per_set, args.seed)
    done = {(row["file"], row["solver"]) for row in benchlib.read_csv(args.out_dir / "runs.csv")}
    runs = planned_runs(formulas, solvers, done, args.seed)
    print(f"{len(formulas)} formulas, {len(done)} runs done before, {len(runs)} to run", flush=True)

    log_dir = args.out_dir / "logs"
    log_dir.mkdir(exist_ok=True)
    log_numbers = itertools.count()
    site_names = {name: reduce_log.SiteNames(z3) for name, z3 in solvers.items()}

    def run(task):
        formula, name = task
        if not args.reduce_log:
            return benchlib.run_solver(solvers[name], formula, args.timeout, args.memory_gb), []
        log = log_dir / f"{next(log_numbers)}.log"
        result = benchlib.run_solver(solvers[name], formula, args.timeout, args.memory_gb, env={"REDUCE_LOG": str(log)})
        calls = reduce_log.read_merged_calls(log, time.monotonic_ns()) if log.exists() else []
        log.unlink(missing_ok=True)
        return result, calls

    run_rows = benchlib.CsvAppender(args.out_dir / "runs.csv", RUN_FIELDS)
    call_rows = benchlib.CsvAppender(args.out_dir / "reduce-calls.csv", CALL_FIELDS) if args.reduce_log else None
    progress = benchlib.Progress(len(runs))
    for (formula, name), (result, calls) in benchlib.run_in_pool(runs, run, args.jobs, args.minutes):
        row = {"file": formula.path, "set": formula.set, "solver": name, "expected": result.expected, "result": result.result,
               "outcome": benchlib.outcome(result.expected, result.result), "seconds": f"{result.seconds:.3f}"}
        if args.reduce_log:
            site_names[name].add_sites(calls)
            row.update(reduce_calls=sum(call["repeats"] for call in calls), reduce_ns=sum(call["ns_sum"] for call in calls))
            for call in calls:
                call_rows.write({"file": formula.path, "set": formula.set, "solver": name, **call})
        run_rows.write(row)
        progress.step()
    run_rows.close()
    if call_rows:
        call_rows.close()


if __name__ == "__main__":
    main()
