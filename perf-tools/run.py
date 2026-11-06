#!/usr/bin/env python3
"""Runs solvers on the formulas of smt-bench and records the results.

If perf-tools/smt-bench does not exist yet, the script first clones smt-bench there, checks out its submodules and downloads the
SMT-LIB formulas (this needs git, curl and unzstd).
The runs go into one pool in a random order of the formulas, and the runs of one formula are next to each other, so that the solvers
run under similar load.
Writes into OUT_DIR:
  solvers.csv     the name, path and build hashcode of each solver;
  runs.csv        one row per run: file, set, solver, expected status, result, outcome and seconds;
  reductions.csv  with --reduce-log, the mata::nfa::reduce calls of each run, summed per call site (see instrumentation/reduce_wrap.cpp).
A rerun with the same OUT_DIR skips the runs already in runs.csv.
Only the Python standard library is used, so that the script runs on any machine.

Example:
  run.py runs/guard --solver old=bin/z3-old --solver new=bin/z3-new
"""

import argparse
import csv
import os
import random
import re
import subprocess
import time
from multiprocessing.pool import ThreadPool
from pathlib import Path

TOOLS = Path(__file__).resolve().parent
SMT_BENCH = TOOLS / "smt-bench"
SMT_BENCH_REPOSITORY = "https://github.com/Kumismar/smt-bench.git"
SMT_BENCH_BRANCH = "ecma2020-mixed-bmp"

# smtcomp25 only repeats formulas of other sets (pcp, rna, hornstr, negated_predicates, matching).
SKIPPED_SETS = ["smtcomp25"]
# The statuses of the mixed ECMAScript constraints assume the engine semantics (RegExp.test() searches for a matching substring).
SET_OPTIONS = {"ecma2020_mixed_bmp": ["smt.str.ecma_engine_semantics=true"]}

RUN_FIELDS = ["file", "set", "solver", "expected", "result", "outcome", "seconds"]
REDUCTION_FIELDS = [
    "file",
    "set",
    "solver",
    "site",
    "guarded",
    "reductions",
    "states_before",
    "states_after",
    "transitions_before",
    "transitions_after",
    "ns",
]

STATUS_LINE = re.compile(r"\(set-info\s+:status\s+(sat|unsat|unknown)\s*\)")
ANSWERS = ("sat", "unsat")


def parse_arguments():
    """The command-line arguments."""
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("out_dir", type=Path)
    parser.add_argument(
        "--solver",
        action="append",
        required=True,
        metavar="NAME=PATH",
        help="a z3 binary under a name (repeat the option for more solvers)",
    )
    parser.add_argument(
        "--sets", default="all", help='comma-separated sets of smt-bench (default: "all" but smtcomp25)'
    )
    parser.add_argument("--sample-per-set", type=int, help="only a random sample of this many formulas of each set")
    parser.add_argument("--seed", type=int, default=0, help="seed of the sample and of the order of the runs")
    parser.add_argument("--jobs", type=int, default=6, help="runs in parallel (default: 6)")
    parser.add_argument("--timeout", type=float, default=60, help="seconds per run (default: 60)")
    parser.add_argument(
        "--memory-gb", type=float, default=16, help="address-space limit of one run, 0 for none (default: 16)"
    )
    parser.add_argument(
        "--reduce-log",
        action="store_true",
        help="record the mata::nfa::reduce calls (the solvers must be built by build_variant.py --reduce-log)",
    )
    args = parser.parse_args()
    args.solver = dict(solver.split("=", 1) for solver in args.solver)
    return args


# ---------------------------------------------------------------------------------------------------------------------------------
# smt-bench and its formulas


def prepare_smt_bench():
    """Clones smt-bench with its submodules and downloads the SMT-LIB formulas, skipping what is already there."""
    if not SMT_BENCH.exists():
        subprocess.run(["git", "clone", "--branch", SMT_BENCH_BRANCH, SMT_BENCH_REPOSITORY, str(SMT_BENCH)], check=True)
    subprocess.run(["git", "-C", str(SMT_BENCH), "submodule", "update", "--init"], check=True)

    # the download script unpacks QF_S, QF_SLIA and QF_SNIA into formulae/; the marker tells that it finished
    marker = SMT_BENCH / "formulae" / ".downloaded"
    if not marker.exists():
        subprocess.run(["bash", "download_smt_benchmarks.sh"], cwd=SMT_BENCH, check=True)
        marker.touch()


def select_formulas(sets, sample_per_set, seed):
    """The (set, path) pairs of the formulas to run, optionally a random sample of each set.

    The paths are relative to smt-bench.
    A formula listed in several sets is taken only once, in the first of them.
    Formulas that are listed but missing are left out with a warning.
    """
    if sets == "all":
        names = sorted(
            listing.stem for listing in (SMT_BENCH / "bench").glob("*.input") if listing.stem not in SKIPPED_SETS
        )
    else:
        names = sets.split(",")

    rng = random.Random(seed)
    formulas, seen, missing = [], set(), 0
    for name in names:
        listing = SMT_BENCH / "bench" / f"{name}.input"
        # the lists name the formulas relative to bench/, e.g. ../formulae/QF_S/...
        paths = [
            os.path.normpath(Path("bench") / line.strip()) for line in listing.read_text().splitlines() if line.strip()
        ]
        if sample_per_set and len(paths) > sample_per_set:
            paths = sorted(rng.sample(paths, sample_per_set))
        for path in paths:
            if path in seen:
                continue
            seen.add(path)
            if (SMT_BENCH / path).is_file():
                formulas.append((name, path))
            else:
                missing += 1

    if missing:
        print(f"warning: {missing} listed formulas are missing", flush=True)
    return formulas


def clean_formula(text):
    """Removes the commands that the benchmarks do not need, like smt-bench's bin/clean-formula.sh."""
    for command in [
        "(get-model)",
        "(set-option :produce-unsat-cores true)",
        "(set-option :produce-models true)",
        "(get-unsat-core)",
    ]:
        text = text.replace(command, "")
    text = "\n".join(line for line in text.split("\n") if "get-value" not in line)
    if "set-logic" not in text:
        text = "(set-logic ALL)\n" + text
    return text


# ---------------------------------------------------------------------------------------------------------------------------------
# running z3


def run_solver(z3, set_name, path, timeout, memory_gb, reduce_log=None):
    """Runs z3 on a formula and returns its expected status, the result and the time in seconds.

    The result is the answers of z3 (sat, unsat or unknown) separated by spaces, or timeout, crash(SIGNAL), error or other.
    With reduce_log, the reduce wrapper in z3 logs its calls to that file.
    """
    text = (SMT_BENCH / path).read_text(errors="replace")
    expected = " ".join(STATUS_LINE.findall(text)) or "-"

    # -T is only a safety net for the case that this script is killed; the timeout is enforced below
    command = [z3, *SET_OPTIONS.get(set_name, []), "model=false", f"-T:{int(timeout) + 10}", "-smt2", "-in"]
    if memory_gb:
        command = ["prlimit", f"--as={int(memory_gb * 2**30)}", "--", *command]
    environment = {**os.environ, "REDUCE_LOG": str(reduce_log)} if reduce_log else None

    start = time.monotonic()
    process = subprocess.Popen(
        command,
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        errors="replace",
        env=environment,
    )
    try:
        output, _ = process.communicate(clean_formula(text), timeout=timeout)
    except subprocess.TimeoutExpired:
        process.kill()
        process.communicate()
        return expected, "timeout", timeout
    seconds = time.monotonic() - start

    lines = [line.strip() for line in output.split("\n") if line.strip()]
    answers = [line for line in lines if line in ("sat", "unsat", "unknown")]
    if process.returncode < 0:
        result = f"crash({-process.returncode})"
    elif any(line.startswith("(error") for line in lines):
        result = "error"
    elif answers:
        result = " ".join(answers)
    else:
        result = "other"
    return expected, result, seconds


def outcome(expected, result):
    """Classifies a run: solved, wrong (an answer contradicts the expected status), timeout, unknown, or failed (crash, error, other)."""
    if result == "timeout":
        return "timeout"
    answers = result.split()
    if answers[0] in ("error", "other") or answers[0].startswith("crash"):
        return "failed"
    for expected_answer, answer in zip(expected.split(), answers):
        if expected_answer in ANSWERS and answer in ANSWERS and expected_answer != answer:
            return "wrong"
    if all(answer in ANSWERS for answer in answers):
        return "solved"
    return "unknown"


def build_hashcode(z3):
    """The short git hashcode that z3 was built from, as z3 --version prints it."""
    version = subprocess.run([z3, "--version"], capture_output=True, text=True).stdout
    match = re.search(r"build hashcode ([0-9a-f]+)", version)
    return match.group(1)[:9] if match else "unknown"


# ---------------------------------------------------------------------------------------------------------------------------------
# the logs of the reduce wrapper


def read_reduce_log(log):
    """The reductions in a log of the reduce wrapper, summed per caller address and guardedness.

    Returns {(caller, guarded): [reductions, states before, states after, transitions before, transitions after, ns]}.
    """
    totals = {}
    if not log.exists():
        return totals
    for line in log.read_text().splitlines():
        fields = line.split()
        # a line cut by killing z3
        if len(fields) != 7:
            continue
        caller, states, transitions, result_states, result_transitions, ns, guarded = fields
        row = totals.setdefault((caller, guarded == "1"), [0] * 6)
        for index, value in enumerate([1, states, result_states, transitions, result_transitions, ns]):
            row[index] += int(value)
    return totals


class SiteNames:
    """Names the call sites of reductions in one z3 binary: the function containing a caller address, found by addr2line.

    The names are cached, as one binary has only a few dozen call sites.
    """

    def __init__(self, z3):
        self.z3 = z3
        self.names = {}

    def __getitem__(self, caller):
        if caller not in self.names:
            # a return address points after the call instruction, so the call is at the address before it
            call_address = hex(int(caller, 16) - 1)
            output = subprocess.run(
                ["addr2line", "-f", "-C", "-e", self.z3, call_address], capture_output=True, text=True
            ).stdout
            # e.g. smt::noodler::FormulaPreprocessor::reduce_automata(...) -> FormulaPreprocessor::reduce_automata
            function = output.split("\n")[0].split("(")[0]
            self.names[caller] = "::".join(function.split("::")[-2:])
        return self.names[caller]


def reductions_per_site(totals, site_names):
    """The totals of read_reduce_log summed per (site, guarded)."""
    per_site = {}
    for (caller, guarded), values in totals.items():
        row = per_site.setdefault((site_names[caller], guarded), [0] * 6)
        for index, value in enumerate(values):
            row[index] += value
    return per_site


# ---------------------------------------------------------------------------------------------------------------------------------
# the benchmark


class CsvAppender:
    """Appends rows to a CSV file and writes the header only into a new file, so that a stopped run can be resumed."""

    def __init__(self, path, fields):
        is_new = not path.exists()
        self.file = open(path, "a", newline="")
        self.writer = csv.DictWriter(self.file, fieldnames=fields)
        if is_new:
            self.writer.writeheader()

    def write(self, row):
        self.writer.writerow(row)
        self.file.flush()


def planned_runs(formulas, solvers, done, seed):
    """The (formula index, solver name) pairs still to run: the formulas in random order, the solvers of a formula next to each other."""
    rng = random.Random(seed)
    order = list(range(len(formulas)))
    rng.shuffle(order)
    runs = []
    for index in order:
        names = list(solvers)
        rng.shuffle(names)
        runs += [(index, name) for name in names if (formulas[index][1], name) not in done]
    return runs


def main():
    """Prepares smt-bench, then runs every solver on every selected formula and appends the results to the CSV files."""
    args = parse_arguments()
    args.out_dir.mkdir(parents=True, exist_ok=True)
    prepare_smt_bench()

    # the solvers, for the header of the report
    with open(args.out_dir / "solvers.csv", "w", newline="") as f:
        writer = csv.writer(f)
        writer.writerow(["name", "path", "hashcode"])
        writer.writerows([name, z3, build_hashcode(z3)] for name, z3 in args.solver.items())

    # the runs not done by a previous call with the same OUT_DIR
    formulas = select_formulas(args.sets, args.sample_per_set, args.seed)
    runs_csv = args.out_dir / "runs.csv"
    done = set()
    if runs_csv.exists():
        with open(runs_csv, newline="") as f:
            done = {(row["file"], row["solver"]) for row in csv.DictReader(f)}
    runs = planned_runs(formulas, args.solver, done, args.seed)
    print(f"{len(formulas)} formulas, {len(done)} runs done before, {len(runs)} to run", flush=True)

    log_dir = args.out_dir / "reduce-logs"
    if args.reduce_log:
        log_dir.mkdir(exist_ok=True)

    def run(task):
        index, name = task
        set_name, path = formulas[index]
        if not args.reduce_log:
            return task, run_solver(args.solver[name], set_name, path, args.timeout, args.memory_gb), {}
        log = log_dir / f"{index}-{name}.log"
        log.unlink(missing_ok=True)
        result = run_solver(args.solver[name], set_name, path, args.timeout, args.memory_gb, log)
        totals = read_reduce_log(log)
        log.unlink(missing_ok=True)
        return task, result, totals

    run_rows = CsvAppender(runs_csv, RUN_FIELDS)
    reduction_rows = CsvAppender(args.out_dir / "reductions.csv", REDUCTION_FIELDS) if args.reduce_log else None
    site_names = {name: SiteNames(z3) for name, z3 in args.solver.items()}
    start = last_progress = time.monotonic()

    with ThreadPool(args.jobs) as pool:
        for done_count, ((index, name), (expected, result, seconds), totals) in enumerate(
            pool.imap_unordered(run, runs), 1
        ):
            set_name, path = formulas[index]
            run_rows.write(
                {
                    "file": path,
                    "set": set_name,
                    "solver": name,
                    "expected": expected,
                    "result": result,
                    "outcome": outcome(expected, result),
                    "seconds": f"{seconds:.3f}",
                }
            )

            # the call sites are named here, in one thread, so that the cache of the names needs no lock
            if reduction_rows:
                for (site, guarded), values in reductions_per_site(totals, site_names[name]).items():
                    reduction_rows.write(
                        {
                            "file": path,
                            "set": set_name,
                            "solver": name,
                            "site": site,
                            "guarded": int(guarded),
                            **dict(zip(REDUCTION_FIELDS[5:], values)),
                        }
                    )

            # progress at most once a minute
            now = time.monotonic()
            if now - last_progress >= 60 or done_count == len(runs):
                minutes = (now - start) / 60
                minutes_left = minutes / done_count * (len(runs) - done_count)
                print(
                    f"{done_count}/{len(runs)} runs, {minutes:.0f} min, about {minutes_left:.0f} min left", flush=True
                )
                last_progress = now


if __name__ == "__main__":
    main()
