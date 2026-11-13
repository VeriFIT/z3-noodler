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

from __future__ import annotations

import argparse
import csv
import dataclasses
import functools
import os
import random
import re
import subprocess
import time
from dataclasses import dataclass
from multiprocessing.pool import ThreadPool
from pathlib import Path
from typing import NamedTuple

TOOLS = Path(__file__).resolve().parent
SMT_BENCH = TOOLS / "smt-bench"
SMT_BENCH_REPOSITORY = "https://github.com/Kumismar/smt-bench.git"
SMT_BENCH_BRANCH = "ecma2020-mixed-bmp"

# smtcomp25 only repeats formulas of other sets (pcp, rna, hornstr, negated_predicates, matching).
SKIPPED_SETS = ["smtcomp25"]

# The statuses of the mixed ECMAScript constraints assume the engine semantics (RegExp.test() searches for a matching substring).
SET_OPTIONS = {"ecma2020_mixed_bmp": ["smt.str.ecma_engine_semantics=true"]}

# The commands that the benchmarks do not need, so they are removed from the formulas.
REMOVED_COMMANDS = [
    "(get-model)",
    "(set-option :produce-unsat-cores true)",
    "(set-option :produce-models true)",
    "(get-unsat-core)",
]

# The status that a formula declares for one of its check-sat commands.
STATUS_LINE = re.compile(r"\(set-info\s+:status\s+(sat|unsat|unknown)\s*\)")

# The answers of z3 to a check-sat, and those of them that decide the formula.
Z3_ANSWERS = ("sat", "unsat", "unknown")
DEFINITE_ANSWERS = ("sat", "unsat")

# The timeout of z3 itself (its option -T) is this many seconds longer than the timeout of a run.
Z3_TIMEOUT_MARGIN = 10

# The progress is printed at most once in this many seconds.
PROGRESS_INTERVAL = 60

# The columns of runs.csv.
RUN_FIELDS = ["file", "set", "solver", "expected", "result", "outcome", "seconds"]

# The columns of reductions.csv.
# The last six of them are the fields of ReductionTotals.
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


# ---------------------------------------------------------------------------------------------------------------------------------
# the data of the benchmark


class Formula(NamedTuple):
    """A formula of smt-bench."""

    set_name: str  # the set that lists the formula
    path: str  # relative to smt-bench


class Task(NamedTuple):
    """One planned run: a solver on a formula."""

    formula_number: int  # the position of the formula among the selected formulas; it names the reduce log of the run
    formula: Formula
    solver: str  # the name of the solver


class RunResult(NamedTuple):
    """What z3 did on a formula."""

    expected: str  # the statuses that the formula declares, separated by spaces, or - if it declares none
    result: str  # the answers of z3 separated by spaces, or timeout, crash(SIGNAL), error or other
    seconds: float


@dataclass
class ReductionTotals:
    """Sums over some reductions of automata: their number, the sizes of the automata before and after them, and their time.

    The fields are the last six columns of reductions.csv.
    """

    reductions: int = 0
    states_before: int = 0
    states_after: int = 0
    transitions_before: int = 0
    transitions_after: int = 0
    ns: int = 0

    def add(self, other: ReductionTotals) -> None:
        """Adds other sums to these sums."""
        self.reductions += other.reductions
        self.states_before += other.states_before
        self.states_after += other.states_after
        self.transitions_before += other.transitions_before
        self.transitions_after += other.transitions_after
        self.ns += other.ns


class FinishedRun(NamedTuple):
    """A task with its result."""

    task: Task
    result: RunResult
    reductions: dict[tuple[str, bool], ReductionTotals]  # see read_reduce_log; empty without --reduce-log


# ---------------------------------------------------------------------------------------------------------------------------------
# the command line


def parse_arguments() -> argparse.Namespace:
    """The command-line arguments, with solvers as a dict from the name of each solver to the path of its z3 binary."""
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)

    parser.add_argument("out_dir", type=Path)
    parser.add_argument(
        "--solver",
        dest="solvers",
        action="append",
        required=True,
        metavar="NAME=PATH",
        help="a z3 binary under a name (repeat the option for more solvers)",
    )

    # Which formulas run.
    parser.add_argument(
        "--sets", default="all", help='comma-separated sets of smt-bench (default: "all" but smtcomp25)'
    )
    parser.add_argument("--sample-per-set", type=int, help="only a random sample of this many formulas of each set")
    parser.add_argument("--seed", type=int, default=0, help="seed of the sample and of the order of the runs")

    # How they run.
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

    # ["old=bin/z3-old", "new=bin/z3-new"] becomes {"old": "bin/z3-old", "new": "bin/z3-new"}.
    args.solvers = dict(solver.split("=", 1) for solver in args.solvers)
    return args


# ---------------------------------------------------------------------------------------------------------------------------------
# smt-bench and its formulas


def prepare_smt_bench() -> None:
    """Clones smt-bench with its submodules and downloads the SMT-LIB formulas, skipping what is already there."""
    if not SMT_BENCH.exists():
        subprocess.run(["git", "clone", "--branch", SMT_BENCH_BRANCH, SMT_BENCH_REPOSITORY, str(SMT_BENCH)], check=True)

    subprocess.run(["git", "-C", str(SMT_BENCH), "submodule", "update", "--init"], check=True)

    # The download script unpacks QF_S, QF_SLIA and QF_SNIA into formulae/, and the marker tells that it finished.
    marker = SMT_BENCH / "formulae" / ".downloaded"
    if not marker.exists():
        subprocess.run(["bash", "download_smt_benchmarks.sh"], cwd=SMT_BENCH, check=True)
        marker.touch()


def set_names(sets: str) -> list[str]:
    """The names of the sets to run: the comma-separated names in sets, or for "all" every set of smt-bench but SKIPPED_SETS."""
    if sets != "all":
        return sets.split(",")

    # bench/NAME.input is the list of the formulas of the set NAME.
    listings = (SMT_BENCH / "bench").glob("*.input")
    return sorted(listing.stem for listing in listings if listing.stem not in SKIPPED_SETS)


def listed_paths(set_name: str) -> list[str]:
    """The paths of the formulas of a set, relative to smt-bench, in the order of the list of the set."""
    listing = SMT_BENCH / "bench" / f"{set_name}.input"
    lines = [line.strip() for line in listing.read_text().splitlines()]

    # The list names the formulas relative to bench/, e.g. ../formulae/QF_S/...
    return [os.path.normpath(Path("bench") / line) for line in lines if line]


def select_formulas(sets: str, sample_per_set: int | None, seed: int) -> list[Formula]:
    """The formulas to run, optionally a random sample of each set.

    A formula listed in several sets is taken only once, in the first of them.
    Formulas that are listed but missing are left out with a warning.
    """
    rng = random.Random(seed)
    formulas: list[Formula] = []
    seen_paths: set[str] = set()
    missing = 0

    for set_name in set_names(sets):
        paths = listed_paths(set_name)

        if sample_per_set and len(paths) > sample_per_set:
            paths = sorted(rng.sample(paths, sample_per_set))

        for path in paths:
            # The formula is already taken in an earlier set.
            if path in seen_paths:
                continue
            seen_paths.add(path)

            if (SMT_BENCH / path).is_file():
                formulas.append(Formula(set_name, path))
            else:
                missing += 1

    if missing:
        print(f"warning: {missing} listed formulas are missing", flush=True)
    return formulas


def clean_formula(text: str) -> str:
    """Removes the commands that the benchmarks do not need, like smt-bench's bin/clean-formula.sh."""
    for command in REMOVED_COMMANDS:
        text = text.replace(command, "")

    # get-value has arguments, so its whole line goes.
    text = "\n".join(line for line in text.split("\n") if "get-value" not in line)

    if "set-logic" not in text:
        text = "(set-logic ALL)\n" + text
    return text


def expected_status(text: str) -> str:
    """The statuses that a formula declares, separated by spaces, or - if it declares none."""
    return " ".join(STATUS_LINE.findall(text)) or "-"


# ---------------------------------------------------------------------------------------------------------------------------------
# running z3


def solver_command(z3: str, set_name: str, timeout: float, memory_gb: float) -> list[str]:
    """The command that runs z3 on a formula of a set, with the formula on the standard input."""
    # -T is only a safety net for the case that this script is killed: run_solver enforces the timeout itself.
    z3_timeout = int(timeout) + Z3_TIMEOUT_MARGIN
    command = [z3, *SET_OPTIONS.get(set_name, []), "model=false", f"-T:{z3_timeout}", "-smt2", "-in"]

    # prlimit starts z3 with a limit of its address space.
    if memory_gb:
        limit_in_bytes = int(memory_gb * 2**30)
        command = ["prlimit", f"--as={limit_in_bytes}", "--", *command]

    return command


def result_of_output(returncode: int, output: str) -> str:
    """The result of a run that finished: the answers of z3 separated by spaces, or crash(SIGNAL), error or other."""
    lines = [line.strip() for line in output.split("\n") if line.strip()]
    answers = [line for line in lines if line in Z3_ANSWERS]

    # A negative exit code is the number of the signal that killed z3.
    if returncode < 0:
        return f"crash({-returncode})"

    if any(line.startswith("(error") for line in lines):
        return "error"

    if answers:
        return " ".join(answers)

    return "other"


def run_solver(
    z3: str, formula: Formula, timeout: float, memory_gb: float, reduce_log: Path | None = None
) -> RunResult:
    """Runs z3 on a formula and returns its expected status, the result and the time in seconds.

    The result is the answers of z3 (sat, unsat or unknown) separated by spaces, or timeout, crash(SIGNAL), error or other.
    With reduce_log, the reduce wrapper in z3 logs its calls to that file.
    """
    text = (SMT_BENCH / formula.path).read_text(errors="replace")
    expected = expected_status(text)

    command = solver_command(z3, formula.set_name, timeout, memory_gb)
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

    # z3 reads the cleaned formula and is killed if it does not finish in time.
    try:
        output, _ = process.communicate(clean_formula(text), timeout=timeout)
    except subprocess.TimeoutExpired:
        process.kill()
        process.communicate()
        return RunResult(expected, "timeout", timeout)

    seconds = time.monotonic() - start
    return RunResult(expected, result_of_output(process.returncode, output), seconds)


def outcome(expected: str, result: str) -> str:
    """Classifies a run: solved, wrong (an answer contradicts the expected status), timeout, unknown, or failed (crash, error, other)."""
    if result == "timeout":
        return "timeout"

    answers = result.split()
    if answers[0] in ("error", "other") or answers[0].startswith("crash"):
        return "failed"

    # The answer to each check-sat is compared with the status that the formula declares for it.
    for expected_answer, answer in zip(expected.split(), answers):
        if expected_answer in DEFINITE_ANSWERS and answer in DEFINITE_ANSWERS and expected_answer != answer:
            return "wrong"

    if all(answer in DEFINITE_ANSWERS for answer in answers):
        return "solved"

    return "unknown"


def build_hashcode(z3: str) -> str:
    """The short git hashcode that z3 was built from, as z3 --version prints it."""
    version = subprocess.run([z3, "--version"], capture_output=True, text=True, check=False).stdout
    match = re.search(r"build hashcode ([0-9a-f]+)", version)
    return match.group(1)[:9] if match else "unknown"


# ---------------------------------------------------------------------------------------------------------------------------------
# the logs of the reduce wrapper


def read_reduce_log(log: Path) -> dict[tuple[str, bool], ReductionTotals]:
    """The reductions in a log of the reduce wrapper, summed per caller address and guardedness.

    Returns {(caller address, guarded): sums}, which is empty if z3 wrote no log.
    """
    totals: dict[tuple[str, bool], ReductionTotals] = {}
    if not log.exists():
        return totals

    with open(log) as lines:
        for line in lines:
            fields = line.split()

            # A line cut by killing z3.
            if len(fields) != 7:
                continue

            # The wrapper writes one line per reduction, with the fields in this order.
            caller, states, transitions, result_states, result_transitions, ns, guarded = fields

            sums = totals.setdefault((caller, guarded == "1"), ReductionTotals())
            sums.reductions += 1
            sums.states_before += int(states)
            sums.states_after += int(result_states)
            sums.transitions_before += int(transitions)
            sums.transitions_after += int(result_transitions)
            sums.ns += int(ns)

    return totals


# functools.cache does the same, but it needs Python 3.9.
@functools.lru_cache(maxsize=None)  # noqa: UP033
def site_name(z3: str, caller: str) -> str:
    """The name of a call site of reductions in a z3 binary: the function containing the caller address, found by addr2line.

    The names are cached, as one binary has only a few dozen call sites.
    """
    # A return address points after the call instruction, so the call is at the address before it.
    call_address = hex(int(caller, 16) - 1)
    command = ["addr2line", "-f", "-C", "-e", z3, call_address]
    output = subprocess.run(command, capture_output=True, text=True, check=False).stdout

    # The first line is the function, e.g. smt::noodler::FormulaPreprocessor::reduce_automata(...).
    function = output.split("\n")[0].split("(")[0]

    # The name is its last two parts, e.g. FormulaPreprocessor::reduce_automata.
    return "::".join(function.split("::")[-2:])


def reductions_per_site(
    reductions: dict[tuple[str, bool], ReductionTotals], z3: str
) -> dict[tuple[str, bool], ReductionTotals]:
    """The sums of read_reduce_log summed per call site: returns {(site name, guarded): sums}.

    Several caller addresses can be in one function, so they have the same site name.
    """
    per_site: dict[tuple[str, bool], ReductionTotals] = {}

    for (caller, guarded), sums in reductions.items():
        site = site_name(z3, caller)
        per_site.setdefault((site, guarded), ReductionTotals()).add(sums)

    return per_site


# ---------------------------------------------------------------------------------------------------------------------------------
# the CSV files


class CsvAppender:
    """Appends rows to a CSV file and writes the header only into a new file, so that a stopped run can be resumed."""

    def __init__(self, path: Path, fields: list[str]) -> None:
        is_new = not path.exists()

        # The file stays open until the script ends, as the rows are appended one by one.
        self.file = open(path, "a", newline="")  # noqa: SIM115
        self.writer = csv.DictWriter(self.file, fieldnames=fields)

        if is_new:
            self.writer.writeheader()

    def write(self, row: dict[str, object]) -> None:
        """Appends a row and flushes it, so that the row is in the file even if this script is killed."""
        self.writer.writerow(row)
        self.file.flush()


def write_solvers_csv(path: Path, solvers: dict[str, str]) -> None:
    """Writes the name, path and build hashcode of each solver."""
    with open(path, "w", newline="") as f:
        writer = csv.writer(f)
        writer.writerow(["name", "path", "hashcode"])

        for name, z3 in solvers.items():
            writer.writerow([name, z3, build_hashcode(z3)])


def read_done_runs(runs_csv: Path) -> set[tuple[str, str]]:
    """The (file, solver) pairs of the runs that are already in runs.csv, or an empty set if runs.csv does not exist."""
    if not runs_csv.exists():
        return set()

    with open(runs_csv, newline="") as f:
        return {(row["file"], row["solver"]) for row in csv.DictReader(f)}


def run_row(finished: FinishedRun) -> dict[str, object]:
    """The row of runs.csv of a finished run."""
    task = finished.task
    result = finished.result

    return {
        "file": task.formula.path,
        "set": task.formula.set_name,
        "solver": task.solver,
        "expected": result.expected,
        "result": result.result,
        "outcome": outcome(result.expected, result.result),
        "seconds": f"{result.seconds:.3f}",
    }


def reduction_rows(finished: FinishedRun, z3: str) -> list[dict[str, object]]:
    """The rows of reductions.csv of a finished run of the binary z3: one row per call site and guardedness."""
    task = finished.task
    rows = []

    for (site, guarded), sums in reductions_per_site(finished.reductions, z3).items():
        row = {
            "file": task.formula.path,
            "set": task.formula.set_name,
            "solver": task.solver,
            "site": site,
            "guarded": int(guarded),
            **dataclasses.asdict(sums),
        }
        rows.append(row)

    return rows


# ---------------------------------------------------------------------------------------------------------------------------------
# the benchmark


def plan_tasks(formulas: list[Formula], solver_names: list[str], done: set[tuple[str, str]], seed: int) -> list[Task]:
    """The runs still to do: the formulas in a random order, and the solvers of one formula next to each other, also in a random order.

    done are the (file, solver) pairs of the runs that are already in runs.csv.
    """
    rng = random.Random(seed)

    order = list(range(len(formulas)))
    rng.shuffle(order)

    tasks = []
    for formula_number in order:
        formula = formulas[formula_number]

        names = list(solver_names)
        rng.shuffle(names)

        for name in names:
            if (formula.path, name) not in done:
                tasks.append(Task(formula_number, formula, name))

    return tasks


@dataclass(frozen=True)
class TaskRunner:
    """Runs tasks in the worker threads, with the settings that are the same for every run."""

    solvers: dict[str, str]  # the path of the z3 binary of each solver, by the name of the solver
    timeout: float  # seconds per run
    memory_gb: float  # the address-space limit of one run, 0 for none
    reduce_log_dir: Path | None  # where z3 writes its reduce logs, or None if the reductions are not recorded

    def run(self, task: Task) -> FinishedRun:
        """Runs the solver of a task on its formula, and reads the reduce log if the reductions are recorded."""
        z3 = self.solvers[task.solver]

        if self.reduce_log_dir is None:
            result = run_solver(z3, task.formula, self.timeout, self.memory_gb)
            return FinishedRun(task, result, {})

        # The wrapper appends to the log, so a log that a killed run left there must go first.
        log = self.reduce_log_dir / f"{task.formula_number}-{task.solver}.log"
        log.unlink(missing_ok=True)

        result = run_solver(z3, task.formula, self.timeout, self.memory_gb, log)
        reductions = read_reduce_log(log)
        log.unlink(missing_ok=True)

        return FinishedRun(task, result, reductions)


class Progress:
    """Prints how many runs are finished, at most once in PROGRESS_INTERVAL seconds and after the last run."""

    def __init__(self, total: int) -> None:
        self.total = total
        self.finished = 0
        self.start = time.monotonic()
        self.last_print = self.start

    def run_finished(self) -> None:
        """Counts one more finished run and prints the progress if it is time for it."""
        self.finished += 1
        now = time.monotonic()

        is_last_run = self.finished == self.total
        if now - self.last_print < PROGRESS_INTERVAL and not is_last_run:
            return

        # The rest of the runs is expected to take as long per run as the runs so far.
        minutes = (now - self.start) / 60
        minutes_left = minutes / self.finished * (self.total - self.finished)

        print(f"{self.finished}/{self.total} runs, {minutes:.0f} min, about {minutes_left:.0f} min left", flush=True)
        self.last_print = now


def main() -> None:
    """Prepares smt-bench, then runs every solver on every selected formula and appends the results to the CSV files."""
    args = parse_arguments()
    args.out_dir.mkdir(parents=True, exist_ok=True)
    prepare_smt_bench()

    # The solvers, for the header of the reports.
    write_solvers_csv(args.out_dir / "solvers.csv", args.solvers)

    # The runs that a previous call with the same OUT_DIR did not do.
    formulas = select_formulas(args.sets, args.sample_per_set, args.seed)
    runs_csv = args.out_dir / "runs.csv"
    done = read_done_runs(runs_csv)
    tasks = plan_tasks(formulas, list(args.solvers), done, args.seed)
    print(f"{len(formulas)} formulas, {len(done)} runs done before, {len(tasks)} to run", flush=True)

    runs_file = CsvAppender(runs_csv, RUN_FIELDS)

    # The reductions are recorded only with --reduce-log.
    reduce_log_dir = None
    reductions_file = None
    if args.reduce_log:
        reduce_log_dir = args.out_dir / "reduce-logs"
        reduce_log_dir.mkdir(exist_ok=True)
        reductions_file = CsvAppender(args.out_dir / "reductions.csv", REDUCTION_FIELDS)

    runner = TaskRunner(args.solvers, args.timeout, args.memory_gb, reduce_log_dir)
    progress = Progress(len(tasks))

    # The worker threads run the tasks, and this thread writes the rows of each run as soon as it finishes.
    with ThreadPool(args.jobs) as pool:
        for finished in pool.imap_unordered(runner.run, tasks):
            runs_file.write(run_row(finished))

            # The call sites are named here and not in the worker threads, so that each of them is looked up only once.
            if reductions_file:
                z3 = args.solvers[finished.task.solver]
                for row in reduction_rows(finished, z3):
                    reductions_file.write(row)

            progress.run_finished()


if __name__ == "__main__":
    main()
