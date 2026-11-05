"""Shared helpers of the perf-tools scripts: where the benchmarks are, which formulas to run, how to run a solver on one,
how to classify its result, and how to run many of them in parallel.

Only the Python standard library is used here, so that the runner works on any machine.
"""
import csv
import hashlib
import json
import os
import platform
import random
import re
import subprocess
import sys
import time
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
from dataclasses import dataclass
from datetime import datetime
from pathlib import Path

# The z3-noodler repository (this folder is its perf-tools/) and the benchmark repositories next to it.
# Each can be overridden by an environment variable.
REPO = Path(os.environ.get("NOODLER_REPO", Path(__file__).resolve().parent.parent))
SMT_BENCH = Path(os.environ.get("SMT_BENCH", REPO.parent / "smt-bench" / "bench"))
ECMA_BENCH = Path(os.environ.get("ECMA_BENCH", REPO.parent / "ecma2020-smt-bench" / "smt_out"))

# Solver options of a set, as the tools in smt-bench's smt.yaml use them.
# The statuses of the mixed ECMAScript constraints assume the engine semantics (RegExp.test() matches a substring).
SET_OPTIONS = {"ecma2020_mixed_bmp": ["smt.str.ecma_engine_semantics=true"]}

# smtcomp25 contains copies of formulas of other sets (pcp, rna, hornstr, negated_predicates, matching).
DUPLICATE_SETS = ["smtcomp25"]

# smt-bench reads the ECMAScript sets from its git submodule formulae/ecma2020-smt-bench.
# If the submodule is not checked out, the same formulas are read from ECMA_BENCH.
ECMA_SUBMODULE_PART = "/formulae/ecma2020-smt-bench/smt_out/"

ANSWERS = ("sat", "unsat")
STATUS_LINE = re.compile(r"\(set-info\s+:status\s+(sat|unsat|unknown)\s*\)")
ANSWER_LINE = re.compile(r"^(sat|unsat|unknown)$")


@dataclass(frozen=True)
class Formula:
    set: str
    path: str
    options: tuple[str, ...] = ()


@dataclass
class Run:
    expected: str
    result: str
    seconds: float


def available_sets():
    """The sets of smt-bench whose formulas are all present, without DUPLICATE_SETS.

    Some sets need smt-bench's download script or its git submodules.
    """
    sets = []
    for listing in sorted(SMT_BENCH.glob("*.input")):
        if listing.stem not in DUPLICATE_SETS and all(os.path.isfile(formula.path) for formula in formulas_of_set(listing.stem)):
            sets.append(listing.stem)
    return sets


def formulas_of_set(name):
    """The formulas of a set of smt-bench (its bench/NAME.input lists paths relative to bench/)."""
    options = tuple(SET_OPTIONS.get(name, []))
    formulas = []
    for line in read_lines(SMT_BENCH / f"{name}.input"):
        path = os.path.normpath(SMT_BENCH / line)
        if not os.path.isfile(path) and ECMA_SUBMODULE_PART in path:
            path = str(ECMA_BENCH / path.split(ECMA_SUBMODULE_PART)[1])
        formulas.append(Formula(name, path, options))
    return formulas


def select_formulas(sets=None, list_file=None, sample_per_set=None, seed=0):
    """The formulas of a list file or of sets of smt-bench (all available ones if sets is "all"), optionally a sample per set."""
    if list_file:
        formulas = formulas_of_list(list_file)
    else:
        names = available_sets() if sets == "all" else sets.split(",")
        formulas = [formula for name in names for formula in formulas_of_set(name)]
    if sample_per_set:
        formulas = sample_per_set_of(formulas, sample_per_set, seed)
    return formulas


def formulas_of_list(path):
    """The formulas of a list file with lines SET;PATH;OPTIONS (the options separated by spaces)."""
    formulas = []
    for line in read_lines(path):
        name, formula_path, options = line.split(";")
        formulas.append(Formula(name, formula_path, tuple(options.split())))
    return formulas


def write_list(path, formulas):
    """Writes formulas as a list file readable by formulas_of_list."""
    with open(path, "w") as f:
        for formula in formulas:
            f.write(f"{formula.set};{formula.path};{' '.join(formula.options)}\n")


def sample_per_set_of(formulas, size, seed):
    """At most size random formulas of each set, in a reproducible way."""
    rng = random.Random(seed)
    by_set = {}
    for formula in formulas:
        by_set.setdefault(formula.set, []).append(formula)
    sample = []
    for name in sorted(by_set):
        members = by_set[name]
        sample += sorted(rng.sample(members, min(size, len(members))), key=lambda formula: formula.path)
    return sample


def read_lines(path):
    with open(path) as f:
        return [line.strip() for line in f if line.strip()]


def clean_formula(text):
    """Removes the commands that the benchmarks do not need, like smt-bench's bin/clean-formula.sh."""
    for command in ["(get-model)", "(set-option :produce-unsat-cores true)", "(set-option :produce-models true)", "(get-unsat-core)"]:
        text = text.replace(command, "")
    text = "\n".join(line for line in text.split("\n") if "get-value" not in line)
    if "set-logic" not in text:
        text = "(set-logic ALL)\n" + text
    return text


def run_solver(z3, formula, timeout, memory_gb=None, env=None):
    """Runs z3 on the formula and returns the expected status, the result and the time.

    The result is the answers (sat/unsat/unknown) separated by spaces, or timeout, crash(SIGNAL), error or other.
    memory_gb limits the address space of the process.
    env is added to the environment of the process.
    """
    with open(formula.path, errors="replace") as f:
        text = f.read()
    expected = " ".join(STATUS_LINE.findall(text)) or "-"
    command = [z3, *formula.options, "model=false", "-smt2", "-in"]
    if memory_gb:
        command = ["prlimit", f"--as={int(memory_gb * 2**30)}", "--", *command]
    start = time.monotonic()
    process = subprocess.Popen(command, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
                               errors="replace", env={**os.environ, **(env or {})})
    try:
        output, _ = process.communicate(clean_formula(text), timeout=timeout)
    except subprocess.TimeoutExpired:
        process.kill()
        process.communicate()
        return Run(expected, "timeout", timeout)
    seconds = time.monotonic() - start
    return Run(expected, result_of(output, process.returncode), seconds)


def result_of(output, returncode):
    lines = [line.strip() for line in output.split("\n") if line.strip()]
    answers = [line for line in lines if ANSWER_LINE.match(line)]
    if returncode < 0:
        return f"crash({-returncode})"
    if any(line.startswith("(error") for line in lines):
        return "error"
    if answers:
        return " ".join(answers)
    return "other"


def outcome(expected, result):
    """Classifies a run: solved, wrong (an answer contradicts the expected status), timeout, unknown or failed (crash, error, other)."""
    if result == "timeout":
        return "timeout"
    answers = result.split()
    if not answers or answers[0] in ("error", "other") or answers[0].startswith("crash"):
        return "failed"
    for expected_answer, answer in zip(expected.split(), answers):
        if expected_answer in ANSWERS and answer in ANSWERS and expected_answer != answer:
            return "wrong"
    if all(answer in ANSWERS for answer in answers):
        return "solved"
    return "unknown"


def run_in_pool(tasks, work, jobs, minutes=None):
    """Runs work(task) for each task on jobs threads and yields (task, result) as the runs finish.

    The tasks start in their order, and no task starts after the given number of minutes.
    """
    deadline = time.monotonic() + minutes * 60 if minutes is not None else None
    tasks = iter(tasks)
    running = {}
    with ThreadPoolExecutor(jobs) as pool:
        while True:
            while len(running) < jobs and (deadline is None or time.monotonic() < deadline):
                task = next(tasks, None)
                if task is None:
                    break
                running[pool.submit(work, task)] = task
            if not running:
                return
            finished, _ = wait(running, return_when=FIRST_COMPLETED)
            for future in finished:
                yield running.pop(future), future.result()


class Progress:
    """Prints how many of the tasks are done and an estimate of the remaining time, at most once a minute."""

    def __init__(self, total):
        self.total = total
        self.done = 0
        self.start = time.monotonic()
        self.last_print = self.start

    def step(self):
        self.done += 1
        now = time.monotonic()
        if now - self.last_print >= 60 or self.done == self.total:
            elapsed_minutes = (now - self.start) / 60
            remaining_minutes = elapsed_minutes / self.done * (self.total - self.done)
            print(f"{self.done}/{self.total} done, {elapsed_minutes:.0f} min, about {remaining_minutes:.0f} min left", flush=True)
            self.last_print = now


class CsvAppender:
    """Appends rows to a CSV file, writing the header only when the file is new, so that an interrupted run can be resumed."""

    def __init__(self, path, fields):
        is_new = not os.path.exists(path)
        self.file = open(path, "a", newline="")
        self.writer = csv.DictWriter(self.file, fieldnames=fields)
        if is_new:
            self.writer.writeheader()

    def write(self, row):
        self.writer.writerow(row)
        self.file.flush()

    def close(self):
        self.file.close()


def read_csv(path):
    if not os.path.exists(path):
        return []
    with open(path, newline="") as f:
        return list(csv.DictReader(f))


def parse_name_value(text):
    """NAME=VALUE (e.g., a solver NAME=PATH) as a pair, for argparse."""
    name, separator, value = text.partition("=")
    if not separator:
        raise ValueError(f"expected NAME=VALUE: {text}")
    return name, value


def write_provenance(path, solvers):
    """Records how a run was made: the command, the machine, the state of the repository and the solver binaries."""
    def sha256(file):
        with open(file, "rb") as f:
            return hashlib.file_digest(f, "sha256").hexdigest()

    def version(z3):
        return subprocess.run([z3, "--version"], capture_output=True, text=True).stdout.strip()

    describe = subprocess.run(["git", "-C", str(REPO), "describe", "--always", "--dirty"], capture_output=True, text=True).stdout.strip()
    record = {"command": sys.argv, "started": datetime.now().isoformat(timespec="seconds"), "host": platform.node(),
              "repository": describe, "solvers": {name: {"path": z3, "sha256": sha256(z3), "version": version(z3)} for name, z3 in solvers}}
    with open(path, "w") as f:
        json.dump(record, f, indent=2)
