#!/usr/bin/env python3
"""Runs several z3 binaries on the sets of ../smt-bench (bench/<set>.input) in one random-order pool.

The bench directory of smt-bench is taken from $SMT_BENCH.
Each formula is cleaned like smt-bench's bin/clean-formula.sh and passed on stdin with the options of its z3-noodler
tool (model=false -smt2).
The runs of one formula are queued next to each other, so that a stopped run leaves few formulas with a single run.
Rows are appended to the CSV as soon as they finish; a rerun skips the (formula, solver) pairs that are already there.
Usage: smtbench_run.py OUT.csv NAME=Z3_PATH... [--sets s1,s2 | --list FILE] [--jobs N] [--timeout S] [--sample SET=N...] [--minutes M] [--memory-gb G]
"""
import argparse
import csv
import os
import random
import re
import subprocess
import sys
import threading
import time
from concurrent.futures import ThreadPoolExecutor, as_completed

BENCH = os.environ.get("SMT_BENCH", "/home/koumy/Documents/smt-bench/bench")
REGEX = ["sygus_qgen", "denghang", "automatark", "stringfuzz", "redos", "matching", "hornstr"]
EQUATIONS = ["norn", "slog", "slent", "omark", "kepler", "woorpje", "webapp", "kaluza"]
PREDICATES = ["transducer_plus", "leetcode", "str_small_rw", "pcp", "rna", "negated_predicates", "pyex", "full_str_int"]
FIELDS = ["file", "set", "solver", "expected", "result", "seconds"]
STATUS = re.compile(r"\(set-info\s+:status\s+(sat|unsat|unknown)\s*\)")
RESULT = re.compile(r"^(sat|unsat|unknown)$")


def clean(text):
    """Cleans a formula like bin/clean-formula.sh of smt-bench."""
    for s in ["(get-model)", "(set-option :produce-unsat-cores true)", "(set-option :produce-models true)", "(get-unsat-core)"]:
        text = text.replace(s, "")
    text = "\n".join(line for line in text.split("\n") if "get-value" not in line)
    if "set-logic" not in text:
        text = "(set-logic ALL)\n" + text
    return text


def run(path, z3, timeout, options=(), memory_gb=None):
    """Runs z3 with the options on the formula (with at most memory_gb of address space); returns (expected, result, seconds)."""
    with open(path, errors="replace") as f:
        text = f.read()
    expected = " ".join(STATUS.findall(text)) or "-"
    limit = ["prlimit", f"--as={int(memory_gb * 2**30)}"] if memory_gb else []
    start = time.monotonic()
    proc = subprocess.Popen([*limit, z3, *options, "model=false", "-smt2", "-in"], stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, text=True, errors="replace")
    try:
        out, _ = proc.communicate(clean(text), timeout=timeout)
    except subprocess.TimeoutExpired:
        proc.kill()
        proc.communicate()
        return expected, "timeout", timeout
    seconds = time.monotonic() - start
    lines = [line.strip() for line in out.split("\n") if line.strip()]
    answers = [line for line in lines if RESULT.match(line)]
    if proc.returncode < 0:
        result = f"crash({-proc.returncode})"
    elif any(line.startswith("(error") for line in lines):
        result = "error"
    elif answers:
        result = " ".join(answers)
    else:
        result = "other"
    return expected, result, seconds


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("out")
    parser.add_argument("solvers", nargs="+", help="NAME=Z3_PATH")
    parser.add_argument("--sets", default=",".join(REGEX + EQUATIONS + PREDICATES))
    parser.add_argument("--list", help="formula list with lines SET;ABSOLUTE_PATH;OPTIONS instead of --sets")
    parser.add_argument("--jobs", type=int, default=4)
    parser.add_argument("--timeout", type=float, default=10)
    parser.add_argument("--sample", nargs="*", default=[], help="SET=N: only a random sample of N formulas of SET")
    parser.add_argument("--sample-all", type=int, help="N: a random sample of N formulas of every set")
    parser.add_argument("--minutes", type=float, help="runs not started within this many minutes are skipped")
    parser.add_argument("--seed", type=int, default=1103)
    parser.add_argument("--memory-gb", type=float, help="address-space limit of each run")
    args = parser.parse_args()

    solvers = dict(s.split("=", 1) for s in args.solvers)
    samples = {s.split("=")[0]: int(s.split("=")[1]) for s in args.sample}
    rng = random.Random(args.seed)
    formulas = []
    options = {}
    if args.list:
        with open(args.list) as f:
            for name, p, opts in (line.rstrip("\n").split(";") for line in f if line.strip()):
                formulas.append((name, p))
                options[p] = opts.split()
    else:
        for name in args.sets.split(","):
            with open(f"{BENCH}/{name}.input") as f:
                paths = [line.strip() for line in f if line.strip()]
            size = samples.get(name, args.sample_all)
            if size is not None:
                paths = sorted(rng.sample(paths, min(size, len(paths))))
            formulas += [(name, p) for p in paths]

    done = set()
    if os.path.exists(args.out):
        with open(args.out) as f:
            done = {(row["file"], row["solver"]) for row in csv.DictReader(f, delimiter=";")}
    rng.shuffle(formulas)
    tasks = []
    for name, p in formulas:
        order = list(solvers)
        rng.shuffle(order)
        tasks += [(name, p, s) for s in order if (p, s) not in done]
    print(f"{len(formulas)} formulas, {len(done)} runs done, {len(tasks)} to run", flush=True)

    new_file = not os.path.exists(args.out)
    lock = threading.Lock()
    with open(args.out, "a", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=FIELDS, delimiter=";")
        if new_file:
            writer.writeheader()
        start = time.monotonic()
        deadline = start + args.minutes * 60 if args.minutes is not None else None

        def run_until_deadline(path, z3):
            if deadline is not None and time.monotonic() > deadline:
                return None
            return run(path, z3, args.timeout, options.get(path, ()), args.memory_gb)

        with ThreadPoolExecutor(args.jobs) as pool:
            futures = {pool.submit(run_until_deadline, p if args.list else os.path.normpath(os.path.join(BENCH, p)),
                                   solvers[s]): (name, p, s)
                       for name, p, s in tasks}
            for i, future in enumerate(as_completed(futures), 1):
                name, p, s = futures[future]
                try:
                    finished = future.result()
                    if finished is None:
                        continue
                    expected, result, seconds = finished
                except Exception as e:  # noqa: BLE001
                    expected, result, seconds = "-", f"runner-error({e})", 0
                with lock:
                    writer.writerow({"file": p, "set": name, "solver": s, "expected": expected, "result": result,
                                     "seconds": f"{seconds:.3f}"})
                    f.flush()
                if i % 2000 == 0 or i == len(tasks):
                    elapsed = time.monotonic() - start
                    print(f"{i}/{len(tasks)} done, {elapsed / 60:.0f} min, ETA {elapsed / i * (len(tasks) - i) / 60:.0f} min",
                          flush=True)


if __name__ == "__main__":
    sys.exit(main())
