#!/usr/bin/env python3
"""Collects the statistics of every mata::nfa::reduce call of the reduce-stats variant (build_reduce_stats_variant.sh) on smt-bench formulas.

Each formula runs with $REDUCE_LOG set to a log of its own (see reduce_wrap.cpp), which is parsed after the run into rows of OUT-calls.csv
and a row of OUT-formulas.csv; a START line without END (a call cut by the timeout or a crash) gives a censored call whose time is the time
from its start to the end of the run, a lower bound.
Identical calls of a formula (same site, operation, properties and result, e.g., in repeated final checks) are merged into one row with the
number of repeats and the median, min, max and sum of their times.
The formulas run in random order, so a stopped collection leaves a representative part; a rerun skips the formulas already in OUT-formulas.csv.
The sets are those of smt-bench ($SMT_BENCH = its bench/ dir) with their options of smt.yaml; smtcomp25 is left out by default, as its formulas
are copies of the pcp, rna, hornstr, negated_predicates and matching formulas.
At the end, the caller addresses are mapped to source lines by addr2line into OUT-callers.csv.
Usage: reduce_stats_collect.py OUT [--z3 Z3] [--sets s1,s2 | --list FILE] [--jobs N] [--timeout S] [--sample-all N] [--minutes M]
       [--memory-gb G] [--seed N]
"""
import argparse
import csv
import glob
import os
import random
import re
import subprocess
import sys
import threading
import time
from concurrent.futures import ThreadPoolExecutor, as_completed

import smtbench_run

Z3 = "/home/koumy/Documents/z3-noodler/build/release-g/variants/reduce-stats/z3"
SET_OPTIONS = {"ecma2020_mixed_bmp": ["smt.str.ecma_engine_semantics=true"]}
EXCLUDED_SETS = ["smtcomp25"]
START_FIELDS = ["seq", "start_ns", "caller", "operation", "alphabet", "states", "initial", "final", "useful", "transitions", "moves",
                "epsilon", "self_loops", "symbols", "max_out", "max_targets", "deterministic", "sccs", "max_scc", "cyclic"]
# identical calls of a formula (same site, operation, properties and result) are merged into one row
CALL_KEY = [f for f in START_FIELDS if f not in ("seq", "start_ns")] + ["res_states", "res_transitions", "censored"]
CALL_FIELDS = ["file", "set", "first_seq"] + CALL_KEY + ["repeats", "ns", "ns_min", "ns_max", "ns_sum"]
FORMULA_FIELDS = ["file", "set", "expected", "result", "seconds", "calls", "reduce_ns", "censored_calls"]
ADDRESS = re.compile(r"^0x[0-9a-f]+$")


def available_sets():
    """Sets of smt-bench whose formulas are all present, without EXCLUDED_SETS."""
    sets = []
    for path in sorted(glob.glob(f"{smtbench_run.BENCH}/*.input")):
        name = os.path.basename(path)[:-len(".input")]
        with open(path) as f:
            files = [line.strip() for line in f if line.strip()]
        if name not in EXCLUDED_SETS and all(os.path.isfile(os.path.join(smtbench_run.BENCH, p)) for p in files):
            sets.append(name)
    return sets


def parse_log(path, end_ns):
    """Rows of the calls in a log of reduce_wrap.cpp (dicts of START_FIELDS and the result); end_ns is when the run ended."""
    calls = {}
    with open(path, errors="replace") as f:
        for line in f:
            parts = line.split()
            if parts and parts[0] == "S" and len(parts) == len(START_FIELDS) + 1:
                calls[parts[1]] = dict(zip(START_FIELDS, parts[1:]))
            elif parts and parts[0] == "E" and len(parts) == 5 and parts[1] in calls:
                calls[parts[1]].update(res_states=parts[2], res_transitions=parts[3], ns=parts[4], censored=0)
    for call in calls.values():
        if "ns" not in call:
            call.update(res_states="", res_transitions="", ns=max(0, end_ns - int(call["start_ns"])), censored=1)
    return merge_calls(calls.values())


def merge_calls(calls):
    """Merges identical calls into rows with the first sequence number, the number of repeats and the median, min, max and sum of the times."""
    groups = {}
    for call in calls:
        groups.setdefault(tuple(str(call[f]) for f in CALL_KEY), []).append(call)
    rows = []
    for key, group in groups.items():
        times = sorted(int(c["ns"]) for c in group)
        rows.append({"first_seq": min(int(c["seq"]) for c in group), **dict(zip(CALL_KEY, key)), "repeats": len(times),
                     "ns": times[len(times) // 2], "ns_min": times[0], "ns_max": times[-1], "ns_sum": sum(times)})
    return rows


def run(z3, path, options, timeout, log, memory_gb):
    """Runs z3 on the formula with REDUCE_LOG=log; returns (expected, result, seconds, rows of its calls)."""
    with open(path, errors="replace") as f:
        text = f.read()
    expected = " ".join(smtbench_run.STATUS.findall(text)) or "-"
    if os.path.exists(log):
        os.remove(log)
    command = ["prlimit", f"--as={memory_gb << 30}", "--", z3, *options, "model=false", "-smt2", "-in"]
    start = time.monotonic()
    proc = subprocess.Popen(command, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, errors="replace",
                            env={**os.environ, "REDUCE_LOG": log})
    try:
        out, _ = proc.communicate(smtbench_run.clean(text), timeout=timeout)
        seconds = time.monotonic() - start
        if proc.returncode < 0:
            result = f"crash({-proc.returncode})"
        else:
            lines = [line.strip() for line in out.split("\n") if line.strip()]
            answers = [line for line in lines if smtbench_run.RESULT.match(line)]
            result = " ".join(answers) if answers else ("error" if any(line.startswith("(error") for line in lines) else "other")
    except subprocess.TimeoutExpired:
        proc.kill()
        proc.communicate()
        seconds, result = timeout, "timeout"
    end_ns = time.monotonic_ns()
    rows = parse_log(log, end_ns) if os.path.exists(log) else []
    if os.path.exists(log):
        os.remove(log)
    return expected, result, seconds, rows


def map_callers(z3, calls_csv, out_csv):
    """Maps the caller addresses in calls_csv to function and source line (the innermost inlined frame) and the outermost function."""
    with open(calls_csv) as f:
        callers = sorted({row["caller"] for row in csv.DictReader(f)})
    if not callers:
        return
    # the return address points after the call, so the call is at the address before it
    out = subprocess.run(["addr2line", "-e", z3, "-f", "-i", "-C", "-a", *[hex(int(c, 16) - 1) for c in callers]],
                         capture_output=True, text=True).stdout.split("\n")
    frames = {}
    current = None
    for line in out:
        if ADDRESS.match(line):
            current = hex(int(line, 16) + 1)
            frames[current] = []
        elif current is not None and line:
            frames[current].append(line)
    with open(out_csv, "w", newline="") as f:
        writer = csv.writer(f)
        writer.writerow(["caller", "function", "location", "outer_function"])
        for c in callers:
            fr = frames.get(hex(int(c, 16)), [])
            pairs = list(zip(fr[0::2], fr[1::2]))
            if pairs:
                location = pairs[0][1].split(" (discriminator")[0].replace("/home/koumy/Documents/z3-noodler/", "")
                writer.writerow([c, pairs[0][0][:200], location, pairs[-1][0][:200]])
            else:
                writer.writerow([c, "?", "?", "?"])


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("out", help="prefix of the output files")
    parser.add_argument("--z3", default=Z3)
    parser.add_argument("--sets", help="comma-separated sets of smt-bench (default: all available ones)")
    parser.add_argument("--list", help="formula list with lines SET;ABSOLUTE_PATH;OPTIONS instead of --sets")
    parser.add_argument("--jobs", type=int, default=8)
    parser.add_argument("--timeout", type=float, default=30)
    parser.add_argument("--sample-all", type=int, help="N: a random sample of N formulas of every set")
    parser.add_argument("--minutes", type=float, help="formulas not started within this many minutes are skipped")
    parser.add_argument("--memory-gb", type=int, default=6, help="address-space limit of one z3 process")
    parser.add_argument("--seed", type=int, default=1104)
    args = parser.parse_args()

    rng = random.Random(args.seed)
    formulas = []  # (set, absolute path, options)
    if args.list:
        with open(args.list) as f:
            for name, p, opts in (line.rstrip("\n").split(";") for line in f if line.strip()):
                formulas.append((name, p, opts.split()))
    else:
        for name in (args.sets.split(",") if args.sets else available_sets()):
            with open(f"{smtbench_run.BENCH}/{name}.input") as f:
                paths = [os.path.normpath(os.path.join(smtbench_run.BENCH, line.strip())) for line in f if line.strip()]
            if args.sample_all is not None:
                paths = sorted(rng.sample(paths, min(args.sample_all, len(paths))))
            formulas += [(name, p, SET_OPTIONS.get(name, [])) for p in paths]

    calls_csv, formulas_csv = f"{args.out}-calls.csv", f"{args.out}-formulas.csv"
    done = set()
    if os.path.exists(formulas_csv):
        with open(formulas_csv) as f:
            done = {row["file"] for row in csv.DictReader(f)}
    rng.shuffle(formulas)
    tasks = [t for t in formulas if t[1] not in done]
    print(f"{len(formulas)} formulas, {len(done)} done, {len(tasks)} to run", flush=True)

    log_dir = f"{args.out}-logs"
    os.makedirs(log_dir, exist_ok=True)
    lock = threading.Lock()
    new_calls, new_formulas = not os.path.exists(calls_csv), not os.path.exists(formulas_csv)
    with open(calls_csv, "a", newline="") as fc, open(formulas_csv, "a", newline="") as ff:
        calls_writer = csv.DictWriter(fc, fieldnames=CALL_FIELDS)
        formulas_writer = csv.DictWriter(ff, fieldnames=FORMULA_FIELDS)
        if new_calls:
            calls_writer.writeheader()
        if new_formulas:
            formulas_writer.writeheader()
        start = time.monotonic()
        deadline = start + args.minutes * 60 if args.minutes is not None else None

        def task(i, item):
            if deadline is not None and time.monotonic() > deadline:
                return None
            name, path, options = item
            return run(args.z3, path, options, args.timeout, f"{log_dir}/{i}.log", args.memory_gb)

        with ThreadPoolExecutor(args.jobs) as pool:
            futures = {pool.submit(task, i, item): item for i, item in enumerate(tasks)}
            for n, future in enumerate(as_completed(futures), 1):
                name, path, _ = futures[future]
                try:
                    finished = future.result()
                except Exception as e:  # noqa: BLE001
                    finished = ("-", f"runner-error({e})", 0, [])
                if finished is None:
                    continue
                expected, result, seconds, rows = finished
                with lock:
                    for row in rows:
                        calls_writer.writerow({"file": path, "set": name, **row})
                    formulas_writer.writerow({"file": path, "set": name, "expected": expected, "result": result, "seconds": f"{seconds:.3f}",
                                              "calls": sum(r["repeats"] for r in rows), "reduce_ns": sum(r["ns_sum"] for r in rows),
                                              "censored_calls": sum(int(r["censored"]) for r in rows)})
                    fc.flush()
                    ff.flush()
                if n % 1000 == 0 or n == len(tasks):
                    elapsed = time.monotonic() - start
                    print(f"{n}/{len(tasks)} done, {elapsed / 60:.0f} min, ETA {elapsed / n * (len(tasks) - n) / 60:.0f} min", flush=True)

    map_callers(args.z3, calls_csv, f"{args.out}-callers.csv")


if __name__ == "__main__":
    sys.exit(main())
