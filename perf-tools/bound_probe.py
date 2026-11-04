#!/usr/bin/env python3
"""Finds the formulas whose intersections in create_aut_assignment_for_formula reach a size where the reduce guard matters.

Runs the no-guard z3 with the reduce wrapper ($PROBE_Z3, by default variants/reduce-instr-noguard) on a formula list (set;path;options per
line) and writes set;file;result;seconds;max_states;big_calls;big_ms, where big = at least --min-states states.
A variant with a bound of at least --min-states behaves the same as no guard on the formulas without big calls.
Usage: bound_probe.py LIST OUT.csv [--jobs N] [--min-states S]
"""
import argparse
import csv
import os
import re
import subprocess
from concurrent.futures import ThreadPoolExecutor

import smtbench_run

Z3 = os.environ.get("PROBE_Z3", "/home/koumy/Documents/z3-noodler/build/release/variants/reduce-instr-noguard/z3")
REDUCE = re.compile(r"REDUCE caller=(\S+) states=(\d+) trans=\d+ -> states=\d+ trans=\d+ ms=(\S+)")


def caller_range():
    """Address range of create_aut_assignment_for_formula in Z3."""
    out = subprocess.run(["nm", "-C", "-S", Z3], capture_output=True, text=True).stdout
    for line in out.splitlines():
        if "theory_str_noodler::create_aut_assignment_for_formula(" in line:
            start, size = line.split()[:2]
            return int(start, 16), int(start, 16) + int(size, 16)
    raise RuntimeError("create_aut_assignment_for_formula not found")


def probe(item, timeout, low, high, min_states):
    name, path, options = item
    with open(path, errors="replace") as f:
        text = smtbench_run.clean(f.read())
    proc = subprocess.Popen([Z3, *options, "model=false", "-smt2", "-in"], stdin=subprocess.PIPE,
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, errors="replace")
    timed_out = False
    try:
        out, err = proc.communicate(text, timeout=timeout)
    except subprocess.TimeoutExpired:
        proc.kill()
        out, err = proc.communicate()
        timed_out = True
    result = "timeout" if timed_out else (out.split() or ["other"])[0]
    states, big = 0, []
    for m in REDUCE.finditer(err):
        if low <= int(m.group(1), 16) < high:
            states = max(states, int(m.group(2)))
            if int(m.group(2)) >= min_states:
                big.append(float(m.group(3)))
    return name, path, result, states, len(big), sum(big)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("list")
    parser.add_argument("out")
    parser.add_argument("--jobs", type=int, default=4)
    parser.add_argument("--timeout", type=float, default=10)
    parser.add_argument("--min-states", type=int, default=500)
    args = parser.parse_args()
    with open(args.list) as f:
        items = [(s, p, o.split()) for s, p, o in (line.rstrip("\n").split(";") for line in f if line.strip())]
    low, high = caller_range()
    with ThreadPoolExecutor(args.jobs) as pool, open(args.out, "w", newline="") as f:
        writer = csv.writer(f, delimiter=";")
        writer.writerow(["set", "file", "result", "max_states", "big_calls", "big_ms"])
        for name, path, result, states, n, ms in pool.map(lambda i: probe(i, args.timeout, low, high, args.min_states), items):
            writer.writerow([name, path, result, states, n, f"{ms:.0f}"])


if __name__ == "__main__":
    main()
