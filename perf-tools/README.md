# perf-tools

Benchmarks of z3-noodler on [smt-bench](https://github.com/VeriFIT/smt-bench): running solver binaries on the formulas, reports and
plots of the results, and counting the simulation reductions (`mata::nfa::reduce`).

| file | what |
|---|---|
| `run.py` | gets smt-bench and its formulas (on the first run), runs the solvers, writes `runs.csv` (and `reductions.csv`) |
| `report.py` | writes `REPORT.md`, `REDUCTIONS.md` and the plots into the run directory |
| `plots.py` | the plots of `report.py`: time per formula (scatter) and total time per set |
| `build_variant.py` | builds a variant of z3 from patched sources and an existing build, optionally with the reduce wrapper |
| `instrumentation/reduce_wrap.cpp` | link-time wrapper of `mata::nfa::reduce` that logs every call to `$REDUCE_LOG` |
| `instrumentation/guard-flag.patch` | marks the reductions allowed by `regex::should_reduce` as guarded |

`run.py` needs only Python 3, git, curl, unzstd, prlimit and addr2line.
`report.py` needs the packages of `requirements.txt`:

```
python3 -m venv .venv && .venv/bin/pip install -r requirements.txt
```

## Running a benchmark on a server

1. Build the solvers (release builds for times) and copy the binaries and this repository to the server.
2. Start the run in `tmux`, so that it survives logging out:

   ```
   tmux new -s bench
   ./run.py runs/guard --solver old=bin/z3-old --solver new=bin/z3-new
   ```

   The first run clones smt-bench (branch `ecma2020-mixed-bmp` of the fork with the ECMAScript sets) into `smt-bench/`, checks out its
   submodules and downloads the SMT-LIB formulas.
   By default it runs all sets except `smtcomp25` (copies of other sets), 6 runs in parallel, with a timeout of 60 s and an address-space
   limit of 16 GB per run (`--memory-gb 0` removes it).
   `--sets a,b` and `--sample-per-set N` select fewer formulas.
3. If the run stops, the same command resumes it.
4. Copy the run directory back and write the reports:

   ```
   .venv/bin/python report.py runs/guard
   ```

   The report compares the first two solvers of the run, or the ones given by `--old` and `--new`.

## Counting the reductions

```
ninja -C ../build/release z3
./build_variant.py counting --reduce-log
./run.py runs/counts --solver counting=../build/release/variants/counting/z3 --reduce-log
```

Compare instrumented binaries only with each other: the logging slows the runs down, so time comparisons belong to separate runs of
plain binaries.
A patch for `build_variant.py` comes from `git diff`; a source from another revision is `git diff HEAD REV -- SOURCE`.
A header that changed between the versions cannot be patched this way, as only the patched sources are compiled again.

## Outputs of a run

- `solvers.csv`: the name, path and build hashcode of each solver (the header of the reports).
- `runs.csv`: one row per run with `file` (relative to smt-bench), `set`, `solver`, `expected` (the `:status` of the formula), `result`
  (the answers, `timeout`, `crash(SIGNAL)`, `error` or `other`), `outcome` (`solved`, `wrong`, `timeout`, `unknown` or `failed`) and
  `seconds`.
- `reductions.csv` (with `--reduce-log`): per run, call site and guardedness, the number of reductions, the states and transitions before
  and after them, and their time in ns.

## Pitfalls

- About 20-25 ms of a run is starting z3, which is most of the time of an easy formula.
- Binaries that differ only in code that a formula never executes still differ by about ±2 % on it (code layout), and separate runs
  differ by up to 5 %, so compare solvers in the same run.
- Results of single formulas can change a lot with details like `smt.random_seed`, so judge changes on sets, not on single formulas.
