# perf-tools

Tools for performance experiments with z3-noodler: building variants of the solver, running them on benchmarks, comparing them, and
measuring the simulation reduction (`mata::nfa::reduce`).

## Setup

The tools expect the benchmark repositories next to this repository:

| path | what | override |
|---|---|---|
| `..` | this repository (z3-noodler) | `NOODLER_REPO` |
| `../../smt-bench/bench` | [smt-bench](https://github.com/VeriFIT/smt-bench): `<set>.input` lists the formulas of a set; run its `download_smt_benchmarks.sh` and `git submodule update --init` to get the formulas | `SMT_BENCH` |
| `../../ecma2020-smt-bench/smt_out` | the ECMAScript formulas, used for the sets `ecma2020` and `ecma2020_mixed_bmp` when the smt-bench submodule is not checked out | `ECMA_BENCH` |

The runner (`run_bench.py`) and the build script (`build_variant.py`) need only Python 3.11+.
The report, plot and analysis scripts need the packages of `requirements.txt`:

```
python3 -m venv .venv && .venv/bin/pip install -r requirements.txt
```

## Files

| file | what |
|---|---|
| `build_variant.py` | builds `build/PRESET/variants/NAME/z3`: a few sources compiled from other files, git revisions or patches, the rest reused from the build; optionally with the reduce wrapper |
| `run_bench.py` | runs solvers on formulas (sets of smt-bench or a list file) in one random-order pool; writes `runs.csv`, optionally `reduce-calls.csv`, and `provenance.json` |
| `report.py` | Markdown report of a benchmark: outcomes, times per set, changed outcomes, biggest slowdowns and speedups against a baseline |
| `plots.py` | plots of a benchmark: per-formula scatter, tail of the time distribution, ratio histogram, per-set totals |
| `reduce_report.py` | how many reductions each solver makes, per call site and per set |
| `reduce_cost_analysis.py` | statistical analysis of the time of the reductions (ranking of properties, cost models, candidate guards) |
| `benchlib.py` | shared code of the runner: paths, formula sets, running z3, classifying results, the pool |
| `bench_data.py` | the results of `run_bench.py` as pandas tables, for `report.py` and `plots.py` |
| `reduce_log.py` | reading the logs of the reduce wrapper, naming the call sites |
| `plot_style.py` | colors and matplotlib settings of all plots |
| `instrumentation/reduce_wrap.cpp` | link-time wrapper of `mata::nfa::reduce` that logs every call to `$REDUCE_LOG` |
| `instrumentation/reduce-tags.patch` | tags the regex-construction and membership-heuristic calls of reduce with their operation |
| `instrumentation/no-guards.patch` | makes `regex::should_reduce` always reduce, for measuring the reductions that the guard skips |
| `instrumentation/old-versions/` | the tag patch for the sources of b2f2ec58f (the bounds before the cost guard) |
| `results/` | results of past experiments: `SUMMARY.md` (brief per-set results of the runs of November 2026) and one folder per experiment |

## Workflows

Long runs are best started as a systemd service, which survives a restart of the terminal session and limits the memory of all solver
processes together; a stopped run resumes when started again with the same output directory:

```
systemd-run --user --unit=bench --working-directory=$PWD -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 \
    -p StandardOutput=append:$HOME/bench.log -p StandardError=append:$HOME/bench.log .venv/bin/python run_bench.py ...
```

### Comparing two versions of the solver

```
ninja -C ../build/release z3
./build_variant.py old --replace src/smt/theory_str_noodler/regex.cpp=b2f2ec58f
./run_bench.py ~/runs/regex --solver old=../build/release/variants/old/z3 --solver new=../build/release/z3 \
    --sets all --sample-per-set 100 --minutes 40
.venv/bin/python report.py ~/runs/regex/runs.csv --baseline old --out ~/runs/regex/REPORT.md
.venv/bin/python plots.py ~/runs/regex/runs.csv --baseline old --new new --out ~/runs/regex/plots
```

`--replace` takes a file or a git revision; a header that changed between the versions cannot be replaced, so a source that needs another
header has to be edited to fit the current one (as for the old bounds in `results/reduce-counts-2026-11-05/RESULTS.md`).

### Counting and measuring the reductions

```
./build_variant.py counts --reduce-log --patch instrumentation/reduce-tags.patch
./run_bench.py ~/runs/counts --solver counts=../build/release/variants/counts/z3 --sets all --sample-per-set 100 --reduce-log
.venv/bin/python reduce_report.py ~/runs/counts --baseline counts
```

For the statistics of the cost of the reduction, measure every reduction (`--patch instrumentation/no-guards.patch`) and all properties
of the automata (`REDUCE_LOG_GRAPH=1` in the environment of `run_bench.py`), then run `reduce_cost_analysis.py ~/runs/stats --out ~/runs/stats/analysis`.

The patches are tied to the source they were made from; when `git apply` refuses one, edit a copy of the source and make the patch again
(`git diff --no-index`, with the paths changed to `a/src/...` and `b/src/...`).

## Outputs of run_bench.py

- `runs.csv`: `file`, `set`, `solver`, `expected` (the `:status` of the formula), `result` (the answers, `timeout`, `crash(SIGNAL)`, `error`
  or `other`), `outcome` (`solved`, `wrong`, `timeout`, `unknown` or `failed`, see `benchlib.outcome`), `seconds`, and with
  `--reduce-log` the number of reductions and their total time in ns.
- `reduce-calls.csv`: one row per distinct reduction of a run (same caller, input and result), with the `site` (the calling function, plus
  the operation of the tag), the properties of the input automaton (see `instrumentation/reduce_wrap.cpp`), the size of the result,
  whether it was cut by the timeout (`censored`), the number of `repeats` and their times.
- `provenance.json`: the command, the machine, `git describe` of the repository, and the path, checksum and version of each solver.

## Pitfalls

- The time of a run includes about 20-25 ms of starting z3, which is most of the time of a typical easy formula; compare ratios only on
  formulas that take longer (`bench_data.MIN_TIME` caps the ratios of very fast ones).
- Binaries that differ only in code a formula never executes still differ by about ±2 % on it (code layout), and separate runs differ
  by up to 5 %; compare solvers in the same run, and check whether the formulas with differences reach the changed code at all
  (for example with `--reduce-log`).
- The order of the solvers' search depends on details such as which atoms exist; results of single formulas can change a lot with
  `smt.random_seed`, so judge changes on sets, not on single formulas.
