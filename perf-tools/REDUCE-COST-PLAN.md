# Plan: a cost-based guard for `mata::nfa::reduce`

## Goal

Replace the state-count guards of the simulation reduction with a guard based on the measured cost of `reduce`:
- `RED_BOUND = 1000` (NFA construction in `regex.cpp`, membership heuristics),
- `INTERSECTION_RED_BOUND = 100` (intersections in `create_aut_assignment_for_formula`).

The simulation in mata/Simlib is roughly (number of simulation classes) × (number of transitions) in time, and its counters grow with states × symbols.
A state count alone cannot tell a sparse loop NFA (cheap to reduce, and reducing it pays off: `lang_inclusion_1722`) from a dense complement over a big alphabet (expensive: `lang_ops_0145`, `substr_0087`).

## 1. Instrumentation (no change of the branch sources)

Extend `perf-tools/reduce_wrap.cpp` (link-time wrapper of `mata::nfa::reduce`).
For each call, compute the primitives of the input automaton before the timed part:
- states, initial states, final states, useful (trimmed) states;
- transitions (state, symbol, target), moves ((state, symbol) pairs with a target), epsilon transitions, self-loops;
- used symbols;
- max out-degree of a state, max number of targets of one move (nondeterminism), deterministic flag;
- number of SCCs and the size of the largest SCC.

After the call: states and transitions of the result, time in ns (`steady_clock`, only the `reduce` call is timed).

Context:
- call site: return address, mapped to file:line (the calling Noodler objects are compiled with `-g` in the variant);
- for the NFA construction: the regex operation of the node (concatenation, union, star, loop, intersection, complement) and the size of Noodler's alphabet, passed through a thread-local tag set in a variant copy of `regex.cpp` (in `perf-tools/variant-src`, not in the branch);
- sequence number of the call in the run.

Each call prints a START line (with the primitives) before `reduce` and an END line after it, so a call cut by the timeout is still recorded, as censored (time ≥ elapsed).
With all smt-bench formulas there will be millions of calls, so the wrapper should append the lines to a file per process (e.g., a path from an environment variable such as `REDUCE_LOG`) instead of stderr, which the runner would have to keep in memory.
The primitives (SCCs, useful states) are computed outside the timed part, they only make the whole run slower.

## 2. Variant without guards

All guards are effectively infinite (`RED_BOUND`, `INTERSECTION_RED_BOUND` in `regex.cpp`, `memb_heuristics_procedures.cpp`, `theory_str_noodler_final_check.cpp`), so the expensive reductions the guards skip today are measured too.
Linked with the wrapper.

## 3. Collection

Runner `perf-tools/reduce_stats_collect.py` (based on `bound_probe.py` and the `--list`/options support of `smtbench_run.py`):
- **all smt-bench formulas**: every `bench/*.input` list of smt-bench (about 393k formulas); this needs `download_smt_benchmarks.sh` (SMT-LIB'25 QF_S/QF_SLIA/QF_SNIA) and `git submodule update --init` (zaligvinder, regex-smt-benchmarks, ecma2020-smt-bench);
- options: none for the standard sets and `ecma2020` (memberships), `smt.str.ecma_engine_semantics=true` for `ecma2020_mixed_bmp` (as the `z3-noodler-ecma` tool of smt-bench's `smt.yaml` and the `SOLVER_OPTIONS` of ecma2020-smt-bench's `run.py`);
- timeout 30 s (longer than in the benchmarks, fewer censored calls); as many jobs as the machine allows with a memory ceiling per job group (systemd scope), timing noise grows with load, so not every core;
- the collection is a measurement run, not a benchmark: it uses the variant without guards.

Output:
- `results/reduce-stats-<date>.csv.gz`: one row per call (formula, set, call site, node operation, sequence number, all primitives, result sizes, time in ns, censored flag);
- `results/reduce-stats-<date>-formulas.csv`: one row per formula (result, total time, number of reduce calls, total reduce time), to see the share of `reduce` in the solving time.

Millions of rows are expected (one random_mix formula did 5000 calls in 10 s), hence gzip, or Parquet if pyarrow is available.

## 4. Analysis (Python)

Environment: only numpy is installed, so a venv `perf-tools/.venv` with pandas, scipy, statsmodels, scikit-learn and matplotlib.

Script `perf-tools/reduce_cost_analysis.py`:
1. **Cleaning.**
   Calls of the same formula with the same call site and primitives (repeated final checks) are merged into one row with the median time, or weighted by 1 / (calls of the formula), so that formulas with many final checks do not dominate.
   Calls below the timer resolution are kept, but marked.
2. **Ranking of single primitives.**
   Spearman ρ and Kendall τ between each primitive and the time.
   They are rank-based, so it does not matter whether a primitive enters linearly or logarithmically.
   ROC AUC of each primitive for "expensive call" (e.g., > 50 ms), which is the Mann–Whitney U test.
3. **Cost model with combinations.**
   OLS of log(time) on the logarithms of the primitives.
   Combinations do not have to be computed beforehand: log(Q^a · T^b) = a·log Q + b·log T, so the fitted exponents give the best product of powers (a ≈ b ≈ 1 means states × transitions).
   Other combinations (e.g., non-multiplicative ones) are tested as interaction terms with nested-model F or likelihood-ratio tests.
4. **Inference.**
   Standard errors clustered by formula (calls of one run are not independent) and robust to heteroscedasticity.
   VIF for collinearity; states and transitions are strongly correlated, so they may be reparametrized as log Q and log(T/Q) (density).
5. **Model selection.**
   With hundreds of thousands of rows nearly every p-value is close to 0, so significance alone decides nothing.
   The models are compared by effect sizes, AIC/BIC and grouped k-fold cross-validation (folds by formula), and the simplest model within the noise of the best one wins.
6. **Censored calls.**
   Checked to be predicted expensive (or modeled as censored, e.g., an accelerated failure time model).
7. **Benefit.**
   Reduction ratios (states and transitions after / before) per primitive and call site, to see whether the expensive reductions are also the useful ones (e.g., loops).
8. **Guard.**
   From the cost model: skip if the predicted time exceeds a budget (e.g., 50 ms).
   Alternatively a depth-2 decision tree on the primitives, which gives a simple rule.
   For candidate thresholds: how many cheap reductions are skipped and how many expensive ones are kept.

Outputs: tables and log-log plots in `results/`.

## 5. Validation

- Implement the guard as one helper (e.g., `regex::should_reduce(const Nfa&)` in `regex.h`) used at all guarded places, build a variant.
- Known cases first: `lang_inclusion_1722` (must stay reduced), `lang_ops_0145`/`2448`, `regex_6059`/`7316`, `random_mix_1041`, `substr_0087` (an older mixed formula).
- Then a benchmark on **all smt-bench formulas**: the guard variant against **the current state** (the branch as committed: `INTERSECTION_RED_BOUND = 100`, `RED_BOUND` as decided from the 1000 vs 250 run), both binaries in one random-order pool (`smtbench_run.py` queues the runs of a formula next to each other), comparison by `smtbench_compare.py`, brief results into `results/SUMMARY.md` by `summarize.py`.
- Timing differences of a few percent between two binaries are not significant by themselves: binaries that differ only in code a formula never executes differed by ±2 % on the same formula, and separate runs differed by up to 5 %.
  To separate real effects from noise, check whether the formulas with differences reach the changed code at all (as done with `bound_probe.py`).

## Decisions

- Collection on all smt-bench formulas, timeout 30 s, on a more powerful machine (decided 2026-11-04).
- Comparison of the resulting guard with the current state (decided 2026-11-04).
- Still open: additions to the list of primitives; the cost budget of the guard, chosen after seeing the time distribution.
