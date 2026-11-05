# How many automata are reduced: the bounds before and after the cost guard (2026-11-05)

The question: how many reductions (`mata::nfa::reduce` calls) do the solver versions make, and how much do they shrink the automata?

- **old**: the bounds before the cost guard (sources of b2f2ec58f): fewer than 1000 states at the regex construction and in the membership
  heuristics, fewer than 100 states at the final-check intersection, and intersection arguments with at least 1000 states always reduced.
- **new**: the cost guard of 018f0c981, states × transitions ≤ 1e5 at all these sites (HEAD 68d12cfc2).

## Summary

Over the 2352 formulas that both finished:

| | old | new |
|---|---|---|
| reductions | 716,300 | 716,100 |
| reductions at the guarded sites | 48,270 | 48,070 |
| time of the reductions at the guarded sites | 215 s | 24 s |
| time of all reductions | 314 s | 124 s |
| states removed by all reductions | 269,000 | 247,000 |
| transitions removed by all reductions | 6.46M | 5.32M |

- The new guard skips only about 200 reductions (0.4 % of those at the guarded sites), but they took 190 of the 215 s.
- The skipped reductions removed 8 % of all removed states, mostly after concatenations at the regex construction (36,500 → 21,900) and
  in the membership heuristics (8,200 → 4,900).
- The most expensive ones are the intersection arguments with at least 1000 states, which only the old version reduces: 27 reductions,
  122 s (in matching).
- 93 % of all reductions are at sites without any guard, and some of them almost never change the automaton:
  - `seg_nfa::segs_one_initial_final`: 507,500 reductions (71 % of all), 27 s, 5,280 states removed in total;
  - `FormulaPreprocessor::refine_languages`: 16,090 reductions, 7 s, no state removed;
  - `AutAssignment::reduce`: 9,473 reductions, 15 states removed.

Per set, the number of reductions changes only in denghang (1785 → 1741), automatark, ecma2020, stringfuzz, redos, ecma2020_mixed_bmp
and matching (106 → 36, with 183 s → 0.02 s of reduction time).
Details: [REDUCE-REPORT.md](REDUCE-REPORT.md).

## Outcomes and times

Of the 2478 formulas: 3 solved → timeout and 7 timeout → solved (all in matching), no wrong answers.
The total time is 1.012 of the old one, the time of the formulas solved by both 1.027, the geometric mean of the per-formula ratio 0.965.
The per-set totals drop in denghang (9.4 → 5.0 s), ecma2020 (4.1 → 3.5 s), automatark (3.7 → 3.3 s) and stringfuzz (9.5 → 9.0 s).
They grow in matching (992 → 1054 s): its `wildcard-matching-regex-*` formulas split into ones that get about 2.3× slower (e.g., -54 8.5 →
20.3 s, as in [the guard experiment](../reduce-guard-2026-11-04/RESULTS.md#where-the-guard-loses), the unreduced intersection arguments)
and ones that get up to 80× faster (e.g., -100 23.5 → 0.29 s).
Details: [REPORT.md](REPORT.md), [plots/](plots/).

The times are less reliable than in the other experiments: the binaries log every reduction and compute the properties of each automaton
(outside the measured reduction time, but inside the solving time), and the sample has only 100 formulas per set.

## Method

- Binaries: `build/release/variants/count-{old,new}/z3` on the laptop, built from the release build of 68d12cfc2 with the reduce wrapper
  (the version of 2026-11-04, which computes all properties for every call) and the operation tags:
  - new: `regex.cpp` of HEAD with the tags of `instrumentation/reduce-tags.patch` (without the membership-heuristic tags, added later);
  - old: `regex.cpp`, `memb_heuristics_procedures.cpp` and `theory_str_noodler_final_check.cpp` of b2f2ec58f with
    `instrumentation/old-versions/reduce-tags-b2f2ec58f.patch`, and `RED_BOUND` / `INTERSECTION_RED_BOUND` replaced by 1000 / 100,
    as HEAD's `regex.h` no longer defines them.
- Formulas: 100 random formulas of each of the 26 sets available on the laptop (smt-bench without regex, zaligvinder, biopython, django,
  thefuck, position_hard and smtcomp25; ecma2020 and ecma2020_mixed_bmp from ecma2020-smt-bench), 2478 formulas.
- `run_bench.py OUT --solver old=... --solver new=... --sets all --sample-per-set 100 --seed 1105 --jobs 4 --timeout 30 --minutes 40
  --reduce-log`, as a systemd service with MemoryHigh 6G / MemoryMax 8G; all 4956 runs finished in 40 minutes.
- Reports: `reduce_report.py OUT --baseline old`, `report.py OUT/runs.csv --baseline old`, `plots.py ... --baseline old --new new`.
- Raw data (runs.csv, reduce-calls.csv, run.log): `~/Documents/perf-runs/reduce-counts-2026-11-05/` on the laptop;
  [provenance.json](provenance.json) has the checksums of the binaries.
