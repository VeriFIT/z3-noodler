# Benchmark summaries

Brief per-set results of the perf-experiment benchmarks (old = 2d58ba1af, new = perf-experiment unless noted).
Timeout 10 s, 4 jobs, release builds. "other" = unknown, error or crash. Mean times include timeouts as 10 s.
The raw CSVs, logs and sample lists named below stayed on the laptop (archive `~/Documents/perf-experiment-archive-2026-11-04/perf-tools/`).

## ECMAScript benchmark, all memberships + all 4000 BMP mixed (2026-11-04)

Results: ecma2020-smt-bench/results/old-2d58ba1af.csv, new-perf-experiment.csv (run 2026-11-03).

| set | solver | formulas | solved | wrong | timeout | other | mean time [s] | mean time of solved [s] |
|---|---|---|---|---|---|---|---|---|
| memberships/regex | new | 8815 | 8704 | 0 | 11 | 100 | 0.065 | 0.053 |
| memberships/regex | old | 8815 | 8600 | 0 | 115 | 100 | 0.290 | 0.163 |
| mixed_constraints/bmp/lang_equality | new | 1000 | 772 | 0 | 31 | 197 | 0.399 | 0.057 |
| mixed_constraints/bmp/lang_equality | old | 1000 | 463 | 0 | 172 | 365 | 2.098 | 0.073 |
| mixed_constraints/bmp/lang_inclusion | new | 1000 | 754 | 0 | 18 | 228 | 0.241 | 0.057 |
| mixed_constraints/bmp/lang_inclusion | old | 1000 | 426 | 0 | 114 | 460 | 1.291 | 0.147 |
| mixed_constraints/bmp/lang_ops | new | 400 | 389 | 0 | 11 | 0 | 0.674 | 0.411 |
| mixed_constraints/bmp/lang_ops | old | 400 | 375 | 0 | 24 | 1 | 1.008 | 0.435 |
| mixed_constraints/bmp/random_mix | new | 1600 | 346 | 0 | 1251 | 3 | 8.362 | 2.490 |
| mixed_constraints/bmp/random_mix | old | 1600 | 297 | 0 | 1218 | 85 | 8.249 | 2.372 |
| **total** | new | 12815 | 10965 | 0 | 1322 | 528 | 1.160 | 0.143 |
| **total** | old | 12815 | 10161 | 0 | 1643 | 1011 | 1.525 | 0.233 |

## smt-bench 10-minute sample (2393 formulas, 23 sets) (2026-11-04)

Results: perf-tools/results/smtbench-1103-quick.csv (run 2026-11-03). Formulas with only one run (stopped at the deadline) are included per solver.

| set | solver | formulas | solved | wrong | timeout | other | mean time [s] | mean time of solved [s] |
|---|---|---|---|---|---|---|---|---|
| automatark | new | 99 | 99 | 0 | 0 | 0 | 0.060 | 0.060 |
| automatark | old | 99 | 99 | 0 | 0 | 0 | 0.074 | 0.074 |
| denghang | new | 100 | 100 | 0 | 0 | 0 | 0.134 | 0.134 |
| denghang | old | 100 | 100 | 0 | 0 | 0 | 0.156 | 0.156 |
| full_str_int | new | 111 | 111 | 0 | 0 | 0 | 0.049 | 0.049 |
| full_str_int | old | 111 | 111 | 0 | 0 | 0 | 0.050 | 0.050 |
| hornstr | new | 112 | 112 | 0 | 0 | 0 | 0.050 | 0.050 |
| hornstr | old | 112 | 112 | 0 | 0 | 0 | 0.059 | 0.059 |
| kaluza | new | 110 | 110 | 0 | 0 | 0 | 0.031 | 0.031 |
| kaluza | old | 110 | 110 | 0 | 0 | 0 | 0.032 | 0.032 |
| kepler | new | 114 | 114 | 0 | 0 | 0 | 0.039 | 0.039 |
| kepler | old | 114 | 114 | 0 | 0 | 0 | 0.039 | 0.039 |
| leetcode | new | 106 | 106 | 0 | 0 | 0 | 0.024 | 0.024 |
| leetcode | old | 106 | 106 | 0 | 0 | 0 | 0.024 | 0.024 |
| matching | new | 111 | 77 | 0 | 34 | 0 | 6.828 | 5.427 |
| matching | old | 111 | 77 | 0 | 34 | 0 | 6.919 | 5.558 |
| negated_predicates | new | 105 | 91 | 0 | 14 | 0 | 1.728 | 0.456 |
| negated_predicates | old | 105 | 91 | 0 | 14 | 0 | 1.731 | 0.459 |
| norn | new | 110 | 110 | 0 | 0 | 0 | 0.024 | 0.024 |
| norn | old | 110 | 110 | 0 | 0 | 0 | 0.026 | 0.026 |
| omark | new | 17 | 10 | 0 | 7 | 0 | 4.139 | 0.036 |
| omark | old | 17 | 10 | 0 | 7 | 0 | 4.139 | 0.036 |
| pcp | new | 110 | 51 | 0 | 0 | 59 | 0.022 | 0.022 |
| pcp | old | 110 | 51 | 0 | 0 | 59 | 0.022 | 0.023 |
| pyex | new | 111 | 110 | 0 | 1 | 0 | 0.301 | 0.213 |
| pyex | old | 111 | 110 | 0 | 1 | 0 | 0.315 | 0.227 |
| redos | new | 112 | 112 | 0 | 0 | 0 | 0.703 | 0.703 |
| redos | old | 112 | 112 | 0 | 0 | 0 | 0.685 | 0.685 |
| rna | new | 109 | 109 | 0 | 0 | 0 | 0.079 | 0.079 |
| rna | old | 109 | 109 | 0 | 0 | 0 | 0.080 | 0.080 |
| slent | new | 104 | 104 | 0 | 0 | 0 | 0.030 | 0.030 |
| slent | old | 104 | 104 | 0 | 0 | 0 | 0.033 | 0.033 |
| slog | new | 107 | 107 | 0 | 0 | 0 | 0.054 | 0.054 |
| slog | old | 107 | 107 | 0 | 0 | 0 | 0.057 | 0.057 |
| str_small_rw | new | 109 | 107 | 0 | 2 | 0 | 0.213 | 0.030 |
| str_small_rw | old | 109 | 107 | 0 | 2 | 0 | 0.213 | 0.030 |
| stringfuzz | new | 105 | 105 | 0 | 0 | 0 | 0.031 | 0.031 |
| stringfuzz | old | 105 | 105 | 0 | 0 | 0 | 0.033 | 0.033 |
| sygus_qgen | new | 113 | 113 | 0 | 0 | 0 | 0.022 | 0.022 |
| sygus_qgen | old | 113 | 113 | 0 | 0 | 0 | 0.023 | 0.023 |
| transducer_plus | new | 91 | 26 | 0 | 54 | 11 | 6.518 | 1.279 |
| transducer_plus | old | 91 | 26 | 0 | 54 | 11 | 6.518 | 1.267 |
| webapp | new | 110 | 110 | 0 | 0 | 0 | 0.094 | 0.094 |
| webapp | old | 110 | 110 | 0 | 0 | 0 | 0.105 | 0.105 |
| woorpje | new | 117 | 114 | 0 | 3 | 0 | 0.346 | 0.092 |
| woorpje | old | 117 | 114 | 0 | 3 | 0 | 0.350 | 0.096 |
| **total** | new | 2393 | 2208 | 0 | 115 | 70 | 0.776 | 0.311 |
| **total** | old | 2393 | 2208 | 0 | 115 | 70 | 0.784 | 0.319 |

## Reduce bound of the intersection in create_aut_assignment_for_formula, formulas reaching 500 states (2026-11-04)

13 formulas of the fixed sample results/bound-sample.txt (3193 formulas: the 2393 smt-bench formulas of the 10-minute sample, 400 memberships, 100 of each mixed family) whose intersections reach 500 states without the guard (probe: results/bound-probe-1104.csv). On the other 3180 formulas all bounds >= 500 behave the same: no smt-bench formula or membership has an intersection of 185 states or more. 3 repetitions, means over all runs. bN = reduce only intersections with fewer than N states (b1000 = perf-experiment, none = no guard). Results: results/bound-1104-rep{1,2,3}.csv. Best: b500 (lang_ops_2448 4.6 -> 0.3 s, lang_ops_2725 4.4 -> 0.3 s, lang_ops_2535 10 -> 4.1 s).

| set | solver | formulas | solved | wrong | timeout | other | mean time [s] | mean time of solved [s] |
|---|---|---|---|---|---|---|---|---|
| lang_ops | b1000 | 18 | 18 | 0 | 0 | 0 | 4.265 | 4.265 |
| lang_ops | b10000 | 18 | 15 | 0 | 3 | 0 | 4.747 | 3.697 |
| lang_ops | b2500 | 18 | 15 | 0 | 3 | 0 | 4.931 | 3.917 |
| lang_ops | b500 | 18 | 18 | 0 | 0 | 0 | 1.534 | 1.534 |
| lang_ops | b5000 | 18 | 15 | 0 | 3 | 0 | 4.773 | 3.728 |
| lang_ops | none | 18 | 15 | 0 | 3 | 0 | 4.762 | 3.714 |
| random_mix | b1000 | 21 | 0 | 0 | 21 | 0 | 10.000 | 0.000 |
| random_mix | b10000 | 21 | 0 | 0 | 21 | 0 | 10.000 | 0.000 |
| random_mix | b2500 | 21 | 0 | 0 | 21 | 0 | 10.000 | 0.000 |
| random_mix | b500 | 21 | 0 | 0 | 21 | 0 | 10.000 | 0.000 |
| random_mix | b5000 | 21 | 0 | 0 | 21 | 0 | 10.000 | 0.000 |
| random_mix | none | 21 | 0 | 0 | 21 | 0 | 10.000 | 0.000 |
| **total** | b1000 | 39 | 18 | 0 | 21 | 0 | 7.353 | 4.265 |
| **total** | b10000 | 39 | 15 | 0 | 24 | 0 | 7.576 | 3.697 |
| **total** | b2500 | 39 | 15 | 0 | 24 | 0 | 7.660 | 3.917 |
| **total** | b500 | 39 | 18 | 0 | 21 | 0 | 6.093 | 1.534 |
| **total** | b5000 | 39 | 15 | 0 | 24 | 0 | 7.588 | 3.728 |
| **total** | none | 39 | 15 | 0 | 24 | 0 | 7.582 | 3.714 |

## Low reduce bounds of the intersection, formulas with any intersection (2026-11-04)

Formulas of results/bound-sample.txt with an intersection in create_aut_assignment_for_formula (results/bound-any.txt, 392 formulas; the 12-minute run reached 271, rows with all four runs: 270). bN = reduce only intersections with fewer than N states. Results: results/bound-any-1104.csv. b1 (never reduce) adds 39 pyex timeouts and makes norn 10x slower; b100, b250 and b500 give the same outcomes; lang_ops time 18.5 / 18.9 / 21.5 s.

| set | solver | formulas | solved | wrong | timeout | other | mean time [s] | mean time of solved [s] |
|---|---|---|---|---|---|---|---|---|
| full_str_int | b1 | 13 | 13 | 0 | 0 | 0 | 0.152 | 0.152 |
| full_str_int | b100 | 13 | 13 | 0 | 0 | 0 | 0.154 | 0.154 |
| full_str_int | b250 | 13 | 13 | 0 | 0 | 0 | 0.154 | 0.154 |
| full_str_int | b500 | 13 | 13 | 0 | 0 | 0 | 0.154 | 0.154 |
| hornstr | b1 | 17 | 17 | 0 | 0 | 0 | 0.049 | 0.049 |
| hornstr | b100 | 17 | 17 | 0 | 0 | 0 | 0.049 | 0.049 |
| hornstr | b250 | 17 | 17 | 0 | 0 | 0 | 0.049 | 0.049 |
| hornstr | b500 | 17 | 17 | 0 | 0 | 0 | 0.050 | 0.050 |
| kaluza | b1 | 1 | 1 | 0 | 0 | 0 | 0.648 | 0.648 |
| kaluza | b100 | 1 | 1 | 0 | 0 | 0 | 0.636 | 0.636 |
| kaluza | b250 | 1 | 1 | 0 | 0 | 0 | 0.633 | 0.633 |
| kaluza | b500 | 1 | 1 | 0 | 0 | 0 | 0.635 | 0.635 |
| lang_ops | b1 | 41 | 40 | 0 | 1 | 0 | 0.428 | 0.189 |
| lang_ops | b100 | 41 | 40 | 0 | 1 | 0 | 0.450 | 0.211 |
| lang_ops | b250 | 41 | 40 | 0 | 1 | 0 | 0.460 | 0.222 |
| lang_ops | b500 | 41 | 40 | 0 | 1 | 0 | 0.525 | 0.288 |
| leetcode | b1 | 7 | 7 | 0 | 0 | 0 | 0.049 | 0.049 |
| leetcode | b100 | 7 | 7 | 0 | 0 | 0 | 0.049 | 0.049 |
| leetcode | b250 | 7 | 7 | 0 | 0 | 0 | 0.049 | 0.049 |
| leetcode | b500 | 7 | 7 | 0 | 0 | 0 | 0.049 | 0.049 |
| norn | b1 | 45 | 45 | 0 | 0 | 0 | 0.223 | 0.223 |
| norn | b100 | 45 | 45 | 0 | 0 | 0 | 0.025 | 0.025 |
| norn | b250 | 45 | 45 | 0 | 0 | 0 | 0.025 | 0.025 |
| norn | b500 | 45 | 45 | 0 | 0 | 0 | 0.025 | 0.025 |
| pyex | b1 | 64 | 25 | 0 | 39 | 0 | 6.711 | 1.580 |
| pyex | b100 | 64 | 64 | 0 | 0 | 0 | 0.194 | 0.194 |
| pyex | b250 | 64 | 64 | 0 | 0 | 0 | 0.194 | 0.194 |
| pyex | b500 | 64 | 64 | 0 | 0 | 0 | 0.194 | 0.194 |
| random_mix | b1 | 62 | 9 | 0 | 53 | 0 | 8.870 | 2.213 |
| random_mix | b100 | 63 | 9 | 0 | 54 | 0 | 8.917 | 2.421 |
| random_mix | b250 | 63 | 9 | 0 | 54 | 0 | 8.914 | 2.396 |
| random_mix | b500 | 62 | 9 | 0 | 53 | 0 | 8.898 | 2.411 |
| slent | b1 | 2 | 2 | 0 | 0 | 0 | 0.057 | 0.057 |
| slent | b100 | 2 | 2 | 0 | 0 | 0 | 0.059 | 0.059 |
| slent | b250 | 2 | 2 | 0 | 0 | 0 | 0.058 | 0.058 |
| slent | b500 | 2 | 2 | 0 | 0 | 0 | 0.059 | 0.059 |
| str_small_rw | b1 | 2 | 2 | 0 | 0 | 0 | 0.205 | 0.205 |
| str_small_rw | b100 | 2 | 2 | 0 | 0 | 0 | 0.200 | 0.200 |
| str_small_rw | b250 | 2 | 2 | 0 | 0 | 0 | 0.204 | 0.204 |
| str_small_rw | b500 | 2 | 2 | 0 | 0 | 0 | 0.210 | 0.210 |
| stringfuzz | b1 | 7 | 7 | 0 | 0 | 0 | 0.041 | 0.041 |
| stringfuzz | b100 | 7 | 7 | 0 | 0 | 0 | 0.041 | 0.041 |
| stringfuzz | b250 | 7 | 7 | 0 | 0 | 0 | 0.042 | 0.042 |
| stringfuzz | b500 | 7 | 7 | 0 | 0 | 0 | 0.041 | 0.041 |
| woorpje | b1 | 9 | 7 | 0 | 2 | 0 | 2.371 | 0.192 |
| woorpje | b100 | 9 | 7 | 0 | 2 | 0 | 2.375 | 0.196 |
| woorpje | b250 | 9 | 7 | 0 | 2 | 0 | 2.371 | 0.191 |
| woorpje | b500 | 9 | 7 | 0 | 2 | 0 | 2.374 | 0.195 |
| **total** | b1 | 270 | 175 | 0 | 95 | 0 | 3.826 | 0.474 |
| **total** | b100 | 271 | 214 | 0 | 57 | 0 | 2.287 | 0.233 |
| **total** | b250 | 271 | 214 | 0 | 57 | 0 | 2.288 | 0.233 |
| **total** | b500 | 270 | 214 | 0 | 56 | 0 | 2.270 | 0.247 |

## Reduce bound of the intersection: 1000 (perf-experiment) vs 250, 40-minute run (2026-11-04)

Fixed sample results/bound-big-sample.txt (12412 formulas: all 8815 memberships, all lang_ops/lang_inclusion/lang_equality, 300 random_mix, 40 of each smt-bench set), all formulas finished (38 min). Results: results/bound-big-1104.csv, comparison logs/bound-big-1104-compare.txt. b250: lang_ops 0.70x on formulas solved by both (156.6 -> 109.1 s), random_mix 3 timeouts -> solved, everything else the same outcomes and 0.97-1.02x (layout noise), 0 wrong.

| set | solver | formulas | solved | wrong | timeout | other | mean time [s] | mean time of solved [s] |
|---|---|---|---|---|---|---|---|---|
| automatark | b1000 | 40 | 40 | 0 | 0 | 0 | 0.045 | 0.045 |
| automatark | b250 | 40 | 40 | 0 | 0 | 0 | 0.045 | 0.045 |
| denghang | b1000 | 40 | 40 | 0 | 0 | 0 | 0.066 | 0.066 |
| denghang | b250 | 40 | 40 | 0 | 0 | 0 | 0.067 | 0.067 |
| full_str_int | b1000 | 40 | 39 | 0 | 1 | 0 | 0.315 | 0.067 |
| full_str_int | b250 | 40 | 39 | 0 | 1 | 0 | 0.315 | 0.066 |
| hornstr | b1000 | 40 | 40 | 0 | 0 | 0 | 0.046 | 0.046 |
| hornstr | b250 | 40 | 40 | 0 | 0 | 0 | 0.045 | 0.045 |
| kaluza | b1000 | 40 | 40 | 0 | 0 | 0 | 0.025 | 0.025 |
| kaluza | b250 | 40 | 40 | 0 | 0 | 0 | 0.025 | 0.025 |
| kepler | b1000 | 40 | 40 | 0 | 0 | 0 | 0.024 | 0.024 |
| kepler | b250 | 40 | 40 | 0 | 0 | 0 | 0.024 | 0.024 |
| lang_equality | b1000 | 1000 | 772 | 0 | 31 | 197 | 0.397 | 0.057 |
| lang_equality | b250 | 1000 | 772 | 0 | 31 | 197 | 0.397 | 0.056 |
| lang_inclusion | b1000 | 1000 | 754 | 0 | 18 | 228 | 0.241 | 0.056 |
| lang_inclusion | b250 | 1000 | 754 | 0 | 18 | 228 | 0.241 | 0.056 |
| lang_ops | b1000 | 400 | 389 | 0 | 11 | 0 | 0.666 | 0.403 |
| lang_ops | b250 | 400 | 389 | 0 | 11 | 0 | 0.548 | 0.281 |
| leetcode | b1000 | 40 | 40 | 0 | 0 | 0 | 0.025 | 0.025 |
| leetcode | b250 | 40 | 40 | 0 | 0 | 0 | 0.025 | 0.025 |
| matching | b1000 | 40 | 33 | 0 | 7 | 0 | 6.248 | 5.452 |
| matching | b250 | 40 | 33 | 0 | 7 | 0 | 6.281 | 5.492 |
| memberships | b1000 | 8815 | 8704 | 0 | 11 | 100 | 0.064 | 0.052 |
| memberships | b250 | 8815 | 8704 | 0 | 11 | 100 | 0.065 | 0.053 |
| negated_predicates | b1000 | 40 | 37 | 0 | 3 | 0 | 1.516 | 0.828 |
| negated_predicates | b250 | 40 | 37 | 0 | 3 | 0 | 1.523 | 0.836 |
| norn | b1000 | 40 | 40 | 0 | 0 | 0 | 0.027 | 0.027 |
| norn | b250 | 40 | 40 | 0 | 0 | 0 | 0.027 | 0.027 |
| omark | b1000 | 17 | 10 | 0 | 7 | 0 | 4.140 | 0.039 |
| omark | b250 | 17 | 10 | 0 | 7 | 0 | 4.140 | 0.038 |
| pcp | b1000 | 40 | 16 | 0 | 0 | 24 | 0.022 | 0.022 |
| pcp | b250 | 40 | 16 | 0 | 0 | 24 | 0.022 | 0.022 |
| pyex | b1000 | 40 | 40 | 0 | 0 | 0 | 0.261 | 0.261 |
| pyex | b250 | 40 | 40 | 0 | 0 | 0 | 0.262 | 0.262 |
| random_mix | b1000 | 300 | 77 | 0 | 221 | 2 | 7.956 | 2.216 |
| random_mix | b250 | 300 | 80 | 0 | 218 | 2 | 7.940 | 2.447 |
| redos | b1000 | 40 | 39 | 0 | 1 | 0 | 1.018 | 0.788 |
| redos | b250 | 40 | 39 | 0 | 1 | 0 | 1.023 | 0.793 |
| rna | b1000 | 40 | 40 | 0 | 0 | 0 | 0.078 | 0.078 |
| rna | b250 | 40 | 40 | 0 | 0 | 0 | 0.079 | 0.079 |
| slent | b1000 | 40 | 40 | 0 | 0 | 0 | 0.028 | 0.028 |
| slent | b250 | 40 | 40 | 0 | 0 | 0 | 0.028 | 0.028 |
| slog | b1000 | 40 | 40 | 0 | 0 | 0 | 0.115 | 0.115 |
| slog | b250 | 40 | 40 | 0 | 0 | 0 | 0.117 | 0.117 |
| str_small_rw | b1000 | 40 | 36 | 0 | 4 | 0 | 1.028 | 0.032 |
| str_small_rw | b250 | 40 | 36 | 0 | 4 | 0 | 1.029 | 0.032 |
| stringfuzz | b1000 | 40 | 40 | 0 | 0 | 0 | 0.040 | 0.040 |
| stringfuzz | b250 | 40 | 40 | 0 | 0 | 0 | 0.040 | 0.040 |
| sygus_qgen | b1000 | 40 | 40 | 0 | 0 | 0 | 0.022 | 0.022 |
| sygus_qgen | b250 | 40 | 40 | 0 | 0 | 0 | 0.022 | 0.022 |
| transducer_plus | b1000 | 40 | 13 | 0 | 22 | 5 | 6.058 | 0.990 |
| transducer_plus | b250 | 40 | 13 | 0 | 22 | 5 | 6.055 | 0.981 |
| webapp | b1000 | 40 | 39 | 0 | 0 | 1 | 0.198 | 0.192 |
| webapp | b250 | 40 | 39 | 0 | 0 | 1 | 0.201 | 0.195 |
| woorpje | b1000 | 40 | 40 | 0 | 0 | 0 | 0.176 | 0.176 |
| woorpje | b250 | 40 | 40 | 0 | 0 | 0 | 0.175 | 0.175 |
| **total** | b1000 | 12412 | 11518 | 0 | 337 | 557 | 0.373 | 0.102 |
| **total** | b250 | 12412 | 11521 | 0 | 334 | 557 | 0.369 | 0.100 |

## Reduce bound of the intersection: 200 vs 150, 40-minute run (2026-11-04)

Same sample as the 1000 vs 250 run (results/bound-big-sample.txt, 12412 formulas), all finished (38 min). Results: results/bound-big2-1104.csv. Formulas solved by all four bounds, total time: 1000 = 1165.0 s, 250 = 1120.5 s, 200 = 1130.8 s, 150 = 1136.8 s; lang_ops alone 156.6 / 109.1 / 106.6 / 101.4 s. Solved: 11518 / 11521 / 11521 / 11521, 0 wrong. The slightly higher times of 200 and 150 on memberships, matching, slog etc. are run-to-run noise (these formulas have no intersection at all, checked with the probe); only lang_ops and random_mix reach the guard.

| set | solver | formulas | solved | wrong | timeout | other | mean time [s] | mean time of solved [s] |
|---|---|---|---|---|---|---|---|---|
| automatark | b150 | 40 | 40 | 0 | 0 | 0 | 0.047 | 0.047 |
| automatark | b200 | 40 | 40 | 0 | 0 | 0 | 0.046 | 0.046 |
| denghang | b150 | 40 | 40 | 0 | 0 | 0 | 0.068 | 0.068 |
| denghang | b200 | 40 | 40 | 0 | 0 | 0 | 0.066 | 0.066 |
| full_str_int | b150 | 40 | 39 | 0 | 1 | 0 | 0.315 | 0.067 |
| full_str_int | b200 | 40 | 39 | 0 | 1 | 0 | 0.314 | 0.066 |
| hornstr | b150 | 40 | 40 | 0 | 0 | 0 | 0.047 | 0.047 |
| hornstr | b200 | 40 | 40 | 0 | 0 | 0 | 0.047 | 0.047 |
| kaluza | b150 | 40 | 40 | 0 | 0 | 0 | 0.026 | 0.026 |
| kaluza | b200 | 40 | 40 | 0 | 0 | 0 | 0.026 | 0.026 |
| kepler | b150 | 40 | 40 | 0 | 0 | 0 | 0.025 | 0.025 |
| kepler | b200 | 40 | 40 | 0 | 0 | 0 | 0.024 | 0.024 |
| lang_equality | b150 | 1000 | 772 | 0 | 31 | 197 | 0.398 | 0.058 |
| lang_equality | b200 | 1000 | 772 | 0 | 31 | 197 | 0.398 | 0.057 |
| lang_inclusion | b150 | 1000 | 754 | 0 | 18 | 228 | 0.241 | 0.057 |
| lang_inclusion | b200 | 1000 | 754 | 0 | 18 | 228 | 0.241 | 0.056 |
| lang_ops | b150 | 400 | 389 | 0 | 11 | 0 | 0.528 | 0.261 |
| lang_ops | b200 | 400 | 389 | 0 | 11 | 0 | 0.541 | 0.274 |
| leetcode | b150 | 40 | 40 | 0 | 0 | 0 | 0.024 | 0.024 |
| leetcode | b200 | 40 | 40 | 0 | 0 | 0 | 0.024 | 0.024 |
| matching | b150 | 40 | 33 | 0 | 7 | 0 | 6.408 | 5.646 |
| matching | b200 | 40 | 32 | 0 | 8 | 0 | 6.377 | 5.471 |
| memberships | b150 | 8815 | 8704 | 0 | 11 | 100 | 0.066 | 0.054 |
| memberships | b200 | 8815 | 8704 | 0 | 11 | 100 | 0.066 | 0.054 |
| negated_predicates | b150 | 40 | 37 | 0 | 3 | 0 | 1.531 | 0.844 |
| negated_predicates | b200 | 40 | 37 | 0 | 3 | 0 | 1.511 | 0.823 |
| norn | b150 | 40 | 40 | 0 | 0 | 0 | 0.027 | 0.027 |
| norn | b200 | 40 | 40 | 0 | 0 | 0 | 0.027 | 0.027 |
| omark | b150 | 17 | 10 | 0 | 7 | 0 | 4.140 | 0.038 |
| omark | b200 | 17 | 10 | 0 | 7 | 0 | 4.140 | 0.038 |
| pcp | b150 | 40 | 16 | 0 | 0 | 24 | 0.022 | 0.022 |
| pcp | b200 | 40 | 16 | 0 | 0 | 24 | 0.022 | 0.022 |
| pyex | b150 | 40 | 40 | 0 | 0 | 0 | 0.262 | 0.262 |
| pyex | b200 | 40 | 40 | 0 | 0 | 0 | 0.260 | 0.260 |
| random_mix | b150 | 300 | 80 | 0 | 218 | 2 | 7.943 | 2.461 |
| random_mix | b200 | 300 | 81 | 0 | 217 | 2 | 7.940 | 2.540 |
| redos | b150 | 40 | 39 | 0 | 1 | 0 | 1.008 | 0.777 |
| redos | b200 | 40 | 39 | 0 | 1 | 0 | 1.008 | 0.778 |
| rna | b150 | 40 | 40 | 0 | 0 | 0 | 0.083 | 0.083 |
| rna | b200 | 40 | 40 | 0 | 0 | 0 | 0.082 | 0.082 |
| slent | b150 | 40 | 40 | 0 | 0 | 0 | 0.027 | 0.027 |
| slent | b200 | 40 | 40 | 0 | 0 | 0 | 0.027 | 0.027 |
| slog | b150 | 40 | 40 | 0 | 0 | 0 | 0.122 | 0.122 |
| slog | b200 | 40 | 40 | 0 | 0 | 0 | 0.120 | 0.120 |
| str_small_rw | b150 | 40 | 36 | 0 | 4 | 0 | 1.030 | 0.033 |
| str_small_rw | b200 | 40 | 36 | 0 | 4 | 0 | 1.030 | 0.033 |
| stringfuzz | b150 | 40 | 40 | 0 | 0 | 0 | 0.038 | 0.038 |
| stringfuzz | b200 | 40 | 40 | 0 | 0 | 0 | 0.039 | 0.039 |
| sygus_qgen | b150 | 40 | 40 | 0 | 0 | 0 | 0.022 | 0.022 |
| sygus_qgen | b200 | 40 | 40 | 0 | 0 | 0 | 0.022 | 0.022 |
| transducer_plus | b150 | 40 | 13 | 0 | 22 | 5 | 6.062 | 1.006 |
| transducer_plus | b200 | 40 | 13 | 0 | 22 | 5 | 6.057 | 0.994 |
| webapp | b150 | 40 | 39 | 0 | 0 | 1 | 0.200 | 0.198 |
| webapp | b200 | 40 | 39 | 0 | 0 | 1 | 0.198 | 0.195 |
| woorpje | b150 | 40 | 40 | 0 | 0 | 0 | 0.181 | 0.181 |
| woorpje | b200 | 40 | 40 | 0 | 0 | 0 | 0.180 | 0.180 |
| **total** | b150 | 12412 | 11521 | 0 | 334 | 557 | 0.370 | 0.102 |
| **total** | b200 | 12412 | 11521 | 0 | 334 | 557 | 0.369 | 0.101 |

## Reduce bound of the intersection: 100 vs 50, 40-minute run (2026-11-04)

Same sample (results/bound-big-sample.txt, 12412 formulas), all finished (38 min). Results: results/bound-big3-1104.csv. Formulas solved by all six bounds, total time: 1000 = 1156.0 s, 250 = 1111.5 s, 200 = 1121.9 s, 150 = 1127.7 s, 100 = 1105.2 s, 50 = 1096.0 s; lang_ops alone 156.6 / 109.1 / 106.6 / 101.4 / 89.4 / 86.3 s. Solved 11518 / 11521 / 11521 / 11521 / 11519 / 11521, 0 wrong; the outcome differences are borderline matching/random_mix formulas near the timeout. Formulas slower with 100 and 50 outside lang_ops do not reach the guard (run noise); lang_ops_3331 is slower with 50 (0.28 -> 0.52 s). Earlier: bound 1 (never reduce) breaks pyex and norn, whose intersections reach 47 and 55 states.

| set | solver | formulas | solved | wrong | timeout | other | mean time [s] | mean time of solved [s] |
|---|---|---|---|---|---|---|---|---|
| automatark | b100 | 40 | 40 | 0 | 0 | 0 | 0.045 | 0.045 |
| automatark | b50 | 40 | 40 | 0 | 0 | 0 | 0.045 | 0.045 |
| denghang | b100 | 40 | 40 | 0 | 0 | 0 | 0.067 | 0.067 |
| denghang | b50 | 40 | 40 | 0 | 0 | 0 | 0.066 | 0.066 |
| full_str_int | b100 | 40 | 39 | 0 | 1 | 0 | 0.316 | 0.067 |
| full_str_int | b50 | 40 | 39 | 0 | 1 | 0 | 0.315 | 0.066 |
| hornstr | b100 | 40 | 40 | 0 | 0 | 0 | 0.045 | 0.045 |
| hornstr | b50 | 40 | 40 | 0 | 0 | 0 | 0.045 | 0.045 |
| kaluza | b100 | 40 | 40 | 0 | 0 | 0 | 0.025 | 0.025 |
| kaluza | b50 | 40 | 40 | 0 | 0 | 0 | 0.025 | 0.025 |
| kepler | b100 | 40 | 40 | 0 | 0 | 0 | 0.024 | 0.024 |
| kepler | b50 | 40 | 40 | 0 | 0 | 0 | 0.024 | 0.024 |
| lang_equality | b100 | 1000 | 772 | 0 | 31 | 197 | 0.399 | 0.057 |
| lang_equality | b50 | 1000 | 772 | 0 | 31 | 197 | 0.399 | 0.057 |
| lang_inclusion | b100 | 1000 | 754 | 0 | 18 | 228 | 0.241 | 0.056 |
| lang_inclusion | b50 | 1000 | 754 | 0 | 18 | 228 | 0.241 | 0.056 |
| lang_ops | b100 | 400 | 389 | 0 | 11 | 0 | 0.499 | 0.230 |
| lang_ops | b50 | 400 | 389 | 0 | 11 | 0 | 0.491 | 0.222 |
| leetcode | b100 | 40 | 40 | 0 | 0 | 0 | 0.025 | 0.025 |
| leetcode | b50 | 40 | 40 | 0 | 0 | 0 | 0.025 | 0.025 |
| matching | b100 | 40 | 31 | 0 | 9 | 0 | 6.368 | 5.314 |
| matching | b50 | 40 | 32 | 0 | 8 | 0 | 6.366 | 5.457 |
| memberships | b100 | 8815 | 8704 | 0 | 11 | 100 | 0.066 | 0.054 |
| memberships | b50 | 8815 | 8704 | 0 | 11 | 100 | 0.065 | 0.053 |
| negated_predicates | b100 | 40 | 37 | 0 | 3 | 0 | 1.537 | 0.851 |
| negated_predicates | b50 | 40 | 37 | 0 | 3 | 0 | 1.535 | 0.849 |
| norn | b100 | 40 | 40 | 0 | 0 | 0 | 0.028 | 0.028 |
| norn | b50 | 40 | 40 | 0 | 0 | 0 | 0.027 | 0.027 |
| omark | b100 | 17 | 10 | 0 | 7 | 0 | 4.142 | 0.041 |
| omark | b50 | 17 | 10 | 0 | 7 | 0 | 4.140 | 0.038 |
| pcp | b100 | 40 | 16 | 0 | 0 | 24 | 0.022 | 0.022 |
| pcp | b50 | 40 | 16 | 0 | 0 | 24 | 0.022 | 0.022 |
| pyex | b100 | 40 | 40 | 0 | 0 | 0 | 0.264 | 0.264 |
| pyex | b50 | 40 | 40 | 0 | 0 | 0 | 0.265 | 0.265 |
| random_mix | b100 | 300 | 80 | 0 | 218 | 2 | 7.932 | 2.419 |
| random_mix | b50 | 300 | 81 | 0 | 217 | 2 | 7.918 | 2.461 |
| redos | b100 | 40 | 39 | 0 | 1 | 0 | 1.008 | 0.777 |
| redos | b50 | 40 | 39 | 0 | 1 | 0 | 1.000 | 0.769 |
| rna | b100 | 40 | 40 | 0 | 0 | 0 | 0.081 | 0.081 |
| rna | b50 | 40 | 40 | 0 | 0 | 0 | 0.080 | 0.080 |
| slent | b100 | 40 | 40 | 0 | 0 | 0 | 0.027 | 0.027 |
| slent | b50 | 40 | 40 | 0 | 0 | 0 | 0.027 | 0.027 |
| slog | b100 | 40 | 40 | 0 | 0 | 0 | 0.118 | 0.118 |
| slog | b50 | 40 | 40 | 0 | 0 | 0 | 0.118 | 0.118 |
| str_small_rw | b100 | 40 | 36 | 0 | 4 | 0 | 1.029 | 0.032 |
| str_small_rw | b50 | 40 | 36 | 0 | 4 | 0 | 1.029 | 0.032 |
| stringfuzz | b100 | 40 | 40 | 0 | 0 | 0 | 0.039 | 0.039 |
| stringfuzz | b50 | 40 | 40 | 0 | 0 | 0 | 0.039 | 0.039 |
| sygus_qgen | b100 | 40 | 40 | 0 | 0 | 0 | 0.023 | 0.023 |
| sygus_qgen | b50 | 40 | 40 | 0 | 0 | 0 | 0.022 | 0.022 |
| transducer_plus | b100 | 40 | 13 | 0 | 22 | 5 | 6.066 | 1.009 |
| transducer_plus | b50 | 40 | 13 | 0 | 22 | 5 | 6.069 | 1.014 |
| webapp | b100 | 40 | 39 | 0 | 0 | 1 | 0.204 | 0.202 |
| webapp | b50 | 40 | 39 | 0 | 0 | 1 | 0.206 | 0.204 |
| woorpje | b100 | 40 | 40 | 0 | 0 | 0 | 0.177 | 0.177 |
| woorpje | b50 | 40 | 40 | 0 | 0 | 0 | 0.177 | 0.177 |
| **total** | b100 | 12412 | 11519 | 0 | 336 | 557 | 0.368 | 0.098 |
| **total** | b50 | 12412 | 11521 | 0 | 334 | 557 | 0.367 | 0.099 |

## Reduce bound of the intersection: 125 vs 100, 40-minute run (final candidates) (2026-11-04)

Same sample (results/bound-big-sample.txt, 12412 formulas), all finished (38 min), 125 and 100 in one pool. Results: results/bound-big4-1104.csv, comparison logs/bound-big4-1104-compare.txt. Same outcomes except random_mix_1915 (timeout with 100, solved with 125, near the timeout); 0 wrong. Formulas solved by both: total 1173.3 s (100) vs 1163.8 s (125), lang_ops 94.6 vs 95.3 s, i.e. a tie. Per formula, 100 wins on lang_ops_0145 (0.20 vs 1.42 s, intersections of 112 states) and lang_ops_2575 (0.17 vs 0.34 s). This run was about 5 % slower overall than the 100 vs 50 run (b100 1110.0 -> 1164.2 s), which shows the run-to-run noise.

| set | solver | formulas | solved | wrong | timeout | other | mean time [s] | mean time of solved [s] |
|---|---|---|---|---|---|---|---|---|
| automatark | b100 | 40 | 40 | 0 | 0 | 0 | 0.047 | 0.047 |
| automatark | b125 | 40 | 40 | 0 | 0 | 0 | 0.046 | 0.046 |
| denghang | b100 | 40 | 40 | 0 | 0 | 0 | 0.070 | 0.070 |
| denghang | b125 | 40 | 40 | 0 | 0 | 0 | 0.070 | 0.070 |
| full_str_int | b100 | 40 | 39 | 0 | 1 | 0 | 0.320 | 0.071 |
| full_str_int | b125 | 40 | 39 | 0 | 1 | 0 | 0.320 | 0.071 |
| hornstr | b100 | 40 | 40 | 0 | 0 | 0 | 0.047 | 0.047 |
| hornstr | b125 | 40 | 40 | 0 | 0 | 0 | 0.047 | 0.047 |
| kaluza | b100 | 40 | 40 | 0 | 0 | 0 | 0.026 | 0.026 |
| kaluza | b125 | 40 | 40 | 0 | 0 | 0 | 0.026 | 0.026 |
| kepler | b100 | 40 | 40 | 0 | 0 | 0 | 0.025 | 0.025 |
| kepler | b125 | 40 | 40 | 0 | 0 | 0 | 0.025 | 0.025 |
| lang_equality | b100 | 1000 | 772 | 0 | 31 | 197 | 0.400 | 0.059 |
| lang_equality | b125 | 1000 | 772 | 0 | 31 | 197 | 0.400 | 0.058 |
| lang_inclusion | b100 | 1000 | 754 | 0 | 18 | 228 | 0.244 | 0.058 |
| lang_inclusion | b125 | 1000 | 754 | 0 | 18 | 228 | 0.243 | 0.058 |
| lang_ops | b100 | 400 | 389 | 0 | 11 | 0 | 0.511 | 0.243 |
| lang_ops | b125 | 400 | 389 | 0 | 11 | 0 | 0.513 | 0.245 |
| leetcode | b100 | 40 | 40 | 0 | 0 | 0 | 0.026 | 0.026 |
| leetcode | b125 | 40 | 40 | 0 | 0 | 0 | 0.026 | 0.026 |
| matching | b100 | 40 | 32 | 0 | 8 | 0 | 6.548 | 5.685 |
| matching | b125 | 40 | 32 | 0 | 8 | 0 | 6.503 | 5.629 |
| memberships | b100 | 8815 | 8704 | 0 | 11 | 100 | 0.068 | 0.056 |
| memberships | b125 | 8815 | 8704 | 0 | 11 | 100 | 0.067 | 0.055 |
| negated_predicates | b100 | 40 | 37 | 0 | 3 | 0 | 1.542 | 0.856 |
| negated_predicates | b125 | 40 | 37 | 0 | 3 | 0 | 1.537 | 0.851 |
| norn | b100 | 40 | 40 | 0 | 0 | 0 | 0.029 | 0.029 |
| norn | b125 | 40 | 40 | 0 | 0 | 0 | 0.029 | 0.029 |
| omark | b100 | 17 | 10 | 0 | 7 | 0 | 4.141 | 0.040 |
| omark | b125 | 17 | 10 | 0 | 7 | 0 | 4.140 | 0.037 |
| pcp | b100 | 40 | 16 | 0 | 0 | 24 | 0.023 | 0.023 |
| pcp | b125 | 40 | 16 | 0 | 0 | 24 | 0.023 | 0.022 |
| pyex | b100 | 40 | 40 | 0 | 0 | 0 | 0.291 | 0.291 |
| pyex | b125 | 40 | 40 | 0 | 0 | 0 | 0.289 | 0.289 |
| random_mix | b100 | 300 | 78 | 0 | 220 | 2 | 7.978 | 2.398 |
| random_mix | b125 | 300 | 79 | 0 | 219 | 2 | 7.972 | 2.470 |
| redos | b100 | 40 | 39 | 0 | 1 | 0 | 1.050 | 0.821 |
| redos | b125 | 40 | 39 | 0 | 1 | 0 | 1.051 | 0.822 |
| rna | b100 | 40 | 40 | 0 | 0 | 0 | 0.082 | 0.082 |
| rna | b125 | 40 | 40 | 0 | 0 | 0 | 0.081 | 0.081 |
| slent | b100 | 40 | 40 | 0 | 0 | 0 | 0.027 | 0.027 |
| slent | b125 | 40 | 40 | 0 | 0 | 0 | 0.027 | 0.027 |
| slog | b100 | 40 | 40 | 0 | 0 | 0 | 0.130 | 0.130 |
| slog | b125 | 40 | 40 | 0 | 0 | 0 | 0.126 | 0.126 |
| str_small_rw | b100 | 40 | 36 | 0 | 4 | 0 | 1.030 | 0.033 |
| str_small_rw | b125 | 40 | 36 | 0 | 4 | 0 | 1.029 | 0.033 |
| stringfuzz | b100 | 40 | 40 | 0 | 0 | 0 | 0.041 | 0.041 |
| stringfuzz | b125 | 40 | 40 | 0 | 0 | 0 | 0.041 | 0.041 |
| sygus_qgen | b100 | 40 | 40 | 0 | 0 | 0 | 0.023 | 0.023 |
| sygus_qgen | b125 | 40 | 40 | 0 | 0 | 0 | 0.022 | 0.022 |
| transducer_plus | b100 | 40 | 13 | 0 | 22 | 5 | 6.094 | 1.066 |
| transducer_plus | b125 | 40 | 13 | 0 | 22 | 5 | 6.091 | 1.059 |
| webapp | b100 | 40 | 39 | 0 | 0 | 1 | 0.209 | 0.207 |
| webapp | b125 | 40 | 39 | 0 | 0 | 1 | 0.206 | 0.204 |
| woorpje | b100 | 40 | 40 | 0 | 0 | 0 | 0.190 | 0.190 |
| woorpje | b125 | 40 | 40 | 0 | 0 | 0 | 0.193 | 0.193 |
| **total** | b100 | 12412 | 11518 | 0 | 337 | 557 | 0.373 | 0.102 |
| **total** | b125 | 12412 | 11519 | 0 | 336 | 557 | 0.372 | 0.102 |

## RED_BOUND 1000 vs 100 (with INTERSECTION_RED_BOUND = 100), 40-minute run (2026-11-04)

Same sample (results/bound-big-sample.txt, 12412 formulas), all finished. red1000 = current state (build/release/variants/ibound100), red100 = RED_BOUND 100 in regex.cpp and memb_heuristics_procedures.cpp (variants/red100). Results: results/redbound-1104.csv, comparison logs/redbound-1104-compare.txt. Same outcomes except regex_7316 (timeout -> solved) and random_mix_1041 (solved -> timeout, 5.4 -> 11.3 s, reproducible); 0 wrong. Formulas solved by both: total 0.93x (1150.6 -> 1069.5 s); memberships 0.86x, automatark 0.72x, stringfuzz 0.75x, denghang 0.84x, lang_ops 0.92x, lang_equality 0.95x, others about 1.0x. Reproducible regression: lang_inclusion_1722 0.42 -> 5.6 s.

| set | solver | formulas | solved | wrong | timeout | other | mean time [s] | mean time of solved [s] |
|---|---|---|---|---|---|---|---|---|
| automatark | red100 | 40 | 40 | 0 | 0 | 0 | 0.033 | 0.033 |
| automatark | red1000 | 40 | 40 | 0 | 0 | 0 | 0.046 | 0.046 |
| denghang | red100 | 40 | 40 | 0 | 0 | 0 | 0.058 | 0.058 |
| denghang | red1000 | 40 | 40 | 0 | 0 | 0 | 0.069 | 0.069 |
| full_str_int | red100 | 40 | 39 | 0 | 1 | 0 | 0.316 | 0.067 |
| full_str_int | red1000 | 40 | 39 | 0 | 1 | 0 | 0.316 | 0.067 |
| hornstr | red100 | 40 | 40 | 0 | 0 | 0 | 0.045 | 0.045 |
| hornstr | red1000 | 40 | 40 | 0 | 0 | 0 | 0.046 | 0.046 |
| kaluza | red100 | 40 | 40 | 0 | 0 | 0 | 0.027 | 0.027 |
| kaluza | red1000 | 40 | 40 | 0 | 0 | 0 | 0.027 | 0.027 |
| kepler | red100 | 40 | 40 | 0 | 0 | 0 | 0.025 | 0.025 |
| kepler | red1000 | 40 | 40 | 0 | 0 | 0 | 0.025 | 0.025 |
| lang_equality | red100 | 1000 | 772 | 0 | 31 | 197 | 0.398 | 0.055 |
| lang_equality | red1000 | 1000 | 772 | 0 | 31 | 197 | 0.401 | 0.058 |
| lang_inclusion | red100 | 1000 | 754 | 0 | 18 | 228 | 0.242 | 0.057 |
| lang_inclusion | red1000 | 1000 | 754 | 0 | 18 | 228 | 0.242 | 0.057 |
| lang_ops | red100 | 400 | 389 | 0 | 11 | 0 | 0.489 | 0.220 |
| lang_ops | red1000 | 400 | 389 | 0 | 11 | 0 | 0.508 | 0.239 |
| leetcode | red100 | 40 | 40 | 0 | 0 | 0 | 0.025 | 0.025 |
| leetcode | red1000 | 40 | 40 | 0 | 0 | 0 | 0.025 | 0.025 |
| matching | red100 | 40 | 32 | 0 | 8 | 0 | 6.405 | 5.506 |
| matching | red1000 | 40 | 32 | 0 | 8 | 0 | 6.487 | 5.609 |
| memberships | red100 | 8815 | 8705 | 0 | 10 | 100 | 0.058 | 0.047 |
| memberships | red1000 | 8815 | 8704 | 0 | 11 | 100 | 0.067 | 0.055 |
| negated_predicates | red100 | 40 | 37 | 0 | 3 | 0 | 1.524 | 0.837 |
| negated_predicates | red1000 | 40 | 37 | 0 | 3 | 0 | 1.525 | 0.838 |
| norn | red100 | 40 | 40 | 0 | 0 | 0 | 0.027 | 0.027 |
| norn | red1000 | 40 | 40 | 0 | 0 | 0 | 0.027 | 0.027 |
| omark | red100 | 17 | 10 | 0 | 7 | 0 | 4.142 | 0.041 |
| omark | red1000 | 17 | 10 | 0 | 7 | 0 | 4.142 | 0.041 |
| pcp | red100 | 40 | 16 | 0 | 0 | 24 | 0.022 | 0.022 |
| pcp | red1000 | 40 | 16 | 0 | 0 | 24 | 0.022 | 0.022 |
| pyex | red100 | 40 | 40 | 0 | 0 | 0 | 0.268 | 0.268 |
| pyex | red1000 | 40 | 40 | 0 | 0 | 0 | 0.267 | 0.267 |
| random_mix | red100 | 300 | 78 | 0 | 220 | 2 | 7.971 | 2.366 |
| random_mix | red1000 | 300 | 79 | 0 | 219 | 2 | 7.962 | 2.428 |
| redos | red100 | 40 | 39 | 0 | 1 | 0 | 1.034 | 0.804 |
| redos | red1000 | 40 | 39 | 0 | 1 | 0 | 1.029 | 0.799 |
| rna | red100 | 40 | 40 | 0 | 0 | 0 | 0.080 | 0.080 |
| rna | red1000 | 40 | 40 | 0 | 0 | 0 | 0.083 | 0.083 |
| slent | red100 | 40 | 40 | 0 | 0 | 0 | 0.027 | 0.027 |
| slent | red1000 | 40 | 40 | 0 | 0 | 0 | 0.027 | 0.027 |
| slog | red100 | 40 | 40 | 0 | 0 | 0 | 0.122 | 0.122 |
| slog | red1000 | 40 | 40 | 0 | 0 | 0 | 0.125 | 0.125 |
| str_small_rw | red100 | 40 | 36 | 0 | 4 | 0 | 1.029 | 0.032 |
| str_small_rw | red1000 | 40 | 36 | 0 | 4 | 0 | 1.029 | 0.032 |
| stringfuzz | red100 | 40 | 40 | 0 | 0 | 0 | 0.029 | 0.029 |
| stringfuzz | red1000 | 40 | 40 | 0 | 0 | 0 | 0.039 | 0.039 |
| sygus_qgen | red100 | 40 | 40 | 0 | 0 | 0 | 0.022 | 0.022 |
| sygus_qgen | red1000 | 40 | 40 | 0 | 0 | 0 | 0.022 | 0.022 |
| transducer_plus | red100 | 40 | 13 | 0 | 22 | 5 | 6.074 | 1.004 |
| transducer_plus | red1000 | 40 | 13 | 0 | 22 | 5 | 6.079 | 1.018 |
| webapp | red100 | 40 | 39 | 0 | 0 | 1 | 0.206 | 0.200 |
| webapp | red1000 | 40 | 39 | 0 | 0 | 1 | 0.208 | 0.201 |
| woorpje | red100 | 40 | 40 | 0 | 0 | 0 | 0.177 | 0.177 |
| woorpje | red1000 | 40 | 40 | 0 | 0 | 0 | 0.178 | 0.178 |
| **total** | red100 | 12412 | 11519 | 0 | 336 | 557 | 0.364 | 0.093 |
| **total** | red1000 | 12412 | 11519 | 0 | 336 | 557 | 0.371 | 0.100 |

## RED_BOUND 1000 vs 250 (with INTERSECTION_RED_BOUND = 100), 40-minute run (2026-11-04)

Same sample (results/bound-big-sample.txt, 12412 formulas), all finished (the run was resumed twice after session restarts; the two runs of a formula still ran next to each other). red1000 = current state (variants/ibound100), red250 = RED_BOUND 250 in regex.cpp and memb_heuristics_procedures.cpp (variants/red250). Results: results/redbound250-1104.csv, comparison logs/redbound250-1104-compare.txt. Same outcomes except regex_7316 (timeout -> solved), 0 wrong, no regressions (largest slowdown 0.2 s, noise). Formulas solved by both: total 0.96x (1169.0 -> 1124.5 s), memberships 0.92x (477.7 -> 441.7 s), stringfuzz 0.75x, automatark 0.90x, webapp 0.93x, slog 0.94x, others 0.97-1.02x. Compared with RED_BOUND 100 (0.93x but lang_inclusion_1722 0.4 -> 5.6 s and random_mix_1041 solved -> timeout), 250 keeps most of the gain without the regressions.

| set | solver | formulas | solved | wrong | timeout | other | mean time [s] | mean time of solved [s] |
|---|---|---|---|---|---|---|---|---|
| automatark | red1000 | 40 | 40 | 0 | 0 | 0 | 0.047 | 0.047 |
| automatark | red250 | 40 | 40 | 0 | 0 | 0 | 0.042 | 0.042 |
| denghang | red1000 | 40 | 40 | 0 | 0 | 0 | 0.068 | 0.068 |
| denghang | red250 | 40 | 40 | 0 | 0 | 0 | 0.067 | 0.067 |
| full_str_int | red1000 | 40 | 39 | 0 | 1 | 0 | 0.316 | 0.068 |
| full_str_int | red250 | 40 | 39 | 0 | 1 | 0 | 0.317 | 0.068 |
| hornstr | red1000 | 40 | 40 | 0 | 0 | 0 | 0.047 | 0.047 |
| hornstr | red250 | 40 | 40 | 0 | 0 | 0 | 0.046 | 0.046 |
| kaluza | red1000 | 40 | 40 | 0 | 0 | 0 | 0.025 | 0.025 |
| kaluza | red250 | 40 | 40 | 0 | 0 | 0 | 0.025 | 0.025 |
| kepler | red1000 | 40 | 40 | 0 | 0 | 0 | 0.025 | 0.025 |
| kepler | red250 | 40 | 40 | 0 | 0 | 0 | 0.025 | 0.025 |
| lang_equality | red1000 | 1000 | 772 | 0 | 31 | 197 | 0.399 | 0.058 |
| lang_equality | red250 | 1000 | 772 | 0 | 31 | 197 | 0.398 | 0.056 |
| lang_inclusion | red1000 | 1000 | 754 | 0 | 18 | 228 | 0.243 | 0.058 |
| lang_inclusion | red250 | 1000 | 754 | 0 | 18 | 228 | 0.242 | 0.057 |
| lang_ops | red1000 | 400 | 389 | 0 | 11 | 0 | 0.507 | 0.239 |
| lang_ops | red250 | 400 | 389 | 0 | 11 | 0 | 0.504 | 0.236 |
| leetcode | red1000 | 40 | 40 | 0 | 0 | 0 | 0.025 | 0.025 |
| leetcode | red250 | 40 | 40 | 0 | 0 | 0 | 0.025 | 0.025 |
| matching | red1000 | 40 | 33 | 0 | 7 | 0 | 6.482 | 5.736 |
| matching | red250 | 40 | 33 | 0 | 7 | 0 | 6.428 | 5.671 |
| memberships | red1000 | 8815 | 8704 | 0 | 11 | 100 | 0.067 | 0.055 |
| memberships | red250 | 8815 | 8705 | 0 | 10 | 100 | 0.062 | 0.051 |
| negated_predicates | red1000 | 40 | 37 | 0 | 3 | 0 | 1.554 | 0.869 |
| negated_predicates | red250 | 40 | 37 | 0 | 3 | 0 | 1.541 | 0.855 |
| norn | red1000 | 40 | 40 | 0 | 0 | 0 | 0.028 | 0.028 |
| norn | red250 | 40 | 40 | 0 | 0 | 0 | 0.028 | 0.028 |
| omark | red1000 | 17 | 10 | 0 | 7 | 0 | 4.140 | 0.037 |
| omark | red250 | 17 | 10 | 0 | 7 | 0 | 4.140 | 0.038 |
| pcp | red1000 | 40 | 16 | 0 | 0 | 24 | 0.022 | 0.022 |
| pcp | red250 | 40 | 16 | 0 | 0 | 24 | 0.022 | 0.023 |
| pyex | red1000 | 40 | 40 | 0 | 0 | 0 | 0.270 | 0.270 |
| pyex | red250 | 40 | 40 | 0 | 0 | 0 | 0.269 | 0.269 |
| random_mix | red1000 | 300 | 79 | 0 | 219 | 2 | 7.957 | 2.416 |
| random_mix | red250 | 300 | 79 | 0 | 219 | 2 | 7.952 | 2.396 |
| redos | red1000 | 40 | 39 | 0 | 1 | 0 | 1.036 | 0.806 |
| redos | red250 | 40 | 39 | 0 | 1 | 0 | 1.042 | 0.812 |
| rna | red1000 | 40 | 40 | 0 | 0 | 0 | 0.084 | 0.084 |
| rna | red250 | 40 | 40 | 0 | 0 | 0 | 0.081 | 0.081 |
| slent | red1000 | 40 | 40 | 0 | 0 | 0 | 0.028 | 0.028 |
| slent | red250 | 40 | 40 | 0 | 0 | 0 | 0.029 | 0.029 |
| slog | red1000 | 40 | 40 | 0 | 0 | 0 | 0.124 | 0.124 |
| slog | red250 | 40 | 40 | 0 | 0 | 0 | 0.117 | 0.117 |
| str_small_rw | red1000 | 40 | 36 | 0 | 4 | 0 | 1.030 | 0.034 |
| str_small_rw | red250 | 40 | 36 | 0 | 4 | 0 | 1.030 | 0.033 |
| stringfuzz | red1000 | 40 | 40 | 0 | 0 | 0 | 0.039 | 0.039 |
| stringfuzz | red250 | 40 | 40 | 0 | 0 | 0 | 0.029 | 0.029 |
| sygus_qgen | red1000 | 40 | 40 | 0 | 0 | 0 | 0.023 | 0.023 |
| sygus_qgen | red250 | 40 | 40 | 0 | 0 | 0 | 0.022 | 0.022 |
| transducer_plus | red1000 | 40 | 13 | 0 | 22 | 5 | 6.079 | 1.030 |
| transducer_plus | red250 | 40 | 13 | 0 | 22 | 5 | 6.072 | 1.017 |
| webapp | red1000 | 40 | 39 | 0 | 0 | 1 | 0.213 | 0.210 |
| webapp | red250 | 40 | 39 | 0 | 0 | 1 | 0.200 | 0.197 |
| woorpje | red1000 | 40 | 40 | 0 | 0 | 0 | 0.179 | 0.179 |
| woorpje | red250 | 40 | 40 | 0 | 0 | 0 | 0.177 | 0.177 |
| **total** | red1000 | 12412 | 11520 | 0 | 335 | 557 | 0.371 | 0.101 |
| **total** | red250 | 12412 | 11521 | 0 | 334 | 557 | 0.366 | 0.098 |
