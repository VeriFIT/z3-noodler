Formulas with a run of every solver: 239797; timeouts count as 30 s; common = the formulas solved by every solver.

## current vs qt-1e5

|                                                      |      current |       qt-1e5 |    ratio |
|:-----------------------------------------------------|-------------:|-------------:|---------:|
| solved                                               |    2.361e+05 |    2.361e+05 |   1      |
| timeout                                              | 1945         | 1918         |   0.9861 |
| other (unknown, error, memory)                       | 1157         | 1157         |   1      |
| wrong                                                |  603         |  603         |   1      |
| disagree                                             |    0         |    0         | nan      |
| solved only by this one                              |   10         |   37         |   3.7    |
| total time [s]                                       |    8.417e+04 |    8.251e+04 |   0.9802 |
| mean [s]                                             |    0.351     |    0.3441    |   0.9802 |
| 50th percentile [s]                                  |    0.017     |    0.017     |   1      |
| 90th percentile [s]                                  |    0.168     |    0.161     |   0.9583 |
| 95th percentile [s]                                  |    0.292     |    0.274     |   0.9384 |
| 97th percentile [s]                                  |    0.538     |    0.496     |   0.9219 |
| 98th percentile [s]                                  |    0.87      |    0.788     |   0.9057 |
| 99th percentile [s]                                  |    8.45      |    8.042     |   0.9517 |
| 99.5th percentile [s]                                |   30         |   30         |   1      |
| 99.9th percentile [s]                                |   30         |   30         |   1      |
| max [s]                                              |   30         |   30         |   1      |
| total time of the formulas solved by both [s]        |    2.522e+04 |    2.388e+04 |   0.9469 |
| mean of the formulas solved by both [s]              |    0.1068    |    0.1012    |   0.9469 |
| 50th percentile of the formulas solved by both [s]   |    0.017     |    0.017     |   1      |
| 90th percentile of the formulas solved by both [s]   |    0.157     |    0.149     |   0.949  |
| 95th percentile of the formulas solved by both [s]   |    0.248     |    0.242     |   0.9758 |
| 97th percentile of the formulas solved by both [s]   |    0.397     |    0.3746    |   0.9435 |
| 98th percentile of the formulas solved by both [s]   |    0.582     |    0.543     |   0.933  |
| 99th percentile of the formulas solved by both [s]   |    1.063     |    0.889     |   0.8363 |
| 99.5th percentile of the formulas solved by both [s] |    2.513     |    2.177     |   0.8661 |
| 99.9th percentile of the formulas solved by both [s] |   15.77      |   14.25      |   0.904  |
| formulas over 1 s                                    | 4433         | 4096         |   0.924  |
| formulas over 10 s (timeouts included)               | 2354         | 2341         |   0.9945 |

|                                                                                                   |    value |
|:--------------------------------------------------------------------------------------------------|---------:|
| geometric mean of the per-formula time ratio (solved by both, times below 0.01 s count as 0.01 s) |   0.9923 |
| formulas more than 2× and 0.5 s faster                                                            | 470      |
| formulas more than 2× and 0.5 s slower                                                            |  54      |
| formulas more than 1 s faster                                                                     | 350      |
| formulas more than 1 s slower                                                                     |  74      |

## Totals: all formulas (239797)

|         |   formulas |   solved |   wrong |   disagree |   timeout |    other |   time_s |   time_ratio |   common_s |   common_ratio |
|:--------|-----------:|---------:|--------:|-----------:|----------:|---------:|---------:|-------------:|-----------:|---------------:|
| current |    2.4e+05 | 2.36e+05 |     603 |          0 |  1.94e+03 | 1.16e+03 | 8.42e+04 |         1    |   2.52e+04 |          1     |
| qt-1e5  |    2.4e+05 | 2.36e+05 |     603 |          0 |  1.92e+03 | 1.16e+03 | 8.25e+04 |         0.98 |   2.39e+04 |          0.947 |

## Time distribution [s] (all formulas, and the formulas solved by every solver)

|                 |   formulas |    total |   mean |   p50 |   p90 |   p95 |   p97 |   p98 |   p99 |   max |
|:----------------|-----------:|---------:|-------:|------:|------:|------:|------:|------:|------:|------:|
| all: current    |   2.4e+05  | 8.42e+04 |  0.351 | 0.017 | 0.168 | 0.292 | 0.538 | 0.87  | 8.45  |  30   |
| all: qt-1e5     |   2.4e+05  | 8.25e+04 |  0.344 | 0.017 | 0.161 | 0.274 | 0.496 | 0.788 | 8.04  |  30   |
| common: current |   2.36e+05 | 2.52e+04 |  0.107 | 0.017 | 0.157 | 0.248 | 0.397 | 0.582 | 1.06  |  30   |
| common: qt-1e5  |   2.36e+05 | 2.39e+04 |  0.101 | 0.017 | 0.149 | 0.242 | 0.375 | 0.543 | 0.889 |  29.9 |

## Per-formula time ratio to current (formulas solved by every solver, times below 0.01 s count as 0.01 s)

|        |   geometric_mean |    p1 |    p5 |   p50 |   p95 |   p99 |   faster_2x |   slower_2x |
|:-------|-----------------:|------:|------:|------:|------:|------:|------------:|------------:|
| qt-1e5 |            0.992 | 0.506 | 0.933 |     1 |  1.07 |  1.13 |    2.33e+03 |          55 |

## Per set: solved / total time [s] / mean time [s] / 99th percentile of the time [s]

| set                |   formulas | current                       | qt-1e5                        |
|:-------------------|-----------:|:------------------------------|:------------------------------|
| automatark         |      15995 | 15988 / 1139 / 0.071 / 0.52   | 15989 / 601 / 0.038 / 0.10    |
| denghang           |        999 | 998 / 98 / 0.099 / 0.69       | 999 / 37 / 0.037 / 0.10       |
| ecma2020           |       8815 | 8707 / 583 / 0.066 / 0.49     | 8708 / 464 / 0.053 / 0.19     |
| ecma2020_mixed_bmp |       4000 | 2479 / 36682 / 9.170 / 30.00  | 2480 / 36666 / 9.166 / 30.00  |
| full_str_int       |      16968 | 16913 / 2511 / 0.148 / 0.63   | 16912 / 2526 / 0.149 / 0.64   |
| hornstr            |        552 | 552 / 21 / 0.039 / 0.15       | 552 / 22 / 0.039 / 0.17       |
| kaluza             |      19465 | 19439 / 1503 / 0.077 / 0.20   | 19439 / 1507 / 0.077 / 0.21   |
| kepler             |        587 | 584 / 107 / 0.182 / 0.41      | 584 / 107 / 0.183 / 0.42      |
| leetcode           |       2652 | 2651 / 90 / 0.034 / 0.10      | 2651 / 91 / 0.034 / 0.10      |
| matching           |        246 | 204 / 2313 / 9.403 / 30.00    | 224 / 2173 / 8.834 / 30.00    |
| negated_predicates |        450 | 432 / 1203 / 2.672 / 30.00    | 432 / 1207 / 2.683 / 30.00    |
| norn               |       1027 | 1027 / 20 / 0.019 / 0.03      | 1027 / 20 / 0.020 / 0.03      |
| omark              |         17 | 10 / 210 / 12.372 / 30.00     | 10 / 210 / 12.370 / 30.00     |
| pcp                |       1000 | 500 / 18 / 0.018 / 0.02       | 500 / 18 / 0.018 / 0.02       |
| pyex               |      23845 | 23797 / 5828 / 0.244 / 1.02   | 23797 / 5839 / 0.245 / 0.98   |
| redos              |       3287 | 3283 / 2146 / 0.653 / 6.23    | 3285 / 2101 / 0.639 / 6.14    |
| regex              |       2172 | 1567 / 351 / 0.162 / 2.43     | 1568 / 159 / 0.073 / 0.42     |
| rna                |       1000 | 1000 / 57 / 0.057 / 0.07      | 1000 / 57 / 0.057 / 0.07      |
| slent              |       1128 | 1126 / 106 / 0.094 / 0.36     | 1126 / 107 / 0.095 / 0.36     |
| slog               |       1976 | 1976 / 71 / 0.036 / 0.42      | 1976 / 72 / 0.036 / 0.42      |
| snia               |         37 | 37 / 1 / 0.016 / 0.03         | 37 / 1 / 0.016 / 0.02         |
| str_small_rw       |       1880 | 1823 / 1757 / 0.934 / 30.00   | 1823 / 1758 / 0.935 / 30.00   |
| stringfuzz         |      11618 | 11618 / 337 / 0.029 / 0.22    | 11618 / 297 / 0.026 / 0.11    |
| sygus_qgen         |        343 | 343 / 6 / 0.018 / 0.02        | 343 / 6 / 0.018 / 0.02        |
| transducer_plus    |         91 | 28 / 1621 / 17.817 / 30.00    | 28 / 1621 / 17.818 / 30.00    |
| webapp             |        681 | 669 / 165 / 0.242 / 2.64      | 669 / 165 / 0.243 / 2.63      |
| woorpje            |        809 | 779 / 1077 / 1.331 / 30.00    | 779 / 1077 / 1.331 / 30.00    |
| zaligvinder        |     118157 | 117562 / 24152 / 0.204 / 0.96 | 117563 / 23597 / 0.200 / 0.86 |

## Changes against the baseline

### qt-1e5 vs current

Solved only by qt-1e5: 37, only by current: 10; more than 2× and 0.5 s faster: 470, slower: 54; time difference -1666 s.

Biggest slowdowns:

| formula | set | current [s] | qt-1e5 [s] |
|---|---|---|---|
| lang_inclusion_0092.smt2 | ecma2020_mixed_bmp | 0.85 (solved) | timeout |
| notsubset_8_8.smt2 | regex | 5.36 (solved) | timeout |
| random_mix_3208.smt2 | ecma2020_mixed_bmp | 7.43 (solved) | timeout |
| random_mix_3418.smt2 | ecma2020_mixed_bmp | 8.89 (solved) | timeout |
| lang_ops_3444.smt2 | ecma2020_mixed_bmp | 11.92 (solved) | timeout |
| random_mix_0508.smt2 | ecma2020_mixed_bmp | 13.00 (solved) | timeout |
| wildcard-matching-regex-04.smt2 | matching | 15.72 (solved) | timeout |
| random_mix_0146.smt2 | ecma2020_mixed_bmp | 18.12 (solved) | timeout |
| random_mix_0836.smt2 | ecma2020_mixed_bmp | 19.83 (solved) | timeout |
| random_mix_3119.smt2 | ecma2020_mixed_bmp | 11.32 (solved) | 19.69 (solved) |
| wildcard-matching-regex-22.smt2 | matching | 5.71 (solved) | 14.03 (solved) |
| wildcard-matching-regex-66.smt2 | matching | 5.79 (solved) | 13.82 (solved) |

Biggest speedups:

| formula | set | current [s] | qt-1e5 [s] |
|---|---|---|---|
| instance09716.smt2 | automatark | timeout | 0.08 (solved) |
| instance9602.smt2 | zaligvinder | timeout | 0.08 (solved) |
| instance37.smt2 | denghang | timeout | 0.16 (solved) |
| membership_800.smt2 | regex | timeout | 0.49 (solved) |
| instance9529.smt2 | zaligvinder | 28.44 (solved) | 0.09 (solved) |
| instance12333.smt2 | automatark | 28.28 (solved) | 0.09 (solved) |
| instance14223.smt2 | automatark | 23.62 (solved) | 3.00 (solved) |
| instance6267.smt2 | zaligvinder | 23.43 (solved) | 2.92 (solved) |
| inter_30_60_90.smt2 | regex | timeout | 9.58 (solved) |
| instance15752.smt2 | automatark | 22.92 (solved) | 2.82 (solved) |
| random_mix_3644.smt2 | ecma2020_mixed_bmp | timeout | 9.95 (solved) |
| instance1371.smt2 | zaligvinder | 22.71 (solved) | 2.90 (solved) |

