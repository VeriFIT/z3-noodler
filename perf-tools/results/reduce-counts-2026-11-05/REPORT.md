2478 formulas with a run of every solver; timeouts count as the timeout; common = the formulas solved by every solver.

## Totals

|     |   formulas |   solved |   wrong |   disagree |   timeout |   unknown |   failed |   total time [s] |   common time [s] |   total / baseline |   common / baseline |
|:----|-----------:|---------:|--------:|-----------:|----------:|----------:|---------:|-----------------:|------------------:|-------------------:|--------------------:|
| old |       2478 |     2293 |       0 |          0 |       107 |        62 |       16 |             4531 |              1212 |              1     |               1     |
| new |       2478 |     2297 |       0 |          0 |       103 |        62 |       16 |             4585 |              1244 |              1.012 |               1.027 |

## Per set

| set                |   formulas |   old solved |   old time [s] |   new solved |   new time [s] |
|:-------------------|-----------:|-------------:|---------------:|-------------:|---------------:|
| automatark         |        100 |          100 |          3.695 |          100 |          3.311 |
| denghang           |        100 |          100 |          9.448 |          100 |          4.987 |
| ecma2020           |        100 |          100 |          4.087 |          100 |          3.452 |
| ecma2020_mixed_bmp |        100 |           68 |        877.6   |           68 |        875.6   |
| full_str_int       |        100 |          100 |          7.999 |          100 |          7.89  |
| hornstr            |        100 |          100 |          5.031 |          100 |          5.104 |
| kaluza             |        100 |          100 |          6.155 |          100 |          6.207 |
| kepler             |        100 |          100 |          3.222 |          100 |          3.241 |
| leetcode           |        100 |          100 |          2.878 |          100 |          2.891 |
| matching           |        100 |           87 |        991.5   |           91 |       1054     |
| negated_predicates |        100 |           95 |        319.6   |           95 |        320.4   |
| norn               |        100 |          100 |          2.708 |          100 |          2.635 |
| omark              |         17 |           10 |        210.4   |           10 |        210.4   |
| pcp                |        100 |           46 |          2.436 |           46 |          2.433 |
| pyex               |        100 |          100 |         34.12  |          100 |         34     |
| redos              |        100 |          100 |         80.29  |          100 |         78.21  |
| rna                |        100 |          100 |          8.217 |          100 |          8.224 |
| slent              |        100 |          100 |         15.55  |          100 |         15.64  |
| slog               |        100 |          100 |          2.742 |          100 |          2.76  |
| snia               |         70 |           70 |          1.474 |           70 |          1.454 |
| str_small_rw       |        100 |           97 |         99.09  |           97 |         99.11  |
| stringfuzz         |        100 |          100 |          9.471 |          100 |          8.978 |
| sygus_qgen         |        100 |          100 |          2.447 |          100 |          2.452 |
| transducer_plus    |         91 |           28 |       1649     |           28 |       1649     |
| webapp             |        100 |           95 |         38.58  |           95 |         38.58  |
| woorpje            |        100 |           97 |        143     |           97 |        143.4   |

## new against old

Changed outcomes:

| old     | new     |   formulas |
|:--------|:--------|-----------:|
| solved  | timeout |          3 |
| timeout | solved  |          7 |

|                                     |       old |       new |   ratio |
|:------------------------------------|----------:|----------:|--------:|
| all: total [s]                      | 4531      | 4585      |  1.012  |
| all: mean [s]                       |    1.828  |    1.85   |  1.012  |
| all: 50th percentile [s]            |    0.026  |    0.026  |  1      |
| all: 90th percentile [s]            |    2.263  |    1.423  |  0.6288 |
| all: 95th percentile [s]            |   16.14   |   19.64   |  1.217  |
| all: 99th percentile [s]            |   30      |   30      |  1      |
| solved by both: total [s]           | 1212      | 1244      |  1.027  |
| solved by both: mean [s]            |    0.5291 |    0.5433 |  1.027  |
| solved by both: 50th percentile [s] |    0.025  |    0.025  |  1      |
| solved by both: 90th percentile [s] |    0.3035 |    0.2481 |  0.8175 |
| solved by both: 95th percentile [s] |    3.066  |    2.435  |  0.7942 |
| solved by both: 99th percentile [s] |   10.77   |   16.37   |  1.52   |

- geometric mean of the per-formula time ratio (solved by both): 0.9649
- formulas more than 2× and 0.5 s faster: 19
- formulas more than 2× and 0.5 s slower: 20

Biggest slowdowns:

| formula                         | set      |   old [s] | old outcome   |   new [s] | new outcome   |
|:--------------------------------|:---------|----------:|:--------------|----------:|:--------------|
| wildcard-matching-regex-31.smt2 | matching |      3.92 | solved        |     30.00 | timeout       |
| sub-find-unsat-3.smt2           | matching |     12.80 | solved        |     30.00 | timeout       |
| wildcard-matching-regex-66.smt2 | matching |      8.58 | solved        |     20.63 | solved        |
| wildcard-matching-regex-78.smt2 | matching |      8.47 | solved        |     20.30 | solved        |
| wildcard-matching-regex-54.smt2 | matching |      8.52 | solved        |     20.26 | solved        |
| wildcard-matching-regex-18.smt2 | matching |      7.90 | solved        |     19.37 | solved        |
| wildcard-matching-regex-42.smt2 | matching |      8.16 | solved        |     19.62 | solved        |
| wildcard-matching-regex-46.smt2 | matching |      8.38 | solved        |     19.77 | solved        |
| wildcard-matching-regex-70.smt2 | matching |      8.27 | solved        |     19.01 | solved        |
| wildcard-matching-regex-74.smt2 | matching |      8.03 | solved        |     18.58 | solved        |
| wildcard-matching-regex-82.smt2 | matching |      8.02 | solved        |     18.21 | solved        |
| wildcard-matching-regex-10.smt2 | matching |      7.68 | solved        |     17.50 | solved        |

Biggest speedups:

| formula                          | set      |   old [s] | old outcome   |   new [s] | new outcome   |
|:---------------------------------|:---------|----------:|:--------------|----------:|:--------------|
| wildcard-matching-regex-100.smt2 | matching |     23.46 | solved        |      0.29 | solved        |
| wildcard-matching-regex-03.smt2  | matching |     21.94 | solved        |      2.44 | solved        |
| wildcard-matching-regex-112.smt2 | matching |     12.79 | solved        |      0.20 | solved        |
| wildcard-matching-regex-109.smt2 | matching |     10.08 | solved        |      0.30 | solved        |
| wildcard-matching-regex-127.smt2 | matching |      9.62 | solved        |      0.14 | solved        |
| wildcard-matching-regex-130.smt2 | matching |      8.59 | solved        |      0.14 | solved        |
| wildcard-matching-regex-107.smt2 | matching |      7.54 | solved        |      0.13 | solved        |
| wildcard-matching-regex-120.smt2 | matching |      7.36 | solved        |      1.80 | solved        |
| wildcard-matching-regex-111.smt2 | matching |      4.13 | solved        |      0.07 | solved        |
| wildcard-matching-regex-28.smt2  | matching |     30.00 | timeout       |     25.96 | solved        |
| wildcard-matching-regex-126.smt2 | matching |      4.06 | solved        |      0.09 | solved        |
| wildcard-matching-regex-52.smt2  | matching |     30.00 | timeout       |     26.10 | solved        |
