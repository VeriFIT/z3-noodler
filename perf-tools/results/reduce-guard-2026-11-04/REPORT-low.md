Formulas with a run of every solver: 3019; timeouts count as 30 s; common = the formulas solved by every solver.

## Totals: affected formulas (2011)

|         |   formulas |   solved |   wrong |   disagree |   timeout |   other |   time_s |   time_ratio |   common_s |   common_ratio |
|:--------|-----------:|---------:|--------:|-----------:|----------:|--------:|---------:|-------------:|-----------:|---------------:|
| current |   2.01e+03 | 1.99e+03 |      14 |          0 |         5 |       0 | 2.27e+03 |        1     |   1.74e+03 |          1     |
| qt-1    |   2.01e+03 | 1.83e+03 |      14 |          0 |       170 |       0 | 6.63e+03 |        2.92  |   1.45e+03 |          0.835 |
| qt-1e4  |   2.01e+03 | 1.99e+03 |      14 |          0 |         4 |       0 | 1.68e+03 |        0.741 |   1.19e+03 |          0.682 |
| qt-3e4  |   2.01e+03 | 1.99e+03 |      14 |          0 |         4 |       0 | 1.69e+03 |        0.745 |   1.22e+03 |          0.703 |
| qt-1e5  |   2.01e+03 | 1.99e+03 |      14 |          0 |         4 |       0 | 1.7e+03  |        0.748 |   1.23e+03 |          0.706 |

## Totals: control formulas (1008)

|         |   formulas |   solved |   wrong |   disagree |   timeout |   other |     time_s |   time_ratio |   common_s |   common_ratio |
|:--------|-----------:|---------:|--------:|-----------:|----------:|--------:|-----------:|-------------:|-----------:|---------------:|
| current |   1.01e+03 |      968 |       8 |          0 |         6 |      26 | 539        |        1     |        341 |          1     |
| qt-1    |   1.01e+03 |      947 |       8 |          0 |        27 |      26 |   1.28e+03 |        2.38  |        344 |          1.01  |
| qt-1e4  |   1.01e+03 |      974 |       8 |          0 |         0 |      26 | 464        |        0.862 |        334 |          0.979 |
| qt-3e4  |   1.01e+03 |      974 |       8 |          0 |         0 |      26 | 460        |        0.853 |        329 |          0.964 |
| qt-1e5  |   1.01e+03 |      974 |       8 |          0 |         0 |      26 | 465        |        0.864 |        335 |          0.98  |

## Time distribution [s] (all formulas, and the formulas solved by every solver)

|                 |   formulas |    total |   mean |   p50 |   p90 |   p95 |   p97 |   p98 |   p99 |   max |
|:----------------|-----------:|---------:|-------:|------:|------:|------:|------:|------:|------:|------:|
| all: current    |   3.02e+03 | 2.81e+03 |  0.929 | 0.094 | 1.62  |  4.69 |  7.6  | 12.5  |  19.1 |  30   |
| all: qt-1       |   3.02e+03 | 7.91e+03 |  2.62  | 0.032 | 6.14  | 30    | 30    | 30    |  30   |  30   |
| all: qt-1e4     |   3.02e+03 | 2.14e+03 |  0.71  | 0.04  | 0.928 |  3.1  |  6.97 | 11.7  |  18.3 |  30   |
| all: qt-3e4     |   3.02e+03 | 2.15e+03 |  0.712 | 0.044 | 0.929 |  3.1  |  7.04 | 11.9  |  18.2 |  30   |
| all: qt-1e5     |   3.02e+03 | 2.16e+03 |  0.716 | 0.049 | 0.936 |  3.09 |  7.25 | 11.9  |  17.9 |  30   |
| common: current |   2.76e+03 | 2.08e+03 |  0.753 | 0.086 | 1.26  |  4.31 |  6.27 |  9.26 |  15.9 |  28.1 |
| common: qt-1    |   2.76e+03 | 1.8e+03  |  0.65  | 0.031 | 0.384 |  4.08 |  7.33 | 11.2  |  14.6 |  29.3 |
| common: qt-1e4  |   2.76e+03 | 1.52e+03 |  0.55  | 0.038 | 0.21  |  2.46 |  5.87 |  8.9  |  13.8 |  29.8 |
| common: qt-3e4  |   2.76e+03 | 1.55e+03 |  0.562 | 0.041 | 0.219 |  2.46 |  6.08 |  9.04 |  14.3 |  29.4 |
| common: qt-1e5  |   2.76e+03 | 1.56e+03 |  0.565 | 0.046 | 0.23  |  2.54 |  5.77 |  9.02 |  14   |  29.6 |

## Per-formula time ratio to current (formulas solved by every solver, times below 0.01 s count as 0.01 s)

|        |   geometric_mean |     p1 |     p5 |   p50 |   p95 |   p99 |   faster_2x |   slower_2x |
|:-------|-----------------:|-------:|-------:|------:|------:|------:|------------:|------------:|
| qt-1   |            0.495 | 0.0198 | 0.085  | 0.595 |  1.39 |  9.93 |    1.24e+03 |          99 |
| qt-1e4 |            0.508 | 0.0199 | 0.0915 | 0.628 |  1.07 |  1.46 |    1.16e+03 |          25 |
| qt-3e4 |            0.529 | 0.0208 | 0.101  | 0.66  |  1.07 |  1.23 |    1.09e+03 |          25 |
| qt-1e5 |            0.56  | 0.0225 | 0.101  | 0.739 |  1.07 |  1.19 |  931        |          23 |

## Per set: solved / total time [s] / mean time [s] / 99th percentile of the time [s]

| set                |   formulas | current                    | qt-1                       | qt-1e4                     | qt-3e4                     | qt-1e5                     |
|:-------------------|-----------:|:---------------------------|:---------------------------|:---------------------------|:---------------------------|:---------------------------|
| automatark         |        459 | 458 / 289 / 0.629 / 11.26  | 459 / 21 / 0.046 / 0.17    | 459 / 25 / 0.054 / 0.18    | 459 / 27 / 0.059 / 0.19    | 459 / 31 / 0.067 / 0.21    |
| denghang           |        166 | 166 / 17 / 0.105 / 1.27    | 166 / 6 / 0.037 / 0.22     | 166 / 6 / 0.034 / 0.13     | 166 / 6 / 0.037 / 0.13     | 166 / 7 / 0.041 / 0.14     |
| ecma2020           |        142 | 141 / 48 / 0.340 / 3.72    | 141 / 21 / 0.148 / 2.59    | 141 / 22 / 0.153 / 2.59    | 141 / 22 / 0.154 / 2.58    | 141 / 22 / 0.157 / 2.58    |
| ecma2020_mixed_bmp |        203 | 191 / 1229 / 6.057 / 30.00 | 186 / 1263 / 6.221 / 30.00 | 191 / 1169 / 5.759 / 30.00 | 191 / 1174 / 5.785 / 30.00 | 191 / 1168 / 5.753 / 30.00 |
| full_str_int       |         40 | 40 / 2 / 0.051 / 0.23      | 40 / 2 / 0.051 / 0.23      | 40 / 2 / 0.052 / 0.24      | 40 / 2 / 0.052 / 0.23      | 40 / 2 / 0.052 / 0.24      |
| hornstr            |         43 | 43 / 2 / 0.037 / 0.14      | 43 / 2 / 0.050 / 0.30      | 43 / 2 / 0.038 / 0.15      | 43 / 2 / 0.038 / 0.15      | 43 / 2 / 0.038 / 0.15      |
| kaluza             |         32 | 32 / 1 / 0.017 / 0.05      | 32 / 1 / 0.018 / 0.05      | 32 / 1 / 0.018 / 0.05      | 32 / 1 / 0.018 / 0.05      | 32 / 1 / 0.017 / 0.05      |
| kepler             |         40 | 40 / 1 / 0.030 / 0.29      | 40 / 1 / 0.030 / 0.29      | 40 / 1 / 0.030 / 0.29      | 40 / 1 / 0.030 / 0.29      | 40 / 1 / 0.030 / 0.30      |
| leetcode           |         43 | 43 / 1 / 0.027 / 0.14      | 43 / 1 / 0.026 / 0.14      | 43 / 1 / 0.027 / 0.14      | 43 / 1 / 0.027 / 0.15      | 43 / 1 / 0.027 / 0.15      |
| matching           |         68 | 62 / 476 / 6.996 / 30.00   | 68 / 494 / 7.270 / 22.64   | 68 / 494 / 7.265 / 22.77   | 68 / 492 / 7.238 / 22.93   | 68 / 495 / 7.273 / 22.89   |
| negated_predicates |         41 | 41 / 69 / 1.689 / 23.02    | 41 / 67 / 1.636 / 22.48    | 41 / 68 / 1.648 / 22.73    | 41 / 65 / 1.587 / 21.94    | 41 / 68 / 1.662 / 22.51    |
| norn               |         40 | 40 / 1 / 0.019 / 0.02      | 40 / 1 / 0.021 / 0.06      | 40 / 1 / 0.019 / 0.02      | 40 / 1 / 0.019 / 0.02      | 40 / 1 / 0.019 / 0.02      |
| omark              |          2 | 2 / 0 / 0.019 / 0.02       | 2 / 0 / 0.019 / 0.02       | 2 / 0 / 0.019 / 0.02       | 2 / 0 / 0.019 / 0.02       | 2 / 0 / 0.019 / 0.02       |
| pcp                |         35 | 18 / 1 / 0.017 / 0.02      | 18 / 1 / 0.018 / 0.02      | 18 / 1 / 0.018 / 0.02      | 18 / 1 / 0.018 / 0.02      | 18 / 1 / 0.018 / 0.02      |
| pyex               |        120 | 120 / 115 / 0.957 / 2.42   | 16 / 3148 / 26.231 / 30.00 | 120 / 99 / 0.827 / 2.20    | 120 / 100 / 0.836 / 2.20   | 120 / 103 / 0.855 / 2.24   |
| redos              |         66 | 66 / 45 / 0.675 / 6.82     | 66 / 32 / 0.490 / 3.99     | 66 / 32 / 0.486 / 4.16     | 66 / 32 / 0.486 / 4.02     | 66 / 32 / 0.486 / 4.00     |
| regex              |        126 | 104 / 98 / 0.782 / 6.40    | 104 / 48 / 0.382 / 10.10   | 104 / 19 / 0.155 / 1.54    | 104 / 20 / 0.159 / 1.54    | 104 / 20 / 0.161 / 1.42    |
| rna                |         38 | 38 / 2 / 0.056 / 0.06      | 38 / 2 / 0.056 / 0.07      | 38 / 2 / 0.057 / 0.07      | 38 / 2 / 0.056 / 0.06      | 38 / 2 / 0.057 / 0.07      |
| slent              |         32 | 32 / 1 / 0.017 / 0.03      | 32 / 1 / 0.017 / 0.03      | 32 / 1 / 0.018 / 0.03      | 32 / 1 / 0.017 / 0.03      | 32 / 1 / 0.018 / 0.03      |
| slog               |         41 | 41 / 1 / 0.023 / 0.12      | 41 / 1 / 0.023 / 0.10      | 41 / 1 / 0.023 / 0.10      | 41 / 1 / 0.023 / 0.10      | 41 / 1 / 0.024 / 0.12      |
| snia               |         32 | 32 / 0 / 0.015 / 0.02      | 32 / 1 / 0.016 / 0.02      | 32 / 1 / 0.016 / 0.02      | 32 / 1 / 0.016 / 0.02      | 32 / 1 / 0.016 / 0.02      |
| str_small_rw       |         36 | 36 / 1 / 0.031 / 0.32      | 36 / 1 / 0.032 / 0.34      | 36 / 1 / 0.032 / 0.32      | 36 / 1 / 0.032 / 0.34      | 36 / 1 / 0.033 / 0.34      |
| stringfuzz         |        293 | 293 / 54 / 0.184 / 0.44    | 292 / 145 / 0.496 / 11.59  | 293 / 37 / 0.127 / 0.81    | 293 / 35 / 0.120 / 0.49    | 293 / 35 / 0.120 / 0.43    |
| sygus_qgen         |         38 | 38 / 1 / 0.018 / 0.02      | 38 / 1 / 0.017 / 0.02      | 38 / 1 / 0.018 / 0.02      | 38 / 1 / 0.018 / 0.02      | 38 / 1 / 0.018 / 0.02      |
| transducer_plus    |         12 | 12 / 11 / 0.950 / 3.40     | 12 / 12 / 0.970 / 3.56     | 12 / 11 / 0.954 / 3.44     | 12 / 12 / 0.970 / 3.56     | 12 / 12 / 0.961 / 3.49     |
| webapp             |         52 | 52 / 16 / 0.311 / 6.77     | 52 / 16 / 0.313 / 6.78     | 52 / 16 / 0.313 / 6.79     | 52 / 16 / 0.313 / 6.78     | 52 / 16 / 0.312 / 6.75     |
| woorpje            |         29 | 29 / 5 / 0.160 / 2.50      | 29 / 5 / 0.161 / 2.50      | 29 / 5 / 0.161 / 2.50      | 29 / 5 / 0.162 / 2.52      | 29 / 5 / 0.160 / 2.48      |
| zaligvinder        |        750 | 750 / 319 / 0.425 / 5.02   | 667 / 2616 / 3.488 / 30.00 | 750 / 126 / 0.168 / 1.70   | 750 / 128 / 0.171 / 1.71   | 750 / 134 / 0.179 / 1.75   |

## Changes against the baseline

### qt-1 vs current

Solved only by qt-1: 8, only by current: 194; more than 2× and 0.5 s faster: 206, slower: 261; time difference +5103 s.

Biggest slowdowns:

| formula | set | current [s] | qt-1 [s] |
|---|---|---|---|
| fd50330824b256c2fe70e629f0a969279b306da99aa4a92287a3b154.smt2 | pyex | 0.07 (solved) | timeout |
| 9ec5e41557719045bc1b54ba4e72840aac7184150e4be85ee5853ad4.smt2 | pyex | 0.09 (solved) | timeout |
| 10bb1a52bcafc4a50a907fdd8ec7c46bc78d4096fcb55f6543c4c675.smt2 | pyex | 0.10 (solved) | timeout |
| f507c1d2be88b7f29516267a2e9314c4f53b0b6a84151ee49406efdc.smt2 | pyex | 0.10 (solved) | timeout |
| b89212cc5d4c702efe00bf0961844e3061cfbf0c98f2b786bf42faa3.smt2 | pyex | 0.11 (solved) | timeout |
| 7ab9add0ffd71590962f9c3db693d487132597877202349329eccebe.smt2 | pyex | 0.11 (solved) | timeout |
| 13507e2f959090fd3f7375a6b07a178b58b07bc4a25266f3fc0a85a6.smt2 | zaligvinder | 0.12 (solved) | timeout |
| a5faa9428d91cb8f706e291808a31a48d37d89ba74f4f606022a269a.smt2 | pyex | 0.12 (solved) | timeout |
| d6f0bcff953132c87111467aaf2635bd18a82b90acc43c982a8a78e5.smt2 | pyex | 0.14 (solved) | timeout |
| befc3ecb132ae95740557b87c2479314bddab1d0550e3582c61d44ec.smt2 | pyex | 0.14 (solved) | timeout |
| 416ea0358d86cb47a62a8e6b8bf9662418cf4f6544ffe69d5263f5c4.smt2 | pyex | 0.16 (solved) | timeout |
| bd2c3ed0b7151969acf1e3ecd5bad6283d7a26096e123a3f52b4795e.smt2 | zaligvinder | 0.16 (solved) | timeout |

Biggest speedups:

| formula | set | current [s] | qt-1 [s] |
|---|---|---|---|
| instance09716.smt2 | automatark | timeout | 0.07 (solved) |
| instance12333.smt2 | automatark | 28.07 (solved) | 0.07 (solved) |
| random_mix_3224.smt2 | ecma2020_mixed_bmp | 26.87 (solved) | 9.27 (solved) |
| random_mix_3126.smt2 | ecma2020_mixed_bmp | 22.36 (solved) | 6.05 (solved) |
| instance4458.smt2 | zaligvinder | 16.23 (solved) | 0.05 (solved) |
| instance11999.smt2 | automatark | 15.78 (solved) | 0.12 (solved) |
| instance06476.smt2 | automatark | 15.09 (solved) | 0.06 (solved) |
| instance8851.smt2 | zaligvinder | 14.66 (solved) | 0.06 (solved) |
| lang_equality_3780.smt2 | ecma2020_mixed_bmp | timeout | 16.57 (solved) |
| wildcard-matching-regex-24.smt2 | matching | timeout | 18.15 (solved) |
| wildcard-matching-regex-16.smt2 | matching | timeout | 18.51 (solved) |
| wildcard-matching-regex-52.smt2 | matching | timeout | 18.88 (solved) |

### qt-1e4 vs current

Solved only by qt-1e4: 10, only by current: 3; more than 2× and 0.5 s faster: 205, slower: 27; time difference -663 s.

Biggest slowdowns:

| formula | set | current [s] | qt-1e4 [s] |
|---|---|---|---|
| random_mix_0139.smt2 | ecma2020_mixed_bmp | 12.02 (solved) | timeout |
| random_mix_0146.smt2 | ecma2020_mixed_bmp | 18.09 (solved) | timeout |
| wildcard-matching-regex-02.smt2 | matching | 19.10 (solved) | 29.82 (solved) |
| random_mix_3484.smt2 | ecma2020_mixed_bmp | 19.05 (solved) | 29.42 (solved) |
| wildcard-matching-regex-54.smt2 | matching | 5.70 (solved) | 13.75 (solved) |
| wildcard-matching-regex-18.smt2 | matching | 5.46 (solved) | 13.37 (solved) |
| wildcard-matching-regex-62.smt2 | matching | 5.47 (solved) | 13.31 (solved) |
| wildcard-matching-regex-50.smt2 | matching | 5.79 (solved) | 13.63 (solved) |
| random_mix_3194.smt2 | ecma2020_mixed_bmp | 22.20 (solved) | timeout |
| wildcard-matching-regex-14.smt2 | matching | 5.60 (solved) | 13.04 (solved) |
| wildcard-matching-regex-82.smt2 | matching | 5.31 (solved) | 12.47 (solved) |
| wildcard-matching-regex-74.smt2 | matching | 5.26 (solved) | 12.25 (solved) |

Biggest speedups:

| formula | set | current [s] | qt-1e4 [s] |
|---|---|---|---|
| instance09716.smt2 | automatark | timeout | 0.07 (solved) |
| instance12333.smt2 | automatark | 28.07 (solved) | 0.07 (solved) |
| random_mix_3644.smt2 | ecma2020_mixed_bmp | timeout | 9.65 (solved) |
| instance4458.smt2 | zaligvinder | 16.23 (solved) | 0.05 (solved) |
| instance11999.smt2 | automatark | 15.78 (solved) | 0.12 (solved) |
| instance06476.smt2 | automatark | 15.09 (solved) | 0.07 (solved) |
| instance8851.smt2 | zaligvinder | 14.66 (solved) | 0.07 (solved) |
| lang_equality_3780.smt2 | ecma2020_mixed_bmp | timeout | 16.52 (solved) |
| wildcard-matching-regex-24.smt2 | matching | timeout | 18.25 (solved) |
| wildcard-matching-regex-16.smt2 | matching | timeout | 18.30 (solved) |
| wildcard-matching-regex-52.smt2 | matching | timeout | 18.88 (solved) |
| wildcard-matching-regex-56.smt2 | matching | timeout | 18.96 (solved) |

### qt-3e4 vs current

Solved only by qt-3e4: 10, only by current: 3; more than 2× and 0.5 s faster: 200, slower: 27; time difference -657 s.

Biggest slowdowns:

| formula | set | current [s] | qt-3e4 [s] |
|---|---|---|---|
| random_mix_0139.smt2 | ecma2020_mixed_bmp | 12.02 (solved) | timeout |
| random_mix_3484.smt2 | ecma2020_mixed_bmp | 19.05 (solved) | timeout |
| wildcard-matching-regex-02.smt2 | matching | 19.10 (solved) | 29.35 (solved) |
| wildcard-matching-regex-54.smt2 | matching | 5.70 (solved) | 13.80 (solved) |
| wildcard-matching-regex-18.smt2 | matching | 5.46 (solved) | 13.56 (solved) |
| wildcard-matching-regex-50.smt2 | matching | 5.79 (solved) | 13.66 (solved) |
| random_mix_3194.smt2 | ecma2020_mixed_bmp | 22.20 (solved) | timeout |
| wildcard-matching-regex-62.smt2 | matching | 5.47 (solved) | 13.24 (solved) |
| random_mix_0146.smt2 | ecma2020_mixed_bmp | 18.09 (solved) | 25.70 (solved) |
| random_mix_1509.smt2 | ecma2020_mixed_bmp | 6.68 (solved) | 14.15 (solved) |
| wildcard-matching-regex-14.smt2 | matching | 5.60 (solved) | 13.03 (solved) |
| wildcard-matching-regex-82.smt2 | matching | 5.31 (solved) | 12.47 (solved) |

Biggest speedups:

| formula | set | current [s] | qt-3e4 [s] |
|---|---|---|---|
| instance09716.smt2 | automatark | timeout | 0.08 (solved) |
| instance12333.smt2 | automatark | 28.07 (solved) | 0.08 (solved) |
| random_mix_0840.smt2 | ecma2020_mixed_bmp | timeout | 5.70 (solved) |
| random_mix_3644.smt2 | ecma2020_mixed_bmp | timeout | 9.67 (solved) |
| instance4458.smt2 | zaligvinder | 16.23 (solved) | 0.06 (solved) |
| instance11999.smt2 | automatark | 15.78 (solved) | 0.12 (solved) |
| instance06476.smt2 | automatark | 15.09 (solved) | 0.08 (solved) |
| instance8851.smt2 | zaligvinder | 14.66 (solved) | 0.07 (solved) |
| lang_equality_3780.smt2 | ecma2020_mixed_bmp | timeout | 16.46 (solved) |
| wildcard-matching-regex-24.smt2 | matching | timeout | 18.06 (solved) |
| wildcard-matching-regex-16.smt2 | matching | timeout | 18.50 (solved) |
| wildcard-matching-regex-56.smt2 | matching | timeout | 18.80 (solved) |

### qt-1e5 vs current

Solved only by qt-1e5: 9, only by current: 2; more than 2× and 0.5 s faster: 198, slower: 23; time difference -644 s.

Biggest slowdowns:

| formula | set | current [s] | qt-1e5 [s] |
|---|---|---|---|
| random_mix_0146.smt2 | ecma2020_mixed_bmp | 18.09 (solved) | timeout |
| wildcard-matching-regex-02.smt2 | matching | 19.10 (solved) | 29.62 (solved) |
| random_mix_0836.smt2 | ecma2020_mixed_bmp | 19.63 (solved) | timeout |
| wildcard-matching-regex-54.smt2 | matching | 5.70 (solved) | 13.88 (solved) |
| wildcard-matching-regex-18.smt2 | matching | 5.46 (solved) | 13.46 (solved) |
| wildcard-matching-regex-62.smt2 | matching | 5.47 (solved) | 13.39 (solved) |
| wildcard-matching-regex-50.smt2 | matching | 5.79 (solved) | 13.51 (solved) |
| wildcard-matching-regex-14.smt2 | matching | 5.60 (solved) | 13.02 (solved) |
| wildcard-matching-regex-82.smt2 | matching | 5.31 (solved) | 12.49 (solved) |
| wildcard-matching-regex-74.smt2 | matching | 5.26 (solved) | 12.28 (solved) |
| wildcard-matching-regex-34.smt2 | matching | 4.76 (solved) | 11.48 (solved) |
| wildcard-matching-regex-10.smt2 | matching | 5.16 (solved) | 11.86 (solved) |

Biggest speedups:

| formula | set | current [s] | qt-1e5 [s] |
|---|---|---|---|
| instance09716.smt2 | automatark | timeout | 0.07 (solved) |
| instance12333.smt2 | automatark | 28.07 (solved) | 0.08 (solved) |
| random_mix_3644.smt2 | ecma2020_mixed_bmp | timeout | 10.03 (solved) |
| instance4458.smt2 | zaligvinder | 16.23 (solved) | 0.06 (solved) |
| instance11999.smt2 | automatark | 15.78 (solved) | 0.12 (solved) |
| instance06476.smt2 | automatark | 15.09 (solved) | 0.09 (solved) |
| instance8851.smt2 | zaligvinder | 14.66 (solved) | 0.09 (solved) |
| lang_equality_3780.smt2 | ecma2020_mixed_bmp | timeout | 16.61 (solved) |
| wildcard-matching-regex-24.smt2 | matching | timeout | 18.31 (solved) |
| wildcard-matching-regex-16.smt2 | matching | timeout | 18.53 (solved) |
| wildcard-matching-regex-56.smt2 | matching | timeout | 18.88 (solved) |
| wildcard-matching-regex-52.smt2 | matching | timeout | 18.97 (solved) |

