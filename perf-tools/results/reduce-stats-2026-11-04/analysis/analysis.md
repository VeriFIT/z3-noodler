# Cost of mata::nfa::reduce

Collections: results/reduce-stats-2026-11-04/c

## Overview

239862 formulas, 35929078 calls, 3515140 distinct calls (same formula, site, properties and result), 1529 censored.

| set                |   formulas |   timeouts |    seconds |   reduce_s |      calls |   reduce_share |
|:-------------------|-----------:|-----------:|-----------:|-----------:|-----------:|---------------:|
| redos              |   3.29e+03 |  925       |   3.04e+04 |   2.91e+04 |   6.95e+04 |        0.957   |
| ecma2020_mixed_bmp |   4e+03    |    1.1e+03 |   3.76e+04 |   1.32e+04 |   8.41e+06 |        0.352   |
| zaligvinder        |   1.18e+05 |  526       |   2.51e+04 |   5.79e+03 |   1.27e+07 |        0.231   |
| matching           | 246        |   90       |   3.56e+03 |   2.77e+03 | 382        |        0.779   |
| pyex               |   2.38e+04 |   50       |   6.25e+03 |   1.12e+03 |   2.81e+06 |        0.179   |
| automatark         |   1.6e+04  |    7       |   1.34e+03 | 951        |   2.22e+05 |        0.71    |
| transducer_plus    |  91        |   51       |   1.63e+03 | 555        |   3.72e+04 |        0.342   |
| kaluza             |   1.95e+04 |   26       |   1.56e+03 | 513        |   5.99e+05 |        0.33    |
| regex              |   2.17e+03 |    4       | 528        | 458        |   6.94e+04 |        0.867   |
| ecma2020           |   8.82e+03 |    5       | 614        | 300        |   1.37e+05 |        0.488   |
| woorpje            | 809        |   30       |   1.09e+03 | 267        |   5.94e+05 |        0.245   |
| full_str_int       |   1.7e+04  |   47       |   2.62e+03 | 202        |   1.67e+06 |        0.0772  |
| omark              |  17        |    7       | 210        | 154        |   1.64e+05 |        0.734   |
| stringfuzz         |   1.16e+04 |    0       | 426        | 153        |   1.19e+06 |        0.36    |
| denghang           | 999        |    2       | 132        | 107        |   1.8e+04  |        0.812   |
| negated_predicates | 450        |   18       |   1.31e+03 | 103        |   4.12e+06 |        0.0785  |
| webapp             | 681        |    2       | 171        |  88.2      |   5.54e+04 |        0.516   |
| str_small_rw       |   1.88e+03 |   55       |   1.77e+03 |  61.8      |   2.72e+06 |        0.0349  |
| slent              |   1.13e+03 |    2       | 110        |  57.1      |   1.48e+05 |        0.517   |
| slog               |   1.98e+03 |    0       |  76.7      |  34.4      |   1.16e+04 |        0.449   |
| rna                |   1e+03    |    0       |  61.1      |  34.3      |   6.5e+03  |        0.561   |
| hornstr            | 552        |    0       |  26.1      |  11.4      |   1.21e+05 |        0.438   |
| leetcode           |   2.65e+03 |    1       |  97        |   2.63     |   4.26e+04 |        0.0271  |
| norn               |   1.03e+03 |    0       |  22.4      |   2.05     |   2.43e+04 |        0.0915  |
| sygus_qgen         | 343        |    0       |   6.76     |   0.654    |   3.52e+03 |        0.0968  |
| pcp                |   1e+03    |    0       |  19.5      |   0.327    |   5e+03    |        0.0168  |
| kepler             | 587        |    3       | 109        |   0.255    |   1.12e+04 |        0.00235 |
| snia               |  70        |    0       |   1.17     |   0.00182  |  32        |        0.00155 |

Per site (median and p99 over the distinct calls):

| site                               |    calls |   distinct |    total_s |   median_us |     p99_ms |     max_ms |   censored | guarded   |
|:-----------------------------------|---------:|-----------:|-----------:|------------:|-----------:|-----------:|-----------:|:----------|
| construction:concat                |  1220170 |     302083 |   3.25e+04 |  300        |  72.3      |   3.26e+04 |        981 | True      |
| final_check_intersection           |  2723638 |     931182 |   7.83e+03 |  369        |  11        |   3e+04    |        197 | True      |
| reduce_automata:1154               |  5993150 |     498482 |   6.31e+03 |  172        |  14.2      |   2.98e+04 |        160 | False     |
| noodlify_for_equation              |  1233133 |     274792 |   3.12e+03 |  284        |  99.5      |   2.98e+04 |         30 | False     |
| segs_one_initial_final             | 18403026 |     667772 |   2.08e+03 |  135        |  10.4      |   1.17e+03 |         75 | False     |
| construction:intersection          |    98868 |      16084 |   1.56e+03 |  274        | 157        |   3e+04    |         51 | True      |
| refine_languages:1145              |  2801663 |     122244 | 787        |   32.9      |   7.43     | 634        |         17 | False     |
| memb_heuristic_union               |    50330 |      16021 | 629        |    2.52e+03 | 132        |   2.06e+04 |          3 | True      |
| memb_heuristic_intersection        |    26630 |      23072 | 253        |   75.4      | 143        |   2.92e+04 |          3 | True      |
| construction:union                 |   535936 |     211027 | 248        |  115        |   4.81     |   1.14e+04 |          1 | True      |
| construction:complement            |   117420 |      14843 | 159        |  346        |   3.92     |   1.81e+04 |          5 | True      |
| reduce:407                         |   963062 |      85919 | 145        |   68.1      |   0.468    | 781        |          4 | False     |
| construction:star                  |   569685 |     134745 | 130        |  102        |   1.8      |   1.18e+03 |          0 | True      |
| construction:loop_body             |   197255 |      71110 |  65.5      |  129        |   1.21     |   9.19e+03 |          0 | False     |
| construction:loop                  |    55060 |      54102 |  57.2      |  326        |  10.3      |   2.13e+03 |          0 | True      |
| process_transducer:442             |      736 |        222 |  39.1      |    1.36e+03 |   2.24e+03 |   2.49e+04 |          1 | False     |
| noodlify_for_transducer            |     8716 |       1772 |  38.8      |    1.36e+03 | 126        | 363        |          0 | False     |
| propagate_singletons:398           |   326029 |       8803 |  21.3      |   64.4      |   0.103    |  12.9      |          1 | False     |
| get_to_int_value_bounds:126        |   132480 |      14082 |  12.1      |  127        |   0.637    |   1.39     |          0 | False     |
| process_transducer:390             |     1117 |       1081 |  11.5      |    1.14e+04 |  13.7      |  17        |          0 | False     |
| get_to_int_value_bounds:125        |   132480 |      12639 |  11.5      |   74.7      |   0.34     |   0.94     |          0 | False     |
| construction:loop_body_unbounded   |    54718 |      29284 |  10.2      |  165        |   0.739    | 452        |          0 | False     |
| get_formula_for_valid_int_case:479 |    97090 |       5250 |   8.75     |   59.6      |   0.272    |   0.506    |          0 | False     |
| conversions_validity:1771          |    84788 |      12421 |   8.3      |   91.4      |   0.389    |   9.26     |          0 | False     |
| get_formula_for_invalid_case:442   |    97090 |       4025 |   2.21     |    7.68     |   0.324    |   2.43     |          0 | False     |
| construction:plus                  |     4623 |       2000 |   1.06     |  160        |   0.764    |  94.4      |          0 | True      |
| reluctant_nfa_with_marker          |      173 |         77 |   0.125    |  627        |   3.96     |   5.14     |          0 | False     |
| get_lia_for_not_contains_group:943 |       12 |          6 |   0.000586 |   65.6      |   0.107    |   0.108    |          0 | False     |

## Ranking of single properties

Spearman ρ and Kendall τ with the time (non-censored distinct calls; τ on a sample of at most 200k), ROC AUC of each property for a call over the threshold (censored calls over it count as expensive).

|               |   spearman |   kendall |   AUC>1ms |   AUC>10ms |   AUC>50ms |
|:--------------|-----------:|----------:|----------:|-----------:|-----------:|
| Q*M           |     0.976  |    0.877  |     0.996 |      0.997 |      0.998 |
| Q*T           |     0.974  |    0.873  |     0.995 |      0.997 |      0.998 |
| Q*S           |     0.954  |    0.833  |     0.984 |      0.99  |      0.997 |
| Q^2*S         |     0.932  |    0.793  |     0.988 |      0.992 |      0.997 |
| moves         |     0.907  |    0.761  |     0.922 |      0.987 |      0.994 |
| transitions   |     0.907  |    0.761  |     0.923 |      0.987 |      0.995 |
| states        |     0.73   |    0.577  |     0.971 |      0.985 |      0.984 |
| sccs          |     0.717  |    0.563  |     0.928 |      0.97  |      0.968 |
| symbols       |     0.7    |    0.533  |     0.71  |      0.672 |      0.658 |
| max_out       |     0.635  |    0.485  |     0.66  |      0.662 |      0.659 |
| self_loops    |     0.59   |    0.48   |     0.624 |      0.667 |      0.738 |
| T/Q           |     0.545  |    0.407  |     0.561 |      0.559 |      0.561 |
| cyclic        |     0.53   |    0.43   |     0.638 |      0.688 |      0.773 |
| useful        |     0.433  |    0.326  |     0.955 |      0.98  |      0.98  |
| max_targets   |     0.383  |    0.313  |     0.694 |      0.709 |      0.744 |
| alphabet      |     0.275  |    0.204  |     0.641 |      0.551 |      0.557 |
| max_scc       |     0.155  |    0.129  |     0.609 |      0.59  |      0.611 |
| completeness  |     0.146  |    0.103  |     0.358 |      0.363 |      0.357 |
| final         |     0.0833 |    0.0688 |     0.584 |      0.553 |      0.617 |
| epsilon       |     0.0828 |    0.0682 |     0.53  |      0.623 |      0.634 |
| initial       |    -0.0593 |   -0.0452 |     0.503 |      0.501 |      0.535 |
| deterministic |    -0.155  |   -0.127  |     0.357 |      0.336 |      0.276 |

## Cost models of log(time): all distinct calls

3513611 distinct non-censored calls of 125755 formulas; standard errors clustered by formula.

|                     |     R2 |   R2_cv |   RMSE_cv |       AIC |       BIC | coefficients                                                                                                                                                                                                                                                  |
|:--------------------|-------:|--------:|----------:|----------:|----------:|:--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| Q                   | 0.6626 |  0.6626 |    0.8096 | 8.487e+06 | 8.487e+06 | states 1.15±0.00                                                                                                                                                                                                                                              |
| T                   | 0.8019 |  0.8019 |    0.6204 | 6.616e+06 | 6.616e+06 | transitions 0.72±0.00                                                                                                                                                                                                                                         |
| Q*T                 | 0.9365 |  0.9365 |    0.3513 | 2.62e+06  | 2.62e+06  | Q*T 0.52±0.00                                                                                                                                                                                                                                                 |
| Q+T                 | 0.9491 |  0.9491 |    0.3143 | 1.838e+06 | 1.838e+06 | states 0.65±0.00, transitions 0.52±0.00                                                                                                                                                                                                                       |
| Q+T+S               | 0.9501 |  0.9501 |    0.3114 | 1.773e+06 | 1.773e+06 | states 0.68±0.00, transitions 0.46±0.00, symbols 0.09±0.00                                                                                                                                                                                                    |
| Q+T+S+M             | 0.9524 |  0.9524 |    0.304  | 1.603e+06 | 1.603e+06 | states 0.68±0.00, transitions -0.12±0.01, symbols 0.07±0.00, moves 0.59±0.01                                                                                                                                                                                  |
| Q+T/Q+S+compl       | 0.9544 |  0.9544 |    0.2977 | 1.457e+06 | 1.457e+06 | states 1.20±0.00, T/Q 0.71±0.00, symbols -0.06±0.00, completeness -0.47±0.01                                                                                                                                                                                  |
| Q+T+S+structure     | 0.9604 |  0.9604 |    0.2775 | 9.62e+05  | 9.622e+05 | states 0.22±0.01, transitions 0.22±0.01, symbols -0.01±0.00, moves 0.30±0.01, useful 0.23±0.00, sccs 0.29±0.01, max_scc 0.20±0.01, cyclic -0.05±0.00, max_out 0.09±0.00, max_targets -0.47±0.01, deterministic 0.07±0.01, final -0.15±0.00, initial 0.04±0.00 |
| Q+T+Q²+T²           | 0.9569 |  0.9569 |    0.2892 | 1.253e+06 | 1.253e+06 | states 0.36±0.00, transitions 0.42±0.00, states^2 0.05±0.00, transitions^2 0.02±0.00                                                                                                                                                                          |
| Q+T+S+Q²+T²         | 0.9613 |  0.9613 |    0.2741 | 8.76e+05  | 8.761e+05 | states 0.45±0.00, transitions 0.19±0.01, symbols 0.22±0.00, states^2 0.04±0.00, transitions^2 0.03±0.00                                                                                                                                                       |
| post: Q+T+S+classes | 0.9553 |  0.9553 |    0.2948 | 1.387e+06 | 1.387e+06 | states 0.23±0.01, transitions 0.54±0.00, symbols 0.03±0.00, res_states 0.42±0.01                                                                                                                                                                              |

Likelihood-ratio test structure vs Q+T+S: LR 811325.9, df 10, p 0 (non-robust; with this many calls, effect sizes and CV decide).

VIF (Q+T+S+M): states 2.1, transitions 220.9, symbols 5.6, moves 224.9

## Cost models of log(time): guarded sites

1703918 distinct non-censored calls of 108425 formulas; standard errors clustered by formula.

|                     |     R2 |   R2_cv |   RMSE_cv |        AIC |        BIC | coefficients                                                                                                                                                                                                                                                     |
|:--------------------|-------:|--------:|----------:|-----------:|-----------:|:-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| Q                   | 0.4753 |  0.4753 |    0.8324 |  4.21e+06  |  4.21e+06  | states 1.09±0.01                                                                                                                                                                                                                                                 |
| T                   | 0.7876 |  0.7876 |    0.5296 |  2.669e+06 |  2.669e+06 | transitions 0.67±0.00                                                                                                                                                                                                                                            |
| Q*T                 | 0.9377 |  0.9377 |    0.2869 |  5.801e+05 |  5.802e+05 | Q*T 0.55±0.00                                                                                                                                                                                                                                                    |
| Q+T                 | 0.9474 |  0.9474 |    0.2635 |  2.904e+05 |  2.904e+05 | states 0.68±0.00, transitions 0.55±0.00                                                                                                                                                                                                                          |
| Q+T+S               | 0.9497 |  0.9497 |    0.2576 |  2.134e+05 |  2.134e+05 | states 0.72±0.00, transitions 0.47±0.00, symbols 0.13±0.00                                                                                                                                                                                                       |
| Q+T+S+M             | 0.9498 |  0.9498 |    0.2575 |  2.11e+05  |  2.111e+05 | states 0.72±0.00, transitions 0.28±0.03, symbols 0.12±0.00, moves 0.19±0.03                                                                                                                                                                                      |
| Q+T/Q+S+compl       | 0.952  |  0.952  |    0.2519 |  1.363e+05 |  1.364e+05 | states 1.23±0.00, T/Q 0.57±0.00, symbols 0.11±0.00, completeness -0.06±0.01                                                                                                                                                                                      |
| Q+T+S+structure     | 0.9563 |  0.9563 |    0.2402 | -2.483e+04 | -2.466e+04 | states 0.36±0.01, transitions 0.79±0.03, symbols 0.13±0.00, moves -0.17±0.03, useful 0.14±0.00, sccs 0.16±0.01, max_scc 0.03±0.01, cyclic -0.06±0.00, max_out -0.12±0.00, max_targets -0.33±0.01, deterministic -0.11±0.00, final -0.09±0.00, initial -0.04±0.00 |
| Q+T+Q²+T²           | 0.9543 |  0.9543 |    0.2457 |  5.207e+04 |  5.213e+04 | states 0.24±0.01, transitions 0.46±0.00, states^2 0.07±0.00, transitions^2 0.01±0.00                                                                                                                                                                             |
| Q+T+S+Q²+T²         | 0.9588 |  0.9588 |    0.2332 | -1.263e+05 | -1.262e+05 | states 0.31±0.01, transitions 0.27±0.00, symbols 0.19±0.00, states^2 0.07±0.00, transitions^2 0.02±0.00                                                                                                                                                          |
| post: Q+T+S+classes | 0.9546 |  0.9546 |    0.2449 |  3.992e+04 |  3.998e+04 | states 0.31±0.00, transitions 0.52±0.00, symbols 0.10±0.00, res_states 0.36±0.00                                                                                                                                                                                 |

Likelihood-ratio test structure vs Q+T+S: LR 238234.0, df 10, p 0 (non-robust; with this many calls, effect sizes and CV decide).

VIF (Q+T+S+M): states 1.5, transitions 939.8, symbols 5.9, moves 952.6

## Cost models of log(time): calls with at least 100 states

72852 distinct non-censored calls of 11619 formulas; standard errors clustered by formula.

|                     |     R2 |   R2_cv |   RMSE_cv |       AIC |       BIC | coefficients                                                                                                                                                                                                                                                    |
|:--------------------|-------:|--------:|----------:|----------:|----------:|:----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| Q                   | 0.6568 |  0.6568 |    0.8417 | 1.816e+05 | 1.816e+05 | states 1.50±0.01                                                                                                                                                                                                                                                |
| T                   | 0.6852 |  0.685  |    0.8064 | 1.753e+05 | 1.753e+05 | transitions 0.83±0.01                                                                                                                                                                                                                                           |
| Q*T                 | 0.8546 |  0.8544 |    0.5482 | 1.191e+05 | 1.191e+05 | Q*T 0.68±0.00                                                                                                                                                                                                                                                   |
| Q+T                 | 0.8777 |  0.8776 |    0.5027 | 1.065e+05 | 1.065e+05 | states 0.96±0.01, transitions 0.56±0.01                                                                                                                                                                                                                         |
| Q+T+S               | 0.8957 |  0.8955 |    0.4644 | 9.488e+04 | 9.491e+04 | states 1.06±0.01, transitions 0.49±0.01, symbols 0.26±0.01                                                                                                                                                                                                      |
| Q+T+S+M             | 0.8959 |  0.8957 |    0.4641 | 9.475e+04 | 9.48e+04  | states 1.06±0.01, transitions 0.36±0.05, symbols 0.26±0.01, moves 0.13±0.05                                                                                                                                                                                     |
| Q+T/Q+S+compl       | 0.9049 |  0.9047 |    0.4436 | 8.814e+04 | 8.819e+04 | states 1.57±0.01, T/Q 0.32±0.02, symbols 0.43±0.01, completeness 1.40±0.11                                                                                                                                                                                      |
| Q+T+S+structure     | 0.9141 |  0.9134 |    0.4229 | 8.078e+04 | 8.091e+04 | states 0.93±0.04, transitions 0.63±0.06, symbols 0.20±0.01, moves -0.03±0.06, useful 0.14±0.02, sccs -0.00±0.02, max_scc 0.00±0.01, cyclic -0.06±0.01, max_out -0.00±0.02, max_targets -0.01±0.04, deterministic 0.31±0.02, final -0.10±0.01, initial 0.19±0.01 |
| Q+T+Q²+T²           | 0.8859 |  0.8856 |    0.4859 | 1.014e+05 | 1.015e+05 | states 0.68±0.08, transitions -0.06±0.04, states^2 0.02±0.01, transitions^2 0.04±0.00                                                                                                                                                                           |
| Q+T+S+Q²+T²         | 0.8998 |  0.8995 |    0.4555 | 9.196e+04 | 9.202e+04 | states 0.57±0.07, transitions 0.10±0.04, symbols 0.24±0.01, states^2 0.04±0.01, transitions^2 0.03±0.00                                                                                                                                                         |
| post: Q+T+S+classes | 0.9232 |  0.9231 |    0.3984 | 7.253e+04 | 7.257e+04 | states 0.80±0.01, transitions 0.55±0.01, symbols 0.17±0.01, res_states 0.38±0.01                                                                                                                                                                                |

Likelihood-ratio test structure vs Q+T+S: LR 14113.0, df 10, p 0 (non-robust; with this many calls, effect sizes and CV decide).

VIF (Q+T+S+M): states 1.6, transitions 90.0, symbols 1.2, moves 90.6

## Censored calls

1529 censored calls; predicted time vs the lower bound (time until the end of the run):

|         | set   | site                |   states |   transitions |   symbols |   moves |   lower_bound_ms |   predicted_ms |
|--------:|:------|:--------------------|---------:|--------------:|----------:|--------:|-----------------:|---------------:|
| 1975692 | redos | construction:concat |    10022 |         60021 |        16 |   40024 |         3.26e+04 |     948        |
| 2489564 | redos | construction:concat |    15011 |        200010 |        19 |  150020 |         3.13e+04 |       2.2e+03  |
| 2172708 | redos | construction:concat |    30044 |        470354 |        30 |  435356 |         3.1e+04  |       5.44e+03 |
| 1477284 | redos | construction:concat |    20006 |         25016 |        11 |   20017 |         3.07e+04 |     987        |
| 2267102 | redos | construction:concat |    20030 |         25412 |        70 |   20400 |         3.06e+04 |       1.17e+03 |
| 1069510 | redos | construction:concat |    25004 |         35003 |         4 |   30004 |         3.06e+04 |       1.24e+03 |
|  647576 | redos | construction:concat |    20012 |         25011 |         7 |   20012 |         3.06e+04 |     952        |
| 3391494 | redos | construction:concat |    25008 |         35033 |         9 |   30032 |         3.06e+04 |       1.32e+03 |
|  796102 | redos | construction:concat |    25007 |         35006 |         5 |   30007 |         3.06e+04 |       1.26e+03 |
|  957248 | redos | construction:concat |    25011 |         35030 |         9 |   30027 |         3.06e+04 |       1.32e+03 |
| 2370906 | redos | construction:concat |    20007 |         25006 |         6 |   20007 |         3.06e+04 |     940        |
|  552122 | redos | construction:concat |    20025 |         25407 |        69 |   20395 |         3.06e+04 |       1.16e+03 |
| 1449759 | redos | construction:concat |    25014 |         35035 |        10 |   30032 |         3.05e+04 |       1.33e+03 |
| 2489632 | redos | construction:concat |    10007 |        150006 |        16 |  100016 |         3.05e+04 |       1.44e+03 |
| 1087093 | redos | construction:concat |    10007 |        150006 |        13 |  100016 |         3.05e+04 |       1.42e+03 |
| 1536194 | redos | construction:concat |    10007 |         15147 |        71 |   10147 |         3.04e+04 |     573        |
| 2091286 | redos | construction:concat |    10019 |         20220 |        67 |   10207 |         3.04e+04 |     651        |
| 3243280 | redos | construction:concat |    25011 |         35039 |        10 |   30038 |         3.04e+04 |       1.33e+03 |
| 1006994 | redos | construction:concat |    10018 |         20202 |        19 |   10201 |         3.04e+04 |     584        |
| 1399839 | redos | construction:concat |    10011 |         15030 |        13 |   10029 |         3.04e+04 |     493        |
|  806018 | redos | construction:concat |    10016 |         20160 |        19 |   10160 |         3.04e+04 |     583        |
|  522540 | redos | construction:concat |    10009 |         15028 |        12 |   10027 |         3.04e+04 |     490        |
| 1988796 | redos | construction:concat |    10007 |         15006 |         6 |   10007 |         3.04e+04 |     463        |
| 3282320 | redos | construction:concat |    10009 |         15010 |         4 |   10009 |         3.04e+04 |     450        |
| 1597947 | redos | construction:concat |    10008 |         15009 |         4 |   10008 |         3.04e+04 |     450        |
| 1734934 | redos | construction:concat |    10012 |         20011 |         8 |   10012 |         3.04e+04 |     541        |
|  636402 | redos | construction:concat |    10014 |         15033 |        14 |   10032 |         3.04e+04 |     497        |
|  886086 | redos | construction:concat |    10006 |         15007 |         3 |   10006 |         3.04e+04 |     441        |
| 2351893 | redos | construction:concat |    10010 |         15009 |         7 |   10010 |         3.04e+04 |     469        |
| 1681085 | redos | construction:concat |    10005 |         15004 |         5 |   10005 |         3.04e+04 |     457        |

## Benefit of the reductions

Median ratios after/before by cost of the call (guarded sites):

| cost     |      calls |   state_ratio |   transition_ratio |
|:---------|-----------:|--------------:|-------------------:|
| <0.1ms   |   2.47e+05 |         0.875 |              1     |
| 0.1-1ms  |   1.27e+06 |         0.5   |              0.5   |
| 1-10ms   |   1.71e+05 |         0.857 |              0.84  |
| 10-100ms |   1.66e+04 |         0.9   |              0.9   |
| 0.1-1s   |   3.38e+03 |         0.911 |              0.934 |
| >1s      | 747        |         0.974 |              0.621 |

By site:

| site                               |      calls |   state_ratio |   transition_ratio |   unchanged |
|:-----------------------------------|-----------:|--------------:|-------------------:|------------:|
| final_check_intersection           |   9.31e+05 |         0.5   |             0.5    |     0.0467  |
| segs_one_initial_final             |   6.68e+05 |         1     |             1      |     0.911   |
| reduce_automata:1154               |   4.98e+05 |         0.8   |             0.644  |     0.474   |
| construction:concat                |   3.01e+05 |         0.889 |             0.691  |     0.367   |
| noodlify_for_equation              |   2.75e+05 |         1     |             1      |     0.73    |
| construction:union                 |   2.11e+05 |         0.769 |             1      |     0.111   |
| construction:star                  |   1.35e+05 |         1     |             1      |     0.943   |
| refine_languages:1145              |   1.22e+05 |         1     |             1      |     1       |
| reduce:407                         |   8.59e+04 |         1     |             1      |     0.896   |
| construction:loop_body             |   7.11e+04 |         1     |             1      |     0.986   |
| construction:loop                  |   5.41e+04 |         0.75  |             0.75   |     0.00532 |
| construction:loop_body_unbounded   |   2.93e+04 |         0.75  |             1      |     0.00137 |
| memb_heuristic_intersection        |   2.31e+04 |         0.849 |             0.871  |     0.345   |
| construction:intersection          |   1.6e+04  |         0.75  |             1      |     0.445   |
| memb_heuristic_union               |   1.6e+04  |         0.964 |             0.997  |     0.0267  |
| construction:complement            |   1.48e+04 |         1     |             1      |     0.965   |
| get_to_int_value_bounds:126        |   1.41e+04 |         1     |             1      |     0.901   |
| get_to_int_value_bounds:125        |   1.26e+04 |         1     |             1      |     0.889   |
| conversions_validity:1771          |   1.24e+04 |         1     |             1      |     0.83    |
| propagate_singletons:398           |   8.8e+03  |         1     |             1      |     1       |
| get_formula_for_valid_int_case:479 |   5.25e+03 |         1     |             1      |     0.962   |
| get_formula_for_invalid_case:442   |   4.02e+03 |         0     |             0      |     0.408   |
| construction:plus                  |   2e+03    |         1     |             1      |     1       |
| noodlify_for_transducer            |   1.77e+03 |         0.25  |             0.0833 |     0.308   |
| process_transducer:390             |   1.08e+03 |         1     |             1      |     0.996   |
| process_transducer:442             | 221        |         0.995 |             0.99   |     0.457   |
| reluctant_nfa_with_marker          |  77        |         0.5   |             0.5    |     0       |
| get_lia_for_not_contains_group:943 |   6        |         1     |             1      |     1       |

## Candidate guards (guarded sites, calls weighted by repeats, out-of-fold decisions)

Columns: share of reduced calls, share of the reduce time still spent, for each budget B the calls over B still reduced and the calls under B skipped, and the share of the states removed by the reductions that is lost by skipping.

|               |   reduced_calls |   time_kept |   kept>1ms |   skipped<=1ms |   kept>5ms |   skipped<=5ms |   kept>10ms |   skipped<=10ms |   kept>20ms |   skipped<=20ms |   kept>50ms |   skipped<=50ms |   kept>100ms |   skipped<=100ms |   states_removed_lost |
|:--------------|----------------:|------------:|-----------:|---------------:|-----------:|---------------:|------------:|----------------:|------------:|----------------:|------------:|----------------:|-------------:|-----------------:|----------------------:|
| Q<100         |           0.991 |      0.12   |   9.36e+05 |       0        |   1.68e+05 |       4.36e+03 |    4.42e+04 |        1.15e+04 |    1.27e+04 |        2.05e+04 |    2.69e+03 |        3.34e+04 |     1.25e+03 |         4.07e+04 |                0.228  |
| Q<250         |           0.998 |      0.15   |   9.74e+05 |       0        |   2.02e+05 |       0        |    7.09e+04 |        1        |    3.08e+04 |      452        |    9.69e+03 |        2.16e+03 |     3.43e+03 |         4.7e+03  |                0.138  |
| Q<1000        |           1     |      0.221  |   9.84e+05 |       0        |   2.12e+05 |       0        |    8.12e+04 |        0        |    4.07e+04 |        0        |    1.78e+04 |        0        |     9.03e+03 |         2        |                0.043  |
| model<=1ms    |           0.81  |      0.0296 |   3.83e+04 |       7.62e+04 |  11        |       8.1e+05  |    2        |        9.41e+05 |    2        |        9.82e+05 |    2        |        1e+06    |     0        |         1.01e+06 |                0.678  |
| Q*T<=c(1ms)   |           0.789 |      0.0273 |   6.14e+03 |       1.61e+05 |  11        |       9.26e+05 |    2        |        1.06e+06 |    2        |        1.1e+06  |    2        |        1.12e+06 |     0        |         1.13e+06 |                0.689  |
| Q*M<=c(1ms)   |           0.788 |      0.0272 |   5.55e+03 |       1.64e+05 |  11        |       9.31e+05 |    2        |        1.06e+06 |    2        |        1.1e+06  |    2        |        1.13e+06 |     0        |         1.13e+06 |                0.689  |
| model<=5ms    |           0.956 |      0.0708 |   7.46e+05 |       0        |   3.44e+04 |       6.01e+04 |    1.86e+03 |        1.59e+05 |   36        |        1.97e+05 |    9        |        2.2e+05  |     0        |         2.29e+05 |                0.412  |
| Q*T<=c(5ms)   |           0.885 |      0.0435 |   3.65e+05 |      25        | 384        |       4.08e+05 |    7        |        5.38e+05 |    2        |        5.79e+05 |    2        |        6.02e+05 |     0        |         6.11e+05 |                0.586  |
| Q*M<=c(5ms)   |           0.885 |      0.0436 |   3.66e+05 |      19        | 496        |       4.07e+05 |    7        |        5.38e+05 |    2        |        5.78e+05 |    2        |        6.01e+05 |     0        |         6.1e+05  |                0.586  |
| model<=10ms   |           0.985 |      0.0944 |   9.03e+05 |       0        |   1.31e+05 |     132        |    1.71e+04 |        1.73e+04 |    2.23e+03 |        4.29e+04 |   77        |        6.36e+04 |    12        |         7.23e+04 |                0.278  |
| Q*T<=c(10ms)  |           0.929 |      0.0581 |   6.02e+05 |       0        |   1.17e+04 |       1.82e+05 |  163        |        3.01e+05 |   14        |        3.42e+05 |    9        |        3.65e+05 |     0        |         3.73e+05 |                0.493  |
| Q*M<=c(10ms)  |           0.932 |      0.0596 |   6.21e+05 |       0        |   1.38e+04 |       1.65e+05 |  212        |        2.83e+05 |   14        |        3.23e+05 |    9        |        3.46e+05 |     0        |         3.55e+05 |                0.484  |
| model<=20ms   |           0.994 |      0.116  |   9.54e+05 |       0        |   1.81e+05 |       0        |    5.04e+04 |       79        |    1.39e+04 |        4.08e+03 |    2.3e+03  |        1.53e+04 |   508        |         2.23e+04 |                0.203  |
| Q*T<=c(20ms)  |           0.956 |      0.0717 |   7.51e+05 |       0        |   3.96e+04 |       6.03e+04 |    2.21e+03 |        1.54e+05 |   57        |        1.92e+05 |   13        |        2.15e+05 |     2        |         2.24e+05 |                0.411  |
| Q*M<=c(20ms)  |           0.958 |      0.0728 |   7.61e+05 |       0        |   4.3e+04  |       5.41e+04 |    2.61e+03 |        1.45e+05 |   62        |        1.83e+05 |   17        |        2.06e+05 |     2        |         2.14e+05 |                0.405  |
| model<=50ms   |           0.998 |      0.151  |   9.76e+05 |       0        |   2.04e+05 |       0        |    7.26e+04 |        0        |    3.21e+04 |        3        |    1.02e+04 |      916        |     3.05e+03 |         2.56e+03 |                0.126  |
| Q*T<=c(50ms)  |           0.975 |      0.0852 |   8.53e+05 |       0        |   8.74e+04 |       6.06e+03 |    9.49e+03 |        5.93e+04 |  532        |        9.08e+04 |   38        |        1.13e+05 |     3        |         1.22e+05 |                0.329  |
| Q*M<=c(50ms)  |           0.975 |      0.0851 |   8.52e+05 |       0        |   8.68e+04 |       6.61e+03 |    9.68e+03 |        6.06e+04 |  529        |        9.2e+04  |   38        |        1.14e+05 |     3        |         1.23e+05 |                0.33   |
| model<=100ms  |           0.999 |      0.181  |   9.81e+05 |       0        |   2.09e+05 |       0        |    7.82e+04 |        0        |    3.77e+04 |        1        |    1.49e+04 |        2        |     6.27e+03 |       206        |                0.0862 |
| Q*T<=c(100ms) |           0.977 |      0.0872 |   8.65e+05 |       0        |   9.7e+04  |       4.12e+03 |    1.09e+04 |        4.93e+04 |  766        |        7.96e+04 |   57        |        1.02e+05 |    10        |         1.1e+05  |                0.318  |
| Q*M<=c(100ms) |           0.977 |      0.0872 |   8.64e+05 |       0        |   9.67e+04 |       4.48e+03 |    1.11e+04 |        5.01e+04 |  763        |        8.02e+04 |   57        |        1.02e+05 |    10        |         1.11e+05 |                0.319  |

Thresholds of the product rules fitted on all guarded calls: Q*T<=c(1ms): c = 1.98e+03, Q*M<=c(1ms): c = 1.92e+03, Q*T<=c(5ms): c = 1.6e+04, Q*M<=c(5ms): c = 1.55e+04, Q*T<=c(10ms): c = 3.38e+04, Q*M<=c(10ms): c = 3.65e+04, Q*T<=c(20ms): c = 6.58e+04, Q*M<=c(20ms): c = 6.44e+04, Q*T<=c(50ms): c = 1.18e+05, Q*M<=c(50ms): c = 1.15e+05, Q*T<=c(100ms): c = 1.54e+05, Q*M<=c(100ms): c = 1.5e+05

Depth-2 tree for > 1 ms (thresholds on log(x+1) of states, transitions, moves, symbols):
```
|--- l_transitions <= 5.58
|   |--- l_states <= 2.86
|   |   |--- class: False
|   |--- l_states >  2.86
|   |   |--- class: True
|--- l_transitions >  5.58
|   |--- l_states <= 2.01
|   |   |--- class: True
|   |--- l_states >  2.01
|   |   |--- class: True
```

Depth-2 tree for > 5 ms (thresholds on log(x+1) of states, transitions, moves, symbols):
```
|--- l_states <= 3.07
|   |--- l_transitions <= 7.57
|   |   |--- class: False
|   |--- l_transitions >  7.57
|   |   |--- class: True
|--- l_states >  3.07
|   |--- l_moves <= 4.98
|   |   |--- class: False
|   |--- l_moves >  4.98
|   |   |--- class: True
```

Depth-2 tree for > 10 ms (thresholds on log(x+1) of states, transitions, moves, symbols):
```
|--- l_states <= 3.38
|   |--- l_transitions <= 7.36
|   |   |--- class: False
|   |--- l_transitions >  7.36
|   |   |--- class: True
|--- l_states >  3.38
|   |--- l_states <= 3.73
|   |   |--- class: True
|   |--- l_states >  3.73
|   |   |--- class: True
```

Depth-2 tree for > 20 ms (thresholds on log(x+1) of states, transitions, moves, symbols):
```
|--- l_states <= 3.75
|   |--- l_transitions <= 8.39
|   |   |--- class: False
|   |--- l_transitions >  8.39
|   |   |--- class: True
|--- l_states >  3.75
|   |--- l_moves <= 6.07
|   |   |--- class: False
|   |--- l_moves >  6.07
|   |   |--- class: True
```

Depth-2 tree for > 50 ms (thresholds on log(x+1) of states, transitions, moves, symbols):
```
|--- l_states <= 4.07
|   |--- l_moves <= 8.57
|   |   |--- class: False
|   |--- l_moves >  8.57
|   |   |--- class: True
|--- l_states >  4.07
|   |--- l_moves <= 6.18
|   |   |--- class: False
|   |--- l_moves >  6.18
|   |   |--- class: True
```

Depth-2 tree for > 100 ms (thresholds on log(x+1) of states, transitions, moves, symbols):
```
|--- l_transitions <= 8.14
|   |--- l_states <= 5.09
|   |   |--- class: False
|   |--- l_states >  5.09
|   |   |--- class: True
|--- l_transitions >  8.14
|   |--- l_transitions <= 8.72
|   |   |--- class: True
|   |--- l_transitions >  8.72
|   |   |--- class: True
```

