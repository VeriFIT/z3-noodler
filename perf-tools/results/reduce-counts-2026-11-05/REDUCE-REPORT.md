2352 formulas finished by every solver (old, new).

Guarded sites: the regex construction (except loop bodies), the final-check intersection and the membership heuristics.

## Per solver

|                        |          old |          new |
|:-----------------------|-------------:|-------------:|
| formulas               | 2352         | 2352         |
| reductions             |    7.163e+05 |    7.161e+05 |
| states_before          |    2.496e+06 |    2.359e+06 |
| states_after           |    2.227e+06 |    2.112e+06 |
| transitions_before     |    1.571e+07 |    1.342e+07 |
| transitions_after      |    9.249e+06 |    8.099e+06 |
| reduce_seconds         |  314.4       |  123.7       |
| states_removed         |    2.69e+05  |    2.472e+05 |
| solving_seconds        | 1229         | 1261         |
| guarded_reductions     |    4.827e+04 |    4.807e+04 |
| guarded_reduce_seconds |  215.4       |   23.91      |

## Per call site

| site                                                    | guarded   |   old reductions |   old reduce_seconds |   old states_removed |   new reductions |   new reduce_seconds |   new states_removed |
|:--------------------------------------------------------|:----------|-----------------:|---------------------:|---------------------:|-----------------:|---------------------:|---------------------:|
| seg_nfa::segs_one_initial_final                         | False     |        5.075e+05 |            27.24     |         5280         |        5.075e+05 |            27.2      |         5280         |
| seg_nfa::noodlify_for_equation                          | False     |        1.024e+05 |            24.22     |            2.834e+04 |        1.024e+05 |            24.51     |            2.834e+04 |
| FormulaPreprocessor::reduce_automata                    | False     |        2.525e+04 |            30.5      |            5.636e+04 |        2.525e+04 |            30.89     |            5.6e+04   |
| FormulaPreprocessor::refine_languages                   | False     |        1.609e+04 |             7.195    |            0         |        1.609e+04 |             7.221    |            0         |
| NfaConstructor::create_nfa_for_expr:union               | True      |        1.256e+04 |             2.963    |            2.386e+04 |        1.256e+04 |             2.365    |            2.385e+04 |
| NfaConstructor::create_nfa_for_expr:concat              | True      |        1.159e+04 |            66.88     |            3.651e+04 |        1.152e+04 |             3.715    |            2.186e+04 |
| NfaConstructor::create_nfa_for_expr:star                | True      |        1.146e+04 |             2.079    |         1697         |        1.145e+04 |             1.429    |         1533         |
| AutAssignment::reduce                                   | False     |     9473         |             0.5915   |           15         |     9473         |             0.5909   |           15         |
| theory_str_noodler::create_aut_assignment_for_formula   | True      |     8618         |            13.46     |            3.216e+04 |     8563         |            12.77     |            3.168e+04 |
| seg_nfa::noodlify_for_transducer                        | False     |     3230         |             6.813    |            6.974e+04 |     3230         |             6.888    |            6.974e+04 |
| NfaConstructor::create_nfa_for_expr:loop_body           | False     |     1267         |             0.237    |           19         |     1267         |             0.237    |           19         |
| NfaConstructor::create_nfa_for_expr:intersection        | True      |     1160         |             0.6131   |         1549         |     1159         |             0.5872   |         1542         |
| NfaConstructor::create_nfa_for_expr:complement          | True      |     1140         |             0.616    |           16         |     1140         |             0.6156   |           16         |
| ConversionHandler::get_to_int_value_bounds              | False     |     1060         |             0.1477   |           16         |     1060         |             0.1452   |           16         |
| MultMembHeuristicProcedure::compute_next_solution       | True      |      840         |             5.589    |         8198         |      799         |             1.016    |         4875         |
| NfaConstructor::create_nfa_for_expr:loop                | True      |      492         |             1.342    |          970         |      492         |             1.358    |          970         |
| NfaConstructor::create_nfa_for_expr:loop_body_unbounded | False     |      485         |             0.1086   |          485         |      485         |             0.1095   |          485         |
| DecisionProcedure::process_transducer                   | False     |      408         |             1.845    |          284         |      408         |             1.876    |          284         |
| NfaConstructor::create_nfa_for_expr:plus                | True      |      383         |             0.05052  |            0         |      383         |             0.05098  |            0         |
| FormulaPreprocessor::conversions_validity               | False     |      268         |             0.04395  |          600         |      268         |             0.04397  |          600         |
| ConversionHandler::get_formula_for_valid_int_case       | False     |      222         |             0.02011  |            0         |      222         |             0.02013  |            0         |
| ConversionHandler::get_formula_for_invalid_case         | False     |      222         |             0.007478 |            6         |      222         |             0.007819 |            6         |
| FormulaPreprocessor::propagate_singletons               | False     |      215         |             0.01598  |            0         |      215         |             0.01524  |            0         |
| NfaConstructor::create_nfa_for_expr:intersection_arg    | True      |       27         |           121.8      |         2856         |        0         |             0        |            0         |
| ReluctantReplace::reluctant_nfa_with_marker             | False     |       13         |             0.01123  |           63         |       13         |             0.01155  |           63         |

## Per set

| set                |   old reductions |   old reduce_seconds |   new reductions |   new reduce_seconds |
|:-------------------|-----------------:|---------------------:|-----------------:|---------------------:|
| negated_predicates |        4.983e+05 |            18.49     |        4.983e+05 |            18.53     |
| stringfuzz         |        5.98e+04  |             3.76     |        5.978e+04 |             3.128    |
| woorpje            |        4.36e+04  |            13.17     |        4.36e+04  |            13.31     |
| ecma2020_mixed_bmp |        3.893e+04 |            38.91     |        3.887e+04 |            38.11     |
| hornstr            |        1.828e+04 |             2.041    |        1.828e+04 |             2.071    |
| pyex               |        1.389e+04 |            10.57     |        1.389e+04 |            10.53     |
| transducer_plus    |     8540         |            12.49     |     8540         |            12.45     |
| slent              |     8308         |             9.485    |     8308         |             9.634    |
| str_small_rw       |     5306         |             0.2356   |     5306         |             0.2333   |
| full_str_int       |     5299         |             1.054    |     5299         |             1.059    |
| redos              |     2513         |             1.937    |     2511         |             0.9233   |
| norn               |     2229         |             0.261    |     2229         |             0.2586   |
| denghang           |     1785         |             6.484    |     1741         |             2.002    |
| kaluza             |     1422         |             0.5235   |     1422         |             0.533    |
| webapp             |     1312         |             3.216    |     1312         |             3.254    |
| ecma2020           |     1092         |             1.424    |     1090         |             0.7721   |
| automatark         |     1080         |             1.333    |     1074         |             0.9926   |
| leetcode           |     1016         |             0.1112   |     1016         |             0.1111   |
| sygus_qgen         |      990         |             0.2588   |      990         |             0.2642   |
| omark              |      945         |             0.06474  |      945         |             0.0659   |
| rna                |      643         |             4.83     |      643         |             4.9      |
| pcp                |      508         |             0.04521  |      508         |             0.04447  |
| slog               |      372         |             0.4812   |      372         |             0.4914   |
| matching           |      106         |           183.3      |       36         |             0.01846  |
| snia               |       32         |             0.002665 |       32         |             0.002249 |
