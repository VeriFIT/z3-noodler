/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    input_rewriter.cpp

Abstract:

    Rewriter for processing expressions only when they are loaded from input.

Author:

    Z3 Team 2026

--*/
#include "ast/rewriter/input_rewriter.h"
#include "smt/theory_str_noodler/expr_cases.h"

std::optional<expr_ref> input_rewriter::rewrite_to_code(expr* e) {
    expr_ref full_char(m_util_s.re.mk_full_char(m_util_s.re.mk_re(m_util_s.mk_string_sort())), m);
    expr_ref not_full_char(m_util_s.re.mk_complement(full_char), m);

    expr* to_code_arg; bool is_num_larger, is_eq; rational num;
    if (smt::noodler::expr_cases::is_to_code_leq_or_geq(e, m, m_util_s, m_util_a, to_code_arg, num, is_num_larger)) {
        if (is_num_larger) {
            // we have (str.to_code to_code_arg) <= num
            if (num >= zstring::max_char()) {
                return expr_ref(m.mk_true(), m);
            } else if (num < -1) {
                return expr_ref(m.mk_false(), m);
            } else {
                expr_ref regex(not_full_char); // encoding the case that to_code == -1
                if (num >= 0) {
                    unsigned num_unsigned = num.get_unsigned();
                    if (num_unsigned <= zstring::max_char()/2) {
                        // code point of to_code_arg is between [0, num] -> we can replace with regex to_code_arg \in range from 0 to num
                        // we only do it if [0, num] is smaller than [num+1, maxchar]
                        regex = expr_ref(m_util_s.re.mk_union(regex, m_util_s.re.mk_range(m_util_s.str.mk_string(zstring(unsigned(0))), m_util_s.str.mk_string(zstring(num_unsigned)))), m);
                    } else {
                        // [num+1, maxchar] is smaller -> we replace with regex allchar AND complement of range from 0 to num-1
                        expr_ref range(m_util_s.re.mk_inter(full_char, m_util_s.re.mk_complement(m_util_s.re.mk_range(m_util_s.str.mk_string(zstring(num_unsigned+1)), m_util_s.str.mk_string(zstring::max_char())))), m);
                        regex = expr_ref(m_util_s.re.mk_union(regex, range), m);
                    }
                }
                return expr_ref(m_util_s.re.mk_in_re(to_code_arg, regex), m);
            }
        } else {
            // we have (str.to_code to_code_arg) >= num
            if (num <= -1) {
                return expr_ref(m.mk_true(), m);
            } else if (num > zstring::max_char()) {
                return expr_ref(m.mk_false(), m);
            } else {
                unsigned num_unsigned = num.get_unsigned();
                if (num_unsigned == 0) {
                    return expr_ref(m_util_s.re.mk_in_re(to_code_arg, full_char), m);
                } else if (num_unsigned == zstring::max_char()) {
                    return expr_ref(m.mk_eq(to_code_arg, m_util_s.str.mk_string(zstring(zstring::max_char()))), m);
                } else if (num_unsigned > zstring::max_char()/2) {
                    // code point of to_code_arg is between [num, maxchar] -> we can replace with regex to_code_arg \in range from num to maxchar
                    // we only do it if [num, maxchar] is smaller than [0, num-1]
                    return expr_ref(m_util_s.re.mk_in_re(to_code_arg, m_util_s.re.mk_range(m_util_s.str.mk_string(zstring(num_unsigned)), m_util_s.str.mk_string(zstring(zstring::max_char())))), m);
                } else {
                    // [0, num-1] is smaller -> we replace with regex to_code_arg \in allchar AND to_code_arg \not\in range from 0 to num-1
                    return expr_ref(
                        m.mk_and(
                            m_util_s.re.mk_in_re(to_code_arg, full_char), // to_code_arg \in allchar
                            m.mk_not(m_util_s.re.mk_in_re(to_code_arg, m_util_s.re.mk_range(m_util_s.str.mk_string(zstring(unsigned(0))), m_util_s.str.mk_string(zstring(num_unsigned-1))))) // to_code_arg \not\in range from 0 to num-1
                        ), m);
                }
            }
        }
    } else if (smt::noodler::expr_cases::is_to_code_num_eq(e, m, m_util_s, m_util_a, to_code_arg, num, is_eq)) {
        if (is_eq) {
            if (num == -1) {
                return expr_ref(m_util_s.re.mk_in_re(to_code_arg, not_full_char), m);
            } else if (0 <= num && num <= zstring::max_char()) {
                return expr_ref(m.mk_eq(to_code_arg, m_util_s.str.mk_string(zstring(num.get_unsigned()))), m);
            } else {
                return expr_ref(m.mk_false(), m);
            }
        } else {
            if (num == -1) {
                return expr_ref(m_util_s.re.mk_in_re(to_code_arg, full_char), m);
            } else if (0 <= num && num <= zstring::max_char()) {
                return expr_ref(m.mk_not(m.mk_eq(to_code_arg, m_util_s.str.mk_string(zstring(num.get_unsigned())))), m);
            } else {
                return expr_ref(m.mk_true(), m);
            }
        }
    } else {
        return std::nullopt;
    }
}

expr_ref input_rewriter::rewrite_input(expr* e) {
    if (auto res = rewrite_to_code(e); res) { return *res; }
    else { return expr_ref(e, m); }
}


