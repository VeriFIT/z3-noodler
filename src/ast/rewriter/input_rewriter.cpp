#include <unordered_set>

#include "ast/rewriter/input_rewriter.h"
#include "smt/theory_str_noodler/expr_cases.h"

/**
 * @brief Add special axioms for length (in)equations. In particular
 * - for (len s) == 10 create s \in \Sigma^10
 * - for (len s) <= 10 create s \in re.loop(0, 10)
 * - for 10 <= (len s) create s \in re.loop(10, \inf)
 * (len s) can be potentially any LIA formula where the "variables" are length constraints and there is no minus
 */
std::optional<expr_ref> input_rewriter::rewrite_len(expr* e) {
    // number bound for the conversion of length constraints into regex constraints.
    // For higher values this conversion could not be beneficial as we would work with 
    // big automata in the decision procedure.
    const int MAX_NUM = 64; 
    const unsigned MAX_VARS = 4;

    expr_ref full_char(m_util_s.re.mk_full_char(m_util_s.re.mk_re(m_util_s.mk_string_sort())), m);
    auto create_and_of_equals_to_empty_string = [this](expr_ref_vector& len_vars_with_repetition) {
        std::unordered_set<expr*> used_len_vars;
        expr_ref_vector eqs(m);
        for (expr* var : len_vars_with_repetition) {
            if (!used_len_vars.contains(var)) {
                eqs.push_back(m.mk_eq(var, m_util_s.str.mk_string(zstring())));
                used_len_vars.insert(var);
            }
        }
        return expr_ref(m.mk_and(eqs), m);
    };

    rational val;
    bool val_is_larger;
    expr_ref_vector len_arg(m);
    if (smt::noodler::expr_cases::is_len_num_eq(e, m, m_util_s, m_util_a, len_arg, val) && val < MAX_NUM) {
        if (val < 0) {
            // The sum of lengths should be equal to negative number, which is not possible.
            return expr_ref(m.mk_false(), m);
        } else if (val == 0) {
            // we know that concatenation of vars in len_arg must be empty string,
            // which means every variable in len_arg must be equal to empty string
            create_and_of_equals_to_empty_string(len_arg);
        } else if (len_arg.size() <= MAX_VARS) {
            expr_ref re(full_char, m);
            for(rational i{1}; i < val; i++) {
                re = m_util_s.re.mk_concat(re, full_char);
            }
            return expr_ref(m_util_s.re.mk_in_re(m_util_s.str.mk_concat(len_arg, nullptr), re), m);
        }
    } else if (smt::noodler::expr_cases::is_len_num_leq_or_geq(e, m, m_util_s, m_util_a, len_arg, val, val_is_larger) && val < MAX_NUM) {
        if (val < 0) {
            if (val_is_larger) {
                // The sum of lengths should be less than or equal than negative number, which is not possible.
                return expr_ref(m.mk_false(), m);
            } else {
                // if val is smaller than len_arg, then this expression just say that the length of len_arg is larger than minus number -> it is useless
                return expr_ref(m.mk_true(), m);
            }
        } else if (val == 0) {
            if (val_is_larger) {
                // the sum of lengths <= 0 --> every var must be equal to empty string
                create_and_of_equals_to_empty_string(len_arg);
            } else {
                // if val is smaller than len_arg, then this expression just say that the length of len_arg is larger or equal than 0 -> it is useless
                return expr_ref(m.mk_true(), m);
            }
        } else if (len_arg.size() <= MAX_VARS) {
            expr_ref re(
                val_is_larger ? 
                    m_util_s.re.mk_loop(m_util_s.re.mk_full_char(nullptr), m_util_a.mk_int(0), m_util_a.mk_int(val)) :
                    m_util_s.re.mk_loop(m_util_s.re.mk_full_char(nullptr), m_util_a.mk_int(val)),
                m
            );
            return expr_ref(m_util_s.re.mk_in_re(m_util_s.str.mk_concat(len_arg, nullptr), re), m);
        }
    }
    return std::nullopt;
}

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
    else if (auto res = rewrite_len(e); res) { return *res; }
    else { return expr_ref(e, m); }
}


