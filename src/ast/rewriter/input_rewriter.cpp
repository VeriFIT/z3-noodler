#include "ast/rewriter/input_rewriter.h"
#include "smt/theory_str_noodler/expr_cases.h"

/// Rewrites <, <=, >, >=, ==, !=, where one side is str.to_code and other a numeral to str.in_re predicate
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

/// Rewrites <, <=, >, >=, ==, !=, where one side is str.to_int and other a numeral to str.in_re predicate
std::optional<expr_ref> input_rewriter::rewrite_to_int(expr *e) {
    // [0-9]
    expr_ref digits_regex(m_util_s.re.mk_range(m_util_s.str.mk_string("0"), m_util_s.str.mk_string("9")), m);
    // 0*
    expr_ref zero_star(m_util_s.re.mk_star(m_util_s.re.mk_to_re(m_util_s.str.mk_string("0"))), m);
    // complement of [0-9]+
    expr_ref non_valid_number_regex(m_util_s.re.mk_complement(m_util_s.re.mk_plus(digits_regex)), m);

    expr* to_int_arg;
    rational num;
    bool is_num_larger, is_eq;
    if (smt::noodler::expr_cases::is_to_int_leq_or_geq(e, m, m_util_s, m_util_a, to_int_arg, num, is_num_larger)) {
        if (is_num_larger) {
            // (str.to_int to_int_arg) <= num
            if (num < -1) {
                return expr_ref(m.mk_false(), m);
            } else {
                expr_ref final_re = non_valid_number_regex; // case when num is -1
                if (num >= 0) {
                    std::string string_representation_of_num = num.to_string();
                    size_t length_of_num = string_representation_of_num.size();

                    if (length_of_num > 1) {
                        // all numbers whose lenght in decimal representation is shorter than num
                        // 0*[0-9]{1,length_of_num-1}
                        expr_ref re_shorter(m_util_s.re.mk_concat(zero_star, m_util_s.re.mk_loop(digits_regex, 1, length_of_num-1)), m);
                        final_re = m_util_s.re.mk_union(final_re, re_shorter);
                    }

                    // we now encode all numbers of length of num <= num
                    // for example, for num == 4601, we encode (by iterating for all positions):
                    //        - 0*[1-3][0-9][0-9][0-9]
                    //        - 0*4[0-5][0-9][0-9]
                    //        - third position ('0') is skipped
                    //        - 0*460[0-1]
                    // or for num == 190:
                    //        - first position ('1') is skipped
                    //        - 0*1[0-8][0-9]
                    //        - 0*19[0-0]
                    for (size_t pos = 0; pos < length_of_num; ++pos) {
                        char char_on_pos = string_representation_of_num[pos];
                        if (pos == 0 && pos != length_of_num-1 && char_on_pos == '1') { continue; }
                        if (pos != length_of_num-1 && char_on_pos == '0') { continue; }

                        std::string prefix = string_representation_of_num.substr(0, pos); // take the substring before the position pos
                        // 0*<prefix>
                        expr_ref re_case(m_util_s.re.mk_concat(zero_star, m_util_s.re.mk_to_re(m_util_s.str.mk_string(prefix))), m);
                        if (pos == length_of_num-1) {
                            // last position (can be also first): we add [0-<char_on_pos>]
                            re_case = m_util_s.re.mk_concat(re_case, m_util_s.re.mk_range(m_util_s.str.mk_string("0"), m_util_s.str.mk_string(char_on_pos)));
                        } else {
                            if (pos == 0) {
                                // first (but not last) position: we add [1-<char_on_pos-1>]
                                re_case = m_util_s.re.mk_concat(re_case, m_util_s.re.mk_range(m_util_s.str.mk_string("1"), m_util_s.str.mk_string(char_on_pos-1)));
                            } else {
                                // middle position: we add [0-<char_on_pos-1>]
                                re_case = m_util_s.re.mk_concat(re_case, m_util_s.re.mk_range(m_util_s.str.mk_string("0"), m_util_s.str.mk_string(char_on_pos-1)));
                            }
                            // we also add [0-9]^(length of string after pos)
                            re_case = m_util_s.re.mk_concat(re_case, m_util_s.re.mk_loop_proper(digits_regex, length_of_num-1-pos, length_of_num-1-pos));
                        }
                        final_re = m_util_s.re.mk_union(final_re, re_case);
                    }
                }

                return expr_ref(m_util_s.re.mk_in_re(to_int_arg, final_re), m);
            }
        } else {
            // (str.to_int to_int_arg) >= num
            if (num <= -1) {
                return expr_ref(m.mk_true(), m);
            } else {
                std::string string_representation_of_num = num.to_string();
                size_t length_of_num = string_representation_of_num.size();

                // all numbers whose lenght in decimal representation is longer than num
                // 0*[1-9][0-9]{length_of_num,}
                expr_ref re_longer(m_util_s.re.mk_concat(zero_star, m_util_s.re.mk_concat(m_util_s.re.mk_range(m_util_s.str.mk_string("1"), m_util_s.str.mk_string("9")), m_util_s.re.mk_loop(digits_regex, length_of_num))), m);

                expr_ref final_re = re_longer;
                // we now encode all numbers of length of num >= num
                // for example, for num == 4901, we encode (by iterating for all positions):
                //        - 0*[5-9][0-9][0-9][0-9]
                //        - second position ('9') is skipped
                //        - 0*49[1-9][0-9]
                //        - 0*490[1-9]
                // or for num == 995:
                //        - first position ('9') is skipped
                //        - second position ('9') is skipped
                //        - 0*99[5-9]
                for (size_t pos = 0; pos < length_of_num; ++pos) {
                    char char_on_pos = string_representation_of_num[pos];
                    if (pos != length_of_num-1 && char_on_pos == '9') { continue; }

                    std::string prefix = string_representation_of_num.substr(0, pos); // take the substring before the position pos
                    // 0*<prefix>
                    expr_ref re_case(m_util_s.re.mk_concat(zero_star, m_util_s.re.mk_to_re(m_util_s.str.mk_string(prefix))), m);
                    if (pos == length_of_num-1) {
                        // last position: we add [<char_on_pos>-9]
                        re_case = m_util_s.re.mk_concat(re_case, m_util_s.re.mk_range(m_util_s.str.mk_string(char_on_pos), m_util_s.str.mk_string("9")));
                    } else {
                        // before last position: we add [<char_on_pos+1>-9][0-9]^(length of string after pos)
                        re_case = m_util_s.re.mk_concat(re_case, m_util_s.re.mk_range(m_util_s.str.mk_string(char_on_pos+1), m_util_s.str.mk_string("9")));
                        re_case = m_util_s.re.mk_concat(re_case, m_util_s.re.mk_loop_proper(digits_regex, length_of_num-1-pos, length_of_num-1-pos));
                    }
                    final_re = m_util_s.re.mk_union(final_re, re_case);
                }

                return expr_ref(m_util_s.re.mk_in_re(to_int_arg, final_re), m);
            }
        }
    } else if(smt::noodler::expr_cases::is_to_int_num_eq(e, m, m_util_s, m_util_a, to_int_arg, num, is_eq)) {
        expr_ref re(m);
        if (num < -1) {
            // values smaller than -1 cannot be results of str.to_int
            if (is_eq) { return expr_ref(m.mk_false(), m); }
            else { return expr_ref(m.mk_true(), m); }
        } else if (num == -1) {
            re = non_valid_number_regex;
        } else {
            // 0*<num>
            re = m_util_s.re.mk_concat(zero_star, m_util_s.re.mk_to_re(m_util_s.str.mk_string(num.to_string())));
        }
        expr_ref in_re(m_util_s.re.mk_in_re(to_int_arg, re), m);
        if (!is_eq) { in_re = m.mk_not(in_re); }
        return in_re;
    } else {
        return std::nullopt;
    }
}

expr_ref input_rewriter::rewrite_input(expr* e) {
    if (auto res = rewrite_to_code(e); res) { return *res; }
    if (auto res = rewrite_to_int(e); res) { return *res; }
    else { return expr_ref(e, m); }
}


