#include <cassert>

#include "ast/ast_pp.h"

#include "expr_cases.h"

namespace smt::noodler::expr_cases {

bool is_contains_index(expr* e, expr*& ind, ast_manager& m, seq_util& m_util_s, arith_util& m_util_a) {
    // e.g. (str.contains (str.substr value2 0 (+ n (str.indexof value2 "A" 0))) "A")
    expr *subs = nullptr, *val = nullptr, *val_ind = nullptr, *str = nullptr, *str_ind = nullptr, *offset_ind = nullptr;
    if(m_util_s.str.is_contains(e, subs, val)) {     // subs = (str.substr value2 0 (+ n (str.indexof value2 "A" 0)))
        expr *subb1 = nullptr, *subb2 = nullptr, *num = nullptr;
        rational num_val; //n
        if(m_util_s.str.is_extract(subs, str, subb1, subb2)) {
            if(m_util_a.is_zero(subb1) && m_util_a.is_add(subb2, num, ind) && m_util_a.is_numeral(num, num_val) && num_val.get_int32() > 0) { 
                if(m_util_s.str.is_index(ind, str_ind, val_ind) || (m_util_s.str.is_index(ind, str_ind, val_ind, offset_ind) && m_util_a.is_zero(offset_ind))) {
                    if(str != str_ind || val != val_ind) {
                        return false;
                    }
                    return true;
                }
            }
        }
    }
    return false;
}

bool is_replace_indexof(expr* rpl_str, expr* rpl_find, ast_manager& m, seq_util& m_util_s, arith_util& m_util_a, expr*& ind) {
    expr* sub_str = nullptr, *sub_start = nullptr, *sub_len = nullptr;

    if(m_util_s.str.is_extract(rpl_str, sub_str, sub_start, sub_len)) {
        expr*ind_str = nullptr, *ind_find = nullptr, *ind_start = nullptr, *add = nullptr;
        rational one(1);
        if(m_util_a.is_zero(sub_start) && m_util_a.is_add(sub_len, add, ind) && m_util_a.is_numeral(add, one) && m_util_s.str.is_index(ind, ind_str, ind_find, ind_start) && one.get_int32() == 1) {
            if(ind_find != rpl_find || sub_str != ind_str || !m_util_a.is_zero(ind_start)) {
                return false;
            }
            return true;
        }
    }
    return false;
} 

bool is_indexof_add(expr* e, expr* index_str, ast_manager& m, seq_util& m_util_s, arith_util& m_util_a, expr*& val, expr*& ind_find) {
    expr * ind = nullptr, *ind_str = nullptr, *ind_start = nullptr;
    if(m_util_a.is_add(e, val, ind) && m_util_s.str.is_index(ind, ind_str, ind_find, ind_start)) {
        if(ind_str != index_str) {
            return false;
        }
        return true;
    }
    return false;
}

bool is_one_add_indexof_string(expr* e, expr* index_str, ast_manager& m, seq_util& m_util_s, arith_util& m_util_a, zstring& ind_find) {
    expr* val, *ind_find_expr;
    rational r;
    return (is_indexof_add(e, index_str, m, m_util_s, m_util_a, val, ind_find_expr) && m_util_a.is_one(val) && m_util_s.str.is_string(ind_find_expr, ind_find));
}

bool is_to_int_num_eq(expr* e, ast_manager& m, seq_util& m_util_s, arith_util& m_util_a, expr*& to_int_arg, rational& num) {
    expr* left = nullptr, *right = nullptr;
    if(m.is_eq(e, left, right)) {
        if(m_util_a.is_numeral(left, num) && num.is_int() && m_util_s.str.is_stoi(right, to_int_arg)) {
            return true;
        }
        if(m_util_a.is_numeral(right, num) && num.is_int() && m_util_s.str.is_stoi(left, to_int_arg)) {
            return true;
        }
    }
    return false;
}

bool is_to_code_num_eq(expr* e, ast_manager& m, seq_util& m_util_s, arith_util& m_util_a, expr*& to_code_arg, rational& num, bool& is_eq) {
    expr* left = nullptr, *right = nullptr, *not_argument = nullptr;
    if(m.is_eq(e, left, right)) {
        is_eq = true;
    } else if (m.is_distinct(e, left, right) || (m.is_not(e, not_argument) && m.is_eq(not_argument, left, right))) {
        is_eq = false;
    } else {
        return false;
    }

    if(m_util_a.is_numeral(left, num) && num.is_int() && m_util_s.str.is_to_code(right, to_code_arg)) {
        return true;
    } else if(m_util_a.is_numeral(right, num) && num.is_int() && m_util_s.str.is_to_code(left, to_code_arg)) {
        return true;
    } else {
        return false;
    }
}

bool is_sum_of_lens(expr* e, ast_manager& m, seq_util& m_util_s, arith_util& m_util_a, expr_ref_vector& len_vars) {
    expr *arg = nullptr, *arg2;
    len_vars = expr_ref_vector(m);
    expr_ref_vector argref(m);
    if (m_util_s.str.is_length(e, arg)) { // str.len(x), we return x
        len_vars.push_back(arg);
        return true;
    } else if (m_util_a.is_mul(e, arg, arg2)) {
        // check if of the form N*str.len(x), where N is a positive number
        rational val;
        if (((m_util_a.is_numeral(arg, val) && is_sum_of_lens(arg2, m, m_util_s, m_util_a, argref)) ||
             (m_util_a.is_numeral(arg2, val) && is_sum_of_lens(arg, m, m_util_s, m_util_a, argref))) && val > 0) {
            // we return concatenation xxxx...x, with x being N times in the concatenation
            for (rational i{0}; i < val; ++i) {
                for (expr* var : argref) {
                    len_vars.push_back(var);
                }
            }
            return true;
        } else {
            return false;
        }
    } else if (m_util_a.is_add(e)) {
        // check if it a summation of str.len (using recursion)
        for (unsigned i = 0; i < to_app(e)->get_num_args(); ++i) {
            arg = to_app(e)->get_arg(i);
            if (is_sum_of_lens(arg, m, m_util_s, m_util_a, argref)) {
                for (expr* var : argref) {
                    len_vars.push_back(var);
                }
            } else {
                return false;
            }
        }
        return true;
    }
    return false;
}

bool is_len_num_eq(expr* e, ast_manager& m, seq_util& m_util_s, arith_util& m_util_a, expr_ref_vector& len_arg, rational& num) {
    expr* left = nullptr, *right = nullptr;
    if(m.is_eq(e, left, right)) {
        expr* non_num_side;
        if (m_util_a.is_numeral(left, num)) {
            non_num_side = right;
        } else if (m_util_a.is_numeral(right, num)) {
            non_num_side = left;
        } else {
            return false;
        }

        if (is_sum_of_lens(non_num_side, m, m_util_s, m_util_a, len_arg)) {
            return true;
        }
    }
    return false;
}

bool is_len_num_leq_or_geq(expr* e, ast_manager& m, seq_util& m_util_s, arith_util& m_util_a, expr_ref_vector& len_arg, rational& num, bool& num_is_larger) {
    STRACE(str_is_len_num_leq_or_geq, tout << mk_pp(e, m) << std::endl;);
    expr* less = nullptr, *more = nullptr, *e_not = nullptr;
    bool strictly_less;
    if (m_util_a.is_lt(e, less, more) || (m.is_not(e, e_not) && m_util_a.is_ge(e_not, less, more)) ||
        m_util_a.is_gt(e, more, less) || (m.is_not(e, e_not) && m_util_a.is_le(e_not, more, less))) {
        strictly_less = true;
    } else if (m_util_a.is_le(e, less, more) || (m.is_not(e, e_not) && m_util_a.is_gt(e_not, less, more)) ||
               m_util_a.is_ge(e, more, less) || (m.is_not(e, e_not) && m_util_a.is_lt(e_not, more, less))) {
        strictly_less = false;
    } else {
        return false;
    }
    
    if (m_util_a.is_numeral(more, num) && num.is_int() && is_sum_of_lens(less, m, m_util_s, m_util_a, len_arg)) {
        if (strictly_less) {
            --num;
        }
        num_is_larger = true;
        return true;
    } else if (m_util_a.is_numeral(less, num) && num.is_int() && is_sum_of_lens(more, m, m_util_s, m_util_a, len_arg)) {
        if (strictly_less) {
            ++num;
        }
        num_is_larger = false;
        return true;
    } else {
        return false;
    }
}

bool is_indexof_at(expr * index_param, expr* index_str, ast_manager& m, seq_util& m_util_s) {
    expr *at_str, *at_pos;
    if (m_util_s.str.is_at(index_param, at_str, at_pos) && index_str == at_str) {
        return true;
    }
    return false;
}

bool is_num_plus_len(expr* val, expr* s, ast_manager& m, seq_util& m_util_s, arith_util& m_util_a, rational& num_res) {
    expr *num, *len, *str;
    return (m_util_a.is_add(val, num, len) && m_util_s.str.is_length(len, str) && str == s && m_util_a.is_numeral(num, num_res));
}

bool is_to_code_leq_or_geq(expr* e, ast_manager& m, seq_util& m_util_s, arith_util& m_util_a, expr*& to_code_arg, rational& num, bool& num_is_larger) {
    expr* less = nullptr, *more = nullptr, *e_not = nullptr;
    bool strictly_less;
    if (m_util_a.is_lt(e, less, more) || (m.is_not(e, e_not) && m_util_a.is_ge(e_not, less, more)) ||
        m_util_a.is_gt(e, more, less) || (m.is_not(e, e_not) && m_util_a.is_le(e_not, more, less))) {
        strictly_less = true;
    } else if (m_util_a.is_le(e, less, more) || (m.is_not(e, e_not) && m_util_a.is_gt(e_not, less, more)) ||
               m_util_a.is_ge(e, more, less) || (m.is_not(e, e_not) && m_util_a.is_lt(e_not, more, less))) {
        strictly_less = false;
    } else {
        return false;
    }

    if (m_util_a.is_numeral(more, num) && num.is_int() && m_util_s.str.is_to_code(less, to_code_arg)) {
        if (strictly_less) {
            --num;
        }
        num_is_larger = true;
        return true;
    } else if (m_util_a.is_numeral(less, num) && num.is_int() && m_util_s.str.is_to_code(more, to_code_arg)) {
        if (strictly_less) {
            ++num;
        }
        num_is_larger = false;
        return true;
    } else {
        return false;
    }
}

bool has_quantifier(expr* e, ast_manager& m) {
    if (is_quantifier(e)) {
        return true;
    }
    if (is_app(e)) {
        app *app_term = to_app(e);
        unsigned num_args = app_term->get_num_args();
        for (unsigned i = 0; i < num_args; i++) {
            if (has_quantifier(app_term->get_arg(i), m)) {
                return true;
            }
        }
    }

    return false;
}

}
