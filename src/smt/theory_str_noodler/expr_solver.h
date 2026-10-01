/*
The skeleton of this code was obtained by Yu-Fang Chen from https://github.com/guluchen/z3.
Eternal glory to Yu-Fang.
*/

#ifndef _EXPR_INT_SOLVER_H_
#define _EXPR_INT_SOLVER_H_

#include "params/smt_params.h"
#include "smt/theory_str_noodler/lia_solver.h"

namespace smt::noodler {
    class int_expr_solver : public lia_solver {
        smt_params fp;
    public:
        int_expr_solver(ast_manager& m, smt_params fp, const obj_map<expr, expr*>& predicate_replace):
            lia_solver(m, predicate_replace), fp(fp) {
            this->fp.m_string_solver = symbol("none");
       }

        lbool check_sat(expr* e) override;
    };
}

#endif
