/*
The skeleton of this code was obtained by Yu-Fang Chen from https://github.com/guluchen/z3. 
Eternal glory to Yu-Fang.
*/

#ifndef _EXPR_INT_SOLVER_H_
#define _EXPR_INT_SOLVER_H_

#include "smt/smt_kernel.h"
#include "params/smt_params.h"
#include "smt/smt_context.h"
#include "smt/theory_str_noodler/lia_solver.h"

namespace smt::noodler {
    class int_expr_solver : public lia_solver {
        ast_manager& m;
        bool initialized;
        expr_ref_vector erv;
        expr_ref unsat_core;
        expr_ref model_formula;
        smt_params fp;
    public:
        int_expr_solver(ast_manager& m, smt_params fp): m(m),erv(m),unsat_core(m),model_formula(m),fp(fp){
            this->fp.m_string_solver = symbol("none");
            initialized=false;
       }

        lbool check_sat(expr* e) override;
        void initialize(context& ctx, bool include_assignment = true) override;
        void get_unsat_core(expr_ref& dst) override;
        void assert_expr(expr * e);
        expr_ref get_model() override { return model_formula; }
    };
}

#endif