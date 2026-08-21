/*
The skeleton of this code was obtained by Yu-Fang Chen from https://github.com/guluchen/z3. 
Eternal glory to Yu-Fang.
*/

#include "expr_solver.h"
#include "util.h"
#include "ast/ast_pp.h"

namespace smt::noodler {
    lbool int_expr_solver::check_sat(expr* e) {
        TRACE(str_lia, tout << "check_sat start\n";);

        erv.push_back(e);
        kernel solver(m, fp);
        lbool r = solver.check(erv);
        erv.pop_back();

        unsat_core = m.mk_true();
        if(r==lbool::l_false){
            for (unsigned i = 0; i < solver.get_unsat_core_size(); ++i) {
                unsat_core = m.mk_and(unsat_core, solver.get_unsat_core_expr(i));
            }
            STRACE(str_lia, tout << "UNSAT core:" << std::endl << mk_pp(unsat_core, m));
        }

        model_formula = m.mk_true();
        if (r == lbool::l_true) {
            model_ref mdl;
            solver.get_model(mdl);
            
            struct collect_vars {
                ast_manager &m;
                expr_ref_vector vars;
                arith_util m_util_a;
                seq_util m_util_s;

                collect_vars(ast_manager &m) : m(m), vars(m), m_util_a(m), m_util_s(m) {}
                void operator()(expr* e) {
                    if (m_util_s.str.is_length(e) || (!m_util_s.is_string(e->get_sort()) && util::is_variable(e))) {
                        vars.push_back(e);
                    }
                }
            };
            collect_vars cv(m);
            for_each_expr(cv, e);
            for (expr* v : cv.vars) {
                expr_ref res(m);
                mdl->eval_expr(v, res);
                STRACE(str_lia, tout << "Model for " << mk_pp(v, m) << " is " << mk_pp(res, m) << std::endl;);
                model_formula = m.mk_and(model_formula, m.mk_eq(v, res));
            }
        }

        TRACE(str_lia, tout << "check_sat end\n";);
        return r;
    }

    void int_expr_solver::initialize(context& ctx, bool include_assignment) {
        if(!initialized){
            initialized=true;
            expr_ref_vector Assigns(m);
            ctx.get_assignments(Assigns);
            for (unsigned i = 0; i < ctx.get_num_asserted_formulas(); ++i) {
                STRACE(str_lia, tout<< "check_sat context from asserted: " << mk_pp(ctx.get_asserted_formula(i),m) << std::endl);
                assert_expr(ctx.get_asserted_formula(i));

            }
            if (include_assignment) {
                for (auto & e : Assigns){
                    if(ctx.is_relevant(e)) {
                        STRACE(str_lia, tout << "check_sat context from assign: " << mk_pp(e, m) << std::endl);
                        assert_expr(e);
                    }
                }
            }
        }
    }

    void int_expr_solver::assert_expr(expr * e) {
        erv.push_back(e);
    }

    void int_expr_solver::get_unsat_core(expr_ref& dst) {
        dst = unsat_core;
    }
}
