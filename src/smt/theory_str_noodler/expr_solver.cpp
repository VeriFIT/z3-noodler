/*
The skeleton of this code was obtained by Yu-Fang Chen from https://github.com/guluchen/z3.
Eternal glory to Yu-Fang.
*/

#include "smt/smt_kernel.h"
#include "expr_solver.h"

namespace smt::noodler {
    lbool int_expr_solver::check_sat(expr* e) {
        TRACE(str_lia, tout << "check_sat start\n";);

        expr* e_rw = rewrite_for_external_solver(e);
        erv.push_back(e_rw);
        kernel solver(m, fp);
        lbool r = solver.check(erv);
        erv.pop_back();

        reset_result();
        if (r == lbool::l_false) {
            expr_ref_vector raw_core(m);
            for (unsigned i = 0; i < solver.get_unsat_core_size(); ++i) {
                raw_core.push_back(solver.get_unsat_core_expr(i));
            }
            compute_unsat_core(raw_core);
        }
        if (r == lbool::l_true) {
            model_ref mdl;
            solver.get_model(mdl);
            compute_model_formula(e_rw, mdl);
        }

        TRACE(str_lia, tout << "check_sat end\n";);
        return r;
    }
}
