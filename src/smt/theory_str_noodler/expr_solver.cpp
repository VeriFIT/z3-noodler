/*
The skeleton of this code was obtained by Yu-Fang Chen from https://github.com/guluchen/z3. 
Eternal glory to Yu-Fang.
*/

#include "expr_solver.h"
#include "ast/ast_pp.h"

namespace smt::noodler {
    lbool int_expr_solver::check_sat(expr* e) {
        TRACE(str_lia, tout << "check_sat start\n";);

        erv.push_back(e);
        lbool r = m_kernel.check(erv);
        erv.pop_back();

        STRACE(str_lia,
            if(r==lbool::l_false){
                tout << "UNSAT core:" << std::endl;
                for(unsigned i=0; i < m_kernel.get_unsat_core_size(); i++) {
                    tout << mk_pp(m_kernel.get_unsat_core_expr(i), m) << std::endl;
                }
            }
        );

        TRACE(str_lia, tout << "check_sat end\n";);
        return r;
    }

    void int_expr_solver::initialize(context& ctx, bool include_ass) {
        if(!initialized){
            initialized=true;
            expr_ref_vector Assigns(m);
            ctx.get_assignments(Assigns);
            for (unsigned i = 0; i < ctx.get_num_asserted_formulas(); ++i) {
                STRACE(str_lia, tout<< "check_sat context from asserted: " << mk_pp(ctx.get_asserted_formula(i),m) << std::endl);
                assert_expr(ctx.get_asserted_formula(i));

            }
            if (include_ass) {
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
        if(!unsat_core){
            erv.push_back(e);
            // m_kernel.assert_expr(e);
        } else {
            erv.push_back(e);
            lbool r = m_kernel.check(erv);
            STRACE(str_lia,
                if(r==lbool::l_false){
                    tout << "UNSAT core:" << std::endl;
                    for(unsigned i=0; i<m_kernel.get_unsat_core_size(); i++) {
                        tout << mk_pp(m_kernel.get_unsat_core_expr(i), m) << std::endl;
                    }
                }
            );
        }
    }
}
