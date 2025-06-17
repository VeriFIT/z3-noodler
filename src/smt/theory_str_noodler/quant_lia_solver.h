#ifndef _QUANT_LIA_SOLVER_H_
#define _QUANT_LIA_SOLVER_H_

#include "smt/smt_kernel.h"
#include "params/smt_params.h"
#include "smt/smt_context.h"
#include "smt/theory_arith.h"
#include "solver/tactic2solver.h"
#include "smt/smt_solver.h"
#include "tactic/smtlogics/quant_tactics.h"

namespace smt::noodler {
    class quant_lia_solver {
    
    private:
        ast_manager& m;
        bool initialized;
        expr_ref_vector erv;
    
    public:
        quant_lia_solver(ast_manager& m) : m(m), erv(m) {
            initialized=false;
        }

        /**
         * @brief Check is the given length formula is SAT (together with the 
         * formulae from the context).
         * 
         * @param e Length formula
         * @return lbool Satisfiability check result
         */
        lbool check_sat(expr* e) {
            params_ref p;
            
            // parameters used by z3 for quantified LIA formulae
            p.set_sym("string_solver", symbol("none"));
            p.set_bool("mbqi", true);
            p.set_uint("qi_lazy_threshold", 20);
            p.set_double("restart_factor", 1.5);
            p.set_bool("pi_use_database", true);
            p.set_bool("eliminate_bounds", true);

            // another options for a solver: mk_smt_solver(m, p, symbol("LIA")); (no tactic)
            // tactic solver used by z3 to solve quantified LIA formula
            solver* sl = mk_tactic2solver(m, mk_lia_tactic(m, p), p, false, true, false, symbol("ALL"));

            erv.push_back(e);
            sl->assert_expr(erv);
            auto res = sl->check_sat();
            erv.pop_back();

            return res;
        }

        /**
         * @brief Initialize LIA solver. Take input LIA formula from the context and formulae corresponding to the 
         * current assignment and add them to the vector of solved LIA formulae.
         * 
         * @param ctx Current context
         * @param include_ass Include the current assignment from the context?
         */
        void initialize(context& ctx, bool include_ass = true) {
            if(!initialized){
                initialized=true;
                expr_ref_vector Assigns(m);
                ctx.get_assignments(Assigns);
                for (unsigned i = 0; i < ctx.get_num_asserted_formulas(); ++i) {
                    STRACE(str-lia, tout<< "check_sat context from asserted: " << mk_pp(ctx.get_asserted_formula(i),m) << std::endl);
                    assert_expr(ctx.get_asserted_formula(i));
                }
                if (include_ass) {
                    for (auto & e : Assigns){
                        if(ctx.is_relevant(e)) {
                            STRACE(str-lia, tout << "check_sat context from assign: " << mk_pp(e, m) << std::endl);
                            assert_expr(e);
                        }
                    }
                }
            }
        }

        void assert_expr(expr * e) {
            erv.push_back(e);
        }
    };
}

#endif
