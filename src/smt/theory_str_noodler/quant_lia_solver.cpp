#include "smt/smt_kernel.h"
#include "smt/theory_arith.h"
#include "solver/tactic2solver.h"
#include "smt/smt_solver.h"
#include "tactic/smtlogics/quant_tactics.h"
#include "smt/theory_str_noodler/quant_lia_solver.h"

namespace smt::noodler {
    lbool quant_lia_solver::check_sat(expr* e) {
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
        solver* sl = mk_tactic2solver(m, mk_lia_tactic(m, p), p, false, true, true, symbol("ALL"));

        expr* e_rw = rewrite_for_external_solver(e);
        erv.push_back(e_rw);
        sl->assert_expr(erv);
        auto res = sl->check_sat();
        expr_ref_vector raw_core(m);
        sl->get_unsat_core(raw_core);
        erv.pop_back();

        reset_result();
        if (res == lbool::l_false) {
            compute_unsat_core(raw_core);
        }
        if (res == lbool::l_true) {
            model_ref mdl;
            sl->get_model(mdl);
            compute_model_formula(e_rw, mdl);
        }

        return res;
    }
}
