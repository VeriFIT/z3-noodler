#ifndef _QUANT_LIA_SOLVER_H_
#define _QUANT_LIA_SOLVER_H_

#include "smt/theory_str_noodler/lia_solver.h"

namespace smt::noodler {
    class quant_lia_solver : public lia_solver {
    public:
        quant_lia_solver(ast_manager& m, const obj_map<expr, expr*>& predicate_replace):
            lia_solver(m, predicate_replace) {
        }

        /**
         * @brief Check is the given length formula is SAT (together with the
         * formulae from the context).
         *
         * @param e Length formula
         * @return lbool Satisfiability check result
         */
        lbool check_sat(expr* e) override;
    };
}

#endif
