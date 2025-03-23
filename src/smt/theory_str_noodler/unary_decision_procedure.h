#ifndef _NOODLER_UNARY_PROCEDURE_H_
#define _NOODLER_UNARY_PROCEDURE_H_

#include "decision_procedure.h"
#include "regex.h"

namespace smt::noodler {

    /**
     * @brief Decision procedure for system of equations containing a single symbol only (no regular constraints, conversions, and others).
     * 
     * The satisfiability of unary system of equations (system of equations over singleton alphabet) is 
     * satisfiable iff the lengths are satisfiable. The model is then constructed as a^n where n is a LIA 
     * solution for a particular variable. It is assumed that the lenght formulas from equations are already
     * in the system and after runnnig this procedure, you should check_len_sat with true formula.
     */
    class UnaryDecisionProcedure : public AbstractDecisionProcedure {
        Formula formula;
        const theory_str_noodler_params& m_params;
        mata::Symbol symbol;

    public:
        UnaryDecisionProcedure(const Formula& equations, const AutAssignment& init_aut_ass, const theory_str_noodler_params& par)
            : formula(equations), m_params(par) {

            auto alph = init_aut_ass.get_alphabet();
            alph.erase(util::get_dummy_symbol());
            VERIFY(alph.size() == 1);
            symbol = *alph.begin();
        }

        lbool compute_next_solution() override { return l_false; };

        std::vector<BasicTerm> get_len_vars_for_model(const BasicTerm& str_var) override {
            return {str_var};
        }

        /**
         * @brief Get model of the variable @p var. Since there is only a single symbol a in the system, the assignment is 
         * generated as a^n, where n is LIA length model of @p var. 
         * 
         * @param var Variable
         * @param arith_model Length assignment to variables
         * @return zstring String assignment
         */
        zstring get_model(BasicTerm var, const std::map<BasicTerm,rational>& arith_model) override;
    };
}

#endif
