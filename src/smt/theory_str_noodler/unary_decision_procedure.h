#ifndef _NOODLER_UNARY_PROCEDURE_H_
#define _NOODLER_UNARY_PROCEDURE_H_

#include "decision_procedure.h"
#include "formula.h"
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
        AutAssignment aut_ass;

    public:
        UnaryDecisionProcedure(const Formula& equations, const AutAssignment& init_aut_ass, const theory_str_noodler_params& par)
            : formula(equations), m_params(par), aut_ass(init_aut_ass) {

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
         * @brief Get the length constraints for the unary system of equations.
         *
         * This method constructs a formula representing the length constraints for the unary system of equations.
         * It includes the lengths of variables and any additional constraints from the predicates in the formula.
         *
         * @return A pair containing the length formula and its precision.
         */
        std::pair<LenNode, LenNodePrecision> get_lengths() override {
            LenNode ln(LenFormulaType::AND);
            ln.succ.push_back(LenNode(LenFormulaType::TRUE));

            for(const BasicTerm& bt : this->aut_ass.get_keys()) {
                ln.succ.push_back(this->aut_ass.get_lengths(bt));
            }
            for(const Predicate& pr : this->formula.get_predicates()) {
                if(pr.is_equation()) {
                    continue;
                } else if(pr.is_inequation()) {
                    // add |LHS| != |RHS| (for equations it is not necessary to add because it was
                    // already added during the axiom saturation before). 
                    ln.succ.push_back(pr.get_formula_eq());
                } else {
                    UNREACHABLE();
                }
                
            }
            STRACE(str-unary-lengths, tout << ln << "\n";);
            return {ln, LenNodePrecision::PRECISE};
        }

        /**
         * @brief Check if the unary decision procedure is suitable for the given formula and automaton assignment.
         *
         * This method verifies whether the formula and automaton assignment meet the requirements for the unary decision procedure.
         * It checks the alphabet size, predicate types, and constraints on variables.
         * 
         * The unary procedure should work for 
         * (i) equations where all variables are \Sigma^*
         * (ii) equations+disequations where all languages are over the same singleton alphabet
         *
         * @param formula The formula to check.
         * @param init_aut_ass The initial automaton assignment.
         * @return True if the unary decision procedure is suitable, false otherwise.
         */
        static bool is_suitable(const Formula& formula, const AutAssignment& init_aut_ass) {
            if(init_aut_ass.get_alphabet().size() != 2) {
                return false;
            }
            if(formula.contains_pred_type(PredicateType::Transducer) || formula.contains_pred_type(PredicateType::NotContains)) {
                return false;
            }
            // it is ok to have only equations with \Sigma^* constraints
            bool only_eqs = !formula.contains_pred_type(PredicateType::Inequation);
            mata::nfa::Nfa sigma_star = init_aut_ass.sigma_star_automaton();
            for(const auto& [bt, aut] : init_aut_ass) {
                if(only_eqs && init_aut_ass.are_equivalent(bt, sigma_star)) {
                    continue;
                }
                auto used_symbols = aut->delta.get_used_symbols();
                if(used_symbols.size() != 1 || util::is_dummy_symbol(used_symbols.back())) {
                    return false;
                } 
            }
            return true;
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
