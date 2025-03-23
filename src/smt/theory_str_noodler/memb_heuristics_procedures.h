#ifndef _NOODLER_MEMB_HEURISTICS_PROCEDURES_H_
#define _NOODLER_MEMB_HEURISTICS_PROCEDURES_H_

#include "decision_procedure.h"
#include "regex.h"

namespace smt::noodler {

    /**
     * @brief Decision procedure for one regex membership contraint
     * 
     * It uses some heuristics to check if the regex is universal/empty
     * which can then be easily used to decide if the contraint holds.
     * If the heuristics are not enough, for the case we have `x not in RE`
     * we create the automaton for RE and check if it is equal to universal
     * automaton, which should be better than complementation, as it can blow up
     */
    class MembHeuristicProcedure : public AbstractDecisionProcedure {
        BasicTerm var;
        expr_ref regex;
        bool is_regex_positive;
        const seq_util& m_util_s;
        const ast_manager& m;
        bool produce_model;
        std::unordered_set<BasicTerm> init_length_vars {};

        std::optional<zstring> model;
    public:
        MembHeuristicProcedure(BasicTerm var, expr_ref regex, bool is_regex_positive, const seq_util& m_util_s, const ast_manager& m, bool produce_model)
            : var(var), regex(regex), is_regex_positive(is_regex_positive), m_util_s(m_util_s), m(m), produce_model(produce_model) {}

        lbool compute_next_solution() override;

        std::vector<BasicTerm> get_len_vars_for_model(const BasicTerm& str_var) override {
            // heuristic should be used only if we do not have length vars, so nothing is needed
            return {};
        }

        zstring get_model(BasicTerm var, const std::map<BasicTerm,rational>& arith_model) override;

        /**
         * @brief Get the length sensitive variables
         */
        const std::unordered_set<BasicTerm>& get_init_length_sensitive_vars() const override {
            return this->init_length_vars;
        }
    };

    class MultMembHeuristicProcedure : public AbstractDecisionProcedure {
        std::map<BasicTerm, std::vector<std::pair<bool,app*>>> var_to_list_of_regexes_and_complement_flag;
        regex::Alphabet alph;
        const seq_util& m_util_s;
        const ast_manager& m;
        bool produce_model;
        std::unordered_set<BasicTerm> init_length_vars {};

        std::map<BasicTerm, zstring> models;
    public:
        MultMembHeuristicProcedure(std::map<BasicTerm, std::vector<std::pair<bool,app*>>> var_to_list_of_regexes_and_complement_flag, regex::Alphabet alph, const seq_util& m_util_s, const ast_manager& m, bool produce_model)
            : var_to_list_of_regexes_and_complement_flag(var_to_list_of_regexes_and_complement_flag), alph(alph), m_util_s(m_util_s), m(m), produce_model(produce_model) {}

        lbool compute_next_solution() override;

        std::vector<BasicTerm> get_len_vars_for_model(const BasicTerm& str_var) override {
            // heuristic should be used only if we do not have length vars, so nothing is needed
            return {};
        }

        zstring get_model(BasicTerm var, const std::map<BasicTerm,rational>& arith_model) override;

        /**
         * @brief Get the length sensitive variables
         */
        const std::unordered_set<BasicTerm>& get_init_length_sensitive_vars() const override {
            return this->init_length_vars;
        }
    };
}

#endif
