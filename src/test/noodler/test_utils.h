#include <iostream>
#include <algorithm>
#include <utility>

#include <catch2/catch_test_macros.hpp>
#include <mata/parser/re2parser.hh>

#include "smt/theory_str_noodler/decision_procedure.h"
#include "smt/theory_str_noodler/theory_str_noodler.h"
#include "ast/reg_decl_plugins.h"

#ifndef Z3_TEST_UTILS_H
#define Z3_TEST_UTILS_H

using namespace smt::noodler;

class TheoryStrNoodlerCUT : public theory_str_noodler {
public:
    TheoryStrNoodlerCUT(smt::context &ctx, ast_manager &m, const theory_str_noodler_params& params)
            : theory_str_noodler(ctx, m, params) {}

    using theory_str_noodler::m_util_s, theory_str_noodler::m, theory_str_noodler::m_util_a;
    using theory_str_noodler::mk_str_var_fresh, theory_str_noodler::mk_int_var_fresh, theory_str_noodler::mk_literal;
};

class DecisionProcedureCUT : public DecisionProcedure {
public:
    DecisionProcedureCUT(const Formula &equalities, AutAssignment init_aut_ass,
                         const std::unordered_set<BasicTerm>& init_length_sensitive_vars,
                         ast_manager& m, seq_util& m_util_s, arith_util& m_util_a, const BasicTermEqiv& len_eq_vars, const theory_str_noodler_params& par
    ) : DecisionProcedure(equalities, std::move(init_aut_ass), init_length_sensitive_vars, par, {}) {}

    using DecisionProcedure::compute_next_solution;
    using DecisionProcedure::get_lengths;
    using DecisionProcedure::preprocess;
    using DecisionProcedure::solution;
    using DecisionProcedure::init_computation;
};

// variables have one char names
inline Predicate create_equality(const std::string& left_side, const std::string& right_side) {
    std::vector<BasicTerm> left_side_vars;
    for (char var_name : left_side) {
        left_side_vars.emplace_back(BasicTermType::Variable, std::string(1, var_name));
    }
    std::vector<BasicTerm> right_side_vars;
    for (char var_name : right_side) {
        right_side_vars.emplace_back(BasicTermType::Variable, std::string(1, var_name));
    }
    return Predicate(PredicateType::Equation, { left_side_vars, right_side_vars});
}

// variables have one char names
inline Predicate create_transducer(const mata::nft::Nft& transducer, const std::string& input, const std::string& output) {
    std::vector<BasicTerm> input_vars;
    for (char var_name : input) {
        input_vars.emplace_back(BasicTermType::Variable, std::string(1, var_name));
    }
    std::vector<BasicTerm> output_vars;
    for (char var_name : output) {
        output_vars.emplace_back(BasicTermType::Variable, std::string(1, var_name));
    }
    return Predicate(PredicateType::Transducer, { input_vars, output_vars}, std::make_shared<mata::nft::Nft>(transducer));
}


inline BasicTerm get_var(char var) {
    return { BasicTermType::Variable, std::string(1, var) };
}

inline std::shared_ptr<mata::nfa::Nfa> regex_to_nfa(const std::string& regex) {
    mata::nfa::Nfa aut;
    mata::parser::create_nfa(&aut, regex);
    return std::make_shared<mata::nfa::Nfa>(aut);
}

inline std::map<BasicTerm, expr_ref> create_var_map(const std::unordered_set<BasicTerm>& vars, ast_manager& m, seq_util& m_util_s) {
    std::map<BasicTerm, expr_ref> ret;

    for(const BasicTerm& v : vars) {
        expr_ref var(m_util_s.mk_skolem(symbol(v.get_name().encode()), 0, nullptr, m_util_s.mk_string_sort()), m);
        ret.insert({v, var});
    }

    return ret;
}

#endif //Z3_TEST_UTILS_H
