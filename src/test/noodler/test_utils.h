#include <iostream>
#include <algorithm>
#include <utility>

#include <catch2/catch_test_macros.hpp>
#include <mata/parser/re2parser.hh>

#include "smt/theory_str_noodler/decision_procedure.h"
#include "smt/theory_str_noodler/theory_str_noodler.h"
#include "ast/reg_decl_plugins.h"
#include "ast/rewriter/arith_rewriter.h"
#include "ast/bv_decl_plugin.h"
#include "ast/ast_pp.h"
#include "ast/reg_decl_plugins.h"
#include "ast/rewriter/th_rewriter.h"
#include "model/model.h"
#include "parsers/smt2/smt2parser.h"

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

/**
 * Verifies that a given Z3 formula is satisfiable and matches the expected assignments.
 * 
 * @param m The AST manager used for managing Z3 expressions.
 * @param formula The Z3 formula to be checked.
 * @param assgn A map of variable names to their expected values in the model.
 */
inline void check_lia_model(ast_manager& m, expr* formula, const std::map<std::string, std::string>& assgn) {
    smt_params str_params{};
    int_expr_solver solver(m, str_params);

    // Check if the formula is satisfiable
    REQUIRE(solver.check_sat(formula) == l_true);

    model_ref mdl;
    solver.m_kernel.get_model(mdl);
    unsigned num = mdl->get_num_constants();

    // Iterate through the model's constants and verify assignments
    for (unsigned i = 0; i < num; i++) {
        func_decl * c = mdl->get_constant(i);
        expr * c_i    = mdl->get_const_interp(c);

        auto it = assgn.find(c->get_name().str());
        if(it != assgn.end()) {
            std::ostringstream buffer;
            buffer << mk_pp(c_i, m);
            // Ensure the model's value matches the expected assignment
            REQUIRE(it->second == buffer.str());
        }
    }
}

/**
 * Converts a LenNode formula into a Z3 expression.
 * 
 * @param m The AST manager used for managing Z3 expressions.
 * @param ctx The command context for parsing SMT-LIB2 formulas.
 * @param formula The LenNode formula to be converted.
 * @return A Z3 expression representing the given LenNode formula.
 */
inline expr_ref len_node_to_expr(ast_manager& m, cmd_context& ctx, const LenNode& formula) {
    expr_ref result(m);
    std::ostringstream buffer;

    // Serialize the LenNode formula into SMT-LIB2 format
    write_len_formula_as_smt2(formula, buffer);

    std::istringstream is(buffer.str());
    // Parse the SMT-LIB2 formula into the Z3 context
    REQUIRE(parse_smt2_commands(ctx, is));
    REQUIRE(!ctx.assertions().empty());

    // Retrieve the parsed formula as an expr_ref
    result = ctx.assertions().get(0);
    return result;
}

inline lbool check_lia_sat(const LenNode& formula) {
    ast_manager ast_m;
    reg_decl_plugins(ast_m);
    cmd_context cmd_ctx(false, &ast_m);
    std::ostringstream trash;
    cmd_ctx.set_regular_stream(trash);
    smt_params str_params{};
    int_expr_solver solver(ast_m, str_params);
    return solver.check_sat(len_node_to_expr(ast_m, cmd_ctx, formula));
}

#endif //Z3_TEST_UTILS_H
