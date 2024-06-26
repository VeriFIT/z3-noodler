#ifndef _NOODLER_UTIL_H_
#define _NOODLER_UTIL_H_

#include <functional>
#include <list>
#include <set>
#include <stack>
#include <map>
#include <memory>
#include <queue>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "smt/params/smt_params.h"
#include "ast/arith_decl_plugin.h"
#include "ast/seq_decl_plugin.h"
#include "smt/params/theory_str_params.h"
#include "smt/smt_kernel.h"
#include "smt/smt_theory.h"
#include "smt/smt_arith_value.h"
#include "util/scoped_vector.h"
#include "util/union_find.h"
#include "ast/rewriter/seq_rewriter.h"
#include "ast/rewriter/th_rewriter.h"

#include "formula.h"
#include "aut_assignment.h"

// FIXME most if not all these functions should probably be in theory_str_noodler

namespace smt::noodler::util {
    using expr_pair = std::pair<expr_ref, expr_ref>;
    using expr_pair_flag = std::tuple<expr_ref, expr_ref, bool>;

    /**
     * Throws error and select which class to throw based on debug (if we are
     * debugging, we do not want z3 to catch our error, if we are not debugging
     * we want z3 to catch it and return unknown).
     * 
     * @param errMsg Error message
     */
    void throw_error(std::string errMsg);

    /**
    Get variables from a given expression @p ex. Append to the output parameter @p res.
    @param ex Expression to be checked for variables.
    @param m_util_s Seq util for AST
    @param m AST manager
    @param[out] res Vector of found variables (may contain duplicities).
    @param pred_map predicate to variable mapping
    */
    void get_str_variables(expr* ex, const seq_util& m_util_s, const ast_manager& m, obj_hashtable<expr>& res, obj_map<expr, expr*>* pred_map=nullptr);

    /**
     * Check whether an @p expression is a string variable.
     *
     * Function checks only the top-level expression and is not recursive.
     * Regex variables do not count as string variables.
     * @param expression Expression to check.
     * @return True if @p expression is a variable, false otherwise.
     */
    bool is_str_variable(const expr* expression, const seq_util& m_util_s);

    /**
     * Check whether an @p expression is any kind of variable (string, regex, integer).
     *
     * Function checks only the top-level expression and is not recursive.
     * @param expression Expression to check.
     * @return True if @p expression is a variable, false otherwise.
     */
    bool is_variable(const expr* expression);

    /**
     * Get variable names from a given expression @p ex. Append to the output parameter @p res.
     * @param[in] ex Expression to be checked for variables.
     * @param[in] m_util_s Seq util for AST.
     * @param[in] m AST manager.
     * @param[out] res Vector of found variables (may contain duplicities).
     */
    void get_variable_names(expr* ex, const seq_util& m_util_s, const ast_manager& m, std::unordered_set<std::string>& res);

    /**
     * Get dummy symbols.
     *
     * @param[in] new_symb_num Number of added symbols.
     * @param[out] symbols_to_append_to Set of symbols where dummy symbols are appended to.
     * @return Set of dummy symbols.
     */
    std::set<uint32_t> get_dummy_symbols(size_t new_symb_num, std::set<uint32_t>& symbols_to_append_to);

    /**
     * Collect basic terms (vars, literals) from a concatenation @p ex. Append the basic terms to the output parameter
     *  @p terms.
     * @param ex Expression to be checked for basic terms.
     * @param m_util_s Seq util for AST
     * @param pred_replace Replacement of predicate and functions
     * @param[out] terms Vector of found BasicTerm (in right order).
     *
     * TODO: Test.
     */
    void collect_terms(app* ex, ast_manager& m, const seq_util& m_util_s, obj_map<expr, expr*>& pred_replace,
                       std::map<BasicTerm, expr_ref>& var_name, std::vector<BasicTerm>& terms
    );

    /**
     * Convert variable in @c expr form to @c BasicTerm.
     * @param variable Variable to be converted to @c BasicTerm.
     * @return Passed @p variable as a @c BasicTerm
     *
     * TODO: Test.
     */
    BasicTerm get_variable_basic_term(expr* variable);

    void get_len_exprs(app* ex, const seq_util& m_util_s, const ast_manager& m, obj_hashtable<app>& res);

    /**
     * @brief Create a fresh Z3 int variable with a given @p name followed by a unique suffix.
     *
     * @param name Infix of the name (rest is added to get a unique name)
     * FIXME same function is in theory_str_noodler, decide which to keep
     */
    static expr_ref mk_int_var_fresh(const std::string& name, ast_manager& m, arith_util& m_util_a) {
        app* fresh_var = m.mk_fresh_const(name, m_util_a.mk_int(), false);
        // TODO maybe we need to internalize and mark as relevant, so that arith solver can handle it (see mk_int_var in theory_str.h of z3str3)
        return expr_ref(fresh_var, m);
    }
    
    /**
     * @brief Create a fresh Z3 string variable with a given @p name followed by a unique suffix.
     *
     * @param name Infix of the name (rest is added to get a unique name)
     * FIXME same function is in theory_str_noodler, decide which to keep
     */
    static expr_ref mk_str_var_fresh(const std::string& name, ast_manager& m, seq_util& m_util_s) {
        app* fresh_var = m.mk_fresh_const(name, m_util_s.mk_string_sort(), false);
        return expr_ref(fresh_var, m);
    }

    /**
     * @brief Get Z3 int var with exact given @p name
     *
     * @param name Name of the var
     */
    static expr_ref mk_int_var(const std::string& name, ast_manager& m, arith_util& m_util_a) {
        app* var = m.mk_const(name, m_util_a.mk_int());
        // TODO maybe we need to internalize and mark as relevant, so that arith solver can handle it (see mk_int_var in theory_str.h of z3str3)
        return expr_ref(var, m);
    }

    /**
     * @brief Get Z3 string var with exact given @p name
     *
     * @param name Name of the var
     */
    static expr_ref mk_str_var(const std::string& name, ast_manager& m, seq_util& m_util_s) {
        app* var = m.mk_const(name, m_util_s.mk_string_sort());
        return expr_ref(var, m);
    }

    /**
     * @brief Create a fresh noodler (BasicTerm) variable with a given @p name followed by a unique suffix.
     * 
     * The suffix contains a number which is incremented for each use of this function for a given @p name
     * 
     * @param name Infix of the name (rest is added to get a unique name)
     */
    inline BasicTerm mk_noodler_var_fresh(const std::string& name) {
        // TODO kinda ugly, function is defined in header and have static variable
        // so it needs to be inline, maybe we should define some variable handler class
        static std::map<std::string,unsigned> next_id_of_name;
        return BasicTerm{BasicTermType::Variable, name + std::string("!n") + std::to_string((next_id_of_name[name])++)};
    }

    /**
     * @brief Check whether the expression @p val is of the form ( @p num_res ) + (len @p s ).
     * 
     * @param val Expression to be checked
     * @param s String term with length
     * @param m ast manager
     * @param m_util_s string ast util
     * @param m_util_a arith ast util
     * @param[out] num_res expression to be substracked from length term
     * @return Is of the form.
     */
    bool is_len_sub(expr* val, expr* s, ast_manager& m, seq_util& m_util_s, arith_util& m_util_a, expr*& num_res);

    /**
     * @brief Convert Length node to z3 length formula
     *
     * @param node Length node
     * @param variable_map mapping of variables(BasicTerms) to the corresponding z3 variables(expr_ref)
     * @param m ast manager
     * @param m_util_s string ast util
     * @param m_util_a arith ast util
     * @return expr_ref
     */
    expr_ref len_to_expr(const LenNode &node, const std::map<BasicTerm, expr_ref>& variable_map, ast_manager &m, seq_util& m_util_s, arith_util& m_util_a);

}

#endif
