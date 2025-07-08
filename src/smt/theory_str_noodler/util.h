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
#include <mata/nft/nft.hh>
#include <mata/nft/strings.hh>

#include "smt/params/smt_params.h"
#include "ast/arith_decl_plugin.h"
#include "ast/seq_decl_plugin.h"
#include "smt/params/theory_str_params.h"
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
     * @brief Get the value of the symbol representing all symbols not ocurring in the formula (i.e. a minterm)
     *
     * Dummy symbol represents all symbols not occuring in the problem. It is needed,
     * because if we have for example disequation x != y and nothing else, we would
     * have no symbols and incorrectly say it is unsat. Similarly, for 'x not in "aaa"
     * and |x| = 3', we would only get symbol 'a' and say (incorrectly) unsat. This
     * symbol however needs to have special semantics, for example to_code should
     * interpret is as anything but used symbols.
     */
    inline mata::Symbol get_dummy_symbol() { static const mata::Symbol DUMMY_SYMBOL = zstring::max_char() + 1; return DUMMY_SYMBOL; }
    inline bool is_dummy_symbol(mata::Symbol sym) { return sym == get_dummy_symbol(); }

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
     */
    BasicTerm get_variable_basic_term(expr* variable);

    void get_len_exprs(expr* ex, const seq_util& m_util_s, ast_manager& m, obj_hashtable<app>& res);

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
     * @brief Assuming that concatenation of automata in @p automata accepts @p word, returns in @p words splitted @p word, where @p word[i] is accepted by @p automata[i]
     *
     * @return boolean indicating whether we can split the @p word to @p automata (true if we can)
     */
    bool split_word_to_automata(const zstring& word, const std::vector<std::shared_ptr<mata::nfa::Nfa>>& automata, std::vector<zstring>& words);

    /**
     * @brief Convert zstring to mata::Word
     * 
     * @param word zstring
     * @return mata::Word 
     */
    mata::Word get_mata_word_zstring(const zstring& word);

    /**
     * @brief Checks if the transducer contains an identity mapping for a word of given length (w,w).
     *
     * This function explores the transducer as a multi-tape automaton and checks if there exists a path
     * from an initial state to a final state such that the sequence of symbols on all tapes is identical
     * (i.e., the transducer realizes the identity relation for some word of the given length).
     *
     * The search is performed using BFS over a state space where each state consists of:
     *   - the current automaton state
     *   - the sequence of symbols read/written on each tape so far
     *
     * The function returns true if such a path exists, false otherwise.
     *
     * @param transducer The NFT (non-deterministic finite transducer) to check.
     * @param length The length of the word to check for identity mapping.
     * @return true if the transducer may contains an identity mapping of the given length, false if there is surely no such mapping.
     */
    bool contains_trans_identity(const mata::nft::Nft& transducer, unsigned length);

    /**
     * @brief Create a vector of inclusions of the form left_sides[i] ⊆ right_sides[i] for all i.
     * 
     * Assumes that @p left_sides and @p right_sides have the same size.
     */
    std::vector<Predicate> create_inclusions_from_multiple_sides(const std::vector<std::vector<BasicTerm>>& left_sides, const std::vector<std::vector<BasicTerm>>& right_sides);

    void replace_dummy_symbol_in_transducer_with(mata::nft::Nft& transducer, const std::set<mata::Symbol>& symbols_to_replace_with);

    bool is_concatenation_of_literals(const std::vector<BasicTerm>& concatenation, zstring& literal);
}

#endif
