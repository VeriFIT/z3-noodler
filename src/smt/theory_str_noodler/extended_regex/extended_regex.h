#pragma once

#include "constraint_generator.h"
#include "regex_ast.h"
#include "regex_constraint_graph.h"

#include "ast/ast.h"
#include "ast/seq_decl_plugin.h"
#include "params/theory_str_noodler_params.h"
#include "util/symbol.h"
#include "util/zstring.h"

// Extended regexes given by ((_ re.from_regex flavor) pattern). The pattern is parsed by the frontend of its flavor
// into the common AST (regex_ast.h), which is converted into the regex constraint graph (regex_constraint_graph.h),
// from which the string constraints are generated (constraint_generator.h).
namespace smt::noodler::extended_regex {
    /**
     * @brief Parse the @p pattern written in the regex flavor @p flavor into the common AST.
     *
     * @param flavor  The regex flavor, e.g., ecma2020.
     * @param pattern The regex pattern.
     * @return NodeRef The AST of the pattern.
     */
    NodeRef parse(const symbol& flavor, const zstring& pattern);

    /**
     * Top-level class for translating an extended regex into Z3 string constraints.
     *
     * Usage:
     *   1. Construct with the regex flavor and pattern.
     *   2. Call build_rcg() once to parse the regex and build the RCG.
     *   3. Call generate_constraints(target) to produce an SMT2 formula that is satisfiable
     *      iff target matches the regex.
     */
    class RegexConstraintBuilder {
    public:
        RegexConstraintBuilder(ast_manager& m, const symbol& flavor, const zstring& pattern,
                               const theory_str_noodler_params& params)
            : m_manager(m),
              m_flavor(flavor),
              m_pattern(pattern),
              m_params(params),
              m_util_s(m),
              m_fresh_vars(m) { }

        /**
         * @brief Build the Regex Constraint Graph (RCG) from the regex pattern.
         *
         * Parses the pattern into the common AST, removes the capture groups that are never referenced, checks the
         * backreferences to captures inside lookarounds and converts the AST into the RCG. With the engine matching
         * semantics (str.ecma_engine_semantics), the RCG is wrapped in Sigma*, see extended_regex::build_rcg().
         *
         * @return const RegexConstraintGraph& The fully assembled RCG.
         */
        const RegexConstraintGraph& build_rcg();

        /**
         * @brief Generate constraints for the given target string based on the RCG built from the regex pattern.
         *
         * See ConstraintGenerator::generate_constraints().
         *
         * @param target_string The string for which the regex constraints are to be generated.
         * @return expr_ref A ground Z3 expression that is satisfiable iff target matches the regex pattern.
         */
        expr_ref generate_constraints(app* target_string);

        /**
         * @brief Return the fresh Skolem variables introduced during the last generate_constraints() call.
         *
         * Used by the caller to build the existentially-quantified form needed for the negative implication.
         *
         * @return const app_ref_vector& All fresh variables created during DFS (including inner DFS for lookarounds).
         */
        const app_ref_vector& get_fresh_vars() const;

        /**
         * @brief Get the regex of the whole RCG if the RCG is a single path consisting only of match edges, see
         * ConstraintGenerator::get_regular_path_regex().
         *
         * @return app_ref The regex of the RCG, or null if the RCG is not a single path of match edges.
         */
        app_ref get_regular_path_regex();

    private:
        ast_manager& m_manager;
        symbol m_flavor;
        zstring m_pattern;
        const theory_str_noodler_params& m_params;
        seq_util m_util_s;
        RegexConstraintGraph m_graph;

        // Populated by generate_constraints(); holds every fresh Skolem constant introduced during DFS.
        app_ref_vector m_fresh_vars;
    };

    /**
     * @brief Replace each ((_ re.from_regex flavor) pattern) in @p regex by the classical regex of its pattern.
     *
     * The classical regex is the one from RegexConstraintBuilder::get_regular_path_regex(), so its language is the set
     * of strings matching the pattern under the semantics given by @p params.
     *
     * @param regex  The regex in which ((_ re.from_regex flavor) ...) is replaced.
     * @param m      The AST manager.
     * @param params The parameters of the string theory (the engine matching semantics).
     * @return expr_ref The classical regex, or null if some pattern is not a string constant or is not regular
     *                  (e.g., it contains anchors, lookarounds or backreferences).
     */
    expr_ref to_classical_regex(expr* regex, ast_manager& m, const theory_str_noodler_params& params);
}  // namespace smt::noodler::extended_regex
