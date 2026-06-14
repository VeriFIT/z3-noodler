/*++
Module Name:

    input_rewriter.h

Abstract:

    Rewriter for processing expressions only when they are loaded from input.
    This ensures that custom rewriting rules are applied exactly once to input
    expressions and not to expressions created internally during solving.

--*/
#pragma once

#include "ast/ast.h"
#include "ast/seq_decl_plugin.h"
#include "ast/arith_decl_plugin.h"

/**
 * \brief Input rewriter: applies rewrite rules only to expressions loaded from input.
 *
 * This class is designed to be used at expression load time (in cmd_context::assert_expr)
 * to rewrite expressions exactly once when they are parsed from input. This allows to
 * define rules that should not be used for rewriting internal formulas, such as a rule
 * to replace (= (str.to_code x) 100) with (= x "d"), which would cause problems for
 * noodler string solver if it was applied always.
 */
class input_rewriter {
protected:
    ast_manager&    m;
    seq_util        m_util_s;
    arith_util      m_util_a;

public:
    /**
     * \brief Create an input rewriter with the given manager and parameters.
     *
     * \param m      The AST manager
     */
    input_rewriter(ast_manager& m) : m(m), m_util_s(m), m_util_a(m) { }

    /**
     * \brief Rewrite an expression that came from input.
     *
     * \param e  The expression to rewrite
     */
    expr_ref rewrite_input(expr* e);

private:
    std::optional<expr_ref> rewrite_to_code(expr* e);
};
