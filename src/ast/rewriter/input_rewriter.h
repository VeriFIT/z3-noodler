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
 * to rewrite expressions exactly once when they are parsed from input. This prevents
 * rewriting overhead during the solving process since expressions created internally
 * during solving will not be rewritten.
 *
 * Usage:
 *   input_rewriter rewriter(manager);
 *   expr_ref input_expr = ...;  // expression from parsed input
 *   rewriter.rewrite_input(input_expr);
 *
 * To add custom input-only rewriting rules:
 *   1. Add a method to apply your custom rules
 *   2. Call it from rewrite_input() when appropriate parameter is set
 *   3. Extend this class for domain-specific rewriting
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
