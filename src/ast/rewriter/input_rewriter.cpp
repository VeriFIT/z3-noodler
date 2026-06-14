/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    input_rewriter.cpp

Abstract:

    Rewriter for processing expressions only when they are loaded from input.

Author:

    Z3 Team 2026

--*/
#include "ast/rewriter/input_rewriter.h"
#include "smt/theory_str_noodler/expr_cases.h"

expr_ref input_rewriter::rewrite_input(expr* e) {
    return expr_ref(e, m);
}


