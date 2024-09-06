#ifndef _NOODLER_EXPR_CASES_H_
#define _NOODLER_EXPR_CASES_H_

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

namespace smt::noodler::expr_cases {

/**
 * @brief Check if the given contraint @p e is of the form 
 * (str.contains (str.substr val 0 (+ n (str.indexof val S 0))) S) where n > 0
 * 
 * @param e Constraint to be checked
 * @param ind Extracted (str.indexof val S 0) term
 * @param m Ast manager
 * @param m_util_s string ast util
 * @param m_util_a arith ast util
 * @return true <-> if of the particular form.
 */
bool is_contains_index(expr* e, expr*& ind, ast_manager& m, seq_util& m_util_s, arith_util& m_util_a);

/**
 * @brief Check if the given constraint @p rpl_str is of the form 
 * (str.substr s 0 (1 + str.indexof s ( @p rpl_find ) 0))
 * 
 * @param rpl_str Constraint of the replace
 * @param rpl_find Replace find
 * @param m Ast manager
 * @param m_util_s string ast util
 * @param m_util_a arith ast util
 * @param[out] ind Extracted (str.indexof s ( @p rpl_find ) 0)
 * @return true <-> if of the particular form.
 */
bool is_replace_indexof(expr* rpl_str, expr* rpl_find, ast_manager& m, seq_util& m_util_s, arith_util& m_util_a, expr*& ind);

/**
 * @brief Check if the given contraint @p e is of the form 
 * (( @p val ) + (str.indexof ( @p index_str ) ( @p ind_find ) n )
 * 
 * @param e Constraint to be checked
 * @param index_str Required index of parameter
 * @param m Ast manager
 * @param m_util_s string ast util
 * @param m_util_a arith ast util
 * @param[out] val Extracted addition value 
 * @param[out] ind_find Extracted indexof find 
 * @return true <-> if of the particular form.
 */
bool is_indexof_add(expr* e, expr* index_str, ast_manager& m, seq_util& m_util_s, arith_util& m_util_a, expr*& val, expr*& ind_find);


bool is_to_int_num_eq(expr* e, ast_manager& m, seq_util& m_util_s, arith_util& m_util_a, expr*& to_int_arg, rational& num);

bool is_len_num_eq(expr* e, ast_manager& m, seq_util& m_util_s, arith_util& m_util_a, expr*& len_arg, rational& num);

bool is_len_num_leq(expr* e, ast_manager& m, seq_util& m_util_s, arith_util& m_util_a, expr*& len_arg, rational& num);

/**
 * @brief Check if the formula @p e contains a quantifier.
 * 
 * @param e Z3 formula
 * @param m AST manager
 * @return true <--> @p e has a quantifier
 */
bool has_quantifier(expr* e, ast_manager& m);


}
#endif
