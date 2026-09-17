/*
The skeleton of this code was obtained by Yu-Fang Chen from https://github.com/guluchen/z3. 
Eternal glory to Yu-Fang.
*/

#ifndef _EXPR_INT_SOLVER_H_
#define _EXPR_INT_SOLVER_H_

#include "smt/smt_kernel.h"
#include "params/smt_params.h"
#include "smt/smt_context.h"
#include "ast/seq_decl_plugin.h"
#include "smt/theory_str_noodler/lia_solver.h"
#include "smt/theory_str_noodler/util.h"

namespace smt::noodler {
    class int_expr_solver : public lia_solver {
        ast_manager& m;
        seq_util m_util_s;
        bool initialized;
        expr_ref_vector erv;
        expr_ref unsat_core;
        expr_ref model_formula;
        smt_params fp;

        // Noodler's own predicate/complex-string-function -> variable replacement (read-only here), see
        // theory_str_noodler::predicate_replace.
        const obj_map<expr, expr*>& predicate_replace;
        // canonical str.len/str.to_code/str.stoi/str.stor application -> fresh arithmetic constant
        // introduced for this solver instance, see util::replace_arith_str_funcs.
        obj_map<expr, expr*> fresh_vars;
        // reverse of fresh_vars, used to map a fresh constant's model value back to the term we care about
        obj_map<expr, expr*> canonical_of_fresh;
        obj_map<expr, expr*> rewrite_memo;
        expr_ref_vector pinned;
    public:
        int_expr_solver(ast_manager& m, smt_params fp, const obj_map<expr, expr*>& predicate_replace):
            m(m), m_util_s(m), erv(m), unsat_core(m), model_formula(m), fp(fp),
            predicate_replace(predicate_replace), pinned(m) {
            this->fp.m_string_solver = symbol("none");
            initialized=false;
       }

        lbool check_sat(expr* e) override;
        void initialize(context& ctx, bool include_assignment = true) override;
        void get_unsat_core(expr_ref& dst) override;
        void assert_expr(expr * e);
        expr_ref get_model() override { return model_formula; }

    private:
        /// Rewrite @p e so it is safe to hand to this ("none" string-solver) sub-kernel, see
        /// util::replace_arith_str_funcs.
        expr* rewrite_for_external_solver(expr* e) {
            return util::replace_arith_str_funcs(e, m, m_util_s, predicate_replace, fresh_vars, canonical_of_fresh, rewrite_memo, pinned);
        }
    };
}

#endif