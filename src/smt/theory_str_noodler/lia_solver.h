#ifndef _NOODLER_LIA_SOLVER_H_
#define _NOODLER_LIA_SOLVER_H_

#include "ast/ast.h"
#include "ast/seq_decl_plugin.h"
#include "util/lbool.h"
#include "model/model.h"
#include "smt/smt_context.h"
#include "smt/theory_str_noodler/util.h"

namespace smt::noodler {

    /**
     * @brief Base class for internal LIA solvers used by noodler to check satisfiability of a
     * length/arithmetic `expr` against a Z3 `context`.
     *
     * Holds everything that is shared between the concrete solvers (int_expr_solver, quant_lia_solver):
     * gathering formulas from the context (`initialize`/`assert_expr`) and turning the model/unsat core
     * returned by the external ("none" string-solver) sub-kernel into `model_formula`/`unsat_core`
     * (`compute_model_formula`/`compute_unsat_core`). Subclasses only need to implement `check_sat`,
     * using those helpers around whatever concrete sub-kernel/tactic-solver they drive.
     */
    class lia_solver {
    protected:
        ast_manager& m;
        seq_util m_util_s;
        bool initialized;
        expr_ref_vector erv;
        expr_ref model_formula;
        expr_ref unsat_core;

        lia_solver(ast_manager& m);

        /// Reset model_formula/unsat_core to `true`; call at the start of check_sat before (re)computing
        /// them.
        void reset_result();

        /// Aggregate (conjunction) @p raw_core, straight out of the sub-solver, into `unsat_core`.
        void compute_unsat_core(const expr_ref_vector& raw_core);

        /**
         * @brief Get the value of @p a (an application of str.len/str.to_code/str.to_int/str.to_real,
         * see util::is_arith_str_func) in the model @p mdl of the external solver.
         *
         * The external solver has no string theory, so these functions are uninterpreted there, and their
         * model is a table (func_interp) mapping values of the string argument to arithmetic values, plus
         * an else value. String values in such a model are either string literals (for terms equal to some
         * literal) or abstract values `String!val!N` (for all other terms). Evaluating @p a directly by
         * mdl->eval_expr can therefore return an ite such as `(ite (= String!val!7 "aaaabbbb") 8 0)`:
         * if the table has no entry for the argument's value (entries equal to the else value are removed
         * by func_interp::compress), the evaluator falls back to the whole table as an ite, and it cannot
         * decide whether an abstract value equals a literal. As each value in the model belongs to a
         * different equivalence class and literals are given only to classes containing them, an abstract
         * value is never equal to a literal, so the right value is the entry for the argument's value if
         * there is one, and the else value otherwise. We therefore do this lookup ourselves.
         *
         * Falls back to mdl->eval_expr if the lookup is not possible (no table for the function, the
         * argument does not evaluate to a value, or there is no usable else value).
         */
        expr_ref eval_arith_str_func(app* a, model_ref& mdl);

        /// Build `model_formula` by evaluating, in @p mdl, every int/real variable and every ground
        /// str.len/str.to_code/str.to_int/str.to_real application (see eval_arith_str_func) occurring
        /// in @p e.
        void compute_model_formula(expr* e, model_ref& mdl);

    public:
        virtual ~lia_solver() = default;

        /**
         * @brief Initialize the solver with formulas present in the given Z3 `context`.
         *
         * @param ctx The Z3 `context` from which to take asserted formulas and current assignment.
         * @param include_assignment If true, include (assert) expressions corresponding to the current model returned by SMT core.
         * @param include_clauses If true, also include clauses (e.g. not-yet-fully-decided theory axioms) currently held by @p ctx.
         */
        virtual void initialize(context& ctx, bool include_assignment = true, bool include_clauses = false);

        /**
         * @brief Check satisfiability of the given length/arithmetic expression together
         *        with any formulas previously provided via `initialize` or `assert_expr`.
         *
         * @param e The Z3 expression to check for satisfiability.
         * @return `l_true` if satisfiable, `l_false` if unsatisfiable, `l_undef` otherwise.
         */
        virtual lbool check_sat(expr* e) = 0;

        /// @brief Assert @p e for subsequent check_sat calls.
        void assert_expr(expr* e);

        /**
         * @brief Populate `dst` with an expression representing the unsat core.
         *
         * If the underlying solver can provide an unsat core, this method should
         * append or set `dst` to a conjunction of core formulas. If no core is
         * available, implementations should set `dst` to `m.mk_true()` or an empty
         * conjunction as appropriate.
         *
         * @param dst Output reference where the constructed unsat-core expression
         *            will be stored. The caller provides an `expr_ref` associated
         *            with the current `ast_manager`.
         */
        virtual void get_unsat_core(expr_ref& dst);

        /// @brief Get the formula encoding model of arith vars/length constraints
        virtual expr_ref get_model();
    };

}

#endif
