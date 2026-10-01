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
     * gathering formulas from the context (`initialize`/`assert_expr`), rewriting terms so they are safe
     * to hand to an external ("none" string-solver) sub-kernel (`rewrite_for_external_solver`, see
     * `replace_arith_str_funcs`), and translating the model/unsat-core the sub-kernel returns back
     * into the caller's own vocabulary (`compute_model_formula`/`compute_unsat_core`, see
     * `translate_fresh_vars_back`). Subclasses only need to implement `check_sat`, using those
     * helpers around whatever concrete sub-kernel/tactic-solver they drive.
     */
    class lia_solver {
    protected:
        ast_manager& m;
        seq_util m_util_s;
        bool initialized;
        expr_ref_vector erv;
        expr_ref model_formula;
        expr_ref unsat_core;

        // Noodler's own predicate/complex-string-function -> variable replacement (read-only here), see
        // theory_str_noodler::predicate_replace.
        const obj_map<expr, expr*>& predicate_replace;
        // canonical str.len/str.to_code/str.stoi/str.stor application -> fresh arithmetic constant
        // introduced for this solver instance, see replace_arith_str_funcs.
        obj_map<expr, expr*> fresh_vars;
        // reverse of fresh_vars, used to map a fresh constant's model/unsat-core value back to the term
        // we care about, see translate_fresh_vars_back.
        obj_map<expr, expr*> canonical_of_fresh;
        obj_map<expr, expr*> rewrite_memo;
        expr_ref_vector pinned;

        lia_solver(ast_manager& m, const obj_map<expr, expr*>& predicate_replace);

        /**
         * @brief Rewrites @p ex so it is safe to hand to an external solver that has no theory registered
         * for the string sort (i.e. smt.string_solver=none).
         *
         * Such a solver treats every string-sorted function symbol as completely uninterpreted, including
         * str.len/str.to_code/str.stoi/str.stor. Left as-is, their model (built by generic function
         * model-completion) can come back as an arbitrary ite-tree over ground string arguments the solver
         * happened to see (e.g. `(ite (= x "aa") 2 3)`) instead of a genuine arithmetic value. This function
         * rewrites @p ex bottom-up so that:
         *   - any subterm that already has a replacement registered in `predicate_replace` is replaced by
         *     it (so that a term coming from a raw/original formula, e.g. `(str.len (str.at x i))`, lines
         *     up with whatever variable Noodler's own length formula already uses for the same subterm,
         *     e.g. `@at!1`);
         *   - every remaining application recognized by util::is_arith_str_func is replaced by a fresh
         *     arithmetic constant.
         *
         * `fresh_vars` and `rewrite_memo` are reused for every formula handed to this solver instance, so
         * that the same source application is always replaced by the same fresh constant (this is what
         * keeps e.g. the derived length formula and the raw context formulas linked). Every time a new
         * fresh constant is created, it is also registered into `canonical_of_fresh` (fresh constant ->
         * the canonical application it stands for) so callers can map a fresh constant's model value back
         * to the term they actually care about. Newly created expressions are appended to `pinned` to keep
         * them alive for as long as the maps are used.
         */
        expr* replace_arith_str_funcs(expr* ex);

        /**
         * @brief Undo the fresh-constant substitution replace_arith_str_funcs performed: replaces every
         * occurrence of a fresh constant registered in `canonical_of_fresh` (fresh constant -> the
         * str.len/str.to_code/str.stoi/str.stor application it stands for) by that canonical application,
         * so that @p ex is expressed again purely over the caller's own vocabulary instead of the external
         * solver's fresh constants. Used to translate a model or unsat core coming back from an external
         * ("none" string-solver) sub-kernel/tactic-solver.
         */
        expr_ref translate_fresh_vars_back(expr* ex);

        /// Rewrite @p e so it is safe to hand to an external ("none" string-solver) sub-kernel, see
        /// replace_arith_str_funcs.
        expr* rewrite_for_external_solver(expr* e);

        /// Reset model_formula/unsat_core to `true`; call at the start of check_sat before (re)computing
        /// them.
        void reset_result();

        /// Translate @p raw_core (straight out of the sub-solver, still expressed over
        /// rewrite_for_external_solver's fresh constants) back to the caller's vocabulary and aggregate
        /// it (conjunction) into `unsat_core`.
        void compute_unsat_core(const expr_ref_vector& raw_core);

        /// Build `model_formula` by evaluating every int/real variable occurring in the rewritten
        /// formula @p e_rw (fresh constants included) in @p mdl, mapping each fresh constant back to the
        /// canonical str.len/str.to_code/str.stoi/str.stor application it stands for.
        void compute_model_formula(expr* e_rw, model_ref& mdl);

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

        /// @brief Rewrite and assert @p e for subsequent check_sat calls.
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
