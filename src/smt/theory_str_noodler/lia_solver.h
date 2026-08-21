#ifndef _NOODLER_LIA_SOLVER_H_
#define _NOODLER_LIA_SOLVER_H_

#include "ast/ast.h"
#include "util/lbool.h"
#include "smt/smt_context.h"

namespace smt::noodler {

    /**
     * @brief Abstract interface for internal LIA solvers used by noodler.
     *
     * Implementations must provide initialization from a `context`, a method to
     * check satisfiability of an arithmetic/length `expr` and a way to
     * retrieve an (approximate) unsat core when available.
     */
    class lia_solver {
    public:
        /**
         * @brief Virtual destructor.
         */
        virtual ~lia_solver() = default;

        /**
         * @brief Initialize the solver with formulas present in the given Z3 `context`.
         *
         * @param ctx The Z3 `context` from which to take asserted formulas and current assignment.
         * @param include_assignment If true, include (assert) expressions corresponding to the current model returned by SMT core.
         */
        virtual void initialize(context& ctx, bool include_assignment = true) = 0;

        /**
         * @brief Check satisfiability of the given length/arithmetic expression together
         *        with any formulas previously provided via `initialize` or `assert`.
         *
         * @param e The Z3 expression to check for satisfiability.
         * @return `l_true` if satisfiable, `l_false` if unsatisfiable, `l_undef` otherwise.
         */
        virtual lbool check_sat(expr* e) = 0;

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
        virtual void get_unsat_core(expr_ref& dst) = 0;
    };

}

#endif
