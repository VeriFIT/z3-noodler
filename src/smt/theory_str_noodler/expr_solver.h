/*
The skeleton of this code was obtained by Yu-Fang Chen from https://github.com/guluchen/z3.
Eternal glory to Yu-Fang.
*/

#ifndef _EXPR_INT_SOLVER_H_
#define _EXPR_INT_SOLVER_H_

#include "params/smt_params.h"
#include "smt/smt_kernel.h"
#include "smt/theory_str_noodler/lia_solver.h"

namespace smt::noodler {
    /**
     * @brief A kernel without the string theory holding the formulas asserted in a context.
     *
     * A fresh kernel preprocesses and internalizes every formula and assumption given to it, which costs far
     * more than the length check itself. The kernel is therefore kept and reused by the checks against the
     * same context while the formulas asserted in it stay the same, and each assumption is internalized once,
     * as an implication from a fresh constant that is assumed instead.
     */
    class asserted_formulas_kernel {
        ast_manager& m;
        smt_params fp;
        scoped_ptr<kernel> solver;
        // the formulas asserted to solver, a prefix of the ones asserted in the context
        expr_ref_vector fmls;
        // the assumptions given to mk_assumption() and the constants implying them in solver
        obj_map<expr, expr*> proxies;
        expr_ref_vector pinned;
    public:
        explicit asserted_formulas_kernel(ast_manager& m): m(m), fmls(m), pinned(m) {}

        /// The kernel holding exactly the formulas asserted in @p ctx, rebuilt if some of them were removed.
        kernel& get(context& ctx);

        /**
         * @brief An assumption for the kernel returned by the last get() that is equivalent to assuming @p e.
         */
        expr* mk_assumption(expr* e);
    };

    class int_expr_solver : public lia_solver {
        smt_params fp;
        // if set, the formulas asserted in the context given to initialize() are checked in this kernel
        asserted_formulas_kernel* asserted_kernel;
        context* asserted_ctx = nullptr;

    protected:
        void add_asserted_formulas(context& ctx) override;

    public:
        /**
         * @param asserted_kernel If not null, the kernel the formulas asserted in the context are checked in.
         *  The unsat core then omits them, so it must not be computed.
         */
        int_expr_solver(ast_manager& m, smt_params fp, asserted_formulas_kernel* asserted_kernel = nullptr):
            lia_solver(m), fp(fp), asserted_kernel(asserted_kernel) {
            this->fp.m_string_solver = symbol("none");
       }

        lbool check_sat(expr* e, bool compute_model, bool compute_unsat_core) override;
    };
}

#endif
