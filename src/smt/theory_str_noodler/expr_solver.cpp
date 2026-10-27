/*
The skeleton of this code was obtained by Yu-Fang Chen from https://github.com/guluchen/z3.
Eternal glory to Yu-Fang.
*/

#include "smt/smt_kernel.h"
#include "expr_solver.h"

namespace smt::noodler {
    kernel& asserted_formulas_kernel::get(context& ctx) {
        const unsigned num_of_formulas = ctx.get_num_asserted_formulas();
        unsigned num_of_kept = 0;
        while (num_of_kept < fmls.size() && num_of_kept < num_of_formulas &&
               fmls.get(num_of_kept) == ctx.get_asserted_formula(num_of_kept)) {
            ++num_of_kept;
        }
        if (!solver || num_of_kept < fmls.size()) {
            fp = ctx.get_fparams();
            fp.m_string_solver = symbol("none");
            solver = alloc(kernel, m, fp);
            fmls.reset();
            proxies.reset();
            pinned.reset();
            num_of_kept = 0;
        }
        for (unsigned i = num_of_kept; i < num_of_formulas; ++i) {
            fmls.push_back(ctx.get_asserted_formula(i));
            solver->assert_expr(fmls.back());
        }
        return *solver;
    }

    expr* asserted_formulas_kernel::mk_assumption(expr* e) {
        expr* atom = e;
        m.is_not(e, atom);
        if (is_uninterp_const(atom)) { return e; }
        expr* proxy = nullptr;
        if (proxies.find(e, proxy)) { return proxy; }
        app_ref fresh(m.mk_fresh_const("noodler!asm", m.mk_bool_sort()), m);
        proxy = fresh;
        pinned.push_back(e);
        pinned.push_back(proxy);
        proxies.insert(e, proxy);
        solver->assert_expr(m.mk_implies(proxy, e));
        return proxy;
    }

    kernel& asserted_formulas_kernel::get_empty(const smt_params& fp) {
        if (!empty_solver) {
            empty_fp = fp;
            empty_solver = alloc(kernel, m, empty_fp);
        }
        return *empty_solver;
    }

    void int_expr_solver::add_asserted_formulas(context& ctx) {
        if (asserted_kernel == nullptr) {
            lia_solver::add_asserted_formulas(ctx);
        } else {
            asserted_ctx = &ctx;
        }
    }

    lbool int_expr_solver::check_sat(expr* e, bool compute_model, bool compute_unsat_core) {
        TRACE(str_lia, tout << "check_sat start\n";);
        SASSERT(!compute_unsat_core || asserted_ctx == nullptr);

        scoped_ptr<kernel> fresh_solver;
        kernel* solver;
        lbool r;
        if (asserted_ctx != nullptr) {
            solver = &asserted_kernel->get(*asserted_ctx);
            expr_ref_vector assumptions(m);
            for (expr* f : erv) { assumptions.push_back(asserted_kernel->mk_assumption(f)); }
            assumptions.push_back(e);
            r = solver->check(assumptions);
        } else {
            if (asserted_kernel != nullptr) {
                solver = &asserted_kernel->get_empty(fp);
            } else {
                fresh_solver = alloc(kernel, m, fp);
                solver = fresh_solver.get();
            }
            erv.push_back(e);
            r = solver->check(erv);
            erv.pop_back();
        }

        reset_result();
        if (compute_unsat_core && r == lbool::l_false) {
            expr_ref_vector raw_core(m);
            for (unsigned i = 0; i < solver->get_unsat_core_size(); ++i) {
                raw_core.push_back(solver->get_unsat_core_expr(i));
            }
            this->compute_unsat_core(raw_core);
        }
        if (compute_model && r == lbool::l_true) {
            model_ref mdl;
            solver->get_model(mdl);
            compute_model_formula(e, mdl);
        }

        TRACE(str_lia, tout << "check_sat end\n";);
        return r;
    }
}
