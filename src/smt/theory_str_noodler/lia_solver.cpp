#include "ast/ast_pp.h"
#include "smt/theory_str_noodler/lia_solver.h"

namespace smt::noodler {

    lia_solver::lia_solver(ast_manager& m, const obj_map<expr, expr*>& predicate_replace):
        m(m), m_util_s(m), initialized(false), erv(m), model_formula(m), unsat_core(m),
        predicate_replace(predicate_replace), pinned(m) {
    }

    expr* lia_solver::rewrite_for_external_solver(expr* e) {
        return util::replace_arith_str_funcs(e, m, m_util_s, predicate_replace, fresh_vars, canonical_of_fresh, rewrite_memo, pinned);
    }

    void lia_solver::reset_result() {
        model_formula = expr_ref(m.mk_true(), m);
        unsat_core = expr_ref(m.mk_true(), m);
    }

    void lia_solver::compute_unsat_core(const expr_ref_vector& raw_core) {
        for (expr* c : raw_core) {
            unsat_core = m.mk_and(unsat_core, c);
        }
        // the core is expressed over rewrite_for_external_solver's fresh constants -- translate it back
        // to the caller's own vocabulary.
        unsat_core = util::translate_fresh_vars_back(unsat_core, m, canonical_of_fresh);
        STRACE(str_lia, tout << "UNSAT core:" << std::endl << mk_pp(unsat_core, m));
    }

    void lia_solver::compute_model_formula(expr* e_rw, model_ref& mdl) {
        // Collect vars from the rewritten formula: genuine int/real variables are kept as-is, while
        // the fresh constants introduced by rewrite_for_external_solver stand for str.len/str.to_code/
        // str.stoi/str.stor applications (see canonical_of_fresh) and must be evaluated back into
        // an equation over the original application, not over the fresh constant itself.
        struct collect_vars {
            ast_manager &m;
            expr_ref_vector vars;
            seq_util m_util_s;

            collect_vars(ast_manager &m) : m(m), vars(m), m_util_s(m) {}
            void operator()(expr* e) {
                if (!m_util_s.is_string(e->get_sort()) && util::is_variable(e)) {
                    vars.push_back(e);
                }
            }
        };
        collect_vars cv(m);
        for_each_expr(cv, e_rw);
        for (expr* v : cv.vars) {
            expr_ref res(m);
            mdl->eval_expr(v, res);
            expr* canonical;
            expr* lhs = canonical_of_fresh.find(v, canonical) ? canonical : v;
            STRACE(str_lia, tout << "Model for " << mk_pp(lhs, m) << " is " << mk_pp(res, m) << std::endl;);
            model_formula = m.mk_and(model_formula, m.mk_eq(lhs, res));
        }
    }

    void lia_solver::initialize(context& ctx, bool include_assignment, bool include_clauses) {
        if (!initialized) {
            initialized = true;
            expr_ref_vector Assigns(m);
            ctx.get_assignments(Assigns);
            for (unsigned i = 0; i < ctx.get_num_asserted_formulas(); ++i) {
                STRACE(str_lia, tout << "check_sat context from asserted: " << mk_pp(ctx.get_asserted_formula(i), m) << std::endl);
                assert_expr(ctx.get_asserted_formula(i));
            }
            if (include_assignment) {
                for (auto& e : Assigns) {
                    if (ctx.is_relevant(e)) {
                        STRACE(str_lia, tout << "check_sat context from assign: " << mk_pp(e, m) << std::endl);
                        assert_expr(e);
                    }
                }
            }
            if (include_clauses) {
                // Assigns/get_asserted_formula only expose the original assertions and literals that
                // already have a concrete truth value. Clauses with still-undecided literals (e.g. a
                // semantic axiom for str.substr/str.indexof relating a proxy variable to a real problem
                // variable, guarded by not-yet-decided bound checks) are otherwise invisible here, so
                // include them too -- see util::get_context_clauses.
                expr_ref_vector context_clauses(m);
                util::get_context_clauses(ctx, m, context_clauses);
                for (expr* cl : context_clauses) {
                    STRACE(str_lia, tout << "check_sat context from clause: " << mk_pp(cl, m) << std::endl);
                    assert_expr(cl);
                }
            }
        }
    }

    void lia_solver::assert_expr(expr* e) {
        erv.push_back(rewrite_for_external_solver(e));
    }

    void lia_solver::get_unsat_core(expr_ref& dst) {
        dst = unsat_core;
    }

    expr_ref lia_solver::get_model() {
        return model_formula;
    }

}
