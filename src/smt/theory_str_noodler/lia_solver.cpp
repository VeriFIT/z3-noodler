#include "ast/ast_pp.h"
#include "ast/rewriter/expr_safe_replace.h"
#include "smt/theory_str_noodler/lia_solver.h"

namespace smt::noodler {

    lia_solver::lia_solver(ast_manager& m, const obj_map<expr, expr*>& predicate_replace):
        m(m), m_util_s(m), initialized(false), erv(m), model_formula(m), unsat_core(m),
        predicate_replace(predicate_replace), pinned(m) {
    }

    expr* lia_solver::replace_arith_str_funcs(expr* ex) {
        expr* cached;
        if (rewrite_memo.find(ex, cached)) {
            return cached;
        }

        expr* result;
        if (is_quantifier(ex)) {
            quantifier* q = to_quantifier(ex);
            expr* new_body = replace_arith_str_funcs(q->get_expr());
            if (new_body == q->get_expr()) {
                result = ex;
            } else {
                quantifier* new_q = m.update_quantifier(q, new_body);
                pinned.push_back(new_q);
                result = new_q;
            }
        } else if (is_var(ex)) {
            // bound variable, nothing to do
            result = ex;
        } else {
            SASSERT(is_app(ex));
            expr* pred_repl;
            if (predicate_replace.find(ex, pred_repl)) {
                // ex is a complex string (sub)term Noodler has already replaced elsewhere by a variable
                // (e.g. `(str.at x i)` -> `@at!1`); reuse the exact same replacement so occurrences of
                // this subterm coming from raw context formulas line up with Noodler's own length formula.
                result = replace_arith_str_funcs(pred_repl);
            } else {
                app* a = to_app(ex);
                bool changed = false;
                ptr_vector<expr> new_args;
                for (unsigned i = 0; i < a->get_num_args(); ++i) {
                    expr* new_arg = replace_arith_str_funcs(a->get_arg(i));
                    new_args.push_back(new_arg);
                    changed |= (new_arg != a->get_arg(i));
                }
                app* rebuilt = a;
                if (changed) {
                    rebuilt = m.mk_app(a->get_decl(), new_args.size(), new_args.data());
                    pinned.push_back(rebuilt);
                }

                if (util::is_arith_str_func(rebuilt, m_util_s)) {
                    expr* fresh;
                    if (!fresh_vars.find(rebuilt, fresh)) {
                        app* fresh_const = m.mk_fresh_const("@ext_arith_str", rebuilt->get_sort(), true);
                        pinned.push_back(fresh_const);
                        fresh_vars.insert(rebuilt, fresh_const);
                        canonical_of_fresh.insert(fresh_const, rebuilt);
                        fresh = fresh_const;
                    }
                    result = fresh;
                } else {
                    result = rebuilt;
                }
            }
        }

        rewrite_memo.insert(ex, result);
        return result;
    }

    expr_ref lia_solver::translate_fresh_vars_back(expr* ex) {
        if (canonical_of_fresh.empty()) {
            return expr_ref(ex, m);
        }
        expr_safe_replace replace(m);
        for (const auto& entry : canonical_of_fresh) {
            replace.insert(&entry.get_key(), entry.get_value());
        }
        expr_ref result(m);
        replace(ex, result);
        return result;
    }

    expr* lia_solver::rewrite_for_external_solver(expr* e) {
        return replace_arith_str_funcs(e);
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
        unsat_core = translate_fresh_vars_back(unsat_core);
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
                // include them too -- important when you want to use the model generated by this LIA solver.
                expr_ref_vector context_clauses(m);
                auto collect = [this, &ctx, &context_clauses](const clause_vector& clauses) {
                    for (clause* c : clauses) {
                        unsigned num_lits = c->get_num_literals();
                        if (num_lits == 0) {
                            continue;
                        }
                        expr_ref_vector lits(m);
                        for (unsigned i = 0; i < num_lits; ++i) {
                            lits.push_back(ctx.literal2expr(c->get_literal(i)));
                        }
                        context_clauses.push_back(lits.size() == 1 ? lits.get(0) : m.mk_or(lits.size(), lits.data()));
                    }
                };
                collect(ctx.get_lemmas());
                collect(ctx.get_aux_clauses());
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
