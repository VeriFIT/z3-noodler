#ifndef _QUANT_LIA_SOLVER_H_
#define _QUANT_LIA_SOLVER_H_

#include "smt/smt_kernel.h"
#include "params/smt_params.h"
#include "smt/smt_context.h"
#include "smt/theory_arith.h"
#include "solver/tactic2solver.h"
#include "smt/smt_solver.h"
#include "tactic/smtlogics/quant_tactics.h"
#include "ast/seq_decl_plugin.h"
#include "smt/theory_str_noodler/lia_solver.h"
#include "smt/theory_str_noodler/util.h"

namespace smt::noodler {
    class quant_lia_solver : public lia_solver {

    private:
        ast_manager& m;
        seq_util m_util_s;
        bool initialized;
        expr_ref_vector erv;
        expr_ref_vector unsat_core;
        expr_ref model_formula;

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
        quant_lia_solver(ast_manager& m, const obj_map<expr, expr*>& predicate_replace)
            : m(m), m_util_s(m), erv(m), unsat_core(m), model_formula(m),
              predicate_replace(predicate_replace), pinned(m) {
            initialized=false;
        }

    private:
        /// Rewrite @p e so it is safe to hand to this ("none" string-solver) sub-kernel, see
        /// util::replace_arith_str_funcs.
        expr* rewrite_for_external_solver(expr* e) {
            return util::replace_arith_str_funcs(e, m, m_util_s, predicate_replace, fresh_vars, canonical_of_fresh, rewrite_memo, pinned);
        }

    public:

        /**
         * @brief Check is the given length formula is SAT (together with the 
         * formulae from the context).
         * 
         * @param e Length formula
         * @return lbool Satisfiability check result
         */
        lbool check_sat(expr* e) override {
            params_ref p;
            
            // parameters used by z3 for quantified LIA formulae
            p.set_sym("string_solver", symbol("none"));
            p.set_bool("mbqi", true);
            p.set_uint("qi_lazy_threshold", 20);
            p.set_double("restart_factor", 1.5);
            p.set_bool("pi_use_database", true);
            p.set_bool("eliminate_bounds", true);

            // another options for a solver: mk_smt_solver(m, p, symbol("LIA")); (no tactic)
            // tactic solver used by z3 to solve quantified LIA formula
            solver* sl = mk_tactic2solver(m, mk_lia_tactic(m, p), p, false, true, true, symbol("ALL"));

            expr* e_rw = rewrite_for_external_solver(e);
            erv.push_back(e_rw);
            sl->assert_expr(erv);
            auto res = sl->check_sat();
            sl->get_unsat_core(unsat_core);
            erv.pop_back();

            model_formula = m.mk_true();
            if (res == lbool::l_true) {
                model_ref mdl;
                sl->get_model(mdl);

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

            return res;
        }

        /**
         * @brief Initialize LIA solver. Take input LIA formula from the context and formulae corresponding to the 
         * current assignment and add them to the vector of solved LIA formulae.
         * 
         * @param ctx Current context
         * @param include_assignment Include the current assignment from the context?
         */
        void initialize(context& ctx, bool include_assignment = true) override {
            if(!initialized){
                initialized=true;
                expr_ref_vector Assigns(m);
                ctx.get_assignments(Assigns);
                for (unsigned i = 0; i < ctx.get_num_asserted_formulas(); ++i) {
                    STRACE(str_lia, tout<< "check_sat context from asserted: " << mk_pp(ctx.get_asserted_formula(i),m) << std::endl);
                    assert_expr(ctx.get_asserted_formula(i));
                }
                if (include_assignment) {
                    for (auto & e : Assigns){
                        if(ctx.is_relevant(e)) {
                            STRACE(str_lia, tout << "check_sat context from assign: " << mk_pp(e, m) << std::endl);
                            assert_expr(e);
                        }
                    }
                }
            }
        }

        void assert_expr(expr * e) {
            erv.push_back(rewrite_for_external_solver(e));
        }

        void get_unsat_core(expr_ref& dst) override {
            dst = m.mk_and(unsat_core);
        }
        
        expr_ref get_model() override {
            return model_formula;
        }
    };
}

#endif
