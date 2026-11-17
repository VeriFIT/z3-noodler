/**
 * @file theory_str_noodler_blocking.cpp
 * @brief Blocking the current instance by theory lemmas.
 *
 * When final_check_eh finds the instance built from the relevant constraints unsatisfiable (possibly only for
 * the lengths of the solutions found), it adds a lemma blocking it: the negation of the constraints (see
 * construct_refinement), possibly disjuncted with the length formula of the solutions (see block_curr_len).
 * If the instance is unsatisfiable regardless of lengths and its constraints split into independent slices
 * (see compute_independent_slices), the lemma is built only from an unsatisfiable slice, which is much stronger
 * (see block_unsat_slice).
 */

#include <functional>

#include "smt/theory_str_noodler/theory_str_noodler.h"
#include "smt/theory_str_noodler/constraint_slices.h"

namespace smt::noodler {

    expr_ref theory_str_noodler::construct_refinement() {
        context& ctx = get_context();

        ast_manager& m = get_manager();
        expr *refinement = nullptr;
        STRACE(str, tout << "[Constructing refinement]\n";);
        for (const auto& we : this->m_word_eq_todo_rel) {
            // we create the equation according to we
            expr *const e = ctx.mk_eq_atom(we.first, we.second);
            refinement = refinement == nullptr ? e : m.mk_and(refinement, e);
        }

        literal_vector ls;
        for (const auto& wi : this->m_word_diseq_todo_rel) {
            expr_ref e(m.mk_not(ctx.mk_eq_atom(wi.first, wi.second)), m);
            // e might not be internalized
            if(!ctx.e_internalized(e)) {
                ctx.internalize(e, false);
            }
            refinement = refinement == nullptr ? e : m.mk_and(refinement, e);
        }
        for (const auto& in : this->m_membership_todo_rel) {
            app_ref in_app(m_util_s.re.mk_in_re(std::get<0>(in), std::get<1>(in)), m);
            if(!std::get<2>(in)){
                in_app = m.mk_not(in_app);
                if(!ctx.e_internalized(in_app)) {
                    ctx.internalize(in_app, false);
                }
            }
            refinement = refinement == nullptr ? in_app : m.mk_and(refinement, in_app);
        }
        for (const auto& in : this->m_rat_membership_todo_rel) {
            app_ref in_app(m_util_s.rat_rel.mk_in_rat(std::get<0>(in), std::get<1>(in),  std::get<2>(in)), m);
            if(!std::get<3>(in)){
                in_app = m.mk_not(in_app);
                if(!ctx.e_internalized(in_app)) {
                    ctx.internalize(in_app, false);
                }
            }
            refinement = refinement == nullptr ? in_app : m.mk_and(refinement, in_app);
        }
        for(const auto& nc : this->m_not_contains_todo_rel) {
            app_ref nc_app(m.mk_not(m_util_s.str.mk_contains(nc.first, nc.second)), m);
            refinement = refinement == nullptr ? nc_app : m.mk_and(refinement, nc_app);
        }
        if (refinement != nullptr && seq_abstraction) {
            // the solution relies also on (dis)equalities of elements of generic sequences
            expr_ref_vector facts(m);
            seq_abstraction->get_facts(facts);
            for (expr* fact : facts) {
                refinement = m.mk_and(refinement, fact);
            }
        }

        return expr_ref(refinement, m);
    }

    void theory_str_noodler::block_curr_len(expr_ref len_formula, bool add_axiomatized, bool is_overapprox) {
        STRACE(str_block, tout << __LINE__ << " enter " << __FUNCTION__ << std::endl;);

        expr_ref refinement = construct_refinement();

        if(m_params.m_loop_protect && add_axiomatized) {
            this->axiomatized_instances.push_back({refinement, stored_instance{ .lengths = len_formula, .is_overapprox = is_overapprox}});
        }
        if (refinement != nullptr) {
            set_input_has_quantifiers(expr_cases::has_quantifier(len_formula, m));
            add_axiom(m.mk_or(m.mk_not(refinement), len_formula));
        }
        STRACE(str_block, tout << __LINE__ << " leave " << __FUNCTION__ << std::endl;);
    }

    bool theory_str_noodler::block_unsat_slice(const Formula& instance) {
        if (instance.contains_pred_type(PredicateType::Transducer) || !m_conversion_todo.empty() || !m_rat_membership_todo_rel.empty()) {
            return false;
        }

        // the string variables (or atomic string terms) of a side of a constraint, as in util::collect_terms
        std::function<void(expr*, std::vector<expr*>&)> collect_vars = [&](expr* e, std::vector<expr*>& vars) {
            expr* replacement = nullptr;
            if (predicate_replace.find(e, replacement)) {
                vars.push_back(replacement);
            } else if (m_util_s.str.is_concat(e)) {
                for (expr* arg : *to_app(e)) {
                    collect_vars(arg, vars);
                }
            } else if (!m_util_s.str.is_string(e) && !m_util_s.str.is_empty(e) && !m_util_s.str.is_unit(e)) {
                vars.push_back(e);
            }
        };

        // constraints are indexed: equations, disequations, memberships, not-contains
        const unsigned num_eqs = m_word_eq_todo_rel.size();
        const unsigned num_diseqs = m_word_diseq_todo_rel.size();
        const unsigned num_membs = m_membership_todo_rel.size();
        const unsigned num_constraints = num_eqs + num_diseqs + num_membs + m_not_contains_todo_rel.size();
        std::vector<std::vector<expr*>> constraint_vars(num_constraints);
        for (unsigned i = 0; i < num_constraints; ++i) {
            if (i < num_eqs) {
                collect_vars(m_word_eq_todo_rel[i].first, constraint_vars[i]);
                collect_vars(m_word_eq_todo_rel[i].second, constraint_vars[i]);
            } else if (i < num_eqs + num_diseqs) {
                collect_vars(m_word_diseq_todo_rel[i - num_eqs].first, constraint_vars[i]);
                collect_vars(m_word_diseq_todo_rel[i - num_eqs].second, constraint_vars[i]);
            } else if (i < num_eqs + num_diseqs + num_membs) {
                collect_vars(std::get<0>(m_membership_todo_rel[i - num_eqs - num_diseqs]), constraint_vars[i]);
            } else {
                const expr_pair& nc = m_not_contains_todo_rel[i - num_eqs - num_diseqs - num_membs];
                collect_vars(nc.first, constraint_vars[i]);
                collect_vars(nc.second, constraint_vars[i]);
            }
        }

        // independent slices, the smaller ones first (smaller lemmas)
        const std::vector<std::vector<unsigned>> slices = compute_independent_slices(constraint_vars);
        if (slices.size() <= 1) {
            return false;
        }

        // the decision procedure works with the relevant constraints, so we temporarily restrict them to a slice
        vector<expr_pair> all_eqs, all_diseqs, all_not_contains;
        vector<expr_pair_flag> all_membs;
        all_eqs.swap(m_word_eq_todo_rel);
        all_diseqs.swap(m_word_diseq_todo_rel);
        all_membs.swap(m_membership_todo_rel);
        all_not_contains.swap(m_not_contains_todo_rel);
        auto restore = [&]() {
            m_word_eq_todo_rel.swap(all_eqs);
            m_word_diseq_todo_rel.swap(all_diseqs);
            m_membership_todo_rel.swap(all_membs);
            m_not_contains_todo_rel.swap(all_not_contains);
        };

        bool blocked = false;
        try {
            for (const std::vector<unsigned>& slice : slices) {
                m_word_eq_todo_rel.reset();
                m_word_diseq_todo_rel.reset();
                m_membership_todo_rel.reset();
                m_not_contains_todo_rel.reset();
                for (unsigned i : slice) {
                    if (i < num_eqs) {
                        m_word_eq_todo_rel.push_back(all_eqs[i]);
                    } else if (i < num_eqs + num_diseqs) {
                        m_word_diseq_todo_rel.push_back(all_diseqs[i - num_eqs]);
                    } else if (i < num_eqs + num_diseqs + num_membs) {
                        m_membership_todo_rel.push_back(all_membs[i - num_eqs - num_diseqs]);
                    } else {
                        m_not_contains_todo_rel.push_back(all_not_contains[i - num_eqs - num_diseqs - num_membs]);
                    }
                }

                regex::Alphabet slice_symbols = get_symbols_from_relevant();
                Formula slice_instance = get_formula_from_relevant(slice_symbols);
                AutAssignment slice_aut_assignment{create_aut_assignment_for_formula(slice_instance, slice_symbols)};
                DecisionProcedure slice_proc(slice_instance, slice_aut_assignment, get_init_length_vars(slice_aut_assignment), m_params, {}, m);
                if (slice_proc.preprocess(PreprocessType::PLAIN, var_eqs.get_equivalence_bt(slice_aut_assignment, ctx, m_util_s)) == l_false) {
                    STRACE(str, tout << "Unsat slice (" << slice.size() << " of " << num_constraints << " constraints):\n" << slice_instance.to_string(););
                    // the refinement is constructed from the (restricted) relevant constraints
                    block_curr_len(expr_ref(m.mk_false(), m), false, true);
                    blocked = true;
                    break;
                }
            }
        } catch (...) {
            restore();
            throw;
        }
        restore();
        return blocked;
    }

    void theory_str_noodler::block_unsat_instance(const Formula& instance, bool add_axiomatized, bool is_overapprox) {
        if (!block_unsat_slice(instance)) {
            block_curr_len(expr_ref(m.mk_false(), m), add_axiomatized, is_overapprox);
        }
    }
}
