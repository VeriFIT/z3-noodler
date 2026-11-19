#include <mata/nfa/builder.hh>
#include <memory>
#include "ast/ast_util.h"
#include "formula.h"
#include "smt/theory_str_noodler/theory_str_noodler.h"
#include "smt/theory_str_noodler/ecma_regex.h"
#include "smt/theory_str_noodler/expr_solver.h"
#include "smt/theory_str_noodler/quant_lia_solver.h"
#include "memb_heuristics_procedures.h"
#include "diseq_length_heuristic.h"

namespace smt::noodler {

    void write_z3_expr_into_stream(ast_manager& manager, std::ostream& stream, expr_ref formula) {
        ast_pp_util utl(manager);
        utl.collect(formula);
        utl.display_decls(stream);
        stream << "(assert\n";
        utl.display_expr(stream, formula);
        stream << "\n)"
               << "(check-sat)\n"
               << "(get-model)";
    }

    /**
     * @brief Checks satisfiability of constraints in _todo member variables (e.g. m_word_eq_todo, m_membership_todo,...)
     *
     * It follows these steps:
     *   1) Remove constraints that are not relevant for the solution, adding all relevant constraints to *_todo_rel, ending with
     *        - language equations and diseqations (m_lang_eq_or_diseq_todo_rel)
     *        - word equations and diseqations (m_word_eq_todo_rel and m_word_diseq_todo_rel)
     *        - membership constraints (m_membership_todo_rel)
     *        - not contains constraints (m_not_contains_todo, currently cannot be handled and we return unknown)
     *   2) Check if all language eqations and disequations are true (the sides are given as regexes)
     *   3) Create the formula instance and automata assignment from word (dis)eqautions and membership constraints
     *   4) Check if it is satisfiable which consists of
     *        - preprocessing the formula (simplifying (dis)equations, reducing the number of variables etc.)
     *        - iteratively running the decision procedure until a satisfiable solution and length constraint is found or until
     *          it finishes wihtout result
     */
    final_check_status theory_str_noodler::final_check_eh(unsigned) {
        final_check_status status = solve_string_constraints();
        if (status == FC_DONE && mk_interface_eqs() > 0) {
            // the string constraints are satisfied, but the search needs to decide the equalities of shared terms
            // first (their merging may change the string constraints, so they need to be solved again)
            last_run_was_sat = false;
            scope_with_last_run_was_sat = -1;
            return FC_CONTINUE;
        }
        return status;
    }

    final_check_status theory_str_noodler::solve_string_constraints() {
        TRACE(str, tout << "final_check starts" << std::endl;);
        invalidate_arith_projection();

        // sequences that are arguments of the uninterpreted seq.nth_u must be decided as (dis)equal
        // (checked before the shortcut for the last sat run, as new nth_u terms or classes might appear
        // after it; in that case the decision procedure must be run again with the new (dis)equations)
        if (mk_nth_u_extensionality_eqs() > 0) {
            last_run_was_sat = false;
            scope_with_last_run_was_sat = -1;
            return FC_CONTINUE;
        }

        if (last_run_was_sat) {
            // if we returned previously sat, then we should always return sat (final_check_eh should not be called again, but for some reason Z3 calls it)
            TRACE(str, tout << "Last run was sat on scope level " << scope_with_last_run_was_sat << "\n";);
            return FC_DONE;
        }

        dec_proc = nullptr;
        seq_abstraction = nullptr;
        relevant_vars.clear();
        scope_with_last_run_was_sat = -1;

        remove_irrelevant_constr();
        remove_constraints_of_fresh_classes();
        STRACE(str,
            tout << "Relevant predicates:" << std::endl;
            tout << "  eqs(" << this->m_word_eq_todo_rel.size() << "):" << std::endl;
            for (const auto &we: this->m_word_eq_todo_rel) {
                tout << "    " << mk_pp(we.first, m) << " == " << mk_pp(we.second, m) << std::endl;
            }
            tout << "  diseqs(" << this->m_word_diseq_todo_rel.size() << "):" << std::endl;
            for (const auto &wd: this->m_word_diseq_todo_rel) {
                tout << "    " << mk_pp(wd.first, m) << " != " << mk_pp(wd.second, m) << std::endl;
            }
            tout << "  membs(" << this->m_membership_todo_rel.size() << "):" << std::endl;
            for (const auto &memb: this->m_membership_todo_rel) {
                tout << "    " << mk_pp(std::get<0>(memb), m) << (std::get<2>(memb) ? "" : " not") << " in " << mk_pp(std::get<1>(memb), m) << std::endl;
            }
            tout << "  rat membs(" << this->m_rat_membership_todo_rel.size() << "):" << std::endl;
            for (const auto &memb: this->m_rat_membership_todo_rel) {
                tout << "    (" << mk_pp(std::get<0>(memb), m) << ", " << mk_pp(std::get<1>(memb), m) << ")" << (std::get<3>(memb) ? "" : " not") << " in " << mk_pp(std::get<2>(memb), m) << std::endl;
            }
            tout << "  lang (dis)eqs(" << this->m_lang_eq_or_diseq_todo_rel.size() << "):" << std::endl;
            for (const auto &led: this->m_lang_eq_or_diseq_todo_rel) {
                tout << "    " << mk_pp(std::get<0>(led), m) << (std::get<2>(led) ? " == " : " != ") << mk_pp(std::get<1>(led), m) << std::endl;
            }
            tout << "  not_contains(" << this->m_not_contains_todo_rel.size() << "):" << std::endl;
            for (const auto &notc: this->m_not_contains_todo_rel) {
                tout << "    " << mk_pp(notc.first, m) << "; " << mk_pp(notc.second, m) << std::endl;
            }
            tout << "  conversions(" << this->m_conversion_todo.size() << "):" << std::endl;
            for (const auto &conv: this->m_conversion_todo) {
                tout << "    " << get_conversion_name(conv.type) << " with string var " << conv.string_var << " and number var " << conv.number_var << std::endl;
            }
        );

        // Solve Language (dis)equations
        lbool lang_eqs_diseqs_res = solve_lang_eqs_diseqs();
        if (lang_eqs_diseqs_res == l_false) {
            // one of the (dis)equations is unsat
            return FC_CONTINUE;
        } else if (lang_eqs_diseqs_res == l_undef) {
            return FC_GIVEUP;
        } // for true case it means we need to solve string constraints to get final solution

        // Generic sequences (Seq T) are handled only by the main stabilization-based decision procedure, where
        // the elements are abstracted by symbols (see SeqElementAbstraction).
        const bool has_gen_seq = relevant_has_generic_seq();
        if (has_gen_seq && !prepare_seq_abstraction()) {
            // some (dis)equalities of elements need to be decided first
            return FC_CONTINUE;
        }

        /***************************** SOLVE WORD (DIS)EQUATIONS + REGULAR MEMBERSHIPS ******************************/

        // the instance being solved (the key of the pending candidate solution and of the skipped procedures)
        m_current_key = construct_refinement();

        // a candidate solution whose guarded length formula was decided by the main context (see sat_handling)
        if (final_check_status pending_status; handle_pending_len_candidate(pending_status)) {
            return pending_status;
        }

        // cache for storing already solved instances. For each instance we store the length formula obtained from the decision procedure.
        // if we get an instance that we have already solved, we use this stored length formula (if we run the procedure
        // we get the same formula up to alpha reduction).
        if(m_params.m_loop_protect) {
            lbool result = run_loop_protection();
            if(result == l_true && !m_params.m_produce_models) { // if we want to produce model, we need the exact solution in dec_proc, so we need to run procedure again
                last_run_was_sat = true;
                scope_with_last_run_was_sat = m_scope_level;
                return FC_DONE;
            } else if (result == l_false) {
                return FC_CONTINUE;
            }
        }

        ++num_of_solving_final_checks;

        bool contains_word_equations = !this->m_word_eq_todo_rel.empty();
        bool contains_word_disequations = !this->m_word_diseq_todo_rel.empty();
        bool contains_conversions = !this->m_conversion_todo.empty();
        bool contains_eqs_and_diseqs_only = this->m_not_contains_todo_rel.empty() && this->m_conversion_todo.empty() && this->m_rat_membership_todo_rel.empty();

        // nothing is trivially SAT
        if(contains_eqs_and_diseqs_only && this->m_word_eq_todo_rel.empty() && this->m_word_diseq_todo_rel.empty() && this->m_membership_todo_rel.empty() ) {
            return FC_DONE;
        }

        // As a heuristic, for the case we have exactly one constraint, which is of type 'x (not)in RE', we use universality/emptiness
        // checking of the regex (using some heuristics) instead of constructing the automaton of RE. The construction (especially complement)
        // can sometimes blow up, so the check should be faster.
        if(m_params.m_try_memb_heur && !has_gen_seq && this->m_membership_todo_rel.size() == 1 && !contains_word_equations && !contains_word_disequations && !contains_conversions && this->m_not_contains_todo_rel.empty() && this->m_rat_membership_todo_rel.empty()
                && this->len_vars.empty() // TODO: handle length vars that are not x (i.e., there are no string constraints on them, other than length ones, we just need to compute arith model)
        ) {
            const auto& reg_data = this->m_membership_todo_rel[0];
            // TODO: check if "xyz in RE" works correctly
            expr_ref var = std::get<0>(reg_data);
            if (util::is_str_variable(var, m_util_s) && !this->len_vars.contains(var)) { // the variable cannot be length one
                STRACE(str, tout << "trying one membership heuristics\n";);
                BasicTerm noodler_var = util::get_variable_basic_term(var);
                relevant_vars.insert(noodler_var);
                dec_proc = std::make_shared<MembHeuristicProcedure>(
                    noodler_var,
                    std::get<1>(reg_data),
                    std::get<2>(reg_data),
                    m_util_s, m, nfa_constructor, m_params.m_produce_models
                );
                this->statistics.at("single-memb-heur").num_start++;
                lbool result = dec_proc->compute_next_solution();
                if(result != l_undef) this->statistics.at("single-memb-heur").num_finish++;
                if(result == l_true) {
                    return FC_DONE;
                } else if(result == l_false) {
                    block_curr_len(expr_ref(this->m.mk_false(), this->m)); // the variable is not legnth one, so we block fully
                    return FC_CONTINUE;
                }
            }
        }

        if (m_params.m_try_memb_heur && !has_gen_seq && is_mult_membership_suitable()) {
            lbool result = run_mult_membership_heur();
            if(result == l_true) {
                return FC_DONE;
            } else if(result == l_false) {
                block_curr_len(expr_ref(this->m.mk_false(), this->m)); // there should not be any length vars, so we block fully
                return FC_CONTINUE;
            }
        }

        // Gather symbols from relevant (dis)equations and from regular expressions of relevant memberships
        regex::Alphabet symbols_in_formula = get_symbols_from_relevant();

        // Gather relevant word (dis)equations (and transducers that occur in them) to noodler formula
        Formula instance = get_formula_from_relevant(symbols_in_formula);

        // Create automata assignment for the formula
        AutAssignment aut_assignment{create_aut_assignment_for_formula(instance, symbols_in_formula)};

        bool contains_transducers = instance.contains_pred_type(PredicateType::Transducer);

        std::vector<TermConversion> conversions = get_conversions_as_basicterms(aut_assignment);

        for (const auto& [var, nfa] : aut_assignment) {
            relevant_vars.insert(var);
        }

        // Get the initial length vars that are needed here (i.e they are in aut_assignment)
        std::unordered_set<BasicTerm> init_length_sensitive_vars{ get_init_length_vars(aut_assignment) };
        STRACE(str,
            tout << "Relevant formula:\n" << instance.to_string();
            for (const auto& conv : conversions) {
                tout << get_conversion_name(conv.type) << " with string var " << conv.string_var << " and number var " << conv.number_var << std::endl;
            }
            tout << "Length variables:";
            for (const auto &len_var : init_length_sensitive_vars) {
                tout << " " << len_var;
            }
            tout << std::endl
        );


        // There is only one symbol in the equation. The system is SAT iff lengths are SAT
        if(m_params.m_try_unary_proc && !is_len_source_skipped(LenCandidateSource::UNARY) && !has_gen_seq && symbols_in_formula.size() == 2 && !contains_conversions && !contains_transducers && this->m_not_contains_todo_rel.size() == 0 && UnaryDecisionProcedure::is_suitable(instance, aut_assignment)) { // dummy symbol + 1
            lbool result = run_length_sat(instance, aut_assignment, init_length_sensitive_vars, conversions);
            if(result == l_true) {
                return FC_DONE;
            } else if(result == l_false) {
                return FC_CONTINUE;
            }
        }

        // try a heuristic based procedure for disequations only
        if (contains_word_disequations && !is_len_source_skipped(LenCandidateSource::DISEQ_HEUR) && !has_gen_seq && this->m_conversion_todo.empty() && this->m_not_contains_todo_rel.empty() && this->m_rat_membership_todo_rel.empty()
            && DiseqLengthHeuristicProcedure::is_suitable(instance, aut_assignment)) {
            lbool result = run_diseq_length_heur(instance, aut_assignment, init_length_sensitive_vars);
            if (result == l_true) {
                return FC_DONE;
            } else if(result == l_false) {
                return FC_CONTINUE;
            }
        }

        // try Nielsen transformation (if enabled) to solve
        // Nielsen is used also for generic sequences: it works only with the equations and its models consist only of
        // the literals (symbols of elements) occurring in them, so they never contain symbols not representing elements.
        // length-only memberships (e.g., x in re.allchar{2,} obtained from |x| >= 2) are handled as length constraints,
        // their variables become length-sensitive for Nielsen
        std::unordered_set<BasicTerm> nielsen_length_sensitive_vars = init_length_sensitive_vars;
        if(m_params.m_try_nielsen && !is_len_source_skipped(LenCandidateSource::NIELSEN) && is_nielsen_suitable(instance, nielsen_length_sensitive_vars)) {
            lbool result = run_nielsen(instance, aut_assignment, nielsen_length_sensitive_vars);
            if(result == l_true) {
                return FC_DONE;
            } else if(result == l_false) {
                return FC_CONTINUE;
            }
        }

        // we do not put into dec_proc directly, because we might do underapproximation that saves into dec_proc
        std::shared_ptr<DecisionProcedure> main_dec_proc = std::make_shared<DecisionProcedure>(instance, aut_assignment, init_length_sensitive_vars, m_params, conversions, m);

        // whether we will be checking length formulae from the decision procedure with the existing context in Z3
        // if there are no length vars in the current string formula, we do not need to check with context
        bool check_len_sat_with_context = !init_length_sensitive_vars.empty();

        // the skip_len_sat preprocessing rule requires that the input formula is length satisfiable
        // --> before we apply the preprocessing, we need to be sure that it is indeed true.
        // length constraints from initial assignment
        // we want to include all variables from the formula --> e.g.
        // s.t = u where u \in ab, |s| > 100. The only length variable is s, but we need
        // to include also length of |u| to propagate the value to |s|
        expr_ref lengths = len_node_to_z3_formula(main_dec_proc->get_initial_lengths(true));
        if(check_len_sat(lengths, check_len_sat_with_context) == l_false) {
            STRACE(str, tout << "Unsat from initial lengths (1)" << std::endl);

            this->statistics.at("stabilization").num_solved_preprocess++;
            // If the instance is both length unsatisfiable and unsatisfiable from preprocessing,
            // we want to kill it after preprocessing as it generates stronger theory lemma (negation of the string part).
            lbool result = main_dec_proc->preprocess(PreprocessType::PLAIN, this->var_eqs.get_equivalence_bt(aut_assignment, ctx, m_util_s));
            if (result == l_false) {
                block_unsat_instance(instance, false, true);
            } else {
                block_curr_len(lengths, true, true);
            }
            return FC_CONTINUE;

        }

        // now we know that the initial formula is length-satisfiable
        // try length-based decision procedure (if enabled) to solve
        if(m_params.m_try_length_proc && !is_len_source_skipped(LenCandidateSource::LENGTH) && !has_gen_seq && contains_eqs_and_diseqs_only && !contains_transducers && LengthDecisionProcedure::is_suitable(instance, aut_assignment)) {
            lbool result = run_length_proc(instance, aut_assignment, init_length_sensitive_vars);
            if(result == l_true) {
                return FC_DONE;
            } else if(result == l_false) {
                return FC_CONTINUE;
            }
        }

        // try underapproximation (if enabled) to solve
        if(m_params.m_underapproximation && !is_len_source_skipped(LenCandidateSource::UNDERAPPROX) && !has_gen_seq && is_underapprox_suitable(instance, aut_assignment, conversions)) {
            STRACE(str, tout << "Try underapproximation" << std::endl);
            lbool underapprox_result = solve_underapprox(instance, aut_assignment, init_length_sensitive_vars, conversions);
            if (underapprox_result == l_true) {
                STRACE(str, tout << "Sat from underapproximation" << std::endl;);
                return FC_DONE;
            } else if (underapprox_result == l_false) {
                // the candidate solution is decided by the main context (see sat_handling)
                return FC_CONTINUE;
            }
            STRACE(str, tout << "Underapproximation did not help\n";);
        }

        dec_proc = main_dec_proc;

        STRACE(str, tout << "Starting preprocessing" << std::endl);
        lbool result = dec_proc->preprocess(PreprocessType::PLAIN, this->var_eqs.get_equivalence_bt(aut_assignment, ctx, m_util_s));
        if (result == l_false) {
            this->statistics.at("stabilization").num_solved_preprocess++;
            STRACE(str, tout << "Unsat from preprocessing" << std::endl);
            block_unsat_instance(instance, false, true); // we do not store for loop protection
            return FC_CONTINUE;
        } // we do not check for l_true, because we will get it in get_another_solution() anyway TODO: should we check?

        // it is possible that the arithmetic formula becomes unsatisfiable already by adding the
        // length constraints from initial assignment
        lengths = len_node_to_z3_formula(dec_proc->get_initial_lengths());
        if(check_len_sat(lengths, check_len_sat_with_context) == l_false) {
            this->statistics.at("stabilization").num_solved_preprocess++;
            STRACE(str, tout << "Unsat from initial lengths (2)" << std::endl);
            block_curr_len(lengths, true, true);
            return FC_CONTINUE;
        }

        STRACE(str, tout << "Starting main decision procedure" << std::endl);
        dec_proc->init_computation();
        this->statistics.at("stabilization").num_start++;

        return run_main_enumeration(std::make_shared<MainEnumState>(m, main_dec_proc, instance, check_len_sat_with_context));
    }

    final_check_status theory_str_noodler::run_main_enumeration(const std::shared_ptr<MainEnumState>& st) {
        dec_proc = st->dec_proc;

        auto check_lens_with_precision = [this, st]() {
            auto [noodler_lengths, precision] = dec_proc->get_lengths();

            st->lengths = len_node_to_z3_formula(noodler_lengths);
            m_rewrite(st->lengths);

            STRACE(str_print_notcontains_lia,
                std::ofstream out_file("./not-contains-lia.smt2");
                write_z3_expr_into_stream(this->m, out_file, st->lengths);
                out_file.close();
            );

            lbool sat = check_len_sat(st->lengths, st->check_len_sat_with_context);
            return std::pair<lbool, LenNodePrecision>(sat, precision);
        };
        auto check_lens = [&check_lens_with_precision, this, st](bool add_to_block) -> lbool {
            auto [is_lengths_sat, precision] = check_lens_with_precision();
            if (add_to_block && is_lengths_sat == l_false) {
                st->block_len = m.mk_or(st->block_len, st->lengths);
            }
            return is_lengths_sat;
        };

        while (true) {
            util::check_limit(m);
            lbool result = st->dec_proc->compute_next_solution_with_len_checks(check_lens);
            if (result == l_true) {
                auto [is_lengths_sat, precision] = check_lens_with_precision();

                if (is_lengths_sat == l_true) {
                    STRACE(str, tout << "len sat " << mk_pp(st->lengths, m) << std::endl;);
                    lbool result_of_sat_handling = sat_handling(st->lengths, LenCandidateSource::MAIN, false, precision, st);
                    if (result_of_sat_handling == l_true) {
                        this->statistics.at("stabilization").num_finish++;
                        return FC_DONE;
                    } else if (result_of_sat_handling == l_undef) {
                        // the main context decides whether the length formula is consistent (see handle_pending_len_candidate)
                        this->statistics.at("stabilization").num_finish++;
                        return FC_CONTINUE;
                    } else {
                        is_lengths_sat = l_false;
                        st->check_len_sat_with_context = true;
                    }
                }

                if (is_lengths_sat == l_false) {
                    STRACE(str, tout << "len unsat " <<  mk_pp(st->lengths, m) << std::endl;);
                    st->block_len = m.mk_or(st->block_len, st->lengths);

                    if(precision == LenNodePrecision::UNDERAPPROX) {
                        ctx.get_fparams().is_underapprox = true;
                    }
                } else {
                    // The solver returned `l_undef`. As not-contains predicates are being reduced to quantified LIA, we are using a solver with quantified instantiation
                    // that is incomplete and it might return `l_undef` (unknown) on some branches. We want to continue exploring other branches, hoping that some other
                    // might get solved. Hence we set is_underapprox = true - we don't really know whether this branch has contained any solutions.
                    ctx.get_fparams().is_underapprox = true;
                }
            } else if (result == l_false) {
                // we did not find a solution (with satisfiable length constraints)
                // we need to block current assignment
                STRACE(str, tout << "assignment unsat " << mk_pp(st->block_len, m) << std::endl;);

                if (!st->check_len_sat_with_context) {
                    // if we were not checking length satisfiability with the context, then the current string assignment must be unsatisfiable on its own => we can block it completely
                    block_unsat_instance(st->instance, true, false);
                } else {
                    // If some solving states were skipped, an overapproximation was added to block_len
                    const bool overapprox = st->dec_proc->get_skipped_some_with_len_checks();

                    block_curr_len(st->block_len, true, overapprox);
                }
                this->statistics.at("stabilization").num_finish++;
                return FC_CONTINUE;
            } else {
                // we could not decide if there is solution, let's just give up
                STRACE(str, tout << "giving up" << std::endl);
                return FC_GIVEUP;
            }
        }
    }

    unsigned theory_str_noodler::remove_constraints_of_fresh_classes() {
        // the class (root in the e-graph) of a side that is a single term (nullptr for a concatenation)
        auto side_class = [&](expr* e) -> enode* {
            if (m_util_s.str.is_concat(e) || !ctx.e_internalized(e)) {
                return nullptr;
            }
            return ctx.get_enode(e)->get_root();
        };

        // classes used elsewhere than as a whole side of a disequation or in an equation inside the class
        obj_hashtable<enode> used;
        std::function<void(expr*)> use = [&](expr* e) {
            if (m_util_s.str.is_concat(e)) {
                for (expr* arg : *to_app(e)) {
                    use(arg);
                }
            } else if (ctx.e_internalized(e)) {
                used.insert(ctx.get_enode(e)->get_root());
            }
        };
        for (const auto& [l, r] : m_word_eq_todo_rel) {
            if (enode* c = side_class(l); c == nullptr || c != side_class(r)) {
                use(l);
                use(r);
            }
        }
        for (const auto& [l, r] : m_word_diseq_todo_rel) {
            if (side_class(l) == nullptr) use(l);
            if (side_class(r) == nullptr) use(r);
        }
        for (const auto& memb : m_membership_todo_rel) {
            use(std::get<0>(memb));
        }
        for (const auto& memb : m_rat_membership_todo_rel) {
            use(std::get<0>(memb));
            use(std::get<1>(memb));
        }
        for (const auto& nc : m_not_contains_todo_rel) {
            use(nc.first);
            use(nc.second);
        }
        for (const TermConversion& conv : m_conversion_todo) {
            auto it = var_name.find(conv.string_var);
            if (it == var_name.end()) {
                return 0; // cannot find the class of the converted variable
            }
            use(it->second);
        }
        // a class that is not used by the other constraints becomes fresh once its constraints are removed
        auto fresh = [&](enode* c) {
            return c != nullptr && !used.contains(c) && has_fresh_shape(c);
        };

        unsigned removed = 0;
        vector<expr_pair> kept_diseqs;
        for (const auto& diseq : m_word_diseq_todo_rel) {
            enode* lc = side_class(diseq.first);
            enode* rc = side_class(diseq.second);
            if (lc != rc && surely_different_values(lc, rc, fresh)) {
                STRACE(str, tout << "removed disequation: " << mk_pp(diseq.first, m) << " != " << mk_pp(diseq.second, m) << std::endl;);
                ++removed;
            } else {
                kept_diseqs.push_back(diseq);
            }
        }
        m_word_diseq_todo_rel = std::move(kept_diseqs);
        vector<expr_pair> kept_eqs;
        for (const auto& eq : m_word_eq_todo_rel) {
            if (enode* c = side_class(eq.first); c == nullptr || c != side_class(eq.second) || !fresh(c)) {
                kept_eqs.push_back(eq);
            }
        }
        m_word_eq_todo_rel = std::move(kept_eqs);
        return removed;
    }

    bool theory_str_noodler::is_foreign_theory_term(expr* e) const {
        if (!is_app(e)) {
            return false;
        }
        family_id fid = to_app(e)->get_family_id();
        return fid != null_family_id // it is not uninterpreted function/variable
            && fid != m.get_family_id(symbol("recfun")) // nor is it recursive function
            && fid != m_util_s.get_family_id(); // and it is of different theory than this one
    }

    void theory_str_noodler::remove_irrelevant_constr() {
        STRACE(str, tout << "Remove irrevelant" << std::endl);

        this->m_word_eq_todo_rel.clear();
        this->m_word_diseq_todo_rel.clear();
        this->m_membership_todo_rel.clear();
        this->m_rat_membership_todo_rel.clear();
        this->m_lang_eq_or_diseq_todo_rel.clear();
        this->m_not_contains_todo_rel.clear();

        for (const auto& we : m_word_eq_todo) {
            app_ref eq(m.mk_eq(we.first, we.second), m);
            app_ref eq_rev(m.mk_eq(we.second, we.first), m);

            STRACE(str,
                tout << "  Eq " << mk_pp(eq.get(), m) << " is " << (ctx.is_relevant(eq.get()) ? "" : "not ") << "relevant"
                     << " with assignment " << ctx.find_assignment(eq.get())
                     << " and its reverse is " << (ctx.is_relevant(eq_rev.get()) ? "" : "not ") << "relevant" << std::endl;
            );

            // check if equation or its reverse are relevant, or already assigned a truth value
            // (relevancy is just a laziness heuristic of Z3's core and does not guarantee that a
            // constraint that is already decided true/false can be safely ignored, e.g. disequations
            // generated internally by the array theory's extensionality axiom are never marked
            // relevant even though they are asserted true). We only fall back to the assignment when
            // one side is rooted in a foreign (non-string) theory, since that is the signature of a
            // fact controlled by another theory's internal reasoning with no other representation;
            // Noodler's own string-function decomposition (dis)equations are always seq-family/plain
            // variables on both sides, so this avoids a massive, needless blowup of the instance passed
            // to the decision procedure from including those (almost always already-decided) facts. and...
            if((ctx.is_relevant(eq.get()) || ctx.is_relevant(eq_rev.get()) ||
                ((ctx.find_assignment(eq.get()) != l_undef || ctx.find_assignment(eq_rev.get()) != l_undef) &&
                 (is_foreign_theory_term(we.first) || is_foreign_theory_term(we.second)))) &&
               // ...neither equation nor its reverse are saved as relevant yet
               !this->m_word_eq_todo_rel.contains(we) && !this->m_word_eq_todo_rel.contains({we.second, we.first})
               ) {
                // save it as relevant
                this->m_word_eq_todo_rel.push_back(we);
            }
        }

        for (const auto& wd : m_word_diseq_todo) {
            app_ref dis(m.mk_not(m.mk_eq(wd.first, wd.second)), m);
            app_ref dis_rev(m.mk_not(m.mk_eq(wd.second, wd.first)), m);

            STRACE(str,
                tout << "  Diseq " << mk_pp(dis.get(), m) << " is " << (ctx.is_relevant(dis.get()) ? "" : "not ") << "relevant"
                     << " with assignment " << ctx.find_assignment(dis.get())
                     << " and its reverse is " << (ctx.is_relevant(dis_rev.get()) ? "" : "not ") << "relevant" << std::endl;
            );

            // check if disequation or its reverse are relevant, or already assigned a truth value
            // (see comment above the equation case for why this is needed and how it is scoped) and...
            if((ctx.is_relevant(dis.get()) || ctx.is_relevant(dis_rev.get()) ||
                ((ctx.find_assignment(dis.get()) != l_undef || ctx.find_assignment(dis_rev.get()) != l_undef) &&
                 (is_foreign_theory_term(wd.first) || is_foreign_theory_term(wd.second)))) &&
               // ...neither disequation nor its reverse are saved as relevant yet
               !this->m_word_diseq_todo_rel.contains(wd) && !this->m_word_diseq_todo_rel.contains({wd.second, wd.first})
               ) {
                // save it as relevant
                this->m_word_diseq_todo_rel.push_back(wd);
            }
        }

        for (const auto& memb : this->m_membership_todo) {
            app_ref memb_app(m_util_s.re.mk_in_re(std::get<0>(memb), std::get<1>(memb)), m);
            app_ref memb_app_orig(m_util_s.re.mk_in_re(std::get<0>(memb), std::get<1>(memb)), m);
            if(!std::get<2>(memb)){
                memb_app = m.mk_not(memb_app);

            }

            STRACE(str,
                tout << "  " << mk_pp(memb_app.get(), m) << " is " << (ctx.is_relevant(memb_app.get()) ? "" : "not ") << "relevant"
                     << " with assignment " << ctx.find_assignment(memb_app.get())
                     << ", " << mk_pp(memb_app_orig.get(), m) << " is " << (ctx.is_relevant(memb_app_orig.get()) ? "" : "not ") << "relevant"
                     << std::endl;
            );

            // check if membership (or if we have negation, its negated form) is relevant, or already
            // assigned a truth value (see comment above the equation case) and...
            if((ctx.is_relevant(memb_app.get()) || ctx.is_relevant(memb_app_orig.get()) ||
                (ctx.find_assignment(memb_app.get()) != l_undef &&
                 is_foreign_theory_term(std::get<0>(memb)))) &&
               // this membership constraint is not added to relevant yet
               !this->m_membership_todo_rel.contains(memb)
               ) {
                this->m_membership_todo_rel.push_back(memb);
            }
        }

        for (const auto& memb : this->m_rat_membership_todo) {
            app_ref memb_app(m_util_s.rat_rel.mk_in_rat(std::get<0>(memb), std::get<1>(memb), std::get<2>(memb)), m);
            app_ref memb_app_orig(memb_app);
            if(!std::get<3>(memb)){
                memb_app = m.mk_not(memb_app);
            }

            STRACE(str,
                tout << "  " << mk_pp(memb_app.get(), m) << " is " << (ctx.is_relevant(memb_app.get()) ? "" : "not ") << "relevant"
                     << " with assignment " << ctx.find_assignment(memb_app.get())
                     << ", " << mk_pp(memb_app_orig.get(), m) << " is " << (ctx.is_relevant(memb_app_orig.get()) ? "" : "not ") << "relevant"
                     << std::endl;
            );

            // check if membership (or if we have negation, its negated form) is relevant, or already
            // assigned a truth value (see comment above the equation case) and...
            if((ctx.is_relevant(memb_app.get()) || ctx.is_relevant(memb_app_orig.get()) ||
                (ctx.find_assignment(memb_app.get()) != l_undef &&
                 (is_foreign_theory_term(std::get<0>(memb)) || is_foreign_theory_term(std::get<1>(memb))))) &&
               // this membership constraint is not added to relevant yet
               !this->m_rat_membership_todo_rel.contains(memb)
               ) {
                this->m_rat_membership_todo_rel.push_back(memb);
            }
        }

        // not contains
        for(const auto& not_con_pair: this->m_not_contains_todo) {
            app_ref con_expr(m_util_s.str.mk_contains(not_con_pair.first, not_con_pair.second), m);
            app_ref not_con_expr(m.mk_not(con_expr), m);

            STRACE(str,
                tout << "  NOT contains " << mk_pp(con_expr.get(), m) << " is " << (ctx.is_relevant(con_expr.get()) ? "" : "not ") << "relevant"
                     << " with assignment " << ctx.find_assignment(con_expr.get())
                     << ", " << mk_pp(not_con_expr.get(), m) << " is " << (ctx.is_relevant(not_con_expr.get()) ? "" : "not ") << "relevant"
                     << std::endl;
            );

            // relevant, or already assigned a truth value (see comment above the equation case)
            if((ctx.is_relevant(con_expr.get()) || ctx.is_relevant(not_con_expr.get()) ||
                ((ctx.find_assignment(con_expr.get()) != l_undef || ctx.find_assignment(not_con_expr.get()) != l_undef) &&
                 (is_foreign_theory_term(not_con_pair.first) || is_foreign_theory_term(not_con_pair.second)))) &&
                !this->m_not_contains_todo_rel.contains(not_con_pair)) {
                this->m_not_contains_todo_rel.push_back(not_con_pair);
            }
        }

        // TODO check for relevancy of language (dis)equations, right now we assume everything is relevant
        for(const auto& le : m_lang_eq_todo) {
            this->m_lang_eq_or_diseq_todo_rel.push_back({le.first, le.second, true});
        }
        for(const auto& ld : m_lang_diseq_todo) {
            this->m_lang_eq_or_diseq_todo_rel.push_back({ld.first, ld.second, false});
        }
    }

    Predicate theory_str_noodler::conv_eq_pred(app* const ex) {
        STRACE(str_conv_eq, tout << "conv_eq_pred: " << mk_pp(ex, m) << std::endl);
        const app* eq = ex;
        PredicateType ptype = PredicateType::Equation;
        if(m.is_not(ex)) {
            SASSERT(is_app(ex->get_arg(0)));
            SASSERT(ex->get_num_args() == 1);
            eq = to_app(ex->get_arg(0));
            ptype = PredicateType::Inequation;
        }
        SASSERT(eq->get_num_args() == 2);
        SASSERT(eq->get_arg(0));
        SASSERT(eq->get_arg(1));

        std::vector<BasicTerm> left, right;
        const auto unit_symbol = get_unit_symbol_fn();
        util::collect_terms(to_app(eq->get_arg(0)), m, this->m_util_s, this->predicate_replace, left, unit_symbol);
        util::collect_terms(to_app(eq->get_arg(1)), m, this->m_util_s, this->predicate_replace, right, unit_symbol);

        return Predicate(ptype, std::vector<std::vector<BasicTerm>>{left, right});
    }

    bool theory_str_noodler::is_tmp_transducer_eq(app* const ex) {
        if (this->m_util_s.str.is_replace_all(ex->get_arg(0)) || this->m_util_s.str.is_replace_re_all(ex->get_arg(0)) || this->m_util_s.str.is_replace_re(ex->get_arg(0))) {
            expr* rpl = this->predicate_replace.find(ex->get_arg(0));
            return rpl == ex->get_arg(1);
        }
        if (this->m_util_s.str.is_replace_all(ex->get_arg(1)) || this->m_util_s.str.is_replace_re_all(ex->get_arg(1)) || this->m_util_s.str.is_replace_re(ex->get_arg(1))) {
            expr* rpl = this->predicate_replace.find(ex->get_arg(1));
            return rpl == ex->get_arg(0);
        }
        return false;
    }

    Formula theory_str_noodler::get_formula_from_relevant(const regex::Alphabet& alph) {
        Formula instance;

        for (const auto &we: this->m_word_eq_todo_rel) {
            // ignore trivial equations obtained from axiomatization of 
            // transducer constraints, e.g., tmp = replace_all(...)
            if(is_tmp_transducer_eq(ctx.mk_eq_atom(we.first, we.second))) {
                continue;
            }
            Predicate inst = this->conv_eq_pred(ctx.mk_eq_atom(we.first, we.second));
            // gather transducer constraints occurring in the concatenation
            regex::gather_transducer_constraints(to_app(we.first), m, this->m_util_s, this->predicate_replace, alph, nfa_constructor, instance);
            regex::gather_transducer_constraints(to_app(we.second), m, this->m_util_s, this->predicate_replace, alph, nfa_constructor, instance);
            instance.add_predicate(inst);
        }

        for (const auto& wd : this->m_word_diseq_todo_rel) {
            Predicate inst = this->conv_eq_pred(m.mk_not(ctx.mk_eq_atom(wd.first, wd.second)));
            // gather transducer constraints occurring in the concatenation
            regex::gather_transducer_constraints(to_app(wd.first), m, this->m_util_s, this->predicate_replace, alph, nfa_constructor, instance);
            regex::gather_transducer_constraints(to_app(wd.second), m, this->m_util_s, this->predicate_replace, alph, nfa_constructor, instance);
            instance.add_predicate(inst);
        }

        for (const auto& rat_memb : this->m_rat_membership_todo_rel) {
            if (!std::get<3>(rat_memb)) {
                util::throw_error("We cannot handle negated membership in rational relations");
            }
            std::vector<BasicTerm> input, output;
            util::collect_terms(to_app(std::get<0>(rat_memb)), m, this->m_util_s, this->predicate_replace, input);
            util::collect_terms(to_app(std::get<1>(rat_memb)), m, this->m_util_s, this->predicate_replace, output);
            Predicate inst = Predicate::create_transducer(regex::conv_to_nft(to_app(std::get<2>(rat_memb)), m_util_s, m, alph), input, output);
            regex::gather_transducer_constraints(to_app(std::get<0>(rat_memb)), m, this->m_util_s, this->predicate_replace, alph, nfa_constructor, instance);
            regex::gather_transducer_constraints(to_app(std::get<1>(rat_memb)), m, this->m_util_s, this->predicate_replace, alph, nfa_constructor, instance);
            instance.add_predicate(inst);
        }

        // construct not contains predicates
        for(const auto& not_contains : this->m_not_contains_todo_rel) {
            std::vector<BasicTerm> left, right;
            const auto unit_symbol = get_unit_symbol_fn();
            util::collect_terms(to_app(not_contains.first), m, this->m_util_s, this->predicate_replace, left, unit_symbol);
            util::collect_terms(to_app(not_contains.second), m, this->m_util_s, this->predicate_replace, right, unit_symbol);
            // gather transducer constraints occurring in the concatenation
            regex::gather_transducer_constraints(to_app(not_contains.first), m, this->m_util_s, this->predicate_replace, alph, nfa_constructor, instance);
            regex::gather_transducer_constraints(to_app(not_contains.second), m, this->m_util_s, this->predicate_replace, alph, nfa_constructor, instance);
            Predicate inst = Predicate::create_not_contains(left, right);
            instance.add_predicate(inst);
        }

        for (const auto& conv : this->m_conversion_todo) {
            regex::gather_transducer_constraints(to_app(var_name.at(conv.string_var)), m, this->m_util_s, this->predicate_replace, alph, nfa_constructor, instance);
        }

        for (const auto& len: len_vars) {
            regex::gather_transducer_constraints(to_app(len), m, this->m_util_s, this->predicate_replace, alph, nfa_constructor, instance);
        }

        return instance;
    }

    regex::Alphabet theory_str_noodler::get_symbols_from_relevant() {
        // start with symbol representing everything not in formula
        regex::Alphabet symbols_in_formula{};

        for (const auto &word_equation: m_word_eq_todo_rel) {
            regex::extract_symbols(word_equation.first, m_util_s, symbols_in_formula);
            regex::extract_symbols(word_equation.second, m_util_s, symbols_in_formula);
        }

        for (const auto &word_disequation: m_word_diseq_todo_rel) {
            regex::extract_symbols(word_disequation.first, m_util_s, symbols_in_formula);
            regex::extract_symbols(word_disequation.second, m_util_s, symbols_in_formula);
        }

        for (const auto &membership: m_membership_todo_rel) {
            regex::extract_symbols(std::get<1>(membership), m_util_s, symbols_in_formula);
        }

        for (const auto &rat_membership: m_rat_membership_todo_rel) {
            regex::extract_symbols(std::get<0>(rat_membership), m_util_s, symbols_in_formula);
            regex::extract_symbols(std::get<1>(rat_membership), m_util_s, symbols_in_formula);
            regex::extract_symbols(std::get<2>(rat_membership), m_util_s, symbols_in_formula);
        }

        // extract from not contains
        for(const auto& not_contains : m_not_contains_todo_rel) {
            regex::extract_symbols(not_contains.first, m_util_s, symbols_in_formula);
            regex::extract_symbols(not_contains.second, m_util_s, symbols_in_formula);
        }

        bool contains_int_conversion = false;
        for (const auto& c : m_conversion_todo) { if (c.type == ConversionType::FROM_INT || c.type == ConversionType::TO_INT) { contains_int_conversion = true; break; } }
        bool contains_real_conversion = false;
        for (const auto& c : m_conversion_todo) { if (c.type == ConversionType::FROM_REAL || c.type == ConversionType::TO_REAL) { contains_real_conversion = true; break; } }

        // If we have to_int/from_int/to_real/from_real, we keep digits (0-9) as explicit symbols, so that they are not represented by dummy_symbol and it is easier to handle the conversions
        if (contains_int_conversion || contains_real_conversion) {
            for (mata::Symbol s = AutAssignment::DIGIT_SYMBOL_START; s <= AutAssignment::DIGIT_SYMBOL_END; ++s) {
                symbols_in_formula.insert(s);
            }
        }
        // If we have to_real/from_real, we also add '.', so that decimal point is not represented by dummy symbol
        if (contains_real_conversion) { symbols_in_formula.insert(AutAssignment::REAL_NUMBER_DELIMITER); }

        // symbols representing elements of generic sequences
        if (seq_abstraction) {
            seq_abstraction->assign_symbols(symbols_in_formula);
        }

        // we also insert dummy symbol representing all symbols NOT occurring in formula (but only if we do not have ALL symbols in formula)
        symbols_in_formula.insert_dummy_if_not_full();

        return symbols_in_formula;
    }

    AutAssignment theory_str_noodler::create_aut_assignment_for_formula(Formula& instance, const regex::Alphabet& noodler_alphabet) {
        AutAssignment aut_assignment{noodler_alphabet};
        const regex::Alphabet &alph = aut_assignment.get_alphabet();
        for (const auto &membership: m_membership_todo_rel) {
            const expr_ref& var_expr{ std::get<0>(membership) };
            assert(is_app(var_expr));
            const auto& var_app{ to_app(var_expr) };
            assert(var_app->get_num_args() == 0);
            const std::string& variable_name{ var_app->get_decl()->get_name().str() };

            zstring s;
            BasicTerm term = m_util_s.str.is_string(var_app, s) ? BasicTerm{BasicTermType::Literal, s} : util::get_variable_basic_term(var_expr);

            // If the regular constraint is in a negative form, create a complement of the regular expression instead.
            const bool make_complement{ !std::get<2>(membership) };
            // regexes over generic sequences are translated to string regexes over the symbols representing elements
            const expr_ref regex = seq_abstraction ? seq_abstraction->translate_regex(std::get<1>(membership)) : std::get<1>(membership);
            std::shared_ptr<const mata::nfa::Nfa> nfa = nfa_constructor.conv_to_nfa(to_app(regex), m_util_s, m, alph, make_complement, make_complement);
            auto aut_ass_it{ aut_assignment.find(term) };
            if (aut_ass_it != aut_assignment.end()) {
                // This variable already has some regular constraints. Hence, we create an intersection of the new one
                //  with the previously existing.
                aut_ass_it->second = std::make_shared<mata::nfa::Nfa>(
                        mata::nfa::reduce(mata::nfa::intersection(*nfa, *aut_ass_it->second)));

            } else { // We create a regular constraint for the current variable for the first time.
                aut_assignment[term] = std::make_shared<mata::nfa::Nfa>(*nfa);
            }

            // we also need to gather transducer constraints for the var
            regex::gather_transducer_constraints(var_app, m, this->m_util_s, this->predicate_replace, alph, nfa_constructor, instance);
        }

        // create sigma star automaton for our alphabet
        std::shared_ptr<mata::nfa::Nfa> nfa_sigma_star = std::make_shared<mata::nfa::Nfa>(aut_assignment.sigma_star_automaton());

        // some variables/literals are not assigned to anything yet, we need to fix that
        for (const auto &pred : instance.get_predicates()) {
            for (const auto &side : pred.get_params()) {
                for (const auto &var_or_literal : side) {
                    if (var_or_literal.is_variable() && aut_assignment.find(var_or_literal) == aut_assignment.end()) {
                        // assign sigma star automaton for all yet unassigned variables
                        aut_assignment[var_or_literal] = nfa_sigma_star;
                    } else if (var_or_literal.is_literal()) {
                        // to string literals. assign automaton accepting the word denoted by the literal
                        // TODO if Z3 can give us `string literal in RE` then we should check if aut_assignment does not contain this literal already (if yes, do intersection)
                        mata::nfa::Nfa nfa{ AutAssignment::create_word_nfa(var_or_literal.get_name()) };
                        aut_assignment.emplace(var_or_literal, std::make_shared<mata::nfa::Nfa>(std::move(nfa)));
                    }
                }
            }
        }

        // sequences over finite element sorts can contain only the symbols representing the values of the sort
        if (seq_abstraction) {
            for (auto& [var, nfa] : aut_assignment) {
                if (!var.is_variable()) {
                    continue;
                }
                auto var_expr_it = var_name.find(var);
                if (var_expr_it == var_name.end()) {
                    util::throw_error("unknown sort of a variable in a formula with generic sequences");
                }
                sort* var_sort = var_expr_it->second->get_sort();
                if (!seq_abstraction->is_finite_seq_sort(var_sort)) {
                    continue;
                }
                mata::nfa::Nfa elems_star(1, {0}, {0});
                for (mata::Symbol s : seq_abstraction->get_finite_symbols(var_sort)) {
                    elems_star.delta.add(0, s, 0);
                }
                nfa = std::make_shared<mata::nfa::Nfa>(mata::nfa::reduce(mata::nfa::intersection(*nfa, elems_star)));
            }
        }

        TRACE(str_nfa,
            tout << "Created automata assignment for formula:" << std::endl;
            for (const auto& single_aut_assignment: aut_assignment) {
               tout << "Automaton for " << single_aut_assignment.first.get_name() << ":" << std::endl;
               tout << *single_aut_assignment.second;
            }
        );

        return aut_assignment;
    }

    std::unordered_set<BasicTerm> theory_str_noodler::get_init_length_vars(AutAssignment& ass) {
        std::unordered_set<BasicTerm> init_lengths{};
        for (const auto& len : len_vars) {
            BasicTerm v = util::get_variable_basic_term(len);
            if(ass.find(v) != ass.end())
                init_lengths.emplace(v);
        }
        return init_lengths;
    }

    std::vector<TermConversion> theory_str_noodler::get_conversions_as_basicterms(AutAssignment& ass) {
        std::shared_ptr<mata::nfa::Nfa> nfa_sigma_star = std::make_shared<mata::nfa::Nfa>(ass.sigma_star_automaton());

        std::vector<TermConversion> conversions;
        for (const auto& transf : m_conversion_todo) {
            ass.insert({transf.string_var, nfa_sigma_star});
            conversions.push_back(transf);
        }
        return conversions;
    }

    expr_ref theory_str_noodler::get_classical_regex(expr* regex) {
        const auto cached = m_ecma_cache.classical_regexes.find(regex);
        if (cached != m_ecma_cache.classical_regexes.end()) {
            return cached->second.classical_regex;
        }
        expr_ref classical_regex = ecma::to_classical_regex(regex, m, m_params);
        m_ecma_cache.classical_regexes.emplace(
            regex, ecma_cache::classical_regex_entry{expr_ref(regex, m), classical_regex});
        return classical_regex;
    }

    lbool theory_str_noodler::solve_lang_eqs_diseqs() {
        for(const auto& item : this->m_lang_eq_or_diseq_todo_rel) {
            expr_ref left_side = std::get<0>(item);
            expr_ref right_side = std::get<1>(item);
            bool is_equation = std::get<2>(item);

            STRACE(str,
                tout << "Checking lang (dis)eq: " << mk_pp(left_side, m) << (is_equation ? " == " : " != ") << mk_pp(right_side, m) << std::endl;
            );

            // An equation whose sides are congruent (the same operator over arguments from the same equivalence
            // classes) follows from the equations of the arguments, which are checked separately, e.g.,
            // (re.from_ecma2020 "a") = (re.from_ecma2020 "b") after the literals "a" and "b" were merged.
            if (is_equation && smt::congruent(ctx.get_enode(left_side), ctx.get_enode(right_side))) {
                continue;
            }

            // (re.from_ecma2020 ...) with a regular pattern is compared as the classical regex of the pattern
            const expr_ref left_regex = get_classical_regex(left_side);
            const expr_ref right_regex = get_classical_regex(right_side);
            if (!left_regex || !right_regex ||
                !m_util_s.re.is_ground(left_regex) || !m_util_s.re.is_ground(right_regex)) {
                return l_undef;
            }

            // get symbols from both sides
            regex::Alphabet alph;
            regex::extract_symbols(left_regex, m_util_s, alph);
            regex::extract_symbols(right_regex, m_util_s, alph);
            alph.insert_dummy_if_not_full(); // dummy is needed for example for equation such as (= re.allchar (str.to_re "a"))

            // construct NFAs for both sides
            std::shared_ptr<const mata::nfa::Nfa> nfa1 = nfa_constructor.conv_to_nfa(to_app(left_regex), m_util_s, m, alph, false );
            std::shared_ptr<const mata::nfa::Nfa> nfa2 = nfa_constructor.conv_to_nfa(to_app(right_regex), m_util_s, m ,alph, false );

            // check if NFAs are equivalent (if we have equation) or not (if we have disequation)
            bool are_equiv;
            // for the case that one side is empty, we just need to check if the other automaton is empty
            if (nfa1->num_of_states() == 0) {
                are_equiv = nfa2->is_lang_empty();
            } else if (nfa2->num_of_states() == 0) {
                are_equiv = nfa1->is_lang_empty();
            } else {
                are_equiv = mata::nfa::are_equivalent(*nfa1, *nfa2);
            }
            if ((is_equation && !are_equiv) || (!is_equation && are_equiv)) {
                // the language (dis)equation does not hold => block it and return
                app_ref lang_eq(m.mk_eq(left_side, right_side), m);
                if(is_equation){
                    STRACE(str, tout << mk_pp(lang_eq, m) << " is unsat" << std::endl);
                    add_axiom({mk_literal(m.mk_not(lang_eq))});
                } else {
                    STRACE(str, tout << mk_pp(m.mk_not(lang_eq), m) << " is unsat" << std::endl);
                    add_axiom({mk_literal(lang_eq)});
                }
                return l_false;
            }
        }

        // if we are here, all (dis)equations hold
        return l_true;
    }

    lbool theory_str_noodler::solve_underapprox(const Formula& instance, const AutAssignment& aut_assignment,
                                                const std::unordered_set<BasicTerm>& init_length_sensitive_vars,
                                                std::vector<TermConversion> conversions) {
        context& ctx = get_context();
        std::shared_ptr<DecisionProcedure> main_dec_proc = std::make_shared<DecisionProcedure>(instance, aut_assignment, init_length_sensitive_vars, m_params, conversions, m);
        dec_proc = main_dec_proc;
        if (dec_proc->preprocess(PreprocessType::UNDERAPPROX, this->var_eqs.get_equivalence_bt(aut_assignment, ctx, m_util_s)) == l_false) {
            return l_undef;
        }

        dec_proc->init_computation();
        this->statistics.at("underapprox").num_start++;

        bool check_with_context = !init_length_sensitive_vars.empty();
        auto check_lens = [this, &check_with_context](bool) {
            expr_ref lengths = len_node_to_z3_formula(dec_proc->get_lengths().first);
            return check_len_sat(lengths, check_with_context);
        };

        while (main_dec_proc->compute_next_solution_with_len_checks(check_lens) == l_true) {
            expr_ref lengths = len_node_to_z3_formula(dec_proc->get_lengths().first);
            if (check_len_sat(lengths, check_with_context) == l_true) { // if there are no length vars in the current string formula, we do not need to check with context
                lbool res = sat_handling(lengths, LenCandidateSource::UNDERAPPROX, false, LenNodePrecision::UNDERAPPROX);
                if (res == l_true) {
                    this->statistics.at("underapprox").num_finish++;
                    return l_true;
                } else if (res == l_undef) {
                    this->statistics.at("underapprox").num_finish++;
                    return l_false; // pending, decided by the main context
                }
            }
        }
        return l_undef;
    }

    const expr_ref_vector& theory_str_noodler::get_arith_projection() {
        if (!m_arith_projection_valid) {
            m_arith_projection.reset();
            collect_arith_projection(ctx, m_arith_projection);
            m_arith_projection_valid = true;
        }
        return m_arith_projection;
    }

    kernel& theory_str_noodler::get_arith_kernel() {
        if (!m_arith_kernel) {
            m_arith_kernel_params = get_fparams();
            m_arith_kernel_params.m_string_solver = symbol("none");
            m_arith_kernel = alloc(kernel, m, m_arith_kernel_params);
            for (expr* e : get_arith_projection()) {
                m_arith_kernel->assert_expr(e);
            }
        }
        return *m_arith_kernel;
    }

    lbool theory_str_noodler::check_len_sat(expr_ref len_formula, bool check_with_context, expr_ref* unsat_core, expr_ref* model_formula, bool check_with_clauses) {
        if (!check_with_context && len_formula == m.mk_true()) {
            if (model_formula != nullptr) {
                *model_formula = expr_ref(m.mk_true(), m);
            }
            return l_true;
        }

        bool compute_model = (model_formula != nullptr);
        bool compute_unsat_core = (unsat_core != nullptr);

        const bool len_has_quantifier = expr_cases::has_quantifier(len_formula, m);
        m_rewrite(len_formula);

        if (check_with_context && !check_with_clauses && !len_has_quantifier && !compute_unsat_core && !compute_model) {
            // the usual case: check the length formula with the arithmetic projection of the context (see
            // collect_arith_projection), which is all the context knows about arithmetic terms, using the
            // incremental solver of the current final check (the length formula is an assumption)
            expr* assumption = len_formula.get();
            lbool ret = get_arith_kernel().check(1, &assumption);
            STRACE(str, tout << "ret (incremental): " << ret << std::endl;);
            return ret;
        }

        bool has_quantifier = len_has_quantifier || (check_with_context && this->input_has_quantifiers);
        std::unique_ptr<lia_solver> solver;
        if (has_quantifier) {
            solver = std::make_unique<quant_lia_solver>(get_manager());
        } else {
            solver = std::make_unique<int_expr_solver>(get_manager(), get_fparams());
        }

        if (check_with_context) {
            solver->initialize(get_context(), true, check_with_clauses);
        }
        lbool ret = solver->check_sat(len_formula, compute_model, compute_unsat_core);
        STRACE(str, tout << "ret" << (has_quantifier ? " (quant)" : "") << ": " << ret << std::endl;);
        if (compute_unsat_core) {
            expr_ref solver_core(m);
            solver_core = m.mk_true();
            solver->get_unsat_core(solver_core);
            *unsat_core = m.mk_and(*unsat_core, solver_core);
        }
        if (compute_model) {
            *model_formula = filter_model_formula_to_length_vars(solver->get_model());
        }
        return ret;
    }

    expr_ref theory_str_noodler::filter_model_formula_to_length_vars(expr_ref model_formula) {
        if (m.is_true(model_formula)) {
            return model_formula;
        }

        // the set of z3 exprs dec_proc actually needs (the length/arith value of) to build the model of some
        // relevant string variable -- see noodler_var_value_proc in theory_str_noodler_model.cpp, which
        // queries dec_proc->get_len_vars_for_model the exact same way when it is time to construct the real
        // model, and resolves each needed BasicTerm to a z3 expr via the same util::basic_term_to_length_expr
        // used below -- so a model equation survives filtering here exactly when noodler_var_value_proc would
        // also ask for its value. Every implementation of get_len_vars_for_model we have either ignores its
        // argument and returns the same (decision-procedure-wide) set every time, or (UnaryDecisionProcedure,
        // where each variable's model depends only on its own length) genuinely needs to be queried per
        // variable, so we query it once per relevant_vars to cover both cases.
        obj_hashtable<expr> needed_exprs;
        expr_ref_vector needed_exprs_pinned(m); // keeps the exprs in needed_exprs alive
        auto add_needed = [&](const BasicTerm& var) {
            expr_ref e = util::basic_term_to_length_expr(var, this->var_name, m, m_util_s, m_util_a);
            needed_exprs.insert(e.get());
            needed_exprs_pinned.push_back(e);
        };
        SASSERT(this->dec_proc);
        for (const BasicTerm& var : this->relevant_vars) {
            for (const BasicTerm& needed : this->dec_proc->get_len_vars_for_model(var)) {
                add_needed(needed);
            }
        }

        // we also need to get models of variables representing conversions, so that the internal solver can give the conversions the
        // correct values (as these are handled by arith solver and not by string solver, so this will force the correct value in the arith solver)
        for (const TermConversion& conv : m_conversion_todo) {
            add_needed(conv.number_var);
        }

        expr_ref_vector conjuncts(m);
        flatten_and(model_formula.get(), conjuncts);
        expr_ref_vector kept(m);
        for (expr* conj : conjuncts) {
            expr *lhs, *rhs;
            if (m.is_eq(conj, lhs, rhs) && needed_exprs.contains(lhs)) {
                kept.push_back(conj);
            } else {
                STRACE(str_sat_handling, tout << "Dropping non-length-sensitive model entry: " << mk_pp(conj, m) << std::endl;);
            }
        }
        return expr_ref(mk_and(kept), m);
    }

    bool theory_str_noodler::is_nielsen_suitable(const Formula& instance, std::unordered_set<BasicTerm>& length_sensitive_vars) const {
        if(!this->m_not_contains_todo_rel.empty() || !this->m_conversion_todo.empty() || !this->m_word_diseq_todo_rel.empty() || instance.contains_pred_type(PredicateType::Transducer)) {
            return false;
        }

        // Nielsen works only with equations; memberships constraining only lengths of variables occurring in the
        // equations can be handled as length constraints (see run_nielsen)
        std::unordered_set<BasicTerm> memb_vars;
        if (!this->m_membership_todo_rel.empty()) {
            const std::set<BasicTerm> instance_vars = instance.get_vars();
            for (const auto& memb : this->m_membership_todo_rel) {
                expr* var = std::get<0>(memb);
                if (!util::is_variable(var) || !is_length_only_regex(std::get<1>(memb))) {
                    return false;
                }
                BasicTerm var_bt = util::get_variable_basic_term(var);
                if (!instance_vars.contains(var_bt)) {
                    return false;
                }
                memb_vars.insert(var_bt);
            }
        }

        if((length_sensitive_vars.size() > 0 || memb_vars.size() > 0) && !instance.is_quadratic()) {
            return false;
        }

        FormulaGraph incl = FormulaGraph::create_inclusion_graph(instance);
        if (!incl.is_cyclic()) {
            return false;
        }
        length_sensitive_vars.insert(memb_vars.begin(), memb_vars.end());
        return true;
    }

    bool theory_str_noodler::is_length_only_regex(expr* re) const {
        if (!is_app(re) || to_app(re)->get_family_id() != m_util_s.get_family_id()) {
            return false;
        }
        app* re_app = to_app(re);
        if (m_util_s.re.is_full_char(re_app) || m_util_s.re.is_full_seq(re_app) || m_util_s.re.is_empty(re_app)) {
            return true;
        }
        if (expr* s = nullptr; m_util_s.re.is_to_re(re_app, s)) {
            return m_util_s.str.is_empty(s);
        }
        switch (re_app->get_decl_kind()) {
            case OP_RE_CONCAT:
            case OP_RE_UNION:
            case OP_RE_INTERSECT:
            case OP_RE_COMPLEMENT:
            case OP_RE_STAR:
            case OP_RE_PLUS:
            case OP_RE_OPTION:
            case OP_RE_LOOP:
            case OP_RE_POWER:
                for (expr* arg : *re_app) {
                    // non-regex arguments are the bounds of loops
                    if (m_util_s.is_re(arg) && !is_length_only_regex(arg)) {
                        return false;
                    }
                }
                return true;
            default:
                return false;
        }
    }

    bool theory_str_noodler::is_underapprox_suitable(const Formula& instance, const AutAssignment& aut_ass, const std::vector<TermConversion>& convs) const {
        if(!convs.empty() || instance.contains_pred_type(PredicateType::Transducer)) {
            return false;
        }
        /**
         * Check each variable occurring within the instance. The instance is suitable for underapproximation if
         * 1) predicates are (dis)equations only and 2) language of the variable is a) sigma star (approximated by
         * the first condition) b) co-finite (complement is a finite language), or c) singleton meaning that the
         * variable is string literal.
         */
        for(const Predicate& pred : instance.get_predicates()) {
            if(!pred.is_eq_or_ineq()) {
                return false;
            }
            for(const BasicTerm& var : pred.get_vars()) {

                if(aut_ass.at(var)->num_of_states() <= 1) {
                    continue;
                }
                if(aut_ass.is_co_finite(var)) {
                    continue;
                }
                if(aut_ass.is_singleton(var)) {
                    continue;
                }
                return false;
            }
        }
        return true;
    }

    lbool theory_str_noodler::run_nielsen(const Formula& instance, const AutAssignment& aut_assignment, const std::unordered_set<BasicTerm>& init_length_sensitive_vars) {
        STRACE(str, tout << "Trying nielsen" << std::endl);
        dec_proc = std::make_shared<NielsenDecisionProcedure>(instance, aut_assignment, init_length_sensitive_vars, m_params);
        dec_proc->preprocess();
        expr_ref block_len(m.mk_false(), m);
        dec_proc->init_computation();
        this->statistics.at("nielsen").num_start++;
        // if there are no length vars in the current string formula, we do not need to check with context
        bool check_len_sat_with_context = !init_length_sensitive_vars.empty();

        // length constraints of (length-only) memberships, which are not handled by Nielsen (see is_nielsen_suitable)
        expr_ref memb_lengths(m.mk_true(), m);
        for (const auto& memb : this->m_membership_todo_rel) {
            BasicTerm var = util::get_variable_basic_term(std::get<0>(memb));
            memb_lengths = m.mk_and(memb_lengths, len_node_to_z3_formula(aut_assignment.get_lengths(var)));
        }

        while (true) {
            lbool result = dec_proc->compute_next_solution();
            if (result == l_true) {
                expr_ref lengths(m.mk_and(len_node_to_z3_formula(dec_proc->get_lengths().first), memb_lengths), m);
                if (check_len_sat(lengths, check_len_sat_with_context) == l_true) {
                    lbool res = sat_handling(lengths, LenCandidateSource::NIELSEN, false, LenNodePrecision::PRECISE);
                    if (res == l_true) {
                        this->statistics.at("nielsen").num_finish++;
                        return l_true;
                    } else if (res == l_undef) {
                        this->statistics.at("nielsen").num_finish++;
                        return l_false; // pending, decided by the main context
                    } else {
                        STRACE(str, tout << "nielsen len unsat" <<  mk_pp(lengths, m) << std::endl;);
                        block_len = m.mk_or(block_len, lengths);
                        check_len_sat_with_context = true;
                    }
                } else {
                    STRACE(str, tout << "nielsen len unsat" <<  mk_pp(lengths, m) << std::endl;);
                    block_len = m.mk_or(block_len, lengths);
                }
            } else if (result == l_false) {
                // we did not find a solution (with satisfiable length constraints)
                // we need to block current assignment
                if (!check_len_sat_with_context) {
                    block_curr_len(expr_ref(m.mk_false(), m));
                } else {
                    block_curr_len(block_len);
                }
                this->statistics.at("nielsen").num_finish++;
                return l_false;
            } else {
                // we could not decide if there is solution, continue with noodler decision procedure
                break;
            }
        }
        return l_undef;
    }

    lbool theory_str_noodler::run_length_proc(const Formula& instance, const AutAssignment& aut_assignment, const std::unordered_set<BasicTerm>& init_length_sensitive_vars) {
        STRACE(str, tout << "Trying length-based procedure" << std::endl);
        // we need a method get_formula from LengthDecisionProcedure
        std::shared_ptr<LengthDecisionProcedure> len_dec_proc = std::make_shared<LengthDecisionProcedure>(instance, aut_assignment, init_length_sensitive_vars, m_params);
        dec_proc = len_dec_proc;
        expr_ref block_len(m.mk_false(), m);
        if (dec_proc->preprocess() == l_false) {
            this->statistics.at("length").num_solved_preprocess++;
            STRACE(str, tout << "len: unsat from preprocessing\n");
            block_curr_len(block_len);
            return l_false;
        }

        this->statistics.at("length").num_start++;
        dec_proc->init_computation();

        bool check_len_sat_with_context = !init_length_sensitive_vars.empty(); // if there are no length vars in the current string formula, we do not need to check with context
        lbool result = dec_proc->compute_next_solution();

        if (result == l_true) {
            auto [formula, precision] = dec_proc->get_lengths();
            expr_ref lengths = len_node_to_z3_formula(formula);
            lbool len_sat = check_len_sat(lengths, check_len_sat_with_context);
            if (len_sat == l_true) {
                lbool res = sat_handling(lengths, LenCandidateSource::LENGTH, precision != LenNodePrecision::UNDERAPPROX, precision);
                if (res == l_true) {
                    this->statistics.at("length").num_finish++;
                    STRACE(str, tout << "len: sat from lengths:" <<  mk_pp(lengths, m) << std::endl;);
                    return l_true;
                } else if (res == l_undef) {
                    this->statistics.at("length").num_finish++;
                    return l_false; // pending, decided by the main context
                } else {
                    len_sat = l_false;
                    check_len_sat_with_context = true;
                }
            }
            if (len_sat == l_false) {
                STRACE(str, tout << "len: unsat from lengths:" <<  mk_pp(lengths, m) << std::endl;);
                block_len = m.mk_or(block_len, lengths);

                if (precision != LenNodePrecision::UNDERAPPROX) {
                    if (!check_len_sat_with_context) {
                        block_curr_len(expr_ref(m.mk_false(), m));
                    } else {
                        block_curr_len(lengths);
                    }
                    this->statistics.at("length").num_finish++;
                    return l_false;
                } else {
                    // An unsatisfiable underapproximation does not justify any lemma (blocking would
                    // exclude real solutions) --> continue with other decision procedures.
                    return l_undef;
                }
            }
        }
        // we could not decide if there is solution, continue with other decision procedure
        return l_undef;
    }

    bool theory_str_noodler::is_mult_membership_suitable() {
        // TODO handle length vars (also the ones without any constraints other than lenght ones, for those we just need to compute arith model)
        if (!this->m_conversion_todo.empty() || !this->m_not_contains_todo_rel.empty() || !this->m_rat_membership_todo_rel.empty() || !this->len_vars.empty()) {
            return false;
        }

        // TODO handle (string_literal in RE) and also length vars, instead of giving up
        for (const auto& membership: m_membership_todo_rel) {
            if(m_util_s.str.is_string(to_app(std::get<0>(membership))) || len_vars.contains(std::get<0>(membership))) {
                return false;
            }
        }

        // we now check if we only have "trivial" (dis)equations, i.e. they can only be of form
        //    x == str_literal or x != str_literal
        // i.e., one variable on the left, a string literal on the right

        for (const auto& diseq : m_word_diseq_todo_rel) {
            if (!(util::is_str_variable(diseq.first, m_util_s) && m_util_s.str.is_string(diseq.second))
                || len_vars.contains(diseq.first)) // TODO handle length vars in run_mult_membership_heur() by using the lengths from the final intersection automaton
            {
                return false;
            }
        }

        for (const auto& eq : m_word_eq_todo_rel) {
            if (!(util::is_str_variable(eq.first, m_util_s) && m_util_s.str.is_string(eq.second))
                || len_vars.contains(eq.first)) // TODO handle length vars in run_mult_membership_heur() by using the lengths from the final intersection automaton
            {
                return false;
            }
        }

        return true;
    }

    lbool theory_str_noodler::run_mult_membership_heur() {
        STRACE(str, tout << "trying multiple regex membership heuristic" << std::endl;);

        regex::Alphabet alph(get_symbols_from_relevant());
        // to each var x we map all the regexes RE where we have (x in RE) + bool that is true if it is (x not in RE)
        std::map<BasicTerm, std::vector<std::pair<bool,app*>>> var_to_list_of_regexes_and_complement_flag;

        // collect from relevant memberships
        for (const auto &membership: m_membership_todo_rel) {
            BasicTerm var = util::get_variable_basic_term(std::get<0>(membership));
            relevant_vars.insert(var);
            app* reg = to_app(std::get<1>(membership));
            var_to_list_of_regexes_and_complement_flag[var].push_back(std::make_pair(!std::get<2>(membership), reg));
        }

        // we assume that is_mult_membership_heur was run before, therefore we have only disequations
        //   x != str_literal
        // i.e., one var on left and some string literal on right, we can replace this with (x not in {str_literal})
        for (const auto& diseq : m_word_diseq_todo_rel) {
            BasicTerm var = util::get_variable_basic_term(diseq.first);
            relevant_vars.insert(var);
            app* reg = to_app(diseq.second);
            var_to_list_of_regexes_and_complement_flag[var].push_back(std::make_pair(true, reg));
        }

        // we assume that is_mult_membership_heur was run before, therefore we have only equations
        //   x == str_literal
        // i.e., one var on left and some string literal on right, we can replace this with (x in {str_literal})
        for (const auto& eq : m_word_eq_todo_rel) {
            BasicTerm var = util::get_variable_basic_term(eq.first);
            relevant_vars.insert(var);
            app* reg = to_app(eq.second);
            var_to_list_of_regexes_and_complement_flag[var].push_back(std::make_pair(false, reg));
        }

        dec_proc = std::make_shared<MultMembHeuristicProcedure>(var_to_list_of_regexes_and_complement_flag, alph, m_util_s, m, nfa_constructor, m_params.m_produce_models);
        this->statistics.at("multi-memb-heur").num_start++;
        lbool result = dec_proc->compute_next_solution();

        if(result != l_undef) this->statistics.at("multi-memb-heur").num_finish++;
        return result;
    }

    lbool theory_str_noodler::run_diseq_length_heur(const Formula& instance, const AutAssignment& aut_assignment, const std::unordered_set<BasicTerm>& init_length_sensitive_vars) {
        dec_proc = std::make_shared<DiseqLengthHeuristicProcedure>(instance, aut_assignment, init_length_sensitive_vars, m_params);
        this->statistics.at("diseq-length-heur").num_start++;

        STRACE(str, tout << "Trying diseq-length heuristic" << std::endl;);

        dec_proc->init_computation();
        if (dec_proc->preprocess() == l_false) {
            this->statistics.at("diseq-length-heur").num_solved_preprocess++;
            block_curr_len(expr_ref(m.mk_false(), m));
            STRACE(str, tout << "Solved by preprocessing: UNSAT" << std::endl;);
            return l_false;
        }

        auto [len_node, precision] = dec_proc->get_lengths();
        expr_ref lengths = len_node_to_z3_formula(len_node);
        (void)precision; // precision is always underapprox for this procedure

        if (check_len_sat(lengths, !init_length_sensitive_vars.empty()) == l_true) { // if there are no length vars in the current string formula, we do not need to check with context
            lbool res = sat_handling(lengths, LenCandidateSource::DISEQ_HEUR, false, LenNodePrecision::UNDERAPPROX);
            if (res == l_true) {
                this->statistics.at("diseq-length-heur").num_finish++;
                STRACE(str, tout << "Solved by diseq-length heuristic: SAT" << std::endl;);
                return l_true;
            } else if (res == l_undef) {
                this->statistics.at("diseq-length-heur").num_finish++;
                return l_false; // pending, decided by the main context
            }
        }
        return l_undef;
    }

    lbool theory_str_noodler::run_loop_protection() {
        expr_ref refine = construct_refinement();
        if (refine != nullptr) {
            bool found = false;
            /**
             * Variable denoting that the only stored instance in @p axiomatized_instances was obtained by unsat from initial lengths or premature LIA checks.
             * In that case if we get SAT from lengths, we do not surely know if it is indeed sat and we need to call the decision procedure again (now it
             * should proceed to the main decision procedure and obtain lengths different from the initial assignment).
             */
            bool overapprox_only = true;
            expr_ref len_formula(this->m);

            for (const auto &pr : this->axiomatized_instances) {
                if (pr.first == refine) {
                    len_formula = pr.second.lengths;
                    overapprox_only = overapprox_only && pr.second.is_overapprox;
                    found = true;
                    STRACE(str,
                        tout << "loop-protection: found ";
                        if (pr.second.is_overapprox) { tout << "(overapprox) "; }
                        tout << std::endl;);

                    // We need to force the LIA solver to find another solution, because adding block_curr_len(len_formula) is not sufficient for SAT solver to get another solution

                    if (len_formula == m.mk_false()) {
                        // if the length formula is false, we can force the LIA solver by adding something completely wrong (but related to strings) -> all lengths are -1
                        STRACE(str, tout << "loop-protection: unsat (len false) " << std::endl;);
                        for (const auto& len_var : len_vars) {
                            len_formula = m.mk_and(len_formula, m.mk_eq(m_util_s.str.mk_length(len_var), m_util_a.mk_int(-1)));
                        }
                        block_curr_len(len_formula, false);
                        return l_false;
                    } else {
                        // otherwise we find unsat core of the current assignment with the len_formula and add this unsat core as a theory lemma.
                        expr_ref unsat_core(m.mk_true(), m);
                        if (check_len_sat(len_formula, true, &unsat_core) == l_false) {
                            unsat_core = m.mk_not(unsat_core);
                            set_input_has_quantifiers(expr_cases::has_quantifier(unsat_core, m));
                            ctx.internalize(unsat_core.get(), true);
                            add_axiom({mk_literal(unsat_core)});
                            block_curr_len(len_formula, false);
                            STRACE(str, tout << "loop-protection: unsat " << std::endl;);
                            return l_false;
                        }
                    }
                }
            }
            if (found && !overapprox_only) {
                /**
                 * If all stored items are SAT and the lengths were obtained from the main decision
                 * procedure --> it is safe to say SAT.
                 */
                STRACE(str, tout << "loop-protection: sat " << std::endl;);
                return l_true;
            }
        }
        STRACE(str, tout << "loop-protection: failed " << std::endl;);
        return l_undef;
    }

    lbool theory_str_noodler::run_length_sat(const Formula& instance, const AutAssignment& aut_ass,
                                const std::unordered_set<BasicTerm>& init_length_sensitive_vars,
                                std::vector<TermConversion> conversions) {

        dec_proc = std::make_shared<UnaryDecisionProcedure>(instance, aut_ass, m_params);
        expr_ref lengths = len_node_to_z3_formula(dec_proc->get_lengths().first);
        this->statistics.at("unary").num_start++;
        this->statistics.at("unary").num_finish++;
        expr_ref model_formula(m);
        bool check_len_sat_with_context = !init_length_sensitive_vars.empty(); // if there are no length vars in the current string formula, we do not need to check with context
        lbool len_sat = check_len_sat(lengths, check_len_sat_with_context);
        if (len_sat == l_true) {
            STRACE(str, tout << "Sat from unary procedure with LIA formula: " << mk_pp(lengths, m) << std::endl);
            lbool res = sat_handling(lengths, LenCandidateSource::UNARY, true, LenNodePrecision::PRECISE);
            if (res == l_true) {
                return l_true;
            } else if (res == l_undef) {
                return l_false; // pending, decided by the main context
            } else {
                len_sat = l_false;
                check_len_sat_with_context = true;
            }
        }
        if (len_sat == l_false) {
            STRACE(str, tout << "Unsat from unary procedure with LIA formula: " << mk_pp(lengths, m) << std::endl);
            if (!check_len_sat_with_context) {
                block_curr_len(expr_ref(m.mk_false(), m));
            } else {
                block_curr_len(lengths);
            }
            return l_false;
        }
        return l_undef;
    }

    lbool theory_str_noodler::sat_handling(expr_ref length_formula, LenCandidateSource source, bool complete, LenNodePrecision precision,
                                           std::shared_ptr<MainEnumState> main_state, bool use_limits) {
        // TODO: using model from external solvers for quantifiers needs some more testing, so it is not enabled for now
        #if 0
        if (expr_cases::has_quantifier(length_formula, m) || this->input_has_quantifiers) {
            expr_ref model_formula(m);
            // meed to include also clauses, as without it the model could be potentionally incorrect
            lbool len_result_with_full_context = check_len_sat(length_formula, true, nullptr, &model_formula, true);
            if (len_result_with_full_context != lbool::l_true) { return len_result_with_full_context; }
            last_run_was_sat = true;
            m_rewrite(model_formula);
            STRACE(str_sat_handling, tout << "Model formula " << mk_pp(model_formula, m) << std::endl;);
            add_axiom(model_formula);
            scope_with_last_run_was_sat = m_scope_level;
            return l_true;
        }
        #endif

        expr_ref base_len = length_formula;
        bool limited = false;

        if (use_limits && m_params.m_produce_models) {
            // If we want to produce models, we would like to limit the lengths more significantly,
            // so that Z3 arith solver does not give us some large numbers (for example it can give 60000
            // and returning such a long model can take a long time).
            // We therefore check if we can still get a model if we limit all lengths by some number.
            const int LENGTH_LIMIT = 100; // this seems a small enough number so that model generation is easy, while allowing model to pass trough for most benchmarks
            auto mk_len_limit = [&](expr* str_var) {
                // |str_var| <= LENGTH_LIMIT
                return expr_ref(m_util_a.mk_le(m_util_s.str.mk_length(str_var), m_util_a.mk_int(LENGTH_LIMIT)), m);
            };
            expr_ref_vector len_constraints(m);
            for (expr* len_var : len_vars) {
                len_constraints.push_back(mk_len_limit(len_var));
            }
            // String variables that are not length variables but whose length occurs in the context (e.g., the fresh
            // variables from the axiom of a contains that is false, see issue #483). Their model is
            // constructed only from their length, which arith solver can set to something huge (e.g., 2^32).
            expr_ref_vector other_len_constraints(m);
            for (enode* n : ctx.enodes()) {
                expr* len_arg = nullptr;
                if (m_util_s.str.is_length(n->get_expr(), len_arg) && ctx.is_relevant(n) && util::is_str_variable(len_arg, m_util_s) && !len_vars.contains(len_arg)) {
                    other_len_constraints.push_back(mk_len_limit(len_arg));
                }
            }
            // we first try to limit all lengths, if it is not possible, we limit only the lengths of length variables
            std::vector<expr_ref> candidates;
            if (!other_len_constraints.empty()) {
                candidates.push_back(expr_ref(m.mk_and(length_formula, m.mk_and(len_constraints), m.mk_and(other_len_constraints)), m));
            }
            if (!len_constraints.empty()) {
                candidates.push_back(expr_ref(m.mk_and(length_formula, m.mk_and(len_constraints)), m));
            }
            for (const expr_ref& length_formula_underapprox : candidates) {
                STRACE(str_sat_handling, tout << "Checking if we can put stronger limits on lengths with formula " << mk_pp(length_formula_underapprox, m) << " which is ";);
                if (check_len_sat(length_formula_underapprox, true) == lbool::l_true) { // we need to check with context, we are asking whether we can limit lengths of all length variables depending (also) on the context
                    // we can limit the lengths => add it to the resulting length formula
                    STRACE(str_sat_handling, tout << "sat\n");
                    length_formula = length_formula_underapprox;
                    limited = true;
                    break;
                } else {
                    STRACE(str_sat_handling, tout << "unsat\n");
                }
            }
        }

        m_rewrite(length_formula);
        if (m.is_true(length_formula)) {
            // nothing to check
            last_run_was_sat = true;
            scope_with_last_run_was_sat = m_scope_level;
            if (precision == LenNodePrecision::OVERAPPROX) {
                ctx.get_fparams().is_overapprox = true;
            }
            return l_true;
        }
        if (m.is_false(length_formula)) {
            return l_false;
        }

        // L holds only for this solution, it cannot be added as an axiom (learned clauses depending on it would
        // be invalid) --> add (not g or L) for a fresh guard g, which the main context decides
        auto pending = std::make_unique<PendingLenCandidate>(m);
        pending->key = construct_refinement();
        pending->guard = m.mk_fresh_const("noodler_len_guard", m.mk_bool_sort());
        add_guarded_len_formula(pending->guard, length_formula, pending->len_atom, pending->len_sign);
        pending->base_len = base_len;
        pending->limited = limited;
        pending->source = source;
        pending->complete = complete;
        pending->precision = precision;
        pending->scope_level = m_scope_level;
        pending->dec_proc = dec_proc;
        pending->relevant_vars = relevant_vars;
        pending->seq_abstraction = seq_abstraction;
        pending->main_state = std::move(main_state);
        STRACE(str, tout << "pending length formula guarded by " << mk_pp(pending->guard, m) << ": " << mk_pp(length_formula, m) << std::endl;);
        m_pending_len = std::move(pending);
        return l_undef;
    }

    void theory_str_noodler::add_guarded_len_formula(expr* guard, expr* length_formula, expr_ref& len_atom, bool& len_sign) {
        if (expr_cases::has_quantifier(length_formula, m)) {
            // quantified formulae (e.g., from not-contains) need the preprocessing of asserted formulae (internalization
            // of existential quantifiers is not supported); (g -> L) is asserted only in the current scope
            set_input_has_quantifiers(true);
            ctx.assert_expr(m.mk_implies(guard, length_formula));
            ctx.internalize_assertions();
            if (!ctx.b_internalized(guard)) {
                ctx.internalize(guard, false);
            }
            len_atom = nullptr;
            len_sign = false;
        } else {
            // the clause is valid on its own (g is fresh), so it is replayed after backtracking
            axiom_recorder recorder(m_axiom_replay);
            literal len_lit = mk_literal(length_formula);
            literal guard_lit = mk_literal(guard);
            add_axiom({~guard_lit, len_lit});
            len_atom = ctx.bool_var2expr(len_lit.var());
            len_sign = len_lit.sign();
        }
        if (!m_len_guards.contains(guard)) {
            m_len_guards.insert(guard);
            m_len_guards_pin.push_back(guard);
        }
        apply_len_guard_hints(guard);
    }

    void theory_str_noodler::apply_len_guard_hints(expr* guard) {
        if (!ctx.b_internalized(guard)) {
            return;
        }
        bool_var v = ctx.get_bool_var(guard);
        ctx.mark_as_relevant(v);
        if (ctx.get_assignment(v) == l_undef) {
            // decide the guard before the atoms of the length formula, trying true first
            ctx.set_true_first_flag(v);
            ctx.inc_bvar_activity(v, 1000.0);
        }
    }

    bool theory_str_noodler::handle_pending_len_candidate(final_check_status& status) {
        if (!m_pending_len) {
            return false;
        }
        if (!m_current_key || m_pending_len->key != m_current_key || !ctx.b_internalized(m_pending_len->guard)) {
            // the instance changed (or the guard was removed by backtracking) --> solve the current instance
            STRACE(str, tout << "pending length candidate dropped" << std::endl;);
            m_pending_len = nullptr;
            return false;
        }
        lbool guard_val = ctx.get_assignment(m_pending_len->guard.get());
        if (guard_val == l_true) {
            if (m_pending_len->len_atom) {
                lbool len_val = ctx.b_internalized(m_pending_len->len_atom) ? ctx.get_assignment(m_pending_len->len_atom.get()) : l_undef;
                if (m_pending_len->len_sign) {
                    len_val = ~len_val;
                }
                if (len_val != l_true) {
                    // cannot happen while the guarded clause is present
                    STRACE(str, tout << "pending length candidate dropped (length formula not true)" << std::endl;);
                    m_pending_len = nullptr;
                    return false;
                }
            }
            // the length formula holds in the context --> the solution is accepted
            STRACE(str, tout << "pending length candidate accepted (" << mk_pp(m_pending_len->guard, m) << ")" << std::endl;);
            dec_proc = m_pending_len->dec_proc;
            relevant_vars = m_pending_len->relevant_vars;
            seq_abstraction = m_pending_len->seq_abstraction;
            if (m_pending_len->precision == LenNodePrecision::OVERAPPROX) {
                ctx.get_fparams().is_overapprox = true;
            }
            last_run_was_sat = true;
            scope_with_last_run_was_sat = m_scope_level;
            // the decision procedure may be modified by the model generation, it cannot be resumed anymore
            m_pending_len = nullptr;
            status = FC_DONE;
            return true;
        }
        if (guard_val == l_undef) {
            // should not happen at final check
            m_pending_len = nullptr;
            return false;
        }

        // the length formula is inconsistent with the context --> continue with the next candidate
        std::unique_ptr<PendingLenCandidate> pending = std::move(m_pending_len);
        STRACE(str, tout << "pending length candidate rejected (" << mk_pp(pending->guard, m) << ")" << std::endl;);
        dec_proc = pending->dec_proc;
        relevant_vars = pending->relevant_vars;
        seq_abstraction = pending->seq_abstraction;
        if (pending->limited) {
            // only the length formula with the length limits for model generation was rejected, try it without them
            lbool res = sat_handling(pending->base_len, pending->source, pending->complete, pending->precision, pending->main_state, false);
            if (res == l_true) {
                status = FC_DONE;
                return true;
            }
            if (res == l_undef) {
                status = FC_CONTINUE;
                return true;
            }
        }
        if (pending->source == LenCandidateSource::MAIN) {
            SASSERT(pending->main_state);
            // as for a length formula inconsistent with the context in run_main_enumeration
            if (pending->precision == LenNodePrecision::UNDERAPPROX) {
                ctx.get_fparams().is_underapprox = true;
            }
            pending->main_state->block_len = m.mk_or(pending->main_state->block_len, pending->base_len);
            pending->main_state->check_len_sat_with_context = true;
            status = run_main_enumeration(pending->main_state);
            return true;
        }
        if (pending->complete) {
            // the length formula characterizes all solutions of the instance, and it is inconsistent with the context
            block_curr_len(pending->base_len);
            status = FC_CONTINUE;
            return true;
        }
        // the procedure is incomplete --> skip it for this instance and continue with the next procedures
        if (m_skip_len_key != m_current_key) {
            m_skip_len_key = m_current_key;
            m_skipped_len_sources.clear();
        }
        m_skipped_len_sources.insert(pending->source);
        dec_proc = nullptr;
        relevant_vars.clear();
        return false;
    }

    expr_ref theory_str_noodler::len_node_to_z3_formula(const LenNode &node) {

        LenFormulaContext context = {
            .manager = this->m,
            .arith_utilities = this->m_util_a,
            .seq_utilities = this->m_util_s,
            .quantified_vars = this->quantif_vars,
            .known_z3_exprs = this->var_name
        };

        return convert_len_node_to_z3_formula(context, node);
    }

    void theory_str_noodler::collect_shared_vars(sbuffer<theory_var> & result) const {
        ptr_buffer<enode> to_unmark;
        unsigned num_vars = get_num_vars();
        for (unsigned i = 0; i < num_vars; i++) {
            enode * n = get_enode(i);
            // it suffices to consider only root shared nodes (thats basically what ctx.is_shared does)
            if(n->is_shared() == l_false || !n->is_root()) {
                continue;
            }
            enode * r = n->get_root();
            // mark to avoid duplicities
            if (r->is_marked()) {
                continue;
            }

            if (!ctx.is_relevant(r) || !((r->get_expr()->get_kind() == ast_kind::AST_APP || r->get_expr()->get_kind() == ast_kind::AST_VAR )) || !m_util_s.is_seq(r->get_sort())) {
                continue;
            }
            // is variable shared among theories?
            if (ctx.is_shared(r)) {
                STRACE(str, tout << "new shared var: #" << r->get_owner_id() << " " << mk_pp(r->get_expr(), m) << "\n";);
                theory_var r_th_var = r->get_th_var(get_id());
                SASSERT(r_th_var != null_theory_var);
                result.push_back(r_th_var);
            }
            r->set_mark();
            to_unmark.push_back(r);            
        }
        unmark_enodes(to_unmark.size(), to_unmark.data());
    }

    expr* theory_str_noodler::get_class_value(enode* n) const {
        for (enode* member : *n->get_root()) {
            if (is_ground_seq_value(member->get_expr())) {
                return member->get_expr();
            }
        }
        return nullptr;
    }

    bool theory_str_noodler::has_fresh_shape(enode* n) const {
        enode* root = n->get_root();
        if (!m_util_s.is_string(root->get_expr()->get_sort())) {
            return false;
        }
        for (enode* member : *root) {
            expr* e = member->get_expr();
            if (is_app(e) && to_app(e)->get_family_id() == m_util_s.get_family_id()) {
                // a literal, a concatenation, or a string function (e.g., str.replace_all) has a value determined by
                // its arguments
                return false;
            }
        }
        return true;
    }

    bool theory_str_noodler::is_fresh_class(enode* n) const {
        if (!has_fresh_shape(n)) {
            return false;
        }
        for (enode* member : *n->get_root()) {
            expr* var = member->get_expr();
            predicate_replace.find(var, var);
            if (util::is_variable(var) && relevant_vars.contains(util::get_variable_basic_term(var))) {
                return false;
            }
        }
        return true;
    }

    unsigned theory_str_noodler::mk_interface_eqs() {
        sbuffer<theory_var> roots;
        collect_shared_vars(roots);
        unsigned result = 0;
        for (unsigned i = 0; i < roots.size(); ++i) {
            enode* n1 = get_enode(roots[i]);
            for (unsigned j = i + 1; j < roots.size(); ++j) {
                enode* n2 = get_enode(roots[j]);
                if (n1->get_expr()->get_sort() != n2->get_expr()->get_sort()) {
                    // shared variables of different (sequence) sorts
                    continue;
                }
                if (ctx.is_diseq(n1, n2)) {
                    // disequation of inter-theory variables are always relevant
                    ctx.mark_as_relevant(m.mk_not(ctx.mk_eq_atom(n1->get_expr(), n2->get_expr())));
                    continue;
                }
                if (ctx.is_eq(n1, n2)) {
                    continue;
                }
                if (surely_different_values(n1->get_root(), n2->get_root(), [this](enode* c) { return is_fresh_class(c); })) {
                    continue;
                }
                if (ctx.assume_eq(n1, n2)) {
                    STRACE(str, tout << "mk_interface_eqs: " << mk_pp(n1->get_expr(), m) << " = " << mk_pp(n2->get_expr(), m) << std::endl;);
                    ++result;
                }
            }
        }
        return result;
    }

    unsigned theory_str_noodler::mk_nth_u_extensionality_eqs() {
        // relevant classes of seq.nth_u(s, i) represented by (root of s, root of i, root of seq.nth_u(s, i))
        struct NthU { enode* seq; enode* idx; enode* app; };
        std::vector<NthU> nths;
        ptr_buffer<enode> to_unmark;
        for (unsigned v = 0; v < get_num_vars(); ++v) {
            enode* r = get_enode(v)->get_root();
            if (r->is_marked() || !m_util_s.is_seq(r->get_sort())) {
                continue;
            }
            r->set_mark();
            to_unmark.push_back(r);
            // parents of the root are the parents of all members of the class
            for (enode* p : r->get_parents()) {
                if (!m_util_s.str.is_nth_u(p->get_expr()) || p->get_arg(0)->get_root() != r || !ctx.is_relevant(p)) {
                    continue;
                }
                enode* idx = p->get_arg(1)->get_root();
                enode* app = p->get_root();
                bool dup = false;
                for (const NthU& o : nths) {
                    if (o.seq == r && o.idx == idx && o.app == app) { dup = true; break; }
                }
                if (!dup) {
                    nths.push_back({r, idx, app});
                }
            }
        }
        unmark_enodes(to_unmark.size(), to_unmark.data());

        unsigned result = 0;
        for (size_t k = 0; k < nths.size(); ++k) {
            for (size_t l = k + 1; l < nths.size(); ++l) {
                const NthU& a = nths[k];
                const NthU& b = nths[l];
                if (a.seq == b.seq || a.seq->get_sort() != b.seq->get_sort()) {
                    // same sequence: the values can differ only by indices (handled by arithmetic)
                    continue;
                }
                if (a.app == b.app) {
                    // both applications have the same value, equal sequences cannot cause a conflict
                    continue;
                }
                if (a.idx != b.idx && m.are_distinct(a.idx->get_expr(), b.idx->get_expr())) {
                    // indices are distinct values (interpreted values are roots of their classes);
                    // we cannot use ctx.is_diseq here, the disequation might be irrelevant and hence
                    // ignored by the arithmetic solver
                    continue;
                }
                app_ref eq(ctx.mk_eq_atom(a.seq->get_expr(), b.seq->get_expr()), m);
                if (m.is_false(eq)) {
                    // distinct values
                    continue;
                }
                STRACE(str, tout << "nth_u extensionality: " << mk_pp(eq, m) << "\n";);
                // We do not rely on ctx.is_diseq (the disequation might be irrelevant and then ignored
                // by the decision procedure), we always use this specific equation atom.
                if (!ctx.b_internalized(eq.get()) || !ctx.is_relevant(eq.get())) {
                    ctx.internalize(eq.get(), false);
                    ctx.mark_as_relevant(eq.get());
                    result++;
                    continue;
                }
                switch (ctx.get_assignment(eq.get())) {
                    case l_false:
                        // the disequation must be passed to the decision procedure
                        ctx.mark_as_relevant(m.mk_not(eq));
                        break;
                    case l_true:
                        // a and b are going to be merged
                        break;
                    default:
                        result++;
                        break;
                }
            }
        }
        return result;
    }
}

namespace smt::noodler {
    bool theory_str_noodler::relevant_has_generic_seq() const {
        auto is_gen = [this](expr* e) {
            return m_util_s.str.is_non_string_sequence(e);
        };
        for (const auto& eq : m_word_eq_todo_rel) {
            if (is_gen(eq.first) || is_gen(eq.second)) return true;
        }
        for (const auto& diseq : m_word_diseq_todo_rel) {
            if (is_gen(diseq.first) || is_gen(diseq.second)) return true;
        }
        for (const auto& memb : m_membership_todo_rel) {
            if (is_gen(std::get<0>(memb))) return true;
        }
        for (const auto& nc : m_not_contains_todo_rel) {
            if (is_gen(nc.first) || is_gen(nc.second)) return true;
        }
        return false;
    }

    bool theory_str_noodler::prepare_seq_abstraction() {
        seq_abstraction = std::make_shared<SeqElementAbstraction>(m, m_util_s, ctx);
        for (const auto& eq : m_word_eq_todo_rel) {
            seq_abstraction->collect(eq.first);
            seq_abstraction->collect(eq.second);
        }
        for (const auto& diseq : m_word_diseq_todo_rel) {
            seq_abstraction->collect(diseq.first);
            seq_abstraction->collect(diseq.second);
        }
        for (const auto& memb : m_membership_todo_rel) {
            seq_abstraction->collect(std::get<0>(memb));
            seq_abstraction->collect(std::get<1>(memb));
        }
        for (const auto& nc : m_not_contains_todo_rel) {
            seq_abstraction->collect(nc.first);
            seq_abstraction->collect(nc.second);
        }
        for (const auto& rat_memb : m_rat_membership_todo_rel) {
            seq_abstraction->collect(std::get<0>(rat_memb));
            seq_abstraction->collect(std::get<1>(rat_memb));
        }
        // sorts of variables replacing functions are not visible in the constraints
        for (const auto& [var, var_expr] : var_name) {
            if (m_util_s.is_seq(var_expr->get_sort())) {
                seq_abstraction->register_seq_sort(var_expr->get_sort());
            }
        }

        bool decided = seq_abstraction->build_classes([this](expr* elem, const ptr_vector<expr>& values) {
            std::vector<literal> clause;
            for (expr* value : values) {
                clause.push_back(mk_eq(elem, value, false));
            }
            STRACE(str, tout << "seq elements: element " << mk_pp(elem, m) << " must be equal to some value of its sort" << std::endl;);
            add_axiom(clause);
        });
        if (!decided) {
            seq_abstraction = nullptr;
        }
        return decided;
    }

    std::function<unsigned(expr*)> theory_str_noodler::get_unit_symbol_fn() const {
        if (!seq_abstraction) {
            return {};
        }
        std::shared_ptr<SeqElementAbstraction> abstraction = seq_abstraction;
        return [abstraction](expr* elem) -> unsigned { return abstraction->get_symbol(elem); };
    }
}
