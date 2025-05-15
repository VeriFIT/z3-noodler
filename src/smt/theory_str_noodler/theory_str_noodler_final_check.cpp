#include <mata/nfa/builder.hh>
#include "formula.h"
#include "smt/theory_str_noodler/theory_str_noodler.h"
#include "memb_heuristics_procedures.h"

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
    final_check_status theory_str_noodler::final_check_eh() {
        TRACE("str", tout << "final_check starts" << std::endl;);

        if (last_run_was_sat) {
            // if we returned previously sat, then we should always return sat (final_check_eh should not be called again, but for some reason Z3 calls it)
            TRACE("str", tout << "Last run was sat on scope level " << scope_with_last_run_was_sat << "\n";);
            if (m_params.m_produce_models) {
                // we need to add previous axioms, so that z3 arith solver returns correct model
                add_axiom(sat_length_formula);
            }
            return FC_DONE;
        }

        dec_proc = nullptr;
        relevant_vars.clear();
        sat_length_formula = expr_ref(m);
        scope_with_last_run_was_sat = -1;

        remove_irrelevant_constr();
        STRACE("str",
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
            tout << "  lang (dis)eqs(" << this->m_lang_eq_or_diseq_todo_rel.size() << "):" << std::endl;
            for (const auto &led: this->m_lang_eq_or_diseq_todo_rel) {
                tout << "    " << mk_pp(std::get<0>(led), m) << (std::get<2>(led) ? " == " : " != ") << mk_pp(std::get<1>(led), m) << std::endl;
            }
            tout << "  not_contains(" << this->m_not_contains_todo_rel.size() << "):" << std::endl;
            for (const auto &notc: this->m_not_contains_todo_rel) {
                tout << "    " << mk_pp(notc.first, m) << "; " << mk_pp(notc.second, m) << std::endl;
            }
            tout << " conversions(" << this->m_conversion_todo.size() << "):" << std::endl;
            for (const auto &conv: this->m_conversion_todo) {
                tout << "    " << get_conversion_name(conv.type) << " with string var " << conv.string_var << " and int var " << conv.int_var << std::endl;
            }
        );

        // Solve Language (dis)equations
        if (!solve_lang_eqs_diseqs()) {
            // one of the (dis)equations is unsat
            return FC_CONTINUE;
        }

        /***************************** SOLVE WORD (DIS)EQUATIONS + REGULAR MEMBERSHIPS ******************************/

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
        bool contains_eqs_and_diseqs_only = this->m_not_contains_todo_rel.empty() && this->m_conversion_todo.empty();

        // nothing is trivially SAT
        if(contains_eqs_and_diseqs_only && this->m_word_eq_todo_rel.empty() && this->m_word_diseq_todo_rel.empty() && this->m_membership_todo_rel.empty() ) {
            return FC_DONE;
        }

        // As a heuristic, for the case we have exactly one constraint, which is of type 'x (not)in RE', we use universality/emptiness
        // checking of the regex (using some heuristics) instead of constructing the automaton of RE. The construction (especially complement)
        // can sometimes blow up, so the check should be faster.
        if(m_params.m_try_memb_heur && this->m_membership_todo_rel.size() == 1 && !contains_word_equations && !contains_word_disequations && !contains_conversions && this->m_not_contains_todo_rel.size() == 0
                && this->len_vars.empty() // TODO: handle length vars that are not x (i.e., there are no string constraints on them, other than length ones, we just need to compute arith model)
        ) {
            const auto& reg_data = this->m_membership_todo_rel[0];
            // TODO: check if "xyz in RE" works correctly
            expr_ref var = std::get<0>(reg_data);
            if (util::is_str_variable(var, m_util_s) && !this->len_vars.contains(var)) { // the variable cannot be length one
                STRACE("str", tout << "trying one membership heuristics\n";);
                BasicTerm noodler_var = util::get_variable_basic_term(var);
                relevant_vars.insert(noodler_var);
                dec_proc = std::make_shared<MembHeuristicProcedure>(
                    noodler_var,
                    std::get<1>(reg_data),
                    std::get<2>(reg_data),
                    m_util_s, m, m_params.m_produce_models
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

        if (m_params.m_try_memb_heur && is_mult_membership_suitable()) {
            lbool result = run_mult_membership_heur();
            if(result == l_true) {
                return FC_DONE;
            } else if(result == l_false) {
                block_curr_len(expr_ref(this->m.mk_false(), this->m)); // there should not be any length vars, so we block fully
                return FC_CONTINUE;
            }
        }

        // Gather symbols from relevant (dis)equations and from regular expressions of relevant memberships
        std::set<mata::Symbol> symbols_in_formula = get_symbols_from_relevant();

        // For the case that it is possible we have to_int/from_int, we keep digits (0-9) as explicit symbols, so that they are not represented by dummy_symbol and it is easier to handle to_int/from_int
        if (!m_conversion_todo.empty()) {
            for (mata::Symbol s = 48; s <= 57; ++s) {
                symbols_in_formula.insert(s);
            }
        }

        // Gather relevant word (dis)equations (and transducers that occur in them) to noodler formula
        Formula instance = get_formula_from_relevant(symbols_in_formula);

        // Create automata assignment for the formula
        AutAssignment aut_assignment{create_aut_assignment_for_formula(instance, symbols_in_formula)};

        bool contains_transducers = instance.contains_pred_type(PredicateType::Transducer);

        std::vector<TermConversion> conversions = get_conversions_as_basicterms(aut_assignment, symbols_in_formula);

        for (const auto& [var, nfa] : aut_assignment) {
            relevant_vars.insert(var);
        }

        // Get the initial length vars that are needed here (i.e they are in aut_assignment)
        std::unordered_set<BasicTerm> init_length_sensitive_vars{ get_init_length_vars(aut_assignment) };
        STRACE("str",
            tout << "Relevant formula:\n" << instance.to_string();
            for (const auto& conv : conversions) {
                tout << get_conversion_name(conv.type) << " with string var " << conv.string_var << " and int var " << conv.int_var << std::endl;
            }
            tout << "Length variables:";
            for (const auto &len_var : init_length_sensitive_vars) {
                tout << " " << len_var;
            }
            tout << std::endl
        );


        // There is only one symbol in the equation. The system is SAT iff lengths are SAT
        if(m_params.m_try_unary_proc && symbols_in_formula.size() == 2 && !contains_conversions && !contains_transducers && this->m_not_contains_todo_rel.size() == 0 && UnaryDecisionProcedure::is_suitable(instance, aut_assignment)) { // dummy symbol + 1
            lbool result = run_length_sat(instance, aut_assignment, init_length_sensitive_vars, conversions);
            if(result == l_true) {
                return FC_DONE;
            } else if(result == l_false) {
                return FC_CONTINUE;
            }
        }

        // try Nielsen transformation (if enabled) to solve
        if(m_params.m_try_nielsen && is_nielsen_suitable(instance, init_length_sensitive_vars)) {
            lbool result = run_nielsen(instance, aut_assignment, init_length_sensitive_vars);
            if(result == l_true) {
                return FC_DONE;
            } else if(result == l_false) {
                return FC_CONTINUE;
            }
        }

        // we do not put into dec_proc directly, because we might do underapproximation that saves into dec_proc
        std::shared_ptr<DecisionProcedure> main_dec_proc = std::make_shared<DecisionProcedure>(instance, aut_assignment, init_length_sensitive_vars, m_params, conversions);

        // the skip_len_sat preprocessing rule requires that the input formula is length satisfiable
        // --> before we apply the preprocessing, we need to be sure that it is indeed true.
        // length constraints from initial assignment
        // we want to include all variables from the formula --> e.g.
        // s.t = u where u \in ab, |s| > 100. The only length variable is s, but we need
        // to include also length of |u| to propagate the value to |s|
        expr_ref lengths = len_node_to_z3_formula(main_dec_proc->get_initial_lengths(true));
        if(check_len_sat(lengths) == l_false) {
            STRACE("str", tout << "Unsat from initial lengths" << std::endl);

            this->statistics.at("stabilization").num_solved_preprocess++;
            // If the instance is both length unsatisfiable and unsatisfiable from preprocessing,
            // we want to kill it after preprocessing as it generates stronger theory lemma (negation of the string part).
            lbool result = main_dec_proc->preprocess(PreprocessType::PLAIN, this->var_eqs.get_equivalence_bt(aut_assignment));
            if (result == l_false) {
                block_curr_len(expr_ref(m.mk_false(), m), false, true);
            } else {
                block_curr_len(lengths, true, true);
            }
            return FC_CONTINUE;

        }

        // now we know that the initial formula is length-satisfiable
        // try length-based decision procedure (if enabled) to solve
        if(m_params.m_try_length_proc && contains_eqs_and_diseqs_only && !contains_transducers && LengthDecisionProcedure::is_suitable(instance, aut_assignment)) {
            lbool result = run_length_proc(instance, aut_assignment, init_length_sensitive_vars);
            if(result == l_true) {
                return FC_DONE;
            } else if(result == l_false) {
                return FC_CONTINUE;
            }
        }

        // try underapproximation (if enabled) to solve
        if(m_params.m_underapproximation && is_underapprox_suitable(instance, aut_assignment, conversions)) {
            STRACE("str", tout << "Try underapproximation" << std::endl);
            if (solve_underapprox(instance, aut_assignment, init_length_sensitive_vars, conversions) == l_true) {
                STRACE("str", tout << "Sat from underapproximation" << std::endl;);
                return FC_DONE;
            }
            STRACE("str", tout << "Underapproximation did not help\n";);
        }

        dec_proc = std::move(main_dec_proc);

        STRACE("str", tout << "Starting preprocessing" << std::endl);
        lbool result = dec_proc->preprocess(PreprocessType::PLAIN, this->var_eqs.get_equivalence_bt(aut_assignment));
        if (result == l_false) {
            this->statistics.at("stabilization").num_solved_preprocess++;
            STRACE("str", tout << "Unsat from preprocessing" << std::endl);
            block_curr_len(expr_ref(m.mk_false(), m), false, true); // we do not store for loop protection
            return FC_CONTINUE;
        } // we do not check for l_true, because we will get it in get_another_solution() anyway TODO: should we check?

        // it is possible that the arithmetic formula becomes unsatisfiable already by adding the
        // length constraints from initial assignment
        lengths = len_node_to_z3_formula(dec_proc->get_initial_lengths());
        if(check_len_sat(lengths) == l_false) {
            this->statistics.at("stabilization").num_solved_preprocess++;
            STRACE("str", tout << "Unsat from initial lengths" << std::endl);
            block_curr_len(lengths, true, true);
            return FC_CONTINUE;
        }

        STRACE("str", tout << "Starting main decision procedure" << std::endl);
        dec_proc->init_computation();
        this->statistics.at("stabilization").num_start++;

        expr_ref block_len(m.mk_false(), m);
        while (true) {
            result = dec_proc->compute_next_solution();
            if (result == l_true) {
                auto [noodler_lengths, precision] = dec_proc->get_lengths();

                lengths = len_node_to_z3_formula(noodler_lengths);

                STRACE("str-print-notcontains-lia",
                    std::ofstream out_file("./not-contains-lia.smt2");
                    write_z3_expr_into_stream(this->m, out_file, lengths);
                    out_file.close();
                );

                lbool is_lengths_sat = check_len_sat(lengths);

                if (is_lengths_sat == l_true) {
                    STRACE("str", tout << "len sat " << mk_pp(lengths, m) << std::endl;);
                    sat_handling(lengths);

                    if(precision == LenNodePrecision::OVERAPPROX) {
                        ctx.get_fparams().is_overapprox = true;
                    }

                    this->statistics.at("stabilization").num_finish++;
                    return FC_DONE;
                } else if (is_lengths_sat == l_false) {
                    STRACE("str", tout << "len unsat " <<  mk_pp(lengths, m) << std::endl;);
                    block_len = m.mk_or(block_len, lengths);

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
                STRACE("str", tout << "assignment unsat " << mk_pp(block_len, m) << std::endl;);

                if(m.is_false(block_len)) {
                    block_curr_len(block_len, false, true);
                // if there are no length vars comming from the initial formula (or from axiom saturation),
                // we can block the string assignment only
                // Note that if we use tag automata for handling disequations/notcontains, the variables inside them 
                // are included to lenght vars during the procedure. Therefore, if dec_proc->get_init_length_sensitive_vars()
                // is empty, there are no disequations/notcontains
                } else if(init_length_sensitive_vars.size() == 0 && dec_proc->get_init_length_sensitive_vars().empty()) {
                    block_curr_len(expr_ref(m.mk_false(), m));
                } else {
                    block_curr_len(block_len);
                }
                this->statistics.at("stabilization").num_finish++;
                return FC_CONTINUE;
            } else {
                // we could not decide if there is solution, let's just give up
                STRACE("str", tout << "giving up" << std::endl);
                return FC_GIVEUP;
            }
        }
    }

    void theory_str_noodler::remove_irrelevant_constr() {
        STRACE("str", tout << "Remove irrevelant" << std::endl);

        this->m_word_eq_todo_rel.clear();
        this->m_word_diseq_todo_rel.clear();
        this->m_membership_todo_rel.clear();
        this->m_lang_eq_or_diseq_todo_rel.clear();
        this->m_not_contains_todo_rel.clear();

        for (const auto& we : m_word_eq_todo) {
            app_ref eq(m.mk_eq(we.first, we.second), m);
            app_ref eq_rev(m.mk_eq(we.second, we.first), m);

            STRACE("str",
                tout << "  Eq " << mk_pp(eq.get(), m) << " is " << (ctx.is_relevant(eq.get()) ? "" : "not ") << "relevant"
                     << " with assignment " << ctx.find_assignment(eq.get())
                     << " and its reverse is " << (ctx.is_relevant(eq_rev.get()) ? "" : "not ") << "relevant" << std::endl;
            );

            // check if equation or its reverse are relevant (we check reverse to be safe) and...
            if((ctx.is_relevant(eq.get()) || ctx.is_relevant(eq_rev.get())) &&
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

            STRACE("str",
                tout << "  Diseq " << mk_pp(dis.get(), m) << " is " << (ctx.is_relevant(dis.get()) ? "" : "not ") << "relevant"
                     << " with assignment " << ctx.find_assignment(dis.get())
                     << " and its reverse is " << (ctx.is_relevant(dis_rev.get()) ? "" : "not ") << "relevant" << std::endl;
            );

            // check if disequation or its reverse are relevant (we check reverse to be safe) and...
            if((ctx.is_relevant(dis.get()) || ctx.is_relevant(dis_rev.get())) &&
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

            STRACE("str",
                tout << "  " << mk_pp(memb_app.get(), m) << " is " << (ctx.is_relevant(memb_app.get()) ? "" : "not ") << "relevant"
                     << " with assignment " << ctx.find_assignment(memb_app.get())
                     << ", " << mk_pp(memb_app_orig.get(), m) << " is " << (ctx.is_relevant(memb_app_orig.get()) ? "" : "not ") << "relevant"
                     << std::endl;
            );

            // check if membership (or if we have negation, its negated form) is relevant and...
            if((ctx.is_relevant(memb_app.get()) || ctx.is_relevant(memb_app_orig.get())) &&
               // this membership constraint is not added to relevant yet
               !this->m_membership_todo_rel.contains(memb)
               ) {
                this->m_membership_todo_rel.push_back(memb);
            }
        }

        // not contains
        for(const auto& not_con_pair: this->m_not_contains_todo) {
            app_ref con_expr(m_util_s.str.mk_contains(not_con_pair.first, not_con_pair.second), m);
            app_ref not_con_expr(m.mk_not(con_expr), m);

            STRACE("str",
                tout << "  NOT contains " << mk_pp(con_expr.get(), m) << " is " << (ctx.is_relevant(con_expr.get()) ? "" : "not ") << "relevant"
                     << " with assignment " << ctx.find_assignment(con_expr.get())
                     << ", " << mk_pp(not_con_expr.get(), m) << " is " << (ctx.is_relevant(not_con_expr.get()) ? "" : "not ") << "relevant"
                     << std::endl;
            );

            if((ctx.is_relevant(con_expr.get()) || ctx.is_relevant(not_con_expr.get())) &&
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
        STRACE("str-conv-eq", tout << "conv_eq_pred: " << mk_pp(ex, m) << std::endl);
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

        obj_hashtable<expr> vars;
        util::get_str_variables(ex, this->m_util_s, this->m, vars);
        for(expr * const v : vars) {

            BasicTerm vterm(BasicTermType::Variable, to_app(v)->get_name().str());
            this->var_name.insert({vterm, expr_ref(v, this->m)});
        }

        std::vector<BasicTerm> left, right;
        util::collect_terms(to_app(eq->get_arg(0)), m, this->m_util_s, this->predicate_replace, this->var_name, left);
        util::collect_terms(to_app(eq->get_arg(1)), m, this->m_util_s, this->predicate_replace, this->var_name, right);

        return Predicate(ptype, std::vector<std::vector<BasicTerm>>{left, right});
    }

    bool theory_str_noodler::is_tmp_transducer_eq(app* const ex) {
        if (this->m_util_s.str.is_replace_all(ex->get_arg(0)) || this->m_util_s.str.is_replace_re_all(ex->get_arg(0))) {
            expr* rpl = this->predicate_replace.find(ex->get_arg(0));
            return rpl->hash() == ex->get_arg(1)->hash();
        }
        if (this->m_util_s.str.is_replace_all(ex->get_arg(1)) || this->m_util_s.str.is_replace_re_all(ex->get_arg(1))) {
            expr* rpl = this->predicate_replace.find(ex->get_arg(1));
            return rpl->hash() == ex->get_arg(0)->hash();
        }
        return false;
    }

    Formula theory_str_noodler::get_formula_from_relevant(const std::set<mata::Symbol>& alph) {
        Formula instance;
        // create mata alphabet for transducer constraints
        mata::EnumAlphabet mata_alph{};
        for(const mata::Symbol& symb : alph) {
            mata_alph.add_new_symbol(symb);
        }

        for (const auto &we: this->m_word_eq_todo_rel) {
            // ignore trivial equations obtained from axiomatization of 
            // transducer constraints, e.g., tmp = replace_all(...)
            if(is_tmp_transducer_eq(ctx.mk_eq_atom(we.first, we.second))) {
                continue;
            }
            Predicate inst = this->conv_eq_pred(ctx.mk_eq_atom(we.first, we.second));
            // gather transducer constraints occurring in the concatenation
            regex::gather_transducer_constraints(to_app(we.first), m, this->m_util_s, this->predicate_replace, this->var_name, &mata_alph, instance);
            regex::gather_transducer_constraints(to_app(we.second), m, this->m_util_s, this->predicate_replace, this->var_name, &mata_alph, instance);
            instance.add_predicate(inst);
        }

        for (const auto& wd : this->m_word_diseq_todo_rel) {
            Predicate inst = this->conv_eq_pred(m.mk_not(ctx.mk_eq_atom(wd.first, wd.second)));
            // gather transducer constraints occurring in the concatenation
            regex::gather_transducer_constraints(to_app(wd.first), m, this->m_util_s, this->predicate_replace, this->var_name, &mata_alph, instance);
            regex::gather_transducer_constraints(to_app(wd.second), m, this->m_util_s, this->predicate_replace, this->var_name, &mata_alph, instance);
            instance.add_predicate(inst);
        }

        // construct not contains predicates
        for(const auto& not_contains : this->m_not_contains_todo_rel) {
            std::vector<BasicTerm> left, right;
            util::collect_terms(to_app(not_contains.first), m, this->m_util_s, this->predicate_replace, this->var_name, left);
            util::collect_terms(to_app(not_contains.second), m, this->m_util_s, this->predicate_replace, this->var_name, right);
            // gather transducer constraints occurring in the concatenation
            regex::gather_transducer_constraints(to_app(not_contains.first), m, this->m_util_s, this->predicate_replace, this->var_name, &mata_alph, instance);
            regex::gather_transducer_constraints(to_app(not_contains.second), m, this->m_util_s, this->predicate_replace, this->var_name, &mata_alph, instance);
            Predicate inst = Predicate::create_not_contains(left, right);
            instance.add_predicate(inst);
        }

        for (const auto& conv : this->m_conversion_todo) {
            regex::gather_transducer_constraints(to_app(var_name.at(conv.string_var)), m, this->m_util_s, this->predicate_replace, this->var_name, &mata_alph, instance);
        }

        for (const auto& len: len_vars) {
            regex::gather_transducer_constraints(to_app(len), m, this->m_util_s, this->predicate_replace, this->var_name, &mata_alph, instance);
        }

        return instance;
    }

    std::set<mata::Symbol> theory_str_noodler::get_symbols_from_relevant() {
        // start with symbol representing everything not in formula
        std::set<mata::Symbol> symbols_in_formula{util::get_dummy_symbol()};

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
        // extract from not contains
        for(const auto& not_contains : m_not_contains_todo_rel) {
            regex::extract_symbols(not_contains.first, m_util_s, symbols_in_formula);
            regex::extract_symbols(not_contains.second, m_util_s, symbols_in_formula);
        }

        return symbols_in_formula;
    }

    AutAssignment theory_str_noodler::create_aut_assignment_for_formula(
            Formula& instance,
            const std::set<mata::Symbol>& noodler_alphabet
    ) {
        AutAssignment aut_assignment{};
        aut_assignment.set_alphabet(noodler_alphabet);
        regex::Alphabet alph(noodler_alphabet);
        mata::EnumAlphabet mata_alphabet(noodler_alphabet.begin(), noodler_alphabet.end());
        for (const auto &membership: m_membership_todo_rel) {
            const expr_ref& var_expr{ std::get<0>(membership) };
            assert(is_app(var_expr));
            const auto& var_app{ to_app(var_expr) };
            assert(var_app->get_num_args() == 0);
            const std::string& variable_name{ var_app->get_decl()->get_name().str() };

            zstring s;
            BasicTerm term{ BasicTermType::Variable, variable_name };
            if(m_util_s.str.is_string(var_app, s)) {
                term = BasicTerm(BasicTermType::Literal, s.encode());
            }
            // If the regular constraint is in a negative form, create a complement of the regular expression instead.
            const bool make_complement{ !std::get<2>(membership) };
            mata::nfa::Nfa nfa{ regex::conv_to_nfa(to_app(std::get<1>(membership)), m_util_s, m, alph, make_complement, make_complement) };
            auto aut_ass_it{ aut_assignment.find(term) };
            if (aut_ass_it != aut_assignment.end()) {
                // This variable already has some regular constraints. Hence, we create an intersection of the new one
                //  with the previously existing.
                aut_ass_it->second = std::make_shared<mata::nfa::Nfa>(
                        mata::nfa::reduce(mata::nfa::intersection(nfa, *aut_ass_it->second)));

            } else { // We create a regular constraint for the current variable for the first time.
                aut_assignment[term] = std::make_shared<mata::nfa::Nfa>(std::forward<mata::nfa::Nfa>(std::move(nfa)));
                // TODO explain after this function is moved to theory_str_noodler, we do this because var_name contains only variables occuring in instance and not those that occur only in str.in_re
                this->var_name.insert({term, var_expr});
            }

            // we also need to gather transducer constraints for the var
            regex::gather_transducer_constraints(var_app, m, this->m_util_s, this->predicate_replace, this->var_name, &mata_alphabet, instance);
        }

        // create sigma star automaton for our alphabet
        auto nfa_sigma_star = std::make_shared<mata::nfa::Nfa>(mata::nfa::builder::create_sigma_star_nfa(&mata_alphabet));
        // remove the pointer to alphabet in the automaton, as it points to local variable (and we have the alphabet in aut_assignment)
        nfa_sigma_star->alphabet = nullptr;

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

        TRACE("str-nfa",
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

    std::vector<TermConversion> theory_str_noodler::get_conversions_as_basicterms(AutAssignment& ass, const std::set<mata::Symbol>& noodler_alphabet) {
        mata::EnumAlphabet mata_alphabet(noodler_alphabet.begin(), noodler_alphabet.end());
        auto nfa_sigma_star = std::make_shared<mata::nfa::Nfa>(mata::nfa::builder::create_sigma_star_nfa(&mata_alphabet));

        std::vector<TermConversion> conversions;
        for (const auto& transf : m_conversion_todo) {
            ass.insert({transf.string_var, nfa_sigma_star});
            conversions.push_back(transf);
        }
        return conversions;
    }

    bool theory_str_noodler::solve_lang_eqs_diseqs() {
        for(const auto& item : this->m_lang_eq_or_diseq_todo_rel) {
            expr_ref left_side = std::get<0>(item);
            expr_ref right_side = std::get<1>(item);
            bool is_equation = std::get<2>(item);

            if (util::is_variable(left_side) || util::is_variable(right_side)) {
                // RegLan variables are replaced by rewriter if we have some equation "v = some regular lang",
                // but if we get some completely unrestricted variables (for example just disequation "v != v'"),
                // we throw error (TODO: we could possibly handle this, theoretically we could just ignore this
                // sort of disequations, as we can always find a language that differs and equations should not
                // have unrestricted RegLan anyway, as they are also replaced by rewriter)
                util::throw_error("unrestricted RegLan variables in disequations are not supported");
            }

            STRACE("str",
                tout << "Checking lang (dis)eq: " << mk_pp(left_side, m) << (is_equation ? " == " : " != ") << mk_pp(right_side, m) << std::endl;
            );

            // get symbols from both sides
            std::set<uint32_t> alphabet;
            regex::extract_symbols(left_side, m_util_s, alphabet);
            regex::extract_symbols(right_side, m_util_s, alphabet);
            regex::Alphabet alph(alphabet);

            // construct NFAs for both sides
            mata::nfa::Nfa nfa1 = regex::conv_to_nfa(to_app(left_side), m_util_s, m, alph, false );
            mata::nfa::Nfa nfa2 = regex::conv_to_nfa(to_app(right_side), m_util_s, m ,alph, false );

            // check if NFAs are equivalent (if we have equation) or not (if we have disequation)
            bool are_equiv;
            // for the case that one side is empty, we just need to check if the other automaton is empty
            if (nfa1.num_of_states() == 0) {
                are_equiv = nfa2.is_lang_empty();
            } else if (nfa2.num_of_states() == 0) {
                are_equiv = nfa1.is_lang_empty();
            } else {
                are_equiv = mata::nfa::are_equivalent(nfa1, nfa2);
            }
            if ((is_equation && !are_equiv) || (!is_equation && are_equiv)) {
                // the language (dis)equation does not hold => block it and return
                app_ref lang_eq(m.mk_eq(left_side, right_side), m);
                if(is_equation){
                    STRACE("str", tout << mk_pp(lang_eq, m) << " is unsat" << std::endl);
                    add_axiom({mk_literal(m.mk_not(lang_eq))});
                } else {
                    STRACE("str", tout << mk_pp(m.mk_not(lang_eq), m) << " is unsat" << std::endl);
                    add_axiom({mk_literal(lang_eq)});
                }
                return false;
            }
        }

        // if we are here, all (dis)equations hold
        return true;
    }

    lbool theory_str_noodler::solve_underapprox(const Formula& instance, const AutAssignment& aut_assignment,
                                                const std::unordered_set<BasicTerm>& init_length_sensitive_vars,
                                                std::vector<TermConversion> conversions) {
        dec_proc = std::make_shared<DecisionProcedure>(instance, aut_assignment, init_length_sensitive_vars, m_params, conversions);
        if (dec_proc->preprocess(PreprocessType::UNDERAPPROX, this->var_eqs.get_equivalence_bt(aut_assignment)) == l_false) {
            return l_undef;
        }

        dec_proc->init_computation();
        this->statistics.at("underapprox").num_start++;

        while(dec_proc->compute_next_solution() == l_true) {
            expr_ref lengths = len_node_to_z3_formula(dec_proc->get_lengths().first);
            if(check_len_sat(lengths) == l_true) {
                sat_handling(lengths);
                this->statistics.at("underapprox").num_finish++;
                return l_true;
            }
        }
        return l_undef;
    }

    lbool theory_str_noodler::check_len_sat(expr_ref len_formula, expr_ref* unsat_core) {
        if (len_formula == m.mk_true() && (len_vars.empty() || !m_params.m_produce_models)) {
            // we assume here that existing length constraints are satisfiable, so adding true will do nothing
            // however, for model generation, we need to always produce models if we have some length vars
            return l_true;
        }

        // if the length formula has quantifiers --> use quant_lia_solver
        // TODO: the quant_lia_solver does not support UNSAT cores
        if(expr_cases::has_quantifier(len_formula, m)) {
            m_rewrite(len_formula);
            quant_lia_solver m_quant_int_solver(get_manager());
            m_quant_int_solver.initialize(get_context());

            lbool is_sat = m_quant_int_solver.check_sat(len_formula);
            return is_sat;
        }

        int_expr_solver m_int_solver(get_manager(), get_fparams());
        // do we solve only regular constraints (and we do not want to produce models)? If yes, skip other temporary length constraints (they are not necessary)
        bool include_ass = true;
        if(this->m_word_diseq_todo_rel.size() == 0 && this->m_word_eq_todo_rel.size() == 0 && this->m_not_contains_todo.size() == 0 && this->m_conversion_todo.size() == 0 && !m_params.m_produce_models) {
            include_ass = false;
        }
        m_int_solver.initialize(get_context(), include_ass);
        auto ret = m_int_solver.check_sat(len_formula);
        // construct an unsat core --> might be expensive
        // TODO: better interface of m_int_solver
        if(unsat_core != nullptr) {
            for(unsigned i=0;i<m_int_solver.m_kernel.get_unsat_core_size();i++){
                *unsat_core = m.mk_and(*unsat_core, m_int_solver.m_kernel.get_unsat_core_expr(i));
            }
        }
        return ret;
    }

    void theory_str_noodler::block_curr_len(expr_ref len_formula, bool add_axiomatized, bool init_lengths) {
        STRACE("str-block", tout << __LINE__ << " enter " << __FUNCTION__ << std::endl;);

        context& ctx = get_context();

        ast_manager& m = get_manager();
        expr *refinement = nullptr;
        for (const auto& we : this->m_word_eq_todo_rel) {
            // we create the equation according to we
            //expr *const e = m.mk_not(m.mk_eq(we.first, we.second));
            expr *const e = ctx.mk_eq_atom(we.first, we.second);
            refinement = refinement == nullptr ? e : m.mk_and(refinement, e);
        }

        literal_vector ls;
        for (const auto& wi : this->m_word_diseq_todo_rel) {
            expr_ref e(m.mk_not(ctx.mk_eq_atom(wi.first, wi.second)), m);
            refinement = refinement == nullptr ? e : m.mk_and(refinement, e);
        }

        for (const auto& in : this->m_membership_todo_rel) {
            app_ref in_app(m_util_s.re.mk_in_re(std::get<0>(in), std::get<1>(in)), m);
            if(!std::get<2>(in)){
                in_app = m.mk_not(in_app);
            }
            if(!ctx.e_internalized(in_app)) {
                ctx.internalize(in_app, false);
            }
            refinement = refinement == nullptr ? in_app : m.mk_and(refinement, in_app);
        }

        for(const auto& nc : this->m_not_contains_todo_rel) {
            app_ref nc_app(m.mk_not(m_util_s.str.mk_contains(nc.first, nc.second)), m);
            refinement = refinement == nullptr ? nc_app : m.mk_and(refinement, nc_app);
        }

        if(m_params.m_loop_protect && add_axiomatized) {
            this->axiomatized_instances.push_back({expr_ref(refinement, this->m), stored_instance{ .lengths = len_formula, .initial_length = init_lengths}});
        }
        if (refinement != nullptr) {
            add_axiom(m.mk_or(m.mk_not(refinement), len_formula));
        }
        STRACE("str-block", tout << __LINE__ << " leave " << __FUNCTION__ << std::endl;);
    }

    bool theory_str_noodler::is_nielsen_suitable(const Formula& instance, const std::unordered_set<BasicTerm>& init_length_sensitive_vars) const {
        if(!this->m_membership_todo_rel.empty() || !this->m_not_contains_todo_rel.empty() || !this->m_conversion_todo.empty() || !this->m_word_diseq_todo_rel.empty() || instance.contains_pred_type(PredicateType::Transducer)) {
            return false;
        }

        if(init_length_sensitive_vars.size() > 0 && !instance.is_quadratic()) {
            return false;
        }

        FormulaGraph incl = FormulaGraph::create_inclusion_graph(instance);
        return incl.is_cyclic();
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
        STRACE("str", tout << "Trying nielsen" << std::endl);
        dec_proc = std::make_shared<NielsenDecisionProcedure>(instance, aut_assignment, init_length_sensitive_vars, m_params);
        dec_proc->preprocess();
        expr_ref block_len(m.mk_false(), m);
        dec_proc->init_computation();
        this->statistics.at("nielsen").num_start++;

        while (true) {
            lbool result = dec_proc->compute_next_solution();
            if (result == l_true) {
                expr_ref lengths = len_node_to_z3_formula(dec_proc->get_lengths().first);
                if (check_len_sat(lengths) == l_true) {
                    sat_handling(lengths);
                    this->statistics.at("nielsen").num_finish++;
                    return l_true;
                } else {
                    STRACE("str", tout << "nielsen len unsat" <<  mk_pp(lengths, m) << std::endl;);
                    block_len = m.mk_or(block_len, lengths);
                }
            } else if (result == l_false) {
                // we did not find a solution (with satisfiable length constraints)
                // we need to block current assignment
                block_curr_len(block_len);
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
        STRACE("str", tout << "Trying length-based procedure" << std::endl);
        // we need a method get_formula from LengthDecisionProcedure
        std::shared_ptr<LengthDecisionProcedure> len_dec_proc = std::make_shared<LengthDecisionProcedure>(instance, aut_assignment, init_length_sensitive_vars, m_params);
        dec_proc = len_dec_proc;
        expr_ref block_len(m.mk_false(), m);
        if (dec_proc->preprocess() == l_false) {
            this->statistics.at("length").num_solved_preprocess++;
            STRACE("str", tout << "len: unsat from preprocessing\n");
            block_curr_len(block_len);
            return l_false;
        }

        this->statistics.at("length").num_start++;
        dec_proc->init_computation();

        lbool result = dec_proc->compute_next_solution();

        if (result == l_true) {
            auto [formula, precision] = dec_proc->get_lengths();
            expr_ref lengths = len_node_to_z3_formula(formula);
            if (check_len_sat(lengths) == l_true) {
                sat_handling(lengths);
                this->statistics.at("length").num_finish++;
                return l_true;
            } else {
                STRACE("str", tout << "len: unsat from lengths:" <<  mk_pp(lengths, m) << std::endl;);
                block_len = m.mk_or(block_len, lengths);

                if (precision != LenNodePrecision::UNDERAPPROX) {
                    block_curr_len(lengths);
                    this->statistics.at("length").num_finish++;
                    return l_false;
                }
                else if (len_dec_proc->get_formula().get_predicates().size() > 10) {
                    ctx.get_fparams().is_underapprox = true;
                    block_curr_len(expr_ref(m.mk_false(), m));
                    this->statistics.at("length").num_finish++;
                    return l_false;
                }
                else {
                    return l_undef;
                }
            }
        }
        // we could not decide if there is solution, continue with other decision procedure
        return l_undef;
    }

    bool theory_str_noodler::is_mult_membership_suitable() {
        // TODO handle length vars (also the ones without any constraints other than lenght ones, for those we just need to compute arith model)
        if (!this->m_conversion_todo.empty() || !this->m_not_contains_todo_rel.empty() || !this->len_vars.empty()) {
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
        STRACE("str", tout << "trying multiple regex membership heuristic" << std::endl;);

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

        dec_proc = std::make_shared<MultMembHeuristicProcedure>(var_to_list_of_regexes_and_complement_flag, alph, m_util_s, m, m_params.m_produce_models);
        this->statistics.at("multi-memb-heur").num_start++;
        lbool result = dec_proc->compute_next_solution();

        if(result != l_undef) this->statistics.at("multi-memb-heur").num_finish++;
        return result;
    }

    lbool theory_str_noodler::run_loop_protection() {
        expr_ref refine = construct_refinement();
        if (refine != nullptr) {
            bool found = false;
            /**
             * Variable denoting that the only stored instance in @p axiomatized_instances was obtained by unsat from initial lengths. In that case
             * if we get SAT from lengths, we do not surely know if it is indeed sat and we need to call the decision procedure again (now it
             * should proceed to the main decision procedure and obtain lengths different from the initial assignment).
             */
            bool init_only = true;
            expr_ref len_formula(this->m);

            for (const auto &pr : this->axiomatized_instances) {
                if (pr.first == refine) {
                    len_formula = pr.second.lengths;
                    init_only = init_only && pr.second.initial_length;
                    found = true;

                    /**
                     * We need to force the SAT solver to find another solution, because adding block_curr_len(len_formula);
                     * is not sufficient for SAT solver to get another solution. We hence find unsat core of
                     * the current assignment with the len_formula and add this unsat core as
                     * a theory lemma.
                     */
                    STRACE("str", tout << "loop-protection: found " << std::endl;);
                    expr_ref unsat_core(m.mk_true(), m);
                    if (check_len_sat(len_formula, &unsat_core) == l_false) {
                        unsat_core = m.mk_not(unsat_core);
                        ctx.internalize(unsat_core.get(), true);
                        add_axiom({mk_literal(unsat_core)});
                        block_curr_len(len_formula, false);
                        STRACE("str", tout << "loop-protection: unsat " << std::endl;);
                        return l_false;
                    }
                }
            }
            if (found && !init_only) {
                /**
                 * If all stored items are SAT and the lengths were obtained from the main decision
                 * procedure --> it is safe to say SAT.
                 */
                STRACE("str", tout << "loop-protection: sat " << std::endl;);
                return l_true;
            }
        }
        return l_undef;
    }

    lbool theory_str_noodler::run_length_sat(const Formula& instance, const AutAssignment& aut_ass,
                                const std::unordered_set<BasicTerm>& init_length_sensitive_vars,
                                std::vector<TermConversion> conversions) {

        dec_proc = std::make_shared<UnaryDecisionProcedure>(instance, aut_ass, m_params);
        expr_ref lengths = len_node_to_z3_formula(dec_proc->get_lengths().first); // it is assumed that lenght formulas from equations were added in new_eq_eh, so we can just have 'true'
        this->statistics.at("unary").num_start++;
        this->statistics.at("unary").num_finish++;
        if(check_len_sat(lengths, nullptr) == l_false) {
            STRACE("str", tout << "Unsat from initial lengths (one symbol)" << std::endl);
            block_curr_len(lengths, true, true);
            return l_false;
        } else {
            sat_handling(lengths);
            return l_true;
        }
    }

    void theory_str_noodler::sat_handling(expr_ref length_formula) {
        last_run_was_sat = true;
        scope_with_last_run_was_sat = m_scope_level;
        if (m_params.m_produce_models) {
            // If we want to produce models, we would like to limit the lengths more significantly,
            // so that Z3 arith solver does not give us some large numbers (for example it can give 60000
            // and returning such a long model can take a long time).
            // We therefore check if we can still get a model if we limit all lengths by some number.
            const int LENGTH_LIMIT = 100; // this seems a small enough number so that model generation is easy, while allowing model to pass trough for most benchmarks
            expr_ref_vector len_constraints(m);
            for (expr* len_var : len_vars) {
                // |len_var| <= LENGTH_LIMIT
                len_constraints.push_back(expr_ref(m_util_a.mk_le(m_util_s.str.mk_length(len_var), m_util_a.mk_int(LENGTH_LIMIT)), m));
            }
            expr_ref length_formula_underapprox(m.mk_and(length_formula, m.mk_and(len_constraints)), m);
            STRACE("str-sat-handling", tout << "Checking if we can put stronger limits on lengths with formula " << mk_pp(length_formula_underapprox, m) << " which is ";);
            if (check_len_sat(length_formula_underapprox) == lbool::l_true) {
                // we can limit the lengths => add it to the resulting length formula
                STRACE("str-sat-handling", tout << "sat\n");
                length_formula = length_formula_underapprox;
            } else {
                STRACE("str-sat-handling", tout << "unsat\n");
            }
        }
        sat_length_formula = length_formula;
        // It seems thare is problem if the length_formula has quantifiers. In that case we skip adding axioms.
        if(!expr_cases::has_quantifier(length_formula, m)) {
            // WARNING: the model generation is not supported for tag automata stuff. 
            // In order to add a support of model generation we need to handle adding axioms in the form of quantified formulae 
            // (so-far the internal solver timeouts with quntified axioms)
            add_axiom(length_formula);
        }
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
}
