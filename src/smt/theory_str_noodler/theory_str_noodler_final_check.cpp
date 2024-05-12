#include <mata/nfa/builder.hh>
#include "smt/theory_str_noodler/theory_str_noodler.h"

namespace smt::noodler {
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

    Formula theory_str_noodler::get_word_formula_from_relevant() {
        Formula instance;

        for (const auto &we: this->m_word_eq_todo_rel) {
            Predicate inst = this->conv_eq_pred(ctx.mk_eq_atom(we.first, we.second));
            instance.add_predicate(inst);
        }

        for (const auto& wd : this->m_word_diseq_todo_rel) {
            Predicate inst = this->conv_eq_pred(m.mk_not(ctx.mk_eq_atom(wd.first, wd.second)));
            instance.add_predicate(inst);
        }

        // construct not contains predicates
        for(const auto& not_contains : this->m_not_contains_todo_rel) {
            std::vector<BasicTerm> left, right;
            util::collect_terms(to_app(not_contains.first), m, this->m_util_s, this->predicate_replace, this->var_name, left);
            util::collect_terms(to_app(not_contains.second), m, this->m_util_s, this->predicate_replace, this->var_name, right);
            Predicate inst(PredicateType::NotContains, std::vector<Concat>{left, right});
            instance.add_predicate(inst);
        }

        return instance;
    }

    std::set<mata::Symbol> theory_str_noodler::get_symbols_from_relevant() {
        // start with symbol representing everything not in formula
        std::set<mata::Symbol> symbols_in_formula{get_dummy_symbol()};

        for (const auto &word_equation: m_word_eq_todo_rel) {
            extract_symbols(word_equation.first, symbols_in_formula);
            extract_symbols(word_equation.second, symbols_in_formula);
        }

        for (const auto &word_disequation: m_word_diseq_todo_rel) {
            extract_symbols(word_disequation.first, symbols_in_formula);
            extract_symbols(word_disequation.second, symbols_in_formula);
        }

        for (const auto &membership: m_membership_todo_rel) {
            extract_symbols(std::get<1>(membership), symbols_in_formula);
        }
        // extract from not contains
        for(const auto& not_contains : m_not_contains_todo_rel) {
            extract_symbols(not_contains.first, symbols_in_formula);
            extract_symbols(not_contains.second, symbols_in_formula);
        }

        return symbols_in_formula;
    }

    AutAssignment theory_str_noodler::create_aut_assignment_for_formula(
            const Formula& instance,
            const std::set<mata::Symbol>& noodler_alphabet
    ) {
        AutAssignment aut_assignment{};
        aut_assignment.set_alphabet(noodler_alphabet);
        regex::Alphabet alph(noodler_alphabet);
        for (const auto &word_equation: m_membership_todo_rel) {
            const expr_ref& var_expr{ std::get<0>(word_equation) };
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
            const bool make_complement{ !std::get<2>(word_equation) };
            mata::nfa::Nfa nfa{ regex::conv_to_nfa(to_app(std::get<1>(word_equation)), m_util_s, m, alph, make_complement, make_complement) };
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
        }

        // create sigma star automaton for our alphabet
        mata::EnumAlphabet mata_alphabet(noodler_alphabet.begin(), noodler_alphabet.end());
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
               single_aut_assignment.second->print_to_DOT(tout);
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
            BasicTerm result(BasicTermType::Variable, to_app(std::get<0>(transf))->get_decl()->get_name().str());
            BasicTerm argument(BasicTermType::Variable, to_app(std::get<1>(transf))->get_decl()->get_name().str());
            ConversionType type = std::get<2>(transf);

            if (type == ConversionType::FROM_CODE || type == ConversionType::FROM_INT) {
                conversions.emplace_back(type, result, argument);
                var_name.insert({result, expr_ref(std::get<0>(transf), m)});
                ass.insert({result, nfa_sigma_star});
            } else {
                conversions.emplace_back(type, argument, result);
                var_name.insert({argument, expr_ref(std::get<1>(transf), m)});
                ass.insert({argument, nfa_sigma_star});
            }
        }
        return conversions;
    }

    bool theory_str_noodler::solve_lang_eqs_diseqs() {
        for(const auto& item : this->m_lang_eq_or_diseq_todo_rel) {
            // RegLan variables should not occur here, they are eliminated by z3 rewriter I think,
            // so both sides of the (dis)equations should be terms representing reg. languages
            expr_ref left_side = std::get<0>(item);
            expr_ref right_side = std::get<1>(item);
            bool is_equation = std::get<2>(item);

            STRACE("str",
                tout << "Checking lang (dis)eq: " << mk_pp(left_side, m) << (is_equation ? " == " : " != ") << mk_pp(right_side, m) << std::endl;
            );

            // get symbols from both sides
            std::set<uint32_t> alphabet;
            extract_symbols(left_side, alphabet);
            extract_symbols(right_side, alphabet);
            regex::Alphabet alph(alphabet);

            // construct NFAs for both sides
            mata::nfa::Nfa nfa1 = regex::conv_to_nfa(to_app(left_side), m_util_s, m, alph, false );
            mata::nfa::Nfa nfa2 = regex::conv_to_nfa(to_app(right_side), m_util_s, m, alph, false );

            // check if NFAs are equivalent (if we have equation) or not (if we have disequation)
            bool are_equiv = mata::nfa::are_equivalent(nfa1, nfa2);
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
        DecisionProcedure dec_proc = DecisionProcedure{ instance, aut_assignment, init_length_sensitive_vars, m_params, conversions };
        if (dec_proc.preprocess(PreprocessType::UNDERAPPROX, this->var_eqs.get_equivalence_bt(aut_assignment)) == l_false) {
            return l_false;
        }

        dec_proc.init_computation();
        while(dec_proc.compute_next_solution() == l_true) {
            expr_ref lengths = len_node_to_z3_formula(dec_proc.get_lengths().first);
            if(check_len_sat(lengths) == l_true) {
                return l_true;
            }
        }
        return l_false;
    }

    lbool theory_str_noodler::check_len_sat(expr_ref len_formula, expr_ref* unsat_core) {
        if (len_formula == m.mk_true()) {
            // we assume here that existing length constraints are satisfiable, so adding true will do nothing
            return l_true;
        }

        int_expr_solver m_int_solver(get_manager(), get_context().get_fparams());
        // do we solve only regular constraints? If yes, skip other temporary length constraints (they are not necessary)
        bool include_ass = true;
        if(this->m_word_diseq_todo_rel.size() == 0 && this->m_word_eq_todo_rel.size() == 0 && this->m_not_contains_todo.size() == 0 && this->m_conversion_todo.size() == 0) {
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

    void theory_str_noodler::extract_symbols(expr* const ex, std::set<uint32_t>& alphabet) {
        if (m_util_s.str.is_string(ex)) {
            auto ex_app{ to_app(ex) };
            SASSERT(ex_app->get_num_parameters() == 1);
            const zstring string_literal{ zstring{ ex_app->get_parameter(0).get_zstring() } };
            for (size_t i{ 0 }; i < string_literal.length(); ++i) {
                alphabet.insert(string_literal[i]);
            }
            return;
        }

        if(util::is_variable(ex)) { // Skip variables.
            return;
        }

        SASSERT(is_app(ex));
        app* ex_app = to_app(ex);

        if (m_util_s.re.is_to_re(ex_app)) { // Handle conversion to regex function call.
            SASSERT(ex_app->get_num_args() == 1);
            const auto arg{ ex_app->get_arg(0) };
            // Assume that expression inside re.to_re() function is a string of characters.
            if (!m_util_s.str.is_string(arg)) { // if to_re has something other than string literal
                util::throw_error("we support only string literals in str.to_re");
            }
            extract_symbols(to_app(arg), alphabet);
            return;
        } else if (m_util_s.re.is_concat(ex_app) // Handle regex concatenation.
                || m_util_s.str.is_concat(ex_app) // Handle string concatenation.
                || m_util_s.re.is_intersection(ex_app) // Handle intersection.
            ) {
            for (unsigned int i = 0; i < ex_app->get_num_args(); ++i) {
                extract_symbols(to_app(ex_app->get_arg(i)), alphabet);
            }
            return;
        } else if (m_util_s.re.is_antimirov_union(ex_app)) { // Handle Antimirov union.
            util::throw_error("antimirov union is unsupported");
        } else if (m_util_s.re.is_complement(ex_app)) { // Handle complement.
            SASSERT(ex_app->get_num_args() == 1);
            const auto child{ ex_app->get_arg(0) };
            SASSERT(is_app(child));
            extract_symbols(to_app(child), alphabet);
            return;
        } else if (m_util_s.re.is_derivative(ex_app)) { // Handle derivative.
            util::throw_error("derivative is unsupported");
        } else if (m_util_s.re.is_diff(ex_app)) { // Handle diff.
            util::throw_error("regex difference is unsupported");
        } else if (m_util_s.re.is_dot_plus(ex_app)) { // Handle dot plus.
            // Handle repeated full char ('.+') (SMT2: (re.+ re.allchar)).
            return;
        } else if (m_util_s.re.is_empty(ex_app)) { // Handle empty language.
            return;
        } else if (m_util_s.re.is_epsilon(ex_app)) { // Handle epsilon.
            return;
        } else if (m_util_s.re.is_full_char(ex_app)) {
            // Handle full char (single occurrence of any string symbol, '.') (SMT2: re.allchar).
            return;
        } else if (m_util_s.re.is_full_seq(ex_app)) {
            // Handle full sequence of characters (any sequence of characters, '.*') (SMT2: re.all).
            return;
        } else if (m_util_s.re.is_of_pred(ex_app)) { // Handle of predicate.
            util::throw_error("of predicate is unsupported");
        } else if (m_util_s.re.is_opt(ex_app) // Handle optional.
                || m_util_s.re.is_plus(ex_app) // Handle positive iteration.
                || m_util_s.re.is_star(ex_app) // Handle star iteration.
                || m_util_s.re.is_loop(ex_app) // Handle loop.
            ) {
            SASSERT(ex_app->get_num_args() == 1);
            const auto child{ ex_app->get_arg(0) };
            SASSERT(is_app(child));
            extract_symbols(to_app(child), alphabet);
            return;
        } else if (m_util_s.re.is_range(ex_app)) { // Handle range.
            SASSERT(ex_app->get_num_args() == 2);
            const auto range_begin{ ex_app->get_arg(0) };
            const auto range_end{ ex_app->get_arg(1) };
            SASSERT(is_app(range_begin));
            SASSERT(is_app(range_end));
            const auto range_begin_value{ to_app(range_begin)->get_parameter(0).get_zstring()[0] };
            const auto range_end_value{ to_app(range_end)->get_parameter(0).get_zstring()[0] };

            auto current_value{ range_begin_value };
            while (current_value <= range_end_value) {
                alphabet.insert(current_value);
                ++current_value;
            }
        } else if (m_util_s.re.is_reverse(ex_app)) { // Handle reverse.
            util::throw_error("reverse is unsupported");
        } else if (m_util_s.re.is_union(ex_app)) { // Handle union (= or; A|B).
            SASSERT(ex_app->get_num_args() == 2);
            const auto left{ ex_app->get_arg(0) };
            const auto right{ ex_app->get_arg(1) };
            SASSERT(is_app(left));
            SASSERT(is_app(right));
            extract_symbols(to_app(left), alphabet);
            extract_symbols(to_app(right), alphabet);
            return;
        } else if(util::is_variable(ex_app)) { // Handle variable.
            util::throw_error("variable should not occur here");
        } else {
            // When ex is not string literal, variable, nor regex, recursively traverse the AST to find symbols.
            // TODO: maybe we can just leave is_range, is_variable and is_string in this function and otherwise do this:
            for(unsigned i = 0; i < ex_app->get_num_args(); i++) {
                SASSERT(is_app(ex_app->get_arg(i)));
                app *arg = to_app(ex_app->get_arg(i));
                extract_symbols(arg, alphabet);
            }
        }
    }

    bool theory_str_noodler::is_nielsen_suitable(const Formula& instance, const std::unordered_set<BasicTerm>& init_length_sensitive_vars) const {
        if(!this->m_membership_todo_rel.empty() || !this->m_not_contains_todo_rel.empty() || !this->m_conversion_todo.empty() || !this->m_word_diseq_todo_rel.empty()) {
            return false;
        }

        if(init_length_sensitive_vars.size() > 0 && !instance.is_quadratic()) {
            return false;
        }

        Graph incl = Graph::create_inclusion_graph(instance);
        return incl.is_cyclic();
    }

    bool theory_str_noodler::is_underapprox_suitable(const Formula& instance, const AutAssignment& aut_ass, const std::vector<TermConversion>& convs) const {
        if(!convs.empty()) {
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
        NielsenDecisionProcedure nproc(instance, aut_assignment, init_length_sensitive_vars, m_params);
        nproc.preprocess();
        expr_ref block_len(m.mk_false(), m);
        nproc.init_computation();
        while (true) {
            lbool result = nproc.compute_next_solution();
            if (result == l_true) {
                expr_ref lengths = len_node_to_z3_formula(nproc.get_lengths().first);
                if (check_len_sat(lengths) == l_true) {
                    return l_true;
                } else {
                    STRACE("str", tout << "nielsen len unsat" <<  mk_pp(lengths, m) << std::endl;);
                    block_len = m.mk_or(block_len, lengths);
                }
            } else if (result == l_false) {
                // we did not find a solution (with satisfiable length constraints)
                // we need to block current assignment
                block_curr_len(block_len);
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
        LengthDecisionProcedure nproc(instance, aut_assignment, init_length_sensitive_vars, m_params);
        expr_ref block_len(m.mk_false(), m);
        if (nproc.preprocess() == l_false) {
            STRACE("str", tout << "len: unsat from preprocessing\n");
            block_curr_len(block_len);
            return l_false;
        }
        nproc.init_computation();
        while (true) {
            lbool result = nproc.compute_next_solution();
            if (result == l_true) {
                expr_ref lengths = len_node_to_z3_formula(nproc.get_lengths().first);
                if (check_len_sat(lengths) == l_true) {
                    return l_true;
                } else {
                    STRACE("str", tout << "len: unsat from lengths:" <<  mk_pp(lengths, m) << std::endl;);
                    if (nproc.precision != LenNodePrecision::UNDERAPPROX) {
                        block_curr_len(lengths);
                        return l_false;
                    } else {
                        return l_undef;
                    }
                }
            } else if (result == l_false) { // never happens
                block_curr_len(block_len);
                return l_false;
            } else {
                // we could not decide if there is solution, continue with other decision procedure
                break;
            }
        }
        return l_undef;
    }

    lbool theory_str_noodler::run_membership_heur() {
        STRACE("str", tout << "Trying heuristic for the case we only have 'x (not)in RE'" << std::endl);
        const auto& reg_data = this->m_membership_todo_rel[0];
        // Heuristic: Get info about the regular expression. If the membership is negated and the regex is not universal for sure --> return FC_DONE.
        // If the membership is in the positive form and the regex is not empty --> regurn FC_DONE.
        regex::RegexInfo regInfo = regex::get_regex_info(to_app(std::get<1>(reg_data)), m_util_s, m);
        if(!std::get<2>(reg_data) && !this->len_vars.contains(std::get<0>(reg_data)) && regInfo.universal == l_false) {
            return l_true;
        }
        if(std::get<2>(reg_data) && !this->len_vars.contains(std::get<0>(reg_data)) && regInfo.empty == l_false) {
            return l_true;
        }
        if(!std::get<2>(reg_data) // membership is negated
            && !this->len_vars.contains(std::get<0>(reg_data)) // x is not length variable
        ) {
            // start with minterm representing symbols not ocurring in the regex
            std::set<mata::Symbol> symbols_in_regex{get_dummy_symbol()};
            extract_symbols(std::get<1>(reg_data), symbols_in_regex);
            regex::Alphabet reg_alph(symbols_in_regex);

            mata::nfa::Nfa nfa{ regex::conv_to_nfa(to_app(std::get<1>(reg_data)), m_util_s, m, reg_alph, false, false) };

            mata::EnumAlphabet alph(symbols_in_regex.begin(), symbols_in_regex.end());
            mata::nfa::Nfa sigma_star = mata::nfa::builder::create_sigma_star_nfa(&alph);

            if(mata::nfa::are_equivalent(nfa, sigma_star)) {
                // x should not belong in sigma*, so it is unsat
                block_curr_len(expr_ref(this->m.mk_false(), this->m));
                STRACE("str", tout << "Membership " << mk_pp(std::get<0>(reg_data), m) << " not in " << mk_pp(std::get<1>(reg_data), m) << " is unsat" << std::endl;);
                return l_false;
            } else {
                // otherwise x should not belong in some nfa that is not sigma*, so it is sat
                return l_true;
            }
        }
        return l_undef;
    }

    bool theory_str_noodler::is_mult_membership_suitable() {
        if (!this->m_conversion_todo.empty() || !this->m_not_contains_todo_rel.empty()) {
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
            BasicTerm var(BasicTermType::Variable, to_app(std::get<0>(membership))->get_decl()->get_name().str());
            app* reg = to_app(std::get<1>(membership));
            var_to_list_of_regexes_and_complement_flag[var].push_back(std::make_pair(!std::get<2>(membership), reg));
        }

        // we assume that is_mult_membership_heur was run before, therefore we have only disequations
        //   x != str_literal
        // i.e., one var on left and some string literal on right, we can replace this with (x not in {str_literal})
        for (const auto& diseq : m_word_diseq_todo_rel) {
            BasicTerm var(BasicTermType::Variable, to_app(diseq.first)->get_decl()->get_name().str());
            app* reg = to_app(diseq.second);
            var_to_list_of_regexes_and_complement_flag[var].push_back(std::make_pair(true, reg));
        }

        // we assume that is_mult_membership_heur was run before, therefore we have only equations
        //   x == str_literal
        // i.e., one var on left and some string literal on right, we can replace this with (x in {str_literal})
        for (const auto& eq : m_word_eq_todo_rel) {
            BasicTerm var(BasicTermType::Variable, to_app(eq.first)->get_decl()->get_name().str());
            app* reg = to_app(eq.second);
            var_to_list_of_regexes_and_complement_flag[var].push_back(std::make_pair(false, reg));
        }

        for (auto& [var, list_of_regexes] : var_to_list_of_regexes_and_complement_flag) {
            // sort the regexes using get_loop_sum, where those regexes that needs to be complemented should all be at the end
            std::sort(list_of_regexes.begin(), list_of_regexes.end(), [this](const std::pair<bool,app*>& l, const std::pair<bool,app*>& r) {
                return ((!l.first && r.first) | (regex::get_loop_sum(l.second, m_util_s) < regex::get_loop_sum(r.second, m_util_s)));
            });
            STRACE("str-mult-memb-heur",
                tout << "Sorted NFAs for var " << var << std::endl;
                unsigned i = 0;
                for (const auto & [is_complement, nfa] : list_of_regexes) {
                    tout << i << " (" << (is_complement ? "" : "not ") <<"complemented):" << std::endl;
                    tout << nfa << std::endl;
                }
            );

            std::shared_ptr<mata::nfa::Nfa> intersection = nullptr; // we save the intersected automata here
            for (auto& [is_complement, reg] : list_of_regexes) {
                STRACE("str", tout << "building intersection for var " << var << " and regex " << mk_pp(reg, m) << (is_complement ? " that needs to be first complemented" : " that does not need to be first complemented") << std::endl;);

                std::shared_ptr<mata::nfa::Nfa> nfa = std::make_shared<mata::nfa::Nfa>(regex::conv_to_nfa(reg, m_util_s, m, alph, is_complement, is_complement));

                if (intersection == nullptr) {
                    intersection = nfa; // this is first nfa
                } else {
                    intersection = std::make_shared<mata::nfa::Nfa>(mata::nfa::reduce(mata::nfa::intersection(*nfa, *intersection)));
                }
                nfa = nullptr;
                
                if (intersection->is_lang_empty()) {
                    STRACE("str", tout << "intersection is empty => UNSAT" << std::endl;);
                    block_curr_len(expr_ref(this->m.mk_false(), this->m));
                    return l_false;
                }
            }
        }

        STRACE("str", tout << "intersection is not empty => SAT" << std::endl;);
        return l_true;
    }
    
    lbool theory_str_noodler::run_length_proc(const Formula& instance, const AutAssignment& aut_assignment, const std::unordered_set<BasicTerm>& init_length_sensitive_vars) {
        STRACE("str", tout << "Trying length-based procedure" << std::endl);
        LengthDecisionProcedure nproc(instance, aut_assignment, init_length_sensitive_vars, m_params);
        nproc.preprocess();
        expr_ref block_len(m.mk_false(), m);
        nproc.init_computation();
        while (true) {
            lbool result = nproc.compute_next_solution();
            if (result == l_true) {
                expr_ref lengths = len_node_to_z3_formula(nproc.get_lengths());
                if (check_len_sat(lengths) == l_true) {
                    return l_true;
                } else {
                    STRACE("str", tout << "length-based procedure len unsat" <<  mk_pp(lengths, m) << std::endl;);
                    block_len = m.mk_or(block_len, lengths);
                }
            } else if (result == l_false) {
                // we did not find a solution (with satisfiable length constraints)
                // we need to block current assignment
                block_curr_len(block_len);
                return l_false;
            } else {
                // we could not decide if there is solution, continue with noodler decision procedure
                break;
            }
        }
        return l_undef;
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

        DecisionProcedure dec_proc = DecisionProcedure{ instance, aut_ass, init_length_sensitive_vars, m_params, conversions };
        expr_ref lengths = len_node_to_z3_formula(dec_proc.get_initial_lengths());
        if(check_len_sat(lengths) == l_false) {
            STRACE("str", tout << "Unsat from initial lengths (one symbol)" << std::endl);
            block_curr_len(lengths, true, true);
            return l_false;
        } else {
            return l_true;
        }
    }
}
