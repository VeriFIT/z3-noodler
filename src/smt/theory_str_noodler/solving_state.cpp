#include "solving_state.h"
#include "formula_preprocess.h"
#include "inclusion_graph.h"

namespace smt::noodler {



    void SolvingState::substitute_vars(const std::set<BasicTerm>& vars_to_substitute) {
        // substitutes variables in a vector using substitution_map
        auto substitute_vector = [this, &vars_to_substitute](const std::vector<BasicTerm> &vector) {
            std::vector<BasicTerm> result;
            for (const BasicTerm &var : vector) {
                if (!vars_to_substitute.contains(var)) {
                    result.push_back(var);
                } else {
                    const auto &to_this = substitution_map.at(var);
                    result.insert(result.end(), to_this.begin(), to_this.end());
                }
            }
            return result;
        };

        // substitutes variables in both sides of inclusion using substitution_map
        auto substitute_predicate = [&substitute_vector](const Predicate &pred) {
            std::vector<std::vector<BasicTerm>> new_params;
            for (const auto& param : pred.get_params()) {
                new_params.push_back(substitute_vector(param));
            }
            if (pred.is_transducer()) return Predicate{pred.get_type(), new_params, pred.get_transducer()};
            else return Predicate{pred.get_type(), new_params};
        };

        // returns true if the inclusion has the same thing on both sides
        auto inclusion_has_same_sides = [](const Predicate &inclusion) { return (inclusion.is_equation() && inclusion.get_left_side() == inclusion.get_right_side()); };

        // substitutes variables of inclusions in a vector using substitute_map, but does not keep the ones that have the same sides after substitution
        auto substitute_set = [&substitute_predicate, &inclusion_has_same_sides](const std::set<Predicate> predicates) {
            std::set<Predicate> new_predicates;
            for (const auto &old_pred : predicates) {
                auto new_pred = substitute_predicate(old_pred);
                if (!inclusion_has_same_sides(new_pred)) { // skip inclusions that have both sides equal
                    new_predicates.insert(new_pred);
                }
            }
            return new_predicates;
        };

        inclusions = substitute_set(inclusions);
        transducers = substitute_set(transducers);
        predicates_not_on_cycle = substitute_set(predicates_not_on_cycle);

        // substituting predicates to process is bit harder, it is possible that two predicates that were supposed to
        // be processed become same after substituting, so we do not want to keep both in predicates to process
        std::set<Predicate> substituted_predicates_to_process;
        std::deque<Predicate> new_predicates_to_process;
        while (!predicates_to_process.empty()) {
            Predicate substituted_inclusion = substitute_predicate(predicates_to_process.front());
            predicates_to_process.pop_front();

            if (!inclusion_has_same_sides(substituted_inclusion)
                && !substituted_predicates_to_process.contains(substituted_inclusion)) { // we do not want to add predicates that are already in predicates_to_process
                new_predicates_to_process.push_back(substituted_inclusion);
            }
        }
        predicates_to_process = new_predicates_to_process;

        for (auto& [subst_var, substitution] : substitution_map) {
            substitution = substitute_vector(substitution);
        }

        apply_substitutions_to_disequations();
    }

    LenNode SolvingState::get_disequations_underapprox_length_formula() const {
        LenNode result{LenFormulaType::AND};
        for(const Predicate& diseq : postponed_disequations.get_predicates()) {
            result.succ.push_back(diseq.get_formula_eq());
        }
        return result;
    }

    std::set<BasicTerm> SolvingState::get_vars_referenced_by_state_constraints() const {
        std::set<BasicTerm> referenced_vars;

        for (const TermConversion& conversion : conversions) {
            referenced_vars.insert(conversion.string_var);
            referenced_vars.insert(conversion.number_var);
        }

        const std::set<BasicTerm> diseq_vars = postponed_disequations.get_vars();
        referenced_vars.insert(diseq_vars.begin(), diseq_vars.end());

        for (const LenNode& conjunct : disequations_len_formula_conjuncts) {
            const std::set<BasicTerm> vars_in_conjunct = collect_free_vars(conjunct);
            referenced_vars.insert(vars_in_conjunct.begin(), vars_in_conjunct.end());
        }

        return referenced_vars;
    }

    void SolvingState::apply_substitutions_to_disequations() {
        auto substitute_concat = [this](const std::vector<BasicTerm>& con) {
            std::vector<BasicTerm> result;
            for (const BasicTerm& bt : con) {
                const std::vector<BasicTerm> subst = get_substituted_vars(bt);
                result.insert(result.end(), subst.begin(), subst.end());
            }
            return result;
        };

        for (Predicate& diseq : postponed_disequations.get_predicates()) {
            SASSERT(diseq.is_inequation());
            diseq = Predicate::create_disequation(
                substitute_concat(diseq.get_left_side()),
                substitute_concat(diseq.get_right_side())
            );
        }
    }

    /**
     * Replace disequality @p diseq L != P by equalities L = x1a1y1 and R = x2a2y2
     * where x1,x2,y1,y2 \in \Sigma* and a1,a2 \in \Sigma \cup {\epsilon} and
     * also create arithmetic formula:
     *   |x1| = |x2| && to_code(a1) != to_code(a2) && (|a1| = 0 => |y1| = 0) && (|a2| = 0 => |y2| = 0)
     * The variables a1/a2 represent the characters on which the two sides differ
     * (they have different code values). They have to occur on the same position,
     * i.e. lengths of x1 and x2 are equal. The situation where one of the a1/a2
     * is empty word (to_code returns -1) represents that one of the sides is
     * longer than the other (they differ on the character just after the last
     * character of the shorter side). We have to force that nothing is after
     * the empty a1/a2, i.e. length of y1/y2 must be 0.
     */
    std::vector<Predicate> SolvingState::replace_disequality(const Predicate& diseq) {
        // automaton accepting empty word or exactly one symbol
        std::shared_ptr<mata::nfa::Nfa> sigma_eps_automaton = std::make_shared<mata::nfa::Nfa>(aut_ass.sigma_eps_automaton());

        // function that will take a1 and a2 and create the "to_code(a1) != to_code(a2)" part of the arithmetic formula
        auto create_to_code_ineq = [this](const BasicTerm& var1, const BasicTerm& var2) {
            // we are going to check that to_code(var1) != to_code(var2), we need exact languages, so we make them length
            length_sensitive_vars.insert(var1);
            length_sensitive_vars.insert(var2);

            // variables that are results of to_code applied to var1/var2
            BasicTerm var1_to_code = util::mk_internal_noodler_var(var1.get_name() + zstring("!ineq_to_code"));
            BasicTerm var2_to_code = util::mk_internal_noodler_var(var2.get_name() + zstring("!ineq_to_code"));

            // add the information that we need to process "var1_to_code = to_code(var1)" and "var2_to_code = to_code(var2)"
            conversions.push_back(TermConversion{ConversionType::TO_CODE, var1, var1_to_code});
            conversions.push_back(TermConversion{ConversionType::TO_CODE, var2, var2_to_code});

            // add to_code(var1) != to_code(var2) to the len formula for disequations
            disequations_len_formula_conjuncts.push_back(LenNode(LenFormulaType::NEQ, {var1_to_code, var2_to_code}));
        };

        // This optimization represents the situation where L = a1 and R = a2
        // and we know that a1,a2 \in \Sigma \cup {\epsilon}, i.e. we do not create new equations.
        if (diseq.get_left_side().size() == 1 && diseq.get_right_side().size() == 1) {
            BasicTerm a1 = diseq.get_left_side()[0];
            BasicTerm a2 = diseq.get_right_side()[0];
            auto autl = aut_ass.at(a1);
            auto autr = aut_ass.at(a2);

            if (mata::nfa::is_included(*autl, *sigma_eps_automaton) && mata::nfa::is_included(*autr, *sigma_eps_automaton)) {
                // create to_code(a1) != to_code(a2)
                create_to_code_ineq(a1, a2);
                STRACE(str_dis, tout << "from disequation " << diseq << " no new equations were created" << std::endl;);
                return std::vector<Predicate>();
            }
        }

        // automaton accepting everything
        std::shared_ptr<mata::nfa::Nfa> sigma_star_automaton = std::make_shared<mata::nfa::Nfa>(aut_ass.sigma_star_automaton());

        BasicTerm x1 = util::mk_noodler_var_fresh("diseq_start");
        aut_ass[x1] = sigma_star_automaton;
        BasicTerm a1 = util::mk_noodler_var_fresh("diseq_char");
        aut_ass[a1] = sigma_eps_automaton;
        BasicTerm y1 = util::mk_noodler_var_fresh("diseq_end");
        aut_ass[y1] = sigma_star_automaton;
        BasicTerm x2 = util::mk_noodler_var_fresh("diseq_start");
        aut_ass[x2] = sigma_star_automaton;
        BasicTerm a2 = util::mk_noodler_var_fresh("diseq_char");
        aut_ass[a2] = sigma_eps_automaton;
        BasicTerm y2 = util::mk_noodler_var_fresh("diseq_end");
        aut_ass[y2] = sigma_star_automaton;

        std::vector<Predicate> new_eqs;
        // L = x1a1y1
        new_eqs.push_back(Predicate::create_equation(diseq.get_left_side(), std::vector<BasicTerm>{x1, a1, y1}));
        // R = x2a2y2
        new_eqs.push_back(Predicate::create_equation(diseq.get_right_side(), std::vector<BasicTerm>{x2, a2, y2}));

        // we want |x1| == |x2|, making x1 and x2 length ones
        length_sensitive_vars.insert(x1);
        length_sensitive_vars.insert(x2);
        // |x1| = |x2|
        disequations_len_formula_conjuncts.push_back(LenNode(LenFormulaType::EQ, {x1, x2}));

        // create to_code(a1) != to_code(a2)
        create_to_code_ineq(a1, a2);

        // we are also going to check for the lengths of y1 and y2, so they have to be length
        length_sensitive_vars.insert(y1);
        length_sensitive_vars.insert(y2);
        // (|a1| = 0) => (|y1| = 0)
        disequations_len_formula_conjuncts.push_back(LenNode(LenFormulaType::OR, {LenNode(LenFormulaType::NEQ, {a1, 0}), LenNode(LenFormulaType::EQ, {y1, 0})}));
        // (|a2| = 0) => (|y2| = 0)
        disequations_len_formula_conjuncts.push_back(LenNode(LenFormulaType::OR, {LenNode(LenFormulaType::NEQ, {a2, 0}), LenNode(LenFormulaType::EQ, {y2, 0})}));

        STRACE(str_dis, tout << "from disequation " << diseq << " created equations: " << new_eqs[0] << " and " << new_eqs[1] << std::endl;);
        return new_eqs;
    }

    void SolvingState::translate_postponed_disequations_to_equations() {
        // we can add equations from replacing disequations as they are. The right side of 
        // each equation contains fresh variables only. Therefore, they cannot depend on 
        // alredy processed equations.
        for (const Predicate& diseq : postponed_disequations.get_predicates()) {
            for (const Predicate& eq_from_diseq : replace_disequality(diseq)) {
                add_predicate(eq_from_diseq, false);
                push_unique(eq_from_diseq, false);
            }
        }

        postponed_disequations.get_predicates().clear();
    }

    lbool SolvingState::preprocess_disequations_for_unsat(const theory_str_noodler_params& params) {
        if (postponed_disequations.get_predicates().empty()) {
            return l_true;
        }

        std::set<BasicTerm> conversion_vars;
        for (const TermConversion& conv : conversions) {
            conversion_vars.insert(conv.string_var);
        }

        FormulaPreprocessor prep_handler{postponed_disequations, aut_ass, length_sensitive_vars, params, conversion_vars};

        prep_handler.remove_trivial();
        prep_handler.reduce_diseqalities();
        prep_handler.propagate_eps();
        prep_handler.refine_languages();
        prep_handler.reduce_diseqalities();

        if (!prep_handler.get_aut_assignment().is_sat() || prep_handler.contains_unsat_eqs_or_diseqs()) {
            return l_false;
        }

        // Persist the simplified disequations and refined state back.
        postponed_disequations = prep_handler.get_modified_formula();
        aut_ass = prep_handler.get_aut_assignment();
        const std::unordered_set<BasicTerm>& prep_len_vars = prep_handler.get_len_variables();
        length_sensitive_vars.insert(prep_len_vars.begin(), prep_len_vars.end());

        return l_true;
    }

    void SolvingState::remove_vars(const std::set<BasicTerm>& vars_to_remove, const std::set<BasicTerm>& vars_to_keep) {
        std::set<BasicTerm> vars_required_by_state = get_vars_referenced_by_state_constraints();

        for (const BasicTerm& var : vars_to_remove) {
            if (vars_to_keep.contains(var)) {
                continue;
            }

            if (vars_required_by_state.contains(var)) {
                // Keep substitution/length information for variables that still occur in
                // state-local constraints (e.g., disequality replacement artifacts),
                // but remove direct automaton assignment to preserve substitution semantics.
                aut_ass.erase(var);
                continue;
            }

            substitution_map.erase(var);
            length_sensitive_vars.erase(var);
            aut_ass.erase(var);
        }
    }

    LenNode SolvingState::get_lengths(const BasicTerm& var) const {
        if (aut_ass.count(var) > 0) {
            // if var is not substituted, get length constraint from its automaton
            return aut_ass.get_lengths(var);
        } else if (substitution_map.count(var) > 0) {
            // if var is substituted, i.e. state.substitution_map[var] = x_1 x_2 ... x_n, then we have to create length equation
            //      |var| = |x_1| + |x_2| + ... + |x_n|
            std::vector<LenNode> plus_operands;
            for (const auto& subst_var : substitution_map.at(var)) {
                plus_operands.emplace_back(subst_var);
            }
            LenNode result(LenFormulaType::EQ, {var, LenNode(LenFormulaType::PLUS, plus_operands)});
            // to be safe, we add |var| >= 0 (for the aut_ass case, it is done in aut_ass.get_lengths)
            return LenNode(LenFormulaType::AND, {result, LenNode(LenFormulaType::LEQ, {0, var})});
        } else {
            util::throw_error("Variable was neither in automata assignment nor was substituted");
            return LenNode(BasicTerm(BasicTermType::Literal)); // return something to get rid of warnings
        }
    }

    void SolvingState::flatten_substition_map() {
        std::unordered_map<BasicTerm, std::vector<BasicTerm>> new_substitution_map;
        std::function<std::vector<BasicTerm>(const BasicTerm&)> flatten_var;

        flatten_var = [&new_substitution_map, &flatten_var, this](const BasicTerm &var) -> std::vector<BasicTerm> {
            if (new_substitution_map.count(var) == 0) {
                std::vector<BasicTerm> flattened_mapping;
                for (const auto &subst_var : this->substitution_map.at(var)) {
                    if (aut_ass.count(subst_var) > 0) {
                        // subst_var is not substituted, keep it
                        flattened_mapping.push_back(subst_var);
                    } else {
                        // subst_var has a substitution, flatten it and insert it to the end of flattened_mapping
                        std::vector<BasicTerm> flattened_mapping_of_subst_var = flatten_var(subst_var);
                        flattened_mapping.insert(flattened_mapping.end(),
                                                 flattened_mapping_of_subst_var.begin(),
                                                 flattened_mapping_of_subst_var.end());
                    }
                }
                new_substitution_map[var] = flattened_mapping;
                return flattened_mapping;
            } else {
                return new_substitution_map[var];
            }
        };

        for (const auto &subst_map_pair : substitution_map) {
            flatten_var(subst_map_pair.first);
        }

        STRACE(str_nfa,
            tout << "Flattened substitution map:" << std::endl;
            for (const auto &var_map : new_substitution_map) {
                tout << "    " << var_map.first.get_name() << " ->";
                for (const auto &subst_var : var_map.second) {
                    tout << " " << subst_var;
                }
                tout << std::endl;
            });

        substitution_map = new_substitution_map;
        apply_substitutions_to_disequations();
    }

    std::pair<std::vector<std::shared_ptr<mata::nfa::Nfa>>,std::vector<std::vector<BasicTerm>>> SolvingState::get_automata_and_division_of_concatenation(const std::vector<BasicTerm>& concatenation, bool group_non_length) {
        if (concatenation.empty()) {
            return std::make_pair<std::vector<std::shared_ptr<mata::nfa::Nfa>>,std::vector<std::vector<BasicTerm>>>({}, {});
        }

        std::vector<std::shared_ptr<mata::nfa::Nfa>> automata_for_concatenation;
        std::vector<std::vector<BasicTerm>> divisions;

        BasicTerm cur_var = concatenation[0];
        // we will build an automaton in prev_aut for the variables in prev_division which are pushed into result when needed
        std::shared_ptr<mata::nfa::Nfa> prev_aut = aut_ass.at(cur_var);
        std::vector<BasicTerm> prev_division{ cur_var };
        bool prev_is_length = length_sensitive_vars.contains(cur_var);

        for (std::vector<BasicTerm>::size_type i = 1; i < concatenation.size(); ++i) {
            cur_var = concatenation[i];
            std::shared_ptr<mata::nfa::Nfa> cur_var_aut = aut_ass.at(cur_var);
            bool cur_is_length = length_sensitive_vars.contains(cur_var);

            if (!group_non_length || prev_is_length || cur_is_length) {
                // we want to push prev_aut and prev_division into result as either we are not grouping automata, or previous var is
                // length, therefore it cannot be grouped, or the current variable is length, therefore, we do not want to group it
                // with the previous automaton
                automata_for_concatenation.push_back(prev_aut);
                divisions.push_back(prev_division);
                STRACE(str_nfa,
                    tout << "Automaton for var(s)";
                    for (const auto &var : prev_division) {
                        tout << " " << var.get_name();
                    }
                    tout << ":" << std::endl
                            << *prev_aut;
                );
                prev_aut = cur_var_aut;
                prev_division = std::vector<BasicTerm>{ cur_var };
            } else {
                // we group the current non-length-aware variable with the non-length-aware vars before
                prev_aut = std::make_shared<mata::nfa::Nfa>(mata::nfa::concatenate(*prev_aut, *cur_var_aut));
                prev_division.push_back(cur_var);
            }

            prev_is_length = cur_is_length;
        }
        // we need to push last automaton into result
        automata_for_concatenation.push_back(prev_aut);
        divisions.push_back(prev_division);
        STRACE(str_nfa,
            tout << "Automaton for var(s)";
            for (const auto &var : prev_division) {
                tout << " " << var.get_name();
            }
            tout << ":" << std::endl << *prev_aut;
        );

        return std::make_pair<std::vector<std::shared_ptr<mata::nfa::Nfa>>,std::vector<std::vector<BasicTerm>>>(std::move(automata_for_concatenation), std::move(divisions));
    }

    std::set<BasicTerm> SolvingState::process_substituting_inclusions_from_right(const std::vector<Predicate>& inclusions, bool on_cycle) {
        std::set<BasicTerm> newly_substituted_vars;
        for (const Predicate& inclusion : inclusions) {
            SASSERT(inclusion.is_equation());
            const std::vector<BasicTerm>& right_side = inclusion.get_right_side();
            if (contains_length_var(right_side)) {
                // right side is exactly one length-aware variable x
                SASSERT(right_side.size() == 1);
                const BasicTerm &right_var = right_side[0];
                SASSERT(right_var.is_variable()); // right_var should not be literal if it is length-aware
                if (!substitution_map.contains(right_var)) {
                    // if we have not substituted right_var yet, we substitute it now with the left side
                    substitution_map[right_var] = inclusion.get_left_side();
                    aut_ass.erase(right_var); // right_var is substituted, we need to remove it from automata assignment
                    newly_substituted_vars.insert(right_var);
                    STRACE(str, tout << "right side var " << right_var.get_name() << " replaced with:"; for (auto const &var : inclusion.get_left_side()) { tout << " " << var.get_name(); } tout << std::endl; );
                } else {
                    // right_var is already substituted, therefore we add the inclusion but with substituted right_var into the solving state
                    Predicate new_inclusion = add_inclusion(inclusion.get_left_side(), substitution_map.at(right_var), on_cycle);
                    // and we also add it into the queue to process (because its right side changed)
                    push_unique(new_inclusion, on_cycle);
                    STRACE(str, tout << "added new inclusion from the right side because it could not be substituted: " << new_inclusion << std::endl; );
                }
            } else {
                // the variables on the right side are non-length, therefore we just add the inclusion into the solving state
                add_predicate(inclusion, on_cycle);
                // because all the variables on the right side are non-length, they were not substituted and therefore we do not need to process
                // the inclusion, as the function assumes that it already holds
                STRACE(str, tout << "added new inclusion from the right side (non-length): " << inclusion << std::endl; );
            }
        }
        // we need to substitute the variables in all other inclusions/transducers
        substitute_vars(newly_substituted_vars);
        // some simple transducers could possibly become non-simple after substitution, we need to readd them for processing
        push_non_simple_transducers_to_processing();
        // note that we do not need to add any inclusions into processing here, as all inclusions that had a variable from newly_substituted_vars
        // on the right side must have been in the queue already, otherwise it would have to be processed and substituted before

        return newly_substituted_vars;
    }


    std::set<BasicTerm> SolvingState::process_substituting_inclusions_from_left(const std::vector<Predicate>& inclusions, bool on_cycle) {
        std::set<BasicTerm> newly_substituted_vars;
        for (const Predicate& inclusion : inclusions) {
            SASSERT(inclusion.is_equation());
            const std::vector<BasicTerm>& left_side = inclusion.get_left_side();
            SASSERT(left_side.size() == 1); // we assume that the inclusion coming to this function have exactly one left var
            const BasicTerm &left_var = left_side[0];
            if (left_var.is_literal()) {
                // we do not want to substitute literals
                continue;
            }
            if (!substitution_map.contains(left_var)) {
                // if we have not substituted left_var yet, we substitute it now with the right side
                substitution_map[left_var] = inclusion.get_right_side();
                aut_ass.erase(left_var); // left_var is substituted, we need to remove it from automata assignment
                newly_substituted_vars.insert(left_var);
                STRACE(str, tout << "left side var " << left_var.get_name() << " replaced with:"; for (auto const &var : inclusion.get_right_side()) { tout << " " << var.get_name(); } tout << std::endl; );
            } else {
                // left_var is already substituted, therefore we add the inclusion but with substituted left_var into the solving state
                Predicate new_inclusion = add_inclusion(substitution_map.at(left_var), inclusion.get_right_side(), on_cycle);
                // and we also add it into the queue to process (because the inclusion might not hold anymore)
                push_unique(new_inclusion, on_cycle);
                STRACE(str, tout << "added new inclusion from the left side because it could not be substituted: " << new_inclusion << std::endl; );
            }
        }
        // before substituting, we need to push all variables that depend on the changed vars for processing
        push_dependent_predicates(newly_substituted_vars, on_cycle);
        // we need to substitute the variables in all other inclusions/transducers
        substitute_vars(newly_substituted_vars);
        // some simple transducers could possibly become non-simple after substitution, we need to readd them for processing
        push_non_simple_transducers_to_processing();

        return newly_substituted_vars;
    }

    BasicTerm SolvingState::add_fresh_var(std::shared_ptr<mata::nfa::Nfa> nfa, std::string var_prefix, bool is_length, bool optimize_literal) {
        if (zstring literal; optimize_literal && AutAssignment::aut_encodes_literal(*nfa, literal)) {
            BasicTerm new_literal{BasicTermType::Literal, literal};
            aut_ass[new_literal] = nfa;
            return new_literal;
        } else {
            BasicTerm new_var = util::mk_noodler_var_fresh(var_prefix);
            aut_ass[new_var] = nfa;
            if (is_length) { length_sensitive_vars.insert(new_var); }
            return new_var;
        }
    }

    void SolvingState::replace_dummy_symbol_in_transducers_with(std::set<mata::Symbol> replacements) {
        if (replacements.empty()) { return; }
        for (const Predicate& trans : transducers) {
            util::replace_dummy_symbol_in_transducer_with(*trans.get_transducer(), replacements);
        }
    }

    std::string SolvingState::print_to_DOT() const {
        auto escape_DOT_string = [](std::string string_to_escape) {
            std::ostringstream res;
            for (char c : string_to_escape) {
                if (c == '\\' || c == '{' || c == '}' || c == '<' || c == '>' || c == '|' || c == '\"' || c == ' ') {
                    res << '\\' << c;
                } else {
                    res << c;
                }
            }
            return res.str();
        };

        auto print_predicate_to_DOT = [this,&escape_DOT_string](const Predicate& pred) {
            std::ostringstream res;
            if (pred.is_equation()) { // inclusion
                res << escape_DOT_string(to_string(pred.get_left_side())) << "\\ ⊆\\ " << escape_DOT_string(to_string(pred.get_right_side()));
            } else { //transducer
                SASSERT(pred.is_transducer());
                res << escape_DOT_string(to_string(pred.get_output())) << "\\ =\\ T" << pred.get_transducer().get() << "(" << escape_DOT_string(to_string(pred.get_input())) << ")";
            }
            if (is_predicate_on_cycle(pred)) {
                res << "\\ :\\ oncycle";
            }
            return res.str();
        };
        
        auto print_strings = [](std::vector<std::string>& strings, bool order, std::string del = "\\n") {
            if (order) {
                std::sort(strings.begin(), strings.end());
            }
            bool first = true;
            std::ostringstream res;
            for (const std::string& string : strings) {
                if (first) {
                    first = false;
                    res << string;
                } else {
                    res << del << string;
                }
            }
            return res.str(); 
        };

        auto print_predicate_container_to_DOT = [&print_predicate_to_DOT, &print_strings]<typename T>(const T& predicate_container, bool order) {
            std::vector<std::string> predicate_strings(predicate_container.size());
            std::transform(predicate_container.begin(), predicate_container.end(), predicate_strings.begin(), print_predicate_to_DOT);
            return print_strings(predicate_strings, order);
        };


        auto print_vars_to_DOT = [&escape_DOT_string, &print_strings]<typename T>(const T& vars, bool order, bool delimit_by_space) {
            std::vector<std::string> var_names(vars.size());
            std::transform(vars.begin(), vars.end(), var_names.begin(), [&escape_DOT_string](const BasicTerm& var) { return escape_DOT_string(var.to_string());});
            return print_strings(var_names, order, (delimit_by_space ? "\\ " : "\\n"));
        };

        std::ostringstream res;
        res << DOT_name << "[shape=record,label=\"" << print_predicate_container_to_DOT(inclusions, true);
        if (!inclusions.empty() && !transducers.empty()) {
            res << "\\n";
        }
        res << print_predicate_container_to_DOT(transducers, true) << "|" << print_predicate_container_to_DOT(predicates_to_process, false) << "|";

        std::vector<std::string> strings_to_print;
        for (const auto& [var,subst_vars] : substitution_map) {
            strings_to_print.push_back(escape_DOT_string(var.to_string()) + std::string("\\ -\\>\\ ") + print_vars_to_DOT(subst_vars, false, true));
        }
        for (const BasicTerm& var : aut_ass.get_keys()) {
            if (!var.is_literal()) { 
                strings_to_print.push_back(escape_DOT_string(var.to_string()) + std::string("\\ -\\>\\ NFA"));
            }
        }
        res << print_strings(strings_to_print, true);

        res << "|";

        res << print_vars_to_DOT(length_sensitive_vars, true, false);

        res << "\"];";
        return res.str();
    }

}