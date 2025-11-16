#include "solving_state.h"

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
    }

    void SolvingState::remove_vars(const std::set<BasicTerm>& vars_to_remove, const std::set<BasicTerm>& vars_to_keep) {
        for (const BasicTerm& var : vars_to_remove) {
            if (!vars_to_keep.contains(var)) {
                substitution_map.erase(var);
                length_sensitive_vars.erase(var);
                aut_ass.erase(var);
            }
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
        std::map<BasicTerm, std::vector<BasicTerm>> new_substitution_map;
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
        zstring literal;
        if (optimize_literal && AutAssignment::aut_encodes_literal(*nfa, literal)) {
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