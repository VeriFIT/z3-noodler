#include <queue>
#include <utility>
#include <algorithm>
#include <functional>

#include <mata/nfa/strings.hh>
#include "util.h"
#include "aut_assignment.h"
#include "decision_procedure.h"
#include "regex.h"

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

        STRACE("str-nfa",
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
                STRACE("str-nfa",
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
        STRACE("str-nfa",
            tout << "Automaton for var(s)";
            for (const auto &var : prev_division) {
                tout << " " << var.get_name();
            }
            tout << ":" << std::endl << *prev_aut;
        );

        return std::make_pair<std::vector<std::shared_ptr<mata::nfa::Nfa>>,std::vector<std::vector<BasicTerm>>>(std::move(automata_for_concatenation), std::move(divisions));
    }

    void SolvingState::process_substituting_inclusions_from_right(const std::vector<Predicate>& inclusions, bool on_cycle) {
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
                    STRACE("str", tout << "right side var " << right_var.get_name() << " replaced with:"; for (auto const &var : inclusion.get_left_side()) { tout << " " << var.get_name(); } tout << std::endl; );
                } else {
                    // right_var is already substituted, therefore we add the inclusion but with substituted right_var into the solving state
                    Predicate new_inclusion = add_inclusion(inclusion.get_left_side(), substitution_map.at(right_var), on_cycle);
                    // and we also add it into the queue to process (because its right side changed)
                    push_unique(new_inclusion, on_cycle);
                    STRACE("str", tout << "added new inclusion from the right side because it could not be substituted: " << new_inclusion << std::endl; );
                }
            } else {
                // the variables on the right side are non-length, therefore we just add the inclusion into the solving state
                add_predicate(inclusion, on_cycle);
                // because all the variables on the right side are non-length, they were not substituted and therefore we do not need to process
                // the inclusion, as the function assumes that it already holds
                STRACE("str", tout << "added new inclusion from the right side (non-length): " << inclusion << std::endl; );
            }
        }
        // we need to substitute the variables in all other inclusions/transducers
        substitute_vars(newly_substituted_vars);
        // some simple transducers could possibly become non-simple after substitution, we need to readd them for processing
        push_non_simple_transducers_to_processing();
        // note that we do not need to add any inclusions into processing here, as all inclusions that had a variable from newly_substituted_vars
        // on the right side must have been in the queue already, otherwise it would have to be processed and substituted before
    }


    void SolvingState::process_substituting_inclusions_from_left(const std::vector<Predicate>& inclusions, bool on_cycle) {
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
                STRACE("str", tout << "left side var " << left_var.get_name() << " replaced with:"; for (auto const &var : inclusion.get_right_side()) { tout << " " << var.get_name(); } tout << std::endl; );
            } else {
                // left_var is already substituted, therefore we add the inclusion but with substituted left_var into the solving state
                Predicate new_inclusion = add_inclusion(substitution_map.at(left_var), inclusion.get_right_side(), on_cycle);
                // and we also add it into the queue to process (because the inclusion might not hold anymore)
                push_unique(new_inclusion, on_cycle);
                STRACE("str", tout << "added new inclusion from the left side because it could not be substituted: " << new_inclusion << std::endl; );
            }
        }
        // before substituting, we need to push all variables that depend on the changed vars for processing
        push_dependent_predicates(newly_substituted_vars, on_cycle);
        // we need to substitute the variables in all other inclusions/transducers
        substitute_vars(newly_substituted_vars);
        // some simple transducers could possibly become non-simple after substitution, we need to readd them for processing
        push_non_simple_transducers_to_processing();
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
            auto trans_ptr = trans.get_transducer();
            for (mata::nfa::State state = 0; state < trans_ptr->num_of_states(); ++state) {
                if (!trans_ptr->delta[state].empty()) { // if there is some transition from state
                    mata::nfa::StatePost& delta_from_state = trans_ptr->delta.mutable_state_post(state); // then we can for sure get mutable transitions from state without side effect
                    for (auto iter = delta_from_state.begin(); iter != delta_from_state.end(); ++iter) {
                        if (iter->symbol == util::get_dummy_symbol()) {
                            mata::nfa::StateSet targets = iter->targets;
                            delta_from_state.erase(iter);
                            for (mata::Symbol replacement : replacements) {
                                trans_ptr->delta.add(state, replacement, targets); // this invalidates iter, but we are breaking from the loop anyway
                            }
                            break;
                        }
                    }
                }
            }
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

        auto print_predicate_container_to_DOT = [&print_predicate_to_DOT]<typename T>(T predicate_container) {
            bool first = true;
            std::ostringstream res;
            for (const Predicate& pred : predicate_container) {
                if (first) {
                    first = false;
                    res << print_predicate_to_DOT(pred);
                } else {
                    res << "\\n" << print_predicate_to_DOT(pred);
                }
            }
            return res.str(); 
        };


        auto print_vars_to_DOT = [&escape_DOT_string](const std::vector<BasicTerm>& vars) {
            bool first = true;
            std::ostringstream res;
            for (const BasicTerm& var : vars) {
                if (first) {
                    first = false;
                    res << escape_DOT_string(var.to_string());
                } else {
                    res << "\\n" << escape_DOT_string(var.to_string());
                }
            }
            return res.str(); 
        };

        std::ostringstream res;
        res << DOT_name << "[shape=record,label=\"" << print_predicate_container_to_DOT(inclusions);
        if (!inclusions.empty() && !transducers.empty()) {
            res << "\\n";
        }
        res << print_predicate_container_to_DOT(transducers) << "|" << print_predicate_container_to_DOT(predicates_to_process) << "|";

        bool first = true;
        for (const auto& [var,subst_vars] : substitution_map) {
            if (first) {
                first = false;
                res << escape_DOT_string(var.to_string()) << "\\ -\\>\\ " << print_vars_to_DOT(subst_vars);
            } else {
                res << "\\n" << escape_DOT_string(var.to_string()) << "\\ -\\>\\ " << print_vars_to_DOT(subst_vars);
            }
        }
        for (const BasicTerm& var : aut_ass.get_keys()) {
            if (var.is_literal()) { continue; }
            if (first) {
                first = false;
                res << escape_DOT_string(var.to_string()) << "\\ -\\>\\ NFA";
            } else {
                res << "\\n" << escape_DOT_string(var.to_string()) << "\\ -\\>\\ NFA";
            }
        }

        res << "|";

        first = true;
        for (const BasicTerm& var : length_sensitive_vars) {
            if (first) {
                first = false;
                res << escape_DOT_string(var.to_string());
            } else {
                res << "\\n" << escape_DOT_string(var.to_string());
            }
        }
        res << "\"];";
        return res.str();
    }

    lbool DecisionProcedure::compute_next_solution() {
        // iteratively select next state of solving that can lead to solution and
        // process one of the unprocessed nodes (or possibly find solution)
        STRACE("str", tout << "------------------------"
                           << "Getting another solution"
                           << "------------------------" << std::endl;);

        while (!worklist.empty()) {
            SolvingState element_to_process = pop_from_worklist();

            if (element_to_process.predicates_to_process.empty()) {
                // we found another solution, element_to_process contain the automata
                // assignment and variable substition that satisfy the original
                // inclusion graph
                solution = std::move(element_to_process);
                STRACE("str",
                    tout << "Found solution:" << std::endl;
                    for (const auto &var_substitution : solution.substitution_map) {
                        tout << "    " << var_substitution.first << " ->";
                        for (const auto& subst_var : var_substitution.second) {
                            tout << " " << subst_var;
                        }
                        tout << std::endl;
                    }
                    for (const auto& var_aut : solution.aut_ass) {
                        tout << "    " << var_aut.first << " -> NFA" << std::endl;
                        if (is_trace_enabled("str-nfa")) {
                            var_aut.second->print_to_mata(tout);
                        }
                    }
                    for (const auto& transd : solution.transducers) {
                        tout << transd << "\n";
                    }
                );
                STRACE("str-noodle-dot", tout << solution.DOT_name << " [style=filled,fillcolor=\"aqua\"];\n";);
                return l_true;
            }

            // we will now process one inclusion from the inclusion graph which is at front
            // i.e. we will update automata assignments and substitutions so that this inclusion is fulfilled
            Predicate predicate_to_process = element_to_process.predicates_to_process.front();
            element_to_process.predicates_to_process.pop_front();

            if (predicate_to_process.is_equation()) { // inclusion
                process_inclusion(predicate_to_process, element_to_process);
            } else {
                SASSERT(predicate_to_process.is_transducer());
                process_transducer(predicate_to_process, element_to_process);
            }
        }

        // there are no solving states left, which means nothing led to solution -> it must be unsatisfiable
        STRACE("str-noodle-dot", tout << "}\n";);
        return l_false;
    }

    void DecisionProcedure::process_inclusion(const Predicate& inclusion_to_process, SolvingState& solving_state) {
        // this will decide whether we will continue in our search by DFS or by BFS
        bool is_inclusion_to_process_on_cycle = solving_state.is_predicate_on_cycle(inclusion_to_process);

        STRACE("str", tout << "Processing node with inclusion " << inclusion_to_process << " which is" << (is_inclusion_to_process_on_cycle ? " " : " not ") << "on the cycle" << std::endl;);
        STRACE("str",
            tout << "Length variables are:";
            for(auto const &var : inclusion_to_process.get_vars()) {
                if (solving_state.length_sensitive_vars.count(var)) {
                    tout << " " << var.to_string();
                }
            }
            tout << std::endl;
        );

        const auto &left_side_vars = inclusion_to_process.get_left_side();
        const auto &right_side_vars = inclusion_to_process.get_right_side();

        /********************************************************************************************************/
        /****************************************** One side is empty *******************************************/
        /********************************************************************************************************/
        // As kinda optimization step, we do "noodlification" for empty sides separately (i.e. sides that
        // represent empty string). This is because it is simpler, we would get only one noodle so we just need to
        // check that the non-empty side actually contains empty string and replace the vars on that side by epsilon.
        if (right_side_vars.empty() || left_side_vars.empty()) {
            auto const non_empty_side_vars = right_side_vars.empty() ?
                                                    inclusion_to_process.get_left_set()
                                                    : inclusion_to_process.get_right_set();
            bool non_empty_side_contains_empty_word = true;
            for (const auto &var : non_empty_side_vars) {
                if (solving_state.aut_ass.contains_epsilon(var)) {
                    solving_state.substitution_map[var] = {};
                    solving_state.aut_ass.erase(var);
                } else {
                    // var does not contain empty word => whole non-empty side cannot contain empty word
                    non_empty_side_contains_empty_word = false;
                    break;
                }
            }
            if (!non_empty_side_contains_empty_word) {
                // in the case that the non_empty side does not contain empty word
                // the inclusion cannot hold (noodlification would not create anything)
                return;
            }

            solving_state.remove_predicate(inclusion_to_process); // we processed the inclusion
            if (right_side_vars.empty()) {
                // if we are updating vars on the left side, we need to add dependent predicates for processing
                solving_state.push_dependent_predicates(non_empty_side_vars, is_inclusion_to_process_on_cycle);
            }
            solving_state.substitute_vars(non_empty_side_vars); // we need to substitute the variables in other predicates
            // it is possible that some transducer become non-simple (one of its side becomes empty), we want to process these again
            solving_state.push_non_simple_transducers_to_processing();

            // we push to front when the inclusion is not on cycle, because we want to get to the result as fast as possible
            // and if there is no cycle, we do not need to do BFS, the algorithm should end
            push_to_worklist(std::move(solving_state), is_inclusion_to_process_on_cycle);

            return;
        }
        /********************************************************************************************************/
        /*************************************** End of one side is empty ***************************************/
        /********************************************************************************************************/



        // Get automata of the variables on the left side
        STRACE("str-nfa", tout << "Left automata:" << std::endl);
        auto [left_side_automata, left_side_division] = solving_state.get_automata_and_division_of_concatenation(left_side_vars, false);
        SASSERT(left_side_division.size() == left_side_vars.size()); // each division should contain exactly one left variable
        SASSERT(left_side_automata.size() == left_side_division.size()); // we have one automaton for each division

        // Get automata of the variables on the right side, but we can group non-length-aware vars next to each other
        // together. Each right side automaton corresponds to either concatenation of non-length-aware vars (vector of
        // basic terms) or one lenght-aware var (vector of one basic term). Division then contains for each right
        // side automaton the variables whose concatenation it represents.
        STRACE("str-nfa", tout << "Right automata:" << std::endl);
        auto [right_side_automata, right_side_division] = solving_state.get_automata_and_division_of_concatenation(right_side_vars, true);
        SASSERT(right_side_automata.size() == right_side_division.size()); // we have one automaton for each division


        /********************************************************************************************************/
        /****************************************** Inclusion test **********************************************/
        /********************************************************************************************************/
        if (!solving_state.contains_length_var(right_side_vars)) {
            // we have no length-aware variables on the right hand side => we do not need to do noodlification but can directly check if inclusion holds
            SASSERT(right_side_automata.size() == 1); // there should be exactly one element in right_side_automata as we do not have length variables
            // TODO probably we should try shortest words, it might work correctly (see https://github.com/VeriFIT/z3-noodler/pull/201)
            if (is_inclusion_to_process_on_cycle // we do not test inclusion if we have node that is not on cycle, because we will not go back to it (TODO: should we really not test it?)
                && mata::nfa::is_included(solving_state.aut_ass.get_automaton_concat(left_side_vars), *right_side_automata[0])) {
                // the inclusion holds, therefore we do not need to do noodlification and we can continue with this
                // solving_state (we push to front and not back because we can just directly continue with next inclusion
                // and we can possibly get to the result on the next step)
                push_to_worklist(std::move(solving_state), false);
                return;
            }
        }
        /********************************************************************************************************/
        /*************************************** End of inclusion test ******************************************/
        /********************************************************************************************************/

        // we are processing this inclusion as it does not hold, so we need to replace it with new inclusions/substitutions -> we remove it first
        solving_state.remove_predicate(inclusion_to_process);


        /* TODO check here if we have empty elements_to_process, if we do, then every noodle we get should finish and return sat
         * right now if we test sat at the beginning it should work, but it is probably better to immediatly return sat if we have
         * empty elements_to_process, however, we need to remmeber the state of the algorithm, we would need to return back to noodles
         * and process them if z3 realizes that the result is actually not sat (because of lengths)
         */



        /********************************************************************************************************/
        /******************************************* Noodlification *********************************************/
        /********************************************************************************************************/
        /**
         * We get noodles where each noodle consists of automata connected with a vector of numbers.
         * So for example if we have some noodle and automaton noodle[i].first, then noodle[i].second is a vector,
         * where first element i_l = noodle[i].second[0] tells us that automaton noodle[i].first belongs to the
         * i_l-th left var (i.e. left_side_vars[i_l]) and the second element i_r = noodle[i].second[1] tell us that
         * it belongs to the i_r-th division of the right side (i.e. right_side_division[i_r])
         **/
        auto noodles = mata::strings::seg_nfa::noodlify_for_equation(left_side_automata,
                                                                    right_side_automata,
                                                                    false,
                                                                    {{"reduce", "forward"}});

        for (const auto &noodle : noodles) {
            STRACE("str", tout << "Processing noodle" << (is_trace_enabled("str-nfa") ? " with automata:" : "") << std::endl;);
            SolvingState new_element = solving_state;

            /* Explanation of the next code on an example:
             * Left side has variables x_1, x_2, x_3, x_2 while the right side has variables x_4, x_1, x_5, x_6, where x_1
             * and x_4 are length-aware (i.e. there is one automaton for concatenation of x_5 and x_6 on the right side).
             * Assume that noodle represents the case where it was split like this:
             *              | x_1 |    x_2    | x_3 |       x_2       |
             *              | t_1 | t_2 | t_3 | t_4 | t_5 |    t_6    |
             *              |    x_4    |       x_1       | x_5 | x_6 |
             * In the following for loop, we create the vars t1, t2, ..., t6 and prepare two vectors left_side_vars_to_new_vars
             * and right_side_divisions_to_new_vars which map left vars and right divisions into the concatenation of the new
             * vars. So for example left_side_vars_to_new_vars[1] = t_2 t_3, because second left var is x_2 and we map it to t_2 t_3,
             * while right_side_divisions_to_new_vars[2] = t_6, because the third division on the right represents the automaton for
             * concatenation of x_5 and x_6 and we map it to t_6.
             */
            std::vector<std::vector<BasicTerm>> left_side_vars_to_new_vars(left_side_vars.size());
            std::vector<std::vector<BasicTerm>> right_side_divisions_to_new_vars(right_side_division.size());
            for (unsigned i = 0; i < noodle.size(); ++i) {
                // we add a fresh var for each segment of noodle (TODO: do not make new var if we can replace it from one side by one var)
                BasicTerm new_var = new_element.add_fresh_var(
                                                        noodle[i].first, // we assign to it the automaton from the segment
                                                        std::string("align_") + std::to_string(noodlification_no), // the prefix of the new var
                                                        // the var is length if the corresponding variable on the left or right is length too
                                                        new_element.length_sensitive_vars.contains(left_side_vars[noodle[i].second[0]])
                                                            || new_element.contains_length_var(right_side_division[noodle[i].second[1]]),
                                                        // we want to create literal if possible, the automaton should be trimmed and reduced from noodlification
                                                        true);
                left_side_vars_to_new_vars[noodle[i].second[0]].push_back(new_var);
                right_side_divisions_to_new_vars[noodle[i].second[1]].push_back(new_var);
                STRACE("str-nfa", tout << new_var << std::endl << *noodle[i].first;);
            }

            /* Following the example from before, the following will create these inclusions from the right side divisions:
             *         t_1 t_2 ⊆ x_4
             *     t_3 t_4 t_5 ⊆ x_1
             *             t_6 ⊆ x_5 x_6
             */
            std::vector<Predicate> right_side_inclusions = util::create_inclusions_from_multiple_sides(right_side_divisions_to_new_vars, right_side_division);
            /*
             * However, we do not add the first two inclusions into the inclusion graph but use them for substitution, i.e.
             *        substitution_map[x_4] = t_1 t_2
             *        substitution_map[x_1] = t_3 t_4 t_5
             * because they are length-aware vars and we only add the inclusion t_6 ⊆ x_5 x_6.
             * The following function does this and it also add new inclusions/transducers to processing if needed.
             */
            new_element.process_substituting_inclusions_from_right(right_side_inclusions, is_inclusion_to_process_on_cycle);

            /* Following the example from before, the following will create these inclusions from the left side:
             *           x_1 ⊆ t_1
             *           x_2 ⊆ t_2 t_3
             *           x_3 ⊆ t_4
             *           x_2 ⊆ t_5 t_6
             */
             std::vector<Predicate> left_side_inclusions = util::create_inclusions_from_multiple_sides(left_side_division, left_side_vars_to_new_vars);
             /* Again, we want to use the inclusions for substitutions, but we replace only those variables which were
             * not substituted yet, so the first inclusion stays (x_1 was substituted from the right side) and the
             * fourth inclusion stays (as we substitute x_2 using the second inclusion). So from the second and third
             * inclusion we get:
             *        substitution_map[x_2] = t_2 t_3
             *        substitution_map[x_3] = t_4
             * and we only add inclusions x_1 ⊆ t_1 and t_2 t_3 ⊆ t_5 t_6.
             * The following function does this and it also add new inclusions/transducers to processing if needed.
             */
            new_element.process_substituting_inclusions_from_left(left_side_inclusions, is_inclusion_to_process_on_cycle);

            // we push to front when the inclusion is not on cycle, because we want to get to the result as fast as possible
            // and if there is no cycle, we do not need to do BFS, the algorithm should end
            push_to_worklist(std::move(new_element), is_inclusion_to_process_on_cycle);
        }

        ++noodlification_no; // TODO: when to do this increment?? maybe noodlification_no should be part of SolvingState?
        /********************************************************************************************************/
        /*************************************** End of noodlification ******************************************/
        /********************************************************************************************************/

    }

    void DecisionProcedure::process_transducer(const Predicate& transducer_to_process, SolvingState& solving_state) {
        // We assume that if we have transducers in procedure, then the inclusion tree is without cycles
        SASSERT(!solving_state.is_predicate_on_cycle(transducer_to_process));

        STRACE("str", tout << "Processing node with transducer " << transducer_to_process << std::endl;);
        STRACE("str-nfa", tout << *transducer_to_process.get_transducer(););
        STRACE("str",
            tout << "Length variables are:";
            for(auto const &var : transducer_to_process.get_vars()) {
                if (solving_state.length_sensitive_vars.count(var)) {
                    tout << " " << var.to_string();
                }
            }
            tout << std::endl;
        );

        solving_state.remove_predicate(transducer_to_process);

        const std::vector<BasicTerm>& input_vars = transducer_to_process.get_input();
        const std::vector<BasicTerm>& output_vars = transducer_to_process.get_output();

        if (input_vars.empty() || output_vars.empty()) {
            // If one side is empty, we can apply empty string on the tape connected with the empty side and replace the transducer with inclusion.
            // For example, if we have
            //     output_vars = T("")          or             "" = T(input_vars)
            // we replace it with
            //     output_vars ⊆ fresh_var      or      fresh_var ⊆ input_vars
            // where the language of the fresh_var is the application of empty string on T (either on input or output, based on which side is empty).

            bool input_is_empty = input_vars.empty();
            mata::nft::Level level_of_empty_side = input_is_empty ? 0 : 1;

            // we apply empty string to empty tape of transducer, getting the NFA for the nonempty side
            mata::nfa::Nfa application_to_empty_string = transducer_to_process.get_transducer()->apply(mata::Word(), level_of_empty_side).to_nfa_move();
            application_to_empty_string = mata::nfa::reduce(mata::nfa::remove_epsilon(application_to_empty_string.trim()));
            
            if (application_to_empty_string.is_lang_empty()) {
                // empty string is not accepted by transducer as input, this solving_state cannot lead to solution
                return;
            }

            const std::vector<BasicTerm>& non_empty_side = input_is_empty ? output_vars : input_vars;

            if (non_empty_side.empty()) {
                // if the non-empty side is actually also empty, then we can just check if the result of application contains epsilon
                if (application_to_empty_string.is_in_lang({})) {
                    // if it does, we can continue with this solving_state, otherwise we keep it out of worklist as it will not lead to solution
                    push_to_worklist(std::move(solving_state), false);
                }
                return;
            }

            // we create new inclusion, either output_var ⊆ application_to_empty_string or application_to_empty_string ⊆ input_vars
            Predicate new_inclusion = input_is_empty ? Predicate::create_equation(non_empty_side, {}) : Predicate::create_equation({}, non_empty_side);
            if (!mata::strings::is_lang_eps(application_to_empty_string)) {
                // if the application does not lead to empty string we need to create a new var for empty side and replace it with its language set to application_to_empty_string
                BasicTerm fresh_var = util::mk_noodler_var_fresh(std::string("emptysideapp_") + std::to_string(noodlification_no));
                solving_state.aut_ass[fresh_var] = std::make_shared<mata::nfa::Nfa>(application_to_empty_string);
                if (input_is_empty) {
                    new_inclusion.set_right_side({fresh_var});
                } else {
                    new_inclusion.set_left_side({fresh_var});
                }
            }
            solving_state.add_predicate(new_inclusion, false);
            solving_state.push_front_unique(new_inclusion);
            push_to_worklist(std::move(solving_state), false);
            return;
        }

        STRACE("str-nfa", tout << "Input automata:" << std::endl);
        auto [input_vars_automata, input_vars_divisions] = solving_state.get_automata_and_division_of_concatenation(input_vars, true);
        SASSERT(input_vars_automata.size() == input_vars_divisions.size());

        STRACE("str-nfa", tout << "Output automata:" << std::endl);
        auto [output_vars_automata, output_vars_divisions] = solving_state.get_automata_and_division_of_concatenation(output_vars, false);
        SASSERT(output_vars_automata.size() == output_vars_divisions.size());
        SASSERT(output_vars_divisions.size() == output_vars.size());

        std::vector<mata::strings::seg_nfa::TransducerNoodle> noodles = mata::strings::seg_nfa::noodlify_for_transducer(transducer_to_process.get_transducer(), input_vars_automata, output_vars_automata, true);
        for (const auto& noodle : noodles) {
            // each noodle is a vector of tuples (T,i,Ai,o,Ao) where
            //      - T is a transducer, which will take one input and one output var: xo = T(xi)
            //      - i is the number denoting which input variable is connected with T
            //      - Ai is NFA for the new input variable xi
            //      - o is the number denoting which output variable is connected with T
            //      - Ao is NFA for the new output variable xo

            // we are doing similar things as in processing of inclusion, just with two types of vars (input/output) instead of one
            // and the result is also a set of simple transducers 
            STRACE("str", tout << "Processing noodle" << std::endl;);

            SolvingState new_element = solving_state;

            std::vector<std::vector<BasicTerm>> input_vars_to_new_input_vars(input_vars_divisions.size());
            std::vector<std::vector<BasicTerm>> output_vars_to_new_output_vars(output_vars.size());
            for (unsigned i = 0; i < noodle.size(); ++i) {
                // TODO do not make new vars if we can replace them with one var

                BasicTerm new_input_var = new_element.add_fresh_var(
                                                            noodle[i].input_aut, // we assign Ai to new_input_var
                                                            std::string("input_") + std::to_string(noodlification_no),
                                                            new_element.contains_length_var(input_vars_divisions[noodle[i].input_index]),
                                                            true
                                                        ); // xi
                input_vars_to_new_input_vars[noodle[i].input_index].push_back(new_input_var);

                BasicTerm new_output_var = new_element.add_fresh_var(
                                                            noodle[i].output_aut, // we assign Ao to new_output_var
                                                            std::string("output_") + std::to_string(noodlification_no),
                                                            // lengthness must be propagated from input to output too
                                                            new_element.contains_length_var(input_vars_divisions[noodle[i].input_index])
                                                                || new_element.length_sensitive_vars.contains(output_vars[noodle[i].output_index]),
                                                            true
                                                        ); // xo
                output_vars_to_new_output_vars[noodle[i].output_index].push_back(new_output_var);

                // add the new transducer xo = T(xi)
                Predicate new_trans = new_element.add_transducer(noodle[i].transducer, {new_input_var}, {new_output_var}, false);
                STRACE("str",
                    tout << "New transducer: " << new_trans << std::endl;
                    if (is_trace_enabled("str-nfa")) {
                        tout << new_input_var << ":\n" << *noodle[i].input_aut
                             << new_output_var << ":\n" << *noodle[i].output_aut
                             << "transducer:\n" << *new_trans.get_transducer();
                    }
                );
            }

            std::vector<Predicate> input_inclusions = util::create_inclusions_from_multiple_sides(input_vars_to_new_input_vars, input_vars_divisions);
            new_element.process_substituting_inclusions_from_right(input_inclusions, false);

            std::vector<Predicate> output_inclusions = util::create_inclusions_from_multiple_sides(output_vars_divisions, output_vars_to_new_output_vars);
            new_element.process_substituting_inclusions_from_left(output_inclusions, false);

            push_to_worklist(std::move(new_element), false);
        }
        ++noodlification_no; // TODO: when to do this increment?? maybe noodlification_no should be part of SolvingState?
    }

    LenNode DecisionProcedure::get_initial_lengths(bool all_vars) {
        if (init_length_sensitive_vars.empty()) {
            // there are no length sensitive vars, so we can immediately say true
            return LenNode(LenFormulaType::TRUE);
        }

        // start from length formula from preprocessing
        std::vector<LenNode> conjuncts = {preprocessing_len_formula};

        // for each initial length variable get the lengths of all its possible words for automaton in init_aut_ass
        if(all_vars) {
            for (const BasicTerm &var : this->formula.get_vars()) {
                conjuncts.push_back(init_aut_ass.get_lengths(var));
            }
        } else {
            for (const BasicTerm &var : this->init_length_sensitive_vars) {
                conjuncts.push_back(init_aut_ass.get_lengths(var));
            }
        }


        return LenNode(LenFormulaType::AND, conjuncts);
    }

    std::pair<LenNode, LenNodePrecision> DecisionProcedure::get_lengths() {
        LenNodePrecision precision = LenNodePrecision::PRECISE; // start with precise and possibly change it later

        if (solution.length_sensitive_vars.empty() && this->not_contains.get_predicates().empty() 
            && this->disequations.get_predicates().empty()) {
            // There is not notcontains predicate to be solved and there are no length vars (which also means no
            // disequations nor conversions), it is not needed to create the lengths formula.
            return {LenNode(LenFormulaType::TRUE), precision};
        }

        // some formulas (lie the one for conversions) assumes that we have flattened substitution map
        solution.flatten_substition_map();

        // collect all variables that substitute some string_var of some conversion (we do it here
        // because we need to know which variables are used in conversions for parikh image of variables
        // in transducers)
        std::tie(code_subst_vars, int_subst_vars) = get_vars_substituted_in_conversions();

        // start with formula for disequations
        std::vector<LenNode> conjuncts = disequations_len_formula_conjuncts;

        // add length formula from preprocessing
        conjuncts.push_back(preprocessing_len_formula);

        // compute formula for vars in transducers (lengths and code-point conversions)
        conjuncts.push_back(get_formula_for_len_vars());

        // formula for encoding lengths
        conjuncts.push_back(get_formula_for_len_vars());

        // add formula for conversions
        auto conv_form_with_precision = get_formula_for_conversions();
        conjuncts.push_back(conv_form_with_precision.first);
        precision = conv_form_with_precision.second;

        // get the LIA formula describing solutions for special predicates
        conjuncts.push_back(get_formula_for_ca_diseqs());
        auto not_cont_prec = get_formula_for_not_contains();
        precision = get_resulting_precision_for_conjunction(precision, not_cont_prec.second);
        conjuncts.push_back(not_cont_prec.first);

        LenNode result(LenFormulaType::AND, conjuncts);
        STRACE("str", tout << "Final " << (precision == LenNodePrecision::PRECISE ? "precise" : "underapproximating") << " formula from get_lengths(): " << result << std::endl;);
        return {result, precision};
    }

    LenNode DecisionProcedure::get_formula_for_transducers() {
        LenNode result(LenFormulaType::AND);

        length_vars_with_transducers = {};
        code_subst_vars_handled_by_parikh = {};

        // We collect transducers in which length variable occurs in the input (right) side (which also means it must
        // occur also in the output). We do not need transducers where we have length variable only in the output, for
        // any word in the output there exists some word in the input for the transducer.
        // In output_var_to_its_transducers[x] we save the transducers where x is output and the transducer has length
        // var in input. In length_input_vars we save all variables that are length and are input of some transducer.
        std::map<BasicTerm, std::vector<Predicate>> output_var_to_its_transducers;
        std::set<BasicTerm> length_input_vars;
        for (const Predicate& trans : solution.transducers) {
            // transducers in solution should be in simple form (one input, one output var)
            SASSERT(trans.get_input().size() == 1);
            SASSERT(trans.get_output().size() == 1);

            BasicTerm input_var = trans.get_input()[0];
            BasicTerm output_var = trans.get_output()[0];

            if (solution.length_sensitive_vars.contains(input_var)) {
                SASSERT(solution.length_sensitive_vars.contains(output_var)); // if input is length var, output must be too
                output_var_to_its_transducers[output_var].push_back(trans);
                length_input_vars.insert(input_var);
            }
        }

        // This function creates one transducer for ouptut_var using all the transducers on input.
        // For example, if we have transducers x = T1(y), y = T2(z), y = T3(v), v = T4(w) we will
        // get a transducer x = T(y,z,v,w) that composes all these 4 transducers together.
        // The second item of the pair gives us the vector of tapes, for the example is it {x,y,z,v,w}.
        std::function<std::pair<mata::nft::Nft,std::vector<BasicTerm>>(BasicTerm)> get_composed_trans_with_tapes;
        get_composed_trans_with_tapes = [&output_var_to_its_transducers, &get_composed_trans_with_tapes, this](BasicTerm output_var) {
            // we start with a simple transducer representing the NFA for output_var (one tape with output_var)
            mata::nft::Nft final_trans{*this->solution.aut_ass.at(output_var)};
            std::vector<BasicTerm> vars_on_tapes{output_var};

            if (output_var_to_its_transducers.contains(output_var)) {
                const auto& transducers = output_var_to_its_transducers.at(output_var);
                for (std::vector<Predicate>::size_type i = 0; i < transducers.size(); ++i) {
                    // we get transducer output_var = Ti(input_var)
                    mata::nft::Nft invert_trans = mata::nft::invert_levels(*transducers[i].get_transducer()); // after inverting output var is level 0, input var is level 1
                    // we get recursively transducer input_var = Ti'(x1, x2, ...., xn) with vector vars_on_tapes_of_input_trans = {input_var, x1, x2, ..., xn}
                    auto [input_trans, vars_on_tapes_of_input_trans] = get_composed_trans_with_tapes(transducers[i].get_input()[0]);
                    SASSERT(!vars_on_tapes_of_input_trans.empty() && vars_on_tapes_of_input_trans[0] == transducers[i].get_input()[0]);
                    // we compose Ti and Ti' on input_var, getting transducer output_var = Ti''(input_var, x1, x2, ...., xn)
                    mata::nft::Nft composed_input = mata::nft::compose(invert_trans, input_trans, 1, 0, false).trim();
                    SASSERT(!composed_input.contains_jump_transitions());
                    SASSERT(composed_input.num_of_states() > 0);
                    // we have a transducer output_var = T(y1, y2, ..., ym) computed from previous Tj's, j < i, and we compose here on output_var with Ti''
                    // getting transducer output_var = T'(y1, y2, ..., ym, input_var, x1, x2, ..., xn)
                    final_trans = mata::nft::compose(final_trans, composed_input, 0, 0, false).trim();
                    SASSERT(!final_trans.contains_jump_transitions());
                    SASSERT(final_trans.num_of_states() > 0);
                    // we had vars_on_tapes = {output_var, y1, y2, ..., ym} we add to it vars_on_tapes_of_input_trans getting
                    //   {output_var, y1, y2, ..., ym, input_var, x1, x2, ..., xn}
                    vars_on_tapes.insert(vars_on_tapes.end(), vars_on_tapes_of_input_trans.begin(), vars_on_tapes_of_input_trans.end());
                }
            }
            return std::make_pair(final_trans, vars_on_tapes);
        };

        // We now find each output_var which is NOT an input var of some transducer, meaning they are at the end of
        // inclusion graph and we create the composed transducer for them.
        std::vector<std::pair<mata::nft::Nft,std::vector<BasicTerm>>> transducers_with_vars_on_tapes;
        for (const auto& [output_var,transducers] : output_var_to_its_transducers) {
            if (!length_input_vars.contains(output_var)) {
                transducers_with_vars_on_tapes.push_back(get_composed_trans_with_tapes(output_var));
            }
        }

        for (const auto& [transducer, vars_on_tapes] : transducers_with_vars_on_tapes) {
            for (const BasicTerm& var : vars_on_tapes) {
                length_vars_with_transducers.insert(var);
                if (int_subst_vars.contains(var)) {
                    // TODO add support (pretty hard, we need to remember the order of selected transitions by parikh)
                    util::throw_error("Integer conversions with transducers are not supported yet");
                }
            }

            mata::nft::Nft transducer_reduced = mata::nft::reduce(mata::nft::remove_epsilon(transducer).trim()).trim();

            STRACE("str-parikh", tout << "Formula for transducer of size " << transducer_reduced.num_of_states() << " with variables " << vars_on_tapes << " is: ";);
            parikh::ParikhImageTransducer parikh_transducer{transducer_reduced, vars_on_tapes, code_subst_vars};
            LenNode parikh_of_transducer = parikh_transducer.compute_parikh_image();
            STRACE("str-parikh", tout << parikh_of_transducer << "\n";);
            result.succ.push_back(parikh_of_transducer);

            // Handle code-point vars that occur in this transducer
            // A dummy symbol (that represent all symbols that are not in the alphabet) occuring in this transducer should have always
            // the same value, therefore, if we have more than one code-point var, we need to share this value. For this, we will use
            // the variable code_point_of_dummy_symbol, and with is_there_code_conversion_with_dummy_symbol, we know whether we actually
            // need this variable.
            bool is_there_code_conversion_with_dummy_symbol = false; // whether there is some code-point var that can be a dummy symbol
            BasicTerm code_point_of_dummy_symbol = util::mk_noodler_var_fresh("dummy_symbol_in_transduers");
            for (const BasicTerm& var : vars_on_tapes) {
                if (code_subst_vars.contains(var)) {
                    code_subst_vars_handled_by_parikh.insert(var);
                    if (!parikh_transducer.get_tape_var_used_symbols().contains(var)) {
                        // if we are here, this means there is no non-epsilon transition for this var in the transducer,
                        // |var| == 0 (this is encoded in parikh) which means that code_version_of(var) == -1
                        result.succ.emplace_back(LenFormulaType::EQ, std::vector<LenNode>{code_version_of(var),-1});
                    } else {
                        // If we are here, parikh_transducer.get_tape_var_used_symbols().at(var) contains all symbols
                        // that are on some transition in the transducer for this var. Therefore we need to create for
                        // each such symbol s the forula that says
                        //    "(|var| == 1 and s occurs in var) => code_version_of(var) == s"

                        // We first encode the formula that var is not one symbol
                        // (|var| != 1 && code_version_of(var) == -1)
                        LenNode non_char_case(LenFormulaType::AND, { {LenFormulaType::NEQ, std::vector<LenNode>{var, 1}}, {LenFormulaType::EQ, std::vector<LenNode>{code_version_of(var),-1}} });

                        // We now continue with the case that |var| ==1
                        // (|var| == 1 && code_version_of(var) is code point of one of the symbols based on parikh)
                        LenNode char_case(LenFormulaType::AND, { {LenFormulaType::EQ, std::vector<LenNode>{var, 1}}, /* code_version_of(var) is code point of one of the symbols based on parikh */ });
            
                        // the rest is just computing 'code_version_of(var) is code point of one of the symbols based on parikh'

                        for (mata::Symbol s : parikh_transducer.get_tape_var_used_symbols().at(var)) {
                            // var for representing how many times s is in var
                            BasicTerm num_of_s_in_var = parikh_transducer.get_tape_var_for_symbol_mapping(var, s);
                            // num_of_s_in_var != 1
                            LenNode num_of_s_in_var_is_one{ LenFormulaType::NEQ, std::vector<LenNode>{num_of_s_in_var, 1} };

                            LenNode code_version_is_equal_to_s(LenFormulaType::EQ, {code_version_of(var)});
                            if (!util::is_dummy_symbol(s)) {
                                // code_version_of(var) == s
                                code_version_is_equal_to_s.succ.push_back(s);
                            } else {
                                is_there_code_conversion_with_dummy_symbol = true;
                                // code_version_of(var) == code_point_of_dummy_symbol
                                code_version_is_equal_to_s.succ.push_back(code_point_of_dummy_symbol);
                            }
                            // (num_of_s_in_var == 1) => (code_version_of(var) == s), i.e.
                            // (num_of_s_in_var != 1) || (code_version_of(var) == s)
                            char_case.succ.push_back({LenFormulaType::OR, {num_of_s_in_var_is_one, code_version_is_equal_to_s}});
                        }

                        result.succ.emplace_back(LenFormulaType::OR, std::vector<LenNode>{
                            non_char_case,
                            char_case
                        });
                    }
                    STRACE("str-parikh-tocode", tout << "tocode parikh formula for " << var << ": " << result.succ.back() << "\n";);
                }
            }

            if (is_there_code_conversion_with_dummy_symbol) {
                STRACE("str-parikh-tocode", tout << "tocode parikh dummy symbol is needed\n";);
                // if there is dummy symbol, then we need to restrict code_point_of_dummy_symbol so that it is a code point of any char, except those in the alphabet

                // code_point_of_dummy_symbol is valid code_point: (0 <= code_point_of_dummy_symbol <= max_char)
                result.succ.emplace_back(LenFormulaType::LEQ, std::vector<LenNode>{0, code_point_of_dummy_symbol});
                result.succ.emplace_back(LenFormulaType::LEQ, std::vector<LenNode>{code_point_of_dummy_symbol, zstring::max_char()});

                // code_point_of_dummy_symbol is not equal to code point of some symbol in the alphabet
                for (mata::Symbol s : solution.aut_ass.get_alphabet()) {
                    if (!util::is_dummy_symbol(s)) {
                        result.succ.emplace_back(LenFormulaType::NEQ, std::vector<LenNode>{code_point_of_dummy_symbol, s});
                    }
                }
            }
        }

        return result;
    }

    LenNode DecisionProcedure::get_formula_for_len_vars() {
        LenNode result(LenFormulaType::AND);
        // create length constraints from the solution, we only need to look at length sensitive vars which do not have length based on parikh
        for (const BasicTerm &len_var : solution.length_sensitive_vars) {
            if (!length_vars_with_transducers.contains(len_var)) {
                result.succ.push_back(solution.get_lengths(len_var));
            }
        }

        return result;
    }

    std::pair<std::set<BasicTerm>,std::set<BasicTerm>> DecisionProcedure::get_vars_substituted_in_conversions() {
        std::set<BasicTerm> code_subst_vars, int_subst_vars;
        for (const TermConversion& conv : conversions) {
            switch (conv.type)
            {
                case ConversionType::FROM_CODE:
                case ConversionType::TO_CODE:
                {
                    for (const BasicTerm& var : solution.get_substituted_vars(conv.string_var)) {
                        code_subst_vars.insert(var);
                    }
                    break;
                }
                case ConversionType::TO_INT:
                case ConversionType::FROM_INT:
                {
                    for (const BasicTerm& var : solution.get_substituted_vars(conv.string_var)) {
                        int_subst_vars.insert(var);
                    }
                    break;
                }
                default:
                    UNREACHABLE();
            }
        }
        return {code_subst_vars, int_subst_vars};
    }

    LenNode DecisionProcedure::get_formula_for_code_subst_vars(const std::set<BasicTerm>& code_subst_vars) {
        LenNode result(LenFormulaType::AND);

        // for each code substituting variable c, create the formula
        //   (|c| != 1 && code_version_of(c) == -1) || (|c| == 1 && code_version_of(c) is code point of one of the chars in the language of automaton for c)
        for (const BasicTerm& c : code_subst_vars) {
            if (code_subst_vars_handled_by_parikh.contains(c)) { continue; }

            // non_char_case = (|c| != 1 && code_version_of(c) == -1)
            LenNode non_char_case(LenFormulaType::AND, { {LenFormulaType::NEQ, std::vector<LenNode>{c, 1}}, {LenFormulaType::EQ, std::vector<LenNode>{code_version_of(c),-1}} });

            // char_case = (|c| == 1 && code_version_of(c) is code point of one of the chars in the language of automaton for c)
            LenNode char_case(LenFormulaType::AND, { {LenFormulaType::EQ, std::vector<LenNode>{c, 1}}, /* code_version_of(c) is code point of one of the chars in the language of automaton for c */ });

            // the rest is just computing 'code_version_of(c) is code point of one of the chars in the language of automaton for c'

            // chars in the language of c (except dummy symbol)
            std::set<mata::Symbol> real_symbols_of_code_var;
            bool is_there_dummy_symbol = false;
            for (mata::Symbol s : mata::strings::get_accepted_symbols(*solution.aut_ass.at(c))) { // iterate trough chars of c
                if (!util::is_dummy_symbol(s)) {
                    real_symbols_of_code_var.insert(s);
                } else {
                    is_there_dummy_symbol = true;
                }
            }

            if (!is_there_dummy_symbol) {
                // if there is no dummy symbol, we can just create disjunction that code_version_of(c) is equal to one of the symbols in real_symbols_of_code_var
                std::vector<LenNode> equal_to_one_of_symbols;
                for (mata::Symbol s : real_symbols_of_code_var) {
                    equal_to_one_of_symbols.emplace_back(LenFormulaType::EQ, std::vector<LenNode>{code_version_of(c), s});
                }
                char_case.succ.emplace_back(LenFormulaType::OR, equal_to_one_of_symbols);
            } else {
                // if there is dummy symbol, then code_version_of(c) can be code point of any char, except those in the alphabet but not in real_symbols_of_code_var

                // code_version_of(c) is valid code_point: (0 <= code_version_of(c) <= max_char)
                char_case.succ.emplace_back(LenFormulaType::LEQ, std::vector<LenNode>{0, code_version_of(c)});
                char_case.succ.emplace_back(LenFormulaType::LEQ, std::vector<LenNode>{code_version_of(c), zstring::max_char()});

                // code_version_of(c) is not equal to code point of some symbol in the alphabet that is not in real_symbols_of_code_var
                for (mata::Symbol s : solution.aut_ass.get_alphabet()) {
                    if (!util::is_dummy_symbol(s) && !real_symbols_of_code_var.contains(s)) {
                        char_case.succ.emplace_back(LenFormulaType::NEQ, std::vector<LenNode>{code_version_of(c), s});
                    }
                }
            }

            result.succ.emplace_back(LenFormulaType::OR, std::vector<LenNode>{
                non_char_case,
                char_case
            });
        }

        return result;
    }

    LenNode DecisionProcedure::encode_interval_words(const BasicTerm& var, const std::vector<interval_word>& interval_words) {
        LenNode result(LenFormulaType::OR);
        for (const auto& interval_word : interval_words) {
            // How this works on an example:
            //      interval_word = [4-5][0-9][2-5][0-9][0-9]
            // We need to encode, as succintcly as possible, that var is any number from the interval word.
            // It is easy to see, that because last two positions can use all digits, we can create following inequations:
            //      ..200 <= var <= ..599
            // where the first two digits are any of [4-5] and [0-9] respectively, i.e., the full encoding should be the
            // following disjunct:
            //      40200 <= var <= 40599 ||
            //      41200 <= var <= 41599 ||
            //               ...
            //      49200 <= var <= 49599 ||
            //      50200 <= var <= 50599 ||
            //      51200 <= var <= 51599 ||
            //               ...
            //      59200 <= var <= 59599

            // We first compute the vector interval_cases of all the intervals [40200-40599], [41200-41599], ...
            // by going backwards in the interval_word, first by computing the main interval [..200-..599] which
            // ends after hitting first digit interval that does not contain all digits (in the exmaple it is [2-5])
            // and after that point, we add all the possible cases for all digits in the following digit intervals.
            std::vector<std::pair<rational,rational>> interval_cases = { {rational(0),rational(0)} }; // start with interval [0-0], with the assumption that interval word is not empty
            assert(interval_word.size() > 0);
            rational place_value(1); // which point in the interval_word we are now (ones, tens, hundreds, etc.)
            bool need_to_split = false; // have we hit the digit interval that does not contain all digits yet?
            for (auto interval_it = interval_word.crbegin(); interval_it != interval_word.crend(); ++interval_it) { // going backwards in interval_word
                // we are processing interval [s-e]
                rational interval_start(interval_it->first - AutAssignment::DIGIT_SYMBOL_START);
                rational interval_end(interval_it->second - AutAssignment::DIGIT_SYMBOL_START);

                if (!need_to_split) {
                    // We are in the situation that all digit intervals after the currently processed one are in the form [0-9], i.e., we have
                    //      ...[s-e][0-9]...[0-9]
                    // Therefore, we should have only one interval of the form [0...0-9...9] in interval_cases
                    assert(interval_cases.size() == 1);
                    // We change this interval into [s0...0-e9...9]
                    interval_cases[0].first += interval_start*place_value;
                    interval_cases[0].second += interval_end*place_value;
                    if (interval_start != 0 || interval_end != 9) {
                        // If the currently processed interval is not of the form [0-9], we will have to add all cases for
                        need_to_split = true;
                    }
                } else {
                    // At least one of the digit intervals after the currently processed one is not in the form [0-9],
                    // so for each interval [S-E] in interval_cases and each digit d, s<=d<=e, we need to add interval
                    // [dS-dE] to the new vector of interval_cases.
                    std::vector<std::pair<rational,rational>> new_interval_cases;
                    for (std::pair<rational,rational>& interval_case : interval_cases) {
                        // for each interval [S-E] in interval_cases
                        for (rational possible_digit = interval_start; possible_digit <= interval_end; ++possible_digit) {
                            // for each digit d, s<=d<=e
                            new_interval_cases.push_back({
                                // add [dS-dE] to new_interval_cases
                                possible_digit*place_value + interval_case.first,
                                possible_digit*place_value + interval_case.second
                            });
                        }
                    }
                    interval_cases = new_interval_cases;
                }

                // move to the following place value (from ones to tens, from tens to hundreds, etc.)
                place_value *= 10;
            }

            // After computing the vector interval_cases, we can just now create the inequalities
            for (const auto& interval_case : interval_cases) {
                rational min = interval_case.first;
                rational max = interval_case.second;
                // we want to put
                //      min <= var <= max
                // but for the special case where min==max, we can just put
                //      var = min (= max)
                if (min == max) {
                    result.succ.emplace_back(LenFormulaType::EQ, std::vector<LenNode>{var, min});
                } else {
                    result.succ.emplace_back(LenFormulaType::AND, std::vector<LenNode>{
                        LenNode(LenFormulaType::LEQ, {min, var}),
                        LenNode(LenFormulaType::LEQ, {var, max})
                    });
                }
            }
        }
        return result;
    }

    std::pair<LenNode, LenNodePrecision> DecisionProcedure::get_formula_for_int_subst_vars(const std::set<BasicTerm>& int_subst_vars, const std::set<BasicTerm>& code_subst_vars, std::map<BasicTerm,std::vector<unsigned>>& int_subst_vars_to_possible_valid_lengths) {
        LenNode result(LenFormulaType::AND);
        LenNodePrecision res_precision = LenNodePrecision::PRECISE;

        // automaton representing all valid inputs (only digits)
        // - we also keep empty word, because we will use it for substituted vars, and one of them can be empty, while other has only digits (for example s1="45", s2="" but s=s1s2 = "45" is valid)
        mata::nfa::Nfa only_digits = AutAssignment::digit_automaton_with_epsilon();
        STRACE("str-conversion-int", tout << "only-digit NFA:" << std::endl << only_digits << std::endl;);
        // automaton representing all non-valid inputs (contain non-digit)
        mata::nfa::Nfa contain_non_digit = solution.aut_ass.complement_aut(only_digits);
        STRACE("str-conversion-int", tout << "contains-non-digit NFA:" << std::endl << contain_non_digit << std::endl;);

        for (const BasicTerm& int_subst_var : int_subst_vars) {
            int_subst_vars_to_possible_valid_lengths[int_subst_var] = {};

            // formula_for_int_subst_var should encode int_version_of(int_subst_var) = to_int(int_subts_var) for all words in solution.aut_ass.at(int_subst_var) while
            // keeping the correspondence between |int_subst_var|, int_version_of(int_subst_var) and possibly also code_version_of(int_subst_var)
            LenNode formula_for_int_subst_var(LenFormulaType::OR);

            std::shared_ptr<mata::nfa::Nfa> aut = solution.aut_ass.at(int_subst_var);
            STRACE("str-conversion-int", tout << "NFA for " << int_subst_var << ":" << std::endl << *aut << std::endl;);

            // part containing only digits
            mata::nfa::Nfa aut_valid_part = mata::nfa::reduce(mata::nfa::intersection(*aut, only_digits).trim());
            STRACE("str-conversion-int", tout << "only-digit NFA:" << std::endl << aut_valid_part << std::endl;);
            // part containing some non-digit
            mata::nfa::Nfa aut_non_valid_part = mata::nfa::reduce(mata::nfa::intersection(*aut, contain_non_digit).trim());
            STRACE("str-conversion-int", tout << "contains-non-digit NFA:" << std::endl << aut_non_valid_part << std::endl;);

            // First handle the case of all words (except empty word) from solution.aut_ass.at(int_subst_var) that do not represent numbers
            if (!aut_non_valid_part.is_lang_empty()) {
                // aut_non_valid_part is language of words that contain at least one non-digit
                // we therefore create following formula:
                //       |int_subst_var| is length of some word from aut_non_valid_part && int_version_of(int_subst_var) = -1
                formula_for_int_subst_var.succ.emplace_back(LenFormulaType::AND, std::vector<LenNode>{ solution.aut_ass.get_lengths(aut_non_valid_part, int_subst_var), LenNode(LenFormulaType::EQ, { int_version_of(int_subst_var), -1 }) });
                if (code_subst_vars.contains(int_subst_var)) {
                    // int_subst_var is used in some to_code/from_code
                    // => we need to add to the previous formula also the fact, that int_subst_var cannot encode code point of a digit
                    //      .. && (code_version_of(int_subst_var) < AutAssignment::DIGIT_SYMBOL_START || AutAssignment::DIGIT_SYMBOL_END < code_version_of(int_subst_var))
                    formula_for_int_subst_var.succ.back().succ.emplace_back(LenFormulaType::OR, std::vector<LenNode>{
                        LenNode(LenFormulaType::LT, { code_version_of(int_subst_var), AutAssignment::DIGIT_SYMBOL_START }),
                        LenNode(LenFormulaType::LT, { AutAssignment::DIGIT_SYMBOL_END, code_version_of(int_subst_var) })
                    });
                }
            }

            // Now, for each length l of some word containing only digits, we create the formula
            //      (|int_subst_var| = l && int_version_of(int_subst_var) is number represented by some word containing only digits of length l)
            // and add l to int_subst_vars_to_possible_valid_lengths[int_subst_var].
            // For l=0 we need to do something else with the second conjunct, and for l=1, we also need to add something about code_version_of(int_subt_var).

            if (aut_valid_part.is_lang_empty()) {
                result.succ.push_back(formula_for_int_subst_var);
                continue;
            }

            // Handle l=0 as a special case.
            if (aut_valid_part.is_in_lang({})) {
                // Even though it is invalid and it seems that we should set int_version_of(int_subst_var) = -1, we cannot do that
                // as int_subst_var is substituting some string_var in int conversion, and the other variables in the substitution
                // might not be empty, so together they could form a valid string representing integer.
                // In get_formula_for_int_conversion() we will actually ignore the value of int_version_of(int_subst_var) for the case
                // that |int_subst_var| = 0, we just need it to be something else than -1.
                // We therefore get the formula:
                //      |int_subst_var| = 0 && !(int_version_of(int_subst_var) = -1)
                formula_for_int_subst_var.succ.emplace_back(LenFormulaType::AND, std::vector<LenNode>{
                    LenNode(LenFormulaType::EQ, { int_subst_var, 0 }),
                    LenNode(LenFormulaType::NEQ, { int_version_of(int_subst_var), -1 })
                });
                // Also add the information that int_subst_var can have length 0
                int_subst_vars_to_possible_valid_lengths[int_subst_var].push_back(0);
            }

            // maximum length of l
            unsigned max_length_of_words;

            if (aut_valid_part.is_acyclic()) {
                // there is a finite number of words containing only digits => the longest possible word is aut_valid_part.num_of_states()-1
                max_length_of_words = aut_valid_part.num_of_states()-1;
            } else {
                // there is infinite number of such words => we need to underapproximate
                STRACE("str-conversion", tout << "infinite NFA for which we need to do underapproximation:" << std::endl << aut_valid_part << std::endl;);
                max_length_of_words = m_params.m_underapprox_length;
                res_precision = LenNodePrecision::UNDERAPPROX;
            }

            // for lengths l=1 to max_length_of_words
            for (unsigned l = 1; l <= max_length_of_words; ++l) {
                // get automaton representing all accepted words containing only digits of length l
                mata::nfa::Nfa aut_valid_of_length = mata::nfa::minimize(mata::nfa::intersection(aut_valid_part, AutAssignment::digit_automaton_of_length(l)).trim());

                if (aut_valid_of_length.is_lang_empty()) {
                    // there are no such words
                    continue;
                }

                // remember that there are some valid words of length l
                int_subst_vars_to_possible_valid_lengths[int_subst_var].push_back(l);

                // |int_subst_var| = l && encode that int_version_of(int_subst_var) is a numeral represented by some interval word accepted by aut_valid_of_length
                formula_for_int_subst_var.succ.emplace_back(LenFormulaType::AND, std::vector<LenNode>{
                    LenNode(LenFormulaType::EQ, { int_subst_var, l }),
                    encode_interval_words(int_version_of(int_subst_var), AutAssignment::get_interval_words(aut_valid_of_length))
                });

                if (code_subst_vars.contains(int_subst_var) && l == 1) {
                    // int_subst_var is used in some to_code/from_code AND we are handling the case of l==1 (for other lengths, the formula from get_formula_for_code_subst_vars should force that code_version_of(int_subst_var) is -1)
                    // => we need to connect code_version_of(int_subst_var) and int_version_of(int_subst_var)
                    //      code_version_of(int_subst_var) = int_version_of(int_subst_var) + AutAssignment::DIGIT_SYMBOL_START
                    formula_for_int_subst_var.succ.back().succ.emplace_back(LenFormulaType::EQ, std::vector<LenNode>{
                        code_version_of(int_subst_var),
                        LenNode(LenFormulaType::PLUS, std::vector<LenNode>{int_version_of(int_subst_var), AutAssignment::DIGIT_SYMBOL_START })
                    });
                }
            }

            result.succ.push_back(formula_for_int_subst_var);
        }


        STRACE("str-conversion-int", tout << "int_subst_vars formula: " << result << std::endl;);
        return {result, res_precision};
    }

    LenNode DecisionProcedure::get_formula_for_code_conversion(const TermConversion& conv) {
        const BasicTerm& s = conv.string_var;
        const BasicTerm& c = conv.int_var;

        // First handle the invalid inputs
        LenNode invalid_case(LenFormulaType::AND);
        if (conv.type == ConversionType::TO_CODE) {
            // For to_code, invalid input is string whose length is not 1
            // (|s| != 1 && c == -1)
            invalid_case.succ.emplace_back(LenFormulaType::NEQ, std::vector<LenNode>{s, 1});
            invalid_case.succ.emplace_back(LenFormulaType::EQ, std::vector<LenNode>{c, -1});
        } else {
            // For from_code, invalid input is a number not representing a code point of some char
            // (|s| == 0 && c is not a valid code point)
            invalid_case.succ.emplace_back(LenFormulaType::EQ, std::vector<LenNode>{s, 0});
            // non-valid code point means that 'c < 0 || c > max_char'
            invalid_case.succ.emplace_back(LenFormulaType::OR, std::vector<LenNode>{
                LenNode(LenFormulaType::LT, {c, 0}),
                LenNode(LenFormulaType::LT, {zstring::max_char(), c})
            });
        }

        // For s=s_1s_2...s_n substitution in the flattened solution, we now handle the valid inputs:
        //    (|s| == 1 && c >= 0 && c is equal to one of code_version_of(s_i))
        // This is shared for both to_code and from_code.
        LenNode valid_case(LenFormulaType::AND, { {LenFormulaType::EQ, std::vector<LenNode>{s, 1}}, {LenFormulaType::LEQ, std::vector<LenNode>{0, c}}, /*c is equal to one of code_version_of(s_i))*/ });

        // c is equal to one of code_version_of(s_i)
        LenNode equal_to_one_subst_var(LenFormulaType::OR);
        for (const BasicTerm& subst_var : solution.get_substituted_vars(s)) {
            // c == code_version_of(s_i)
            equal_to_one_subst_var.succ.emplace_back(LenFormulaType::EQ, std::vector<LenNode>{c, code_version_of(subst_var)});
        }
        valid_case.succ.push_back(equal_to_one_subst_var);

        return LenNode(LenFormulaType::OR, std::vector<LenNode>{
            invalid_case,
            valid_case
        });
    }

    LenNode DecisionProcedure::get_formula_for_int_conversion(const TermConversion& conv, const std::map<BasicTerm,std::vector<unsigned>>& int_subst_vars_to_possible_valid_lengths) {
        const BasicTerm& s = conv.string_var;
        const BasicTerm& i = conv.int_var;

        LenNode result(LenFormulaType::OR);

        // s = s_1 ... s_n, subst_vars = <s_1, ..., s_n>
        const std::vector<BasicTerm>& subst_vars = solution.get_substituted_vars(s);

        // first handle non-valid cases
        if (conv.type == ConversionType::TO_INT) {
            // for TO_INT empty string or anything that contains non-digit
            LenNode empty_or_one_subst_contains_non_digit(LenFormulaType::OR, {LenNode(LenFormulaType::EQ, {s, 0})}); // start with empty string: |s| = 0
            for (const BasicTerm& subst_var : subst_vars) {
                // subst_var contain non-digit if one of s_i == -1 (see get_formula_for_int_subst_vars)
                empty_or_one_subst_contains_non_digit.succ.emplace_back(LenFormulaType::EQ, std::vector<LenNode>{int_version_of(subst_var), -1});
            }
            result.succ.emplace_back(LenFormulaType::AND, std::vector<LenNode>{
                empty_or_one_subst_contains_non_digit,
                LenNode(LenFormulaType::EQ, {i, -1}) // for non-valid s, to_int(s) == -1
            });
        } else {
            // for FROM_INT only empty string (as we assume that language of s was set to only possible results of from_int)
            result.succ.emplace_back(LenFormulaType::AND, std::vector<LenNode>{
                LenNode(LenFormulaType::LT, {i, 0}), // from_int(i) = "" only if i < 0
                LenNode(LenFormulaType::EQ, {s, 0})
            });
        }

        STRACE("str-conversion-int", tout << "non-valid part for int conversion: " << result << std::endl;);

        if (subst_vars.size() == 0) {
            // we only have empty word, i.e., a non-valid case that is already in result
            return result;
        }

        // length_cases will contain all combinations of lengths l_1,...,l_n, such that l_i represents length of possible word containing only digits of s_i
        std::vector<std::vector<unsigned>> length_cases = {{}};
        for (const BasicTerm& subst_var : solution.get_substituted_vars(s)) { // s_i = subst_var
            std::vector<std::vector<unsigned>> new_cases;
            const auto& possible_lengths = int_subst_vars_to_possible_valid_lengths.at(subst_var);
            if (possible_lengths.size() == 0) {
                // one of the s_i does not have any word containing only digits (not even empty word) => we can just return, there will be just non-valid cases (already in result)
                return result;
            }
            for (unsigned possible_length : possible_lengths) {
                for (const auto& old_case : length_cases) {
                    std::vector<unsigned> new_case = old_case;
                    new_case.push_back(possible_length);
                    new_cases.push_back(new_case);
                }
            }
            length_cases = new_cases;
        }

        for (const auto& one_case : length_cases) {
            assert(subst_vars.size() == one_case.size());

            // Example:
            //      one_case = 2,3,0,1
            // Therefore, int_version_of(s_1) encodes (if it is encoding a number, i.e., it is not equal to -1), for |s_1| == 2,
            // numbers with 2 digits (and there is such number), etc.
            // We can then create formula that says, for the case that |s_1| == 2 && |s_2| == 3 && |s_3| == 0 && |s_4| == 1,
            // i must be equal to
            //      i == int_version_of(s_1)*(10^(3+1)) + int_version_of(s_1)*10 + int_version_of(s_4)
            // For example if int_version_of(s_1) == 15, int_version_of(s_2) == 364 and int_version_of(s_4) == 6, we get
            //      i == 15*10000 + 364*10 + 6 = 150000 + 3640 + 6 = 153646

            // We are then creating formula
            //      ((|s_1| == |l_1| && int_version_of(s_1) != -1) ... && (|s_n| == |l_n| && int_version_of(s_n) != -1)) && ...
            LenNode formula_for_case(LenFormulaType::AND);
            //      ... && i = int_version_of(s_1)*10^(l_2+...+l_n) + int_version_of(s_2)*10^(l_3+...+l_n) + ... + int_version_of(s_2)*10^(l_n) + int_version_of(s_n)
            LenNode formula_for_sum(LenFormulaType::PLUS);

            // However, for case that l_1 = l_2 = ... = l_n = 0, we get an invalid case, so this should be ignored => is_empty will take care of it
            bool is_empty = true;

            rational place_value(1); // builds 10^(...+l_(n-1)+l_n)
            for (int i = subst_vars.size()-1; i >= 0; --i) {
                const BasicTerm& subst_var = subst_vars[i]; // var s_i
                unsigned length_of_subst_var = one_case[i]; // length l_i

                // |s_i| = l_i
                formula_for_case.succ.emplace_back(LenFormulaType::EQ, std::vector<LenNode>{subst_var, length_of_subst_var});
                // For cases where s_i does not represent numbers (except for empty string, but then int_version_of(s_i)!=-1,
                // see get_formula_for_int_subst_vars() for the reason why), we do not want to use it in computation
                // int_version_of(s_i) != -1
                formula_for_case.succ.emplace_back(LenFormulaType::NEQ, std::vector<LenNode>{int_version_of(subst_var), -1});
                STRACE("str-conversion-int", tout << "part of valid part for int conversion: " << formula_for_case << std::endl;);

                if (length_of_subst_var > 0) {
                    is_empty = false; // l_i != 0 => we cannot get the case where all l_1,...,l_n are 0

                    // ... + int_version_of(s_i)*10^(l_{i+1}+...+l_n)
                    formula_for_sum.succ.emplace_back(LenFormulaType::TIMES, std::vector<LenNode>{ int_version_of(subst_var), place_value });
                    STRACE("str-conversion-int", tout << "part of the sum for int conversion: " << formula_for_sum << std::endl;);

                    // place_value = place_value*(10^l_i)
                    for (unsigned j = 0; j < length_of_subst_var; ++j) {
                        place_value *= 10;
                    }
                }
            }

            if (is_empty) continue; // we have the case where every l_i = 0 => ignore, as it is a non-valid case handled at the beginning of the function

            formula_for_case.succ.emplace_back(LenFormulaType::EQ, std::vector<LenNode>{ i, formula_for_sum });

            STRACE("str-conversion-int", tout << "valid part for int conversion: " << formula_for_case << std::endl;);
            result.succ.push_back(formula_for_case);
        }

        STRACE("str-conversion-int", tout << "int conversion: " << result << std::endl;);
        return result;
    }

    /**
     * Creates a LIA formula that encodes to_code/from_code/to_int/from_int functions.
     * Assumes that
     *      - solution is flattened,
     *      - will be used in conjunction with the result of solution.get_lengths,
     *      - the resulting string variable of from_code/from_int is restricted to only valid results of from_code/from_int (should be done in theory_str_noodler::handle_conversion),
     *      - if to_int/from_int will be processed, code points of all digits (symbols 48,..,57) should be in the alphabet (should be done in theory_str_noodler::final_check_eh).
     *
     * We have following types of conversions:
     *      c = to_code(s)
     *      s = from_code(s)
     *      i = to_int(s)
     *      s = from_int(i)
     * With s a string variable and c/i an integer variable.
     * The string variable s can be substituted in the (flattened) solution:
     *      s = s_1 ... s_n (note that we should have |s| = |s_1| + ... + |s_n| from solution.get_lengths)
     * We therefore collect all vars s_i and put them into two sets:
     *      code_subst_vars - all vars that substitute some s in to_code/from_code
     *      int_subst_vars - all vars that substitute some s in to_int/from_int
     *
     * We will then use functions get_formula_for_code_subst_vars and get_formula_for_int_subst_vars to encode
     *      - for each s \in code_subst_vars a formula compactly saying that
     *          - code_version_of(s) is equal to some to_code(w_s) for any w_s \in solution.aut_ass.at(w_s) with the condition that |s| == |w_s|
     *      - for each s \in code_subst_vars a formula compactly saying that
     *          - int_version_of(s) is equal to some to_int(w_s) for any w_s \in solution.aut_ass.at(w_s) with the condition that |s| == |w_s| AND if s also belongs to code_subst_vars, there is a correspondence between int_version_of(s) and code_version_of(s)
     *
     * After that, we use get_formula_for_code_conversion to handle code conversions - both to_code and from_code are handled similarly for valid strings (i.e. strings of length 1), invalid cases must be handled differently.
     * Similarly, we use get_formula_for_int_conversion to handle int_conversions.
     */
    std::pair<LenNode, LenNodePrecision> DecisionProcedure::get_formula_for_conversions() {
        STRACE("str-conversion",
            tout << "Creating formula for conversions" << std::endl;
        );

        // the resulting formula
        LenNode result(LenFormulaType::AND);
        LenNodePrecision res_precision = LenNodePrecision::PRECISE;

        // create formula for each variable substituting some string_var in some code conversion
        LenNode code_subst_formula = get_formula_for_code_subst_vars(code_subst_vars);
        if (!code_subst_formula.succ.empty()) {
            result.succ.push_back(code_subst_formula);
        }

        // create formula for each variable substituting some string_var in some int conversion
        std::map<BasicTerm,std::vector<unsigned>> int_subst_vars_to_possible_valid_lengths;
        auto int_conv_formula_with_precision = get_formula_for_int_subst_vars(int_subst_vars, code_subst_vars, int_subst_vars_to_possible_valid_lengths);
        if (!int_conv_formula_with_precision.first.succ.empty()) {
            result.succ.push_back(int_conv_formula_with_precision.first);
        }
        if (int_conv_formula_with_precision.second != LenNodePrecision::PRECISE) {
            res_precision = int_conv_formula_with_precision.second;
        }

        for (const TermConversion& conv : conversions) {
            STRACE("str-conversion",
                tout << " processing " << get_conversion_name(conv.type) << " with string var " << conv.string_var << " and int var " << conv.int_var << std::endl;
            );

            switch (conv.type)
            {
                case ConversionType::TO_CODE:
                case ConversionType::FROM_CODE:
                {
                    result.succ.push_back(get_formula_for_code_conversion(conv));
                    break;
                }
                case ConversionType::TO_INT:
                case ConversionType::FROM_INT:
                {
                    result.succ.push_back(get_formula_for_int_conversion(conv, int_subst_vars_to_possible_valid_lengths));
                    break;
                }
                default:
                    UNREACHABLE();
            }
        }

        if (result.succ.empty()) {
            result = LenNode(LenFormulaType::TRUE);
        }

        STRACE("str-conversion",
            tout << "Formula for conversions: " << result << std::endl;
        );
        return {result, res_precision};
    }

    void DecisionProcedure::init_ca_diseq(const Predicate& diseq) {
        this->disequations.add_predicate(diseq);
        // include variables occurring in the diseqations into init_length_sensitive_vars
        for (const BasicTerm& var : diseq.get_vars()) {
            this->init_length_sensitive_vars.insert(var);
        }
    }

    LenNode DecisionProcedure::get_formula_for_ca_diseqs() {
        Formula proj_diseqs {};

        auto proj_concat = [&](const Concat& con) -> Concat {
            Concat ret {};
            for(const BasicTerm& bt : con) {
                Concat subst = this->solution.get_substituted_vars(bt);
                ret.insert(ret.end(), subst.begin(), subst.end());
            }
            return ret;
        };

        // take the original disequations (taken from input) and
        // propagate substitutions involved by the current substitution map of
        // a stable solution
        for(const Predicate& dis : this->disequations.get_predicates()) {
            proj_diseqs.add_predicate(Predicate::create_disequation(
                proj_concat(dis.get_left_side()),
                proj_concat(dis.get_right_side())
            ));
        }

        STRACE("str", tout << "CA-DISEQS (original): " << std::endl << this->disequations.to_string() << std::endl;);
        STRACE("str", tout << "CA-DISEQS (substituted): " << std::endl << proj_diseqs.to_string() << std::endl;);
        return ca::get_lia_for_disequations(proj_diseqs, this->solution.aut_ass);
    }

    std::pair<LenNode, LenNodePrecision> DecisionProcedure::get_formula_for_not_contains() {
        Formula proj_not_cont {};

        auto proj_concat = [&](const Concat& con) -> Concat {
            Concat ret {};
            for(const BasicTerm& bt : con) {
                Concat subst = this->solution.get_substituted_vars(bt);
                ret.insert(ret.end(), subst.begin(), subst.end());
            }
            return ret;
        };

        // take the original notcontains (taken from input) and
        // propagate substitutions involved by the current substitution map of
        // a stable solution
        for(const Predicate& not_cont : this->not_contains.get_predicates()) {
            proj_not_cont.add_predicate(Predicate::create_not_contains(
                proj_concat(not_cont.get_haystack()),
                proj_concat(not_cont.get_needle())
            ));
        }

        STRACE("str", tout << "CA-DISEQS (original): " << std::endl << this->not_contains.to_string() << std::endl;);
        STRACE("str", tout << "CA-DISEQS (substituted): " << std::endl << proj_not_cont.to_string() << std::endl;);
        return ca::get_lia_for_not_contains(proj_not_cont, this->solution.aut_ass, true);
    }

    /**
     * @brief Creates initial inclusion graph according to the preprocessed instance.
     */
    void DecisionProcedure::init_computation() {
        Formula equations_and_transducers;

        bool some_diseq_handled_by_ca = false;

        bool has_transducers = false;

        for (auto const &pred : formula.get_predicates()) {
            if (pred.is_equation()) {
                equations_and_transducers.add_predicate(pred);
            } else if (pred.is_inequation()) {
                // If we solve diesquations using CA --> we store the disequations to be solved later on
                if (this->m_params.m_ca_constr) {
                    init_ca_diseq(pred);
                    some_diseq_handled_by_ca = true;
                } else {
                    for (auto const &eq_from_diseq : replace_disequality(pred)) {
                        equations_and_transducers.add_predicate(eq_from_diseq);
                    }
                }
            } else if (pred.is_transducer()) {
                has_transducers = true;
                equations_and_transducers.add_predicate(pred);
            } else {
                util::throw_error("Unsupported constraint in the decision procedure");
            }
        }

        if (has_transducers && this->not_contains.get_predicates().size() > 0) {
            util::throw_error("Transducers cannot be used with counter automata solving"); // TODO: is this true?
        }
        for(const Predicate& nt : this->not_contains.get_predicates()) {
            for(const BasicTerm& var : nt.get_vars()) {
                this->init_length_sensitive_vars.insert(var);
            }
        }

        STRACE("str-dis",
            tout << "Disequation len formula: " << LenNode(LenFormulaType::AND, disequations_len_formula_conjuncts) << std::endl;
        );

        STRACE("str-dis",
            tout << "Equations and transducers after removing disequations" << std::endl;
            for (const auto &eq : equations_and_transducers.get_predicates()) {
                tout << "    " << eq << std::endl;
            }
        );

        SolvingState init_solving_state;
        init_solving_state.length_sensitive_vars = std::move(this->init_length_sensitive_vars);
        init_solving_state.aut_ass = std::move(this->init_aut_ass);
        for (const auto& subs : init_substitution_map) {
            init_solving_state.aut_ass.erase(subs.first);
        }
        init_solving_state.substitution_map = std::move(this->init_substitution_map);

        if (!equations_and_transducers.get_predicates().empty()) {
            FormulaGraph incl_graph = FormulaGraph::create_inclusion_graph(equations_and_transducers);
            for (const FormulaGraphNode &node : incl_graph.get_nodes()) {
                Predicate node_pred = node.get_real_predicate();
                if (node_pred.is_equation()) { // inclusion
                    init_solving_state.inclusions.insert(node_pred);
                } else { // transducer
                    SASSERT(node_pred.is_transducer());
                    if (incl_graph.is_on_cycle(node)) {
                        util::throw_error("We cannot handle non-chain free constraints with transducers");
                    }
                    init_solving_state.transducers.insert(node_pred);
                }

                if (!incl_graph.is_on_cycle(node)) {
                    init_solving_state.predicates_not_on_cycle.insert(node_pred);
                }

                // we assume that nodes of incl_graph are ordered by the topological order
                init_solving_state.predicates_to_process.push_back(node_pred);
            }
        }


        STRACE("str-noodle-dot", tout << "digraph Procedure {\ninit[shape=none, label=\"\"]\n";);
        push_to_worklist(std::move(init_solving_state), true);
    }

    lbool DecisionProcedure::preprocess(PreprocessType opt, const BasicTermEqiv &len_eq_vars) {
        // we collect variables used in conversions, some preprocessing rules cannot be applied for them
        std::unordered_set<BasicTerm> conv_vars;
        for (const auto &conv : conversions) {
            conv_vars.insert(conv.string_var);
        }

        FormulaPreprocessor prep_handler{std::move(this->formula), std::move(this->init_aut_ass), std::move(this->init_length_sensitive_vars), m_params, conv_vars};

        // try to replace the not contains predicates (so-far we replace it by regular constraints)
        if(prep_handler.can_unify_not_contains()) {
            return l_false;
        }

        // So-far just lightweight preprocessing
        prep_handler.remove_trivial();
        prep_handler.reduce_diseqalities();
        if (opt == PreprocessType::UNDERAPPROX) {
            prep_handler.underapprox_languages();
        }
        prep_handler.propagate_eps();
        // Refinement of languages is beneficial only for instances containing not(contains) or disequalities (it is used to reduce the number of
        // disequations/not(contains). For a strong reduction you need to have languages as precise as possible). In the case of
        // pure equalitities it could create bigger automata, which may be problem later during the noodlification.
        if(this->formula.contains_pred_type(PredicateType::Inequation) || this->formula.contains_pred_type(PredicateType::NotContains)) {
            // Refine languages is applied in the order given by the predicates. Single iteration
            // might not update crucial variables that could contradict the formula.
            // Two iterations seem to be a good trade-off since the automata could explode in the fixpoint.
            prep_handler.refine_languages();
            prep_handler.refine_languages();
        }
        // ADDED RULE
        prep_handler.generate_equiv(len_eq_vars);

        prep_handler.propagate_variables();
        prep_handler.propagate_eps();
        prep_handler.infer_alignment();
        prep_handler.remove_regular();
        // Skip_len_sat is not compatible with not(contains) and conversions as the preprocessing may skip equations with variables
        // inside not(contains)/conversion.
        if(this->not_contains.get_predicates().empty() && this->conversions.empty()) {
            prep_handler.skip_len_sat();
        }
        prep_handler.generate_identities();
        prep_handler.propagate_variables();
        prep_handler.refine_languages();
        prep_handler.reduce_diseqalities();
        prep_handler.remove_trivial();
        prep_handler.reduce_regular_sequence(3);
        prep_handler.remove_regular();

        // the following should help with Leetcode
        /// TODO: should be simplyfied? So many preprocessing steps now
        STRACE("str",
            tout << "Variable equivalence classes: " << std::endl;
            for(const auto& t : len_eq_vars) {
                for (const auto& s : t) {
                    tout << s.to_string() << " ";
                }
                tout << std::endl;
            }
        );
        prep_handler.generate_equiv(len_eq_vars);
        prep_handler.common_prefix_propagation();
        prep_handler.common_suffix_propagation();
        prep_handler.propagate_variables();
        prep_handler.generate_identities();
        prep_handler.remove_regular();
        prep_handler.propagate_variables();
        // underapproximation
        if(opt == PreprocessType::UNDERAPPROX) {
            prep_handler.underapprox_languages();
            prep_handler.skip_len_sat(); // if opt == PreprocessType::UNDERAPPROX, there is no not(contains) nor conversion
            prep_handler.reduce_regular_sequence(3);
            prep_handler.remove_regular();
            prep_handler.skip_len_sat(); // if opt == PreprocessType::UNDERAPPROX, there is no not(contains) nor conversion
        }
        prep_handler.reduce_regular_sequence(1);
        prep_handler.generate_identities();
        prep_handler.propagate_variables();
        prep_handler.remove_regular();

        prep_handler.conversions_validity(conversions);

        prep_handler.simplify_not_contains_to_equations();

        // try to replace the not contains predicates (so-far we replace it by regular constraints)
        if(!prep_handler.replace_not_contains() || prep_handler.can_unify_not_contains()) {
            return l_false;
        }

        if(prep_handler.contains_unsat_eqs_or_diseqs()) {
            return l_false;
        }

        // reduce automata of only neccessary variables
        prep_handler.reduce_automata();

         // Refresh the instance
        this->formula = prep_handler.get_modified_formula();
        this->init_aut_ass = prep_handler.get_aut_assignment();
        this->init_substitution_map = prep_handler.get_substitution_map();
        this->init_length_sensitive_vars = prep_handler.get_len_variables();
        this->preprocessing_len_formula = prep_handler.get_len_formula();
        this->inclusions_from_preprocessing = prep_handler.get_removed_inclusions_for_model();

        if (!this->init_aut_ass.is_sat()) {
            // some automaton in the assignment is empty => we won't find solution
            return l_false;
        }

        // extract not contains predicate to a separate container
        this->formula.extract_predicates(PredicateType::NotContains, this->not_contains);

        STRACE("str-nfa", tout << "Automata after preprocessing" << std::endl << init_aut_ass.print());
        STRACE("str",
            tout << "Lenght formula from preprocessing:" << preprocessing_len_formula << std::endl;
            tout << "Length variables after preprocesssing:";
            for (const auto &len_var : init_length_sensitive_vars) {
                tout << " " << len_var;
            }
            tout << std::endl;
            tout << "Formula after preprocessing:" << std::endl << this->formula.to_string() << std::endl;
        );

        // there remains some not contains --> return undef
        if(this->not_contains.get_predicates().size() > 0) {
            return l_undef;
        }

        if (!this->init_aut_ass.is_sat()) {
            // some automaton in the assignment is empty => we won't find solution
            return l_false;
        } else if (this->formula.get_predicates().empty()) {
            // preprocessing solved all (dis)equations => we set the solution (for lengths check)
            this->solution = SolvingState(this->init_aut_ass, {}, {}, {}, {}, this->init_length_sensitive_vars, {});
            return l_true;
        } else {
            // preprocessing was not able to solve it
            return l_undef;
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
    std::vector<Predicate> DecisionProcedure::replace_disequality(Predicate diseq) {

        // automaton accepting empty word or exactly one symbol
        std::shared_ptr<mata::nfa::Nfa> sigma_eps_automaton = std::make_shared<mata::nfa::Nfa>(init_aut_ass.sigma_eps_automaton());

        // function that will take a1 and a2 and create the "to_code(a1) != to_code(a2)" part of the arithmetic formula
        auto create_to_code_ineq = [this](const BasicTerm& var1, const BasicTerm& var2) {
                // we are going to check that to_code(var1) != to_code(var2), we need exact languages, so we make them length
                init_length_sensitive_vars.insert(var1);
                init_length_sensitive_vars.insert(var2);

                // variables that are results of to_code applied to var1/var2
                BasicTerm var1_to_code = BasicTerm(BasicTermType::Variable, var1.get_name().encode() + "!ineq_to_code");
                BasicTerm var2_to_code = BasicTerm(BasicTermType::Variable, var2.get_name().encode() + "!ineq_to_code");

                // add the information that we need to process "var1_to_code = to_code(var1)" and "var2_to_code = to_code(var2)"
                conversions.emplace_back(ConversionType::TO_CODE, var1, var1_to_code);
                conversions.emplace_back(ConversionType::TO_CODE, var2, var2_to_code);

                // add to_code(var1) != to_code(var2) to the len formula for disequations
                disequations_len_formula_conjuncts.push_back(LenNode(LenFormulaType::NEQ, {var1_to_code, var2_to_code}));
        };

        // This optimization represents the situation where L = a1 and R = a2
        // and we know that a1,a2 \in \Sigma \cup {\epsilon}, i.e. we do not create new equations.
        if(diseq.get_left_side().size() == 1 && diseq.get_right_side().size() == 1) {
            BasicTerm a1 = diseq.get_left_side()[0];
            BasicTerm a2 = diseq.get_right_side()[0];
            auto autl = init_aut_ass.at(a1);
            auto autr = init_aut_ass.at(a2);

            if(mata::nfa::is_included(*autl, *sigma_eps_automaton) && mata::nfa::is_included(*autr, *sigma_eps_automaton)) {
                // create to_code(a1) != to_code(a2)
                create_to_code_ineq(a1, a2);
                STRACE("str-dis", tout << "from disequation " << diseq << " no new equations were created" << std::endl;);
                return std::vector<Predicate>();
            }
        }

        // automaton accepting everything
        std::shared_ptr<mata::nfa::Nfa> sigma_star_automaton = std::make_shared<mata::nfa::Nfa>(init_aut_ass.sigma_star_automaton());

        BasicTerm x1 = util::mk_noodler_var_fresh("diseq_start");
        init_aut_ass[x1] = sigma_star_automaton;
        BasicTerm a1 = util::mk_noodler_var_fresh("diseq_char");
        init_aut_ass[a1] = sigma_eps_automaton;
        BasicTerm y1 = util::mk_noodler_var_fresh("diseq_end");
        init_aut_ass[y1] = sigma_star_automaton;
        BasicTerm x2 = util::mk_noodler_var_fresh("diseq_start");
        init_aut_ass[x2] = sigma_star_automaton;
        BasicTerm a2 = util::mk_noodler_var_fresh("diseq_char");
        init_aut_ass[a2] = sigma_eps_automaton;
        BasicTerm y2 = util::mk_noodler_var_fresh("diseq_end");
        init_aut_ass[y2] = sigma_star_automaton;

        std::vector<Predicate> new_eqs;
        // L = x1a1y1
        new_eqs.push_back(Predicate::create_equation(diseq.get_left_side(), Concat{x1, a1, y1}));
        // R = x2a2y2
        new_eqs.push_back(Predicate::create_equation(diseq.get_right_side(), Concat{x2, a2, y2}));

        // we want |x1| == |x2|, making x1 and x2 length ones
        init_length_sensitive_vars.insert(x1);
        init_length_sensitive_vars.insert(x2);
        // |x1| = |x2|
        disequations_len_formula_conjuncts.push_back(LenNode(LenFormulaType::EQ, {x1, x2}));

        // create to_code(a1) != to_code(a2)
        create_to_code_ineq(a1, a2);

        // we are also going to check for the lengths of y1 and y2, so they have to be length
        init_length_sensitive_vars.insert(y1);
        init_length_sensitive_vars.insert(y2);
        // (|a1| = 0) => (|y1| = 0)
        disequations_len_formula_conjuncts.push_back(LenNode(LenFormulaType::OR, {LenNode(LenFormulaType::NEQ, {a1, 0}), LenNode(LenFormulaType::EQ, {y1, 0})}));
        // (|a2| = 0) => (|y2| = 0)
        disequations_len_formula_conjuncts.push_back(LenNode(LenFormulaType::OR, {LenNode(LenFormulaType::NEQ, {a2, 0}), LenNode(LenFormulaType::EQ, {y2, 0})}));

        STRACE("str-dis", tout << "from disequation " << diseq << " created equations: " << new_eqs[0] << " and " << new_eqs[1] << std::endl;);
        return new_eqs;
    }

    void DecisionProcedure::init_model(const std::map<BasicTerm,rational>& arith_model) {
        if (is_model_initialized) { return ;}

        // Move inclusions from inclusions_from_preprocessing to solution (and clear inclusions_from_preprocessing)
        // the inclusions from preprocessing should be of form where all vars on right side
        // occurs only once only in this inclusion, so they should belong to chain-free fragment
        //  => they are not on a cycle (important for model generation, we want to generate the
        //     model of vars on the right side from the left side)
        for (const Predicate& incl : inclusions_from_preprocessing) {
            solution.inclusions.insert(incl);
            solution.predicates_not_on_cycle.insert(incl);
        }
        inclusions_from_preprocessing.clear();

        std::set<mata::Symbol> set_of_symbols_to_replace_dummy_symbol_with;

        // Restrict the languages in solution of length variables and code/int conversion variables by their models
        for (auto& [var, nfa] : solution.aut_ass) {
            if (var.is_literal() || !solution.length_sensitive_vars.contains(var)) { continue; } // literals should have the correct language + we restrict only length vars

            // Restrict length
            rational len = arith_model.at(var);
            mata::nfa::Nfa len_nfa = solution.aut_ass.sigma_automaton_of_length(len.get_unsigned());
            nfa = std::make_shared<mata::nfa::Nfa>(mata::nfa::intersection(*nfa, len_nfa).trim());

            // Restrict int-conversion var
            if (int_subst_vars.contains(var)) {
                if (length_vars_with_transducers.contains(var)) {
                    util::throw_error("We cannot produce models of integer conversions with transducers yet");
                }
                if (len == 0) {
                    // to_int_value(var) != -1 for len==0 (see get_formula_for_int_subst_vars())
                    // so we directly set ""
                    update_model_and_aut_ass(var, zstring());
                } else {
                    rational to_int_value = arith_model.at(int_version_of(var));
                    if (to_int_value == -1) {
                        // the language of var should contain only words containing some non-digit
                        mata::nfa::Nfa only_digits = AutAssignment::digit_automaton_with_epsilon();
                        nfa = std::make_shared<mata::nfa::Nfa>(mata::nfa::intersection(*nfa, solution.aut_ass.complement_aut(only_digits)).trim());
                    } else {
                        zstring to_int_str(to_int_value); // zstring(rational) returns the string representation of the number in the argument
                        SASSERT(len >= to_int_str.length());
                        // pad to_int_str with leading zeros until we reach desired length
                        while (len.get_unsigned() != to_int_str.length()) {
                            to_int_str = zstring("0") + to_int_str;
                        }
                        update_model_and_aut_ass(var, to_int_str);
                    }
                }
            }

            // Restrict code-conversion var
            if (code_subst_vars.contains(var)) {
                if (length_vars_with_transducers.contains(var)) {
                    util::throw_error("We cannot produce models of code-point conversions with transducers yet");
                }
                rational to_code_value = arith_model.at(code_version_of(var));
                if (to_code_value != -1) {
                    mata::Symbol to_code_value_as_symbol = to_code_value.get_unsigned();
                    if (!solution.aut_ass.get_alphabet().contains(to_code_value_as_symbol)) {
                        // the code value is not a symbol of an alphabet, therefore it is "hidden" in a dummy symbol
                        // we want to "unhide" it, and make it explicit
                        set_of_symbols_to_replace_dummy_symbol_with.insert(to_code_value_as_symbol);
                        solution.aut_ass.add_symbol_from_dummy(to_code_value.get_unsigned());
                    }
                    update_model_and_aut_ass(var, zstring(to_code_value.get_unsigned())); // zstring(unsigned) returns char with the code point of the argument
                } // for the case to_code_value == -1 we shoulh have (str.len var) != 1, so we do not need to restrict the language, as it should have been already be restricted by lenght
            }
        }

        // we replace dummy symbol with a new symbol in automata, so we do not have to work with it
        std::optional<mata::Symbol> symbol_replacing_dummy = solution.aut_ass.replace_dummy_with_new_symbol();
        if (symbol_replacing_dummy.has_value()) {
            set_of_symbols_to_replace_dummy_symbol_with.insert(symbol_replacing_dummy.value());
        }

        // we have to also replace dummy symbol in transducers
        solution.replace_dummy_symbol_in_transducers_with(set_of_symbols_to_replace_dummy_symbol_with);

        is_model_initialized = true;

        STRACE("str-model",
            tout << "Init model finished" << std::endl;
            tout << "  Inclusions:" << std::endl;
            for (const auto& incl : solution.inclusions) {
                tout << incl << std::endl;
            }

            tout << "  Transducers:" << std::endl;
            for (const auto& tran : solution.transducers) {
                tout << tran << std::endl;
                if (is_trace_enabled("str-nfa")) {
                    tout << *tran.get_transducer() << std::endl;
                }
            }

            tout << "  Vars in aut ass" << std::endl;
            for (const auto& autass : solution.aut_ass) {
                tout << "      " << autass.first << std::endl;
                if (is_trace_enabled("str-nfa")) {
                    tout << *autass.second << std::endl;
                }
            }
            tout << "  Vars in subst" << std::endl;
            for (const auto& subst : solution.substitution_map) {
                tout << "      " << subst.first << " -> ";
                for (const auto& substituted_var : subst.second) {
                    tout << substituted_var << " ";
                }
                tout << std::endl;
            }
        );
    }

    zstring DecisionProcedure::get_model(BasicTerm var, const std::map<BasicTerm,rational>& arith_model) {
        init_model(arith_model);

        if (model_of_var.contains(var)) {
            return model_of_var.at(var);
        }

        STRACE("str-model",
            tout << "Generating model for var " << var << "\n";
        );

        if (var.is_literal()) {
            return var.get_name();
        }

        if (vars_whose_model_we_are_computing.contains(var)) {
            util::throw_error("There is cycle in inclusion graph, cannot produce model");
        }
        vars_whose_model_we_are_computing.insert(var);

        regex::Alphabet alph(solution.aut_ass.get_alphabet());

        if (solution.substitution_map.contains(var)) {
            zstring result;
            for (const BasicTerm& subs_var : solution.substitution_map.at(var)) {
                result = result + get_model(subs_var, arith_model);
            }
            return update_model_and_aut_ass(var, result);
        } else if (solution.aut_ass.contains(var)) {
            // as a heuristic, we check if the automaton for var contains exactly one word, if yes, we immediately return this word instead of going trough inclusions (this can sometimes help if there is a cycle in inclusions)
            if (solution.aut_ass.is_singleton(var)) {
                mata::Word accepted_word = solution.aut_ass.at(var)->get_word().value();
                return update_model_and_aut_ass(var, alph.get_string_from_mata_word(accepted_word));
            }

            Predicate predicate_with_var_on_right_side;
            if (solution.get_predicate_with_var_on_right_side(var, predicate_with_var_on_right_side)) {
                // TODO check if predicate_with_var_on_right_side lays on a cycle.
                // If it is on a cycle, then we need to use (and implement) the horrible proof.
                // Right now if there is some cycle (checked using vars_whose_model_we_are_computing), we throw error.

                // Transducers are simple, because we assume they are of the form
                //      output_var = T(var)
                // Therefore we just need to get the language of possible inputs given the output is left_side_string
                // and then return some words from intersection of this language and the language for var
                if (predicate_with_var_on_right_side.is_transducer()) {
                    // transducer should be simple => there is one var in the input
                    SASSERT(predicate_with_var_on_right_side.get_output().size() == 1);
                    zstring output_var_model = get_model(predicate_with_var_on_right_side.get_output()[0], arith_model);

                    // transducer should be simple => on the right (input) side there is only var
                    SASSERT(predicate_with_var_on_right_side.get_input().size() == 1 && predicate_with_var_on_right_side.get_input()[0] == var);

                    // we get the possible inputs of transducer when output is model of output_var
                    mata::nfa::Nfa possible_inputs = predicate_with_var_on_right_side.get_transducer()->apply(util::get_mata_word_zstring(output_var_model), 1).to_nfa_move();
                    possible_inputs = mata::nfa::reduce(mata::nfa::remove_epsilon(possible_inputs.trim()));
                    // the model of var is then some word from possible_inputs and the langauge of var
                    mata::Word accepted_word = mata::nfa::intersection(possible_inputs, *solution.aut_ass.at(var)).get_word().value();
                    return update_model_and_aut_ass(var, alph.get_string_from_mata_word(accepted_word));
                }

                // For inclusions, we need to compute the vars on the right side from the vars on the left
                //  - first we get the string model of the left side
                //  - we then do "opposite noodlification" to get the values on the right side
                SASSERT(predicate_with_var_on_right_side.is_equation()); // is inclusion

                zstring left_side_string;
                for (const auto& var_on_left_side : predicate_with_var_on_right_side.get_left_side()) {
                    left_side_string = left_side_string + get_model(var_on_left_side, arith_model);
                }

                if (left_side_string.empty()) {
                    for (const auto &right_side_var : predicate_with_var_on_right_side.get_right_side()) {
                        update_model_and_aut_ass(right_side_var, zstring());
                    }
                } else {
                    const auto& vars_on_right_side = predicate_with_var_on_right_side.get_right_side(); // because inclusion is not on cycle, all variables on the right side must be different
                    std::vector<std::shared_ptr<mata::nfa::Nfa>> automata_on_right_side;
                    for (const auto &right_side_var : vars_on_right_side) {
                        automata_on_right_side.push_back(solution.aut_ass.at(right_side_var));
                    }
                    SASSERT(vars_on_right_side.size() == automata_on_right_side.size());

                    std::vector<zstring> models_of_the_right_side;
                    VERIFY(util::split_word_to_automata(left_side_string, automata_on_right_side, models_of_the_right_side));
                    SASSERT(vars_on_right_side.size() == models_of_the_right_side.size());
                    for (unsigned i = 0; i < vars_on_right_side.size(); ++i) {
                        update_model_and_aut_ass(vars_on_right_side[i], models_of_the_right_side[i]);
                    }
                }
                return model_of_var.at(var);
            } else {
                // var is only on the left side in the inclusion graph => we can return whatever
                const auto& nfa = solution.aut_ass.at(var);
                STRACE("str-model-nfa", tout << "NFA for var " << var << " before getting some word:\n" << *nfa;);
                mata::Word accepted_word = nfa->get_word().value();
                return update_model_and_aut_ass(var, alph.get_string_from_mata_word(accepted_word));
            }
        } else {
            UNREACHABLE();
            return zstring();
        }
    }

    std::vector<BasicTerm> DecisionProcedure::get_len_vars_for_model(const BasicTerm& str_var) {
        // we always need (for initialization) all len_vars that are in aut_ass, so we ignore str_var
        std::vector<BasicTerm> needed_vars;
        for (const BasicTerm& len_var : solution.length_sensitive_vars) {
            if (!len_var.is_literal() && solution.aut_ass.contains(len_var)) {
                needed_vars.push_back(len_var);

                if (int_subst_vars.contains(len_var)) {
                    needed_vars.push_back(int_version_of(len_var));
                }

                if (code_subst_vars.contains(len_var)) {
                    needed_vars.push_back(code_version_of(len_var));
                }
            }
        }
        return needed_vars;
    }

} // Namespace smt::noodler.
