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

    void SolvingState::substitute_vars(std::unordered_map<BasicTerm, std::vector<BasicTerm>> &substitution_map) {
        // substitutes variables in a vector using substitution_map
        auto substitute_vector = [&substitution_map](const std::vector<BasicTerm> &vector) {
            std::vector<BasicTerm> result;
            for (const BasicTerm &var : vector) {
                if (substitution_map.count(var) == 0) {
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
        auto inclusion_has_same_sides = [](const Predicate &inclusion) { return !(inclusion.is_equation() && inclusion.get_left_side() == inclusion.get_right_side()); };

        // substitutes variables of inclusions in a vector using substitute_map, but does not keep the ones that have the same sides after substitution
        auto substitute_set = [&substitute_predicate, &inclusion_has_same_sides](const std::set<Predicate> predicates) {
            std::set<Predicate> new_predicates;
            for (const auto &old_pred : predicates) {
                auto new_pred = substitute_predicate(old_pred);
                if (inclusion_has_same_sides(new_pred)) { // skip inclusions that have both sides equal
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

    lbool DecisionProcedure::compute_next_solution() {
        // iteratively select next state of solving that can lead to solution and
        // process one of the unprocessed nodes (or possibly find solution)
        STRACE("str", tout << "------------------------"
                           << "Getting another solution"
                           << "------------------------" << std::endl;);

        while (!worklist.empty()) {
            SolvingState element_to_process = std::move(worklist.front());
            worklist.pop_front();

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
                );
                return l_true;
            }

            // we will now process one inclusion from the inclusion graph which is at front
            // i.e. we will update automata assignments and substitutions so that this inclusion is fulfilled
            Predicate predicate_to_process = element_to_process.predicates_to_process.front();
            element_to_process.predicates_to_process.pop_front();

            if (predicate_to_process.get_type() == PredicateType::Equation) { // inclusion
                process_inclusion(predicate_to_process, element_to_process);
            } else {
                SASSERT(predicate_to_process.get_type() == PredicateType::Transducer);
                process_transducer(predicate_to_process, element_to_process);
            }
        }

        // there are no solving states left, which means nothing led to solution -> it must be unsatisfiable
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
            std::unordered_map<BasicTerm, std::vector<BasicTerm>> substitution_map;
            auto const non_empty_side_vars = right_side_vars.empty() ?
                                                    inclusion_to_process.get_left_set()
                                                    : inclusion_to_process.get_right_set();
            bool non_empty_side_contains_empty_word = true;
            for (const auto &var : non_empty_side_vars) {
                if (solving_state.aut_ass.contains_epsilon(var)) {
                    // var contains empty word, we substitute it with only empty word, but only if...
                    if (right_side_vars.empty() // ...non-empty side is the left side (var is from left) or...
                            || solving_state.length_sensitive_vars.count(var) > 0 // ...var is length-aware
                        ) {
                        assert(substitution_map.count(var) == 0 && solving_state.aut_ass.count(var) > 0);
                        // we prepare substitution for all vars on the left or only the length vars on the right
                        // (as non-length vars are probably not needed? TODO: would it make sense to update non-length vars too?)
                        substitution_map[var] = {};
                        solving_state.aut_ass.erase(var);
                    }
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

            // TODO: all this following shit is done also during normal noodlification, I need to split it to some better defined functions

            solving_state.remove_predicate(inclusion_to_process);

            // We might be updating left side, in that case we need to process all nodes that contain the variables from the left,
            // i.e. those nodes to which inclusion_to_process goes to. In the case we are updating right side, there will be no edges
            // coming from inclusion_to_process, so this for loop will do nothing.
            for (const auto &dependent_inclusion : solving_state.get_dependent_predicates(inclusion_to_process)) {
                // we push only those nodes which are not already in predicates_to_process
                // if the inclusion_to_process is on cycle, we need to do BFS
                // if it is not on cycle, we can do DFS
                // TODO: can we really do DFS??
                solving_state.push_unique(dependent_inclusion, is_inclusion_to_process_on_cycle);
            }

            // do substitution in the inclusion graph
            solving_state.substitute_vars(substitution_map);
            // update the substitution_map of new_element by the new substitutions
            solving_state.substitution_map.merge(substitution_map);

            // TODO: should we really push to front when not on cycle?
            // TODO: maybe for this case of one side being empty, we should just push to front?
            if (!is_inclusion_to_process_on_cycle) {
                worklist.push_front(solving_state);
            } else {
                worklist.push_back(solving_state);
            }
            return;
        }
        /********************************************************************************************************/
        /*************************************** End of one side is empty ***************************************/
        /********************************************************************************************************/



        /********************************************************************************************************/
        /****************************************** Process left side *******************************************/
        /********************************************************************************************************/
        std::vector<std::shared_ptr<mata::nfa::Nfa>> left_side_automata;
        STRACE("str-nfa", tout << "Left automata:" << std::endl);
        for (const auto &l_var : left_side_vars) {
            left_side_automata.push_back(solving_state.aut_ass.at(l_var));
            STRACE("str-nfa",
                tout << "Automaton for left var " << l_var.get_name() << ":" << std::endl << *left_side_automata.back();
            );
        }
        /********************************************************************************************************/
        /************************************** End of left side processing *************************************/
        /********************************************************************************************************/




        /********************************************************************************************************/
        /***************************************** Process right side *******************************************/
        /********************************************************************************************************/
        // We combine the right side into automata where we concatenate non-length-aware vars next to each other.
        // Each right side automaton corresponds to either concatenation of non-length-aware vars (vector of
        // basic terms) or one lenght-aware var (vector of one basic term). Division then contains for each right
        // side automaton the variables whose concatenation it represents.
        std::vector<std::shared_ptr<mata::nfa::Nfa>> right_side_automata;
        std::vector<std::vector<BasicTerm>> right_side_division;

        assert(!right_side_vars.empty()); // empty case was processed at the beginning
        auto right_var_it = right_side_vars.begin();
        auto right_side_end = right_side_vars.end();

        std::shared_ptr<mata::nfa::Nfa> next_aut = solving_state.aut_ass[*right_var_it];
        std::vector<BasicTerm> next_division{ *right_var_it };
        bool last_was_length = (solving_state.length_sensitive_vars.count(*right_var_it) > 0);
        bool is_there_length_on_right = last_was_length;
        ++right_var_it;

        STRACE("str-nfa", tout << "Right automata:" << std::endl);
        for (; right_var_it != right_side_end; ++right_var_it) {
            std::shared_ptr<mata::nfa::Nfa> right_var_aut = solving_state.aut_ass.at(*right_var_it);
            if (solving_state.length_sensitive_vars.count(*right_var_it) > 0) {
                // current right_var is length-aware
                right_side_automata.push_back(next_aut);
                right_side_division.push_back(next_division);
                STRACE("str-nfa",
                    tout << "Automaton for right var(s)";
                    for (const auto &r_var : next_division) {
                        tout << " " << r_var.get_name();
                    }
                    tout << ":" << std::endl
                            << *next_aut;
                );
                next_aut = right_var_aut;
                next_division = std::vector<BasicTerm>{ *right_var_it };
                last_was_length = true;
                is_there_length_on_right = true;
            } else {
                // current right_var is not length-aware
                if (last_was_length) {
                    // if last var was length-aware, we need to add automaton for it into right_side_automata
                    right_side_automata.push_back(next_aut);
                    right_side_division.push_back(next_division);
                    STRACE("str-nfa",
                        tout << "Automaton for right var(s)";
                        for (const auto &r_var : next_division) {
                            tout << " " << r_var.get_name();
                        }
                        tout << ":" << std::endl
                                << *next_aut;
                    );
                    next_aut = right_var_aut;
                    next_division = std::vector<BasicTerm>{ *right_var_it };
                } else {
                    // if last var was not length-aware, we combine it (and possibly the non-length-aware vars before)
                    // with the current one
                    next_aut = std::make_shared<mata::nfa::Nfa>(mata::nfa::concatenate(*next_aut, *right_var_aut));
                    next_division.push_back(*right_var_it);
                    // TODO should we reduce size here?
                }
                last_was_length = false;
            }
        }
        right_side_automata.push_back(next_aut);
        right_side_division.push_back(next_division);
        STRACE("str-nfa",
            tout << "Automaton for right var(s)";
            for (const auto &r_var : next_division) {
                tout << " " << r_var.get_name();
            }
            tout << ":" << std::endl << *next_aut;
        );
        /********************************************************************************************************/
        /************************************* End of right side processing *************************************/
        /********************************************************************************************************/


        /********************************************************************************************************/
        /****************************************** Inclusion test **********************************************/
        /********************************************************************************************************/
        if (!is_there_length_on_right) {
            // we have no length-aware variables on the right hand side => we need to check if inclusion holds
            assert(right_side_automata.size() == 1); // there should be exactly one element in right_side_automata as we do not have length variables
            // TODO probably we should try shortest words, it might work correctly
            if (is_inclusion_to_process_on_cycle // we do not test inclusion if we have node that is not on cycle, because we will not go back to it (TODO: should we really not test it?)
                && mata::nfa::is_included(solving_state.aut_ass.get_automaton_concat(left_side_vars), *right_side_automata[0])) {
                // TODO can I push to front? I think I can, and I probably want to, so I can immediately test if it is not sat (if solving_state.predicates_to_process is empty), or just to get to sat faster
                worklist.push_front(solving_state);
                // we continue as there is no need for noodlification, inclusion already holds
                return;
            }
        }
        /********************************************************************************************************/
        /*************************************** End of inclusion test ******************************************/
        /********************************************************************************************************/

        solving_state.remove_predicate(inclusion_to_process);

        // We are going to change the automata on the left side (potentially also split some on the right side, but that should not have impact)
        // so we need to add all nodes whose variable assignments are going to change on the right side (i.e. we follow inclusion graph) for processing.
        // Warning: Self-loops are not in inclusion graph, but we might still want to add this node again to predicates_to_process, however, this node will be
        // split during noodlification, so we will only add parts whose right sides actually change (see below in noodlification)
        for (const auto &node : solving_state.get_dependent_predicates(inclusion_to_process)) {
            // we push only those nodes which are not already in predicates_to_process
            // if the inclusion_to_process is on cycle, we need to do BFS
            // if it is not on cycle, we can do DFS
            // TODO: can we really do DFS??
            solving_state.push_unique(node, is_inclusion_to_process_on_cycle);
        }
        // We will need the set of left vars, so we can sort the 'non-existing self-loop' in noodlification (see previous warning)
        const auto left_vars_set = inclusion_to_process.get_left_set();


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
                // TODO do not make a new_var if we can replace it with one left or right var (i.e. new_var is exactly left or right var)
                // TODO also if we can substitute with epsilon, we should do that first? or generally process epsilon substitutions better, in some sort of 'preprocessing'
                BasicTerm new_var = util::mk_noodler_var_fresh(std::string("align_") + std::to_string(noodlification_no));
                left_side_vars_to_new_vars[noodle[i].second[0]].push_back(new_var);
                right_side_divisions_to_new_vars[noodle[i].second[1]].push_back(new_var);
                new_element.aut_ass[new_var] = noodle[i].first; // we assign the automaton to new_var
                STRACE("str-nfa", tout << new_var << std::endl << *noodle[i].first;);
            }

            // Each variable that occurs in the left side or is length-aware needs to be substituted, we use this map for that
            std::unordered_map<BasicTerm, std::vector<BasicTerm>> substitution_map;

            /* Following the example from before, the following loop will create these inclusions from the right side divisions:
                *         t_1 t_2 ⊆ x_4
                *     t_3 t_4 t_5 ⊆ x_1
                *             t_6 ⊆ x_5 x_6
                * However, we do not add the first two inclusions into the inclusion graph but use them for substitution, i.e.
                *        substitution_map[x_4] = t_1 t_2
                *        substitution_map[x_1] = t_3 t_4 t_5
                * because they are length-aware vars.
                */
            for (unsigned i = 0; i < right_side_division.size(); ++i) {
                const auto &division = right_side_division[i];
                if (division.size() == 1 && solving_state.length_sensitive_vars.count(division[0]) != 0) {
                    // right side is length-aware variable y => we are either substituting or adding new inclusion "new_vars ⊆ y"
                    const BasicTerm &right_var = division[0];
                    if (substitution_map.count(right_var)) {
                        // right_var is already substituted, therefore we add 'new_vars ⊆ right_var' to the inclusion graph
                        // TODO: how to decide if sometihng is on cycle? by previous node being on cycle, or when we recompute inclusion graph edges?
                        const auto &new_inclusion = new_element.add_inclusion(right_side_divisions_to_new_vars[i], division, is_inclusion_to_process_on_cycle);
                        // we also add this inclusion to the worklist, as it represents unification
                        // we push it to the front if we are processing node that is not on the cycle, because it should not get stuck in the cycle then
                        // TODO: is this correct? can we push to the front?
                        // TODO: can't we push to front even if it is on cycle??
                        new_element.push_unique(new_inclusion, is_inclusion_to_process_on_cycle);
                        STRACE("str", tout << "added new inclusion from the right side because it could not be substituted: " << new_inclusion << std::endl; );
                    } else {
                        // right_var is not substitued by anything yet, we will substitute it
                        substitution_map[right_var] = right_side_divisions_to_new_vars[i];
                        STRACE("str", tout << "right side var " << right_var.get_name() << " replaced with:"; for (auto const &var : right_side_divisions_to_new_vars[i]) { tout << " " << var.get_name(); } tout << std::endl; );
                        // as right_var wil be substituted in the inclusion graph, we do not need to remember the automaton assignment for it
                        new_element.aut_ass.erase(right_var);
                        // update the length variables
                        for (const BasicTerm &new_var : right_side_divisions_to_new_vars[i]) {
                            new_element.length_sensitive_vars.insert(new_var);
                        }
                    }

                } else {
                    // right side is non-length concatenation "y_1...y_n" => we are adding new inclusion "new_vars ⊆ y1...y_n"
                    // TODO: how to decide if sometihng is on cycle? by previous node being on cycle, or when we recompute inclusion graph edges?
                    // TODO: do we need to add inclusion if previous node was not on cycle? because I think it is not possible to get to this new node anyway
                    const auto &new_inclusion = new_element.add_inclusion(right_side_divisions_to_new_vars[i], division, is_inclusion_to_process_on_cycle);
                    // we add this inclusion to the worklist only if the right side contains something that was on the left (i.e. it was possibly changed)
                    if (SolvingState::is_dependent(left_vars_set, new_inclusion.get_right_set())) {
                        // TODO: again, push to front? back? where the fuck to push??
                        new_element.push_unique(new_inclusion, is_inclusion_to_process_on_cycle);
                    }
                    STRACE("str", tout << "added new inclusion from the right side (non-length): " << new_inclusion << std::endl; );
                }
            }

            /* Following the example from before, the following loop will create these inclusions from the left side:
             *           x_1 ⊆ t_1
             *           x_2 ⊆ t_2 t_3
             *           x_3 ⊆ t_4
             *           x_2 ⊆ t_5 t_6
             * Again, we want to use the inclusions for substitutions, but we replace only those variables which were
             * not substituted yet, so the first inclusion stays (x_1 was substituted from the right side) and the
             * fourth inclusion stays (as we substitute x_2 using the second inclusion). So from the second and third
             * inclusion we get:
             *        substitution_map[x_2] = t_2 t_3
             *        substitution_map[x_3] = t_4
             */
            for (unsigned i = 0; i < left_side_vars.size(); ++i) {
                // TODO maybe if !is_there_length_on_right, we should just do intersection and not create new inclusions
                const BasicTerm &left_var = left_side_vars[i];
                if (left_var.is_literal()) {
                    // we skip literals, we do not want to substitute them
                    continue;
                }
                if (substitution_map.count(left_var)) {
                    // left_var is already substituted, therefore we add 'left_var ⊆ left_side_vars_to_new_vars[i]' to the inclusion graph
                    std::vector<BasicTerm> new_inclusion_left_side{ left_var };
                    // TODO: how to decide if sometihng is on cycle? by previous node being on cycle, or when we recompute inclusion graph edges?
                    const auto &new_inclusion = new_element.add_inclusion(new_inclusion_left_side, left_side_vars_to_new_vars[i], is_inclusion_to_process_on_cycle);
                    // we also add this inclusion to the worklist, as it represents unification
                    // we push it to the front if we are processing node that is not on the cycle, because it should not get stuck in the cycle then
                    // TODO: is this correct? can we push to the front?
                    // TODO: can't we push to front even if it is on cycle??
                    new_element.push_unique(new_inclusion, is_inclusion_to_process_on_cycle);
                    STRACE("str", tout << "added new inclusion from the left side because it could not be substituted: " << new_inclusion << std::endl; );
                } else {
                    // TODO make this function or something, we do the same thing here as for the right side when substituting
                    // left_var is not substitued by anything yet, we will substitute it
                    substitution_map[left_var] = left_side_vars_to_new_vars[i];
                    STRACE("str", tout << "left side var " << left_var.get_name() << " replaced with:"; for (auto const &var : left_side_vars_to_new_vars[i]) { tout << " " << var.get_name(); } tout << std::endl; );
                    // as left_var wil be substituted in the inclusion graph, we do not need to remember the automaton assignment for it
                    new_element.aut_ass.erase(left_var);
                    // update the length variables
                    if (new_element.length_sensitive_vars.count(left_var) > 0) { // if left_var is length-aware => substituted vars should become length-aware
                        for (const BasicTerm &new_var : left_side_vars_to_new_vars[i]) {
                            new_element.length_sensitive_vars.insert(new_var);
                        }
                    }
                }
            }

            // We need to process simple transducers (with at most one output/input var) that stop being simple by the substitution map
            for (const Predicate& simple_transducer : new_element.get_broken_simple_transducers(substitution_map)) {
                SASSERT(!is_inclusion_to_process_on_cycle); // if we have transducers, there should not be a cycle
                new_element.push_unique(simple_transducer, is_inclusion_to_process_on_cycle);
            }

            // do substitution in the inclusion graph
            new_element.substitute_vars(substitution_map);

            // update the substitution_map of new_element by the new substitutions
            new_element.substitution_map.merge(substitution_map);

            // TODO should we really push to front when not on cycle?
            if (!is_inclusion_to_process_on_cycle) {
                worklist.push_front(new_element);
            } else {
                worklist.push_back(new_element);
            }

        }

        ++noodlification_no; // TODO: when to do this increment?? maybe noodlification_no should be part of SolvingState?
        /********************************************************************************************************/
        /*************************************** End of noodlification ******************************************/
        /********************************************************************************************************/

    }

    void DecisionProcedure::process_transducer(const Predicate& transducer_to_process, SolvingState& solving_state) {
        // We assume that if we have transducers in procedure, then the inclusion tree is without cycles
        SASSERT(!solving_state.is_predicate_on_cycle(transducer_to_process));

        // TODO handle epsilons in inputs/outputs differently???

        solving_state.remove_predicate(transducer_to_process);

        const std::vector<BasicTerm>& input_vars = transducer_to_process.get_params()[0];
        const std::vector<BasicTerm>& output_vars = transducer_to_process.get_params()[1];

        if (input_vars.empty()) {
            // emptiness means that on the input we have empty string, therefore, we do not do noodlification but instead apply the empty string on transducer and create new inclusion
            mata::nfa::Nfa application_to_empty_string = mata::nft::project_to(transducer_to_process.get_transducer()->apply(AutAssignment::empty_string_automaton()), 1).to_nfa_move();
            
            if (application_to_empty_string.is_lang_empty()) {
                // empty string is not accepted by transducer as input, this solving_state cannot lead to solution
                return;
            }

            if (output_vars.empty()) {
                // if also ouptut side is just empty string, then we can just check if the result of application contains it
                if (application_to_empty_string.is_in_lang({})) {
                    // if it does, we can continue with this solving_state, otherwise we keep it out of worklist as it will not lead to solution
                    worklist.push_front(solving_state);
                }
                return;
            }

            // we create new inclusion output_var ⊆ application_to_empty_string
            if (mata::strings::is_lang_eps(application_to_empty_string)) {
                // if the application leads to empty string again, the right side of inclusion is empty
                solving_state.push_front_unique(solving_state.add_inclusion(output_vars, {}, false));
            } else {
                // otherwise, right side of inclusion must be application, we create fresh var for it
                BasicTerm fresh_var = util::mk_noodler_var_fresh(std::string("output_") + std::to_string(noodlification_no));
                solving_state.aut_ass[fresh_var] = std::make_shared<mata::nfa::Nfa>(application_to_empty_string);
                solving_state.push_front_unique(solving_state.add_inclusion(output_vars, {fresh_var}, false));
            }

            worklist.push_front(solving_state);
            return;
        }

        if (output_vars.empty()) {
            // we do the same thing when epsilon is in output vars, however we need to take inverted transducer
            mata::nfa::Nfa application_to_empty_string = mata::nft::project_to(mata::nft::invert_levels(*transducer_to_process.get_transducer()).apply(AutAssignment::empty_string_automaton()), 1).to_nfa_move();
            
            if (application_to_empty_string.is_lang_empty()) {
                return;
            }

            // we create new inclusion application_to_empty_string ⊆ input_vars
            if (mata::strings::is_lang_eps(application_to_empty_string)) {
                // if the application leads to empty string again, the left side of inclusion is empty
                solving_state.push_front_unique(solving_state.add_inclusion({}, input_vars, false));
            } else {
                // otherwise, left side of inclusion must be application, we create fresh var for it
                BasicTerm fresh_var = util::mk_noodler_var_fresh(std::string("input_") + std::to_string(noodlification_no));
                solving_state.aut_ass[fresh_var] = std::make_shared<mata::nfa::Nfa>(application_to_empty_string);
                solving_state.push_front_unique(solving_state.add_inclusion({fresh_var}, input_vars, false));
            }

            worklist.push_front(solving_state);
            return;
        }

        std::vector<std::shared_ptr<mata::nfa::Nfa>> input_vars_automata;
        for (const BasicTerm& input_var : input_vars) {
            input_vars_automata.push_back(solving_state.aut_ass.at(input_var));
        }
        std::vector<std::shared_ptr<mata::nfa::Nfa>> output_vars_automata;
        for (const BasicTerm& output_var : output_vars) {
            output_vars_automata.push_back(solving_state.aut_ass.at(output_var));
        }

        std::vector<std::vector<std::tuple<std::shared_ptr<mata::nft::Nft>,unsigned,std::shared_ptr<mata::nfa::Nfa>,unsigned,std::shared_ptr<mata::nfa::Nfa>>>> noodles; // TODO run transducer noodlification
        for (const auto& noodle : noodles) {
            // each noodle is a vector of tuples (T,i,Ai,o,Ao) where
            //      - T is a transducer, which will take one input and one output var: xo = T(xi)
            //      - i is the number denoting which input variable is connected with T
            //      - Ai is NFA for the new input variable xi
            //      - o is the number denoting which output variable is connected with T
            //      - Ao is NFA for the new output variable xo

            SolvingState new_element = solving_state;

            std::vector<std::vector<BasicTerm>> input_vars_to_new_input_vars(input_vars.size());
            std::vector<std::vector<BasicTerm>> output_vars_to_new_output_vars(output_vars.size());
            for (unsigned i = 0; i < noodle.size(); ++i) {
                // TODO do not make new vars if we can replace them with one var

                BasicTerm new_input_var = util::mk_noodler_var_fresh(std::string("input_") + std::to_string(noodlification_no)); // xi
                input_vars_to_new_input_vars[std::get<1>(noodle[i])].push_back(new_input_var);
                new_element.aut_ass[new_input_var] = std::get<2>(noodle[i]); // we assign Ai to new_input_var
                new_element.length_sensitive_vars.insert(new_input_var); // xi is also length-aware as it is in transducer

                BasicTerm new_output_var = util::mk_noodler_var_fresh(std::string("output_") + std::to_string(noodlification_no)); // xo
                output_vars_to_new_output_vars[std::get<3>(noodle[i])].push_back(new_output_var);
                new_element.aut_ass[new_output_var] = std::get<4>(noodle[i]); // we assign Ao to new_output_var
                new_element.length_sensitive_vars.insert(new_output_var); // xo is also length-aware as it is in transducer

                // add the new transducer xo = T(xi)
                new_element.add_transducer(std::get<0>(noodle[i]), {new_input_var}, {new_output_var}, false);
            }

            std::unordered_map<BasicTerm, std::vector<BasicTerm>> substitution_map;

            for (unsigned i = 0; i < input_vars.size(); ++i) {
                const BasicTerm& cur_input_var = input_vars[i];
                if (substitution_map.contains(cur_input_var)) {
                    // cur_input_var is already substituted, we create an inclusion instead
                    const auto &new_inclusion = new_element.add_inclusion(input_vars_to_new_input_vars[i], std::vector<BasicTerm>{cur_input_var}, false);
                    new_element.push_unique(new_inclusion, false);

                    // cur_input_var is certainly not in output_vars (as we assume that we do not have a cycle in the inclusion graph), therefore we do not
                    // need to add this inclusion for processing like we sometimes need while processing inclusions 
                } else {
                    // cur_input_var is not substituted yet, so we substitute it now
                    substitution_map[cur_input_var] = input_vars_to_new_input_vars[i];
                    new_element.aut_ass.erase(cur_input_var);
                }
            }

            for (unsigned i = 0; i < output_vars.size(); ++i) {
                const BasicTerm& cur_output_var = output_vars[i];
                if (substitution_map.contains(cur_output_var)) {
                    // cur_output_var is already substituted, we create an inclusion instead
                    const auto &new_inclusion = new_element.add_inclusion(output_vars_to_new_output_vars[i], std::vector<BasicTerm>{cur_output_var}, false);
                    new_element.push_unique(new_inclusion, false);
                } else {
                    // cur_output_var is not substituted yet, so we substitute it now
                    substitution_map[cur_output_var] = output_vars_to_new_output_vars[i];
                    new_element.aut_ass.erase(cur_output_var);
                }
            }

            // We need to process simple transducers (with at most one output/input var) that stop being simple by the substitution map
            for (const Predicate& simple_transducer : new_element.get_broken_simple_transducers(substitution_map)) {
                new_element.push_unique(simple_transducer, false);
            }

            // do substitution in the inclusion graph
            new_element.substitute_vars(substitution_map);

            // update the substitution_map of new_element by the new substitutions
            new_element.substitution_map.merge(substitution_map);

            worklist.push_front(new_element);
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

        // start with formula for disequations
        std::vector<LenNode> conjuncts = disequations_len_formula_conjuncts;

        // add length formula from preprocessing
        conjuncts.push_back(preprocessing_len_formula);

        // create length constraints from the solution, we only need to look at length sensitive vars
        for (const BasicTerm &len_var : solution.length_sensitive_vars) {
            conjuncts.push_back(solution.get_lengths(len_var));
        }

        // the following functions (getting formula for conversions) assume that we have flattened substitution map
        solution.flatten_substition_map();

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

        // collect all variables that substitute some string_var of some conversion
        std::tie(code_subst_vars, int_subst_vars) = get_vars_substituted_in_conversions();

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
            proj_diseqs.add_predicate(Predicate(PredicateType::Inequation, {
                proj_concat(dis.get_left_side()),
                proj_concat(dis.get_right_side()),
            }));
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

        // take the original disequations (taken from input) and
        // propagate substitutions involved by the current substitution map of
        // a stable solution
        for(const Predicate& dis : this->not_contains.get_predicates()) {
            proj_not_cont.add_predicate(Predicate(PredicateType::NotContains, {
                proj_concat(dis.get_left_side()),
                proj_concat(dis.get_right_side()),
            }));
        }

        STRACE("str", tout << "CA-DISEQS (original): " << std::endl << this->not_contains.to_string() << std::endl;);
        STRACE("str", tout << "CA-DISEQS (substituted): " << std::endl << proj_not_cont.to_string() << std::endl;);
        return ca::get_lia_for_not_contains(proj_not_cont, this->solution.aut_ass, this->m_params.m_ca_constr);
    }

    /**
     * @brief Creates initial inclusion graph according to the preprocessed instance.
     */
    void DecisionProcedure::init_computation() {
        Formula equations_and_transducers;

        bool some_diseq_handled_by_ca = false;

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
                equations_and_transducers.add_predicate(pred);
                for (const BasicTerm& var : pred.get_vars()) {
                    // we add all vars from transducers as length-aware (TODO: do we need to?)
                    this->init_length_sensitive_vars.insert(var);
                }
            } else {
                util::throw_error("Unsupported constraint in the decision procedure");
            }
        }
        // we set all variables in not contains as length
        if(this->m_params.m_ca_constr) {
            for(const Predicate& nt : this->not_contains.get_predicates()) {
                for(const BasicTerm& var : nt.get_vars()) {
                    this->init_length_sensitive_vars.insert(var);
                }
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
            // TODO we probably want to completely get rid of inclusion graphs
            std::deque<std::shared_ptr<GraphNode>> tmp;
            Graph incl_graph = Graph::create_inclusion_graph(equations_and_transducers, tmp);
            for (auto const &node : incl_graph.get_nodes()) {
                init_solving_state.inclusions.insert(node->get_predicate());
                if (!incl_graph.is_on_cycle(node)) {
                    init_solving_state.predicates_not_on_cycle.insert(node->get_predicate());
                }
            }
            // TODO the ordering of predicates_to_process right now is given by how they were added from the splitting graph, should we use something different? also it is not deterministic now, depends on hashes
            while (!tmp.empty()) {
                init_solving_state.predicates_to_process.push_back(tmp.front()->get_predicate());
                tmp.pop_front();
            }
        }

        worklist.push_back(init_solving_state);
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

        // try to replace the not contains predicates (so-far we replace it by regular constraints)
        if(!prep_handler.replace_not_contains() || prep_handler.can_unify_not_contains()) {
            return l_false;
        }

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

        if(this->formula.get_predicates().size() > 0) {
            this->init_aut_ass.reduce(); // reduce all automata in the automata assignment
        }

        if(prep_handler.contains_unsat_eqs_or_diseqs()) {
            return l_false;
        }

        STRACE("str-nfa", tout << "Automata after preprocessing" << std::endl << init_aut_ass.print());
        STRACE("str", tout << "Lenght formula from preprocessing:" << preprocessing_len_formula << std::endl);
        STRACE("str",
            tout << "Length variables after preprocesssing:";
            for (const auto &len_var : init_length_sensitive_vars) {
                tout << " " << len_var;
            }
            tout << std::endl);
        STRACE("str", tout << "Formula after preprocessing:" << std::endl << this->formula.to_string() << std::endl; );

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
            // preprocessing was not able to solve it, we at least reduce the size of created automata
            this->init_aut_ass.reduce();
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
        new_eqs.push_back(Predicate(PredicateType::Equation, {diseq.get_left_side(), Concat{x1, a1, y1}}));
        // R = x2a2y2
        new_eqs.push_back(Predicate(PredicateType::Equation, {diseq.get_right_side(), Concat{x2, a2, y2}}));

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

    void DecisionProcedure::init_model(const std::function<rational(BasicTerm)>& get_arith_model_of_var) {
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

        // Restrict the languages in solution of length variables and code/int conversion variables by their models
        for (auto& [var, nfa] : solution.aut_ass) {
            if (var.is_literal() || !solution.length_sensitive_vars.contains(var)) { continue; } // literals should have the correct language + we restrict only length vars

            // Restrict length
            rational len = get_arith_model_of_var(var);
            mata::nfa::Nfa len_nfa = solution.aut_ass.sigma_automaton_of_length(len.get_unsigned());
            nfa = std::make_shared<mata::nfa::Nfa>(mata::nfa::intersection(*nfa, len_nfa).trim());

            // Restrict int-conversion var
            if (int_subst_vars.contains(var)) {
                if (len == 0) {
                    // to_int_value(var) != -1 for len==0 (see get_formula_for_int_subst_vars())
                    // so we directly set ""
                    update_model_and_aut_ass(var, zstring());
                } else {
                    rational to_int_value = get_arith_model_of_var(int_version_of(var));
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
                rational to_code_value = get_arith_model_of_var(code_version_of(var));
                if (to_code_value != -1) {
                    solution.aut_ass.add_symbol_from_dummy(to_code_value.get_unsigned());
                    update_model_and_aut_ass(var, zstring(to_code_value.get_unsigned())); // zstring(unsigned) returns char with the code point of the argument
                } // for the case to_code_value == -1 we shoulh have (str.len var) != 1, so we do not need to restrict the language, as it should have been already be restricted by lenght
            }
        }

        // we remove dummy symbol from automata, so we do not have to work with it
        solution.aut_ass.replace_dummy_with_new_symbol();

        is_model_initialized = true;

        STRACE("str-model",
            tout << "Init model finished" << std::endl;
            tout << "  Inclusions:" << std::endl;
            for (const auto& incl : solution.inclusions) {
                tout << incl << std::endl;
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

    zstring DecisionProcedure::get_model(BasicTerm var, const std::function<rational(BasicTerm)>& get_arith_model_of_var) {
        init_model(get_arith_model_of_var);

        if (model_of_var.contains(var)) {
            return model_of_var.at(var);
        }

        STRACE("str-model",
            tout << "Generating model for var " << var << "\n";
        );

        if (vars_whose_model_we_are_computing.contains(var)) {
            util::throw_error("There is cycle in inclusion graph, cannot produce model");
        }

        vars_whose_model_we_are_computing.insert(var);

        regex::Alphabet alph(solution.aut_ass.get_alphabet());

        if (solution.substitution_map.contains(var)) {
            zstring result;
            for (const BasicTerm& subs_var : solution.substitution_map.at(var)) {
                result = result + get_model(subs_var, get_arith_model_of_var);
            }
            return update_model_and_aut_ass(var, result);
        } else if (solution.aut_ass.contains(var)) {
            // as a heuristic, we check if the automaton for var contains exactly one word, if yes, we immediately return this word instead of going trough inclusions (this can sometimes help if there is a cycle in inclusions)
            if (solution.aut_ass.is_singleton(var)) {
                mata::Word accepted_word = solution.aut_ass.at(var)->get_word().value();
                return update_model_and_aut_ass(var, alph.get_string_from_mata_word(accepted_word));
            }

            Predicate inclusion_with_var_on_right_side;
            if (solution.get_inclusion_with_var_on_right_side(var, inclusion_with_var_on_right_side)) {
                // TODO check if inclusion_with_var_on_right_side lays on a cycle.
                // If it is on a cycle, then we need to use (and implement) the horrible proof (righ now the following will never finish)
                // Right now if there is some cycle (checked using vars_whose_model_we_are_computing), we throw error.

                // We need to compute the vars on the right side from the vars on the left
                //  - first we get the string model of the left side
                //  - we then do "opposite noodlification" to get the values on the right side

                zstring left_side_string;
                for (const auto& var_on_left_side : inclusion_with_var_on_right_side.get_left_side()) {
                    if (var_on_left_side.is_literal()) {
                        left_side_string = left_side_string + var_on_left_side.get_name();
                    } else {
                        left_side_string = left_side_string + get_model(var_on_left_side, get_arith_model_of_var);
                    }
                }
                if (left_side_string.empty()) {
                    for (const auto &right_side_var : inclusion_with_var_on_right_side.get_right_side()) {
                        update_model_and_aut_ass(right_side_var, zstring());
                    }
                } else {
                    const auto& vars_on_right_side = inclusion_with_var_on_right_side.get_right_side(); // because inclusion is not on cycle, all variables on the right side must be different
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
