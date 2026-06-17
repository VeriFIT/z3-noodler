#include <queue>
#include <utility>
#include <algorithm>
#include <functional>
#include <ranges>
#include <numeric> 

#include <mata/applications/strings.hh>
#include "util.h"
#include "aut_assignment.h"
#include "decision_procedure.h"
#include "regex.h"
#include "conversion_handler.h"

namespace smt::noodler {
    lbool DecisionProcedure::compute_next_solution() {
        // We call the one with length checks but don't check them
        return compute_next_solution_with_len_checks(nullptr).first;
    }

    std::pair<lbool, bool> DecisionProcedure::compute_next_solution_with_len_checks(
        std::function<lbool(bool)> check_lens
    ) {
        // iteratively select next state of solving that can lead to solution and
        // process one of the unprocessed nodes (or possibly find solution)
        STRACE(str, tout << "------------------------"
                           << "Getting another solution"
                           << "------------------------" << std::endl;);

        bool len_checks_enabled = check_lens != nullptr &&
                                  m_params.m_try_premature_len_checks &&
                                  !conversion_handler.are_there_any_conversions() &&
                                  not_contains.get_predicates().empty() &&
                                  (!this->m_params.m_postpone_diseqs_stabilization || !this->input_contains_disequations);
        bool some_skipped = false;

        while (!is_worklist_empty()) {
            util::check_limit(m);
            SolvingState element_to_process = pop_from_worklist();

            if (len_checks_enabled &&
                !element_to_process.predicates_to_process.empty() &&
                element_to_process.transducers.empty() &&
                element_to_process.has_siblings) {
                // Before processing this solving state, we check the
                // length constraints first to potentionally save some time if it is unsat
                this->solution = element_to_process;
                auto lens_sat = check_lens(true);

                STRACE(str_noodle_dot,
                    tout << element_to_process.DOT_name << " [style=filled,fillcolor=\"" << ((lens_sat == l_true) ? "springGreen" : "salmon") << "\"];\n";
                );

                if (lens_sat == l_false) {
                    // Lengths were unsat, we don't have to process this solving state
                    some_skipped = true;
                    continue;
                }
            }

            if (element_to_process.predicates_to_process.empty()) {
                // Now we are in the state with no equations or transducers left to process (but some postponed disequations might be left). 
                // First we in get_lengths generate under-approximation of the disequations by length disequality
                // If the length formula is unsat, we need to solve disequations precisely by translating them to equations and adding to the solving state.
                if (this->m_params.m_postpone_diseqs_stabilization && !element_to_process.postponed_disequations.get_predicates().empty()) {
                    this->solution = element_to_process;
                    lbool underapprox_sat = check_lens(false);
                    if (underapprox_sat == l_false) {
                        if (element_to_process.preprocess_disequations_for_unsat(this->m_params) == l_false) {
                            continue;
                        }
                        element_to_process.translate_postponed_disequations_to_equations();
                    } else if (underapprox_sat == l_true) {
                        solution = std::move(element_to_process);
                        return { l_true, false };
                    } else {
                        // underapprox_sat == l_undef: length under-approximation is inconclusive.
                        // Do not assume satisfiability; instead, solve postponed disequations precisely.
                        element_to_process.translate_postponed_disequations_to_equations();
                    }
                    push_to_worklist(element_to_process, true);
                    continue;
                }

                // we found another solution, element_to_process contain the automata
                // assignment and variable substition that satisfy the original
                // inclusion graph
                solution = std::move(element_to_process);
                STRACE(str,
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
                        if (is_trace_enabled(TraceTag::str_nfa)) {
                            var_aut.second->print_to_mata(tout);
                        }
                    }
                    for (const auto& transd : solution.transducers) {
                        tout << transd << "\n";
                    }
                );
                STRACE(str_noodle_dot, tout << solution.DOT_name << " [style=filled,fillcolor=\"aqua\"];\n";);
                return { l_true, some_skipped };
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
        STRACE(str_noodle_dot, tout << "}\n";);
        return { l_false, some_skipped };
    }

    void DecisionProcedure::process_inclusion(const Predicate& inclusion_to_process, SolvingState& solving_state) {
        // this will decide whether we will continue in our search by DFS or by BFS
        bool is_inclusion_to_process_on_cycle = solving_state.is_predicate_on_cycle(inclusion_to_process);

        STRACE(str, tout << "Processing node with inclusion " << inclusion_to_process << " which is" << (is_inclusion_to_process_on_cycle ? " " : " not ") << "on the cycle" << std::endl;);
        STRACE(str,
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
            solving_state.remove_vars(non_empty_side_vars, initial_variables); // remove unneccesary variables that were substituted
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
        STRACE(str_nfa, tout << "Left automata:" << std::endl);
        auto [left_side_automata, left_side_division] = solving_state.get_automata_and_division_of_concatenation(left_side_vars, false);
        SASSERT(left_side_division.size() == left_side_vars.size()); // each division should contain exactly one left variable
        SASSERT(left_side_automata.size() == left_side_division.size()); // we have one automaton for each division

        // Get automata of the variables on the right side, but we can group non-length-aware vars next to each other
        // together. Each right side automaton corresponds to either concatenation of non-length-aware vars (vector of
        // basic terms) or one lenght-aware var (vector of one basic term). Division then contains for each right
        // side automaton the variables whose concatenation it represents.
        STRACE(str_nfa, tout << "Right automata:" << std::endl);
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
        auto noodles = mata::applications::strings::seg_nfa::noodlify_for_equation(left_side_automata,
                                                                    right_side_automata,
                                                                    false,
                                                                    {{"reduce", "forward"}});
        bool more_than_one_noodle = noodles.size() > 1;

        for (const auto &noodle : noodles) {
            util::check_limit(m);
            STRACE(str, tout << "Processing noodle" << (is_trace_enabled(TraceTag::str_nfa) ? " with automata:" : "") << std::endl;);
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
                                                        true);
                left_side_vars_to_new_vars[noodle[i].second[0]].push_back(new_var);
                right_side_divisions_to_new_vars[noodle[i].second[1]].push_back(new_var);
                STRACE(str_nfa, tout << new_var << std::endl << *noodle[i].first;);
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
            std::set<BasicTerm> newly_substituted_vars_from_right = new_element.process_substituting_inclusions_from_right(right_side_inclusions, is_inclusion_to_process_on_cycle);

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
            std::set<BasicTerm> newly_substituted_vars_from_left = new_element.process_substituting_inclusions_from_left(left_side_inclusions, is_inclusion_to_process_on_cycle);

            // Remove unneccesary variables that were substituted (we do it here, because we the code before depends on the newly substituted vars to be in subtitution_map)
            new_element.remove_vars(newly_substituted_vars_from_right, initial_variables); // remove unneccesary variables that were substituted
            new_element.remove_vars(newly_substituted_vars_from_left, initial_variables); // remove unneccesary variables that were substituted

            // we push to front when the inclusion is not on cycle, because we want to get to the result as fast as possible
            // and if there is no cycle, we do not need to do BFS, the algorithm should end
            new_element.has_siblings = more_than_one_noodle;
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

        STRACE(str, tout << "Processing node with transducer " << transducer_to_process << std::endl;);
        STRACE(str_nfa, tout << *transducer_to_process.get_transducer(););
        STRACE(str,
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

        // If one side is (possibly empty) concatenation of literals, we can apply the literal string on the tape connected with that side and replace the transducer with inclusion.
        // For example, if we have
        //     output_vars = T("abc")          or             "abc" = T(input_vars)
        // we replace it with
        //     output_vars ⊆ fresh_var      or      fresh_var ⊆ input_vars
        // where the language of the fresh_var is the application of "abc" on T (either on input or output, based on which side is "abc").
        zstring literal;
        bool one_side_is_literal = false;
        bool input_is_literal = false;
        mata::nft::Level level_of_literal_side;
        if (util::is_concatenation_of_literals(input_vars, literal)) {
            input_is_literal = true;
            one_side_is_literal = true;
            level_of_literal_side = 0;
        } else if (util::is_concatenation_of_literals(output_vars, literal)) {
            input_is_literal = false;
            one_side_is_literal = true;
            level_of_literal_side = 1;
        } else {
            one_side_is_literal = false;
        }

        if (one_side_is_literal) {
            // we apply the literal to the corresponding tape of the transducer, getting the NFA for the nonliteral side
            mata::nfa::Nfa application_to_literal = transducer_to_process.get_transducer()->apply(util::get_mata_word_zstring(literal), level_of_literal_side, true, mata::nft::JumpMode::NoJump).to_nfa_move();
            application_to_literal = mata::nfa::reduce(mata::nfa::remove_epsilon(application_to_literal.trim()));
            
            if (application_to_literal.is_lang_empty()) {
                // the literal is not accepted by transducer on the corresponding tape, this solving_state cannot lead to solution
                return;
            }

            const std::vector<BasicTerm>& non_literal_side = input_is_literal ? output_vars : input_vars;

            if (non_literal_side.empty()) {
                // if the non-literal side is actually empty, then we can just check if the result of application contains epsilon
                if (application_to_literal.is_in_lang(mata::Word{})) {
                    // if it does, we can continue with this solving_state, otherwise we keep it out of worklist as it will not lead to solution
                    push_to_worklist(std::move(solving_state), false);
                }
                return;
            }

            // we create new inclusion, either output_var ⊆ application_to_literal or application_to_literal ⊆ input_vars
            Predicate new_inclusion = input_is_literal ? Predicate::create_equation(non_literal_side, {}) : Predicate::create_equation({}, non_literal_side);
            if (!mata::applications::strings::is_lang_eps(application_to_literal)) {
                // if the application does not lead to empty string we need to create a new var for literal side and replace it with its language set to application_to_literal
                BasicTerm fresh_var = solving_state.add_fresh_var(std::make_shared<mata::nfa::Nfa>(application_to_literal), std::string("literalsideapp_") + std::to_string(noodlification_no), false, true);
                if (input_is_literal) {
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

        STRACE(str_nfa, tout << "Input automata:" << std::endl);
        auto [input_vars_automata, input_vars_divisions] = solving_state.get_automata_and_division_of_concatenation(input_vars, true);
        SASSERT(input_vars_automata.size() == input_vars_divisions.size());

        // In the case that input side leads to one automaton where we have only non-length vars, we can apply this automaton directly to the transducer.
        // So if we have
        //   output_vars = T(input_vars),
        // we take the language of applying automaton from input_vars on T and create a new fresh_var with this language, where we create
        //    fresh_var = T(input_vars)         and         output_vars ⊆ fresh_var
        // where the inclusion must be processed to update the languages of output_vars.
        // Note: It would seem that we could also use this optimization for when we have one input length var (that leads to one automaton). However,
        // this would not work, after processing the inclusion, the fresh_var (which would need to be length) would be substituted and then "fresh_var = T(input_vars)"
        // would be processed again, but input_vars still lead to one automaton so we would repeat this and get stuck.
        if (input_vars_automata.size() == 1 && !solving_state.contains_length_var(input_vars)) {
            mata::nfa::Nfa application_to_input_automaton = transducer_to_process.get_transducer()->apply(*input_vars_automata[0], 0, true, mata::nft::JumpMode::NoJump).to_nfa_move();
            application_to_input_automaton = mata::nfa::reduce(mata::nfa::remove_epsilon(application_to_input_automaton.trim()));
            
            if (application_to_input_automaton.is_lang_empty()) {
                // applying input on the transducer results in empty language, this solving_state cannot lead to solution
                return;
            }

            // the language of fresh_var is the application, it is length if input_vars contain length
            BasicTerm fresh_var = solving_state.add_fresh_var(std::make_shared<mata::nfa::Nfa>(application_to_input_automaton), std::string("onevarapp_") + std::to_string(noodlification_no), false, true);
            // we add transducer "fresh_var = T(input_vars)"
            solving_state.add_transducer(transducer_to_process.get_transducer(), input_vars, {fresh_var}, false);
            // we add inclusion "output_vars ⊆ fresh_var"
            Predicate new_inclusion = Predicate::create_equation(output_vars, {fresh_var});
            solving_state.add_predicate(new_inclusion, false);
            solving_state.push_front_unique(new_inclusion); // we need to process the inclusion, to update the languages of output_vars
            push_to_worklist(std::move(solving_state), false);
            return;
        }

        STRACE(str_nfa, tout << "Output automata:" << std::endl);
        auto [output_vars_automata, output_vars_divisions] = solving_state.get_automata_and_division_of_concatenation(output_vars, false);
        SASSERT(output_vars_automata.size() == output_vars_divisions.size());
        SASSERT(output_vars_divisions.size() == output_vars.size());

        std::vector<mata::applications::strings::seg_nfa::TransducerNoodle> noodles = mata::applications::strings::seg_nfa::noodlify_for_transducer(transducer_to_process.get_transducer(), input_vars_automata, output_vars_automata, true, m_params.m_homomorphism_heuristic);
        for (const auto& noodle : noodles) {
            util::check_limit(m);
            // each noodle is a vector of tuples (T,i,Ai,o,Ao) where
            //      - T is a transducer, which will take one input and one output var: xo = T(xi)
            //      - i is the number denoting which input variable is connected with T
            //      - Ai is NFA for the new input variable xi
            //      - o is the number denoting which output variable is connected with T
            //      - Ao is NFA for the new output variable xo

            // we are doing similar things as in processing of inclusion, just with two types of vars (input/output) instead of one
            // and the result is also a set of simple transducers 
            STRACE(str, tout << "Processing noodle" << std::endl;);

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
                STRACE(str,
                    tout << "New transducer: " << new_trans << std::endl;
                    if (is_trace_enabled(TraceTag::str_nfa)) {
                        tout << new_input_var << ":\n" << *noodle[i].input_aut
                             << new_output_var << ":\n" << *noodle[i].output_aut
                             << "transducer:\n" << *new_trans.get_transducer();
                    }
                );
            }

            std::vector<Predicate> input_inclusions = util::create_inclusions_from_multiple_sides(input_vars_to_new_input_vars, input_vars_divisions);
            std::set<BasicTerm> newly_substituted_vars_from_right = new_element.process_substituting_inclusions_from_right(input_inclusions, false);

            std::vector<Predicate> output_inclusions = util::create_inclusions_from_multiple_sides(output_vars_divisions, output_vars_to_new_output_vars);
            std::set<BasicTerm> newly_substituted_vars_from_left = new_element.process_substituting_inclusions_from_left(output_inclusions, false);

            // Remove unneccesary variables that were substituted (we do it here, because we the code before depends on the newly substituted vars to be in subtitution_map)
            new_element.remove_vars(newly_substituted_vars_from_right, initial_variables);
            new_element.remove_vars(newly_substituted_vars_from_left, initial_variables);

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

        SolvingState temp_state; // temporary solving state to get lengths
        temp_state.aut_ass = init_aut_ass;
        temp_state.substitution_map = init_substitution_map;
        if(all_vars) {
            for (const BasicTerm &var : this->formula.get_vars()) {
                conjuncts.push_back(temp_state.get_lengths(var));
            }
        } else {
            for (const BasicTerm &var : this->init_length_sensitive_vars) {
                conjuncts.push_back(temp_state.get_lengths(var));
            }
        }


        return LenNode(LenFormulaType::AND, conjuncts);
    }

    std::pair<LenNode, LenNodePrecision> DecisionProcedure::get_lengths() {
        LenNodePrecision precision = LenNodePrecision::PRECISE; // start with precise and possibly change it later

        if (solution.length_sensitive_vars.empty() && this->not_contains.get_predicates().empty() 
            && this->solution.postponed_disequations.get_predicates().empty()) {
            // There is not notcontains predicate to be solved and there are no length vars (which also means no
            // disequations nor conversions), it is not needed to create the lengths formula.
            return {LenNode(LenFormulaType::TRUE), precision};
        }

        conversion_handler.initialize_solution(solution);

        // start with formula from disequation replacements
        std::vector<LenNode> conjuncts(solution.disequations_len_formula_conjuncts.begin(), solution.disequations_len_formula_conjuncts.end());

        // add length formula from preprocessing
        conjuncts.push_back(preprocessing_len_formula);

        // compute formula for vars in transducers (lengths and code-point conversions)
        conjuncts.push_back(get_formula_for_transducers());
        util::check_limit(m);

        // formula for encoding lengths
        conjuncts.push_back(get_formula_for_len_vars());
        util::check_limit(m);

        // add formula for conversions
        auto [conversion_formula, conversion_precision] = conversion_handler.get_formula_encoding_conversions(code_subst_vars_handled_by_parikh);
        conjuncts.push_back(conversion_formula);
        precision = get_resulting_precision_for_conjunction(precision, conversion_precision);

        // get the LIA formula describing solutions for special predicates
        if(this->m_params.m_ca_constr) {
            conjuncts.push_back(get_formula_for_ca_diseqs());
        }
        if (!solution.postponed_disequations.get_predicates().empty()) {
            conjuncts.push_back(solution.get_disequations_underapprox_length_formula());
            // For postponed disequations we currently encode only |lhs| != |rhs|.
            // This is an underapproximation of string disequality and must not be
            // treated as a precise source of unsat.
            precision = get_resulting_precision_for_conjunction(precision, LenNodePrecision::UNDERAPPROX);
        }
        auto [not_cont_formula, not_cont_precicions] = get_formula_for_not_contains();
        conjuncts.push_back(not_cont_formula);
        precision = get_resulting_precision_for_conjunction(precision, not_cont_precicions);

        LenNode result(LenFormulaType::AND, conjuncts);
        STRACE(str, tout << "Final " << (precision == LenNodePrecision::PRECISE ? "precise" : (precision == LenNodePrecision::UNDERAPPROX ?"underapproximating" : "overapproximating")) << " formula from get_lengths(): " << result << std::endl;);
        return {result, precision};
    }

    LenNode DecisionProcedure::get_formula_for_transducers() {
        LenNode result(LenFormulaType::AND);

        length_vars_with_transducers = {};
        code_subst_vars_handled_by_parikh = {};
        transducers_with_parikh_information = {};

        // We collect transducers in which length variable occurs in the input (right) side (which also means it must
        // occur also in the output). We do not need transducers where we have length variable only in the output, for
        // any word in the output there exists some word in the input for the transducer.
        // In output_var_to_its_transducers[x] we save the transducers where x is output and the transducer has length
        // var in input. In length_input_vars we save all variables that are length and are input of some transducer.
        std::map<BasicTerm, std::vector<Predicate>> output_var_to_its_transducers;
        std::set<BasicTerm> length_input_vars;
        for (auto trans_iter = solution.transducers.begin(); trans_iter != solution.transducers.end();) {
            if (solution.contains_length_var(trans_iter->get_input())) {
                // transducers in solution should be in simple form (one input, one output var)
                SASSERT(trans_iter->get_input().size() == 1);
                SASSERT(trans_iter->get_output().size() == 1);
                BasicTerm input_var = trans_iter->get_input()[0];
                BasicTerm output_var = trans_iter->get_output()[0];
                SASSERT(solution.length_sensitive_vars.contains(input_var));
                SASSERT(solution.length_sensitive_vars.contains(output_var)); // if input is length var, output must be too

                output_var_to_its_transducers[output_var].push_back(*trans_iter);
                length_input_vars.insert(input_var);
                // we can remove the transducer, as we will be creating one big transducer from it (which then will be used in model generation)
                trans_iter = solution.transducers.erase(trans_iter);
            } else {
                ++trans_iter;
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
                    mata::nft::Nft composed_input = mata::nft::compose(invert_trans, input_trans, 1, 0, false, mata::nft::JumpMode::NoJump).trim();
                    SASSERT(!composed_input.contains_jump_transitions());
                    SASSERT(composed_input.num_of_states() > 0);
                    // we have a transducer output_var = T(y1, y2, ..., ym) computed from previous Tj's, j < i, and we compose here on output_var with Ti''
                    // getting transducer output_var = T'(y1, y2, ..., ym, input_var, x1, x2, ..., xn)
                    final_trans = mata::nft::compose(final_trans, composed_input, 0, 0, false, mata::nft::JumpMode::NoJump).trim();
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
        for (const auto& [output_var,transducers] : output_var_to_its_transducers | std::views::filter([&length_input_vars](const auto& item){ return !length_input_vars.contains(item.first); })) {
            // The tapes of combined_transducer represent the vars in vars_on_tapes. We want to encode the length dependencies
            // between these vars. We will do it trought parikh formula.
            auto [combined_transducer, vars_on_tapes] = get_composed_trans_with_tapes(output_var);
            assert(combined_transducer.levels.num_of_levels == vars_on_tapes.size());

            // We are now going to build a parikh formula for combined_transducer. We firstly simplify combined_transducer
            // to a one that contains only epsilon transitions and transitions with just one specific symbol. This is because
            // lengths of words of different tapes depend on each other just based on the number of transitions with concrete
            // symbols. However, for code vars, we need to keep exact symbols, so that we are able to compute the exact code-point.
            
            // we build a parikh image for the transducer (first we collect all levels of code_vars)
            std::set<mata::nft::Level> levels_of_code_subst_vars;
            std::set<BasicTerm> code_subst_vars = conversion_handler.get_code_subst_vars();
            for (size_t i = 0; i < vars_on_tapes.size(); ++i) {
                const BasicTerm& var = vars_on_tapes[i];
                length_vars_with_transducers.insert(var);
                if (code_subst_vars.contains(var)) {
                    code_subst_vars_handled_by_parikh.insert(var);
                    levels_of_code_subst_vars.insert(i);
                }
                if (conversion_handler.get_int_subst_vars().contains(var) || conversion_handler.get_real_subst_vars().contains(var)) {
                    // TODO add support (pretty hard, we need to remember the order of selected transitions by parikh)
                    util::throw_error("Integer/real conversions with transducers are not supported yet");
                }
            }

            // We only need the length dependency between variables given by the transducers, therefore we can replace all symbols
            // in the transducer by one symbol except for code-point variables, for these we need exact value (but still, the dependency
            // of this variable on other non-code-point variables is only trough lengths).
            const mata::Symbol ONE_LETTER_SYMBOL = util::get_dummy_symbol() + 1;
            mata::nft::Nft one_symbol_transducer = combined_transducer.get_one_letter_aut(levels_of_code_subst_vars, ONE_LETTER_SYMBOL);

            mata::nft::StateRenaming state_renaming; // will map states of combined_transducer to one_symbol_transducer (if needed for model generation)
            // helping function to combine state renamings
            auto combine_state_renamings = [](mata::nft::StateRenaming& sr_l, const mata::nft::StateRenaming& sr_r) {
                for (auto it = sr_l.begin(); it != sr_l.end(); ) {
                    if (!sr_r.contains(it->second)) {
                        it = sr_l.erase(it);
                    } else {
                        it->second = sr_r.at(it->second);
                        ++it;
                    }
                }
            };

            if (m_params.m_produce_models) { // model generation is enabled, we need to compute state renaming
                // we do not do removing epsilons, as this operation can add new transitions which we cannot map to from the original transducer transitions
                one_symbol_transducer = mata::nft::reduce(one_symbol_transducer, &state_renaming);
                mata::nft::StateRenaming other_state_renaming;
                one_symbol_transducer = one_symbol_transducer.trim(&other_state_renaming);
                combine_state_renamings(state_renaming, other_state_renaming);
            } else { // model generation is not enabled, we can ignore state renaming
                one_symbol_transducer = mata::nft::reduce(mata::nft::remove_epsilon(one_symbol_transducer).trim()).trim();
            }

            // we compute the parikh formula for one_symbol_transducer
            STRACE(str_parikh, tout << "Formula for transducer of size " << one_symbol_transducer.num_of_states() << " with variables " << vars_on_tapes << " is: ";);
            parikh::ParikhImageTransducer parikh_transducer{one_symbol_transducer, vars_on_tapes, code_subst_vars};
            LenNode parikh_of_transducer = parikh_transducer.compute_parikh_image();
            STRACE(str_parikh, tout << parikh_of_transducer << "\n";);
            result.succ.push_back(parikh_of_transducer); // add it to the LIA formula

            if (m_params.m_produce_models) { // models are enabled, we need to compute the mapping from combined_transducer transitions and states to parikh variables
                TransducerParikhInformation transducer_with_parikh_information {
                    .nft = std::move(combined_transducer),
                    .vars_on_tapes = vars_on_tapes,
                };

                const auto& gamma_init = parikh_transducer.get_gamma_init();
                for (mata::nft::State s = 0; s < transducer_with_parikh_information.nft.num_of_states(); ++s) {
                    if (state_renaming.contains(s)) {
                        transducer_with_parikh_information.state_to_gamma_init.insert({s, gamma_init[state_renaming.at(s)]});
                    }
                }

                const auto& parikh_transducer_to_var = parikh_transducer.get_trans_vars();
                for (const auto& trans : transducer_with_parikh_information.nft.delta.transitions()) {
                    if (!state_renaming.contains(trans.source) || !state_renaming.contains(trans.target)) continue;

                    // the parikh transition to which trans is mapped
                    parikh::Transition parikh_transition{
                        state_renaming.at(trans.source),
                        // the transitions of code vars levels and epsilon transitions were kept in one_symbol_transducer, so they will be mapped to the same transition, otherwise we map to ONE_LETTER_SYMBOL transition
                        ((levels_of_code_subst_vars.contains(transducer_with_parikh_information.nft.levels[trans.source]) || trans.symbol == mata::nft::EPSILON) ? trans.symbol : ONE_LETTER_SYMBOL),
                        state_renaming.at(trans.target)
                    };
                    if (parikh_transducer_to_var.contains(parikh_transition)) {
                        transducer_with_parikh_information.transition_to_var.insert({trans, parikh_transducer_to_var.at(parikh_transition)});
                    }
                }

                transducers_with_parikh_information.push_back(transducer_with_parikh_information);
            }

            // Handle code-point vars that occur in this transducer
            for (const BasicTerm& var : vars_on_tapes) {
                if (code_subst_vars.contains(var)) {
                    if (!parikh_transducer.get_tape_var_used_symbols().contains(var)) {
                        // if we are here, this means there is no non-epsilon transition for this var in the transducer,
                        // |var| == 0 (this is encoded in parikh) which means that code_version_of(var) == -1
                        result.succ.emplace_back(LenFormulaType::EQ, std::vector<LenNode>{conversion_handler.code_version_of(var),-1});
                    } else {
                        // If we are here, parikh_transducer.get_tape_var_used_symbols().at(var) contains all symbols
                        // that are on some transition in the transducer for this var. Therefore we need to create for
                        // each such symbol s the forula that says
                        //    "(|var| == 1 and s occurs in var) => code_version_of(var) == s"

                        // We first encode the formula that var is not one symbol
                        // (|var| != 1 && code_version_of(var) == -1)
                        LenNode non_char_case(LenFormulaType::AND, { {LenFormulaType::NEQ, std::vector<LenNode>{var, 1}}, {LenFormulaType::EQ, std::vector<LenNode>{conversion_handler.code_version_of(var),-1}} });

                        // We now continue with the case that |var| ==1
                        // (|var| == 1 && code_version_of(var) is code point of one of the symbols based on parikh)
                        LenNode char_case(LenFormulaType::AND, { {LenFormulaType::EQ, std::vector<LenNode>{var, 1}}, /* code_version_of(var) is code point of one of the symbols based on parikh */ });
            
                        // the rest is just computing 'code_version_of(var) is code point of one of the symbols based on parikh'

                        for (mata::Symbol s : parikh_transducer.get_tape_var_used_symbols().at(var)) {
                            if (util::is_dummy_symbol(s)) {
                                // dummy symbols are hard, because there can be connections between different transitions with dummy symbols, even in different transducers
                                // TODO add handling of dummy symbols
                                util::throw_error("We cannot handle dummy symbols in tocode conversions with transducers");
                            }
                            // var for representing how many times s is in var
                            BasicTerm num_of_s_in_var = parikh_transducer.get_tape_var_for_symbol_mapping(var, s);
                            // num_of_s_in_var != 1
                            LenNode num_of_s_in_var_is_one{ LenFormulaType::NEQ, std::vector<LenNode>{num_of_s_in_var, 1} };

                            // code_version_of(var) == s
                            LenNode code_version_is_equal_to_s(LenFormulaType::EQ, {conversion_handler.code_version_of(var), s});

                            // (num_of_s_in_var == 1) => (code_version_of(var) == s), i.e.
                            // (num_of_s_in_var != 1) || (code_version_of(var) == s)
                            char_case.succ.push_back({LenFormulaType::OR, {num_of_s_in_var_is_one, code_version_is_equal_to_s}});
                        }

                        result.succ.emplace_back(LenFormulaType::OR, std::vector<LenNode>{
                            non_char_case,
                            char_case
                        });
                    }
                    STRACE(str_parikh_tocode, tout << "tocode parikh formula for " << var << ": " << result.succ.back() << "\n";);
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

    void DecisionProcedure::init_ca_diseq(const Predicate& diseq) {
        this->disequations.add_predicate(diseq);
        // include variables occurring in the diseqations into init_length_sensitive_vars
        for (const BasicTerm& var : diseq.get_vars()) {
            this->init_length_sensitive_vars.insert(var);
        }
    }

    LenNode DecisionProcedure::get_formula_for_ca_diseqs() {
        Formula proj_diseqs = this->solution.postponed_disequations;

        STRACE(str, tout << "CA-DISEQS (original): " << std::endl << this->disequations.to_string() << std::endl;);
        STRACE(str, tout << "CA-DISEQS (substituted): " << std::endl << proj_diseqs.to_string() << std::endl;);
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

        STRACE(str, tout << "CA-DISEQS (original): " << std::endl << this->not_contains.to_string() << std::endl;);
        STRACE(str, tout << "CA-DISEQS (substituted): " << std::endl << proj_not_cont.to_string() << std::endl;);
        return ca::get_lia_for_not_contains(proj_not_cont, this->solution.aut_ass, true);
    }

    /**
     * @brief Creates initial inclusion graph according to the preprocessed instance.
     */
    void DecisionProcedure::init_computation() {
        Formula equations_and_transducers;
        std::vector<Predicate> disequalities_to_replace;

        this->input_contains_disequations = false;
        bool has_transducers = false;

        for (auto const &pred : formula.get_predicates()) {
            if (pred.is_equation()) {
                equations_and_transducers.add_predicate(pred);
            } else if (pred.is_inequation()) {
                // if there are some disequations, we cannot use the heuristic for pruning solving 
                // states based on lengths becase the heuristic performs over-approximation but the 
                // postponing disequalities involves under-approximation
                this->input_contains_disequations = true;
                // If we solve diesquations using CA --> we store the disequations to be solved later on
                if (this->m_params.m_ca_constr || this->m_params.m_postpone_diseqs_stabilization) {
                    // we store postponed disequations to this->disequations
                    init_ca_diseq(pred);
                } else {
                    disequalities_to_replace.push_back(pred);
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

        // Build init_solving_state before replacing disequalities so we can use SolvingState::replace_disequality
        SolvingState init_solving_state;
        init_solving_state.length_sensitive_vars = std::move(this->init_length_sensitive_vars);
        init_solving_state.aut_ass = std::move(this->init_aut_ass);
        for (const auto& subs : init_substitution_map) {
            init_solving_state.aut_ass.erase(subs.first);
        }
        init_solving_state.substitution_map = std::move(this->init_substitution_map);
        init_solving_state.postponed_disequations = this->disequations;
        init_solving_state.conversions = this->conversion_handler.get_conversions();

        // Replace disequalities using SolvingState::replace_disequality
        for (const Predicate& diseq : disequalities_to_replace) {
            for (const Predicate& eq_from_diseq : init_solving_state.replace_disequality(diseq)) {
                equations_and_transducers.add_predicate(eq_from_diseq);
            }
        }

        STRACE(str_dis,
            tout << "Disequation len formula: " << LenNode(LenFormulaType::AND, init_solving_state.disequations_len_formula_conjuncts) << std::endl;
        );

        STRACE(str_dis,
            tout << "Equations and transducers after removing disequations" << std::endl;
            for (const auto &eq : equations_and_transducers.get_predicates()) {
                tout << "    " << eq << std::endl;
            }
        );

        set_initial_variables(equations_and_transducers, init_solving_state);

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

        init_solving_state.flatten_substition_map();

        STRACE(str_noodle_dot, tout << "digraph Procedure {\ninit[shape=none, label=\"\"]\n";);
        push_to_worklist(std::move(init_solving_state), true);
    }

    lbool DecisionProcedure::preprocess(PreprocessType opt, const BasicTermEqiv &len_eq_vars) {
        // we collect variables used in conversions, some preprocessing rules cannot be applied for them
        std::set<BasicTerm> conv_vars = conversion_handler.get_string_vars_in_conversions();

        FormulaPreprocessor prep_handler{std::move(this->formula), std::move(this->init_aut_ass), std::move(this->init_length_sensitive_vars), m_params, conv_vars};

        // try to replace the not contains predicates (so-far we replace it by regular constraints)
        if(prep_handler.can_unify_not_contains()) {
            return l_false;
        }

        if (prep_handler.contains_unsat_eqs_or_diseqs()) {
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
        if(this->not_contains.get_predicates().empty() && !conversion_handler.are_there_any_conversions()) {
            prep_handler.skip_len_sat();
        }
        prep_handler.generate_identities();
        prep_handler.propagate_variables();

        if (prep_handler.contains_unsat_eqs_or_diseqs()) {
            return l_false;
        }

        prep_handler.refine_languages();
        prep_handler.reduce_diseqalities();
        prep_handler.remove_trivial();
        prep_handler.reduce_regular_sequence(3);
        prep_handler.remove_regular();
        if(m_params.m_preprocess_nft && prep_handler.has_unsat_transducers()) {
            return l_false;
        }

        // the following should help with Leetcode
        /// TODO: should be simplyfied? So many preprocessing steps now
        STRACE(str,
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

        prep_handler.conversions_validity(conversion_handler.get_conversions());

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

        STRACE(str_nfa, tout << "Automata after preprocessing" << std::endl << init_aut_ass.print());
        STRACE(str,
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
            this->solution = SolvingState(this->init_aut_ass, {}, {}, {}, {}, this->init_length_sensitive_vars, {}, false);
            return l_true;
        } else {
            // preprocessing was not able to solve it
            return l_undef;
        }
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

        // we need to first handle dummy symbol, we want to get rid of it and replace it with some valid symbols
        std::set<mata::Symbol> set_of_symbols_to_replace_dummy_symbol_with;
        // the valid symbols can come from code-point conversions
        for (auto& [var, nfa] : solution.aut_ass) {
            if (var.is_literal() || !conversion_handler.is_var_code_subst_var(var)) { continue; }
            rational len = arith_model.at(var);
            rational to_code_value = arith_model.at(conversion_handler.code_version_of(var));
            if (to_code_value != -1) {
                mata::Symbol to_code_value_as_symbol = to_code_value.get_unsigned();
                if (!solution.aut_ass.get_alphabet().contains(to_code_value_as_symbol)) {
                    // the code value is not a symbol of an alphabet, therefore it is "hidden" in a dummy symbol
                    // we want to "unhide" it, and make it explicit
                    set_of_symbols_to_replace_dummy_symbol_with.insert(to_code_value_as_symbol);
                }
                update_model_and_aut_ass(var, zstring(to_code_value.get_unsigned())); // zstring(unsigned) returns char with the code point of the argument
            } // for the case to_code_value == -1 we should have (str.len var) != 1, this restriction will be sorted out further
        }

        if (solution.aut_ass.get_alphabet().contains(util::get_dummy_symbol())) {
            // if there is no symbol from code-point conversions, we add a fresh one instead
            if (set_of_symbols_to_replace_dummy_symbol_with.empty()) {
                set_of_symbols_to_replace_dummy_symbol_with.insert(solution.aut_ass.get_alphabet().get_unused_symbol());
            }

            // we can now replace dummy symbol in automata
            solution.aut_ass.replace_dummy_with_symbols(set_of_symbols_to_replace_dummy_symbol_with);
        }

        // we have to also replace dummy symbol in transducers
        // TODO it is incorrect, dummy symbols need to be replaced on the level of transducer transitions, not on nfa transitions (works only if there is one symbol to replace with)
        solution.replace_dummy_symbol_in_transducers_with(set_of_symbols_to_replace_dummy_symbol_with);

        for (auto& transducer_with_parikh_information : transducers_with_parikh_information) {
            // TODO this can handle only one dummy symbol (and it should be correct with only one)
            transducer_with_parikh_information.replace_dummy_symbol(set_of_symbols_to_replace_dummy_symbol_with);

            STRACE(str_model_transducer, tout << "Constructing model for vars:";);
            std::vector<unsigned> lengths;
            for (size_t tape_num = 0; tape_num < transducer_with_parikh_information.vars_on_tapes.size(); ++tape_num) {
                rational len = arith_model.at(transducer_with_parikh_information.vars_on_tapes[tape_num]);
                lengths.push_back(len.get_unsigned());
                STRACE(str_model_transducer, tout << " " << transducer_with_parikh_information.vars_on_tapes[tape_num] << " (" << len.get_unsigned() << ")";);
            }
            STRACE(str_model_transducer,
                if (is_trace_enabled(TraceTag::str_model_nfa)) {
                    tout << " and for transducer:\n" << transducer_with_parikh_information.nft.print_to_dot(true, true);
                }
                tout << "\n";
            );

            std::vector<mata::Word> words_for_tape_vars = util::get_word_from_nft(
                                                                    transducer_with_parikh_information.nft,
                                                                    lengths,
                                                                    transducer_with_parikh_information.get_potentional_initial_states(arith_model),
                                                                    transducer_with_parikh_information.get_transition_to_value(arith_model)
                                                                ).value();
            for (size_t tape_num = 0; tape_num < transducer_with_parikh_information.vars_on_tapes.size(); ++tape_num) {
                update_model_and_aut_ass(transducer_with_parikh_information.vars_on_tapes[tape_num], regex::Alphabet{solution.aut_ass.get_alphabet()}.get_string_from_mata_word(words_for_tape_vars[tape_num]));
            }
        }

        // get string representing the integer of length len, possibly padded with leading zeroes
        auto get_string_from_integer = [](const rational& len, const rational& integer) {
            if (len == 0) {
                return zstring();
            } else {
                zstring res(integer); // zstring(rational) returns the string representation of the number in the argument
                SASSERT(len >= res.length());
                // pad to_int_str with leading/trailing zeros until we reach the desired length
                while (len.get_unsigned() != res.length()) {
                    res = zstring("0") + res;
                }
                return res;
            }
        };

        // Restrict the languages in solution of length variables and int conversion variables by their models
        for (auto& [var, nfa] : solution.aut_ass) {
            // literals should have the correct language already and we process only length vars which were not already processed in the dummy-symbol step
            if (var.is_literal() || !solution.length_sensitive_vars.contains(var) || model_of_var.contains(var)) { continue; }

            // Restrict length
            rational len = arith_model.at(var);
            mata::nfa::Nfa len_nfa = solution.aut_ass.sigma_automaton_of_length(len.get_unsigned());
            nfa = std::make_shared<mata::nfa::Nfa>(mata::nfa::intersection(*nfa, len_nfa).trim());

            // Restrict int-conversion var
            if (conversion_handler.is_var_int_subst_var(var) && !conversion_handler.is_var_real_subst_var(var)) {
                rational to_int_value = arith_model.at(conversion_handler.int_version_of(var));
                if (to_int_value == -1) {
                    // the language of var should contain only words containing some non-digit
                    mata::nfa::Nfa only_digits = AutAssignment::digit_automaton_with_epsilon();
                    nfa = std::make_shared<mata::nfa::Nfa>(mata::nfa::intersection(*nfa, solution.aut_ass.complement_aut(only_digits)).trim());
                } else {
                    update_model_and_aut_ass(var, get_string_from_integer(len, to_int_value));
                }
            }

            // Restrict real-conversion var
            if (conversion_handler.is_var_real_subst_var(var)) {
                rational to_int_value = arith_model.at(conversion_handler.int_version_of(var));
                rational dot_position = arith_model.at(conversion_handler.dot_position_of(var));
                if (to_int_value == -1 && dot_position == -1) {
                    // the language of var should contain only words containing some non-number
                    const mata::nfa::Nfa non_number = solution.aut_ass.complement_aut(mata::nfa::union_nondet(AutAssignment::digit_automaton_with_epsilon(), AutAssignment::decimal_automaton()));
                    nfa = std::make_shared<mata::nfa::Nfa>(mata::nfa::intersection(*nfa, non_number).trim());
                } else if (to_int_value != -1) {
                    update_model_and_aut_ass(var, get_string_from_integer(len, to_int_value));
                } else {
                    zstring whole_string = get_string_from_integer(dot_position, arith_model.at(conversion_handler.whole_part_of(var)));
                    zstring decimal_string = get_string_from_integer(len-dot_position-1, arith_model.at(conversion_handler.decimal_part_of(var)));
                    update_model_and_aut_ass(var, whole_string + zstring(".") + decimal_string);
                }
            }
        }

        // We compute here models of variables occuring on cycles
        // Find all strongly connected components (cycles) in the inclusion graph using tarjan algorithm
        // We can assume only inclusions and no transducers, as transducers work only for acyclic graphs
        std::vector<std::vector<int>> sccs = tarjan(find_graph_edges());

        STRACE(str_scc_debug,
            int idx = 0;
            tout << "Found strongly connected components" << std::endl;
            for(std::vector<int> x : sccs){
                tout << "scc - " << idx << " = ";
                for (const auto& val : x) {
                    tout << val << " ";
                }
                tout << std::endl;
                idx++;
            }
        );

        //Get model for each SCC
        for(std::vector<int> scc_list : sccs){
            //SCC of size one has just one inclusion and that is not a cycle
            if(scc_list.size() > 1){
                get_model_for_cyclic_SCC(scc_list);
            }
        }

        is_model_initialized = true;

        STRACE(str_model,
            tout << "Init model finished" << std::endl;
            tout << "  Inclusions:" << std::endl;
            for (const auto& incl : solution.inclusions) {
                tout << incl << std::endl;
            }

            tout << "  Transducers:" << std::endl;
            for (const auto& tran : solution.transducers) {
                tout << tran << std::endl;
                if (is_trace_enabled(TraceTag::str_nfa)) {
                    tout << *tran.get_transducer() << std::endl;
                }
            }

            tout << "  Vars in aut ass" << std::endl;
            for (const auto& autass : solution.aut_ass) {
                tout << "      " << autass.first << std::endl;
                if (is_trace_enabled(TraceTag::str_nfa)) {
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

    std::vector<std::vector<int>> DecisionProcedure::find_graph_edges() {
        std::vector<std::vector<int>> adjacency_list;
        //Look throught all inclusions for variable matches
        int idx_right = 0;
        int idx_left = 0;
        
        //foreach inclusion's right side
        for (const Predicate& incl_left : solution.inclusions) {
            adjacency_list.push_back({});

            //pair with each inclusion's left side
            idx_right = 0;
            for (const Predicate& incl_right : solution.inclusions){
                //Is there an edge from L -> R
                if(solution.is_dependent(incl_left.get_side_vars(Predicate::EquationSideType::Left),
                    incl_right.get_side_vars(Predicate::EquationSideType::Right)))
                    adjacency_list[idx_left].push_back(idx_right);           
                idx_right++;
            }
           idx_left++;
        }
        return adjacency_list;
    }

    static void tarjan_visit(int v, const std::vector<std::vector<int>> &adj_list,
                            std::vector<int> &disc, std::vector<int> &lowlink,
                            std::vector<bool> &on_stack, std::stack<int> &dfs_stack,
                            int &visit_counter, std::vector<std::vector<int>> &result) {
        // Initialise discovery time and lowlink
        disc[v] = lowlink[v] = visit_counter++;

        // Push v so descendants can detect back-edges to it via on_stack.
        dfs_stack.push(v);
        on_stack[v] = true;

        for (int w : adj_list[v]) {
            if (disc[w] == -1) {
                // Tree edge: recurse then pull up the lowest reachable index from w's subtree.
                tarjan_visit(w, adj_list, disc, lowlink, on_stack, dfs_stack, visit_counter, result);
                lowlink[v] = std::min(lowlink[v], lowlink[w]);
            }
            else if (on_stack[w]) {
                // Back-edge to an ancestor: use disc[w], not lowlink[w], to avoid merging separate SCCs.
                lowlink[v] = std::min(lowlink[v], disc[w]);
            }
            // Visited and off the stack means w belongs to a finalised SCC — ignore.
        }

        // if v is an SCC root then pop the stack to collect the component.
        if (lowlink[v] == disc[v]) {
            std::vector<int> component;
            int w;
            do {
                w = dfs_stack.top();
                dfs_stack.pop();
                on_stack[w] = false;
                component.push_back(w);
            } while (w != v);
            result.push_back(component);
        }
    }

    std::vector<std::vector<int>> DecisionProcedure::tarjan(const std::vector<std::vector<int>> &adjacency_list) {
        int n = adjacency_list.size();

        std::vector<int> disc(n, -1);
        std::vector<int> lowlink(n, 0);    // Lowest disc reachable from each vertex's subtree
        std::vector<bool> on_stack(n, false);
        std::stack<int> dfs_stack;
        int visit_counter = 0;
        std::vector<std::vector<int>> result;

        // Start from every vertex to handle disconnected graphs.
        for (int vertex = 0; vertex < n; vertex++) {
            if (disc[vertex] == -1)
                tarjan_visit(vertex, adjacency_list, disc, lowlink,
                            on_stack, dfs_stack, visit_counter, result);
        }

        return result;
    }

    void DecisionProcedure::synchronize_word_on_position(int position, Predicate::EquationSideType missing_side, AtomicEquationContext& equation_context) {
        Atom missing_atom = missing_side == Predicate::EquationSideType::Left 
                          ? equation_context.left_side[position] 
                          : equation_context.right_side[position];
        
        // Var that would be changed
        BasicTerm changed_var = missing_atom.term;

        // Get word from opposite side
        std::vector<Atom> opposite_side = missing_side == Predicate::EquationSideType::Left
                                        ? equation_context.right_side : equation_context.left_side;

        int start_in_pattern = position - missing_atom.index; // Get starting position of variable from which the missing atom is 
        int var_length = equation_context.scc_solution[changed_var].size(); // Length of the given variable (num of its atoms)

        //Copy values from opposite side of the equation
        mata::Word new_word_for_var;
        for (int i = 0; i < var_length; i++) {
            const Atom& atom_on_opposite_side = opposite_side[start_in_pattern + i];
            new_word_for_var.push_back(equation_context.scc_solution[atom_on_opposite_side.term][atom_on_opposite_side.index]);
        }
        equation_context.scc_solution[changed_var] = new_word_for_var;

        // Remove atoms of resolved variable that were already in solved_atoms with a higher relative index than the new atom  
        auto it = equation_context.solved_atoms.begin();
        while (it != equation_context.solved_atoms.end()) {
            if (it->term == changed_var && it->index > missing_atom.index)
                it = equation_context.solved_atoms.erase(it);
            else
                ++it;
        }
    }

    bool DecisionProcedure::is_half_full(int position, const AtomicEquationContext& equation_context) {
        // Check if atoms on specific index in atomic equation are in solved_atoms 
        bool is_left_atom = equation_context.solved_atoms.contains(equation_context.left_side[position]);
        bool is_right_atom = equation_context.solved_atoms.contains(equation_context.right_side[position]);
        // Return true if just one of the atomic pair is in solved_atoms
        if((is_left_atom && !is_right_atom) || (!is_left_atom && is_right_atom))
            return true;
        else
            return false;
    }

    void DecisionProcedure::get_side_of_atomic_equation(const Predicate& incl, Predicate::EquationSideType inclusion_side, AtomicEquationContext& equation_context){            
        for (const BasicTerm& term: incl.get_side(inclusion_side)) {
            mata::Word some_shortest_word;
            
            //If random word was already assigned to var than use it to create atoms 
            if(equation_context.scc_solution.contains(term)) {
                some_shortest_word = equation_context.scc_solution[term];
            } 
            else {
                //Else if the term is a variable find a random shortest word
                if(term.is_variable()) {
                    some_shortest_word = solution.aut_ass.at(term)->get_shortest_word().value();
                } 
                // For literal use their name for creating atoms
                else {
                    some_shortest_word = util::get_mata_word_zstring(term.get_name());
                }
                
                //Store newly found word and icrement num_of_atoms
                equation_context.scc_solution[term] = some_shortest_word;
                equation_context.num_of_atoms += some_shortest_word.size();
            }
            
            // Add atoms to correct side of the atomic equation
            for(unsigned relative_idx = 0; relative_idx < some_shortest_word.size(); relative_idx++) {
                Atom atom_to_add(term,relative_idx);
                if (inclusion_side == Predicate::EquationSideType::Left)
                    equation_context.left_side.push_back(atom_to_add);
                else
                    equation_context.right_side.push_back(atom_to_add);
            }
        }
    }

    void DecisionProcedure::get_model_for_cyclic_SCC(const std::vector<int> &scc){
        //Get alphabet used for strace debugging and model updating
        const regex::Alphabet& alph(solution.aut_ass.get_alphabet());
        
        // Empty struct for solving the atomic equation and correct word assigment
        AtomicEquationContext atomic_equation_context;

        // Create atomic equations
        STRACE(str_scc_debug, tout << "Creating atomic equations." << std::endl;);
        for(int incl_idx: scc){

            auto inclusion = std::next(solution.inclusions.begin(), incl_idx);
            get_side_of_atomic_equation(*inclusion, Predicate::EquationSideType::Left, atomic_equation_context);
            get_side_of_atomic_equation(*inclusion, Predicate::EquationSideType::Right, atomic_equation_context);
        }
                

        STRACE(str_scc_debug,
            tout << "Random Assignment for all variables:" << std::endl;
            for(auto const& [term, word] : atomic_equation_context.scc_solution)
            {
                tout << term.get_name() << " - " << alph.get_string_from_mata_word(word) << std::endl;
            }
        
            tout << "Started resolving atomic equations" << std::endl;
        );
        
        // Find correct word assigment for all vars in SCC
        while(atomic_equation_context.solved_atoms.size() < atomic_equation_context.num_of_atoms){            
            // Get leftmost half full atom pair's index
            int left_most_half_full_pos = -1;
            for (int pos = 0; pos < atomic_equation_context.left_side.size(); pos++) {
                if (is_half_full(pos, atomic_equation_context))
                {
                    left_most_half_full_pos = pos;
                    break;
                }
            }
            
            // If there is a half full atom pair (lemma 4)
            if (left_most_half_full_pos != -1) {
                Predicate::EquationSideType missing_side = !atomic_equation_context.solved_atoms.contains(atomic_equation_context.left_side[left_most_half_full_pos])
                                                         ? Predicate::EquationSideType::Left
                                                         : Predicate::EquationSideType::Right;
                Atom add_atom = missing_side == Predicate::EquationSideType::Left
                    ? atomic_equation_context.left_side[left_most_half_full_pos]
                    : atomic_equation_context.right_side[left_most_half_full_pos];
                
                // Update the variable's word by copying from the opposite side, 
                // and remove all atoms of resolved variable with higher index from solved_atoms
                synchronize_word_on_position(left_most_half_full_pos, missing_side, atomic_equation_context);
                
                // Insert the newly resolved atom to solved_atoms
                atomic_equation_context.solved_atoms.insert(add_atom);

            } 
            // If there is no half full pair in the equation (lemma 3)
            else {
                // Add any unresolved atom — consistency is preserved regardless of which atom we pick here
                for (unsigned pos = 0; pos < atomic_equation_context.left_side.size(); pos++) {
                    if (!atomic_equation_context.solved_atoms.contains(atomic_equation_context.left_side[pos])) {
                        atomic_equation_context.solved_atoms.insert(atomic_equation_context.left_side[pos]);
                        break;
                    }
                    if (!atomic_equation_context.solved_atoms.contains(atomic_equation_context.right_side[pos])) {
                        atomic_equation_context.solved_atoms.insert(atomic_equation_context.right_side[pos]);
                        break;
                    }
                }
            }                   
        }

        //Update the model with correct word for each variable 
        for(auto const& [term, word] : atomic_equation_context.scc_solution){
            if(term.is_variable()){
                update_model_and_aut_ass(term, alph.get_string_from_mata_word(word));
            }
        }
    }

    zstring DecisionProcedure::get_model(BasicTerm var, const std::map<BasicTerm,rational>& arith_model) {
        init_model(arith_model);

        if (model_of_var.contains(var)) {
            return model_of_var.at(var);
        }

        STRACE(str_model,
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
                    mata::nfa::Nfa possible_inputs = predicate_with_var_on_right_side.get_transducer()->apply(util::get_mata_word_zstring(output_var_model), 1, true, mata::nft::JumpMode::NoJump).to_nfa_move();
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
                STRACE(str_model_nfa, tout << "NFA for var " << var << " before getting some word:\n" << *nfa;);
                mata::Word accepted_word = nfa->get_word().value();
                return update_model_and_aut_ass(var, alph.get_string_from_mata_word(accepted_word));
            }
        } else {
            UNREACHABLE();
            return zstring();
        }
    }

    std::vector<BasicTerm> DecisionProcedure::get_len_vars_for_model(const BasicTerm& str_var) {
        // we ignore str_var and return all vars needed for initializing model
        std::vector<BasicTerm> needed_vars = conversion_handler.get_arith_vars_needed_for_model();
        for (const BasicTerm& len_var : solution.length_sensitive_vars) {
            if (!len_var.is_literal() && solution.aut_ass.contains(len_var)) {
                needed_vars.push_back(len_var);
            }
        }
        for (const auto& transducer_with_parikh_information : transducers_with_parikh_information) {
            for (const BasicTerm& var : transducer_with_parikh_information.get_all_parikh_vars()) {
                needed_vars.push_back(var);
            }
        }
        return needed_vars;
    }

    void DecisionProcedure::set_initial_variables(const Formula& f, const SolvingState& state) {
        initial_variables = f.get_vars();
        for (const auto& [var, _aut] : state.aut_ass) {
            initial_variables.insert(var);
        }
        for (const auto& var : state.length_sensitive_vars) {
            initial_variables.insert(var);
        }
        for (const TermConversion& conv : state.conversions) {
            initial_variables.insert(conv.string_var);
        }
        for (const auto& incl : inclusions_from_preprocessing) {
            for (const auto& var : incl.get_vars()) {
                initial_variables.insert(var);
            }
        }
    }

} // Namespace smt::noodler.
