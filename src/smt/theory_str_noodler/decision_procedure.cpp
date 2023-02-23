#include <queue>
#include <utility>
#include <algorithm>

#include <mata/nfa-strings.hh>
#include "util.h"
#include "aut_assignment.h"
#include "decision_procedure.h"

namespace smt::noodler {
    std::shared_ptr<GraphNode> SolvingState::make_deep_copy_of_inclusion_graph_only_nodes(std::shared_ptr<GraphNode> processed_node) {
        assert(inclusion_graph->get_nodes().count(processed_node) > 0);
        Graph graph_to_copy = *inclusion_graph;
        graph_to_copy.remove_all_edges();
        assert(graph_to_copy.get_nodes().count(processed_node) > 0);
        std::unordered_map<std::shared_ptr<GraphNode>, std::shared_ptr<GraphNode>> node_mapping;
        inclusion_graph = std::make_shared<Graph>(graph_to_copy.deep_copy(node_mapping));
        std::deque<std::shared_ptr<GraphNode>> new_nodes_to_process;
        while (!nodes_to_process.empty()) {
            new_nodes_to_process.push_back(node_mapping.at(nodes_to_process.front()));
            nodes_to_process.pop_front();
        }
        nodes_to_process = new_nodes_to_process;
        return node_mapping.at(processed_node);
    }

    void SolvingState::substitute_vars(std::unordered_map<BasicTerm, std::vector<BasicTerm>> &substitution_map) {
        std::unordered_set<std::shared_ptr<GraphNode>> deleted_nodes;
        inclusion_graph->substitute_vars(substitution_map, deleted_nodes);

        // remove all deleted_nodes from the nodes_to_process (using remove/erase)
        // TODO: is this correct?? I assume that if we delete copy of a merged node from nodes_to_process, it either does not need to be processed or the merged node will be in nodes_to_process
        auto is_deleted = [&deleted_nodes](std::shared_ptr<GraphNode> node) { return (deleted_nodes.count(node) > 0) ; };
        nodes_to_process.erase(std::remove_if(nodes_to_process.begin(), nodes_to_process.end(), is_deleted), nodes_to_process.end());
    }

    AutAssignment SolvingState::flatten_substition_map() {
        AutAssignment result = aut_ass;
        std::function<std::shared_ptr<Mata::Nfa::Nfa>(const BasicTerm&)> flatten_var;

        flatten_var = [&result, &flatten_var, this](const BasicTerm &var) -> std::shared_ptr<Mata::Nfa::Nfa> {
            if (result.count(var) == 0) {
                std::shared_ptr<Mata::Nfa::Nfa> var_aut = std::make_shared<Mata::Nfa::Nfa>(Mata::Nfa::create_empty_string_nfa());
                for (const auto &subst_var : this->substitution_map.at(var)) {
                    var_aut = std::make_shared<Mata::Nfa::Nfa>(Mata::Nfa::concatenate(*var_aut, *flatten_var(subst_var)));
                }
                result[var] = var_aut;
                return var_aut;
            } else {
                return result[var];
            }
        };
        for (const auto &subst_map_pair : substitution_map) {
            flatten_var(subst_map_pair.first);
        }
        return result;
    }

    DecisionProcedure::DecisionProcedure(
            const Formula &equalities, AutAssignment init_aut_ass,
            const std::unordered_set<BasicTerm>& init_length_sensitive_vars,
            ast_manager& m, seq_util& m_util_s, arith_util& m_util_a
    ) : prep_handler(equalities, init_aut_ass, init_length_sensitive_vars), m{ m }, m_util_s{ m_util_s },
        m_util_a{ m_util_a },
        init_length_sensitive_vars{ init_length_sensitive_vars },
        formula { equalities },
        init_aut_ass{ init_aut_ass } {
    }

    bool DecisionProcedure::compute_next_solution() {

        while (!worklist.empty()) {
            SolvingState element_to_process = std::move(worklist.front());
            worklist.pop_front();

            if (element_to_process.nodes_to_process.empty()) {
                // TODO do some arithmetic shit?
                solution = std::move(element_to_process);
                return true;
            }

            std::shared_ptr<GraphNode> node_to_process = element_to_process.nodes_to_process.front();
            assert(node_to_process != nullptr);
            element_to_process.nodes_to_process.pop_front();

            STRACE("str", tout << "Processing node with inclusion " << node_to_process->get_predicate() <<std::endl;);

            bool is_node_to_process_on_cycle = element_to_process.inclusion_graph->is_on_cycle(node_to_process);

            /** process left side **/
            std::vector<std::shared_ptr<Mata::Nfa::Nfa>> left_side_automata;
            const auto &left_side_vars = node_to_process->get_predicate().get_left_side();
            STRACE("str-nfa", tout << "Left automata:" << std::endl);
            for (const auto &l_var : left_side_vars) {
                left_side_automata.push_back(element_to_process.aut_ass.at(l_var));
                STRACE("str-nfa", left_side_automata.back()->print_to_DOT(tout););
            }
            /** end of left side processing **/


            /** Combine the right side into automata where we concatenate non-length-aware vars next to each other **/
            std::vector<std::shared_ptr<Mata::Nfa::Nfa>> right_side_automata;
            const auto &right_side_vars = node_to_process->get_predicate().get_right_side();
            // each right side automaton corresponds to either concatenation of non-length-aware vars (vector of basic terms) or one lenght-aware var (vector of one basic term)
            std::vector<std::vector<BasicTerm>> right_side_division;
            bool is_there_length_on_right = false;

            if (!right_side_vars.empty()) {
                auto right_var_it = right_side_vars.begin();
                auto right_side_end = right_side_vars.end();

                std::shared_ptr<Mata::Nfa::Nfa> next_aut = element_to_process.aut_ass[*right_var_it];
                std::vector<BasicTerm> next_division{ *right_var_it };
                bool last_was_length = (element_to_process.length_sensitive_vars.count(*right_var_it) > 0);
                is_there_length_on_right = last_was_length;
                ++right_var_it;

                for (; right_var_it != right_side_end; ++right_var_it) {
                    std::shared_ptr<Mata::Nfa::Nfa> right_var_aut = element_to_process.aut_ass.at(*right_var_it);
                    if (element_to_process.length_sensitive_vars.count(*right_var_it) > 0) {
                        // current right_var is length-aware
                        right_side_automata.push_back(next_aut);
                        right_side_division.push_back(next_division);
                        next_aut = right_var_aut;
                        next_division = std::vector<BasicTerm>{ *right_var_it };
                        last_was_length = true;
                        is_there_length_on_right = true;
                    } else {
                        // current right_var is not length-aware
                        if (last_was_length) {
                            right_side_automata.push_back(next_aut);
                            right_side_division.push_back(next_division);
                            next_aut = right_var_aut;
                            next_division = std::vector<BasicTerm>{ *right_var_it };
                        } else {
                            next_aut = std::make_shared<Mata::Nfa::Nfa>(Mata::Nfa::concatenate(*next_aut, *right_var_aut));
                            next_division.push_back(*right_var_it);
                            // TODO probably reduce size here
                        }
                        last_was_length = false;
                    }
                }
                right_side_automata.push_back(next_aut);
                STRACE("str-nfa", tout << "Right automata:" << std::endl);
                STRACE("str-nfa", right_side_automata.back()->print_to_DOT(tout););
                right_side_division.push_back(next_division);
            }
            /** end of right side combining **/

            if (!is_there_length_on_right) {
                // we have no length-aware variables on the right hand side => we need to check if inclusion holds

                std::shared_ptr<Mata::Nfa::Nfa> right_side_automaton;
                if (right_side_vars.empty()) {
                    right_side_automaton = std::make_shared<Mata::Nfa::Nfa>(Mata::Nfa::create_empty_string_nfa());
                } else {
                    assert(right_side_automata.size() == 1);
                    right_side_automaton = right_side_automata[0];
                }

                // TODO probably we should try shortest words, it might work correctly
                if (is_node_to_process_on_cycle // TODO should we not test inclusion if we have node that is not on cycle? because we will not go back to it, so it should make sense to just do noodlification
                    && Mata::Nfa::is_included(element_to_process.aut_ass.get_automaton_concat(left_side_vars), *right_side_automaton)) { // there should be exactly one element in right_side_automata as we do not have length variables
                    // TODO can I push to front? I think I can, and I probably want to, so I can immediately test if it is not sat (if element_to_process.nodes_to_process is empty), or just to get to sat faster
                    worklist.push_front(element_to_process);
                    // we continue as there is no need for noodlification, inclusion already holds
                    continue;
                }
            }

            // we are going to change the automata on the left side (potentially also split some on the right side, but that should not have impact)
            // so we need to add all nodes whose variable assignments are going to change on the right side (i.e. we follow inclusion graph) for processing
            for (const auto &node : element_to_process.inclusion_graph->get_edges_from(node_to_process)) {
                // we push only those nodes which are not already in nodes_to_process
                // if the node_to_process is on cycle, we need to do BFS
                // if it is not on cycle, we can do DFS
                // TODO: can we really do DFS??
                element_to_process.push_unique(node, is_node_to_process_on_cycle);
            }

            /* TODO check here if we have empty elements_to_process, if we do, then every noodle we get should finish and return sat
             * right now if we test sat at the beginning it should work, but it is probably better to immediatly return sat if we have
             * empty elements_to_process, however, we need to remmeber the state of the algorithm, we would need to return back to noodles
             * and process them if z3 realizes that the result is actually not sat (because of lengths)
             */


            
            /**
             * We get noodles where each noodle consists of automata connected with a vector of numbers
             * So for example if we have some noodle and automaton noodle[i].first, then noodle[i].second is a vector, where first element
             * i_l = noodle[i].second[0] tells us that automaton noodle[i].first belongs to the i_l-th left var (i.e. left_side_vars[i_l])
             * and the second element i_r = noodle[i].second[1] tell us that it belongs to the i_r-th division of the right side (i.e. right_side_division[i_r])
             **/
            std::vector<std::vector<std::pair<std::shared_ptr<Mata::Nfa::Nfa>, std::vector<unsigned>>>> noodles;
            if (right_side_vars.empty() || left_side_vars.empty()) {
                assert(!(right_side_vars.empty() && left_side_vars.empty()));
                // as noodlification probably cannot handle situation where we have no automata on one side (representing empty word), we handle it here, by adding one empty noodle
                noodles.push_back({});
            } else {
                noodles = Mata::Strings::SegNfa::noodlify_for_equation(left_side_automata, right_side_automata, false, {{"reduce", "true"}});
            }

            for (const auto &noodle : noodles) {
                SolvingState new_element = element_to_process;
                // we need to make a deep copy, because we will be updating this graph
                // TODO if !is_there_length_on_right we should not copy somehow, if there are no automata accepting only empty word 
                auto new_node_to_process = new_element.make_deep_copy_of_inclusion_graph_only_nodes(node_to_process);

                //remove processed inclusion from the inclusion graph
                new_element.inclusion_graph->remove_node(new_node_to_process); // TODO: is this safe?

                std::vector<std::vector<BasicTerm>> left_side_vars_to_new_vars(left_side_vars.size());
                std::vector<std::vector<BasicTerm>> right_side_divisions_to_new_vars(right_side_division.size());
                for (unsigned i = 0; i < noodle.size(); ++i) {
                    // TODO do not make a new_var if we can replace it with one left or right var (i.e. new_var is exactly left or right var)
                    // TODO also if we can substitute with epsilon, we should do that first? or generally process epsilon substitutions better, in some sort of 'preprocessing'
                    BasicTerm new_var(BasicTermType::Variable, VAR_PREFIX + std::string("_") + std::to_string(noodlification_no) + std::string("_") + std::to_string(i));
                    left_side_vars_to_new_vars[noodle[i].second[0]].push_back(new_var);
                    right_side_divisions_to_new_vars[noodle[i].second[1]].push_back(new_var);
                    new_element.aut_ass[new_var] = noodle[i].first; // we assign the automaton to new_var
                }

                std::unordered_map<BasicTerm, std::vector<BasicTerm>> substitution_map;

                for (unsigned i = 0; i < right_side_division.size(); ++i) {
                    const auto &division = right_side_division[i];
                    if (division.size() == 1 && element_to_process.length_sensitive_vars.count(division[0]) != 0) {
                        // right side is length-aware variable y => we are either substituting or adding new inclusion "new_vars included in y"
                        const BasicTerm &right_var = division[0];
                        if (substitution_map.count(right_var)) {
                            // right_var is already substituted, therefore we add 'new_vars included in right_var' to the inclusion graph
                            const auto &new_inclusion = new_element.inclusion_graph->add_node(right_side_divisions_to_new_vars[i], division);
                            // we also add this inclusion to the worklist, as it represents unification
                            // we push it to the front if we are processing node that is not on the cycle, because it should not get stuck in the cycle then
                            // TODO: is this correct? can we push to the front?
                            new_element.push_unique(new_inclusion, is_node_to_process_on_cycle);
                        } else {
                            // right_var is not substitued by anything yet, we will substitute it
                            substitution_map[right_var] = right_side_divisions_to_new_vars[i];
                            // as right_var wil be substituted in the inclusion graph, we do not need to remember the automaton assignment for it
                            new_element.aut_ass.erase(right_var);
                            // update the length variables
                            // TODO: is this enough to update variables only when substituting?
                            for (const BasicTerm &new_var : right_side_divisions_to_new_vars[i]) {
                                new_element.length_sensitive_vars.insert(new_var);
                            }
                        }

                    } else {
                        // right side is non-length concatenation "y_1...y_n" => we are adding new inclusion "new_vars included in y1...y_n"
                        new_element.inclusion_graph->add_node(right_side_divisions_to_new_vars[i], division);
                        // we do not add the new inclusion to the worklist, because it represents the part of the inclusion that "was not split", i.e. it was processed in FM way
                    }
                }

                for (unsigned i = 0; i < left_side_vars.size(); ++i) {
                    // TODO maybe if !is_there_length_on_right, we should just do intersection and not create new inclusions
                    const BasicTerm &left_var = left_side_vars[i];
                    if (substitution_map.count(left_var)) {
                        // left_var is already substituted, therefore we add 'left_var included in left_side_vars_to_new_vars[i]' to the inclusion graph
                        std::vector<BasicTerm> new_inclusion_left_side{ left_var };
                        const auto &new_inclusion = new_element.inclusion_graph->add_node(new_inclusion_left_side, left_side_vars_to_new_vars[i]);
                        // we also add this inclusion to the worklist, as it represents unification
                        // we push it to the front if we are processing node that is not on the cycle, because it should not get stuck in the cycle then
                        // TODO: is this correct? can we push to the front?
                        new_element.push_unique(new_inclusion, is_node_to_process_on_cycle);
                    } else {
                        // TODO make this function or something, we do the same thing here as for the right side when substituting
                        // left_var is not substitued by anything yet, we will substitute it
                        substitution_map[left_var] = left_side_vars_to_new_vars[i];
                        // as left_var wil be substituted in the inclusion graph, we do not need to remember the automaton assignment for it
                        new_element.aut_ass.erase(left_var);
                        // update the length variables
                        // TODO: is this enough to update variables only when substituting?
                        if (new_element.length_sensitive_vars.count(left_var) > 0) { // if left_var is length-aware => substituted vars should become length-aware
                            for (const BasicTerm &new_var : left_side_vars_to_new_vars[i]) {
                                new_element.length_sensitive_vars.insert(new_var);
                            }
                        }
                    }
                }

                // do substitution in the inclusion graph
                new_element.substitute_vars(substitution_map);

                // update inclusion graph edges
                new_element.inclusion_graph->add_inclusion_graph_edges();

                // update the substitution_map of new_element by the new substitutions
                new_element.substitution_map.merge(substitution_map);

                // TODO should we really push to front when not on cycle?
                if (!is_node_to_process_on_cycle) {
                    worklist.push_front(new_element);
                } else {
                    worklist.push_back(new_element);
                }

                // TODO: should we do something more here??

            }

            ++noodlification_no; // TODO: when to do this increment??
        }

        return false;
    }

    /**
     * @brief Get length constraints of the solution
     *
     * @param variable_map Mapping of BasicTerm variables to the corresponding z3 variables
     * @return expr_ref Length formula describing all solutions
     */
    expr_ref DecisionProcedure::get_lengths(std::map<BasicTerm, expr_ref>& variable_map) {
        AutAssignment ass = this->solution.flatten_substition_map();
        expr_ref lengths(this->m.mk_true(), this->m);

        for(const BasicTerm& var : this->init_length_sensitive_vars) {
            std::set<std::pair<int, int>> aut_constr = Mata::Strings::get_word_lengths(*ass.at(var));

            auto it = variable_map.find(var);
            expr_ref var_expr(this->m);
            if(it != variable_map.end()) { // take the existing variable from the map
                var_expr = it->second;
            } else { // if the variable is not found, it was introduced in the preprocessing -> create a new z3 variable
                var_expr = util::mk_str_var(var.get_name().encode(), this->m, this->m_util_s);
            }
            lengths = this->m.mk_and(lengths, mk_len_aut(var_expr, aut_constr));
        }

        // collect lengths introduced by the preprocessing
        expr_ref prep_formula = util::len_to_expr(
                this->prep_handler.get_len_formula(),
                variable_map,
                this->m, this->m_util_s, this->m_util_a );

        if(!this->m.is_true(prep_formula)) {
            lengths = this->m.mk_and(lengths, prep_formula);
        }

        return lengths;
    }

    /**
     * @brief Creates initial inclusion graph according to the preprocessed instance.
     */
    void DecisionProcedure::init_computation() {
        SolvingState initialWlEl;
        initialWlEl.length_sensitive_vars = this->init_length_sensitive_vars;
        initialWlEl.aut_ass = std::move(this->init_aut_ass);

        if(!initialWlEl.aut_ass.is_sat()) { // TODO: return unsat core
            return;
        }

        if (!this->formula.get_predicates().empty()) {
            // TODO the ordering of nodes_to_process right now is given by how they were added from the splitting graph, should we use something different?
            initialWlEl.inclusion_graph = std::make_shared<Graph>(Graph::create_inclusion_graph(this->formula, initialWlEl.nodes_to_process));
        }

        worklist.push_back(initialWlEl);
    }

    /**
     * @brief Preprocessing.
     */
    void DecisionProcedure::preprocess() {
        // As a first preprocessing operation, convert string literals to fresh variables with automata assignment
        //  representing their string literal.
        conv_str_lits_to_fresh_vars();
        this->prep_handler = FormulaPreprocess(this->formula, this->init_aut_ass, this->init_length_sensitive_vars);

        // So-far just lightweight preprocessing
        this->prep_handler.propagate_variables();
        this->prep_handler.propagate_eps();
        this->prep_handler.remove_regular();
        this->prep_handler.generate_identities();
        this->prep_handler.propagate_variables();
        this->prep_handler.remove_trivial();

        // Refresh the instance
        this->init_aut_ass = this->prep_handler.get_aut_assignment();
        this->init_length_sensitive_vars = this->prep_handler.get_len_variables();
        this->formula = this->prep_handler.get_modified_formula();

        if(this->formula.get_predicates().size() > 0) {
            this->init_aut_ass.reduce(); // reduce all automata in the automata assignment
        }

        STRACE("str", tout << "preprocess-output: " << this->formula.to_string() << "\n" );
    }

    /**
     * @brief Make a length constraint for a single NFA loop, handle
     *
     * @param var variable
     * @param v1 handle
     * @param v2 loop
     * @return expr_ref Length formula
     */
    expr_ref DecisionProcedure::mk_len_aut_constr(const expr_ref& var, int v1, int v2) {
        expr_ref len_x(this->m_util_s.str.mk_length(var), this->m);
        expr_ref k = util::mk_int_var_fresh("k", this->m, this->m_util_s, this->m_util_a);
        expr_ref c1(this->m_util_a.mk_int(v1), this->m);
        expr_ref c2(this->m_util_a.mk_int(v2), this->m);

        if(v2 != 0) {
            expr_ref right(this->m_util_a.mk_add(c1, this->m_util_a.mk_mul(k, c2)), this->m);
            return expr_ref(this->m.mk_eq(len_x, right), this->m);
        }
        return expr_ref(this->m.mk_eq(len_x, c1), this->m);
    }

    /**
     * @brief Make a length formula corresponding to a set of pairs <loop, handle>
     *
     * @param var Variable
     * @param aut_constr Set of pairs <loop, handle>
     * @return expr_ref Length constaint of the automaton
     */
    expr_ref DecisionProcedure::mk_len_aut(const expr_ref& var, std::set<std::pair<int, int>>& aut_constr) {
        expr_ref res(this->m.mk_false(), this->m);
        for(const auto& cns : aut_constr) {
            res = this->m.mk_or(res, mk_len_aut_constr(var, cns.first, cns.second));
        }
        res = expr_ref(this->m.mk_and(res, this->m_util_a.mk_ge(this->m_util_s.str.mk_length(var), this->m_util_a.mk_int(0))), this->m);
        return res;
    }

    void DecisionProcedure::conv_str_lits_to_fresh_vars() {
        constexpr char name_prefix[] = "str_lit_to_var_";
        size_t counter{ 0 };
        for (auto& predicate : formula.get_predicates()) {
            if (predicate.is_eq_or_ineq()) {
                for (auto& term : predicate.get_left_side()) {
                    if (term.is_literal()) { // Handle string literal.
                        BasicTerm fresh_variable{ BasicTermType::Variable, name_prefix + std::to_string(counter)};
                        ++counter;
                        Mata::Nfa::Nfa nfa{ util::create_word_nfa(term.get_name()) };
                        init_aut_ass.emplace(fresh_variable, std::make_shared<Mata::Nfa::Nfa>(std::move(nfa)));
                        term = fresh_variable;
                    }
                }

                for (auto& term : predicate.get_right_side()) {
                    if (term.is_literal()) { // Handle string literal.
                        BasicTerm fresh_variable{ BasicTermType::Variable, name_prefix + std::to_string(counter)};
                        ++counter;
                        Mata::Nfa::Nfa nfa{ util::create_word_nfa(term.get_name()) };
                        init_aut_ass.emplace(fresh_variable, std::make_shared<Mata::Nfa::Nfa>(std::move(nfa)));
                        term = fresh_variable;
                    }
                }
            }
        }
    }
} // Namespace smt::noodler.
