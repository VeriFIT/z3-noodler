#include <queue>
#include <utility>
#include <algorithm>

#include <mata/nfa/strings.hh>

#include "util.h"
#include "aut_assignment.h"
#include "nielsen_decision_procedure.h"

namespace smt::noodler {

    std::pair<LenNode, LenNodePrecision> NielsenDecisionProcedure::get_lengths() {
        STRACE("str", tout << "Nielsen lengths: " << length_formula_for_solution << std::endl;);
        return {std::move(length_formula_for_solution), LenNodePrecision::PRECISE};
    }

    /**
     * @brief Initialize computation.
     */
    void NielsenDecisionProcedure::init_computation() {
        // do nothing for now
    }

    /**
     * @brief Preprocessing.
     */
    lbool NielsenDecisionProcedure::preprocess(PreprocessType opt, const BasicTermEqiv &len_eq_vars) {
        FormulaPreprocessor prep_handler(this->formula, this->init_aut_ass, this->init_length_sensitive_vars, m_params, {});

        // this does not affect the model generation
        prep_handler.separate_eqs();

        // Refresh the instance
        this->init_aut_ass = prep_handler.get_aut_assignment();
        this->init_length_sensitive_vars = prep_handler.get_len_variables();
        this->formula = prep_handler.get_modified_formula();
        this->formula = this->formula.split_literals();

        return l_undef;
    }

    /**
     * @brief Compute next solution. Generate all Nielsen graphs and perform the satifiability checking.
     * 
     * @return True -> satisfiable
     */
    lbool NielsenDecisionProcedure::compute_next_solution() {
        // if the compute_next_solution was called for the first time
        if(this->graphs.size() == 0) {

            // sort predicates from smallest to largest
            std::vector<Predicate>& preds = this->formula.get_predicates();
            std::sort(preds.begin(), preds.end(), [](const Predicate& p1, const Predicate& p2) {
                return NielsenDecisionProcedure::get_predicate_cost(p1) < NielsenDecisionProcedure::get_predicate_cost(p2);
            });

            std::vector<Formula> instances = divide_independent_formula(this->formula);
            // initialize model handler for computing models
            this->model_handler = NielsenModel(instances.size(), this->formula.get_vars());
            size_t graph_counter = 0; 
            for(const Formula& fle : instances) {
                bool is_sat;
                // create Nielsen graph and trim it
                // we may early terminate only if it is not necessary to generate models
                NielsenGraph graph = generate_from_formula(fle, this->init_length_sensitive_vars.empty(), this->m_params.m_produce_models || !this->init_length_sensitive_vars.empty(), is_sat);
                if (!is_sat) {
                    // if some Nielsen graph is unsat --> unsat
                    return l_false;
                }
                graph = graph.trim();
                this->graphs.push_back(graph);

                // create a counter system from the Nielsen graph a condensate it
                CounterSystem counter_system;
                if (!create_counter_system(graph, counter_system)) {
                    return l_undef;
                }

                // generate path from the counter system for potential model generation
                if(this->m_params.m_produce_models) {
                    // it suffices to take arbitrary path by default
                    // if a different path is used for LIA generation, this path is set to model generation as well (later) 
                    std::optional<Path<CounterLabel>> path = counter_system.shortest_path(counter_system.get_init(), trim_formula(fle));
                    if(!path.has_value()) {
                        // the formula is of the form x = x --> we know that x is not length (otherwise we get unknown), we can generate the default model x = eps
                        this->model_handler.set_generator(graph_counter, {});
                    } else {
                        this->model_handler.set_generator(graph_counter, NielsenModel::simple_generator_from_path(path.value()));
                    }
                    graph_counter++;
                }

                // if there are no length variables --> do not construct the counter system
                if(this->init_length_sensitive_vars.size() == 0) {
                    continue;
                }

                condensate_counter_system(counter_system);
                condensate_counter_system(counter_system);
                this->length_paths.push_back({});

                // create paths with self-loops containing the desired length variables
                for(const auto& c : find_self_loops(counter_system)) {
                    Path<CounterLabel> path;
                    if (!get_length_path(counter_system, c, path)) {
                        return l_undef;
                    }
                    this->length_paths[this->length_paths.size() - 1].push_back(path);
                }
            }
        } else {
            // otherwise we are enumerating all length paths
            if(this->length_paths_index >= this->length_paths.size()) {
                // incomplete procedure
                return l_undef;
            }
        }

        // we compute the lengths here already instead of in get_lengths(), so that we can return unknown if there is a problem
        bool length_exists = false;
        if(this->init_length_sensitive_vars.size() == 0) {
            length_formula_for_solution = LenNode(LenFormulaType::TRUE);
        } else {
            std::map<BasicTerm, BasicTerm> actual_var_map{};
            std::vector<LenNode> conjuncts;
            for(size_t i = 0; i < this->length_paths.size(); i++) {
                if(this->length_paths_index >= this->length_paths[i].size()) {
                    continue;
                }
                ModelGenerator mod_gen;
                // generate LIA formula for a path and create a model generator
                if(!length_formula_path(this->length_paths[i][this->length_paths_index], actual_var_map, conjuncts, mod_gen)) {
                    return l_undef;
                }
                // set a new generator according to the length path
                // we replace the original i-th generator
                if(this->m_params.m_produce_models) {
                    this->model_handler.set_generator(i, mod_gen);
                }
            }
            if(!generate_len_connection(actual_var_map, conjuncts)) {
                return l_undef;
            }

            length_formula_for_solution = LenNode(LenFormulaType::AND, conjuncts);
            this->length_paths_index++;
        }

        return l_true;
    }

    /**
     * @brief Divide the formula into a sequence of independent subformulae. A predicate is independent if its variables 
     * are disjoint with the  variables of the remaining predicates. The sequence consists of singleton predicate or the 
     * formula with the remaining ones.
     * 
     * @param formula Formula to be divided
     * @return std::vector<Formula> Sequence of independent subformulae.
     */
    std::vector<Formula> NielsenDecisionProcedure::divide_independent_formula(const Formula& formula) const {
        std::vector<Formula> ret;
        auto preds = formula.get_predicates();
        std::vector<std::set<BasicTerm>> vars_map(preds.size());
        std::set<size_t> rem_ind;
        std::set<size_t> all_ind;

        for(size_t i = 0; i < preds.size(); i++) {
            vars_map[i] = preds[i].get_vars();
        }
        
        for(size_t i = 0; i < preds.size(); i++) {
            all_ind.insert(i);
            bool add = true;
            for(size_t j = 0; j < preds.size(); j++) {
                if(i == j) {
                    continue;
                }
                std::vector<BasicTerm> inter;
                std::set_intersection(vars_map[i].begin(), vars_map[i].end(), 
                    vars_map[j].begin(), vars_map[j].end(), std::back_inserter(inter));
                if(!inter.empty()) {
                    add = false;
                    break;
                }
            }
            if(add) {
                rem_ind.insert(i);
                Formula split;
                split.add_predicate(preds[i]);
                ret.push_back(split);
            }
        }

        Formula remaining;
        std::vector<size_t> diff;
        std::set_difference(all_ind.begin(), all_ind.end(), rem_ind.begin(), 
            rem_ind.end(), std::back_inserter(diff));
        for(size_t ind : diff) {
            remaining.add_predicate(preds[ind]);
        }
        if(diff.size() > 0) {
            ret.push_back(remaining);
        }

        return ret;
    }

    /**
     * @brief Get all possible applicable rewriting rules from a predicate
     * 
     * @param pred Equation
     * @return std::set<NielsenLabel> All possible Nielsen rewriting rules
     */
    std::set<NielsenLabel> NielsenDecisionProcedure::get_rules_from_pred(const Predicate& pred) const {
        Concat left = pred.get_left_side();
        Concat right = pred.get_right_side();
        std::set<NielsenLabel> ret;

        if(left.size() > 0 && left[0].is_variable() && right.size() > 0) {
            ret.insert({left[0], Concat({right[0], left[0]})});
        }
        if(right.size() > 0 && right[0].is_variable() && left.size() > 0) {
            ret.insert({right[0], Concat({left[0], right[0]})});
        }
        if(left.size() > 0 && left[0].is_variable()) {
            ret.insert({left[0], Concat()});
        }
        if(right.size() > 0 && right[0].is_variable()) {
            ret.insert({right[0], Concat()});
        }

        return ret;
    }

    /**
     * @brief Generate Nielsen graph from a formula.
     * 
     * @param init Initial node (formula)
     * @param early_termination Stop generating graph when the final node is reached?
     * @param add_edges Add edges to the Nielsen graph?
     * @param[out] is_sat Contains the Nielsen graph an accepting node?
     * @return NielsenGraph 
     */
    NielsenGraph NielsenDecisionProcedure::generate_from_formula(const Formula& init, bool early_termination, bool add_edges, bool & is_sat) const {
        NielsenGraph graph;
        std::set<Formula> generated;

        // use priority queue to prefer smaller formulae (higher probability to reach a final node)
        auto cmp = [](const auto& pr1, const auto& pr2) { return NielsenDecisionProcedure::get_formula_cost(pr1.second) > NielsenDecisionProcedure::get_formula_cost(pr2.second); };
        // priority queue sorted by the cost of formula
        std::priority_queue<std::pair<size_t, Formula>, std::vector<std::pair<size_t, Formula>>, decltype(cmp)> worklist(cmp);
        worklist.push({0, trim_formula(init)}); 
        graph.set_init(init);

        is_sat = false;
        while(!worklist.empty()) {
            std::pair<size_t, Formula> pr = worklist.top();
            size_t index = pr.first;
            if(generated.find(pr.second) != generated.end()) {
                worklist.pop();
                continue;
            }
            generated.insert(pr.second);
            worklist.pop();

            std::vector<Predicate> predicates = pr.second.get_predicates();
            if(is_pred_unsat(predicates[index]) || is_length_unsat(predicates[index])) {
                continue;
            }
            for(; index < predicates.size(); index++) {
                if(!is_pred_sat(predicates[index])) {
                    break;
                }
            }
            if(index >= predicates.size()) {
                is_sat = true;
                graph.add_fin(pr.second);
                if(early_termination) {
                    return graph;
                }
                continue;
            }

            std::set<NielsenLabel> rules = get_rules_from_pred(predicates[index]);
            for(const auto& label : rules) {
                Formula rpl = trim_formula(pr.second.replace(Concat({label.first}), label.second));
                if(add_edges) {
                    graph.add_edge(pr.second, rpl, label);
                }
                if(generated.find(rpl) == generated.end()) {
                    worklist.push({index, rpl});
                }
            }
        }

        return graph;
    }

    /**
     * @brief Trim formula. Trim each predicate in the formula. A predicate is trimmed 
     * if it does not contain the same BasicTerm at the beginning or end of sides.
     * 
     * @param formula Formula
     * @return Formula Trimmed formula
     */
    Formula NielsenDecisionProcedure::trim_formula(const Formula& formula) const {
        Formula ret;

        for(const Predicate& pred : formula.get_predicates()) {
            auto params = pred.get_params();
            size_t len = std::min(params[0].size(), params[1].size());
            size_t i = 0;
            for(; i < len; i++) {
                if(params[0][i] != params[1][i]) {
                    break;
                }
            }
            int left = params[0].size() - 1, right = params[1].size() - 1;
            for(; left >= 0 && right >= 0 && left > i && right > i; left--, right--) {
                if(params[0][left] != params[1][right]) {
                    break;
                }
            }
            ret.add_predicate(
                Predicate::create_equation(
                    Concat(params[0].begin()+i, params[0].begin() + left + 1),
                    Concat(params[1].begin()+i, params[1].begin() + right + 1)
                ));
        }
        return ret;
    }

    /**
     * @brief Check if a predicate is trivially unsat.
     * 
     * @param pred Predicate
     * @return true -> unsat
     */
    bool NielsenDecisionProcedure::is_pred_unsat(const Predicate& pred) const {
        Concat left = pred.get_left_side();
        Concat right = pred.get_right_side();

        if(left.size() == 0 && right.size() > 0 && right[0].is_literal()) {
            return true;
        }
        if(right.size() == 0 && left.size() > 0 && left[0].is_literal()) {
            return true;
        }
        if(left.size() > 0 && right.size() > 0 && right[0].is_literal() && left[0].is_literal() && right[0] != left[0]) {
            return true;
        }
        if(left.size() > 0 && right.size() > 0 && right[right.size() - 1].is_literal() && left[left.size() - 1].is_literal() && right[right.size() - 1] != left[left.size() - 1]) {
            return true;
        }
        return false;
    }

    bool NielsenDecisionProcedure::create_counter_system(const NielsenGraph& graph, CounterSystem& result) const {
        result = CounterSystem();

        // conversion of a nielsen label to the counter label
        auto conv_fnc = [&](const NielsenLabel& lab, CounterLabel& result) {
            if(lab.second.size() == 0) {
                result = CounterLabel{lab.first, {BasicTerm(BasicTermType::Length, "0")}, lab};
            } else if(lab.second.size() == 2 && lab.second[0].is_literal()) {
                result = CounterLabel{lab.first, {lab.second[1], BasicTerm(BasicTermType::Length, "1")}, lab};
            } else if(lab.second.size() == 2 && lab.second[0].is_variable()) {
                result = CounterLabel{lab.first, {lab.second[1], lab.second[0]}, lab};
            } else {
                std::cout << nielsen_label_to_string(lab) << std::endl;
                return false;
            }
            return true;
        };

        // switch initial and final nodes
        for(const Formula& fin : graph.get_fins()) {
            result.set_init(fin);
        }
        result.add_fin(graph.get_init());
        // reverse edges
        for(const auto& pr : graph.edges) {
            for(const auto& trans : pr.second) {
                CounterLabel target {BasicTerm(BasicTermType::Variable), {}, {BasicTerm(BasicTermType::Variable), {}}}; // randomly initialize the variable, this has no meaning
                if (!conv_fnc(trans.second, target)) { // the value of target is set here
                    return false;
                }
                result.add_edge(trans.first, pr.first, target);
            }
        }
        return true;
    }

    NielsenLabel NielsenDecisionProcedure::join_nielsen_label(const NielsenLabel& l1, const NielsenLabel& l2) {
        Concat symbols(l1.second.begin(), l1.second.end() - 1);
        symbols.insert(symbols.end(), l2.second.begin(), l2.second.end());
        return {l1.first, symbols};
    }

    /**
     * @brief Checks if two counter labels are compatible and if yes, join them. Two counter labels are 
     * compatible if they are of the form x := x + k and x := x + l. The resulting label will be 
     * x := x + (k + l).
     * 
     * @param l1 First counter label
     * @param l2 Second counter label
     * @param res Potential result
     * @return Compatible.
     */
    bool NielsenDecisionProcedure::join_counter_label(const CounterLabel& l1, const CounterLabel& l2, CounterLabel & res) {
        if(l1.left == l2.left && l2.sum.size() == l1.sum.size() && l2.sum.size() == 2 && 
            l1.sum[1].get_type() == BasicTermType::Length && l2.sum[1].get_type() == BasicTermType::Length) {
            
            zstring sm = std::to_string(std::stoi(l1.sum[1].get_name().encode()) + std::stoi(l2.sum[1].get_name().encode()));
            res = CounterLabel{l1.left, {l1.sum[0], BasicTerm(BasicTermType::Length, sm)},join_nielsen_label(l2.nielsen_rule, l1.nielsen_rule)};
            return true;
        }
        return false;
    }

    /**
     * @brief Condensate the counter system.
     * 
     * @param cs Counter system.
     */
    void NielsenDecisionProcedure::condensate_counter_system(CounterSystem& cs) {
        // the reverse counter system
        CounterSystem rev = cs.reverse();
        std::set<std::tuple<Formula, Formula, CounterLabel>> add_edges;

        // find edges of the form fl --> mid --> last with compatible labels.
        // Compatible labels: labels of the form x := x + 1; x := x + 1 which can be 
        // simplified to x := x + 2. This edge is added to fl --> last
        for(const Formula& fl : cs.get_nodes()) {
            for(const auto& pr : cs.edges[fl]) {
                Formula mid = pr.first;
                CounterLabel mid_lab = pr.second;
                auto it_last = cs.edges.find(mid);
                if(it_last != cs.edges.end()) {
                    for(const auto& dest_pr : it_last->second) {
                        Formula last = dest_pr.first;
                        CounterLabel last_lab = dest_pr.second;

                        CounterLabel res{BasicTerm(BasicTermType::Length), {}, {BasicTerm(BasicTermType::Length), {}}};
                        if(join_counter_label(mid_lab, last_lab, res)) {
                            add_edges.insert({fl, last, res});
                        }
                    }
                }
            }
        }

        // add saturated edges
        for(const auto& item : add_edges) {
            cs.add_edge(std::get<0>(item), std::get<1>(item), std::get<2>(item));
        }
    }

    /**
     * @brief Find self-loops suitable for length formula conversion. Self-loops of the form x := x + k,
     * where x is a lenght sensitive variable.
     * 
     * @param cs Counter system
     * @return std::set<Formula> Set of nodes containing a suitable self-loop. 
     */
    std::set<SelfLoop<CounterLabel>> NielsenDecisionProcedure::find_self_loops(const CounterSystem& cs) const {
        std::set<SelfLoop<CounterLabel>> self_loops;
        for(const Formula& node : cs.get_nodes()) {
            auto it = cs.edges.find(node);
            if(it != cs.edges.end()) {
                for(const auto& pr : it->second) {
                    auto lab_it = this->init_length_sensitive_vars.find(pr.second.left);
                    if(pr.first == node && pr.second.sum[1].get_type() == BasicTermType::Length && 
                        lab_it != this->init_length_sensitive_vars.end()) {
                        self_loops.insert({node, pr.second});
                    }
                }
            }
        }
        return self_loops;
    }

    /**
     * @brief Get path containing a node @p sl, which is expected to have a suitable self-loop.
     * 
     * Returns false if such a path does not exists.
     * 
     * @param cs Counter system
     * @param sl Node with a suitable self-loop
     * @param[out] result Shortest path containing the node @p sl.
     * @return bool True if a path was successfully constructed
     */
    bool NielsenDecisionProcedure::get_length_path(const CounterSystem& cs, const SelfLoop<CounterLabel>& sl, Path<CounterLabel>& result) {
        std::optional<Path<CounterLabel>> first_opt = cs.shortest_path(cs.get_init(), sl.first);
        std::optional<Path<CounterLabel>> last_opt = cs.shortest_path(sl.first, *cs.get_fins().begin());

        if(!first_opt.has_value() || !last_opt.has_value()) {
            // no shortest path
            return false;
        }
        result = first_opt.value();
        result.append(last_opt.value());
        result.self_loops.insert(sl);
        return true;
    }

    /**
     * @brief Get length formula for a single counter label. If a variable x is not present in @p in_vars, 
     * an additional formula x = 0 is generated and @p in_vars is updated.
     * 
     * @param lab Counter label
     * @param in_vars Current length variables for each BasicTerm
     * @param out_var Length variable where the result is stored
     * @param[out] conjuncts A conjunction of atoms (LenNode) in a form of a vector.
     * @return bool True iff the formula was successfully created
     */
    bool NielsenDecisionProcedure::get_label_formula(const CounterLabel& lab, std::map<BasicTerm, BasicTerm>& in_vars, BasicTerm& out_var, std::vector<LenNode>& conjuncts) {
        // fresh output variable
        out_var = util::mk_noodler_var_fresh(lab.left.get_name().encode());

        // label of the form x := 0 --> out_var = 0
        if(lab.sum.size() == 1) {
            int val = std::stoi(lab.sum[0].get_name().encode());
            conjuncts.push_back(LenNode(LenFormulaType::EQ, {out_var, val}));
        } else if(!lab.sum[1].is_variable()) { // label of the form x := x + k --> out_var = in_var + k
            int val = std::stoi(lab.sum[1].get_name().encode());
            // variable from the label is not found --> generrate var = 0 first
            if(in_vars.find(lab.left) == in_vars.end()) {
                BasicTerm tmp_var(BasicTermType::Variable);
                if (!get_label_formula(CounterLabel{lab.left, {BasicTerm(BasicTermType::Length, "0")}, lab.nielsen_rule}, in_vars, tmp_var, conjuncts)) {
                    return false;
                }
                in_vars.insert_or_assign(lab.left, tmp_var);
            }
            conjuncts.push_back(LenNode(LenFormulaType::EQ, {out_var, LenNode(LenFormulaType::PLUS, {in_vars.at(lab.left), val})}));
        } else {
            // variable from the label is not found --> generrate var = 0 first
            if(in_vars.find(lab.sum[1]) == in_vars.end()) {
                BasicTerm tmp_var(BasicTermType::Variable);
                if (!get_label_formula(CounterLabel{lab.sum[1], {BasicTerm(BasicTermType::Length, "0")}, lab.nielsen_rule}, in_vars, tmp_var, conjuncts)) {
                    return false;
                }
                in_vars.insert_or_assign(lab.sum[1], tmp_var);
            }
            conjuncts.push_back(LenNode(LenFormulaType::EQ, {out_var, LenNode(LenFormulaType::PLUS, {in_vars.at(lab.left), in_vars.at(lab.sum[1])})}));
        }

        return true;
    }

    /**
     * @brief Get length formula for a label occurring in the self-loop
     * 
     * @param lab Counter label in self-loop
     * @param in_vars Current length variables for each BasicTerm
     * @param out_var Length variable where the result is stored
     * @param[out] conjuncts A conjunction of atoms (LenNode) in a form of a vector.
     * @return bool True iff the formula was successfully created
     */
    bool NielsenDecisionProcedure::get_label_sl_formula(const CounterLabel& lab, const std::map<BasicTerm, BasicTerm>& in_vars, BasicTerm& out_var, std::vector<LenNode>& conjuncts) {
        out_var = util::mk_noodler_var_fresh(lab.left.get_name().encode());

        if(lab.sum.size() == 1) {
            // nielsen: incomplete
            return false;
        } else if(!lab.sum[1].is_variable()) { // label of the form x := x + k --> out_var = in_var + k
            int val = std::stoi(lab.sum[1].get_name().encode());
            // fresh variable j
            BasicTerm fresh = util::mk_noodler_var_fresh("j");
            // x1 = x0 + j*k
            conjuncts.push_back(LenNode(LenFormulaType::EQ, {out_var, LenNode(LenFormulaType::PLUS, {in_vars.at(lab.left), LenNode(LenFormulaType::TIMES, {fresh, val})})}));
            // 0 <= j
            conjuncts.push_back(LenNode(LenFormulaType::LEQ, {0, fresh}));
            return true;
        } else {
            // nielsen: incomplete
            return false;
        }
    }

    /**
     * @brief Get length formula for a path with self-loops.
     * 
     * @param path Part of the counter system contining only self-loops.
     * @param actual_var_map Var map assigning temporary int variables to the original string variables
     * @param[out] conjuncts A conjunction of atoms (LenNode) in a form of a vector.
     * @param[out] model_path Model generator obtained from @p path allowing to generate a model.
     * @return bool True iff the formula was successfully created
     */
    bool NielsenDecisionProcedure::length_formula_path(const Path<CounterLabel>& path, std::map<BasicTerm, BasicTerm>& actual_var_map, std::vector<LenNode>& conjuncts, ModelGenerator& model_path) {
        // path of length 0 = true
        if(path.labels.size() == 0) {
            return true;
        }

        // there is less edges than vertices; the first one has not self-loop (the rule is of the form x := 0)
        for(size_t i = 1; i < path.nodes.size(); i++) {
            auto it = path.self_loops.find(path.nodes[i]);
            CounterLabel lab = path.labels[i-1];

            BasicTerm out_var(BasicTermType::Variable);
            if (!get_label_formula(lab, actual_var_map, out_var, conjuncts)) {
                return false;
            }
            actual_var_map.insert_or_assign(lab.left, out_var);
            // add nielsen rule to the model generator
            model_path.push_back({ lab.nielsen_rule, BasicTerm(BasicTermType::Length) });

            // there is a self-loop
            if(it != path.self_loops.end()) {
                BasicTerm sl_var(BasicTermType::Variable);
                if (!get_label_sl_formula(it->second, actual_var_map, sl_var, conjuncts)) {
                    return false;
                }
                // assume that last conjunct is of the form 0 <= fresh, where fresh is a variable counting number of self-loop iterations
                model_path.push_back({ it->second.nielsen_rule, conjuncts.back().succ[1].atom_val });
                actual_var_map.insert_or_assign(it->second.left, sl_var);
            } 
        }

        return true;
    }

    /**
     * @brief Generate connection of temporary int variables with the original string lengths terms. 
     * For instance x!1 = str.len(x) where x!1 is temporary int variable for x in @p actual_var_map.
     * 
     * @param actual_var_map Actual var map of temporary int variables.
     * @param[out] conjuncts A conjunction of atoms (LenNode) in a form of a vector.
     * @return bool True iff the formula was successfully created
     */
    bool NielsenDecisionProcedure::generate_len_connection(const std::map<BasicTerm, BasicTerm>& actual_var_map, std::vector<LenNode>& conjuncts) {
        // map the original string variable to their lengths.
        // i.e., str.len(x) = x_n (x_n is the last length variable of x)
        for(const BasicTerm& lterm : this->init_length_sensitive_vars) {
            auto it = actual_var_map.find(lterm);
            if(it == actual_var_map.end()) {
                // nielsen: incomplete procedure
                return false;
            }
            BasicTerm prev_var = it->second;
            conjuncts.push_back(LenNode(LenFormulaType::EQ, {lterm, prev_var}));
        }
        return true;
    }

    bool NielsenDecisionProcedure::is_length_unsat(const Predicate& pred) {
        std::map<BasicTerm, unsigned> occurLeft = pred.variable_count(Predicate::EquationSideType::Left);
        std::map<BasicTerm, unsigned> occurRight = pred.variable_count(Predicate::EquationSideType::Right);
        BasicTerm litTerm(BasicTermType::Literal, "");

        bool allLeft = true;
        bool allRight = true;
        for(const auto& t : pred.get_vars()) {
            if(occurLeft[t] > occurRight[t]) allLeft = false;
            if(occurLeft[t] < occurRight[t]) allRight = false;
        }

        if(allLeft && occurLeft[litTerm] < occurRight[litTerm]) {
            return true;
        }
        if(allRight && occurRight[litTerm] < occurLeft[litTerm]) {
            return true;
        }

        return false;
    }

    zstring NielsenDecisionProcedure::get_model(BasicTerm var, const std::map<BasicTerm,rational>& arith_model) {
        if(!this->model_handler.is_initialized()) {
            this->model_handler.compute_model(arith_model);
        }
        return this->model_handler.get_var_model(var);
    }

    std::vector<BasicTerm> NielsenDecisionProcedure::get_len_vars_for_model(const BasicTerm& str_var) {
        return this->model_handler.get_len_vars_for_model(str_var);
    }

    // ----------------------------------------------------------------------------------------------------------------------------------------------------

    /**
     * @brief Create a simple model generator from the path in a counter system. Simple generator contains NO loop iterations. 
     * Basically it mimics model obtained from rules on transitions on the path. Used to generate models from Nielsen graphs with no
     * length-aware variables (there we need only arbitrary path in the graph to get a valid model).
     * 
     * @param path Path in a counter system.
     * @return ModelGenerator Model generator of path
     */
    ModelGenerator NielsenModel::simple_generator_from_path(const Path<CounterLabel>& path) {
        ModelGenerator gen {};
        for(size_t i = 1; i < path.nodes.size(); i++) {
            CounterLabel lab = path.labels[i-1];
            // add nielsen rule to the model generator
            gen.push_back({ lab.nielsen_rule, BasicTerm(BasicTermType::Length) });
        }
        return gen;
    }

    void NielsenModel::initialize_model() {
        for(const BasicTerm& var : this->vars) {
            // set epsilon to each variable
            this->model[var] = "";
        }
    }

    /**
     * @brief Generate assignments of variables generated by @p generator. It applies rules of the generator and creates a string model. 
     * If there is a self-loop we repeat the self-loop by the number of times given by the integer model of the loop variable. 
     * The assignments are stored in this->model.
     * 
     * @param generator Model generator
     * @param arith_model LIA assignment of variables
     */
    void NielsenModel::generate_submodel(const ModelGenerator& generator, const std::map<BasicTerm,rational>& arith_model) {
        // assumed to be called after initialize_model()
        for(const ModelLabel& model_label : generator) {
            // we are processing rule x -> eps; all variables are already set to eps
            if(model_label.rule.second.size() == 0) {
                continue;
            }
            // rules are of the form x -> alpha x
            Concat lit_concat(model_label.rule.second.begin(), model_label.rule.second.end() - 1);
            // rule is of the form x -> y x
            if(lit_concat[0].is_variable()) {
                this->model[model_label.rule.first] = this->model[lit_concat[0]] + this->model[model_label.rule.first];
            } else {
                // rule is of the form x -> str x (there might be a repetition variable)
                zstring str_concat = "";
                for(const BasicTerm& bt : lit_concat) {
                    str_concat = str_concat + bt.get_name();
                }
                // repetite the string
                if(model_label.repetition_var.is_variable()) {
                    rational repetitions = arith_model.at(model_label.repetition_var);
                    zstring base = str_concat;
                    str_concat = "";
                    for(rational i = rational(0); i < repetitions; i++) {
                        str_concat = str_concat + base;
                    }
                }
                this->model[model_label.rule.first] = str_concat + this->model[model_label.rule.first];
            }
        }
    }

    void NielsenModel::compute_model(const std::map<BasicTerm,rational>& arith_model) {
        initialize_model();
        for(const ModelGenerator& gen : this->graph_generators) {
            generate_submodel(gen, arith_model);
        }
    }

    std::vector<BasicTerm> NielsenModel::get_len_vars_for_model(const BasicTerm& str_var) {
        std::vector<BasicTerm> needed_vars{};
        // needed_vars.push_back(str_var);
        for(const ModelGenerator& gen : this->graph_generators) {
            for(const ModelLabel& model_label : gen) {
                needed_vars.push_back(model_label.rule.first);
                if(model_label.repetition_var.is_variable()) {
                    needed_vars.push_back(model_label.repetition_var);
                }
                for(const BasicTerm& bt : model_label.rule.second) {
                    if(bt.is_variable()) {
                        needed_vars.push_back(bt);
                    }
                }
            }
        }
        return needed_vars;
    }

} // Namespace smt::noodler.
