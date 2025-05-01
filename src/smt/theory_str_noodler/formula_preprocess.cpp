#include "formula_preprocess.h"
#include "util.h"

namespace smt::noodler {

    FormulaVar::FormulaVar(const Formula& conj) : allpreds(), input_size(0) {
        const std::vector<Predicate>& preds = conj.get_predicates();
        for(size_t i = 0; i < preds.size(); i++) {
            // we skip equations of the form X = X
            if(preds[i].is_equation() && preds[i].get_left_side() == preds[i].get_right_side()) {
                continue;
            }
            if(this->allpreds.find(preds[i]) == this->allpreds.end()) {
                this->predicates[i] = preds[i];
                this->allpreds.insert(preds[i]);
                this->update_varmap(preds[i], i);
                this->max_index = i;
                this->input_size++;
            }
        }
    }

    /**
     * @brief Update the structure collecting information about variable occurrence. The structure contains variables as
     * [var] = { (var;eq_index;position) } s.t. position is negative if it is on the left side (numbering from 1).
     *
     * @param pred Equation whose variables should be stored
     * @param index Index of the given equation @p pred.
     */
    void FormulaVar::update_varmap(const Predicate& pred, size_t index) {
        for(const VarNode& vr : get_var_positions(pred, index, true)) {
            VarMap::iterator iter = this->varmap.find(vr.term);
            if(iter != this->varmap.end()) {
                iter->second.insert(vr);
            } else {
                this->varmap[vr.term] = std::set<VarNode>({vr});
            }
        }
    }

    /**
     * @brief Get VarNode (structure representing variable position in the equation) for each
     * variable in the equation @p pred.
     *
     * @param pred Equation
     * @param index Index of the equation @p pred
     * @param incl_lit Include positions of literals
     * @return std::set<VarNode> Set if VarNodes for each occurrence of a variable.
     */
    std::set<VarNode> FormulaVar::get_var_positions(const Predicate& pred, size_t index, bool incl_lit) const {
        std::set<VarNode> ret;
        int mult = -1;
        for(const std::vector<BasicTerm>& side : pred.get_params()) {
            update_var_positions_side(side, ret, index, incl_lit, mult);
            mult *= -1;
        }

        return ret;
    }

    /**
     * @brief Update BasicTerm positions in the concatenation
     *
     * @param side Concatenation of BasicTerms
     * @param[out] res Set of positions (VarNodes)
     * @param index Index of the equation the @p side belongs to
     * @param incl_lit Include literals or just take variables?
     * @param mult Multiplicative constant of each position (used to distinguish between left (negative positions) and right side of an equation).
     */
    void FormulaVar::update_var_positions_side(const std::vector<BasicTerm>& side, std::set<VarNode>& res, size_t index, bool incl_lit, int mult) const {
        for(size_t i = 0; i < side.size(); i++) {
            if(incl_lit || side[i].is_variable()) {
                VarNode new_item = { side[i], index, mult*int(i+1) };
                    res.insert(new_item);
                }
            }
    }

    /**
     * @brief String representation of FormulaVar.
     *
     * @return String representation
     */
    std::string FormulaVar::to_string() const {
        std::string ret;
        for(const auto& item : this->predicates) {
            ret += std::to_string(item.first) + ": " + item.second.to_string() + "\n";
        }
        for(const auto& item : this->varmap) {
            std::string st;
            if(!item.second.empty()) {
                st = item.second.begin()->to_string();
                std::for_each(std::next(item.second.begin()), item.second.end(), [&st] (const VarNode& val) {
                    st.append(", ").append(val.to_string());
                });
            }
            ret += item.first.to_string() + ": {" + st + "}\n";
        }
        return ret;
    }

    /**
     * @brief Do all given variables occur at most once in the formula?
     *
     * @param items Set of variables to be checked.
     * @return true All variables have unique occurrence.
     */
    bool FormulaVar::single_occurr(const std::set<BasicTerm>& items) const {
        for(const BasicTerm& t : items) {
            if(t.get_type() != BasicTermType::Variable)
                continue;
            assert(t.get_type() == BasicTermType::Variable);
            if(this->varmap.at(t).size() > 1) {
                return false;
            }
        }
        return true;
    }

    /**
     * @brief Is the given predicate @p p regular? If so, set @p out to the form that
     * a single variable is on the left side.
     *
     * @param p predicate to be checked (works for equalities only).
     * @param[out] out Adjusted form of the predicate s.t. |L| = 1
     * @return Is regular?
     */
    bool FormulaVar::is_side_regular(const Predicate& p, Predicate& out) const {
        std::vector<BasicTerm> side;

        if(!p.is_equation()) {
            return false;
        }

        if(p.get_left_side().size() == 1 && single_occurr(p.get_side_vars(Predicate::EquationSideType::Right))) {
            out = p;
            return true;
        } else if (p.get_right_side().size() == 1 && single_occurr(p.get_side_vars(Predicate::EquationSideType::Left))) {
            out = p.get_switched_sides_predicate();
            return true;
        }

        return false;
    }

    /**
     * @brief Get all regular predicates from the formula (regular predicates are defined in remove_regular) with
     * an additional condition that all predicates are switched to the form X = X_1...X_n (the single variable is
     * on the left).
     *
     * @param[out] out Vector of predicates with the corresponding index in the map predicates.
     */
    void FormulaVar::get_side_regulars(std::vector<std::pair<size_t, Predicate>>& out) const {
        for(const auto& item : this->predicates) {
            Predicate regular;
            if(is_side_regular(item.second, regular))
                out.push_back({item.first, regular});
        }
    }

    /**
     * @brief Get simple equations. Simple equation is of the form X = Y where |X| = |Y| = 1.
     *
     * @param[out] out Vector of simple equations with the corresponding index in the map predicates
     */
    void FormulaVar::get_simple_eqs(std::vector<std::pair<size_t, Predicate>>& out) const {
        for(const auto& item : this->predicates) {
            if(is_simple_eq(item.second))
                out.push_back({item.first, item.second});
        }
    }

    /**
     * @brief Clean occurrences of variables that have empty set of occurrences from varmap.
     * In other words remove items from varmap s.t. (x, {}).
     */
    void FormulaVar::clean_varmap() {
        remove_if(this->varmap, [](const auto& n) { return n.second.size() == 0; });
    };

    /**
     * @brief Remove predicate from the formula. Updates the variable map (if the variable is no further present in
     * the system, it is not removed, only the set of occurrences is set to {}).
     *
     * @param index Index of the predicate to be removed.
     */
    void FormulaVar::remove_predicate(size_t index) {
        std::set<BasicTerm> items = this->predicates[index].get_set();

        const auto& filter = [&index](const VarNode& n) { return n.pred_index == index; };
        for(const BasicTerm& v : items) {
            std::set<VarNode>& occurr = this->varmap[v];
            remove_if(occurr, filter);
        }
        this->allpreds.erase(this->predicates[index]);
        this->predicates.erase(index);
    }

    /**
     * @brief Add predicate to the formula (with updating the variable map).
     *
     * @param pred New predicate
     * @param index Index of the new predicate (if set to -1, first higher index than top is chosen)
     */
    int FormulaVar::add_predicate(const Predicate& pred, int index) {
        auto it = this->allpreds.find(pred);
        if(it != this->allpreds.end()) {
            for(const auto& pr : this->predicates) { // WARNING: ineffective; needs to iterate over all predicates
                if(pr.second == pred)
                    return pr.first;
            }
            assert(false);
        }
        if(index == -1) {
            assert(this->predicates.find(index) == this->predicates.end()); // check if the position is free
            this->max_index++;
            index = int(this->max_index);
        } else {
            assert(index >= 0);
            this->max_index = std::max(this->max_index, size_t(index));
        }

        this->predicates[index] = pred;
        this->allpreds.insert(pred);
        update_varmap(pred, size_t(index));
        return index;
    }

    /**
     * @brief Add a set of new predicates.
     *
     * @param preds Set of new predicates to be added
     */
    void FormulaVar::add_predicates(const std::set<Predicate>& preds) {
        for(const Predicate& p : preds) {
            add_predicate(p);
        }
    }

    /**
     * @brief Replace @p find in the formula (in all predicates).
     *
     * @param find Find
     * @param replace Replace
     */
    void FormulaVar::replace(const Concat& find, const Concat& replace) {
        std::vector<std::pair<size_t, Predicate>> replace_map;
        for(const auto& pr : this->predicates) {
            Predicate rpl;
            if(pr.second.replace(find, replace, rpl)) { // changed, result is stored in rpl
                assert(rpl != pr.second);
                replace_map.push_back({pr.first, std::move(rpl)});
            }
        }
        for(const auto& pr : replace_map) {
            remove_predicate(pr.first);
            add_predicate(pr.second, pr.first);
        }
    }

    /**
     * @brief Remove equations with both sides empty.
     */
    void FormulaVar::clean_predicates() {
        std::vector<size_t> rem_ids;
        for(const auto& pr : this->predicates) {
            if(!pr.second.is_equation())
                continue;
            if(pr.second.get_left_side().size() == 0 && pr.second.get_right_side().size() == 0)
                rem_ids.push_back(pr.first);
        }
        for(size_t id : rem_ids) {
            remove_predicate(id);
        }
    };

    /**
     * @brief Update automata assignment of @p var. If var exists in the aut assignment, we set
     * L(var) = L(var) \cap L(upd). Otherwise we set L(var) = L(upd).
     *
     * @param var Basic term to be updated
     * @param upd Concatenation of terms for updating @p var.
     */
    void FormulaPreprocessor::update_reg_constr(const BasicTerm& var, const std::vector<BasicTerm>& upd) {
        mata::nfa::Nfa concat = this->aut_ass.get_automaton_concat(upd);
        auto iter = this->aut_ass.find(var);
        if(iter != this->aut_ass.end()) {
            mata::nfa::Nfa inters = mata::nfa::intersection(*(iter->second), concat);
            inters.trim();
            if(this->m_params.m_preprocess_red) {
                this->aut_ass[var] = std::make_shared<mata::nfa::Nfa>(mata::nfa::reduce(inters));
            } else {
                this->aut_ass[var] = std::make_shared<mata::nfa::Nfa>(inters);
            }     
        } else {
            this->aut_ass[var] = std::make_shared<mata::nfa::Nfa>(concat);
        }
    }

    /**
     * @brief Iteratively remove regular predicates.
     * 
     * A regular predicate is of the form X = X_1 X_2 ... X_n where X_1 ... X_n does not occurr elsewhere in the system.
     * Formally, L = R is regular if |L| = 1 and each variable from Vars(R) has a single occurrence in the system only.
     * Regular predicates can be removed from the system provided A(X) = A(X) \cap A(X_1).A(X_2)...A(X_n) where A(X)
     * is the automaton assigned to variable X.
     */
    void FormulaPreprocessor::remove_regular() {
        STRACE("str-prep", tout << "Preprocessing step - remove_regular\n";);
        std::vector<std::pair<size_t, Predicate>> regs;
        this->formula.get_side_regulars(regs);
        std::deque<std::pair<size_t, Predicate>> worklist(regs.begin(), regs.end());
        // keeps the ids of removed equations
        std::set<size_t> removed;

        while(!worklist.empty()) {
            std::pair<size_t, Predicate> pr = worklist.front();
            worklist.pop_front();

            if (removed.contains(pr.first)) continue; // if the equation was already removed, we do not remove it again

            STRACE("str-prep-remove_regular", tout << "Remove regular:" << pr.second << std::endl;);

            assert(pr.second.get_left_side().size() == 1);

            // if right side contains multiple len vars we must do splitting => cannot remove (we can remove if we have only one length var with possibly literals)
            bool is_right_side_len = !set_disjoint(this->len_variables, pr.second.get_side_vars(Predicate::EquationSideType::Right));
            if(is_right_side_len && pr.second.get_side_vars(Predicate::EquationSideType::Right).size() > 1) {
                continue;
            }

            // if right side contains conversion variable, then we can only handle the case X = Y, i.e., we have only one var on the right side AND there are NO literals (othewise we need to do proper splitting)
            // note that if this is true, then Y is also len var and is_right_side_len is true
            bool is_right_side_conv = !set_disjoint(this->conversion_vars, pr.second.get_side_vars(Predicate::EquationSideType::Right));
            if(is_right_side_conv && pr.second.get_right_side().size() > 1) {
                continue;
            }

            BasicTerm left_var = pr.second.get_left_side()[0];
            update_reg_constr(left_var, pr.second.get_right_side());

            if(is_right_side_len) {
                // In the situation where we have X = Y (with possibly some literals around) and Y is length
                // we propagate the lengthness of right side variable to the left side
                this->len_variables.insert(left_var);
                // and add len constraint |X| = |Y|
                this->add_to_len_formula(pr.second.get_formula_eq());
            }

            if(is_right_side_conv) {
                // if we also have that Y is conversion var, then there cannot be any literals around
                // and we can add Y -> X to subst map (+ propagate that X is also conversion var)
                this->conversion_vars.insert(left_var);
                this->substitution_map[pr.second.get_right_side()[0]] = {left_var};
            } else {
                // otherwise we do not need to put anything in substitution map and we just need to remember the inclusion for model generation
                removed_inclusions_for_model.push_back(pr.second);
            }

            this->formula.remove_predicate(pr.first);
            removed.insert(pr.first);
            STRACE("str-prep-remove_regular", tout << "removed" << std::endl;);

            // check if by removing the regular equation, some other equations did not become regular
            // we only need to check this for left_var, as the variables from the right side do not occur
            // in the formula anymore (they occured only in pr)
            std::set<VarNode> occurrs = this->formula.get_var_occurr(left_var);
            if(occurrs.size() == 1) {
                Predicate reg_pred;
                if(this->formula.is_side_regular(this->formula.get_predicate(occurrs.begin()->pred_index), reg_pred)) {
                    worklist.emplace_back(occurrs.begin()->pred_index, reg_pred);
                    // update dependency
                    map_set_insert(this->dependency, occurrs.begin()->pred_index, pr.first);
                }
            }
        }
        STRACE("str-prep", tout << print_info(is_trace_enabled("str-nfa")));
    }

    /**
     * @brief Propagate variables. Propagate all equations of the form X=Y
     * (find all Y in the formula and replace with X).
     */
    void FormulaPreprocessor::propagate_variables() {
        STRACE("str-prep", tout << "Preprocessing step - propagate_variables\n";);
        std::vector<std::pair<size_t, Predicate>> regs;
        this->formula.get_simple_eqs(regs);
        std::deque<size_t> worklist;

        std::transform(regs.begin(), regs.end(), std::back_inserter(worklist),
            [](auto const& pair){ return pair.first; });

        while(!worklist.empty()) {
            size_t index = worklist.front();
            worklist.pop_front();
            if(this->formula.get_predicates().find(index) == this->formula.get_predicates().end()) {
                continue;
            }
            Predicate eq = this->formula.get_predicate(index);
            if(eq.get_left_side() == eq.get_right_side()) {
                this->formula.remove_predicate(index);
                continue;
            }

            if(!eq.get_left_side()[0].is_variable()) {
                eq = eq.get_switched_sides_predicate();
            }
            if(!eq.get_left_side()[0].is_variable()) {
                continue;
            }
            /// if X = lit it is better to keep only lit
            if(!eq.get_right_side()[0].is_variable()) {
                BasicTerm v_left = eq.get_left_side()[0]; // X
                update_reg_constr(v_left, eq.get_right_side());
                this->formula.replace(eq.get_left_side(), eq.get_right_side());
                this->formula.remove_predicate(index);
                this->add_to_len_formula(eq.get_formula_eq());
                substitution_map[v_left] = {eq.get_right_side()[0]};
                continue;
            }

            assert(eq.get_left_side().size() == 1 && eq.get_right_side().size() == 1);
            BasicTerm v_left = eq.get_left_side()[0]; // X
            BasicTerm v_right = eq.get_right_side()[0]; // Y
            update_reg_constr(v_left, eq.get_right_side()); // L(X) = L(X) cap L(Y)
            this->add_to_len_formula(eq.get_formula_eq()); // add len constraint |X| = |Y|
            // propagate len variables: if Y is in len_variables, include also X
            if(this->len_variables.find(v_right) != this->len_variables.end()) {
                this->len_variables.insert(v_left);
            }
            // propagate conv variables
            if(this->conversion_vars.find(v_right) != this->conversion_vars.end()) {
                this->conversion_vars.insert(v_left);
            }

            this->formula.replace(eq.get_right_side(), eq.get_left_side()); // find Y, replace for X
            substitution_map[v_right] = {v_left}; // subst_map[Y] = X (the length constraint |X| = |Y| is already there)
            this->formula.remove_predicate(index);

            // update dependencies (overapproximation). Each remaining predicat depends on the removed one.
            for(const auto& pr : this->formula.get_predicates()) {
                map_set_insert(this->dependency, pr.first, index);
            }
        }

        // Not true: you can have equation of two, literals which is not removed 
        //assert(!this->formula.contains_simple_eqs());

        STRACE("str-prep", tout << print_info(is_trace_enabled("str-nfa")));
    }

    /**
     * @brief Get symmetrical difference of occurrences of BasicTerms within two concatenations. For instance for X.Y.X and X.Y.W.Z
     * it returns ({{X,3}}, {{W,3}, {Z,4}}). It includes both variables and literals.
     *
     * @param cat1 First concatenation
     * @param cat2 Second concatenation
     * @return Symmetrical difference
     */
    VarNodeSymDiff FormulaPreprocessor::get_eq_sym_diff(const Concat& cat1, const Concat& cat2) const {
        std::set<VarNode> p1, p2;
        this->formula.update_var_positions_side(cat1, p1, 0, true); // include positions of literals, set equation index to 0
        this->formula.update_var_positions_side(cat2, p2, 0, true);
        return {set_difference(p1, p2), set_difference(p2, p1)};
    }

    /**
     * @brief Propagate new equations having the regular shape. (for generate_identities).
     * Creates new equations of the form X = Y1 Y2 Y3...
     * 
     * @param diff1 First occurrence difference
     * @param diff2 Second occurrence difference
     * @param new_pred[out] Newly created equation
     * @return True -> it is possible to create a new equation
     */
    bool FormulaPreprocessor::propagate_regular_eqs(const std::set<VarNode>& diff1, const std::set<VarNode>& diff2, Predicate& new_pred) const {
        VarNode val1 = *diff1.begin();
        std::set<size_t> pos1, pos2;
        std::map<size_t, BasicTerm> sorted_map;
        for(size_t i = 0; i < diff2.size(); i++) pos1.insert(i + val1.position);
        for(const auto& t : diff2) {
            pos2.insert(t.position);
            sorted_map.insert({t.position, t.term});
        } 
        if(pos1 == pos2) {
            Concat right;
            for(const auto& k : sorted_map) { // in the order of their positions
                right.push_back(k.second);
            }
            new_pred = Predicate::create_equation({val1.term}, right);
            return true;
        }
        return false;
    }

    /**
     * @brief Check whether symmetric difference of term occurrences is suitable for generating identities. The
     * symmetric difference contains different BasicTerms that are on the different positions in the contatenations. If so,
     * set @p new_pred with the new predicate that was generated from the difference.
     *
     * @param diff Symmetric difference of two equivalent terms (concatenation)
     * @param[out] new_pred Newly created identity
     * @return Is it suitable for gen identity (was some identity created?)
     */
    bool FormulaPreprocessor::generate_identities_suit(const VarNodeSymDiff& diff, Predicate& new_pred) const {
        if(diff.first.size() == 1 && diff.second.size() == 1) {
            VarNode val1 = *diff.first.begin();
            VarNode val2 = *diff.second.begin();
            if(val1.position == val2.position) {
                new_pred = Predicate::create_equation({val1.term}, {val2.term});
                return true;
            }
        } else if(diff.first.size() == 1) {
            return propagate_regular_eqs(diff.first, diff.second, new_pred);
        } else if(diff.second.size() == 1) {
            return propagate_regular_eqs(diff.second, diff.first, new_pred);
        }
        /// TODO: allow to generate X = eps
        return false;
    }

    /**
     * @brief Generate indentities. It covers two cases (a) X1 X X2 = X1 Y X2 => X = Y
     * (b) X1 X X2 = Z and Z = X1 Y X2 => X = Y. Where each term can be both literal and variable.
     */
    void FormulaPreprocessor::generate_identities() {
        STRACE("str-prep", tout << "Preprocessing step - generate_identities\n";);
        std::set<std::pair<size_t, Predicate>> new_preds;
        std::set<size_t> rem_ids;
        size_t index = this->formula.get_max_index() + 1;

        for(const auto& pr1 : this->formula.get_predicates()) {
            if(!pr1.second.is_equation())
                continue;
            for(const auto& pr2 : this->formula.get_predicates()) {
                if(!pr2.second.is_equation())
                    continue;
                if(pr1.first > pr2.first)
                    continue;

                VarNodeSymDiff diff;
                if(pr1.first == pr2.first) { // two equations are the same
                    diff = get_eq_sym_diff(pr1.second.get_left_side(), pr1.second.get_right_side());
                // L1 = R1 and L2 = R2 and L1 = L2 => R1 = R2
                } else if(pr1.second.get_left_side() == pr2.second.get_left_side()) {
                    diff = get_eq_sym_diff(pr1.second.get_right_side(), pr2.second.get_right_side());
                // L1 = R1 and L2 = R2 and L1 = R2 => R1 = L2
                } else if(pr1.second.get_left_side() == pr2.second.get_right_side()) {
                    diff = get_eq_sym_diff(pr1.second.get_right_side(), pr2.second.get_left_side());
                // L1 = R1 and L2 = R2 and R1 = L2 => L2 = R1
                } else if(pr1.second.get_right_side() == pr2.second.get_left_side()) {
                    diff = get_eq_sym_diff(pr1.second.get_left_side(), pr2.second.get_right_side());
                // L1 = R1 and L2 = R2 and R1 = R2 => L1 = L2
                } else if(pr1.second.get_right_side() == pr2.second.get_right_side()) {
                    diff = get_eq_sym_diff(pr1.second.get_left_side(), pr2.second.get_left_side());
                }

                Predicate new_pred;
                if(generate_identities_suit(diff, new_pred) && new_pred != pr1.second && new_pred != pr2.second) {
                    new_preds.insert({index, new_pred});
                    /// It assumes L = A B X; L = A B Y1 Y2 ... 
                    /// diff.first should contain X; diff.second Y1 Y2
                    if(diff.first.size() == 1) { // if a new predicate is of the form X = Y1 Y2 ... 
                        rem_ids.insert(pr2.first); // remove L = A B Y1 Y2
                    } else {
                        rem_ids.insert(pr1.first);
                    }
                    index++;
                }
            }
        }
        for(const size_t & i : rem_ids) {
            this->formula.remove_predicate(i);
        }
        for(const auto &pr : new_preds) {
            this->formula.add_predicate(pr.second, pr.first);
        }
        STRACE("str-prep", tout << print_info(is_trace_enabled("str-nfa")));
    }

    /**
     * @brief Create concatenation graph. Oriented graph where each term is node and two terms
     * (variable/litaral) t1 and t2 are connected (t1 -> t2) if t1.t2 occurs in some predicate.
     * Moreover each edge is labelled by number of occurrences of such concatenation in the formula.
     *
     * @return ConcatGraph of the formula.
     */
    ConcatGraph FormulaPreprocessor::get_concat_graph() const {
        ConcatGraph graph;

        for(const Predicate& pr : this->formula.get_predicates_set()) {
            for(const std::vector<BasicTerm>& side : pr.get_params()) {
                for(size_t i = 0; i <= side.size(); i++) {
                    // we use variable with empty name to denote that the variable varname is at the end of the side
                    BasicTerm from = graph.init();
                    BasicTerm to = graph.init();
                    if (i > 0) {
                        from = side[i-1];
                    }
                    if(i < side.size()) {
                        to = side[i];
                    }
                    graph.add_edge(from, to);
                }
            }
        }
        return graph;
    }

    /**
     * @brief Get regular sublists, i.e., concatenations X1...Xk such that each Xi occurrs (if it is a variable) in the
     * formula only in  X1...Xk. In other words, if we replace X1...Xk by a fresh variable V, then
     * X+ ... Xk do not occurr in the formula anymore (except in V).
     *
     * @param res Regular sublists with the number of their occurrences.
     */
    void FormulaPreprocessor::get_regular_sublists(std::map<Concat, unsigned>& res) const {
        ConcatGraph graph = get_concat_graph();

        for(const BasicTerm& t : graph.get_init_vars()) {
            Concat sub;
            // Get all occurrences of t
            std::set<VarNode> occurrs = this->formula.get_var_occurr(t);
            // Get side containing t in the first predicate containing t
            Concat side = formula.get_side_of_var_node(*occurrs.begin());

            int start = std::abs(occurrs.begin()->position) - 1;
            for(size_t i = start; i < side.size(); i++) {
                std::set<VarNode> vns;
                // Construct the set of supposed occurences of the symbol side[i]
                for(const VarNode& vn : occurrs) {
                    vns.insert({
                        side[i],
                        vn.pred_index,
                        FormulaVar::increment_side_index(vn.position, i-start)
                    });
                }
                // Compare the supposed occurrences with real occurrences.
                std::set<VarNode> occurs_act = this->formula.get_var_occurr(side[i]);

                // do not include length variables
                if(false && this->len_variables.find(side[i]) != this->len_variables.end()) {
                    break;
                }
                if(side[i].is_variable() && vns != occurs_act) {
                    break;
                }
                if(side[i].is_literal() && !std::includes(occurs_act.begin(),
                    occurs_act.end(), vns.begin(), vns.end())) {
                    break;
                }
                sub.push_back(side[i]);
            }

            if(sub.size() > 1) {
                res[sub] = occurrs.size();
            }
        }
    }

    /**
     * @brief Replace regular sequences with a fresh variables. The regular sequence is a concatenations X1...Xk
     * such that each Xi occurrs (if it is a variable) in the
     * formula only in  X1...Xk. In other words, if we replace X1...Xk by a fresh variable V, then
     * variables from X1 ... Xk do not occurr in the formula anymore (except in V).
     *
     * @param mn Minimum number of occurrences of a regular sequence to be replaced with a fresh variable.
     */
    void FormulaPreprocessor::reduce_regular_sequence(unsigned mn) {
        STRACE("str-prep", tout << "Preprocessing step - reduce_regular_sequence\n";);
        std::map<Concat, unsigned> regs;
        std::set<Predicate> new_eqs;
        get_regular_sublists(regs);

        for(const auto& pr : regs) {
            if(pr.second >= mn) {
                BasicTerm fresh_var = util::mk_noodler_var_fresh("regular_seq");
                this->formula.replace(pr.first, Concat({fresh_var}));
                update_reg_constr(fresh_var, pr.first);
                Predicate new_eq = Predicate::create_equation({fresh_var}, pr.first);
                this->add_to_len_formula(new_eq.get_formula_eq());
                new_eqs.insert(new_eq);
            }
        }
        for(const Predicate& eq : new_eqs) {
            this->formula.add_predicate(eq);
            // We do not add dependency
        }
        STRACE("str-prep", tout << print_info(is_trace_enabled("str-nfa")));
    }

    /**
     * @brief Get all epsilon terms (variables with the language containing eps only and
     * epsilon literals).
     *
     * @param res All terms with epsilon semantics.
     */
    void FormulaPreprocessor::get_eps_terms(std::set<BasicTerm>& res) const {
        for(const auto& pr : get_formula().get_varmap()) {
            if(pr.first.is_variable() && is_var_eps(pr.first)) {
                res.insert(pr.first);
            }
            if(pr.first.is_literal() && pr.first.get_name() == "") {
                res.insert(pr.first);
            }
            if(pr.first.is_literal() && this->aut_ass.is_epsilon(pr.first) ) {
                res.insert(pr.first);
            }

        }
    }

    /**
     * @brief Transitively ropagate epsilon variables. The epsilon variables and the epsilon
     * literal remove from the formula and set the corresponding languages appropriately.
     */
    void FormulaPreprocessor::propagate_eps() {
        STRACE("str-prep", tout << "Preprocessing step - propagate_eps\n";);
        std::set<BasicTerm> eps_set;
        get_eps_terms(eps_set);
        std::deque<size_t> worklist;
        std::set<size_t> eps_eq_id;

        // get indices of equations containing at least one eps term
        for(const BasicTerm& t : eps_set) {
            std::set<VarNode> nds = get_formula().get_var_occurr(t);
            std::transform(nds.begin(), nds.end(), std::back_inserter(worklist),
                [](const VarNode& n){ return n.pred_index ; });
        }

        while(!worklist.empty()) {
            size_t index = worklist.front();
            worklist.pop_front();
            // eps_eq_id contains indices of equations that were reduced to eps = eps (one side is eps)
            if(eps_eq_id.find(index) != eps_eq_id.end())
                continue;

            std::set<BasicTerm> new_eps; // newly added epsilon terms
            Predicate eq = this->formula.get_predicate(index);
            if(!eq.is_equation())
                continue;

            std::set<BasicTerm> left = eq.get_left_set();
            std::set<BasicTerm> right = eq.get_right_set();
            if(is_subset(left, eps_set)) {
                new_eps = set_difference(eq.get_side_vars(Predicate::EquationSideType::Right), eps_set);
                eps_eq_id.insert(index);
            } else if(is_subset(right, eps_set)) {
                new_eps = set_difference(eq.get_side_vars(Predicate::EquationSideType::Left), eps_set);
                eps_eq_id.insert(index);
            }

            for(const BasicTerm& t : new_eps) {
                eps_set.insert(t);
                std::set<VarNode> nds = get_formula().get_var_occurr(t);
                std::transform(nds.begin(), nds.end(), std::back_inserter(worklist),
                    [](const VarNode& n){ return n.pred_index ; });
            }
        }

        for(const BasicTerm& t : eps_set) {
            if(t.is_variable()) {
                update_reg_constr(t, Concat()); // L(t) = L(t) \cap {\eps}
            }
            this->formula.replace(Concat({t}), Concat());
            // add len constraint |X| = 0
            this->add_to_len_formula(Predicate::create_equation({t}, Concat()).get_formula_eq());
        }
        this->formula.clean_predicates();

        // update dependencies (overapproximation). Each remaining predicate depends on all epsilon equations.
        for(const auto& pr : this->formula.get_predicates()) {
            // might result to the case {0: {0,1,...}}
            this->dependency[pr.first].insert(eps_eq_id.begin(), eps_eq_id.end());
        }

        STRACE("str-prep", tout << print_info(is_trace_enabled("str-nfa")));
    }

    /**
     * @brief Gather information about a concatenation for equation separation.
     *
     * @param concat Concatenation
     * @param res vector where i-th position contains a pair (M,n) where M is a map mapping variables to 
     * the number of their occurrences (multimap) preceeding position i in @p concat and n is a length of all 
     * literals preceeding @p concat.
     */
    void FormulaPreprocessor::get_concat_gather(const Concat& concat, SepEqsGather& res) const {
        std::pair<std::map<BasicTerm, unsigned>, unsigned> prev = { std::map<BasicTerm,unsigned>(), 0 };
        for(const BasicTerm& t : concat) {
            std::pair<std::map<BasicTerm, unsigned>, unsigned> new_val(prev);
            if(t.is_variable()) {
                new_val.first[t]++;
            } else if(t.is_literal()) {
                new_val.second += t.get_name().length();
            } else {
                assert(false);
            }
            res.push_back(new_val);
            prev = new_val;
        }
    }

    /**
     * @brief Separate equations into a set of new equations.
     *
     * @param eq Equation
     * @param gather_left Gathered informaiton about left side
     * @param gather_right Gathered informaiton about right side
     * @param res Set of new equations
     */
    void FormulaPreprocessor::separate_eq(const Predicate& eq, const SepEqsGather& gather_left, SepEqsGather& gather_right, std::set<Predicate>& res) const {
        Concat left = eq.get_left_side();
        Concat right = eq.get_right_side();
        auto it_left = left.begin();
        auto it_right = right.begin();
        assert(eq.is_equation());

        for(size_t i = 0; i < gather_left.size(); i++) {
            for(size_t j = 0; j < gather_right.size(); j++) {
                if(gather_left[i] == gather_right[j]) {
                    res.insert(Predicate::create_equation(
                        Concat(it_left, left.begin()+i+1),
                        Concat(it_right, right.begin()+j+1)
                    ));
                    it_left = left.begin()+i+1;
                    it_right = right.begin()+j+1;
                }
            }
        }
        Concat left_rest = Concat(it_left, left.end());
        Concat right_rest = Concat(it_right, right.end());
        if(left_rest.empty() && right_rest.empty()) // nothing to be added
            return;
        if(left_rest.empty())
            left_rest.push_back(BasicTerm(BasicTermType::Literal, "")); // avoid empty side by putting there epsilon
        if(right_rest.empty())
            right_rest.push_back(BasicTerm(BasicTermType::Literal, "")); // avoid empty side by putting there epsilon
        Predicate rest = Predicate::create_equation(left_rest, right_rest);
        res.insert(rest);
    }

    /**
     * @brief Separate equations.
     */
    void FormulaPreprocessor::separate_eqs() {
        STRACE("str-prep", tout << "Preprocessing step - separate_eqs\n";);
        std::set<Predicate> add_eqs;
        std::set<size_t> rem_ids;

        for(const auto& pr : this->formula.get_predicates()) {
            if(!pr.second.is_equation())
                continue;
            SepEqsGather gather_left, gather_right;
            std::set<Predicate> res;
            get_concat_gather(pr.second.get_left_side(), gather_left);
            get_concat_gather(pr.second.get_right_side(), gather_right);
            separate_eq(pr.second, gather_left, gather_right, res);
            if(res.size() > 1) {
                add_eqs.insert(res.begin(), res.end());
                rem_ids.insert(pr.first);
            }
        }

        for(const Predicate& p : add_eqs) {
            this->formula.add_predicate(p);
        }
        for(const size_t & i : rem_ids) {
            this->formula.remove_predicate(i);
        }
        STRACE("str-prep", tout << print_info(is_trace_enabled("str-nfa")));
    }

    /**
     * @brief Gather variables allowing left/right extension. A variable X is left extensible if
     * L(X) = \Sigma^*.L(X) (right extensibility analogously). \Sigma is collected among all
     * automata in the assignment.
     *
     * @param side Left/right extension
     * @param res Extensible variables
     */
    void FormulaPreprocessor::gather_extended_vars(Predicate::EquationSideType side, std::set<BasicTerm>& res) {
        mata::nfa::Nfa sigma_star = this->aut_ass.sigma_star_automaton();
        for(const auto& pr : this->formula.get_varmap()) {
            if(pr.second.size() > 0) {
                mata::nfa::Nfa concat;
                if(side == Predicate::EquationSideType::Left)
                    concat = mata::nfa::concatenate(sigma_star, *(this->aut_ass.at(pr.first)));
                else
                    concat = mata::nfa::concatenate(*(this->aut_ass.at(pr.first)), sigma_star);

                if(mata::nfa::are_equivalent(*(this->aut_ass.at(pr.first)), concat)) {
                    res.insert(pr.first);
                }
            }
        }
    }

    /**
     * @brief Remove extensible variables from beginning/end of an equation:
     * X = Y1 Y2 Y3 if Y1 occurrs always first (and X is the left side) and
     * Y2 is left extensible. We can remove Y1 (similarly the right extensibility and removing from
     * the end of the equation).
     */
    void FormulaPreprocessor::remove_extension() {
        STRACE("str-prep", tout << "Preprocessing step - remove_extension\n";);
        std::set<BasicTerm> begin_star, end_star;
        gather_extended_vars(Predicate::EquationSideType::Left, begin_star);
        gather_extended_vars(Predicate::EquationSideType::Right, end_star);

        using ExtVarMap = std::map<BasicTerm, std::vector<BasicTerm>>;
        ExtVarMap b_map, e_map;
        VarMap varmap = this->formula.get_varmap();

        auto flt = [&varmap](ExtVarMap& mp) {
            std::map<BasicTerm,BasicTerm> ret;
            for(const auto& pr : mp) {
                std::set<BasicTerm> sing(pr.second.begin(), pr.second.end());
                if(varmap[pr.first].size() == pr.second.size() && sing.size() == 1) {
                    ret.insert({pr.first, *sing.begin()});
                }
            }
            return ret;
        };

        for(const auto& pr : this->formula.get_predicates()) {
            if(!pr.second.is_equation())
                continue;
            Concat left = pr.second.get_left_side();
            Concat right = pr.second.get_right_side();
            /**
             * TODO: Extend to both sides (so far just the left side is considered)
             */
            if(left.size() == 1 && right.size() > 1) {
                if(right[0].is_variable() && left[0].is_variable()
                    && right[1].is_variable() && begin_star.find(right[1]) != begin_star.end()
                    && varmap[right[1]].size() == 1
                    && this->len_variables.find(right[0]) == this->len_variables.end()
                    && this->len_variables.find(right[1]) == this->len_variables.end() ) {
                    b_map.insert({right[0], {}});
                    b_map[right[0]].push_back(left[0]);
                }
                if(right[right.size()-1].is_variable() && left[0].is_variable()
                    && right[right.size()-2].is_variable() && end_star.find(right[right.size()-2]) != end_star.end()
                    && varmap[right[right.size()-2]].size() == 1
                    && this->len_variables.find(right[right.size()-1]) == this->len_variables.end()
                    && this->len_variables.find(right[right.size()-2]) == this->len_variables.end() ) {
                    e_map.insert({right[right.size()-1], {}});
                    e_map[right[right.size()-1]].push_back(left[0]);
                }
            }
        }

        std::map<BasicTerm,BasicTerm> b_rem = flt(b_map);
        std::map<BasicTerm,BasicTerm> e_rem = flt(e_map);
        std::map<size_t, Predicate> updates;
        for(const auto& pr : this->formula.get_predicates()) {
            Predicate pred = pr.second;
            if(!pred.is_equation()) continue;
            if(pred.get_left_side().size() > 1) continue;
            if(pred.get_right_side().size() < 2) continue;

            Concat right_side = pred.get_right_side();
            bool modif = false;
            for(const auto& beg : b_rem) {
                if(pred.get_left_side()[0] == beg.second && right_side[0] == beg.first) {
                    // X = Y1 Y2 ...
                    Concat modif_side(right_side.begin()+1, right_side.end());
                    pred = Predicate::create_equation(pred.get_left_side(), modif_side);
                    modif = true;
                    break;
                }
            }
            right_side = pred.get_right_side();
            for(const auto& end : e_rem) {
                if(pred.get_left_side()[0] == end.second && *(right_side.end()-1) == end.first) {
                    pred = Predicate::create_equation(pred.get_left_side(), Concat(right_side.begin(), right_side.end()-1));
                    modif = true;
                    break;
                }
            }
            if(modif) updates.insert({pr.first, pred});
        }

        // We do not need to update dependencies
        for(const auto& pr : updates) {
            this->update_predicate(pr.first, pr.second);
        }
        STRACE("str-prep", tout << print_info(is_trace_enabled("str-nfa")));
    }

    /**
     * @brief Remove trivial equations of the form X = X
     */
    void FormulaPreprocessor::remove_trivial() {
        STRACE("str-prep", tout << "Preprocessing step - remove_trivial\n";);
        std::set<size_t> rem_ids;
        for(const auto& pr : this->formula.get_predicates()) {
            if(!pr.second.is_equation())
                continue;

            if(pr.second.get_left_side() == pr.second.get_right_side()) {
                rem_ids.insert(pr.first);
            }
        }

        for(const size_t & i : rem_ids) {
            this->formula.remove_predicate(i);
        }
        STRACE("str-prep", tout << print_info(is_trace_enabled("str-nfa")));
    }

    /**
     * @brief Flatten dependencies. Compute transition closure of dependencies.
     *
     * @return Transitive closure of the Dependency
     */
    Dependency FormulaPreprocessor::get_flat_dependency() const {
        Dependency flat = get_dependency();
        std::set<size_t> keys;
        for(const auto& pr : flat) {
            keys.insert(pr.first);
        }

        bool changed = true;
        while(changed) {
            changed = false;
            for(const size_t& k : keys) {
                auto it = flat.find(k);
                size_t sb = it->second.size();
                for(const size_t& val : flat[k]) {
                    it->second.insert(flat[val].begin(), flat[val].end());
                }
                if(sb != it->second.size()) {
                    changed = true;
                }
            }
        }

        return flat;
    }


    /**
     * @brief Return a modified formula by the preprocessing.
     *
     * @return Result of the preprocessing.
     */
    Formula FormulaPreprocessor::get_modified_formula() const {
        Formula ret;
        for(const Predicate& p: this->formula.get_predicates_set()) {
            ret.add_predicate(p);
        }
        return ret;
    }

    /**
     * @brief Refine languages for equations of the form X = R (|X|=1) to the L(X) = L(X) \cap L(R).
     * Moreover, for the literal terms l from the current automata assignments, restrict its 
     * languages to L(l) = L(l) \cap {l}. Recall that the automata assignment contains not only 
     * variables but also literals.
     */
    void FormulaPreprocessor::refine_languages() {
        STRACE("str-prep", tout << "Preprocessing step - refine_languages\n";);
        std::set<BasicTerm> ineq_vars;
        for(const auto& pr : this->formula.get_predicates()) {
            if(!pr.second.is_inequation())
                continue;

            if(pr.second.get_left_side().size() == 1 && pr.second.get_left_side()[0].is_variable()) {
                ineq_vars.insert(pr.second.get_left_side()[0]);
            }
            if(pr.second.get_right_side().size() == 1 && pr.second.get_right_side()[0].is_variable()) {
                ineq_vars.insert(pr.second.get_right_side()[0]);
            }
        }

        for(const auto& pr :this->formula.get_predicates()) {
            if(!pr.second.is_equation())
                continue;

            if(pr.second.get_left_side().size() == 1) {
                BasicTerm var = pr.second.get_left_side()[0];
                if(ineq_vars.find(var) != ineq_vars.end()) {
                    update_reg_constr(var, pr.second.get_right_side());
                } else if(pr.second.get_right_side().size() == 1) {
                    update_reg_constr(var, pr.second.get_right_side());
                }
            }
            if(pr.second.get_right_side().size() == 1) {
                BasicTerm var = pr.second.get_right_side()[0];
                if(ineq_vars.find(var) != ineq_vars.end()) {
                    update_reg_constr(var, pr.second.get_left_side());
                } else if(pr.second.get_left_side().size() == 1) {
                    update_reg_constr(var, pr.second.get_left_side());
                }
            }
        }

        // Check if there is a regular constraint of the form "A" in .... 
        // In that case, we construct automaton for "A" and make a product with the 
        // corresponding language of the Basic Term "A".
        for(const auto& pr : this->aut_ass) {
            if(pr.first.is_literal()) {
                mata::nfa::Nfa word_aut = AutAssignment::create_word_nfa(pr.first.get_name());
                mata::nfa::Nfa inters = mata::nfa::intersection(*(pr.second), word_aut);
                inters.trim();
                this->aut_ass[pr.first] = std::make_shared<mata::nfa::Nfa>(mata::nfa::reduce(inters));
            }
        }
        STRACE("str-prep", tout << print_info(is_trace_enabled("str-nfa")));
    }

    /**
     * @brief Skip irrelevant word equations. Assume that the original formula is length-satisfiable.
     * 
     * Remove L=R if single_occur(R) and L(R) = \Sigma^* and R does not contain conversion vars (for these,
     * we need to do proper splitting).
     */
    void FormulaPreprocessor::skip_len_sat() {
        STRACE("str-prep", tout << "Preprocessing step - skip_len_sat\n";);
        std::set<size_t> rem_ids;

        auto is_sigma_star = [&](const std::set<BasicTerm>& bts) {
            mata::nfa::Nfa sigma_star = this->aut_ass.sigma_star_automaton();
            for(const BasicTerm& bt : bts) {
                if(!mata::nfa::are_equivalent(sigma_star, *this->aut_ass.at(bt))) {
                    return false;
                }
            }
            return true;
        };

        for(const auto& pr : this->formula.get_predicates()) {
            if(!pr.second.is_equation())
                continue;

            if(this->formula.single_occurr(pr.second.get_left_set())
                && set_disjoint(this->conversion_vars, pr.second.get_side_vars(Predicate::EquationSideType::Left))) {
                auto left_set = pr.second.get_left_set();
                if(left_set.size() > 0 && is_sigma_star(left_set)) {
                    rem_ids.insert(pr.first);
                    this->add_to_len_formula(pr.second.get_formula_eq());
                    // we add the removed equation to removed_inclusions_for_model, but we have to swap
                    // sides so that the single occurring side is on the right (we are gonna
                    // pretend it is an inclusion and from left side compute the vars of
                    // the right side in the model generation)
                    removed_inclusions_for_model.push_back(pr.second.get_switched_sides_predicate());

                    // if we need to produce models and left side contains some length variable,
                    // we need to make all variables on the right side length too, so that we
                    // select the correct lengths during the model generation
                    if (!set_disjoint(this->len_variables, pr.second.get_side_vars(Predicate::EquationSideType::Left))
                        && m_params.m_produce_models) {
                        for (BasicTerm right_var : pr.second.get_side_vars(Predicate::EquationSideType::Right)) {
                            len_variables.insert(right_var);
                        }
                    }

                    continue; // we removed the equation, continue with next predicate
                }
            }
            
            if(this->formula.single_occurr(pr.second.get_right_set())
                && set_disjoint(this->conversion_vars, pr.second.get_side_vars(Predicate::EquationSideType::Right))) {
                auto right_set = pr.second.get_right_set();
                if(right_set.size() > 0 && is_sigma_star(right_set)) {
                    rem_ids.insert(pr.first);
                    this->add_to_len_formula(pr.second.get_formula_eq());
                    removed_inclusions_for_model.push_back(pr.second);
                    // if we need to produce models and right side contains some length variable,
                    // we need to make all variables on the left side length too, so that we
                    // select the correct lengths during the model generation
                    if (!set_disjoint(this->len_variables, pr.second.get_side_vars(Predicate::EquationSideType::Right))
                        && m_params.m_produce_models) {
                        for (BasicTerm left_var : pr.second.get_side_vars(Predicate::EquationSideType::Left)) {
                            len_variables.insert(left_var);
                        }
                    }
                }               
            }
        }
        for(const size_t & i : rem_ids) {
            this->formula.remove_predicate(i);
        }
        STRACE("str-prep", tout << print_info(is_trace_enabled("str-nfa")));
    }

    /**
     * @brief Generate equalities from the equivalence class containing 
     * length-equivalent variables.
     * 
     * @param ec Equivalence class containing length-equivalent variables.
     */
    void FormulaPreprocessor::generate_equiv(const BasicTermEqiv& ec) {
        STRACE("str-prep", tout << "Preprocessing step - generate_equiv\n";);
        std::set<Predicate> new_preds;
        size_t index = this->formula.get_max_index() + 1;

        for(const auto& pr1 : this->formula.get_predicates()) {
            if(!pr1.second.is_equation())
                continue;
            for(const auto& pr2 : this->formula.get_predicates()) {
                if(!pr2.second.is_equation())
                    continue;
                if(pr1.first >= pr2.first)
                    continue;

                Predicate pc1 = pr1.second;
                Predicate pc2 = pr2.second;
                if(pc1.get_left_side() == pc2.get_right_side()) {
                    pc2 = pc2.get_switched_sides_predicate();
                } else if(pc1.get_right_side() == pc2.get_left_side()) {
                    pc1 = pc1.get_switched_sides_predicate();
                } else if(pc1.get_right_side() == pc2.get_right_side()) {
                    pc1 = pc1.get_switched_sides_predicate();
                    pc2 = pc2.get_switched_sides_predicate();
                } else if(pc1.get_left_side() == pc2.get_left_side()) {
                    // already set
                } else {
                    continue;
                }
                if(pc1.get_right_side().size() == 0 || pc2.get_right_side().size() == 0) {
                    continue;
                }
                for(size_t i = 0; i < std::min(pc1.get_right_side().size(), pc2.get_right_side().size()); i++) {
                    BasicTerm t1 = pc1.get_right_side()[i];
                    BasicTerm t2 = pc2.get_right_side()[i];
                    if(t1 == t2) {
                        continue;
                    } else if(same_length(ec, t1, t2)) {
                        Predicate new_pred = Predicate::create_equation({t1}, {t2});
                        new_preds.insert(new_pred);
                    } else {
                        break;
                    }
                }

                int i = int(pc1.get_right_side().size() - 1), j = int(pc2.get_right_side().size() - 1);
                for(; i >= 0 && j >= 0; i--, j--) {
                    BasicTerm t1 = pc1.get_right_side()[i];
                    BasicTerm t2 = pc2.get_right_side()[j];
                    if(t1 == t2) {
                        continue;
                    } else if(same_length(ec, t1, t2)) {
                        Predicate new_pred = Predicate::create_equation({t1}, {t2});
                        new_preds.insert(new_pred);
                    } else {
                        break;
                    }
                }
            }
        }
        for(const auto &pr : new_preds) {
            this->formula.add_predicate(pr);
        }
        STRACE("str-prep", tout << print_info(is_trace_enabled("str-nfa")));
    }

    /**
     * @brief Check if two languages of two terms have the same length.
     * 
     * @param ec Equivalence class containing length-equivalent variables.
     * @param t1 Term1
     * @param t2 Term2
     * @return Equal length -> true
     */
    bool FormulaPreprocessor::same_length(const BasicTermEqiv& ec, const BasicTerm&t1, const BasicTerm& t2) const {
        if(ec_are_equal(ec, t1, t2)) {
            return true;
        }
        int n1, n2;
        if(this->aut_ass.fixed_length(t1, n1) && this->aut_ass.fixed_length(t2, n2) && n1 == n2) {
            return true;
        }
        return false;
    }

    /**
     * @brief Infer equalities from required alignments. For instance for 
     * X = Y1 "A" Y2
     * X = Z1 "A" Z2 where "A" not in L(Y1) and "A" not in L(Z1)
     * infer Y1 = Z1.
     * 
     * Works also for a propagated case, for instance
     * X = Y1 "A" Y2
     * X = W Z2 
     * W = Z1 "A" Z3 where "A" not in L(Y1) and "A" not in L(Z1)
     */
    void FormulaPreprocessor::infer_alignment() {
        STRACE("str-prep", tout << "Preprocessing step - infer_alignment\n";);
        using VarSeparator = std::map<BasicTerm, std::set<BasicTerm>>;
        // separators for each variable: map of literals -> set of basic terms: 
        // for each literal (L) contains terms (T) that preceeds that literal: there is equation ... = T L
        std::map<BasicTerm, VarSeparator> separators {};

        bool changed = true;
        while(changed) {
            changed = false;
            for(const auto& pr : this->formula.get_predicates()) {
                if(!pr.second.is_equation()) continue;
                if(pr.second.get_left_side().size() != 1) continue;

                // base case
                const Concat& side = pr.second.get_right_side();
                const BasicTerm& left_var = pr.second.get_left_side()[0];
                if(pr.second.get_left_side().size() == 1) {
                    changed = changed || add_var_separator(side, separators[left_var]);
                }

                // propagation of var separators
                // for the case X = Y .... -> add separators from Y to X
                if(side.size() > 0 && side[0] != left_var) {
                    changed = changed || propagate_var_separators(left_var, side[0], separators);
                }
            }
        }

        // construct new equations from computed separators
        for(const auto& pr : separators) {
            for(const auto& a : pr.second) {
                if(a.second.size() <=  1) continue;
                BasicTerm fst = *a.second.begin();
                for(const BasicTerm& dest : a.second) {
                    if(dest != fst) {
                        this->formula.add_predicate(Predicate::create_equation({fst}, {dest}));
                    }
                }
            }
        }
        STRACE("str-prep", tout << print_info(is_trace_enabled("str-nfa")));
    }

    /**
     * @brief Propagate variable separators. Add separators from variable @p src to the variable @p dest. 
     * 
     * @param dest Variable to be updated
     * @param src Variable whose separators are copied to @p dest.
     * @param separators Separators
     * @return true <-> the propagation added a new element to @p separators.
     */
    bool FormulaPreprocessor::propagate_var_separators(const BasicTerm& dest, const BasicTerm& src, std::map<BasicTerm, std::map<BasicTerm, std::set<BasicTerm>>>& separators) {
        bool changed = false;
        for(const auto& var_sep: separators[src]) {
            std::set<BasicTerm>& st = separators[dest][var_sep.first];
            size_t before = st.size();
            st.insert(var_sep.second.begin(), var_sep.second.end());
            changed = changed || st.size() != before;
        }
        return changed;
    }

    /**
     * @brief Add a new separator to @p container (separators of a variable).
     * 
     * @param side Equations side to be used for the update
     * @param container Separators of a variable
     * @return true <-> a new element was added to @p container.
     */
    bool FormulaPreprocessor::add_var_separator(const Concat& side, std::map<BasicTerm, std::set<BasicTerm>>& container) {
        if(side.size() < 2) {
            return false;
        }
        if(!side[1].is_literal()) {
            return false;
        }
        if(this->aut_ass.are_disjoint(side[0], side[1])) {
            if(container[side[1]].contains(side[0])) {
                return false;
            }
            container[side[1]].insert(side[0]);
            return true;
        }
        return false;
    }

    /**
     * @brief Propagate equations from a common prefix. For instance for
     * X = W1 W2 Y
     * X = W1 W2 W3 W4
     * infer Y = W3 W4.
     * 
     * Works also for a propagated case, for instance
     * X = W1 W2 Y
     * X = K W3 W4
     * K = W1 W2
     * infer Y = W3 W4
     */
    void FormulaPreprocessor::common_prefix_propagation() {
        STRACE("str-prep", tout << "Preprocessing step - common_prefix_propagation\n";);
        TermReplaceMap replace_map = construct_replace_map();
        std::set<size_t> rem_ids;
        size_t i = 0;
        for(const auto& pr1 : this->formula.get_predicates()) {
            if(!pr1.second.is_equation()) continue;
            if(pr1.second.get_right_side().size() == 1) continue;

            Concat c1 = flatten_concat(pr1.second.get_right_side(), replace_map);

            for(const auto& pr2 : this->formula.get_predicates()) {
                if(!pr2.second.is_equation()) continue;
                if(pr1 == pr2) continue;
                if(pr1.second.get_left_side() != pr2.second.get_left_side()) continue;
                if(pr2.second.get_right_side().size() == 1) continue;

                Concat c2 = flatten_concat(pr2.second.get_right_side(), replace_map);
                // compute the common prefix
                for(i = 0; i < std::min(c1.size(), c2.size()); i++) {
                    if(c1[i] != c2[i]) break;
                }
                // i is the first mismatching index
                if(c1.size() == i + 1) {
                    Predicate new_pred = Predicate::create_equation({c1[i]}, Concat(c2.begin() + i, c2.end()));
                    this->formula.add_predicate(new_pred);
                    // pr1 is of the form  X = W1 W2 Y
                    // pr2 is of the form  X = W1 W2 W3 W4
                    // We can remove pr2 as we generate new constraint Y = W3 W4
                    // Note that the propagated case has no effect as there is just exactly one equation of the form K = W1 W2
                    if(new_pred.get_right_side().size() > 1) {
                        rem_ids.insert(pr2.first);
                    }
                } else if (c2.size() == i + 1) {
                    Predicate new_pred = Predicate::create_equation({c2[i]}, Concat(c1.begin() + i, c1.end()));
                    this->formula.add_predicate(new_pred);
                    // pr1 is of the form  X = W1 W2 W3 W4
                    // pr2 is of the form  X = W1 W2 Y
                    // We can remove pr1 as we generate new constraint Y = W3 W4
                    // Note that the propagated case has no effect as there is just exactly one equation of the form K = W1 W2
                    if(new_pred.get_right_side().size() > 1) {
                        rem_ids.insert(pr1.first);
                    }
                }
            }
        }
        for(const size_t & i : rem_ids) {
            this->formula.remove_predicate(i);
        }
        STRACE("str-prep", tout << print_info(is_trace_enabled("str-nfa")));
    }

    /**
     * @brief Propagate equations from a common suffix. For instance for
     * X = Y W1 W2
     * X = W3 W4 W1 W2
     * infer Y = W3 W4.
     * 
     * Works also for a propagated case, for instance
     * X = Y W1 W2
     * X = W3 W4 K
     * K = W1 W2
     * infer Y = W3 W4
     */
    void FormulaPreprocessor::common_suffix_propagation() {
        STRACE("str-prep", tout << "Preprocessing step - common_suffix_propagation\n";);
        TermReplaceMap replace_map = construct_replace_map();
        std::set<size_t> rem_ids;
        int i = 0, j = 0;
        for(const auto& pr1 : this->formula.get_predicates()) {
            if(!pr1.second.is_equation()) continue;
            if(pr1.second.get_right_side().size() == 1) continue;

            Concat c1 = flatten_concat(pr1.second.get_right_side(), replace_map);

            for(const auto& pr2 : this->formula.get_predicates()) {
                if(!pr2.second.is_equation()) continue;
                if(pr1 == pr2) continue;
                if(pr1.second.get_left_side() != pr2.second.get_left_side()) continue;
                if(pr2.second.get_right_side().size() == 1) continue;
                

                Concat c2 = flatten_concat(pr2.second.get_right_side(), replace_map);
                // compute the common prefix
                for(i = c1.size() - 1, j = c2.size() - 1; i >= 0 && j >= 0; i--, j--) {
                    if(c1[i] != c2[j]) break;
                }
                // i is the first mismatching index
                if(i == 0) {
                    Predicate new_pred = Predicate::create_equation({c1[i]}, Concat(c2.begin(), c2.begin() + j + 1));
                    this->formula.add_predicate(new_pred);
                    // pr1 is of the form  X = Y W1 W2
                    // pr2 is of the form  X = W3 W4 W1 W2
                    // We can remove pr2 as we generate new constraint Y = W3 W4
                    // Note that the propagated case has no effect as there is just exactly one equation of the form K = W1 W2
                    if(new_pred.get_right_side().size() > 1) {
                        rem_ids.insert(pr2.first);
                    }
                } else if (j == 0) {
                    Predicate new_pred = Predicate::create_equation({c2[j]}, Concat(c1.begin(), c1.begin() + i + 1));
                    this->formula.add_predicate(new_pred);
                    // we can remove one of the original constraint because it is redundant (it can be restored by the new one)
                    // pr1 is of the form  X = W3 W4 W1 W2
                    // pr2 is of the form  X = Y W1 W2
                    // We can remove pr1 as we generate new constraint Y = W3 W4
                    // Note that the propagated case has no effect as there is just exactly one equation of the form K = W1 W2
                    if(new_pred.get_right_side().size() > 1) {
                        rem_ids.insert(pr1.first);
                    }
                }
            }
        }
        for(const size_t & i : rem_ids) {
            this->formula.remove_predicate(i);
        }
        STRACE("str-prep", tout << print_info(is_trace_enabled("str-nfa")));
    }

    /**
     * @brief Construct replace map. Replace map contains all items of the form X -> {W1 W2, W3, ...} if 
     * there are quations X = W1 W2, X = W3, ... 
     * 
     * @return TermReplaceMap Constructed replace map
     */
    TermReplaceMap FormulaPreprocessor::construct_replace_map() const {
        TermReplaceMap replace_map {};
        for(const auto& pr : this->formula.get_predicates()) {
            if(!pr.second.is_equation()) continue;
            if(pr.second.get_left_side().size() != 1) continue;

            const BasicTerm &var = pr.second.get_left_side()[0];
            replace_map[var].insert(pr.second.get_right_side());
        }
        return replace_map;
    }

    /**
     * @brief Flatten the given concatenation @p con according to the replace map. In particular, 
     * replace all variables in @p con with the corresponding item in @p replace_map. 
     * Applicable only if there is exactly one corresponding guy in @p replace_map (i.e., does not work 
     * recursively).
     * 
     * @param con Conjunction to be flattened.
     * @param replace_map Replace map
     * @return Concat Conjunction with subtituted terms.
     */
    Concat FormulaPreprocessor::flatten_concat(const Concat& con, TermReplaceMap& replace_map) const {
        Concat ret {};
        for(const BasicTerm& bt : con) {
            if(replace_map[bt].size() == 1) {
                const Concat& rpl = *replace_map[bt].begin();
                ret.insert(ret.end(), rpl.begin(), rpl.end());
            } else {
                ret.push_back(bt);
            }
        }

        // TODO: Currently, we cannot unify "A" "A" with "AA".
        return ret;
    }

    /**
     * @brief Underapproximates the languages. Replace co-finite languages with length constraints while 
     * setting their languages to \Sigma^*.
     */
    void FormulaPreprocessor::underapprox_languages() {
        STRACE("str-prep", tout << "Preprocessing step - underapprox_languages\n";);
        for(const Predicate& pred : this->formula.get_predicates_set()) {
            for(const BasicTerm& var : pred.get_vars()) {
                if(this->aut_ass.is_co_finite(var)) {
                    underapprox_var_language(var);
                }
            }
        }
        STRACE("str-prep", tout << print_info(is_trace_enabled("str-nfa")));
    } 

    void FormulaPreprocessor::underapprox_var_language(const BasicTerm& var) {
        mata::nfa::Nfa aut_compl = this->aut_ass.complement_lang(var);
        LenNode lengths = AutAssignment::get_lengths(aut_compl, var);
        this->add_to_len_formula(LenNode(LenFormulaType::NOT, {lengths}));
        this->aut_ass[var] = std::make_shared<mata::nfa::Nfa>(this->aut_ass.sigma_star_automaton());
        this->len_variables.insert(var);
    }

    /**
     * @brief Reduce the number of diseqalities.
     */
    void FormulaPreprocessor::reduce_diseqalities() {
        STRACE("str-prep", tout << "Preprocessing step - reduce_diseqalities\n";);
        std::set<size_t> rem_ids;

        for(const auto& pr : this->formula.get_predicates()) {
            if(!pr.second.is_inequation())
                continue;

            mata::nfa::Nfa aut_left = this->aut_ass.get_automaton_concat(pr.second.get_left_side());
            mata::nfa::Nfa aut_right = this->aut_ass.get_automaton_concat(pr.second.get_right_side());
            if(mata::nfa::intersection(aut_left, aut_right).is_lang_empty()) { // L(left) \cap L(right) == empty
                rem_ids.insert(pr.first);
                continue;
            }
            
            if(pr.second.get_left_side().size() == 1 && pr.second.get_left_side()[0].is_variable()) {
                BasicTerm var = pr.second.get_left_side()[0];
                mata::nfa::Nfa other = this->aut_ass.get_automaton_concat(pr.second.get_right_side());
                if(mata::nfa::intersection(*this->aut_ass.at(var), other).is_lang_empty()) {
                    rem_ids.insert(pr.first);
                    continue;
                }
                if(pr.second.get_right_side().size() < 1 || (pr.second.get_right_side().size() == 1 && pr.second.get_right_side()[0].is_literal())) {
                    this->aut_ass[var] = std::make_shared<mata::nfa::Nfa>(mata::nfa::intersection(*this->aut_ass.at(var), this->aut_ass.complement_aut(other)));
                    rem_ids.insert(pr.first);
                    continue;
                }
            }
            if(pr.second.get_right_side().size() == 1 && pr.second.get_right_side()[0].is_variable()) {
                BasicTerm var = pr.second.get_right_side()[0];
                mata::nfa::Nfa other = this->aut_ass.get_automaton_concat(pr.second.get_left_side());
                if(mata::nfa::intersection(*this->aut_ass.at(var), other).is_lang_empty()) {
                    rem_ids.insert(pr.first);
                    continue;
                }
                if(pr.second.get_left_side().size() < 1 || (pr.second.get_left_side().size() == 1 && pr.second.get_left_side()[0].is_literal())) {
                    this->aut_ass[var] = std::make_shared<mata::nfa::Nfa>(mata::nfa::intersection(*this->aut_ass.at(var), this->aut_ass.complement_aut(other)));
                    rem_ids.insert(pr.first);
                    continue;
                }
            }
        }

        for(const size_t & i : rem_ids) {
            this->formula.remove_predicate(i);
        }
        STRACE("str-prep", tout << print_info(is_trace_enabled("str-nfa")));
    }

    void FormulaPreprocessor::reduce_transducers() {
        STRACE("str-prep", tout << "Preprocessing step - reduce_transducers\n";);
        std::set<size_t> rem_ids;

        for (const auto& pred : this->formula.get_predicates()) {
            if (!pred.second.is_transducer()) { continue; }
            const std::vector<BasicTerm>& output = pred.second.get_output();
            const std::vector<BasicTerm>& input = pred.second.get_input();
            if (output.size() == 1 && input.size() == 1) {
                const BasicTerm& output_var = output[0];
                const BasicTerm& input_var = input[0];
                if (output_var.is_variable() && this->formula.get_var_occurr(output_var).size() == 1 && !this->len_variables.contains(output_var)) {
                    this->aut_ass[input_var] = std::make_shared<mata::nfa::Nfa>(mata::nfa::intersection(pred.second.get_transducer()->apply(*this->aut_ass.at(output_var), 1).to_nfa_move(), *this->aut_ass.at(input_var)));
                    rem_ids.insert(pred.first);
                    removed_inclusions_for_model.push_back(Predicate::create_transducer(pred.second.get_transducer(), {output_var}, {input_var}));
                } else if (input_var.is_variable() && this->formula.get_var_occurr(input_var).size() == 1 && !this->len_variables.contains(input_var)) {
                    this->aut_ass[output_var] = std::make_shared<mata::nfa::Nfa>(mata::nfa::intersection(pred.second.get_transducer()->apply(*this->aut_ass.at(input_var), 0).to_nfa_move(), *this->aut_ass.at(output_var)));
                    rem_ids.insert(pred.first);
                    removed_inclusions_for_model.push_back(pred.second);
                }
            }
        }

        for(const size_t & i : rem_ids) {
            this->formula.remove_predicate(i);
        }
        STRACE("str-prep", tout << print_info(is_trace_enabled("str-nfa")));
    }

    /**
     * @brief Heuristicaly check if @p con1 and @p con2 can be unified, meaning that if we replace 
     * variables with their replacements, can we get that @p con1  == @p con2 ? 
     * 
     * @param con1 First conjunction
     * @param con2 Second conjunction
     * @return true -> they can be unified
     */
    bool FormulaPreprocessor::can_unify(const Concat& con1, const Concat& con2, const std::function<bool(const Concat&, const Concat&)> &check) const {
        TermReplaceMap replace_map = construct_replace_map();

        // TODO: make as a parameter (although not sure how to set it in an optimal way). Moreover this algorithm could be 
        // rewrited using ideas of LL(1) parsing. Then this parameter becomes useless.
        int max_unifs = 4;
        Concat tmp1 = con1;
        Concat tmp2 = con2;
        for(int i = 0; i < max_unifs; i++) {
            tmp2 = con2;
            for(int j = 0; j < max_unifs; j++) {
                if(check(tmp1, tmp2)) {
                    return true;
                }
                tmp2 = flatten_concat(tmp2, replace_map);
            }
            tmp1 = flatten_concat(tmp1, replace_map);
        }
        return false;
    }

    /**
     * @brief Check if the instance is clearly unsatisfiable. It checks trivial (dis)equations
     * of the form x != x, ab = cd (x is term, a,b,c,d are constants).
     * 
     * @return True --> unsat for sure.
     */
    bool FormulaPreprocessor::contains_unsat_eqs_or_diseqs() {
        auto check = [](const Concat& c1, const Concat& c2) -> bool {
            return c1 == c2;
        };
        for(const auto& pr : this->formula.get_predicates()) {            
            if (pr.second.is_inequation() && can_unify(pr.second.get_left_side(), pr.second.get_right_side(), check)) {
                return true;
            }
            if (pr.second.is_equation() && pr.second.is_str_const()) {
                zstring left{};
                zstring right{};
                for(const BasicTerm& t : pr.second.get_left_side()) {
                    left = left + t.get_name();
                }
                for(const BasicTerm& t : pr.second.get_right_side()) {
                    right = right + t.get_name();
                }
                if(left != right) return true;
            }
        }
        return false;
    }

    /**
     * @brief Check if we can unify @p left and @p right in the sense of contains 
     * (check if @p right is sublist of @p left ). Unifies according to equations.
     * 
     * @param left First concatenation
     * @param right Second concatenation
     * @return true <-> can be sublist-unified 
     */
    bool FormulaPreprocessor::can_unify_contain(const Concat& left, const Concat& right) const {
        auto check = [](const Concat& c1, const Concat& c2) -> bool {
            for(size_t i = 0; i < c1.size(); i++) {
                auto c1_end = c1.begin() + i + c2.size();
                if (i + c2.size() >= c1.size()) {
                    c1_end = c1.end();
                }
                if(std::equal(c1.begin() + i, c1_end, c2.begin(), c2.end())) {
                    return true;
                }
            }
            return false;
        };
        if (left == right) {
            return true;
        }
        return can_unify(left, right, check);
    }


    /**
     * @brief Adds restrictions from conversions to the len_formula, so that (underapproximating) unsat check can be better
     * 
     * Specifically, it checks if for to_code(x)/to_int(x) there is any valid word in the language of automaton for x, i.e,
     * some one-symbol word for to_code(x) or some word containing only digits for to_int(x).
     * 
     * @param conversions 
     */
    void FormulaPreprocessor::conversions_validity(std::vector<TermConversion>& conversions) {
        STRACE("str-prep", tout << "Preprocessing step - conversions_validity\n";);
        mata::nfa::Nfa sigma_aut = aut_ass.sigma_automaton();
        mata::nfa::Nfa only_digits_aut = AutAssignment::digit_automaton();

        for (const auto& conv : conversions) {
            if ((conv.type == ConversionType::TO_CODE && mata::nfa::reduce(mata::nfa::intersection(sigma_aut,       *aut_ass.at(conv.string_var))).is_lang_empty()) ||
                (conv.type == ConversionType::TO_INT  && mata::nfa::reduce(mata::nfa::intersection(only_digits_aut, *aut_ass.at(conv.string_var))).is_lang_empty()))
                {
                    len_formula.succ.emplace_back(LenFormulaType::EQ, std::vector<LenNode>{conv.int_var, -1});
                }
        }
        STRACE("str-prep", tout << print_info(is_trace_enabled("str-nfa")));
    }

    /**
     * @brief Check if it is possible to unify L and R for not(contains(L,R)).
     * 
     * @return true -> L and R are unifiable
     */
    bool FormulaPreprocessor::can_unify_not_contains() {
        for(const auto& [id, pred] : this->formula.get_predicates()) {
            if(!pred.is_not_cont()) continue;
            if(can_unify_contain(pred.get_haystack(), pred.get_needle())) {
                return true;
            }

        }
        return false;
    }

    /**
     * @brief Try to replace not contains predicates. In particular, we replace predicates of the form (not_contains lit x) where 
     * lit is a literal by a regular constraint x notin Alit' where  Alit' was obtained from A(lit) by setting all 
     * states initial and final.
     * 
     * @return false if a not(contains) is unsatisfiable 
     */
    bool FormulaPreprocessor::replace_not_contains() {
        std::set<size_t> rem_ids;
        for(const auto& [id, pred] : this->formula.get_predicates()) {
            if(!pred.is_not_cont()) continue;
            Concat haystack = pred.get_haystack();
            Concat needle = pred.get_needle();
            if(haystack.size() == 1 && needle.size() == 1 && !this->aut_ass.at(haystack[0])->delta.get_used_symbols().contains(util::get_dummy_symbol())) {
                if(this->aut_ass.is_singleton(haystack[0]) && this->aut_ass.is_singleton(needle[0])) {
                    if(mata::nfa::are_equivalent(*this->aut_ass.at(haystack[0]), *this->aut_ass.at(needle[0]))) {
                        return false;
                    }
                }
                if(this->aut_ass.is_singleton(haystack[0]) && needle[0].is_variable()) {
                    mata::nfa::Nfa nfa_copy = *this->aut_ass.at(haystack[0]);
                    for(unsigned i = 0; i < nfa_copy.num_of_states(); i++) {
                        nfa_copy.initial.insert(i);
                        nfa_copy.final.insert(i);
                    }

                    mata::nfa::Nfa complement = this->aut_ass.complement_aut(nfa_copy);
                    this->aut_ass.restrict_lang(needle[0], complement);
                    rem_ids.insert(id);
                    continue;
                }
            }
            if(needle.size() == 1 && this->aut_ass.is_epsilon(needle[0])) {
                return false;
            }
        }
        
        for(const size_t & i : rem_ids) {
            this->formula.remove_predicate(i);
        }
        return true;
    }

    /**
     * @brief Check whether the system contains trivially unsatisfiable (dis)equations 
     * containing only literals.
     * 
     * @return true the system is unsat
     */
    bool FormulaPreprocessor::contains_unsat_literals() {

        auto gather_lits = [&](const Concat& concat) -> std::optional<zstring> {
            zstring lits;
            for(const BasicTerm& bt : concat) {
                if(bt.is_literal()) {
                    lits = lits + bt.get_name();
                } else {
                    return {};
                }
            }
            return lits;
        };

        for(const auto& [id, pred] : this->formula.get_predicates()) {
            if(!pred.is_eq_or_ineq()) continue;
            std::optional<zstring> left = gather_lits(pred.get_left_side());
            std::optional<zstring> right = gather_lits(pred.get_right_side());
            if(left.has_value() && right.has_value()) {
                if(pred.is_equation() && left.value() != right.value()) {
                    return true;
                }
                if(pred.is_inequation() && left.value() == right.value()) {
                    return true;
                }
            }
        }
        return false;
    }

    std::string FormulaPreprocessor::print_info(bool print_nfas) {
        std::stringstream res;
        res << "Current formula:\n";
        for (const auto& pred : formula.get_predicates_set()) {
            res << pred << std::endl;
        }
        res << "Current automata assignment:\n";
        for (const auto& [var, nfa] : aut_ass) {
            res << var << " -> ";
            if (print_nfas) {
                res << std::endl << *nfa;
            } else {
                res << "NFA\n";
            }
        }
        res << "Current substition map:\n";
        for (const auto& [var, subst] : substitution_map) {
            res << var << " ->";
            for (const auto& subst_var : subst) {
                res << " " << subst_var;
            }
            res << std::endl;
        }
        res << "Current removed equations:\n";
        for (const auto& rem_eq : removed_inclusions_for_model) {
            res << rem_eq << std::endl;
        }
        res << "Current length vars:";
        for (const auto& len_var : len_variables) {
            res << " " << len_var;
        }
        res << "\nCurrent conversion vars:";
        for (const auto& conv_var : conversion_vars) {
            res << " " << conv_var;
        }
        res << std::endl;
        res << "Current length formula: " << len_formula << std::endl;
        return res.str();
    }

} // Namespace smt::noodler.
